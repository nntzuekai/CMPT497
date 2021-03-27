/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.

 */

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <list>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/CFGPrinter.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"

#if defined(LLVM34)
#include "llvm/DebugInfo.h"
#else
#include "llvm/IR/DebugInfo.h"
#endif

#if defined(LLVM34) || defined(LLVM35) || defined(LLVM36)
#define LLVM_OLD_DEBUG_API
#endif

namespace llvm {

template<>
struct DOTGraphTraits<Function*> : public DefaultDOTGraphTraits {
  DOTGraphTraits(bool isSimple=true) : DefaultDOTGraphTraits(isSimple) {}

  static std::string getGraphName(Function *F) {
    return "CFG for '" + F->getName().str() + "' function";
  }

  std::string getNodeLabel(BasicBlock *Node, Function *Graph) {
    if (!Node->getName().empty()) {
      return Node->getName().str();
    }

    std::string Str;
    raw_string_ostream OS(Str);

    Node->printAsOperand(OS, false);
    return OS.str();
  }
};

} // namespace llvm

using namespace llvm;

cl::opt<bool> InstAnalysis{
    "inst",
    cl::desc("Enable Instruction Analysis and Instrumentation.")
};

cl::opt<bool> ExitPathAnalysis{
    "exits",
    cl::desc("Enable Path-to-exit Analysis and Instrumentation.")
};

constexpr int max_exit_dist=5;
constexpr int score_ratio=5;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

  template<int MaxDist>
  struct ExitDistRecord{
    std::array<int,MaxDist+1> forward_dist_count={};
    std::array<int, MaxDist+1> backward_dist_count={};

    int &operator[] (int idx){
      return (idx>=0)?forward_dist_count.at(idx):backward_dist_count.at(-idx);
    }
    const int &operator[] (int idx) const{
      return (idx>=0)?forward_dist_count.at(idx):backward_dist_count.at(-idx);
    }
  };

  template <int MaxDist>
  using BB_ExitDist_map=DenseMap<const BasicBlock *, ExitDistRecord<MaxDist> >; 

}

char AFLCoverage::ID = 0;

static void getDebugLoc(const Instruction *I, std::string &Filename,
                        unsigned &Line) {
#ifdef LLVM_OLD_DEBUG_API
  DebugLoc Loc = I->getDebugLoc();
  if (!Loc.isUnknown()) {
    DILocation cDILoc(Loc.getAsMDNode(M.getContext()));
    DILocation oDILoc = cDILoc.getOrigLocation();

    Line = oDILoc.getLineNumber();
    Filename = oDILoc.getFilename().str();

    if (filename.empty()) {
      Line = cDILoc.getLineNumber();
      Filename = cDILoc.getFilename().str();
    }
  }
#else
  if (DILocation *Loc = I->getDebugLoc()) {
    Line = Loc->getLine();
    Filename = Loc->getFilename().str();

    if (Filename.empty()) {
      DILocation *oDILoc = Loc->getInlinedAt();
      if (oDILoc) {
        Line = oDILoc->getLine();
        Filename = oDILoc->getFilename().str();
      }
    }
  }
#endif /* LLVM_OLD_DEBUG_API */
}

static bool isBlacklisted(const Function *F) {
  static const SmallVector<std::string, 4> BlacklistPrefixes{
    "asan.",
    "llvm.",
    "sancov.",
    "__ubsan_handle_"
  };

  for (auto const &BlacklistPref : BlacklistPrefixes) {
    if (F->getName().startswith(BlacklistPref)) {
      return true;
    }
  }

  static const SmallVector<std::string, 4> Blacklist{
    "free",
    "malloc",
    "calloc",
    "realloc"
  };

  for(auto const &Func:Blacklist){
    if(F->getName()==Func){
      return true;
    }
  }

  return false;
}

// inline static uint64_t total_score(uint64_t arith_cnt, uint64_t store_cnt, uint64_t load_cnt, const std::map<int,int> *exit_dists){
//   if(exit_dists==nullptr){
//     return inst_score(arith_cnt, store_cnt, load_cnt);
//   }
//   else{
//     return score_ratio*inst_score(arith_cnt, store_cnt, load_cnt)+exit_score(exit_dists);
//   }
// }

inline static uint64_t inst_score(uint64_t arith_cnt, uint64_t store_cnt, uint64_t load_cnt){
  return arith_cnt+2*(store_cnt+load_cnt);
}

template<int N=5>
inline static uint64_t exit_score(const ExitDistRecord<N> &exit_dist_record){
  uint64_t sum=0;

  if(exit_dist_record[0]!=0){
    return 0;
  }

  for(int i=1;i<=N;++i){
    sum+=(6-i)*(exit_dist_record[i]+exit_dist_record[-i]);
  }

  return sum;
}

struct InstScoreVisitor:public InstVisitor<InstScoreVisitor>{
  uint64_t arith_cnt=0;
  uint64_t store_cnt=0;
  uint64_t load_cnt=0;

  void reset(){
    arith_cnt=0;
    store_cnt=0;
    load_cnt=0;
  }

  void visitBinaryOperator(BinaryOperator &I){
    ++arith_cnt;
  }

  void visitLoad(LoadInst &I){
    ++load_cnt;
  }

  void visitStore(StoreInst &I){
    ++store_cnt;
  }


};

template<int N=5>
std::unique_ptr<BB_ExitDist_map<N> > exit_path_dists(const Function &F){
	auto BB_num=F.size();

	using map_type=BB_ExitDist_map<N>;
	std::unique_ptr<map_type > exit_dists_ptr=std::unique_ptr<map_type >(new map_type());
  	auto &exit_dists=*exit_dists_ptr;
	DenseMap<const BasicBlock *, std::array<int, 2> > out_degs;
	// DenseMap<const BasicBlock *, SmallVector<const BasicBlock *, 4> > BB_preds;

	SmallVector<std::pair<const BasicBlock *, const BasicBlock *>, 8> back_edges;
	FindFunctionBackedges(F,back_edges);

	DenseSet<std::pair<const BasicBlock *, const BasicBlock *> > BE_set;
	BE_set.insert(back_edges.begin(),back_edges.end());

	DenseSet<const BasicBlock *> zero_degs;
	int finised_cnt=0;

	for(const auto &BB:F){
		auto T_inst=BB.getTerminator();
		auto succ_num=T_inst->getNumSuccessors();

		if(succ_num>0){
			for(const auto *succ_BB:successors(&BB)){
				if(BE_set.count(std::make_pair(&BB,succ_BB))){
					++out_degs[&BB][1];
				}
				else{
					++out_degs[&BB][0];
				}
			}
			if(out_degs[&BB][0]==0){
				exit_dists[&BB][0]=1;
				zero_degs.insert(&BB);
			}
		}
		else{
			exit_dists[&BB][0]=1;
			zero_degs.insert(&BB);
		}
		
	}

	while(!zero_degs.empty()){
		const BasicBlock *BB=*zero_degs.begin();
		zero_degs.erase(zero_degs.begin());

		const auto &exits_entry=exit_dists[BB];

		for(const BasicBlock *pred_BB:predecessors(BB)){
			if(BE_set.count(std::make_pair(pred_BB,BB))){
				continue;
			}

			for(int i=0;i<N;++i){
				exit_dists[pred_BB][i+1]+=exits_entry[i];
			}

			--out_degs[pred_BB][0];

			if(out_degs[pred_BB][0]==0){
				zero_degs.insert(pred_BB);
			}
		}

		++finised_cnt;
	}

	assert(finised_cnt==BB_num);

	for(const auto &BB:F){

		if(out_degs[&BB][1]){
			
			for(const BasicBlock *succ:successors(&BB)){
				if(!BE_set.count(std::make_pair(&BB,succ))){
					continue;
				}

				for(int i=4;i>=0;--i){
					if(exit_dists[succ][i]!=0){
						++exit_dists[&BB][-i-1];
						break;
					}
				}
			}

			
		}
	}

	return exit_dists_ptr;
}


bool AFLCoverage::runOnModule(Module &M) {

  /* Show a banner */

  char be_quiet = 0;
  bool do_inst=InstAnalysis.getValue();
  bool do_exit=ExitPathAnalysis.getValue();
  if (isatty(2) && !getenv("AFL_QUIET")) {

    if(do_inst||do_exit){
      SAYF(cCYA "afl-llvm-pass (497)%s%s" cBRI VERSION cRST " by RHK\n",do_inst?"-inst":"",do_exit?"-exits":"");
    }
    else{
      SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");
    }

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Instrument all the things! */

  int inst_blocks = 0;


    /* Distance instrumentation */

    LLVMContext &C = M.getContext();
    IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
    IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
    IntegerType *Int64Ty = IntegerType::getInt64Ty(C);

#ifdef __x86_64__
    IntegerType *LargestType = Int64Ty;
    ConstantInt *MapCntLoc = ConstantInt::get(LargestType, MAP_SIZE + 8);
#else
    IntegerType *LargestType = Int32Ty;
    ConstantInt *MapCntLoc = ConstantInt::get(LargestType, MAP_SIZE + 4);
#endif
    ConstantInt *MapScoreLoc = ConstantInt::get(LargestType, MAP_SIZE);
    ConstantInt *One = ConstantInt::get(LargestType, 1);

    /* Get globals for the SHM region and the previous location. Note that
       __afl_prev_loc is thread-local. */

    GlobalVariable *AFLMapPtr =
        new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                           GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

    GlobalVariable *AFLPrevLoc = new GlobalVariable(
        M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
        0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

    InstScoreVisitor vis;
    for (auto &F : M) {
      if(isBlacklisted(&F)){
        continue;
      }

      decltype(exit_path_dists(F)) exit_dists=nullptr;
      if(do_exit){
        exit_dists=exit_path_dists(F);
      }

      for (auto &BB : F) {

		    // outs()<<BB<<"\n";
		    // outs()<<score<<"\n=================\n";

        BasicBlock::iterator IP = BB.getFirstInsertionPt();
        IRBuilder<> IRB(&(*IP));

        if (AFL_R(100) >= inst_ratio) continue;

        /* Make up cur_loc */

        unsigned int cur_loc = AFL_R(MAP_SIZE);

        ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

        /* Load prev_loc */

        LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
        PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

        /* Load SHM pointer */

        LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
        MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *MapPtrIdx =
            IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

        /* Update bitmap */

        LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
        Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
        IRB.CreateStore(Incr, MapPtrIdx)
           ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        /* Set prev_loc to cur_loc >> 1 */

        StoreInst *Store =
            IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
        Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        if(do_inst||do_exit){
          uint64_t score=0;

          if(do_inst){
            vis.reset();
            vis.visit(BB);

            score+=inst_score(vis.arith_cnt,vis.store_cnt,vis.load_cnt);
          }

          if(do_exit){
            score*=score_ratio;
            score+=exit_score((*exit_dists)[&BB]);
          }
          

          if(score>0){
            ConstantInt *Score =
                ConstantInt::get(LargestType, score);

            /* Add score to shm[MAPSIZE] */

            Value *MapScorePtr = IRB.CreateBitCast(
                IRB.CreateGEP(MapPtr, MapScoreLoc), LargestType->getPointerTo());
            LoadInst *MapScore = IRB.CreateLoad(MapScorePtr);
            MapScore->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

            Value *IncrDist = IRB.CreateAdd(MapScore, Score);
            IRB.CreateStore(IncrDist, MapScorePtr)
                ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

            /* Increase count at shm[MAPSIZE + (4 or 8)] */

            Value *MapCntPtr = IRB.CreateBitCast(
                IRB.CreateGEP(MapPtr, MapCntLoc), LargestType->getPointerTo());
            LoadInst *MapCnt = IRB.CreateLoad(MapCntPtr);
            MapCnt->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

            Value *IncrCnt = IRB.CreateAdd(MapCnt, One);
            IRB.CreateStore(IncrCnt, MapCntPtr)
                ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
          }
          
        } 
        inst_blocks++;

      }
    }
  

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks,
             getenv("AFL_HARDEN")
             ? "hardened"
             : ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN"))
               ? "ASAN/MSAN" : "non-hardened"),
             inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}

static RegisterPass<AFLCoverage> OptRegAFL{
  "aflc", "AFLCoverage",
  false,
  false
};

static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
