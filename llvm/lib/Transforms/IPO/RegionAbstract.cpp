/*
 * @Author: Wenhan Shang
 * @Email: whu_swh@whu.edu.cn
 * @Date: 2022-01-21 11:32:26
 * @FilePath: /llvm-12-swh/llvm/lib/Transforms/IPO/RegionAbstract.cpp
 */

#include "llvm/Transforms/IPO/RegionAbstract.h"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SequenceAlignment.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/Analysis/RegionPrinter.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Verifier.h"
#include <cassert>
#include <cmath>
#include <cstddef>
#include <iomanip>
#include <iterator>
#include <llvm/IR/IRBuilder.h>

#include "llvm/Support/Casting.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/Support/SuffixTree.h"
#include "llvm/Support/SuffixTreeRepeatedInfos.h"
#include "llvm/Support/Timer.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FormatVariadic.h"

#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/IteratedDominanceFrontier.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"

#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"

#include "llvm/Support/RandomNumberGenerator.h"

//#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"

#include "llvm/Analysis/Utils/Local.h"
#include "llvm/Transforms/Utils/Local.h"

#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Utils/FunctionComparator.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"

#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Transforms/IPO.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/FunctionMerging.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils.h"

#include "llvm/Analysis/InlineSizeEstimatorAnalysis.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <cstdlib>
#include <fstream>

#include <algorithm>
#include <list>
#include <map>
#include <ostream>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>

#include <limits.h>

#include <functional>
#include <queue>
#include <unordered_set>
#include <vector>

#include <algorithm>
#include <stdlib.h>
#include <time.h>

#ifdef __unix__
/* __unix__ is usually defined by compilers targeting Unix systems */
#include <unistd.h>
#elif defined(_WIN32) || defined(WIN32)
/* _Win32 is usually defined by compilers targeting 32 or   64 bit Windows
 * systems */
#include <windows.h>
#endif

//#include <faiss/IndexFlat.h>

#define DEBUG_TYPE "RegionAbstract"

#define ENABLE_DEBUG_CODE

//#define FMSA_USE_JACCARD
//#define FINGERPRINT_USE_TYPE

// #define RA_TIME_STEPS_DEBUG

using namespace llvm;
using IRSimilarity::FunctionData;
using IRSimilarity::InstrDataTraits;

#ifdef RA_TIME_STEPS_DEBUG
Timer RATimePreProcess("RA:Preprocess", "RA:Preprocess");
Timer RATimeMapInstrs("RA:MapInstrs", "RA:MapInstrs");
Timer RATimeAnalysisTree("RA:AnalysisTree", "RA:AnalysisTree");
Timer RATimeGetCandidates("RA:GetCandidates", "RA:GetCandidates");
Timer RATimeMergeCandidate("RA:MergeCandidate", "RA:MergeCandidate");
Timer RATimeTotal("RA::Total", "RA::Total");
#endif

// debug macro by swh
#define PREPROCESS_DEBUG
// #define MAPPER_DEBUG
// #define ANALYSIS_TREE_DEBUG
#define GET_CANDIDATES_DEBUG
#define MERGE_CANDIDATES_DEBUG

static cl::opt<bool> Debug("region-abstract-debug", cl::init(false), cl::Hidden,
                           cl::desc("Outputs debug information"));

static cl::opt<unsigned> RegionFindingMode(
    "region-finding-mode", cl::init(1), cl::Hidden,
    cl::desc("Modes that determines how to find min region, \nwhile 0 mode use "
             "llvm region, 1 mode (default) use a custom function by swh."));

static cl::opt<unsigned> CreateFuncOverHead(
    "create-function-overhead", cl::init(1), cl::Hidden,
    cl::desc("Overhead of creating a new function in code size."));

static cl::opt<unsigned> SmallFunctionLimit(
    "small-function-limit", cl::init(3), cl::Hidden,
    cl::desc("Maximum instruction number of large functions."));

static cl::opt<unsigned>
    RepeatedLowerLimit("repeated-lower-limit", cl::init(2), cl::Hidden,
                       cl::desc("Lower limit of repeated substring length"));

static cl::opt<unsigned>
    OverlapEliminateMode("overlap-eliminate-mode", cl::init(0), cl::Hidden,
                         cl::desc("Eliminate overlap by benefit or by "
                                  "length, default to by benefit."));

static cl::opt<unsigned>
    RAStopAfter("region-abstract-stop-after", cl::init(0), cl::Hidden,
                cl::desc("0 do not stop, 1 stop after get function size info, "
                         "2 stop after analysis suffix tree."));

static cl::opt<unsigned>
    RAMaxNumSelection("region-abstract-max-selects", cl::init(500), cl::Hidden,
                      cl::desc("Maximum number of allowed operand selection"));

static cl::opt<bool> AbstractToPrivateLinkage(
    "region-abstract-private", cl::init(true), cl::Hidden,
    cl::desc("Abstract region to functions of private linkage type."));

// optimazition for args
static cl::opt<bool> RAAggregateArgs(
    "region-abstract-aggregate-args", cl::init(true), cl::Hidden,
    cl::desc("Whether region abstract use struct to aggregate args."));

static cl::opt<bool>
    RAUseSingleStruct("region-abstract-use-single-struct", cl::init(true),
                      cl::Hidden,
                      cl::desc("Whether region abstract use allocated struct "
                               "in function to aggregate args."));

static cl::opt<bool> RAAggregateSourceId(
    "region-abstract-aggregate-source-id", cl::init(true), cl::Hidden,
    cl::desc("Whether region abstract aggregate source-id."));

// important optimazition
static cl::opt<bool> RAAbstractInBlockCandidate(
    "region-abstract-in-block-candidate", cl::init(true), cl::Hidden,
    cl::desc("Whether abstract in-block-candidate."));

static cl::opt<bool>
    RAGetAndMerge("region-abstract-get-merge", cl::init(true), cl::Hidden,
                  cl::desc("Merge immediately after geting candidate."));

// bennefit model
// default to 0, ir benefit model; 1, binary benefit model
static cl::opt<unsigned>
    RABenefitModel("region-abstract-benefit-model", cl::init(0), cl::Hidden,
                   cl::desc("Region Abstract Benefit Model, default to 0 ir "
                            "model, 1 means binary model."));

static cl::opt<unsigned>
    RAInterBenefitLimit("region-abstract-inter-benefit-limit", cl::init(0),
                        cl::Hidden,
                        cl::desc("Lower benefit limit of  inter candidate we "
                                 "can abstract, default to 0."));
static cl::opt<unsigned>
    RAIntraBenefitLimit("region-abstract-intra-benefit-limit", cl::init(200),
                        cl::Hidden,
                        cl::desc("Lower benefit limit of  intra candidate we "
                                 "can abstract, default to 200."));

//预估的
static cl::opt<unsigned> RASelectOverhead(
    "region-abstract-select-overhead-estimate", cl::init(6), cl::Hidden,
    cl::desc("Region abstract select overhead estimate for each candidate."));

// only for debug
static cl::opt<unsigned> RACreatedFuncUpperLimit(
    "region-abstract-created-func-limit", cl::init(2000), cl::Hidden,
    cl::desc("Upper limit of created function number."));

#define CODE_SIZE_REDUCTION_UPPER_LIMIT

#pragma region my_class

// class SuffixTreeInfo {
//   std::vector<int> Input;
// };

// #define BLOCK_ANALYSIS_SWH
class BlockAnalysis {
public:
  std::vector<size_t> SizeOfEachBlock;
  void AnalysisAndPrint() {
    errs() << "######Block Analysis######\n";
    //首先按照大小打印其size信息
    long SumSize = 0;
    std::map<size_t, unsigned> SizeDistribution;
    for (auto BlockSize : SizeOfEachBlock) {
      errs() << BlockSize << "\n";
      SumSize += BlockSize;
      if (SizeDistribution.find(BlockSize) == SizeDistribution.end())
        SizeDistribution[BlockSize] = 0;
      SizeDistribution[BlockSize] += 1;
    }
    //打印平均大小信息
    errs() << "Average Size:" << SumSize / SizeOfEachBlock.size() << "\n";
    //打印大小分布信息
    errs() << "Size Distribution:\n";
    for (auto Pair : SizeDistribution) {
      errs() << Pair.first << ", " << Pair.second << "\n";
    }
    errs() << "######Block Analysis######\n";
  }
};

#pragma endregion

#pragma region my_tools

static void postProcessFunction(Function &F) {
  legacy::FunctionPassManager FPM(F.getParent());

  // FPM.add(createPromoteMemoryToRegisterPass());
  FPM.add(createCFGSimplificationPass());
  // FPM.add(createInstructionCombiningPass(2));
  // FPM.add(createCFGSimplificationPass());

  FPM.doInitialization();
  FPM.run(F);
  FPM.doFinalization();
}

static std::string getValueName(const Value *V) {
  if (V) {
    std::string Name;
    raw_string_ostream Namestream(Name);
    V->printAsOperand(Namestream, false);
    return Namestream.str();
  }
  return "[null]";
}

static void printAlignedSequenceInfo(AlignedSequence<Value *> &AS) {
  unsigned NumMatches = 0;
  unsigned TotalEntries = 0;
  bool AcrossBlocks = false;
  BasicBlock *CurrBB0 = nullptr;
  BasicBlock *CurrBB1 = nullptr;
  for (auto &Entry : AS) {
    TotalEntries++;
    if (Entry.match()) {
      NumMatches++;
      if (isa<BasicBlock>(Entry.get(1))) {
        CurrBB1 = dyn_cast<BasicBlock>(Entry.get(1));
      } else if (Instruction *I = dyn_cast<Instruction>(Entry.get(1))) {
        if (CurrBB1 == nullptr)
          CurrBB1 = I->getParent();
        else if (CurrBB1 != I->getParent()) {
          AcrossBlocks = true;
        }
      }
      if (isa<BasicBlock>(Entry.get(0))) {
        CurrBB0 = dyn_cast<BasicBlock>(Entry.get(0));
      } else if (Instruction *I = dyn_cast<Instruction>(Entry.get(0))) {
        if (CurrBB0 == nullptr)
          CurrBB0 = I->getParent();
        else if (CurrBB0 != I->getParent()) {
          AcrossBlocks = true;
        }
      }
    } else {
      if (Entry.get(0) && isa<BasicBlock>(Entry.get(0)))
        CurrBB1 = nullptr;
      if (Entry.get(1) && isa<BasicBlock>(Entry.get(1)))
        CurrBB0 = nullptr;
    }
  }
  if (AcrossBlocks) {
    errs() << "Across Basic Blocks\n";
  }
  errs() << "Matches: " << NumMatches << ", " << TotalEntries << "\n";
}

static void printAlignedSequence(AlignedSequence<Value *> &AS,
                                 raw_ostream &OFS) {

  for (auto &Entry : AS) {
    if (Entry.match()) {
      OFS << "1: ";
      if (isa<BasicBlock>(Entry.get(0)))
        OFS << "BB " << getValueName(Entry.get(0)) << "\n";
      else {
        Entry.get(0)->print(OFS, true);
        OFS << "\n";
      }

      OFS << "2: ";
      if (isa<BasicBlock>(Entry.get(1)))
        OFS << "BB " << getValueName(Entry.get(1)) << "\n";
      else {
        Entry.get(1)->print(OFS, true);
        OFS << "\n";
      }
      OFS << "----\n";
    } else {
      if (Entry.get(0)) {
        OFS << "1: ";
        if (isa<BasicBlock>(Entry.get(0)))
          OFS << "BB " << getValueName(Entry.get(0)) << "\n";
        else {
          Entry.get(0)->print(OFS, true);
          OFS << "\n";
        }
        OFS << "2: -\n";
      } else if (Entry.get(1)) {
        OFS << "1: -\n";
        OFS << "2: ";
        if (isa<BasicBlock>(Entry.get(1)))
          OFS << "BB " << getValueName(Entry.get(1)) << "\n";
        else {
          Entry.get(1)->print(OFS, true);
          OFS << "\n";
        }
      }
      OFS << "----\n";
    }
  }
}

// vector version
static SwhRegion *getMinRegionOfBlocks(RegionInfo *RI,
                                       std::vector<BasicBlock *> &BBList,
                                       unsigned Mode = 1) {
  if (Mode == 1) {
    // TODO:
    BasicBlock *StartBB = BBList[0];
    BasicBlock *EndBB = BBList[BBList.size() - 1];
    Function *ParentFunc = StartBB->getParent();
    DominatorTree DT(*ParentFunc);
    PostDominatorTree PDT(*ParentFunc);

    // try to find Region Entry

    // std::vector<BasicBlock *> RegionEntryCandidates = {StartBB};
    SetVector<BasicBlock *> RegionEntryCandidates;
    RegionEntryCandidates.insert(StartBB);

    BasicBlock *CurrentBB;
    auto DomAll = [&] {
      for (BasicBlock *BB : BBList) {
        if (!DT.dominates(CurrentBB, BB))
          return false;
      }
      return true;
    };

    bool FindEntrySucc = false;
    for (int I = 0; I < RegionEntryCandidates.size() && I < 2 * BBList.size();
         I++) {
      CurrentBB = RegionEntryCandidates[I];
      if (DomAll()) {
        FindEntrySucc = true;
        break;
      }
      for (auto PredBB = pred_begin(CurrentBB); PredBB != pred_end(CurrentBB);
           PredBB++) {
        // RegionEntryCandidates.push_back(*PredBB);
        RegionEntryCandidates.insert(*PredBB);
      }
    }
    if (!FindEntrySucc) {
      return nullptr;
    }
    // find the Entry
    BasicBlock *RegionEntry = CurrentBB;
    // RegionEntry->dump();
    if (Debug)
      errs() << "\tFind Entry Block: " << RegionEntry->getName() << "\n";

    // try to find Region End
    // std::vector<BasicBlock *> RegionExitCandidates = {EndBB};
    SetVector<BasicBlock *> RegionExitCandidates;
    RegionExitCandidates.insert(EndBB);

    auto PostDomAll = [&] {
      if (!PDT.dominates(CurrentBB, RegionEntry)) {
        // CurrentBB->dump();
        return false;
      }

      if (!DT.dominates(RegionEntry, CurrentBB)) {
        // CurrentBB->dump();
        return false;
      }

      for (BasicBlock *BB : BBList) {
        if (!PDT.dominates(CurrentBB, BB))
          return false;
      }

      return true;
    };

    bool FindExitSucc = false;

    for (int J = 0; J < RegionExitCandidates.size() && J < 2 * BBList.size();
         J++) {
      CurrentBB = RegionExitCandidates[J];
      if (PostDomAll()) {
        FindExitSucc = true;
        break;
      }
      for (auto SuccBB = succ_begin(CurrentBB); SuccBB != succ_end(CurrentBB);
           SuccBB++) {
        // RegionExitCandidates.push_back(*SuccBB);
        RegionExitCandidates.insert(*SuccBB);
      }
    }
    if (!FindExitSucc) {
      return nullptr;
    }

    // find Region End
    BasicBlock *RegionExit = CurrentBB;
    // RegionExit->dump();
    if (Debug)
      errs() << "\tFind Exit Block: " << RegionExit->getName() << "\n";

    // try to find the real Region.
    auto CheckDomi = [&](BasicBlock *BB) {
      if (!PDT.dominates(RegionExit, BB)) {
        // BB->dump();
        return false;
      }

      if (!DT.dominates(RegionEntry, BB)) {
        // BB->dump();
        return false;
      }

      return true;
    };

    std::vector<BasicBlock *> RegionBBs = {RegionExit, RegionEntry};
    int Tmp = std::distance(pred_begin(RegionExit), pred_end(RegionExit));
    std::vector<int> PredNumOfBBs = {Tmp, 0};
    for (int Index = 1; Index < RegionBBs.size(); Index++) {
      CurrentBB = RegionBBs[Index];
      for (auto SuccBB = succ_begin(CurrentBB); SuccBB != succ_end(CurrentBB);
           SuccBB++) {
        if (CheckDomi(*SuccBB)) {
          auto It = std::find(RegionBBs.begin(), RegionBBs.end(), *SuccBB);
          if (It == RegionBBs.end()) {
            RegionBBs.push_back(*SuccBB);
            PredNumOfBBs.push_back(
                std::distance(pred_begin(*SuccBB), pred_end(*SuccBB)) - 1);
          } else {
            long D = std::distance(RegionBBs.begin(), It);
            PredNumOfBBs[D]--;
          }

        } else {
          return nullptr;
        }
      }
    }

    for (int TmpN : PredNumOfBBs) {
      if (TmpN) {
        return nullptr;
      }
    }

    SwhRegion *MyRegion = new SwhRegion(RegionBBs);
    if (MyRegion->NeedFullExit && MyRegion->FollowBB.size() > 1) {
      return nullptr;
    }

    return MyRegion;
  }

  // Mode == 0
  llvm::Region *MinRegion = nullptr;
  for (llvm::BasicBlock *BB : BBList) {
    llvm::Region *Region = RI->getRegionFor(BB);
    if (!MinRegion)
      MinRegion = Region;
    else
      MinRegion = RI->getCommonRegion(Region, MinRegion);
  }
  return new SwhRegion(MinRegion);
}

static void testElimateInterOverlap(
    std::vector<RepeatedInfos::RepeatedSubstringByS *> &RSList,
    std::vector<unsigned> &StrMap) {
  unsigned CreateFunctionOverhead = CreateFuncOverHead;
  // sort by length
  llvm::stable_sort(RSList, [](RepeatedInfos::RepeatedSubstringByS *LHS,
                               RepeatedInfos::RepeatedSubstringByS *RHS) {
    return LHS->Length > RHS->Length;
  });

  // iterate the list and remove all inter-overlap
  for (std::vector<RepeatedInfos::RepeatedSubstringByS *>::iterator RSIt =
           RSList.begin();
       RSIt != RSList.end();) {
    // If we outlined something that overlapped with a candidate in a previous
    // step, then we can't outline from it.
    llvm::RepeatedInfos::RepeatedSubstringByS *RSP = *RSIt;
    // llvm::RepeatedInfos::RepeatedSubstringByS RS = *RSP;
    unsigned StrLength = RSP->Length;
    erase_if(RSP->StartIndices, [&StrMap, &StrLength](unsigned &StartIdx) {
      return std::any_of(
          StrMap.begin() + StartIdx, StrMap.begin() + StartIdx + StrLength,
          [](unsigned I) { return (I == static_cast<unsigned>(-1)); });
    });

    // If we made it unbeneficial to outline this function, skip it.
    if (RSP->getPredictBenefit(CreateFunctionOverhead) < 1) {
      RSList.erase(RSIt);
      continue;
    }
    ++RSIt;

    // If beneficial, record it in StrMap;
    std::for_each(RSP->StartIndices.begin(), RSP->StartIndices.end(),
                  [&StrMap, &StrLength](unsigned &StartIdx) {
                    std::for_each(
                        StrMap.begin() + StartIdx,
                        StrMap.begin() + StartIdx + StrLength,
                        [](unsigned &I) { I = static_cast<unsigned>(-1); });
                  });
  }
}

/**
 * @brief get an output stream of a file
 * @param FilePath file path of the stream
 * @return an output stream of a file
 */
static raw_fd_ostream *getOutputStreamOfFile(std::string FilePath) {
  std::error_code EC;
  raw_fd_ostream *Outfile = new raw_fd_ostream(FilePath, EC, sys::fs::OF_None);
  return Outfile;
}

static unsigned
getPredictBenefitOfRS(const llvm::SuffixTree::RepeatedSubstring &OriginRS) {
  if (OriginRS.StartIndices.empty() || OriginRS.Length < 2) {
    return 0;
  }
  // Original:  Length*StartIndices.size()
  unsigned Original = OriginRS.Length * OriginRS.StartIndices.size();
  // Abstract:  Length+1+StartIndices.size()+CreateFuncOverHead;
  unsigned Abstract =
      OriginRS.Length + 1 + OriginRS.StartIndices.size() + CreateFuncOverHead;

  if (Original <= Abstract)
    return 0;
  // Benefit: Original - Abstract
  return Original - Abstract;
}

static bool compareBenefit(const llvm::SuffixTree::RepeatedSubstring &LRS,
                           const llvm::SuffixTree::RepeatedSubstring &RRS) {
  return getPredictBenefitOfRS(LRS) > getPredictBenefitOfRS(RRS);
}

static void
printRSBenefit(const llvm::SuffixTree::RepeatedSubstring &OriginRS) {
  errs() << "Benefit:\t" << getPredictBenefitOfRS(OriginRS) << "\n";
}

static void printRS(const llvm::SuffixTree::RepeatedSubstring &OriginRS,
                    const llvm::ArrayRef<unsigned> &TreeStr) {
  unsigned StringLen = OriginRS.Length;
  std::vector<unsigned> RepeatStr;
  RepeatStr.insert(
      RepeatStr.end(), std::next(TreeStr.begin(), OriginRS.StartIndices[0]),
      std::next(TreeStr.begin(), OriginRS.StartIndices[0] + StringLen));
  errs() << "\nLen:\t" << OriginRS.Length << "\tRS:\t";
  for (auto Via : RepeatStr) {
    // errs() << Via << " ";
    char VV = (Via + 48);
    errs() << VV << " ";
  }
  errs() << "\nIndices:\t";
  for (unsigned SI : OriginRS.StartIndices) {
    errs() << SI << " ";
  }
}

static size_t estimateFunctionSize(Function *F, TargetTransformInfo *TTI) {
  float Size = 0;
  for (Instruction &I : instructions(F)) {
    switch (I.getOpcode()) {
    // case Instruction::Alloca:
    case Instruction::PHI:
      Size += 0.2;
      break;
    // case Instruction::Select:
    //  size += 1.2;
    //  break;
    default:
      Size += TTI->getInstructionCost(
                     &I, TargetTransformInfo::TargetCostKind::TCK_CodeSize)
                  .getValue()
                  .getValue();
    }
  }
  return size_t(std::ceil(Size));
}

static size_t estimateInstListSize(SetVector<Instruction *> &InstList,
                                   TargetTransformInfo &TTI) {
  float Size = 0;
  for (Instruction *I : InstList) {
    switch (I->getOpcode()) {
    // case Instruction::Alloca:
    case Instruction::PHI:
      Size += 0.2;
      break;
    // case Instruction::Select:
    //  size += 1.2;
    //  break;
    default:
      Size += TTI.getInstructionCost(
                     I, TargetTransformInfo::TargetCostKind::TCK_CodeSize)
                  .getValue()
                  .getValue();
    }
  }
  return size_t(std::ceil(Size));
}

#ifdef RA_TIME_STEPS_DEBUG
static void TimerPrinter() {
  errs() << "\nRA:PreProcess: " << RATimePreProcess.getTotalTime().getWallTime()
         << "\n";
  RATimePreProcess.clear();
  errs() << "RA::MapInstrs: " << RATimeMapInstrs.getTotalTime().getWallTime()
         << "\n";
  RATimeMapInstrs.clear();
  errs() << "RA::RATimeAnalysisTree: "
         << RATimeAnalysisTree.getTotalTime().getWallTime() << "\n";
  RATimeAnalysisTree.clear();
  errs() << "RA::TimeGetCandidates: "
         << RATimeGetCandidates.getTotalTime().getWallTime() << "\n";
  RATimeGetCandidates.clear();
  errs() << "RA::TimeMergeCandidate: "
         << RATimeMergeCandidate.getTotalTime().getWallTime() << "\n";
  RATimeMergeCandidate.clear();
  errs() << "RA:Total: " << RATimeTotal.getTotalTime().getWallTime() << "\n";
  RATimeTotal.clear();
}
#endif

static StringRef getCalledFunctionName(CallInst &CI) {
  assert(CI.getCalledFunction() != nullptr && "Called Function is nullptr?");

  return CI.getCalledFunction()->getName();
}

static void SetFunctionAttributes(Function *F1, Function *F2,
                                  Function *MergedFunc) {
  unsigned MaxAlignment = std::max(F1->getAlignment(), F2->getAlignment());
  if (F1->getAlignment() != F2->getAlignment()) {
    if (Debug)
      errs() << "WARNING: different function alignment!\n";
  }
  if (MaxAlignment)
    MergedFunc->setAlignment(Align(MaxAlignment));

  if (F1->getCallingConv() == F2->getCallingConv()) {
    MergedFunc->setCallingConv(F1->getCallingConv());
  } else {
    if (Debug)
      errs() << "WARNING: different calling convention!\n";
    // MergedFunc->setCallingConv(CallingConv::Fast);
  }

  MergedFunc->setLinkage(GlobalValue::LinkageTypes::InternalLinkage);
  MergedFunc->setDSOLocal(true);

  if (F1->getSubprogram() == F2->getSubprogram()) {
    MergedFunc->setSubprogram(F1->getSubprogram());
  } else {
    if (Debug)
      errs() << "WARNING: different subprograms!\n";
  }

  MergedFunc->setVisibility(GlobalValue::VisibilityTypes::DefaultVisibility);

  // Exception Handling requires landing pads to have the same personality
  // function
  if (F1->hasPersonalityFn() && F2->hasPersonalityFn()) {
    Constant *PersonalityFn1 = F1->getPersonalityFn();
    Constant *PersonalityFn2 = F2->getPersonalityFn();
    if (PersonalityFn1 == PersonalityFn2) {
      MergedFunc->setPersonalityFn(PersonalityFn1);
    } else {
#ifdef ENABLE_DEBUG_CODE
      PersonalityFn1->dump();
      PersonalityFn2->dump();
#endif
      // errs() << "ERROR: different personality function!\n";
      if (Debug)
        errs() << "WARNING: different personality function!\n";
    }
  } else if (F1->hasPersonalityFn()) {
    // errs() << "Only F1 has PersonalityFn\n";
    // TODO: check if this is valid: merge function with personality with
    // function without it
    MergedFunc->setPersonalityFn(F1->getPersonalityFn());
    if (Debug)
      errs() << "WARNING: only one personality function!\n";
  } else if (F2->hasPersonalityFn()) {
    // errs() << "Only F2 has PersonalityFn\n";
    // TODO: check if this is valid: merge function with personality with
    // function without it
    MergedFunc->setPersonalityFn(F2->getPersonalityFn());
    if (Debug)
      errs() << "WARNING: only one personality function!\n";
  }

  if (F1->hasComdat() && F2->hasComdat()) {
    auto *Comdat1 = F1->getComdat();
    auto *Comdat2 = F2->getComdat();
    if (Comdat1 == Comdat2) {
      MergedFunc->setComdat(Comdat1);
    } else if (Debug) {
      errs() << "WARNING: different comdats!\n";
    }
  } else if (F1->hasComdat()) {
    // errs() << "Only F1 has Comdat\n";
    MergedFunc->setComdat(F1->getComdat()); // TODO: check if this is valid:
                                            // merge function with comdat with
                                            // function without it
    if (Debug)
      errs() << "WARNING: only one comdat!\n";
  } else if (F2->hasComdat()) {
    // errs() << "Only F2 has Comdat\n";
    MergedFunc->setComdat(F2->getComdat()); // TODO: check if this is valid:
                                            // merge function with comdat with
                                            // function without it
    if (Debug)
      errs() << "WARNING: only one comdat!\n";
  }

  if (F1->hasSection()) {
    MergedFunc->setSection(F1->getSection());
  }
}

#pragma endregion

// class RegionAbstract
// This Part is similar with findCandidates in Outliner. We calculate the total

void RegionAbstract::alignMisMatchBlock(BasicBlock *BB,
                                        AlignedSequence<Value *> &AlignedSeq,
                                        RegionMergeInfo &RMI, bool IsLeft) {
  if (IsLeft) {
    AlignedSeq.Data.push_back(
        AlignedSequence<Value *>::Entry(BB, nullptr, false));
    for (Instruction &I : *BB) {
      if (isa<PHINode>(&I) || isa<LandingPadInst>(&I))
        continue;
      RMI.TotalInsts++;
      AlignedSeq.Data.push_back(
          AlignedSequence<Value *>::Entry(&I, nullptr, false));
    }
  } else {
    AlignedSeq.Data.push_back(
        AlignedSequence<Value *>::Entry(nullptr, BB, false));
    for (Instruction &I : *BB) {
      if (isa<PHINode>(&I) || isa<LandingPadInst>(&I))
        continue;
      RMI.TotalInsts++;
      AlignedSeq.Data.push_back(
          AlignedSequence<Value *>::Entry(nullptr, &I, false));
    }
  }
}

void RegionAbstract::alignFullMatchBlock(BasicBlock *BB1, BasicBlock *BB2,
                                         AlignedSequence<Value *> &AlignedSeq,
                                         RegionMergeInfo &RMI) {
  AlignedSeq.Data.push_back(AlignedSequence<Value *>::Entry(
      BB1, BB2, FunctionMerger::match(BB1, BB2)));
  auto It1 = BB1->begin();
  auto It2 = BB2->begin();
  while (isa<PHINode>(*It1) || isa<LandingPadInst>(*It1))
    It1++;
  while (isa<PHINode>(*It2) || isa<LandingPadInst>(*It2))
    It2++;

  while (It1 != BB1->end() && It2 != BB2->end()) {
    Instruction *I1 = &*It1;
    Instruction *I2 = &*It2;
    RMI.TotalInsts++;
    AlignedSeq.Data.push_back(AlignedSequence<Value *>::Entry(I1, I2, true));
    RMI.TotalMatches++;
    if (!I1->isTerminator()) {
      RMI.TotalCoreMatches++;
    }
    It1++;
    It2++;
  }

  if (It1 != BB1->end() || It2 != BB2->end()) {
    BB1->print(errs());
    BB2->print(errs());

    assert(false && "Error: Incorrect block matching!");
  }
}

void RegionAbstract::alignPartialMatchBlock(
    BasicBlock *BB1, BasicBlock *BB2,
    std::vector<std::pair<int[2], int[2]>> &SameRangePairs,
    AlignedSequence<Value *> &AlignedSeq, RegionMergeInfo &RMI) {
  AlignedSeq.Data.push_back(AlignedSequence<Value *>::Entry(
      BB1, BB2, FunctionMerger::match(BB1, BB2)));
  auto It1 = BB1->begin();
  auto It2 = BB2->begin();
  while (isa<PHINode>(*It1) || isa<LandingPadInst>(*It1))
    It1++;
  while (isa<PHINode>(*It2) || isa<LandingPadInst>(*It2))
    It2++;
}

/// definedInCaller - Return true if the specified value is defined in the
/// function being code extracted, but not in the region being extracted.
/// These values must be passed in as live-ins to the function.
static bool definedInCaller(const SetVector<BasicBlock *> &Blocks, Value *V) {
  if (isa<Argument>(V)) {
    return true;
  }
  if (Instruction *I = dyn_cast<Instruction>(V)) {
    if (!Blocks.count(I->getParent())) {
      return true;
    }
  } else {
#ifdef MERGE_CANDIDATES_DEBUG
    // if (!dyn_cast<BasicBlock>(VDef)) {
    //   *FS << "Inst[" << *Inst << "] with non-inst operands: " <<
    //   *VDef
    //       << "\n";
    // }
#endif
  }
  return false;
}

/**
 * @brief Try to analysis regions of candidate, such as that if there are
 * regions in same region.
 * @param Candidate vector of regions (or repeated items)
 */
void RegionAbstract::analysisCandidate(
    std::vector<RepeatedItemInRegion *> &Candidate, RegionMergeInfo &RMI) {
  if (Candidate.size() < 2) {
    return;
  }
  DenseMap<Function *, std::vector<RepeatedItemInRegion *> *> *FuncItemMap =
      new DenseMap<Function *, std::vector<RepeatedItemInRegion *> *>();
  raw_fd_ostream *FS = getOutputStreamOfFile(
      "/home/kp4/SWH/llvm-code-size/build-test/log/CurrentCandidate.log");

  for (RepeatedItemInRegion *RepeatedItem : Candidate) {
    // if in same function
    if (FuncItemMap->find(RepeatedItem->ParentFunc) == FuncItemMap->end()) {
      std::vector<RepeatedItemInRegion *> *Items =
          new std::vector<RepeatedItemInRegion *>();
      Items->push_back(RepeatedItem);
      (*FuncItemMap)[RepeatedItem->ParentFunc] = Items;
    } else {
      (*FuncItemMap)[RepeatedItem->ParentFunc]->push_back(RepeatedItem);
    }

    // find DefsOutofRegion and UsesOutofRegion;
    std::map<Value *, std::vector<Use *>> *DefsFromOut =
        new std::map<Value *, std::vector<Use *>>();
    std::map<Value *, std::vector<Use *>> *UsesFromOut =
        new std::map<Value *, std::vector<Use *>>();
    // todo

    // std::vector<BasicBlock *> &BlocksInRegion =
    // RepeatedItem->MinRegion->Blocks;
    SetVector<BasicBlock *> BlocksInRegion(
        RepeatedItem->MinRegion->Blocks.begin(),
        RepeatedItem->MinRegion->Blocks.end());

    for (BasicBlock *BB : BlocksInRegion) {
      auto It = BB->begin();
      while (It != BB->end()) {
        // Region 内的指令
        Instruction *Inst = &*It;
        for (Use &U : Inst->operands()) {
          // find def
          Value *VDef = U.get();
          if (definedInCaller(BlocksInRegion, VDef)) {

            RMI.Inputs.insert(VDef);
            if (DefsFromOut->find(VDef) == DefsFromOut->end()) {
              (*DefsFromOut)[VDef] = {&U};
            } else {
              (*DefsFromOut)[VDef].push_back(&U);
            }
          }
        }

        for (Use &X : Inst->uses()) {
          User *UU = X.getUser();
          Instruction *II = dyn_cast<Instruction>(UU);
          if (II) {
            if (std::find(BlocksInRegion.begin(), BlocksInRegion.end(),
                          II->getParent()) == BlocksInRegion.end()) {
              //来自外部的使用
              // errs() << "IN-DEF { " << *Inst << " }"
              //        << " -> "
              //        << "{ " << *II << " }"
              //        << " OUT-USE;\n";
              RMI.Outputs.insert(Inst);

              if (UsesFromOut->find(Inst) == UsesFromOut->end()) {
                (*UsesFromOut)[Inst] = {&X};
              } else {
                (*UsesFromOut)[Inst].push_back(&X);
              }
              //如果存在来自外部的使用，则不需要再考虑是否有多个使用，因此这里可以考虑break
              break;
            }
          } else {
#ifdef MERGE_CANDIDATES_DEBUG
            // *FS << "Inst[" << *Inst << "] with non-inst use: " << *II <<
            // "\n"; II->dump();
#endif
          }
        }

        It++;
      }
    }

#ifdef MERGE_CANDIDATES_DEBUG
    *FS << "===Defs out of region===\n";
    for (auto Pair : *DefsFromOut) {
      *FS << "Def[" << *(Pair.first) << "]: {\n";
      for (int I = 0; I < Pair.second.size(); I++) {
        *FS << "\tUse " << I << " : [" << *(Pair.second[I]->getUser()) << "]\n";
      }
      *FS << "}\n";
    }
    *FS << "===Uses out of region===\n";
    for (auto Pair : *UsesFromOut) {
      *FS << "Def[" << *(Pair.first) << "]: {\n";
      for (int I = 0; I < Pair.second.size(); I++) {
        *FS << "\tUse " << I << " : [" << *(Pair.second[I]->getUser()) << "]\n";
      }
      *FS << "}\n";
    }
#endif
    RMI.RegionOutDefMap[RepeatedItem] = DefsFromOut;
    RMI.RegionOutUseMap[RepeatedItem] = UsesFromOut;
  }

  for (auto Pair : *FuncItemMap) {
    if (Pair.second->size() > 1) {
      errs() << Pair.second->size() << " Items In Same Function.\n";
      RMI.HasInFuncRepeated = true;
    }
  }

  if (RMI.HasInFuncRepeated == true) {
    RMI.FuncItemMap = FuncItemMap;
  } else {
    delete FuncItemMap;
  }
}

/**
 * @brief Try to get aligned sequence of two repeated item.
 * @param LeftItem left item to align.
 * @param RightItem right item to align.
 * @param AlignedSeq save result to AlignedSeq.
 * @param Options options of abstract
 */
bool RegionAbstract::alignRepeatedItemInRegion(
    RepeatedItemInRegion *LeftItem, RepeatedItemInRegion *RightItem,
    AlignedSequence<Value *> &AlignedSeq, RegionMergeInfo &RMI,
    const RegionAbstractOptions &Options) {

  unsigned MatchBlockNum = RightItem->ReleatedBlocks.size();

  for (unsigned I = 0; I < MatchBlockNum; I++) {
    // BB is match
    BasicBlock *BB1 = LeftItem->ReleatedBlocks[I];
    if (BB1 == LeftItem->MinRegion->ExitBlock) {
      errs() << "Error\n";
      continue;
    }

    if (RMI.BlockFullMatch[I]) {
      BasicBlock *BB2 = RightItem->ReleatedBlocks[I];
      alignFullMatchBlock(BB1, BB2, AlignedSeq, RMI);
    } else {

      BasicBlock *BB2 = RightItem->ReleatedBlocks[I];
      if (BB2 == RightItem->MinRegion->ExitBlock) {
        errs() << "Error\n";
        continue;
      }
      AlignedSeq.Data.push_back(AlignedSequence<Value *>::Entry(
          BB1, BB2, FunctionMerger::match(BB1, BB2)));
      auto It1 = BB1->begin();
      auto It2 = BB2->begin();
      while (isa<PHINode>(*It1) || isa<LandingPadInst>(*It1))
        It1++;
      while (isa<PHINode>(*It2) || isa<LandingPadInst>(*It2))
        It2++;

      while (It1 != BB1->end() && It2 != BB2->end()) {
        Instruction *I1 = &*It1;
        if (!LeftItem->RepeatedInstSet.contains(I1)) {
          AlignedSeq.Data.push_back(
              AlignedSequence<Value *>::Entry(I1, nullptr, false));
          It1++;
          RMI.TotalInsts++;
          continue;
        }

        Instruction *I2 = &*It2;
        if (!RightItem->RepeatedInstSet.contains(I2)) {
          AlignedSeq.Data.push_back(
              AlignedSequence<Value *>::Entry(nullptr, I2, false));
          It2++;
          RMI.TotalInsts++;
          continue;
        }

        RMI.TotalInsts++;
        AlignedSeq.Data.push_back(
            AlignedSequence<Value *>::Entry(I1, I2, true));
        RMI.TotalMatches++;
        if (!I1->isTerminator()) {
          RMI.TotalCoreMatches++;
        }
        It1++;
        It2++;
      }

      while (It1 != BB1->end()) {
        Instruction *I1 = &*It1;
        assert(!LeftItem->RepeatedInstSet.contains(I1) &&
               "RepeatedInstSet Should not contains this instruction.");
        AlignedSeq.Data.push_back(
            AlignedSequence<Value *>::Entry(I1, nullptr, false));
        It1++;
        RMI.TotalInsts++;
      }
      while (It2 != BB2->end()) {
        Instruction *I2 = &*It2;
        assert(!RightItem->RepeatedInstSet.contains(I2) &&
               "RepeatedInstSet Should not contains this instruction.");
        AlignedSeq.Data.push_back(
            AlignedSequence<Value *>::Entry(nullptr, I2, false));
        It2++;
        RMI.TotalInsts++;
      }
    }
  }

  for (BasicBlock *BB : LeftItem->MinRegion->Blocks) {
    //这一部分match的block已经处理过了, exitBlock要留到最后处理
    if (LeftItem->ReleatedBBSet.contains(BB) ||
        BB == LeftItem->MinRegion->ExitBlock)
      continue;
    // BB is mismatch
    alignMisMatchBlock(BB, AlignedSeq, RMI, true);
  }

  for (BasicBlock *BB : RightItem->MinRegion->Blocks) {
    if (RightItem->ReleatedBBSet.contains(BB) ||
        BB == RightItem->MinRegion->ExitBlock) {
      continue;
    }
    // BB is mismatch
    alignMisMatchBlock(BB, AlignedSeq, RMI, false);
  }

  return false;
}

/**
 * @brief Try to get regions of candidate aligned and merged one by one.
 * @param Candidate vector of regions (or repeated items)
 * @param Options options of abstract
 * @return true if merge susscessfully, otherwise false.
 */
bool RegionAbstract::mergeCandidate(
    std::vector<RepeatedItemInRegion *> &Candidate,
    const RegionAbstractOptions &Options, RegionMergeInfo &RMI) {

  // return false if no need to merge
  if (Candidate.size() < 2) {
    return false;
  }

  if (RMI.HasInFuncRepeated) {
    return false;
  }

  RepeatedItemInRegion *RightItem = Candidate.back();
  Candidate.pop_back();

  unsigned MatchBlockNum = RightItem->ReleatedBlocks.size();
  RMI.BlockFullMatch = std::vector<bool>(MatchBlockNum, true);
  RMI.BlockFullMatch[0] = false;
  RMI.BlockFullMatch[MatchBlockNum - 1] = false;

  std::vector<Type *> Args;
  LLVMContext &Context = M->getContext();

  for (unsigned I = 0; I < Candidate.size(); I++) {
    // swh
    //因为Candidate已经pop出来了一个，所以不需要size-1
    Args.push_back(IntegerType::get(Context, 1));
  }

  Type *ReturnType = Type::getVoidTy(Context);
  FunctionType *FTy =
      FunctionType::get(ReturnType, ArrayRef<Type *>(Args), false);
  std::string Name;
  if (Name.empty()) {
    Name = "_r_a_";
  }
  Function *MergedFunc =
      Function::Create(FTy, // GlobalValue::LinkageTypes::InternalLinkage,
                       GlobalValue::LinkageTypes::PrivateLinkage, Twine(Name),
                       M); // merged.function

  std::vector<Argument *> ArgsList;
  for (Argument &Arg : MergedFunc->args()) {
    ArgsList.push_back(&Arg);
  }

  ValueToValueMapTy VMap;
  bool AnyGenSuccess = false;

  unsigned FuncNum = 0;
  while (!Candidate.empty()) {
    RepeatedItemInRegion *LeftItem = Candidate.back();
    Candidate.pop_back();
// #undef MERGE_CANDIDATES_DEBUG
#ifdef MERGE_CANDIDATES_DEBUG
    raw_fd_ostream *OFSL = getOutputStreamOfFile(
        "/home/kp4/SWH/llvm-code-size/build-test/log/LeftItem.log");
    raw_fd_ostream *OFSR = getOutputStreamOfFile(
        "/home/kp4/SWH/llvm-code-size/build-test/log/RightItem.log");
    LeftItem->printAllInsts(*OFSL);
    RightItem->printAllInsts(*OFSR);

    delete OFSL;
    delete OFSR;
#endif

    AlignedSequence<Value *> AlignedSeq;
    alignRepeatedItemInRegion(LeftItem, RightItem, AlignedSeq, RMI, Options);

    //最后处理出口块，如果为null，则之前应该是tailcall，不需要添加额外的返回指令？最后看效果，有可能还是需要:TODO
    BasicBlock *ExitBB1 = LeftItem->MinRegion->ExitBlock;
    BasicBlock *ExitBB2 = RightItem->MinRegion->ExitBlock;
    if (ExitBB1 != nullptr && ExitBB2 != nullptr) {
      AlignedSeq.Data.push_back(
          AlignedSequence<Value *>::Entry(ExitBB1, ExitBB2, true));
      //不需要处理指令，视指令为空，最后直接添加ret指令即可
    }
#ifdef MERGE_CANDIDATES_DEBUG
    //使用AlignedSeq 创建MergedRegion
    raw_fd_ostream *OFS = getOutputStreamOfFile(
        "/home/kp4/SWH/llvm-code-size/build-test/log/AS.log");
    printAlignedSequence(AlignedSeq, *OFS);
    delete OFS;
    printAlignedSequenceInfo(AlignedSeq);
#endif

    if (ExitBB1 == nullptr || ExitBB2 == nullptr) {
      continue;
    }
    // RMI.CurrnetLeft = LeftItem;
    // RMI.CurrnetRight = RightItem;

    //需要记录每个Item的布尔序列的值
    // Left = Merged Region
    //创建function
    Function *F1 = ExitBB1->getParent();
    Function *F2 = ExitBB2->getParent();
    SetFunctionAttributes(F1, F2, MergedFunc);

    // try to gen
    SWHAbstractor SA(LeftItem->MinRegion->Blocks, RightItem->MinRegion->Blocks);
    SA.setFunctionIdentifier(ArgsList[FuncNum])
        .setEntryPoints(LeftItem->MinRegion->EntryBlock,
                        RightItem->MinRegion->EntryBlock)
        .setMergedFunction(MergedFunc)
        .setMergedEntryPoint(BasicBlock::Create(Context, "entry", MergedFunc))
        .setMergedReturnType(ReturnType)
        .setContext(&Context)
        .setIntPtrType(M->getDataLayout().getIntPtrType(Context));
    if (SA.generate(AlignedSeq, VMap, Options, RMI)) {
      AnyGenSuccess = true;
      FuncNum++;
    }
  }

  //如果没有任何代码生成成功的，直接删除函数
  if (!AnyGenSuccess) {
    MergedFunc->eraseFromParent();
    MergedFunc = nullptr;
    if (Debug)
      errs() << "ERROR: Failed to generate the merged function!\n";
  }

  //衡量创建的function的收益
  //插入了多少条选择指令，

  return false;
}

template <typename BlockListType>
static void CodeGen(BlockListType &Blocks1, BlockListType &Blocks2,
                    BasicBlock *EntryBB1, BasicBlock *EntryBB2,
                    Function *MergedFunc, Value *IsFunc1, BasicBlock *PreBB,
                    AlignedSequence<Value *> &AlignedSeq,
                    ValueToValueMapTy &VMap,
                    std::unordered_map<BasicBlock *, BasicBlock *> &BlocksF1,
                    std::unordered_map<BasicBlock *, BasicBlock *> &BlocksF2,
                    std::unordered_map<Value *, BasicBlock *> &MaterialNodes) {

  auto CloneInst = [](IRBuilder<> &Builder, Function *MF,
                      Instruction *I) -> Instruction * {
    Instruction *NewI = nullptr;
    if (I->getOpcode() == Instruction::Ret) {
      if (MF->getReturnType()->isVoidTy()) {
        NewI = Builder.CreateRetVoid();
      } else {
        NewI = Builder.CreateRet(UndefValue::get(MF->getReturnType()));
      }
    } else {
      // assert(I1->getNumOperands() == I2->getNumOperands() &&
      //      "Num of Operands SHOULD be EQUAL!");
      NewI = I->clone();
      for (unsigned i = 0; i < NewI->getNumOperands(); i++) {
        if (!isa<Constant>(I->getOperand(i)))
          NewI->setOperand(i, nullptr);
      }
      Builder.Insert(NewI);
    }

    // NewI->dropPoisonGeneratingFlags(); //TODO: NOT SURE IF THIS IS VALID

    // TODO: temporarily removing metadata

    SmallVector<std::pair<unsigned, MDNode *>, 8> MDs;
    NewI->getAllMetadata(MDs);
    for (std::pair<unsigned, MDNode *> MDPair : MDs) {
      NewI->setMetadata(MDPair.first, nullptr);
    }

    if (isa<GetElementPtrInst>(NewI)) {
      GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(I);
      // GetElementPtrInst * GEP2 = dyn_cast<GetElementPtrInst>(I2);
      dyn_cast<GetElementPtrInst>(NewI)->setIsInBounds(GEP->isInBounds());
    }

    /*
    if (auto *CB = dyn_cast<CallBase>(I)) {
      auto *NewCB = dyn_cast<CallBase>(NewI);
      auto AttrList = CB->getAttributes();
      NewCB->setAttributes(AttrList);
    }*/

    return NewI;
  };

  for (auto &Entry : AlignedSeq) {
    if (Entry.match()) {

      Instruction *I1 = dyn_cast<Instruction>(Entry.get(0));
      Instruction *I2 = dyn_cast<Instruction>(Entry.get(1));

      std::string BBName =
          (I1 == nullptr) ? "m.label.bb"
                          : (I1->isTerminator() ? "m.term.bb" : "m.inst.bb");

      BasicBlock *MergedBB =
          BasicBlock::Create(MergedFunc->getContext(), BBName, MergedFunc);

      MaterialNodes[Entry.get(0)] = MergedBB;
      MaterialNodes[Entry.get(1)] = MergedBB;

      if (I1 != nullptr && I2 != nullptr) {
        IRBuilder<> Builder(MergedBB);
        Instruction *NewI = CloneInst(Builder, MergedFunc, I1);

        VMap[I1] = NewI;
        VMap[I2] = NewI;
        BlocksF1[MergedBB] = I1->getParent();
        BlocksF2[MergedBB] = I2->getParent();
      } else {
        assert(isa<BasicBlock>(Entry.get(0)) && isa<BasicBlock>(Entry.get(1)) &&
               "Both nodes must be basic blocks!");
        BasicBlock *BB1 = dyn_cast<BasicBlock>(Entry.get(0));
        BasicBlock *BB2 = dyn_cast<BasicBlock>(Entry.get(1));

        VMap[BB1] = MergedBB;
        VMap[BB2] = MergedBB;
        BlocksF1[MergedBB] = BB1;
        BlocksF2[MergedBB] = BB2;

        // IMPORTANT: make sure any use in a blockaddress constant
        // operation is updated correctly
        for (User *U : BB1->users()) {
          if (BlockAddress *BA = dyn_cast<BlockAddress>(U)) {
            VMap[BA] = BlockAddress::get(MergedFunc, MergedBB);
          }
        }
        for (User *U : BB2->users()) {
          if (BlockAddress *BA = dyn_cast<BlockAddress>(U)) {
            VMap[BA] = BlockAddress::get(MergedFunc, MergedBB);
          }
        }

        IRBuilder<> Builder(MergedBB);
        for (Instruction &I : *BB1) {
          if (isa<PHINode>(&I)) {
            VMap[&I] = Builder.CreatePHI(I.getType(), 0);
          }
        }
        for (Instruction &I : *BB2) {
          if (isa<PHINode>(&I)) {
            VMap[&I] = Builder.CreatePHI(I.getType(), 0);
          }
        }
      } // end if(instruction)-else
    }   // end if(match)
  }     // end for(Entry in AlignedSeq)

  auto ChainBlocks = [](BasicBlock *SrcBB, BasicBlock *TargetBB,
                        Value *IsFunc1) {
    IRBuilder<> Builder(SrcBB);
    if (SrcBB->getTerminator() == nullptr) {
      Builder.CreateBr(TargetBB);
    } else {
      BranchInst *Br = dyn_cast<BranchInst>(SrcBB->getTerminator());

      // #ifdef MERGE_CANDIDATES_DEBUG
      //       if (!(Br && Br->isUnconditional())) {
      //         errs() << "=========swh=========\n";
      //         SrcBB->dump();
      //         errs() << "=========swh=========\n";
      //         TargetBB->dump();
      //         errs() << "=========swh=========\n";
      //       }
      // #endif

      assert(Br && Br->isUnconditional() &&
             "Branch should be unconditional at this point!");
      BasicBlock *SuccBB = Br->getSuccessor(0);
      if (SuccBB != TargetBB) {
        Br->eraseFromParent();
        Builder.CreateCondBr(IsFunc1, SuccBB, TargetBB);
      }
    }
  };

  auto ProcessEachFunction =
      [&](BlockListType &Blocks,
          std::unordered_map<BasicBlock *, BasicBlock *> &BlocksFX,
          Value *IsFunc1) {
        for (BasicBlock *BB : Blocks) {
          BasicBlock *LastMergedBB = nullptr;
          BasicBlock *NewBB = nullptr;
          bool HasBeenMerged = MaterialNodes.find(BB) != MaterialNodes.end();
          if (HasBeenMerged) {
            LastMergedBB = MaterialNodes[BB];
          } else {
            std::string BBName = std::string("src.bb");
            NewBB = BasicBlock::Create(MergedFunc->getContext(), BBName,
                                       MergedFunc);
            VMap[BB] = NewBB;
            BlocksFX[NewBB] = BB;

            // IMPORTANT: make sure any use in a blockaddress constant
            // operation is updated correctly
            for (User *U : BB->users()) {
              if (BlockAddress *BA = dyn_cast<BlockAddress>(U)) {
                VMap[BA] = BlockAddress::get(MergedFunc, NewBB);
              }
            }

            // errs() << "NewBB: " << NewBB->getName() << "\n";
            IRBuilder<> Builder(NewBB);
            for (Instruction &I : *BB) {
              if (isa<PHINode>(&I)) {
                VMap[&I] = Builder.CreatePHI(I.getType(), 0);
              }
            }
          }
          for (Instruction &I : *BB) {
            if (isa<LandingPadInst>(&I))
              continue;
            if (isa<PHINode>(&I))
              continue;

            bool HasBeenMerged = MaterialNodes.find(&I) != MaterialNodes.end();
            if (HasBeenMerged) {
              BasicBlock *NodeBB = MaterialNodes[&I];
              if (LastMergedBB) {
                // errs() << "Chaining last merged " << LastMergedBB->getName()
                // << " with " << NodeBB->getName() << "\n";
                // #ifdef MERGE_CANDIDATES_DEBUG
                //   errs() << "=========swh=========\n";
                //   I.dump();
                //   errs() << "=========swh=========\n";
                //   LastMergedBB->dump();
                //   errs() << "=========swh=========\n";
                //   NodeBB->dump();
                //   errs() << "=========swh=========\n";
                // #endif
                ChainBlocks(LastMergedBB, NodeBB, IsFunc1);
              } else {
                IRBuilder<> Builder(NewBB);
                Builder.CreateBr(NodeBB);

                // errs() << "Chaining newBB " << NewBB->getName() << " with "
                // << NodeBB->getName() << "\n";
              }
              // end keep track
              LastMergedBB = NodeBB;
            } else {
              if (LastMergedBB) {
                std::string BBName = std::string("split.bb");
                NewBB = BasicBlock::Create(MergedFunc->getContext(), BBName,
                                           MergedFunc);
                ChainBlocks(LastMergedBB, NewBB, IsFunc1);
                BlocksFX[NewBB] = BB;

                // errs() << "Splitting last merged " << LastMergedBB->getName()
                // << " into " << NewBB->getName() << "\n";
              }
              LastMergedBB = nullptr;

              IRBuilder<> Builder(NewBB);
              Instruction *NewI = CloneInst(Builder, MergedFunc, &I);
              VMap[&I] = NewI;
              // errs() << "Cloned into " << NewBB->getName() << " : " <<
              // NewI->getName() << " " << NewI->getOpcodeName() << "\n";
              // I.dump();
            }
          }
        }
      };
  ProcessEachFunction(Blocks1, BlocksF1, IsFunc1);
  ProcessEachFunction(Blocks2, BlocksF2, IsFunc1);

  BasicBlock *BB1 = dyn_cast<BasicBlock>(VMap[EntryBB1]);
  BasicBlock *BB2 = dyn_cast<BasicBlock>(VMap[EntryBB2]);

  BlocksF1[PreBB] = BB1;
  BlocksF2[PreBB] = BB2;

  if (BB1 == BB2) {
    IRBuilder<> Builder(PreBB);
    Builder.CreateBr(BB1);
  } else {
    IRBuilder<> Builder(PreBB);
    Builder.CreateCondBr(IsFunc1, BB1, BB2);
  }
}

bool SWHAbstractor::generate(AlignedSequence<Value *> &AlignedSeq,
                             ValueToValueMapTy &VMap,
                             const RegionAbstractOptions &Options,
                             RegionMergeInfo &RMI) {

  // std::map<Value *, std::vector<Use *>> *LeftInputValueMap =
  //     RMI.RegionOutDefMap[RMI.CurrnetLeft];
  // std::map<Value *, std::vector<Use *>> *LeftOutputValueMap =
  //     RMI.RegionOutUseMap[RMI.CurrnetLeft];
  // std::map<Value *, std::vector<Use *>> *RightInputValueMap =
  //     RMI.RegionOutDefMap[RMI.CurrnetRight];
  // std::map<Value *, std::vector<Use *>> *RightOutputValueMap =
  //     RMI.RegionOutUseMap[RMI.CurrnetRight];

  LLVMContext &Context = *ContextPtr;
  std::list<Instruction *> LinearOffendingInsts;
  std::set<Instruction *> OffendingInsts;
  std::map<Instruction *, std::map<Instruction *, unsigned>>
      CoalescingCandidates;

  std::vector<Instruction *> ListSelects;

  std::vector<AllocaInst *> Allocas;

  // maps new basic blocks in the merged function to their original
  // correspondents
  std::unordered_map<BasicBlock *, BasicBlock *> BlocksF1;
  std::unordered_map<BasicBlock *, BasicBlock *> BlocksF2;
  std::unordered_map<Value *, BasicBlock *> MaterialNodes;

  CodeGen(Blocks1, Blocks2, EntryBB1, EntryBB2, MergedFunc, IsFunc1, PreBB,
          AlignedSeq, VMap, BlocksF1, BlocksF2, MaterialNodes);

//结束代码生成
#ifdef MERGE_CANDIDATES_DEBUG
  raw_fd_ostream *OFSL = getOutputStreamOfFile(
      "/home/kp4/SWH/llvm-code-size/build-test/log/MergedFunc0.log");
  *OFSL << *MergedFunc << "\n";
  delete OFSL;
#endif

  std::set<BranchInst *> XorBrConds;

  // add by swh
  // params?
  DenseSet<Value *> LeftSourcePtr;
  DenseSet<Value *> RightSourcePtr;
  DenseSet<Value *> TargetPtr;

  for (auto &Entry : AlignedSeq) {
    Instruction *I1 = nullptr;
    Instruction *I2 = nullptr;

    if (Entry.get(0) != nullptr)
      I1 = dyn_cast<Instruction>(Entry.get(0));
    if (Entry.get(1) != nullptr)
      I2 = dyn_cast<Instruction>(Entry.get(1));

    // Skip non-instructions
    if (I1 == nullptr && I2 == nullptr)
      continue;

#ifdef MERGE_CANDIDATES_DEBUG
    if (I1 != nullptr) {
      I1->dump();
    } else {
      errs() << "\tI1 is null\n";
    }
    if (I2 != nullptr) {
      I2->dump();
    } else {
      errs() << "\tI2 is null\n";
    }
#endif

    if (Entry.match()) {
      Instruction *I = I1;
      if (I1->getOpcode() == Instruction::Ret) {
        I = (I1->getNumOperands() >= I2->getNumOperands()) ? I1 : I2;
      } else {
        assert(I1->getNumOperands() == I2->getNumOperands() &&
               "Num of Operands SHOULD be EQUAL\n");
      }

      Instruction *NewI = dyn_cast<Instruction>(VMap[I]);

      bool Handled = false;
      if (!Handled) {
        for (unsigned i = 0; i < I->getNumOperands(); i++) {

          Value *F1V = nullptr;
          Value *V1 = nullptr;
          if (i < I1->getNumOperands()) {
            F1V = I1->getOperand(i);
            // F1V->dump();
            V1 = MapValue(F1V, VMap);
            // assert(V1!=nullptr && "Mapped value should NOT be NULL!");
            if (V1 == nullptr) {
              if (RMI.Inputs.contains(F1V)) {

                V1 = UndefValue::get(F1V->getType());
                errs() << "Test\n";
              } else {
                if (Debug)
                  errs() << "ERROR: Null value mapped: V1 = "
                            "MapValue(I1->getOperand(i), "
                            "VMap);\n";
                return false;
              }
            }
          } else {
            V1 = UndefValue::get(I2->getOperand(i)->getType());
          }

          Value *F2V = nullptr;
          Value *V2 = nullptr;
          if (i < I2->getNumOperands()) {
            F2V = I2->getOperand(i);
            V2 = MapValue(F2V, VMap);
            // assert(V2!=nullptr && "Mapped value should NOT be NULL!");

            if (V2 == nullptr) {
              if (RMI.Inputs.contains(F1V)) {

                V2 = UndefValue::get(F2V->getType());
                errs() << "Test\n";
              } else {
                if (Debug)
                  errs() << "ERROR: Null value mapped: V2 = "
                            "MapValue(I2->getOperand(i), "
                            "VMap);\n";
                return false;
              }
            }

          } else {
            V2 = UndefValue::get(I1->getOperand(i)->getType());
          }

          assert(V1 != nullptr && "Value should NOT be null!");
          assert(V2 != nullptr && "Value should NOT be null!");

          Value *V = V1; // first assume that V1==V2

          // handling just label operands for now
          if (!isa<BasicBlock>(V))
            continue;

          BasicBlock *F1BB = dyn_cast<BasicBlock>(F1V);
          BasicBlock *F2BB = dyn_cast<BasicBlock>(F2V);

          if (V1 != V2) {
            BasicBlock *BB1 = dyn_cast<BasicBlock>(V1);
            BasicBlock *BB2 = dyn_cast<BasicBlock>(V2);

            // auto CacheKey = std::pair<BasicBlock *, BasicBlock *>(BB1, BB2);
            BasicBlock *SelectBB =
                BasicBlock::Create(Context, "bb.select", MergedFunc);
            IRBuilder<> BuilderBB(SelectBB);

            BlocksF1[SelectBB] = I1->getParent();
            BlocksF2[SelectBB] = I2->getParent();

            BuilderBB.CreateCondBr(IsFunc1, BB1, BB2);
            V = SelectBB;
          }

          if (F1BB->isLandingPad() || F2BB->isLandingPad()) {
            LandingPadInst *LP1 = F1BB->getLandingPadInst();
            LandingPadInst *LP2 = F2BB->getLandingPadInst();
            assert((LP1 != nullptr && LP2 != nullptr) &&
                   "Should be both as per the BasicBlock match!");

            BasicBlock *LPadBB =
                BasicBlock::Create(Context, "lpad.bb", MergedFunc);
            IRBuilder<> BuilderBB(LPadBB);

            Instruction *NewLP = LP1->clone();
            BuilderBB.Insert(NewLP);

            BuilderBB.CreateBr(dyn_cast<BasicBlock>(V));

            BlocksF1[LPadBB] = I1->getParent();
            BlocksF2[LPadBB] = I2->getParent();

            VMap[F1BB->getLandingPadInst()] = NewLP;
            VMap[F2BB->getLandingPadInst()] = NewLP;

            V = LPadBB;
          }
          NewI->setOperand(i, V);
        }
      }
    } else { // if(entry.match())-else

      auto AssignLabelOperands =
          [&](Instruction *I,
              std::unordered_map<BasicBlock *, BasicBlock *> &BlocksReMap)
          -> bool {
        Instruction *NewI = dyn_cast<Instruction>(VMap[I]);
        // if (isa<BranchInst>(I))
        //  errs() << "Setting operand in " << NewI->getParent()->getName() << "
        //  : " << NewI->getName() << " " << NewI->getOpcodeName() << "\n";
        for (unsigned i = 0; i < I->getNumOperands(); i++) {
          // handling just label operands for now
          if (!isa<BasicBlock>(I->getOperand(i)))
            continue;
          BasicBlock *FXBB = dyn_cast<BasicBlock>(I->getOperand(i));

          Value *V = MapValue(FXBB, VMap);
          // assert( V!=nullptr && "Mapped value should NOT be NULL!");
          if (V == nullptr)
            return false; // ErrorResponse;

          if (FXBB->isLandingPad()) {

            LandingPadInst *LP = FXBB->getLandingPadInst();
            assert(LP != nullptr && "Should have a landingpad inst!");

            BasicBlock *LPadBB =
                BasicBlock::Create(Context, "lpad.bb", MergedFunc);
            IRBuilder<> BuilderBB(LPadBB);

            Instruction *NewLP = LP->clone();
            BuilderBB.Insert(NewLP);
            VMap[LP] = NewLP;
            BlocksReMap[LPadBB] = FXBB; // I->getParent();

            BuilderBB.CreateBr(dyn_cast<BasicBlock>(V));

            V = LPadBB;
          }

          NewI->setOperand(i, V);
          // if (isa<BranchInst>(NewI))
          //  errs() << "Operand " << i << ": " << V->getName() << "\n";
        }
        return true;
      };

      if (I1 != nullptr && !AssignLabelOperands(I1, BlocksF1)) {
        if (Debug)
          errs() << "ERROR: Value should NOT be null\n";
        // MergedFunc->eraseFromParent();
        return false;
      }
      if (I2 != nullptr && !AssignLabelOperands(I2, BlocksF2)) {
        if (Debug)
          errs() << "ERROR: Value should NOT be null\n";
        // MergedFunc->eraseFromParent();
        return false;
      }
    }
  }

//结束第一遍遍历
#ifdef MERGE_CANDIDATES_DEBUG
  OFSL = getOutputStreamOfFile(
      "/home/kp4/SWH/llvm-code-size/build-test/log/MergedFunc1.log");
  *OFSL << *MergedFunc << "\n";
  delete OFSL;
#endif

  // errs() << "Assigning value operands\n";

  auto MergeValues = [&](Value *V1, Value *V2,
                         Instruction *InsertPt) -> Value * {
    if (V1 == V2)
      return V1;

    if (V1 == ConstantInt::getTrue(Context) &&
        V2 == ConstantInt::getFalse(Context)) {
      return IsFunc1;
    } else if (V1 == ConstantInt::getFalse(Context) &&
               V2 == ConstantInt::getTrue(Context)) {
      IRBuilder<> Builder(InsertPt);
      return Builder.CreateNot(
          IsFunc1); /// TODO: create a single not(IsFunc1) for each merged
                    /// function that needs it
    }

    Instruction *IV1 = dyn_cast<Instruction>(V1);
    Instruction *IV2 = dyn_cast<Instruction>(V2);

    if (IV1 && IV2) {
      // if both IV1 and IV2 are non-merged values
      if (BlocksF2.find(IV1->getParent()) == BlocksF2.end() &&
          BlocksF1.find(IV2->getParent()) == BlocksF1.end()) {
        CoalescingCandidates[IV1][IV2]++;
        CoalescingCandidates[IV2][IV1]++;
      }
    }

    IRBuilder<> Builder(InsertPt);
    Instruction *Sel = (Instruction *)Builder.CreateSelect(IsFunc1, V1, V2);
    ListSelects.push_back(dyn_cast<Instruction>(Sel));
    return Sel;
  };

  auto AssignOperands = [&](Instruction *I, bool IsFuncId1) -> bool {
    Instruction *NewI = dyn_cast<Instruction>(VMap[I]);
    IRBuilder<> Builder(NewI);
    for (unsigned i = 0; i < I->getNumOperands(); i++) {
      if (isa<BasicBlock>(I->getOperand(i)))
        continue;

      Value *V = MapValue(I->getOperand(i), VMap);
      // assert( V!=nullptr && "Mapped value should NOT be NULL!");
      if (V == nullptr) {
        return false; // ErrorResponse;
      }

      // Value *CastedV = createCastIfNeeded(V,
      // NewI->getOperand(i)->getType(), Builder, IntPtrTy);
      NewI->setOperand(i, V);
    }
    return true;
  };

  for (auto &Entry : AlignedSeq) {
    Instruction *I1 = nullptr;
    Instruction *I2 = nullptr;

    if (Entry.get(0) != nullptr)
      I1 = dyn_cast<Instruction>(Entry.get(0));
    if (Entry.get(1) != nullptr)
      I2 = dyn_cast<Instruction>(Entry.get(1));

    if (I1 != nullptr && I2 != nullptr) {

      // Instruction *I1 = dyn_cast<Instruction>(MN->N1->getValue());
      // Instruction *I2 = dyn_cast<Instruction>(MN->N2->getValue());

      Instruction *I = I1;
      if (I1->getOpcode() == Instruction::Ret) {
        I = (I1->getNumOperands() >= I2->getNumOperands()) ? I1 : I2;
      } else {
        assert(I1->getNumOperands() == I2->getNumOperands() &&
               "Num of Operands SHOULD be EQUAL\n");
      }

      Instruction *NewI = dyn_cast<Instruction>(VMap[I]);

      IRBuilder<> Builder(NewI);

      for (unsigned i = 0; i < I->getNumOperands(); i++) {
        if (isa<BasicBlock>(I->getOperand(i)))
          continue;

        Value *V1 = nullptr;
        if (i < I1->getNumOperands()) {
          V1 = MapValue(I1->getOperand(i), VMap);
          // assert(V1!=nullptr && "Mapped value should NOT be NULL!");
          if (V1 == nullptr) {
            if (RMI.Inputs.contains(I1->getOperand(i))) {

              V1 = UndefValue::get(I1->getOperand(i)->getType());
              errs() << "Test\n";
            } else {
              if (Debug)
                errs() << "ERROR: Null value mapped: V1 = "
                          "MapValue(I1->getOperand(i), "
                          "VMap);\n";
              // MergedFunc->eraseFromParent();
              return false;
            }
          }
        } else {
          V1 = UndefValue::get(I2->getOperand(i)->getType());
        }

        Value *V2 = nullptr;
        if (i < I2->getNumOperands()) {
          V2 = MapValue(I2->getOperand(i), VMap);
          // assert(V2!=nullptr && "Mapped value should NOT be NULL!");

          if (V2 == nullptr) {
            if (RMI.Inputs.contains(I2->getOperand(i))) {

              V2 = UndefValue::get(I2->getOperand(i)->getType());
              errs() << "Test\n";
            } else {
              if (Debug)
                errs() << "ERROR: Null value mapped: V2 = "
                          "MapValue(I2->getOperand(i), "
                          "VMap);\n";
              // MergedFunc->eraseFromParent();
              return false;
            }
          }

        } else {
          V2 = UndefValue::get(I1->getOperand(i)->getType());
        }

        assert(V1 != nullptr && "Value should NOT be null!");
        assert(V2 != nullptr && "Value should NOT be null!");

        Value *V = MergeValues(V1, V2, NewI);
        if (V == nullptr) {
          if (Debug) {
            errs() << "Could Not select:\n";
            errs() << "ERROR: Value should NOT be null\n";
          }
          // MergedFunc->eraseFromParent();
#ifdef TIME_STEPS_DEBUG
          TimeCodeGen.stopTimer();
#endif
          return false; // ErrorResponse;
        }

        // Value *CastedV = createCastIfNeeded(V,
        // NewI->getOperand(i)->getType(), Builder, IntPtrTy);
        NewI->setOperand(i, V);

      } // end for operands swh
    }   // end if isomorphic
    else {
      // PDGNode *N = MN->getUniqueNode();
      if (I1 != nullptr && !AssignOperands(I1, true)) {
        if (Debug)
          errs() << "ERROR: Value should NOT be null\n";
          // MergedFunc->eraseFromParent();
#ifdef TIME_STEPS_DEBUG
        TimeCodeGen.stopTimer();
#endif
        return false;
      }
      if (I2 != nullptr && !AssignOperands(I2, false)) {
        if (Debug)
          errs() << "ERROR: Value should NOT be null\n";
          // MergedFunc->eraseFromParent();
#ifdef TIME_STEPS_DEBUG
        TimeCodeGen.stopTimer();
#endif
        return false;
      }
    } // end 'if-else' non-isomorphic

  } // end for nodes

//结束第二遍遍历
#ifdef MERGE_CANDIDATES_DEBUG
  OFSL = getOutputStreamOfFile(
      "/home/kp4/SWH/llvm-code-size/build-test/log/MergedFunc2.log");
  *OFSL << *MergedFunc << "\n";
  delete OFSL;
#endif

  // errs() << "Assigning PHI operands\n";

  auto AssignPHIOperandsInBlock =
      [&](BasicBlock *BB,
          std::unordered_map<BasicBlock *, BasicBlock *> &BlocksReMap) -> bool {
    for (Instruction &I : *BB) {
      if (PHINode *PHI = dyn_cast<PHINode>(&I)) {
        PHINode *NewPHI = dyn_cast<PHINode>(VMap[PHI]);

        std::set<int> FoundIndices;

        for (auto It = pred_begin(NewPHI->getParent()),
                  E = pred_end(NewPHI->getParent());
             It != E; It++) {

          BasicBlock *NewPredBB = *It;

          Value *V = nullptr;

          if (BlocksReMap.find(NewPredBB) != BlocksReMap.end()) {
            int Index = PHI->getBasicBlockIndex(BlocksReMap[NewPredBB]);
            if (Index >= 0) {
              V = MapValue(PHI->getIncomingValue(Index), VMap);
              FoundIndices.insert(Index);
            }
          }

          if (V == nullptr)
            V = UndefValue::get(NewPHI->getType());

          // IRBuilder<> Builder(NewPredBB->getTerminator());
          // Value *CastedV = createCastIfNeeded(V, NewPHI->getType(), Builder,
          // IntPtrTy);
          NewPHI->addIncoming(V, NewPredBB);
        }
        if (FoundIndices.size() != PHI->getNumIncomingValues())
          return false;
      }
    }
    return true;
  };

  for (BasicBlock *BB1 : Blocks1) {
    if (!AssignPHIOperandsInBlock(BB1, BlocksF1)) {
      if (Debug)
        errs() << "ERROR: PHI assignment\n";
        // MergedFunc->eraseFromParent();
#ifdef TIME_STEPS_DEBUG
      TimeCodeGen.stopTimer();
#endif
      return false;
    }
  }
  for (BasicBlock *BB2 : Blocks2) {
    if (!AssignPHIOperandsInBlock(BB2, BlocksF2)) {
      if (Debug)
        errs() << "ERROR: PHI assignment\n";
// MergedFunc->eraseFromParent();
#ifdef TIME_STEPS_DEBUG
      TimeCodeGen.stopTimer();
#endif
      return false;
    }
  }

  // errs() << "Collecting offending instructions\n";
  DominatorTree DT(*MergedFunc);

  for (Instruction &I : instructions(MergedFunc)) {
    if (PHINode *PHI = dyn_cast<PHINode>(&I)) {
      for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++) {
        BasicBlock *BB = PHI->getIncomingBlock(i);
        if (BB == nullptr)
          errs() << "Null incoming block\n";
        Value *V = PHI->getIncomingValue(i);
        if (V == nullptr)
          errs() << "Null incoming value\n";
        if (Instruction *IV = dyn_cast<Instruction>(V)) {
          if (BB->getTerminator() == nullptr) {
            if (Debug)
              errs() << "ERROR: Null terminator\n";
              // MergedFunc->eraseFromParent();
#ifdef TIME_STEPS_DEBUG
            TimeCodeGen.stopTimer();
#endif
            return false;
          }
          if (!DT.dominates(IV, BB->getTerminator())) {
            if (OffendingInsts.count(IV) == 0) {
              OffendingInsts.insert(IV);
              LinearOffendingInsts.push_back(IV);
            }
          }
        }
      }
    } else {
      for (unsigned i = 0; i < I.getNumOperands(); i++) {
        if (I.getOperand(i) == nullptr) {
          // MergedFunc->dump();
          // I.getParent()->dump();
          // errs() << "Null operand\n";
          // I.dump();
          if (Debug)
            errs() << "ERROR: Null operand\n";
            // MergedFunc->eraseFromParent();
#ifdef TIME_STEPS_DEBUG
          TimeCodeGen.stopTimer();
#endif
          return false;
        }
        if (Instruction *IV = dyn_cast<Instruction>(I.getOperand(i))) {
          if (!DT.dominates(IV, &I)) {
            if (OffendingInsts.count(IV) == 0) {
              OffendingInsts.insert(IV);
              LinearOffendingInsts.push_back(IV);
            }
          }
        }
      }
    }
  }

  for (BranchInst *NewBr : XorBrConds) {
    IRBuilder<> Builder(NewBr);
    Value *XorCond = Builder.CreateXor(NewBr->getCondition(), IsFunc1);
    NewBr->setCondition(XorCond);
  }

#ifdef TIME_STEPS_DEBUG
  TimeCodeGen.stopTimer();
#endif

#ifdef TIME_STEPS_DEBUG
  TimeCodeGenFix.startTimer();
#endif

  auto StoreInstIntoAddr = [](Instruction *IV, Value *Addr) {
    IRBuilder<> Builder(IV->getParent());
    if (IV->isTerminator()) {
      BasicBlock *SrcBB = IV->getParent();
      if (InvokeInst *II = dyn_cast<InvokeInst>(IV)) {
        BasicBlock *DestBB = II->getNormalDest();

        Builder.SetInsertPoint(&*DestBB->getFirstInsertionPt());
        // create PHI
        PHINode *PHI = Builder.CreatePHI(IV->getType(), 0);
        for (auto PredIt = pred_begin(DestBB), PredE = pred_end(DestBB);
             PredIt != PredE; PredIt++) {
          BasicBlock *PredBB = *PredIt;
          if (PredBB == SrcBB) {
            PHI->addIncoming(IV, PredBB);
          } else {
            PHI->addIncoming(UndefValue::get(IV->getType()), PredBB);
          }
        }
        Builder.CreateStore(PHI, Addr);
      } else {
        for (auto SuccIt = succ_begin(SrcBB), SuccE = succ_end(SrcBB);
             SuccIt != SuccE; SuccIt++) {
          BasicBlock *DestBB = *SuccIt;

          Builder.SetInsertPoint(&*DestBB->getFirstInsertionPt());
          // create PHI
          PHINode *PHI = Builder.CreatePHI(IV->getType(), 0);
          for (auto PredIt = pred_begin(DestBB), PredE = pred_end(DestBB);
               PredIt != PredE; PredIt++) {
            BasicBlock *PredBB = *PredIt;
            if (PredBB == SrcBB) {
              PHI->addIncoming(IV, PredBB);
            } else {
              PHI->addIncoming(UndefValue::get(IV->getType()), PredBB);
            }
          }
          Builder.CreateStore(PHI, Addr);
        }
      }
    } else {
      Instruction *LastI = nullptr;
      Instruction *InsertPt = nullptr;
      for (Instruction &I : *IV->getParent()) {
        InsertPt = &I;
        if (LastI == IV)
          break;
        LastI = &I;
      }
      if (isa<PHINode>(InsertPt) || isa<LandingPadInst>(InsertPt)) {
        // Builder.SetInsertPoint(&*IV->getParent()->getFirstInsertionPt());
        Builder.SetInsertPoint(IV->getParent()->getTerminator());
      } else
        Builder.SetInsertPoint(InsertPt);

      Builder.CreateStore(IV, Addr);
    }
  };

  auto MemfyInst = [&](std::set<Instruction *> &InstSet) -> AllocaInst * {
    if (InstSet.empty())
      return nullptr;
    IRBuilder<> Builder(&*PreBB->getFirstInsertionPt());
    AllocaInst *Addr = Builder.CreateAlloca((*InstSet.begin())->getType());

    for (Instruction *I : InstSet) {
      for (auto UIt = I->use_begin(), E = I->use_end(); UIt != E;) {
        Use &UI = *UIt;
        UIt++;

        Instruction *User = cast<Instruction>(UI.getUser());

        if (PHINode *PHI = dyn_cast<PHINode>(User)) {
          /// TODO: make sure getOperandNo is getting the correct incoming edge
          IRBuilder<> Builder(
              PHI->getIncomingBlock(UI.getOperandNo())->getTerminator());
          UI.set(Builder.CreateLoad(Addr));
        } else {
          IRBuilder<> Builder(User);
          UI.set(Builder.CreateLoad(Addr));
        }
      }
    }

    for (Instruction *I : InstSet)
      StoreInstIntoAddr(I, Addr);

    return Addr;
  };

  auto isCoalescingProfitable = [&](Instruction *I1, Instruction *I2) -> bool {
    std::set<BasicBlock *> BBSet1;
    std::set<BasicBlock *> UnionBB;
    for (User *U : I1->users()) {
      if (Instruction *UI = dyn_cast<Instruction>(U)) {
        BasicBlock *BB1 = UI->getParent();
        BBSet1.insert(BB1);
        UnionBB.insert(BB1);
      }
    }

    unsigned Intersection = 0;
    for (User *U : I2->users()) {
      if (Instruction *UI = dyn_cast<Instruction>(U)) {
        BasicBlock *BB2 = UI->getParent();
        UnionBB.insert(BB2);
        if (BBSet1.find(BB2) != BBSet1.end())
          Intersection++;
      }
    }

    const float Threshold = 0.7;
    return (float(Intersection) / float(UnionBB.size()) > Threshold);
  };

  auto OptimizeCoalescing =
      [&](Instruction *I, std::set<Instruction *> &InstSet,
          std::map<Instruction *, std::map<Instruction *, unsigned>>
              &CoalescingCandidates,
          std::set<Instruction *> &Visited) {
        Instruction *OtherI = nullptr;
        unsigned Score = 0;
        if (CoalescingCandidates.find(I) != CoalescingCandidates.end()) {
          for (auto &Pair : CoalescingCandidates[I]) {
            if (Pair.second > Score &&
                Visited.find(Pair.first) == Visited.end()) {
              if (isCoalescingProfitable(I, Pair.first)) {
                OtherI = Pair.first;
                Score = Pair.second;
              }
            }
          }
        }
        /*
        if (OtherI==nullptr) {
          for (Instruction *OI : OffendingInsts) {
            if (OI->getType()!=I->getType()) continue;
            if (Visited.find(OI)!=Visited.end()) continue;
            if (CoalescingCandidates.find(OI)!=CoalescingCandidates.end())
        continue; if( (BlocksF2.find(I->getParent())==BlocksF2.end() &&
        BlocksF1.find(OI->getParent())==BlocksF1.end()) ||
                (BlocksF2.find(OI->getParent())==BlocksF2.end() &&
        BlocksF1.find(I->getParent())==BlocksF1.end()) ) { OtherI = OI; break;
            }
          }
        }
        */
        if (OtherI) {
          InstSet.insert(OtherI);
          // errs() << "Coalescing: " << GetValueName(I->getParent()) << ":";
          // I->dump(); errs() << "With: " << GetValueName(OtherI->getParent())
          // << ":"; OtherI->dump();
        }
      };

  // errs() << "Finishing code\n";
  if (MergedFunc != nullptr) {
    // errs() << "Offending: " << OffendingInsts.size() << " ";
    // errs() << ((float)OffendingInsts.size())/((float)AlignedSeq.size()) << "
    // : "; if (OffendingInsts.size()>1000) { if (false) {
    if (((float)OffendingInsts.size()) / ((float)AlignedSeq.size()) > 4.5) {
      if (Debug)
        errs() << "Bailing out\n";
#ifdef TIME_STEPS_DEBUG
      TimeCodeGenFix.stopTimer();
#endif
      return false;
    } else {
      std::set<Instruction *> Visited;
      for (Instruction *I : LinearOffendingInsts) {
        if (Visited.find(I) != Visited.end())
          continue;

        std::set<Instruction *> InstSet;
        InstSet.insert(I);

        for (Instruction *OtherI : InstSet)
          Visited.insert(OtherI);

        AllocaInst *Addr = MemfyInst(InstSet);
        if (Addr)
          Allocas.push_back(Addr);
      }

      // errs() << "Fixed Domination:\n";
      // MergedFunc->dump();

#ifdef OPTIMIZE_SALSSA_CODEGEN
      DominatorTree DT(*MergedFunc);
      PromoteMemToReg(Allocas, DT, nullptr);

      // errs() << "Mem2Reg:\n";
      // MergedFunc->dump();

      if (verifyFunction(*MergedFunc)) {
        errs() << "ERROR: Produced Broken Function!\n";
#ifdef TIME_STEPS_DEBUG
        TimeCodeGenFix.stopTimer();
#endif
        return false;
      }
#ifdef TIME_STEPS_DEBUG
      TimeCodeGenFix.stopTimer();
#endif
#ifdef TIME_STEPS_DEBUG
      TimePostOpt.startTimer();
#endif
      postProcessFunction(*MergedFunc);
#ifdef TIME_STEPS_DEBUG
      TimePostOpt.stopTimer();
#endif
      // errs() << "PostProcessing:\n";
      // MergedFunc->dump();
#endif
    }
  }

  return MergedFunc != nullptr;

  return false;
}

bool RegionAbstract::runOnModule(Module &M) {
  this->M = &M;

  srand(time(NULL));

  RegionAbstractOptions RAOptions = RegionAbstractOptions();

  TargetTransformInfo TTI(M.getDataLayout());

  std::vector<FunctionData> FunctionsToProcess;
  // Sum of instruction counts of Small Functions
  unsigned long SmallFuncCount = 0;
  unsigned long SmallFuncTotalInstrCounts = 0;
  unsigned long SmallFuncTotalEstimateSize = 0;
  unsigned long LargeFuncCount = 0;
  unsigned long LargeFuncTotalInstrCounts = 0;
  unsigned long LargeFuncTotalEstimateSize = 0;

#ifdef RA_TIME_STEPS_DEBUG
  RATimePreProcess.startTimer();
  RATimeTotal.startTimer();
#endif
  for (auto &F : M) {
    // if it is a declaration or is too small, there is no need to merge from
    // it

    // if (!AnalysisAndroid) {
    //   std::vector<std::string> TestVector = {
    //       "_ZN20ComputeNonbondedUtil36calc_pair_energy_merge_"
    //       "fullelect_fepEP9nonbonded",
    //       "_ZN20ComputeNonbondedUtil35calc_pair_energy_slow_fullelect_"
    //       "fepEP9nonbonded"};
    //   if (std::find(TestVector.begin(), TestVector.end(), F.getName()) ==
    //       TestVector.end()) {
    //     //只保留两个例子
    //     continue;
    //   }
    //   errs() << F.getName() << "\n";
    //   errs() << F.getLinkage() << "\n";
    // }

    // TODO:
    //  to add a Filter by the linkage of function
    if (F.isDeclaration() ||
        F.getLinkage() == GlobalValue::AvailableExternallyLinkage) {
      continue;
    }

    auto FuncInsrCount = F.getInstructionCount();
    auto EstimateSize = estimateFunctionSize(&F, &TTI);
    if (FuncInsrCount <= SmallFunctionLimit) {
      SmallFuncCount++;
      SmallFuncTotalInstrCounts += FuncInsrCount;
      SmallFuncTotalEstimateSize += EstimateSize;
      continue;
    }
    LargeFuncCount++;
    LargeFuncTotalInstrCounts += FuncInsrCount;
    LargeFuncTotalEstimateSize += EstimateSize;

    // llvm::printCFG(&F);

    // #ifdef PREPROCESS_DEBUG
    //     if (Debug)
    //       errs() << "FNSize: " << F.getName() << " : " << FuncInsrCount <<
    //       "\n";
    // #endif
    if (F.getName() == "_Z17ix86_match_ccmodeP7rtx_def12machine_mode" ||
        F.getName() == "_Z17ix86_check_movabsP7rtx_defi") {
      errs() << F << "\n";
      F.viewCFG();
    }

    FunctionData FD(&F, EstimateSize);
    FunctionsToProcess.push_back(FD);
  }

#ifdef PREPROCESS_DEBUG
  if (Debug) {
    errs() << ", Count, Instr Count, Estimate Size\n";
    errs() << "Small Function, " << SmallFuncCount << ", "
           << SmallFuncTotalInstrCounts << ", " << SmallFuncTotalEstimateSize
           << "\n";
    errs() << "Large Function, " << LargeFuncCount << ", "
           << LargeFuncTotalInstrCounts << ", " << LargeFuncTotalEstimateSize
           << "\n";
    errs() << "Total, " << LargeFuncCount + SmallFuncCount << ", "
           << LargeFuncTotalInstrCounts + SmallFuncTotalInstrCounts << ", "
           << LargeFuncTotalEstimateSize + SmallFuncTotalEstimateSize << "\n";
  }
#endif

#ifdef RA_TIME_STEPS_DEBUG
  RATimePreProcess.stopTimer();
#endif

  if (RAStopAfter.getValue() == 1) {
    return false;
  }

#ifdef RA_TIME_STEPS_DEBUG
  RATimeMapInstrs.startTimer();
#endif
  IRSimilarity::IRInstrMapper IRMapper = IRSimilarity::IRInstrMapper();
  std::vector<InstrData *> InstrList;
  std::vector<unsigned> IntegerMapping;
  // Prepare instruction mappings for the suffix tree.
  // IRMapper.populateMapperForRA(M, FunctionsToProcess, InstrList,
  //                              IntegerMapping);
  IRMapper.populateDFSMapperForRA(M, FunctionsToProcess, InstrList,
                                  IntegerMapping);
#ifdef RA_TIME_STEPS_DEBUG
  RATimeMapInstrs.stopTimer();
#endif

  std::vector<unsigned> TestTree;
  TestTree.insert(TestTree.end(), IntegerMapping.begin(), IntegerMapping.end());

#ifdef RA_TIME_STEPS_DEBUG
  RATimeAnalysisTree.startTimer();
#endif

  SuffixTree ST(TestTree);
  // SuffixTree ST(IntegerMapping);

  // next analysis New
  RepeatedInfos ReptInfo(ST, RepeatedLowerLimit);
  std::vector<RepeatedInfos::RepeatedSubstringByS *> NewRSList =
      ReptInfo.RSList;

  // Previous process make sure that RSList do not have overlap in one RS;
  // Next we should eliminate the overlap between RSs of RSList;
  std::vector<unsigned> StrMap = ST.Str;

  if (OverlapEliminateMode.getValue() == 0) {
    RepeatedInfos::elimateInterOverlap(NewRSList, StrMap,
                                       CreateFuncOverHead.getValue());
  } else if (OverlapEliminateMode.getValue() == 1) {
    testElimateInterOverlap(NewRSList, StrMap);
  }

  // #ifdef ANALYSIS_TREE_DEBUG
  // unsigned TotalBenefit = analysisOld(ST, RepeatedLowerLimit);
  unsigned TotalBenefit =
      RepeatedInfos::analysisOld(ST, RepeatedLowerLimit, CreateFuncOverHead);

  unsigned NewTotalBenefit = 0;
  std::for_each(NewRSList.begin(), NewRSList.end(),
                [&NewTotalBenefit](RepeatedInfos::RepeatedSubstringByS *RS) {
                  NewTotalBenefit += RS->getPredictBenefit(CreateFuncOverHead);
                });
#ifdef OVERLAP_DEBUG
  std::vector<RepeatedInfos::RepeatedSubstringByS *> NewRSListTest =
      ReptInfo.RSList;
  std::vector<unsigned> StrMapTest = ST.Str;
  testElimateInterOverlap(NewRSListTest, StrMapTest);
  unsigned NewTotalBenefitTest = 0;
  std::for_each(
      NewRSListTest.begin(), NewRSListTest.end(),
      [&NewTotalBenefitTest](RepeatedInfos::RepeatedSubstringByS *RS) {
        NewTotalBenefitTest += RS->getPredictBenefit(CreateFuncOverHead);
      });
#endif
  if (Debug) {
    int TTInstrCount = LargeFuncTotalInstrCounts + SmallFuncTotalInstrCounts;
    errs() << "\nOld, New, InstrCount\n";
    errs() << TotalBenefit << ", " << NewTotalBenefit << ", " << TTInstrCount
           << "\n";

#ifdef OVERLAP_DEBUG
    errs() << "############## New RepeatedSubstrings(Length) ##############\n";
    errs() << NewTotalBenefitTest << "\n";
#endif
    errs() << "\n";

    //打印， 以分析数据分布

    // errs() << "\n############## Start RepeatedSubStr Distribution "
    //           "##############\n";
    // std::for_each(NewRSList.begin(), NewRSList.end(),
    //               [&](RepeatedInfos::RepeatedSubstringByS *RS) {
    //                 errs() << RS->Length << ", " << RS->StartIndices.size()
    //                        << "\n";
    //               });
    // errs() << "############## End RepeatedSubStr Distribution
    // ##############\n";
  }

// #endif
#ifdef RA_TIME_STEPS_DEBUG
  RATimeAnalysisTree.stopTimer();
#endif

  if (RAStopAfter.getValue() == 2) {
    return false;
  }

#ifdef RA_TIME_STEPS_DEBUG
  RATimeGetCandidates.startTimer();
#endif
  RegionAbstractManager *RAM = new RegionAbstractManager(M);
  bool NeedMerge = false;
  if (RAGetAndMerge.getValue()) {
    NeedMerge = RAM->getAndMergeCandidateList(NewRSList, InstrList, *this);
  } else {
    NeedMerge = RAM->getCandidateList(NewRSList, InstrList, *this);
  }

#ifdef RA_TIME_STEPS_DEBUG
  RATimeGetCandidates.stopTimer();
  RATimeMergeCandidate.startTimer();
#endif
  if (NeedMerge)
    RAM->mergeCandidateList();

#ifdef RA_TIME_STEPS_DEBUG
  RATimeMergeCandidate.stopTimer();
#endif

#ifdef RA_TIME_STEPS_DEBUG
  RATimeTotal.stopTimer();
  if (Debug)
    TimerPrinter();
#endif

  return true;
}

void RegionAbstract::getAnalysisUsage(AnalysisUsage &AU) const {
  ModulePass::getAnalysisUsage(AU);
  AU.addRequiredTransitive<RegionInfoPass>();

  // AU.addRequired<ProfileSummaryInfoWrapperPass>();
  // AU.addRequired<BlockFrequencyInfoWrapperPass>();
}

char RegionAbstract::ID = 0;
INITIALIZE_PASS(RegionAbstract, "region-abstract", "New Region Abstraction",
                false, false)

ModulePass *llvm::createRegionAbstractPass() { return new RegionAbstract(); }

#pragma region implementations of Abstractor

SwhRegion::SwhRegion(Region *SourceRegion) {
  EntryBlock = SourceRegion->getEntry();
  ExitBlock = SourceRegion->getExit();
  if (!EntryBlock) {
    errs() << "error";
  }
  if (!ExitBlock) {
    errs() << "error";
  }
  for (auto It = SourceRegion->block_begin(); It != SourceRegion->block_end();
       It++) {
    BasicBlock *BB = *It;
    assert(BB && "Error: Null Basic Block in Region!");
    // Blocks.insert(BB);
    Blocks.push_back(BB);
  }
}

SwhRegion::SwhRegion(std::vector<BasicBlock *> &ContainedBBs) {
  // Function *F = ContainedBBs[0]->getParent();
  // DominatorTree DT(*F);
  // DT.viewGraph();
  // PostDominatorTree PDT(*F);
  //根据支配信息，确定出一个最小的region，但是复杂度较高，暂时先搁置了
  if (ContainedBBs.size() == 1) {
    ExitBlock = ContainedBBs[0];
    EntryBlock = ExitBlock;
    Blocks = ContainedBBs;
    return;
  }

  ExitBlock = ContainedBBs[0];
  EntryBlock = ContainedBBs[1];
  Blocks = ContainedBBs;
  if (Debug)
    errs() << EntryBlock->getName() << "-->" << ExitBlock->getName() << "\n";

  for (BasicBlock *PredBB : predecessors(EntryBlock)) {
    if (is_contained(ContainedBBs, PredBB)) {
      if (Debug)
        errs() << PredBB->getName() << "-->" << EntryBlock->getName() << "\n";
      NeedFullEntry = true;
      break;
    }
  }

  for (BasicBlock *SuccBB : successors(ExitBlock)) {
    if (is_contained(ContainedBBs, SuccBB)) {
      if (Debug)
        errs() << SuccBB->getName() << "-->" << ExitBlock->getName() << "\n";
      NeedFullExit = true;
    } else {
      // assert(FollowBB == nullptr && "We can only deal with one FollowBB!");
      FollowBB.push_back(SuccBB);
    }
  }
}

void RepeatedItemInRegion::printInfo() {
  errs() << "Repeated Item Info:\n";
  errs() << "Repeated Size: " << RepeatedInstrDatas.size() << " Instrs in "
         << ReleatedBlocks.size() << " Blocks. "
         << "\n";
  // errs() << "Func[" << ParentFunc << "]:" << ParentFunc->getName() << "\n";
  errs() << "\t"
         << "Region[" << MinRegion << " : " << MinRegion->Blocks.size() << "]:";
  BasicBlock *BB = MinRegion->getEntry();
  if (BB && BB->hasName()) {
    errs() << BB->getName() << "->";
  } else {
    errs() << getValueName(BB) << "->";
  }
  BB = MinRegion->getExit();
  if (!BB) {
    errs() << "[Function Exit] (Top level region)"
           << "\n";
  } else if (BB->hasName()) {
    errs() << BB->getName() << "\n";
  } else {
    errs() << getValueName(BB) << "\n";
  }
  errs() << "Input Size:" << Inputs.size() << "\nOutput Size:" << Outputs.size()
         << "\n";
  errs() << "Inputs:\n";
  for (auto Input : Inputs) {
    errs() << "\t" << Input->getName() << "\n";
  }

  errs() << "Outputs:\n";
  for (auto Output : Outputs) {
    errs() << "\t" << Output->getName() << "\n";
  }
  // errs() << "\tBlocks In Region: \n";
  // for (BasicBlock *BB : MinRegion->Blocks) {//ReleatedBlocks) {
  //   if (BB && BB->hasName()) {
  //     errs() << BB->getName() << "\t";
  //   } else {
  //     errs() << getValueName(BB) << "\t";
  //   }
  // }
  errs() << "\n";
}

void RepeatedItemInRegion::printAllInsts() {
  // for (InstrData *Inst : RepeatedInstrDatas) {
  //   Inst->Inst->dump();
  // }
  for (Instruction *Inst : RepeatedInstSet) {
    Inst->dump();
  }
}

void RepeatedItemInRegion::printAllInsts(raw_ostream &OFS) {
  for (InstrData *Inst : RepeatedInstrDatas) {
    Inst->Inst->print(OFS, true);
    OFS << "\n";
  }
}

void RepeatedItemInRegion::dumpOnly() {
  // printRegionOnly(ParentFunc);
  // ParentFunc->viewCFG();
  // printCFGOnly(ParentFunc);
  // printCFG(ParentFunc);
  printInfo();
  // printAllInsts();
}

void RepeatedItemInRegion::dump() {
  // printRegion(ParentFunc);
  printInfo();
}

bool RepeatedItemInRegion::getMinRegion(RegionInfo *RI) {

  MinRegion = getMinRegionOfBlocks(RI, ReleatedBlocks, RegionFindingMode);
  if (MinRegion == nullptr) {
    if (Debug) {
      errs() << "Error: Can not get MinRegion for this candidate!\n";
    }
    return false;
  }

  if (MinRegion->NeedFullEntry) {
    EntryBlockSplitMode = 1;
  } else if (MinRegion->EntryBlock == ReleatedBlocks[0]) {
    EntryBlockSplitMode = 2;
  }

  if (MinRegion->NeedFullExit) {
    ExitBlockSplitMode = 1;
  } else if (MinRegion->ExitBlock == ReleatedBlocks.back()) {
    ExitBlockSplitMode = 2;
  }

  return true;
}

bool RepeatedItemInRegion::getMinRegionForIntraBBRS() {
  assert(ReleatedBlocks.size() == 1 && "Should have one releated block!");
  MinRegion = new SwhRegion(ReleatedBlocks);
  EntryBlockSplitMode = 2;
  ExitBlockSplitMode = 2;
  return true;
}

bool RepeatedItemInRegion::updatePhiBlock(BasicBlock *NewBB,
                                          BasicBlock *OldBB) {
  bool NeedSplitPHI = false;
  for (Instruction &Inst : *NewBB) {
    if (Inst.getOpcode() != Instruction::PHI) {
      return true;
    }
    PHINode *Node = dyn_cast<PHINode>(&Inst);

    for (BasicBlock *SourceBB : Node->blocks()) {
      if (ReleatedBBSet.contains(SourceBB)) {
        Instruction *TermInst = SourceBB->getTerminator();
        for (int I = 0; I < TermInst->getNumOperands(); I++) {
          Value *Operand = TermInst->getOperand(I);
          BasicBlock *BB = dyn_cast<BasicBlock>(Operand);
          if (BB && BB == OldBB) {
            TermInst->setOperand(I, NewBB);
          }
        }
      } else {
        if (NeedSplitPHI)
          return false;
        assert(
            !NeedSplitPHI &&
            "TODO:Need Split phi-node if have more than 1 preds in phi-node!");
        Node->replaceIncomingBlockWith(SourceBB, OldBB);
        NeedSplitPHI = true;
      }
    }
  }

  return true;
}

bool RepeatedItemInRegion::splitRegion(
    DenseSet<BasicBlock *> &NonSplittableBlockSet,
    std::set<Function *> &AffectedFuncs) {
  assert(!RegionSplit && "Region already split!");
  // need to update start region entry

  Instruction *StartInst, *EndInst;
  switch (EntryBlockSplitMode) {
  case 1:
    StartInst = &*MinRegion->EntryBlock->begin();
    // TODO:需要做特殊的处理
    return false;
    break;
  case 2:
    StartInst = RepeatedInstrDatas[0]->Inst;
    break;
  default:
  case 0:
    StartInst = MinRegion->EntryBlock->getTerminator();
    break;
  }
  if (StartInst) {
    if (EntryBlockSplitMode == 2) {
      // rs should not start with phi, so we remove it from rs
      //由于不存在直接从phi结点不经过br，跳到新的基本块的情况，所以无需更新Blocks
      while (isa<PHINode>(StartInst)) {
        if (RepeatedInstrDatas.empty())
          return false;
        RepeatedInstrDatas.erase(RepeatedInstrDatas.begin());
        RepeatedInstSet.remove(StartInst);
        StartInst = RepeatedInstrDatas[0]->Inst;
      }
    }

    StartBB = StartInst->getParent();
    if (NonSplittableBlockSet.contains(StartBB)) {
      // error region overlap
      return false;
    }
    PrevBB = StartBB;
    std::string OriginalName = PrevBB->getName().str();
    // StartBB = PrevBB->splitBasicBlock(StartInst, OriginalName + "_pre_ra");
    StartBB = PrevBB->splitBasicBlock(StartInst, OriginalName + "_m");
    SplitedStart = true;
    AffectedFuncs.insert(PrevBB->getParent());

    MinRegion->updateEntry(StartBB);
    if (EntryBlockSplitMode == 1) {
      if (!updatePhiBlock(StartBB, PrevBB))
        return false;
    } else if (EntryBlockSplitMode == 2) {
      ReleatedBlocks[0] = StartBB;
      ReleatedBBSet.erase(PrevBB);
      ReleatedBBSet.insert(StartBB);
    }
  }
  switch (ExitBlockSplitMode) {
  case 1:
    EndInst = &MinRegion->ExitBlock->back();
    // TODO：需要做特殊处理
    EndInst = nullptr;
    FollowBB = MinRegion->FollowBB[0];
    break;
  case 2:
    EndInst = RepeatedInstrDatas[RepeatedInstrDatas.size() - 1]->Inst;
    if (EndInst->isTerminator()) {
      //如果是终结符，则特殊处理
      if (EndInst->getNumSuccessors() == 1) {
        EndBB = EndInst->getParent();
        FollowBB = EndInst->getSuccessor(0);
        EndInst = nullptr;
        //此时不需要分割
      } else {
        //如果有多个succ，则我们认为EndInst不能被abstract,直接从EndInst这里分割
        RepeatedInstrDatas.pop_back();
        RepeatedInstSet.remove(EndInst);
      }
    } else {
      //否则需要向后移动一位用来做截断
      EndInst = EndInst->getNextNode();
    }
    break;
  default:
  case 0:
    EndInst = MinRegion->ExitBlock->getFirstNonPHI();
    break;
  }
  if (EndInst) {
    if (ExitBlockSplitMode == 2) {
      // rs should not follow with phi, so we add it to rs
      //由于不存在直接从phi结点不经过br，跳到新的基本块的情况，所以无需更新Blocks
      while (isa<PHINode>(EndInst)) {
        HasExitExtraPHI = true;
        ExitExtraPHI.insert(EndInst);
        EndInst = EndInst->getNextNode();
      }
    }

    EndBB = EndInst->getParent();
    if (NonSplittableBlockSet.contains(EndBB)) {
      // error region overlap
      return false;
    }

    std::string OriginalName = EndBB->getName().str();
    // FollowBB = EndBB->splitBasicBlock(EndInst, OriginalName + "_post_ra");
    FollowBB = EndBB->splitBasicBlock(EndInst, OriginalName + "_n");
    SplitedEnd = true;
    AffectedFuncs.insert(EndBB->getParent());

    MinRegion->updateExit(EndBB);
    if (ExitBlockSplitMode == 2) {
      //此时，这条终结指令应该不在Region之中，但是为了完整性，这里放入Region中
      Instruction *I = EndBB->getTerminator();
      IRSimilarity::IRInstructionDataList *IDL = nullptr;
      InstrData *ID = new InstrData(*I, true, *IDL, 1);
      RepeatedInstrDatas.push_back(ID);
      RepeatedInstSet.insert(I);
    }
  }

  // update Info
  RegionSplit = true;
  return true;
}

bool RepeatedItemInRegion::splitRepeatedSubstring(
    DenseSet<BasicBlock *> &NonSplittableBlockSet,
    std::set<Function *> &AffectedFuncs) {
  Instruction *RSStartInst = RepeatedInstrDatas.front()->Inst;
  if (EntryBlockSplitMode != 2 &&
      RSStartInst != (&RSStartInst->getParent()->front())) {

    while (isa<PHINode>(RSStartInst)) {
      if (RepeatedInstrDatas.empty())
        return false;
      RepeatedInstrDatas.erase(RepeatedInstrDatas.begin());
      RepeatedInstSet.remove(RSStartInst);
      RSStartInst = RepeatedInstrDatas[0]->Inst;
    }

    BasicBlock *RSStartBB = RSStartInst->getParent();
    BasicBlock *RSPreBB = RSStartBB;
    std::string OriginalName = RSPreBB->getName().str();
    RSStartBB =
        RSPreBB->splitBasicBlock(RSStartInst, OriginalName + "_before_rs");
    AffectedFuncs.insert(RSPreBB->getParent());
    // update ReleatedBlocks and ReleatedBBSet
    ReleatedBlocks[0] = RSStartBB;
    ReleatedBBSet.erase(RSPreBB);
    ReleatedBBSet.insert(RSStartBB);
    // update MinRegion
    MinRegion->Blocks.push_back(RSStartBB);
    NonSplittableBlockSet.insert(RSStartBB);
  }

  Instruction *RSEndInst = RepeatedInstrDatas.back()->Inst;
  if (ExitBlockSplitMode != 2 &&
      RSEndInst != (&RSEndInst->getParent()->back())) {
    BasicBlock *RSEndBB = RSEndInst->getParent();
    BasicBlock *RSPostBB = RSEndBB;
    std::string OriginalName = RSEndBB->getName().str();
    RSPostBB = RSEndBB->splitBasicBlock(RSEndInst->getNextNode(),
                                        OriginalName + "_after_rs");
    AffectedFuncs.insert(RSEndBB->getParent());
    // update RepeatedInstrDatas and RepeatedInstSet
    Instruction *I = RSEndBB->getTerminator();
    IRSimilarity::IRInstructionDataList *IDL = nullptr;
    InstrData *ID = new InstrData(*I, true, *IDL, 1);
    RepeatedInstrDatas.push_back(ID);
    RepeatedInstSet.insert(I);

    // RSPostBB->dump();

    // update MinRegion
    MinRegion->Blocks.push_back(RSPostBB);
    NonSplittableBlockSet.insert(RSPostBB);
  }
  return true;
}

void RepeatedItemInRegion::addInputParam(int InputIndex, int Index) {
  Value *Input = Inputs[InputIndex];
  InputParamMap[Input] = Index;
  if (Index == OccupiedListOfInput->size()) {
    OccupiedListOfInput->push_back(InputIndex);
  } else if (Index < OccupiedListOfInput->size()) {
    (*OccupiedListOfInput)[Index] = InputIndex;
  } else {
    assert(false &&
           "Error: Index should not bigger than size of 'OccupiedList'!");
  }
}

void RepeatedItemInRegion::addOutputParam(int OutputIndex, int Index) {
  Value *Output = Outputs[OutputIndex];
  OutputParamMap[Output] = Index;
  if (Index == OccupiedListOfOutput->size()) {
    OccupiedListOfOutput->push_back(OutputIndex);
  } else if (Index < OccupiedListOfOutput->size()) {
    (*OccupiedListOfOutput)[Index] = OutputIndex;
  } else {
    assert(false &&
           "Error: Index should not bigger than size of 'OccupiedList'!");
  }
}

void RegionMergeInfo::addMatchedBBRelation(unsigned OldBBIndex,
                                           BasicBlock *NewLabelBB) {
  for (int J = 0; J < (*CurrGroup).size(); J++) {
    BasicBlock *OldBB = (*CurrGroup)[J]->ReleatedBlocks[OldBBIndex];
    MatchedValues2NBB[(Value *)OldBB] = NewLabelBB;
    (*NewBB2OldBBList[J])[NewLabelBB] = OldBB;
    VMap[(Value *)OldBB] = NewLabelBB;

    for (User *U : OldBB->users()) {
      if (BlockAddress *BA = dyn_cast<BlockAddress>(U)) {
        VMap[BA] = BlockAddress::get(MergedFunc, NewLabelBB);
      }
    }

    //暂定不在这里处理phi结点
    // IRBuilder<> Builder(NewLabelBB);
    // for (Instruction &I : *OldBB) {
    //   if (isa<PHINode>(&I)) {
    //     VMap[&I] = Builder.CreatePHI(I.getType(), 0);
    //   }
    // }
  }
}

void RegionMergeInfo::addMatchedInstRelation(unsigned OldInstIndex,
                                             Instruction *NewInstruction) {
  for (int J = 0; J < (*CurrGroup).size(); J++) {
    Instruction *OldInst = (*CurrGroup)[J]->RepeatedInstSet[OldInstIndex];
    BasicBlock *NewBB = NewInstruction->getParent();
    MatchedValues2NBB[(Value *)OldInst] = NewBB;
    if (!isa<PHINode>(OldInst))
      (*NewBB2OldBBList[J])[NewBB] = OldInst->getParent();
    VMap[(Value *)OldInst] = NewInstruction;
  }
}

void RegionMergeInfo::buildArgumentsRelation() {
  assert(MergedFunc &&
         "Must build Arguments Relation after MergedFunc Created!");

  // output relation
  for (unsigned I = 0; I < OutputsTypeList.size(); I++) {
    for (RepeatedItemInRegion *Candidate : *CurrGroup) {
      if (I >= Candidate->OccupiedListOfOutput->size()) {
        Candidate->OutputsIndex2LocalIndex[I] = -1;
        continue;
      }
      int LocalIndex = (*Candidate->OccupiedListOfOutput)[I];
      Candidate->OutputsIndex2LocalIndex[I] = LocalIndex;
    }
    if (!RAAggregateArgs.getValue()) {
      Argument *ArgI = MergedFunc->getArg(I + OutputsParamListOffset);
      ArgI->setName(OutputsNameList[I] + ".out");
    }
  }

  // if we use RAAggregateArgs, we need to create GetElementPtrInst int
  // MergedFunc to get real new value. So that we build relation later.
  if (RAAggregateArgs.getValue())
    return;

  // input relation
  for (unsigned I = 0; I < InputsTypeList.size(); I++) {
    Argument *ArgI = MergedFunc->getArg(I + InputsParamListOffset);
    ArgI->setName(InputsNameList[I]);
    for (RepeatedItemInRegion *Candidate : *CurrGroup) {
      if (I >= Candidate->OccupiedListOfInput->size())
        continue;
      int InputIndex = (*Candidate->OccupiedListOfInput)[I];
      if (InputIndex < 0)
        continue;

      Value *Input = Candidate->Inputs[InputIndex];
      // VMap[Input] = ArgI;
      InputsToArgs[Input] = ArgI;
    }
  }
}

BasicBlock *RegionMergeInfo::chainBlocks(BasicBlock *SrcBB,
                                         BasicBlock *TargetBB, Value *IsFunc,
                                         unsigned CaseValue) {
  IRBuilder<> Builder(SrcBB);
  if (SrcBB->getTerminator() == nullptr) {
    Builder.CreateBr(TargetBB);
  } else {
    BranchInst *Br = dyn_cast<BranchInst>(SrcBB->getTerminator());
    assert(Br && "Branch should not be null!");
    if (Br->isUnconditional()) {
      BasicBlock *SuccBB = Br->getSuccessor(0);
      if (SuccBB != TargetBB) {
        Br->eraseFromParent();
        //判断这里是不是写反了
        Builder.CreateCondBr(IsFunc, TargetBB, SuccBB);
      }
    } else {
      //如果是有条件跳转，则添加分割块，并添加有条件跳转指令
      BasicBlock *NewBB = SrcBB->splitBasicBlock(Br, "m.br.bb");
      CreatedOverheadBBs.insert(NewBB);

      BranchInst *UBr = dyn_cast<BranchInst>(SrcBB->getTerminator());
      UBr->eraseFromParent();
      Instruction *I = Builder.CreateCondBr(IsFunc, TargetBB, NewBB);
      CreatedOverheadBranches.insert(I);
      return NewBB;
    }
  }
  return nullptr;
}

void RegionMergeInfo::fillWithEachCandidate(
    std::vector<BasicBlock *> &Blocks,
    std::map<BasicBlock *, BasicBlock *> &BBMap, Value *IsFunc,
    unsigned CaseValue, BasicBlock *NewFuncRoot, BasicBlock *SourcePrevBB) {

  for (BasicBlock *BB : Blocks) {
    BasicBlock *LastMergedBB = nullptr;
    BasicBlock *NewBB = nullptr;
    bool BBHasBeenMerged = MatchedValues2NBB.find(BB) != MatchedValues2NBB.end();
    if (BBHasBeenMerged) {
      LastMergedBB = MatchedValues2NBB[BB];
    } else {
      std::string BBName = "src" + to_string(CaseValue) + ".bb";
      NewBB = BasicBlock::Create(MergedFunc->getContext(), BBName, MergedFunc);
      CreatedMisMatchBBs.insert(NewBB);
      VMap[BB] = NewBB;
      BBMap[NewBB] = BB;

      // IMPORTANT: make sure any use in a blockaddress constant
      // operation is updated correctly
      for (User *U : BB->users()) {
        if (BlockAddress *BA = dyn_cast<BlockAddress>(U)) {
          VMap[BA] = BlockAddress::get(MergedFunc, NewBB);
        }
      }

      // errs() << "NewBB: " << NewBB->getName() << "\n";
      IRBuilder<> Builder(NewBB);
      for (Instruction &I : *BB) {
        if (isa<PHINode>(&I)) {
          VMap[&I] = Builder.CreatePHI(I.getType(), 0);
        }
      }
    }
    for (Instruction &I : *BB) {
      if (isa<LandingPadInst>(&I))
        continue;
      if (isa<PHINode>(&I))
        continue;

      bool HasBeenMerged =
          MatchedValues2NBB.find(&I) != MatchedValues2NBB.end();
      if (HasBeenMerged) {
        BasicBlock *NodeBB = MatchedValues2NBB[&I];
        if (LastMergedBB) {
          // if (LastMergedBB->getTerminator())
          BasicBlock *Via =
              chainBlocks(LastMergedBB, NodeBB, IsFunc, CaseValue);
          if (Via) {
            BBMap[Via] = BB;
          }

        } else {
          IRBuilder<> Builder(NewBB);
          Builder.CreateBr(NodeBB);
        }
        // end keep track
        LastMergedBB = NodeBB;
      } else {
        if (LastMergedBB) {
          std::string BBName = std::string("split.bb");
          NewBB =
              BasicBlock::Create(MergedFunc->getContext(), BBName, MergedFunc);
          CreatedMisMatchBBs.insert(NewBB);

          BasicBlock *Via = chainBlocks(LastMergedBB, NewBB, IsFunc, CaseValue);
          if (Via) {
            BBMap[Via] = BB;
          }
          BBMap[NewBB] = BB;
        }
        LastMergedBB = nullptr;

        IRBuilder<> Builder(NewBB);
        Instruction *NewI = cloneInst(Builder, MergedFunc, &I);
        VMap[&I] = NewI;

        //add for Function Folding
        if (BBHasBeenMerged) {
          MisMatchInsrInMatchedBB.insert(&I);
        }
        //end
        
      }
    }
  }

  BasicBlock *EntryBB = Blocks.size() == 1 ? Blocks[0] : Blocks[1];
  BasicBlock *NewEntryBB = dyn_cast<BasicBlock>(VMap[EntryBB]);
  BBMap[NewFuncRoot] = SourcePrevBB;
  BasicBlock *Via = chainBlocks(NewFuncRoot, NewEntryBB, IsFunc, CaseValue);
  if (Via) {
    BBMap[Via] = SourcePrevBB;
  }
}

bool RegionMergeInfo::AssignLabelOperands(
    Instruction *I, std::map<BasicBlock *, BasicBlock *> &BlocksReMap) {
  Value *NewV = VMap[I];
  if (!NewV) {
    I->dump();
    I->getParent()->dump();
  }
  Instruction *NewI = dyn_cast<Instruction>(VMap[I]);
  for (unsigned i = 0; i < I->getNumOperands(); i++) {
    if (!isa<BasicBlock>(I->getOperand(i)))
      continue;
    BasicBlock *FXBB = dyn_cast<BasicBlock>(I->getOperand(i));
    Value *V = MapValue(FXBB, VMap);
    if (V == nullptr)
      return false;
    if (FXBB->getTerminator() == nullptr)
      return false;
    if (FXBB->isLandingPad()) {
      assert(false && "LandingPad");
      LandingPadInst *LP = FXBB->getLandingPadInst();
      assert(LP != nullptr && "Should have a landingpad inst!");

      BasicBlock *LPadBB =
          BasicBlock::Create(MergedFunc->getContext(), "lpad.bb", MergedFunc);
      CreatedMisMatchBBs.insert(LPadBB);

      IRBuilder<> BuilderBB(LPadBB);

      Instruction *NewLP = LP->clone();
      BuilderBB.Insert(NewLP);
      VMap[LP] = NewLP;
      BlocksReMap[LPadBB] = FXBB; // I->getParent();

      BuilderBB.CreateBr(dyn_cast<BasicBlock>(V));

      V = LPadBB;
    }

    NewI->setOperand(i, V);
  }
  return true;
}

bool RegionMergeInfo::AssignValueOperands(
    Instruction *I, std::map<BasicBlock *, BasicBlock *> &BlocksReMap) {
  Instruction *NewI = dyn_cast<Instruction>(VMap[I]);

  if (isa<PHINode>(I)) {
    return true;
  }

  IRBuilder<> Builder(NewI);
  for (unsigned OperNum = 0; OperNum < I->getNumOperands(); OperNum++) {
    if (isa<BasicBlock>(I->getOperand(OperNum)))
      continue;

    //优先使用参数做映射
    Value *V = MapValue(I->getOperand(OperNum), InputsToArgs);
    if (V == nullptr)
      V = MapValue(I->getOperand(OperNum), VMap);

    assert(V != nullptr && "Mapped value should NOT be NULL!");
    NewI->setOperand(OperNum, V);
  }

  return true;
}

int RegionMergeInfo::addInputParam(Type *ParamType, StringRef ParamName) {
  int Index = InputsTypeList.size();
  InputsTypeList.push_back(ParamType);
  InputsNameList.push_back(ParamName);
  auto Arrangement = InputTypeArrangement.find(ParamType);
  if (Arrangement != InputTypeArrangement.end()) {
    Arrangement->second.push_back(Index);
  } else {
    InputTypeArrangement[ParamType] = {Index};
  }
  return Index;
}

int RegionMergeInfo::addOutputParam(Type *ParamType, StringRef ParamName) {
  int Index = OutputsTypeList.size();
  OutputsTypeList.push_back(ParamType);
  OutputsNameList.push_back(ParamName);
  auto Arrangement = OutputTypeArrangement.find(ParamType);
  if (Arrangement != OutputTypeArrangement.end()) {
    Arrangement->second.push_back(Index);
  } else {
    OutputTypeArrangement[ParamType] = {Index};
  }
  return Index;
}

int RegionMergeInfo::findParamForInput(Value *Input,
                                       std::vector<int> &OccupiedList) {
  auto ArrangementIt = InputTypeArrangement.find(Input->getType());
  if (ArrangementIt == InputTypeArrangement.end()) {
    return -1;
  }
  std::vector<int> &AvailableParams = ArrangementIt->second;
  for (int AvailableParamIndex : AvailableParams) {
    if (OccupiedList[AvailableParamIndex] < 0) {
      return AvailableParamIndex;
    }
  }

  return -1;
}

int RegionMergeInfo::findParamForOutput(Value *Output,
                                        std::vector<int> &OccupiedList) {
  Type *OutputType = RAAggregateArgs.getValue()
                         ? Output->getType()
                         : PointerType::getUnqual(Output->getType());
  auto ArrangementIt = OutputTypeArrangement.find(OutputType);
  if (ArrangementIt == OutputTypeArrangement.end()) {
    return -1;
  }
  std::vector<int> &AvailableParams = ArrangementIt->second;
  for (int AvailableParamIndex : AvailableParams) {
    if (OccupiedList[AvailableParamIndex] < 0) {
      return AvailableParamIndex;
    }
  }

  return -1;
}

bool RegionMergeInfo::getInputsTypeList() {
  for (RepeatedItemInRegion *Candidate : *CurrGroup) {

    Candidate->OccupiedListOfInput =
        new std::vector<int>(InputsTypeList.size(), -1);
    int InputIndex = 0;
    for (Value *Input : Candidate->Inputs) {
      int AvailableParamIndex =
          findParamForInput(Input, *Candidate->OccupiedListOfInput);
      if (AvailableParamIndex < 0) {
        AvailableParamIndex = addInputParam(Input->getType(), Input->getName());
      }
      Candidate->addInputParam(InputIndex, AvailableParamIndex);
      InputIndex++;
    }
  }

  return true;
}

bool RegionMergeInfo::getOutputsTypeList() {

  for (RepeatedItemInRegion *Candidate : *CurrGroup) {

    Candidate->OccupiedListOfOutput =
        new std::vector<int>(OutputsTypeList.size(), -1);
    int OutputIndex = 0;
    for (Value *Output : Candidate->Outputs) {
      int AvailableParamIndex =
          findParamForOutput(Output, *Candidate->OccupiedListOfOutput);
      if (AvailableParamIndex < 0) {
        Type *OutputType = RAAggregateArgs.getValue()
                               ? Output->getType()
                               : PointerType::getUnqual(Output->getType());
        AvailableParamIndex = addOutputParam(OutputType, Output->getName());
      }
      Candidate->addOutputParam(OutputIndex, AvailableParamIndex);
      OutputIndex++;
    }
  }

  return true;
}
int RegionMergeInfo::getCallOverhead() {
  int N = (*CurrGroup).size();
  int TotalOutput = 0;
  int TotalInput = 0;
  for (RepeatedItemInRegion *Cand : *CurrGroup) {
    TotalOutput += Cand->Outputs.size();
    TotalInput += Cand->Inputs.size();
  }
  if (RAAggregateArgs.getValue()) {
    return N /*call*/ + 2 * (TotalInput + N) /*gep + store*/ +
           2 * TotalOutput /*reload*/;
  }
  // if not aggregate
  return N /*call*/ + TotalInput /*alloc*/ + TotalOutput /*reload*/;
}

int RegionMergeInfo::getCallOverheadForBinary(TargetTransformInfo &TTI) {
  int N = (*CurrGroup).size();
  int TotalOutput = 0;
  int TotalInput = 0;
  for (RepeatedItemInRegion *Cand : *CurrGroup) {
    TotalOutput += Cand->Outputs.size();
    TotalInput += Cand->Inputs.size();
  }
  if (RAAggregateArgs.getValue()) {
    return 3 * N /*2call + 1alloc, 1souceid gep=0, store =1*/
           +     // ignore for
                 // debug
                 // 2*TotalInput/*gep
                 // + store*/ +
           2 * TotalOutput /*gep + reload*/;
  }
  // if not aggregate
  return 2 * N /*call */ +
         2 * N * N /* sourceid_alloc+store */ + // ignore for debug2*TotalInput
                                                // /*alloc + store*/
         +TotalOutput /*reload*/;
}

int RegionMergeInfo::getMergeFunctionOverheadForBinary(
    TargetTransformInfo &TTI) {
  int N = (*CurrGroup).size();
  int Entry = RAAggregateArgs.getValue() ? InputsTypeList.size() * 2 + N + 1
                                         : (InputsTypeList.size() + N) * 2;
  Entry += MisMatchEntryCount;
  int Exit = OutputsTypeList.size() * 2 - 1;
  Exit += MisMatchExitCount + 1 /*ret*/;
  int SelectOverhead = RASelectOverhead.getValue() * N;
  int BranchOverhead = MatchBrToMisMatch * (N - 1);
  return Entry + Exit + SelectOverhead + BranchOverhead;
}

int RegionMergeInfo::getMergeFunctionOverhead() {
  int N = (*CurrGroup).size();
  int Entry =
      RAAggregateArgs.getValue() ? (InputsTypeList.size() + 1) * 2 + N : 0;
  Entry += MisMatchEntryCount;
  int Exit = RAAggregateArgs.getValue()
                 ? (OutputsTypeList.size()) * 2 /*gep+store*/
                 : OutputsTypeList.size() /*store*/;
  Exit += MisMatchExitCount + 1 /*ret*/;
  int SelectOverhead = RASelectOverhead.getValue() * N;
  int BranchOverhead = MatchBrToMisMatch * (N - 1);
  return Entry + Exit + SelectOverhead + BranchOverhead;
}

int RegionMergeInfo::getNewBenefit(TargetTransformInfo &TTI) {
  if (CurrGroup->size() < 2) {
    return 0;
  }

  int N = (*CurrGroup).size();
  int MatchLength = (*CurrGroup)[0]->RepeatedInstrDatas.size();

  if (RABenefitModel.getValue() == 0) {
    int MatchBenefit = MatchLength * (N - 1);
    int Overhead = getCallOverhead() + getMergeFunctionOverhead();
    return MatchBenefit - Overhead;
  }

  if (RABenefitModel.getValue() == 1) {
    MatchLength = estimateInstListSize((*CurrGroup)[0]->RepeatedInstSet, TTI);
    int MatchBenefit = MatchLength * (N - 1);
    int Overhead =
        getCallOverheadForBinary(TTI) + getMergeFunctionOverheadForBinary(TTI);
    return MatchBenefit - Overhead;
  }

  int MatchBenefit = MatchLength * (N - 1);
  int Overhead =
      1 + N - 1 + (1 + 2 * OutputsTypeList.size()) * N + OutputsTypeList.size();
  return MatchBenefit > Overhead ? (MatchBenefit - Overhead) : 0;
}

#pragma region getCandidateList
bool RegionAbstractManager::getCandidateList(
    std::vector<RepeatedInfos::RepeatedSubstringByS *> &RSList,
    std::vector<InstrData *> &InstrList, RegionAbstract &RA) {

  //从RSList中找到每个重复的Function、blocks，找到region，判断region之间是否有重叠，有重叠就合并成一个
  for (RepeatedInfos::RepeatedSubstringByS *RS : RSList) {
    //将所有的重复所在的Region、Function取出到局部变量里
    RARegionGroup *RegionGroup = new RARegionGroup();
    bool IntraBlock = false;

    RARegionGroup *FaliedGroup = new RARegionGroup();
    std::vector<RARegionGroup *> FaliedGroups;

    if (Debug)
      errs() << "Region Group info {\n";

    for (unsigned int StartIdx : RS->StartIndices) {
      // ReleatedBBs会被释放，但是因为是深拷贝，所以并不影响
      DenseSet<BasicBlock *> ReleatedBBs;
      RepeatedItemInRegion *Entry = new RepeatedItemInRegion();

      for (unsigned InstrIt = StartIdx; InstrIt < StartIdx + RS->Length;
           InstrIt++) {
        InstrData *ID = InstrList[InstrIt];
        assert(ID->IDType >= 0 &&
               "Error: Instruction Data Type should be positive number!");
        Entry->RepeatedInstrDatas.push_back(ID);
        Entry->RepeatedInstSet.insert(ID->Inst);
        BasicBlock *BB = ID->Inst->getParent();
        if (!ReleatedBBs.contains(BB)) {
          ReleatedBBs.insert(BB);
          Entry->ReleatedBlocks.push_back(BB);
        }
      } // end for 3

      if (ReleatedBBs.size() < 2) {
        if (RAAbstractInBlockCandidate.getValue()) {
          Entry->ParentFunc = (*ReleatedBBs.begin())->getParent();
          if (Entry->getMinRegionForIntraBBRS()) {
            Entry->ReleatedBBSet = ReleatedBBs;
            RegionGroup->push_back(Entry);
            IntraBlock = true;
          } else {
            delete Entry;
          }
        } else {
          delete Entry;
        }
      } else {

        //如果不是块内重复，生成对应的项，并加入
        Entry->ParentFunc = (*ReleatedBBs.begin())->getParent();
        Entry->ReleatedBBSet = ReleatedBBs;
        RegionInfo *RI =
            RegionFindingMode
                ? nullptr
                : &RA.getAnalysis<RegionInfoPass>(*Entry->ParentFunc)
                       .getRegionInfo();

        if (Entry->getMinRegion(RI)) {
          // ReleatedBBs会被释放，但是因为是深拷贝，所以并不影响

          // Entry->ReleatedBlocks.insert(Entry->ReleatedBlocks.end(),
          //                              ReleatedBBs.begin(),
          //                              ReleatedBBs.end());
          RegionGroup->push_back(Entry);
        } else {
          FaliedGroup->push_back(Entry);
        }
      }
    } // end for 2

    if (Debug) {
      errs() << RegionGroup->size() << " RS found region.\n";
      errs() << FaliedGroup->size() << " RS cannot find region.\n";
      errs() << "}\n";
    }

    if (RegionGroup->size() < 2)
      delete RegionGroup;
    else {
      if (IntraBlock)
        IntraBlockCandidateList.push_back(RegionGroup);
      else
        CandidateList.push_back(RegionGroup);
    }

    if (FaliedGroup->size() >= 2) {
      if (Debug)
        errs() << "Retry to find region for failed rs.\n";
    }
  }

  if (RAAbstractInBlockCandidate.getValue()) {
    return !CandidateList.empty() || !IntraBlockCandidateList.empty();
  }
  return !CandidateList.empty();
}
#pragma endregion

#pragma region getAndMergeCandidateList
bool RegionAbstractManager::getAndMergeCandidateList(
    std::vector<RepeatedInfos::RepeatedSubstringByS *> &RSList,
    std::vector<InstrData *> &InstrList, RegionAbstract &RA) {

  for (RepeatedInfos::RepeatedSubstringByS *RS : RSList) {
    RARegionGroup *RegionGroup = new RARegionGroup();
    bool IntraBlock = false;
    RARegionGroup *FailedGroup = new RARegionGroup();

    for (unsigned int StartIdx : RS->StartIndices) {
      DenseSet<BasicBlock *> ReleatedBBs;
      RepeatedItemInRegion *Entry = new RepeatedItemInRegion();

      for (unsigned InstrIt = StartIdx; InstrIt < StartIdx + RS->Length;
           InstrIt++) {
        InstrData *ID = InstrList[InstrIt];
        assert(ID->IDType >= 0 &&
               "Error: Instruction Data Type should be positive number!");
        Entry->RepeatedInstrDatas.push_back(ID);
        Entry->RepeatedInstSet.insert(ID->Inst);
        BasicBlock *BB = ID->Inst->getParent();
        if (!ReleatedBBs.contains(BB)) {
          ReleatedBBs.insert(BB);
          Entry->ReleatedBlocks.push_back(BB);
        }
      } // end for 3

      if (ReleatedBBs.size() < 2) {
        if (RAAbstractInBlockCandidate.getValue()) {
          Entry->ParentFunc = (*ReleatedBBs.begin())->getParent();
          if (Entry->getMinRegionForIntraBBRS()) {
            Entry->ReleatedBBSet = ReleatedBBs;
            RegionGroup->push_back(Entry);
            IntraBlock = true;
          } else {
            delete Entry;
          }
        } else {
          delete Entry;
        }
      } else {

        //如果不是块内重复，生成对应的项，并加入
        Entry->ParentFunc = (*ReleatedBBs.begin())->getParent();
        Entry->ReleatedBBSet = ReleatedBBs;
        RegionInfo *RI =
            RegionFindingMode
                ? nullptr
                : &RA.getAnalysis<RegionInfoPass>(*Entry->ParentFunc)
                       .getRegionInfo();

        if (Entry->getMinRegion(RI)) {
          // ReleatedBBs会被释放，但是因为是深拷贝，所以并不影响

          // Entry->ReleatedBlocks.insert(Entry->ReleatedBlocks.end(),
          //                              ReleatedBBs.begin(),
          //                              ReleatedBBs.end());
          RegionGroup->push_back(Entry);
        } else {
          FailedGroup->push_back(Entry);
        }
      }
    } // end for 2

    if (RegionGroup->size() < 2)
      delete RegionGroup;
    else {
      if (IntraBlock)
        IntraBlockCandidateList.push_back(RegionGroup);
      else
        CandidateList.push_back(RegionGroup);
    }

    if (FailedGroup->size() >= 2 && RAAbstractInBlockCandidate.getValue()) {
      if (Debug)
        errs() << "Retry to find region for failed rs.\n";

      // FailedGroup拆分成多个IntraBBGroup

      //按基本块拆分
      int Left = 0;
      BasicBlock *LeftBB =
          FailedGroup->front()->RepeatedInstSet[0]->getParent();

      for (int Right = 1; Right < RS->Length; Right++) {

        //找到基本块分界线
        if (FailedGroup->front()->RepeatedInstSet[Right]->getParent() !=
            LeftBB) {
          //创建新的RegionGroup
          RARegionGroup *RG = new RARegionGroup();

          for (int a = 0; a < FailedGroup->size(); a++) {
            RepeatedItemInRegion *OldEntry = (*FailedGroup)[a];
            //根据旧的Entry创建新的Entry
            RepeatedItemInRegion *NewEntry = new RepeatedItemInRegion();
            for (int l = Left; l < Right; l++) {
              NewEntry->RepeatedInstrDatas.push_back(
                  OldEntry->RepeatedInstrDatas[l]);
              NewEntry->RepeatedInstSet.insert(OldEntry->RepeatedInstSet[l]);
            }
            BasicBlock *TmpBB = OldEntry->RepeatedInstSet[Left]->getParent();
            NewEntry->ReleatedBBSet.insert(TmpBB);
            NewEntry->ReleatedBlocks.push_back(TmpBB);

            NewEntry->ParentFunc = TmpBB->getParent();
            if (NewEntry->getMinRegionForIntraBBRS()) {
              //创建新的Entry成功，插入RegionGroup
              RG->push_back(NewEntry);
            } else {
              //创建新的Entry失败
              delete NewEntry;
            }
          }

          IntraBlockCandidateList.push_back(RG);

          LeftBB = FailedGroup->front()->RepeatedInstSet[Right]->getParent();
          Left = Right;
        }
      }
    }
  }

  // int CFO = CreateFuncOverHead.getValue();
  auto BenefitOf = [&](RARegionGroup *Group0) -> int {
    int Length = Group0->front()->RepeatedInstrDatas.size();
    if (Group0->empty() || Group0->size() < 2 || Length < 2) {
      return 0;
    }
    unsigned Original = Length * Group0->size();
    unsigned Abstract =
        Length + 1 + Group0->size() + CreateFuncOverHead.getValue();

    if (Original <= Abstract)
      return 0;
    return Original - Abstract;
  };

  llvm::stable_sort(CandidateList, [&](RARegionGroup *LHS, RARegionGroup *RHS) {
    return BenefitOf(LHS) > BenefitOf(RHS);
  });

  llvm::stable_sort(IntraBlockCandidateList,
                    [&](RARegionGroup *LHS, RARegionGroup *RHS) {
                      return BenefitOf(LHS) > BenefitOf(RHS);
                    });

  // llvm::for_each(CandidateList, [&](RARegionGroup *Group0) -> void{
  //   errs() << BenefitOf(Group0) << "\n";
  // });

  if (RAAbstractInBlockCandidate.getValue()) {
    return !CandidateList.empty() || !IntraBlockCandidateList.empty();
  }
  return !CandidateList.empty();
}
#pragma endregion

bool RegionAbstractManager::mergeCandidateList() {
  // int I = 0;
  int TotalBenefit = 0;
  for (RARegionGroup *CandidatePointer : CandidateList) {
    RegionMergeInfo RMI(CandidatePointer);
    analysisRegionGroup(CandidatePointer, RMI);
    int Benefit = getGroupBenefit(RMI);
    int LowerLimit = RAInterBenefitLimit.getValue();
    if (Benefit > LowerLimit) {
      if ((*CandidatePointer->begin())
              ->ReleatedBlocks[0]
              ->getParent()
              ->getName() == "_Z17ix86_match_ccmodeP7rtx_def12machine_mode") {
        (*CandidatePointer->begin())->printAllInsts(errs());
        errs() << "\n";
        (*CandidatePointer)[1]->printAllInsts(errs());
        errs() << "\n" << (*CandidatePointer).size() << "\n";
      }
      if (mergeRegionGroup(CandidatePointer, RMI)) {
        if (Debug)
          errs() << "MF_" << CreatedMergedFunctionNum - 1 << " benefit:\t"
                 << Benefit << "\n";
        TotalBenefit += Benefit;
        if (CreatedMergedFunctionNum >= RACreatedFuncUpperLimit.getValue()) {
          break;
        }
      }
    }
  }

  // abstract intra-basicblock candidate.
  if (RAAbstractInBlockCandidate.getValue() &&
      CreatedMergedFunctionNum < RACreatedFuncUpperLimit.getValue()) {
    for (RARegionGroup *CandidatePointer : IntraBlockCandidateList) {
      RegionMergeInfo RMI(CandidatePointer);
      analysisRegionGroup(CandidatePointer, RMI);
      int Benefit = getGroupBenefit(RMI);
      int LowerLimit =
          RABenefitModel.getValue() == 0 ? 0 : RAIntraBenefitLimit.getValue();
      if (Benefit > LowerLimit) {
        if (mergeRegionGroup(CandidatePointer, RMI)) {
          if (Debug)
            errs() << "Intra-BB MF_" << CreatedMergedFunctionNum - 1
                   << " benefit:\t" << Benefit << "\n";
          TotalBenefit += Benefit;
          if (CreatedMergedFunctionNum >= RACreatedFuncUpperLimit.getValue()) {
            break;
          }
        }
      }
    }
  }

  DeleteDeadBlocks(BlocksToDelete);
  for (Function *Func : AffectedFuncs) {
    postProcessFunction(*Func);
  }

  if (Debug) {
    errs() << "When RAAggregateArgs is :"
           << to_string(RAAggregateArgs.getValue()) << "\n";
    errs() << "Get Total IR Benefit:\t" << to_string(TotalBenefit) << "\n";
  }

  return true;
}

/**
 * @brief Try to analysis regions of candidate, such as that if there are
 * regions in same region.
 * @param Group vector of regions (or repeated items)
 */
void RegionAbstractManager::analysisRegionGroup(RARegionGroup *Group,
                                                RegionMergeInfo &RMI) {
  if (Group->size() < 2) {
    return;
  }
  DenseMap<Function *, RARegionGroup *> *FuncItemMap =
      new DenseMap<Function *, RARegionGroup *>();

  RARegionGroup MergeableRegions;

  for (RepeatedItemInRegion *RegionCandidate : *Group) {

    if (!RegionCandidate->splitRegion(NonSplittableBlockSet, AffectedFuncs)) {
      continue;
    }
    // update NonSplittableBlockSet
    if (RegionCandidate->EntryBlockSplitMode != 2) {
      RMI.MisMatchEntryCount++;
    }
    if (RegionCandidate->ExitBlockSplitMode != 2) {
      RMI.MisMatchExitCount++;
    }
    updateNonSplittableBlockSet(RegionCandidate);
    MergeableRegions.push_back(RegionCandidate);

    // if in same function
    if (FuncItemMap->find(RegionCandidate->ParentFunc) == FuncItemMap->end()) {
      std::vector<RepeatedItemInRegion *> *Items =
          new std::vector<RepeatedItemInRegion *>();
      Items->push_back(RegionCandidate);
      (*FuncItemMap)[RegionCandidate->ParentFunc] = Items;
    } else {
      (*FuncItemMap)[RegionCandidate->ParentFunc]->push_back(RegionCandidate);
    }

    // find DefsOutofRegion and UsesOutofRegion;
    std::map<Value *, std::vector<Use *>> *DefsFromOut =
        new std::map<Value *, std::vector<Use *>>();
    std::map<Value *, std::vector<Use *>> *UsesFromOut =
        new std::map<Value *, std::vector<Use *>>();
    // todo

    // std::vector<BasicBlock *> &BlocksInRegion =
    // RepeatedItem->MinRegion->Blocks;
    SetVector<BasicBlock *> BlocksInRegion(
        RegionCandidate->MinRegion->Blocks.begin(),
        RegionCandidate->MinRegion->Blocks.end());

    for (BasicBlock *BB : BlocksInRegion) {
      auto It = BB->begin();
      while (It != BB->end()) {
        Instruction *Inst = &*It;
        for (Use &U : Inst->operands()) {
          Value *VDef = U.get();
          if (definedInCaller(BlocksInRegion, VDef)) {
            RMI.Inputs.insert(VDef);
            RegionCandidate->Inputs.insert(VDef);
            if (DefsFromOut->find(VDef) == DefsFromOut->end()) {
              (*DefsFromOut)[VDef] = {&U};
            } else {
              (*DefsFromOut)[VDef].push_back(&U);
            }
          }
        }

        for (Use &X : Inst->uses()) {
          User *UU = X.getUser();
          Instruction *II = dyn_cast<Instruction>(UU);
          if (II) {
            if (std::find(BlocksInRegion.begin(), BlocksInRegion.end(),
                          II->getParent()) == BlocksInRegion.end()) {
              RMI.Outputs.insert(Inst);
              RegionCandidate->Outputs.insert(Inst);

              if (UsesFromOut->find(Inst) == UsesFromOut->end()) {
                (*UsesFromOut)[Inst] = {&X};
              } else {
                (*UsesFromOut)[Inst].push_back(&X);
              }
              break;
            }
          }
        }

        It++;
      }
    }
    RMI.RegionOutDefMap[RegionCandidate] = DefsFromOut;
    RMI.RegionOutUseMap[RegionCandidate] = UsesFromOut;
  }

  // update group
  Group->swap(MergeableRegions);
  if (Group->size() < 2)
    return;

  for (auto Pair : *FuncItemMap) {
    if (Pair.second->size() > 1) {
      if (Debug)
        errs() << Pair.second->size() << " Items In Same Function.\n";
      RMI.HasInFuncRepeated = true;
    }
  }

  if (RMI.HasInFuncRepeated == true) {
    RMI.FuncItemMap = FuncItemMap;
  } else {
    delete FuncItemMap;
  }

  for (BasicBlock *BB : (*Group)[0]->ReleatedBlocks) {
    if (BB == (*Group)[0]->MinRegion->ExitBlock)
      continue;
    for (BasicBlock *Succ : successors(BB)) {
      if (!(*Group)[0]->ReleatedBBSet.contains(Succ)) {
        RMI.MatchBrToMisMatch++;
      }
    }
  }

  //获取整个Group的Input和Output
  // after analysis inputs and outputs, try to get the paramsList
  getGroupParamsList(RMI);
}

bool RegionAbstractManager::mergeRegionGroup(RARegionGroup *Group,
                                             RegionMergeInfo &RMI) {
  // return false if no need to merge
  if (Group->size() < 2) {
    return false;
  }

  for (RepeatedItemInRegion *RegionCandidate : *Group) {
    RegionCandidate->splitRepeatedSubstring(NonSplittableBlockSet,
                                            AffectedFuncs);
  }

  CreatedMergedFuncList.push_back(
      createMergedFunc(Group, RMI, CreatedMergedFunctionNum));
  CreatedMergedFunctionNum++;
  if (!fillMergedFunc(Group, RMI)) {
    CreatedMergedFuncList.pop_back();
    CreatedMergedFunctionNum--;
    RMI.MergedFunc->eraseFromParent();
    RMI.MergedFunc = nullptr;
    return false;
  }

  //替换原region
  replaceCodeWithCall(Group, RMI);

  return true;
}

bool RegionAbstractManager::replaceCodeWithCall(RARegionGroup *Group,
                                                RegionMergeInfo &RMI) {

  Module *M = RMI.MergedFunc->getParent();
  LLVMContext &Context = M->getContext();
  const DataLayout &DL = M->getDataLayout();

  std::map<Function *, AllocaInst *> StructAllocaMap;
  // if (Debug) {
  //   errs() << "MF_" << CreatedMergedFunctionNum - 1 << "with arg num: "
  //          << RMI.OutputsParamListOffset + RMI.OutputsTypeList.size();
  //   errs() << " abstract from:\n";
  // }

  for (int CandNum = 0; CandNum < Group->size(); CandNum++) {
    RepeatedItemInRegion *Candidate = (*Group)[CandNum];
    BasicBlock *Header = Candidate->StartBB;
    Function *OldFunction = Candidate->ParentFunc;
    SetVector<BasicBlock *> Blocks(Candidate->MinRegion->Blocks.begin(),
                                   Candidate->MinRegion->Blocks.end());
    if (Debug)
      errs() << "\t" << OldFunction->getName() << "\n";
    // if (Debug && OldFunction->getName() ==
    //                  "_ZNK6dealii10FullMatrixISt7complexIeEE6Tmmul"
    //                  "tIS2_EEvRNS0_IT_EERKS6_b") {
    //   raw_fd_ostream *FS = getOutputStreamOfFile(
    //       "/home/swh/Documents/llvm-code-size/build-test/log/ReplaceBefore" +
    //       to_string(CandNum) + ".log");
    //   *FS << *OldFunction << "\n";
    //   delete FS;
    // }

    // create code replacer
    // This takes place of the original region
    BasicBlock *CodeReplacer = BasicBlock::Create(
        Header->getContext(), "codeRepl", OldFunction, Header);
    IRBuilder<> CodeReplacerBuilder(CodeReplacer);

    std::vector<Value *> Params, StructValues, AllocForOutputs, OldOutputs,
        NewOutputs;
    if (RAAggregateArgs.getValue() && RAAggregateSourceId.getValue()) {
      Value *SourceId = ConstantInt::get(
          Type::getInt32Ty(OldFunction->getContext()), CandNum);
      StructValues.push_back(SourceId);
    } else {
      for (int I = 0; I < Group->size(); I++) {
        Value *SourceId =
            I == CandNum ? ConstantInt::getTrue(
                               IntegerType::get(OldFunction->getContext(), 1))
                         : ConstantInt::getFalse(
                               IntegerType::get(OldFunction->getContext(), 1));
        if (RAAggregateArgs.getValue()) {
          StructValues.push_back(SourceId);
        } else {
          Params.push_back(SourceId);
        }
      }
    }

    for (int I = 0; I < RMI.InputsTypeList.size(); I++) {
      // check if I out of bound
      Value *V = UndefValue::get(RMI.InputsTypeList[I]);
      if (I < Candidate->OccupiedListOfInput->size()) {
        int ValueIdx = (*Candidate->OccupiedListOfInput)[I];
        if (ValueIdx >= 0) {
          V = Candidate->Inputs[ValueIdx];
        }
      }
      assert(V != nullptr && "Params Value should not be null!");
      if (RAAggregateArgs.getValue()) {
        StructValues.push_back(V);
      } else {
        Params.push_back(V);
      }
    }

    for (int I = 0; I < RMI.OutputsTypeList.size(); I++) {
      // check if I out of bound
      Value *V = UndefValue::get(RMI.OutputsTypeList[I]);
      if (I < Candidate->OccupiedListOfOutput->size()) {
        int ValueIdx = (*Candidate->OccupiedListOfOutput)[I];
        if (ValueIdx >= 0) {
          V = Candidate->Outputs[ValueIdx];
          OldOutputs.push_back(V);
          if (!RAAggregateArgs.getValue()) {
            V = new AllocaInst(V->getType(), DL.getAllocaAddrSpace(), nullptr,
                               V->getName() + ".loc",
                               &CodeReplacer->getParent()->front().front());
            AllocForOutputs.push_back(V);
          }
        }
      }
      assert(V != nullptr && "Params Value should not be null!");
      if (RAAggregateArgs.getValue()) {
        // StructValues.push_back(V);
      } else {
        Params.push_back(V);
      }
    }

    AllocaInst *Struct = nullptr;
    if (RAAggregateArgs.getValue()) {
      std::vector<Type *> ArgTypes;
      // find struct
      if (RAUseSingleStruct.getValue() &&
          StructAllocaMap.find(OldFunction) != StructAllocaMap.end()) {
        Struct = StructAllocaMap[OldFunction];
      } else {
        Struct = new AllocaInst(RMI.StructTy, DL.getAllocaAddrSpace(), nullptr,
                                "RAStructArg",
                                &CodeReplacer->getParent()->front().front());

        StructAllocaMap[OldFunction] = Struct;
      }

      // use struct
      Params.push_back(Struct);
      Value *Idx[2];
      Idx[0] = Constant::getNullValue(Type::getInt32Ty(Context));
      for (unsigned X = 0, E = RMI.OutputsParamListOffset; X != E; ++X) {
        Idx[1] = ConstantInt::get(Type::getInt32Ty(Context), X);
        GetElementPtrInst *GEP = GetElementPtrInst::Create(
            RMI.StructTy, Struct, Idx, "gep_" + StructValues[X]->getName());
        CodeReplacer->getInstList().push_back(GEP);
        StoreInst *SI = new StoreInst(StructValues[X], GEP, CodeReplacer);
      }
    }

    CallInst *CI = CodeReplacerBuilder.CreateCall(RMI.MergedFunc, Params);
    CI->setIsNoInline();
    if (CodeReplacer->getParent()->getSubprogram()) {
      if (auto DL =
              RMI.MergedFunc->getEntryBlock().getTerminator()->getDebugLoc())
        CI->setDebugLoc(DL);
    }

    if (RAAggregateArgs.getValue()) {
      Value *Idx[2];
      Idx[0] = Constant::getNullValue(Type::getInt32Ty(Context));

      for (unsigned I = 0; I < Candidate->Outputs.size(); I++) {
        Value *Output = Candidate->Outputs[I];
        int OutArgIndex = Candidate->OutputParamMap[Output];
        Idx[1] = ConstantInt::get(Type::getInt32Ty(Context),
                                  OutArgIndex + RMI.OutputsParamListOffset);
        GetElementPtrInst *GEP = GetElementPtrInst::Create(
            RMI.StructTy, Struct, Idx, "gep_output_" + to_string(OutArgIndex));
        CodeReplacer->getInstList().push_back(GEP);
        LoadInst *Reload =
            new LoadInst(Output->getType(), GEP, Output->getName() + ".reload",
                         CodeReplacer);
        std::vector<User *> Users(Output->user_begin(), Output->user_end());
        for (unsigned U = 0, E = Users.size(); U != E; ++U) {
          Instruction *Inst = cast<Instruction>(Users[U]);
          if (!Blocks.count(Inst->getParent()))
            Inst->replaceUsesOfWith(Output, Reload);
        }
      }
    } else {
      // Reload the outputs passed in by reference.
      for (unsigned I = 0; I < AllocForOutputs.size(); I++) {
        Value *AI = AllocForOutputs[I];
        Value *Output = OldOutputs[I];
        LoadInst *Reload = new LoadInst(
            Output->getType(), AI, Output->getName() + ".reload", CodeReplacer);
        NewOutputs.push_back(Reload);
        std::vector<User *> Users(Output->user_begin(), Output->user_end());
        for (unsigned U = 0, E = Users.size(); U != E; ++U) {
          Instruction *Inst = cast<Instruction>(Users[U]);
          if (!Blocks.count(Inst->getParent()))
            Inst->replaceUsesOfWith(Output, Reload);
        }
      }
    }

    // fix start
    std::vector<User *> Users(Header->user_begin(), Header->user_end());
    for (auto &U : Users)
      if (Instruction *I = dyn_cast<Instruction>(U))
        if (I->isTerminator() && I->getFunction() == OldFunction &&
            !Blocks.count(I->getParent()))
          I->replaceUsesOfWith(Header, CodeReplacer);

    // fix end
    BasicBlock *ExitBB = Candidate->EndBB;
    BasicBlock *OutSucc = nullptr;
    for (BasicBlock *Succ : successors(ExitBB)) {
      if (Blocks.contains(Succ))
        continue;
      assert(!OutSucc && "Should have only one out successor!");
      OutSucc = Succ;
    }
    assert(OutSucc && "Out successor of exit basicblock should not be null!");
    CodeReplacerBuilder.CreateBr(OutSucc);
    // fix phi
    OutSucc->replacePhiUsesWith(ExitBB, CodeReplacer);
    if (Instruction *TI = ExitBB->getTerminator()) {
      TI->eraseFromParent();
    }

    // delete all in region
    // for (BasicBlock *Block : Blocks) {
    //   // Block->dump();

    //   std::vector<User *> BBUsers(Block->user_begin(), Block->user_end());
    //   for (auto &U : BBUsers) {
    //     if (Instruction *I = dyn_cast<Instruction>(U)) {
    //       if (I->isTerminator() && I->getFunction() == OldFunction &&
    //           Blocks.count(I->getParent()))
    //         I->eraseFromParent();
    //       else {
    //         I->dump();
    //         I->getParent()->dump();
    //         I->replaceUsesOfWith(Block, CodeReplacer);
    //         assert(false);
    //       }
    //     } else {
    //       U->dump();
    //       U->replaceUsesOfWith(Block, CodeReplacer);
    //       assert(false);
    //     }
    //   }
    // }
    // bool before = BlocksToDelete.size() < 1081;
    BlocksToDelete.insert(BlocksToDelete.end(), Blocks.begin(), Blocks.end());
    // if (before && BlocksToDelete.size() >= 1081 ){
    //   BasicBlock *BB = BlocksToDelete[1080];
    //   BB->dump();
    //   printCFGOnly(BB->getParent());
    //   for (BasicBlock *succ : successors(BB)) {
    //     succ->dump();
    //   }
    // }

    // Delete after all finished
    // DeleteDeadBlocks(Blocks.getArrayRef());

    // if (Debug && OldFunction->getName() ==
    //                  "_ZNK6dealii10FullMatrixISt7complexIeEE6Tmmul"
    //                  "tIS2_EEvRNS0_IT_EERKS6_b") {
    //   raw_fd_ostream *FS = getOutputStreamOfFile(
    //       "/home/swh/Documents/llvm-code-size/build-test/log/ReplaceAfter" +
    //       to_string(CandNum) + ".log");
    //   *FS << *OldFunction << "\n";
    //   delete FS;
    // }
  }

  return true;
}

static void inheritFuncAttr(Function *OldFunction, Function *NewFunction) {
  // If the old function is no-throw, so is the new one.
  if (OldFunction->doesNotThrow())
    NewFunction->setDoesNotThrow();

  // Inherit the uwtable attribute if we need to.
  if (OldFunction->hasUWTable())
    NewFunction->setHasUWTable();

  // Inherit all of the target dependent attributes and white-listed
  // target independent attributes.
  //  (e.g. If the extracted region contains a call to an x86.sse
  //  instruction we need to make sure that the extracted region has the
  //  "target-features" attribute allowing it to be lowered.
  // FIXME: This should be changed to check to see if a specific
  //           attribute can not be inherited.
  for (const auto &Attr : OldFunction->getAttributes().getFnAttributes()) {
    if (Attr.isStringAttribute()) {
      if (Attr.getKindAsString() == "thunk")
        continue;
    } else
      switch (Attr.getKindAsEnum()) {
      // Those attributes cannot be propagated safely. Explicitly list them
      // here so we get a warning if new attributes are added. This list also
      // includes non-function attributes.
      case Attribute::Alignment:
      case Attribute::AllocSize:
      case Attribute::ArgMemOnly:
      case Attribute::Builtin:
      case Attribute::ByVal:
      case Attribute::Convergent:
      case Attribute::Dereferenceable:
      case Attribute::DereferenceableOrNull:
      // case Attribute::ElementType:
      case Attribute::InAlloca:
      case Attribute::InReg:
      case Attribute::InaccessibleMemOnly:
      case Attribute::InaccessibleMemOrArgMemOnly:
      case Attribute::JumpTable:
      case Attribute::Naked:
      case Attribute::Nest:
      case Attribute::NoAlias:
      case Attribute::NoBuiltin:
      case Attribute::NoCapture:
      case Attribute::NoMerge:
      case Attribute::NoReturn:
      case Attribute::NoSync:
      case Attribute::NoUndef:
      case Attribute::None:
      case Attribute::NonNull:
      case Attribute::Preallocated:
      case Attribute::ReadNone:
      case Attribute::ReadOnly:
      case Attribute::Returned:
      case Attribute::ReturnsTwice:
      case Attribute::SExt:
      case Attribute::Speculatable:
      case Attribute::StackAlignment:
      case Attribute::StructRet:
      case Attribute::SwiftError:
      case Attribute::SwiftSelf:
      // case Attribute::SwiftAsync:
      case Attribute::WillReturn:
      case Attribute::WriteOnly:
      case Attribute::ZExt:
      case Attribute::ImmArg:
      case Attribute::ByRef:
      case Attribute::EndAttrKinds:
      case Attribute::EmptyKey:
      case Attribute::TombstoneKey:
        continue;
      // Those attributes should be safe to propagate to the extracted function.
      case Attribute::AlwaysInline:
      case Attribute::Cold:
      // case Attribute::Hot:
      case Attribute::NoRecurse:
      case Attribute::InlineHint:
      case Attribute::MinSize:
      // case Attribute::NoCallback:
      case Attribute::NoDuplicate:
      case Attribute::NoFree:
      case Attribute::NoImplicitFloat:
      case Attribute::NoInline:
      case Attribute::NonLazyBind:
      case Attribute::NoRedZone:
      case Attribute::NoUnwind:
      // case Attribute::NoSanitizeCoverage:
      case Attribute::NullPointerIsValid:
      case Attribute::OptForFuzzing:
      case Attribute::OptimizeNone:
      case Attribute::OptimizeForSize:
      case Attribute::SafeStack:
      case Attribute::ShadowCallStack:
      case Attribute::SanitizeAddress:
      case Attribute::SanitizeMemory:
      case Attribute::SanitizeThread:
      case Attribute::SanitizeHWAddress:
      case Attribute::SanitizeMemTag:
      case Attribute::SpeculativeLoadHardening:
      case Attribute::StackProtect:
      case Attribute::StackProtectReq:
      case Attribute::StackProtectStrong:
      case Attribute::StrictFP:
      case Attribute::UWTable:
      // case Attribute::VScaleRange:
      case Attribute::NoCfCheck:
      case Attribute::MustProgress:
        // case Attribute::NoProfile:
        break;
      }

    NewFunction->addFnAttr(Attr);
  }
}

Function *
RegionAbstractManager::createMergedFunc(RARegionGroup *Group,
                                        RegionMergeInfo &RMI,
                                        unsigned int FunctionNameSuffix) {
  assert(!RMI.MergedFunc && "Function is already defined!");
  LLVMContext &Context = M.getContext();

  std::vector<Type *> ParamTy;

  if (RAAggregateArgs.getValue() && RAAggregateSourceId.getValue()) {
    // when RAAggregateSourceId is true, use a i32 to identify source.
    ParamTy.push_back(IntegerType::get(Context, 32));
    RMI.InputsParamListOffset++;
  } else {
    for (int I = 0; I < Group->size(); I++) {
      ParamTy.push_back(IntegerType::get(Context, 1));
      RMI.InputsParamListOffset++;
    }
  }

  ParamTy.insert(ParamTy.end(), RMI.InputsTypeList.begin(),
                 RMI.InputsTypeList.end());

  RMI.OutputsParamListOffset =
      RMI.InputsParamListOffset + RMI.InputsTypeList.size();

  ParamTy.insert(ParamTy.end(), RMI.OutputsTypeList.begin(),
                 RMI.OutputsTypeList.end());

  // errs() << "ParamSize:" << ParamTy.size() << "\n";
  // for (RepeatedItemInRegion *Region : *Group) {
  //   if (Region->MinRegion->Blocks.size() < 10) {
  //     Region->dumpOnly();
  //   }
  // }

  if (RAAggregateArgs.getValue()) {
    RMI.StructTy = StructType::get(M.getContext(), ParamTy);
    ParamTy.clear();
    ParamTy.push_back(PointerType::getUnqual(RMI.StructTy));
  }

  RMI.MergedFuncType =
      FunctionType::get(Type::getVoidTy(M.getContext()), ParamTy, false);

  GlobalValue::LinkageTypes RALinkageType = AbstractToPrivateLinkage.getValue()
                                                ? GlobalValue::PrivateLinkage
                                                : GlobalValue::InternalLinkage;
  RMI.MergedFunc =
      Function::Create(RMI.MergedFuncType, RALinkageType,
                       "ra_ir_func_" + std::to_string(FunctionNameSuffix), M);

  RMI.MergedFunc->addFnAttr(Attribute::OptimizeForSize);
  RMI.MergedFunc->addFnAttr(Attribute::MinSize);

  for (RepeatedItemInRegion *Candidate : *Group) {
    Function *OldFunc = Candidate->ParentFunc;
    inheritFuncAttr(OldFunc, RMI.MergedFunc);
  }

  // build releation for Arguments
  RMI.buildArgumentsRelation();

  return RMI.MergedFunc;
}

bool RegionAbstractManager::fillMergedFunc(RARegionGroup *Group,
                                           RegionMergeInfo &RMI) {
  // init
  // SmallPtrSet<BasicBlock *, 1> ExitBlocks;
  Function *NewFunction = RMI.MergedFunc;
  BasicBlock *NewFuncRoot =
      BasicBlock::Create(NewFunction->getContext(), "newFuncRoot");
  NewFunction->getBasicBlockList().push_back(NewFuncRoot);
  BasicBlock *NewFuncExit =
      BasicBlock::Create(NewFunction->getContext(), "newFuncExit");
  NewFunction->getBasicBlockList().push_back(NewFuncExit);

  std::vector<Instruction *> ListSelects;
  std::vector<AllocaInst *> Allocas;
  std::vector<unsigned> MatchedPHINodes;

  std::list<Instruction *> LinearOffendingInsts;
  std::set<Instruction *> OffendingInsts;

  std::vector<Value *> SourceIds;

  for (RepeatedItemInRegion *Candidate : *Group) {
    assert(Candidate->FollowBB != nullptr && "FollowBB is null!");
    RMI.VMap[Candidate->FollowBB] = NewFuncExit;
  }

  for (int I = 0; I < (*Group).size(); I++) {
    std::map<BasicBlock *, BasicBlock *> *MapI =
        new std::map<BasicBlock *, BasicBlock *>();
    RMI.NewBB2OldBBList.push_back(MapI);
  }
  // finish init

  // build relation for AggregateArgs Value
  if (RAAggregateArgs.getValue()) {
    Argument *Arg0 = NewFunction->getArg(0);
    Value *Idx[2];
    Idx[0] =
        Constant::getNullValue(Type::getInt32Ty(NewFuncRoot->getContext()));
    // source id
    if (RAAggregateSourceId) {
      Idx[1] = ConstantInt::get(Type::getInt32Ty(NewFuncRoot->getContext()), 0);
      GetElementPtrInst *GEP = GetElementPtrInst::Create(
          RMI.StructTy, Arg0, Idx, "gep_source_num", NewFuncRoot);
      Value *SourceNum = new LoadInst(RMI.StructTy->getElementType(0), GEP,
                                      "source_num", NewFuncRoot);
      for (int I = 0; I < Group->size(); I++) {
        Value *SourceIdInt =
            ConstantInt::get(Type::getInt32Ty(NewFuncRoot->getContext()), I);
        CmpInst *SourceId = CmpInst::Create(
            Instruction::ICmp, ICmpInst::ICMP_EQ, SourceNum, SourceIdInt,
            "sourceid_" + to_string(I), NewFuncRoot);
        SourceIds.push_back(SourceId);
      }
    } else {
      for (int I = 0; I < RMI.InputsParamListOffset; I++) {
        Idx[1] =
            ConstantInt::get(Type::getInt32Ty(NewFuncRoot->getContext()), I);
        GetElementPtrInst *GEP = GetElementPtrInst::Create(
            RMI.StructTy, Arg0, Idx, "gep_sourceid" + to_string(I),
            NewFuncRoot);
        Value *SourceId = new LoadInst(RMI.StructTy->getElementType(I), GEP,
                                       "sourceid_" + to_string(I), NewFuncRoot);
        SourceIds.push_back(SourceId);
      }
    }

    // inputs
    for (int I = 0; I < RMI.InputsTypeList.size(); I++) {
      Idx[1] = ConstantInt::get(Type::getInt32Ty(NewFuncRoot->getContext()),
                                I + RMI.InputsParamListOffset);
      GetElementPtrInst *GEP = GetElementPtrInst::Create(
          RMI.StructTy, Arg0, Idx, "gep_input_" + RMI.InputsNameList[I],
          NewFuncRoot);
      Value *NewV = new LoadInst(
          RMI.StructTy->getElementType(I + RMI.InputsParamListOffset), GEP,
          "input_" + to_string(I), NewFuncRoot);

      for (RepeatedItemInRegion *Candidate : *Group) {
        if (I >= Candidate->OccupiedListOfInput->size())
          continue;
        int InputIndex = (*Candidate->OccupiedListOfInput)[I];
        if (InputIndex < 0)
          continue;

        Value *Input = Candidate->Inputs[InputIndex];
        RMI.InputsToArgs[Input] = NewV;
      }
    }
  } else {
    for (int I = 0; I < (*Group).size(); I++) {
      SourceIds.push_back(NewFunction->getArg(I));
    }
  }

  // Fill In Content
  unsigned CurrentMatchedInstIndex = 0;
  // 1. fill in content for match part
  for (unsigned I = 0; I < (*Group)[0]->ReleatedBlocks.size(); I++) {
    BasicBlock *LabelBB = BasicBlock::Create(NewFunction->getContext(),
                                             "m.label.bb", NewFunction);
    RMI.addMatchedBBRelation(I, LabelBB);

    RepeatedItemInRegion *Candidate0 = (*Group)[0];
    BasicBlock *SourceBB = Candidate0->ReleatedBlocks[I];
    // Candidate0->printAllInsts();
    // errs() << "\n\n" << *SourceBB << "\n";

    for (Instruction &Inst : *SourceBB) {
      if (CurrentMatchedInstIndex >= Candidate0->RepeatedInstSet.size()) {
        break;
      }
      if (&Inst != Candidate0->RepeatedInstSet[CurrentMatchedInstIndex]) {
        // Inst.dump();
        // Candidate0->RepeatedInstSet[CurrentMatchedInstIndex]->dump();
        if (Debug) {
          errs() << "Error: no map for instruction\n";
        }
        return false;
      }

      BasicBlock *InstBB = isa<PHINode>(&Inst)
                               ? LabelBB
                               : BasicBlock::Create(NewFunction->getContext(),
                                                    "m.inst.bb", NewFunction);
      IRBuilder<> Builder(InstBB);
      Instruction *NewI = RMI.cloneInst(Builder, NewFunction, &Inst);
      RMI.addMatchedInstRelation(CurrentMatchedInstIndex, NewI);
      if (isa<PHINode>(&Inst)) {
        MatchedPHINodes.push_back(CurrentMatchedInstIndex);
      }

      CurrentMatchedInstIndex++;
    }
  }

  // if (Debug) {
  //   raw_fd_ostream *FS = getOutputStreamOfFile(
  //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterFillMatch.log");
  //   *FS << *NewFunction << "\n";
  //   delete FS;
  // }

  // 2. file in mismatch part
  for (int I = 0; I < (*Group).size(); I++) {
    Value *SourceId = SourceIds[I];
    RepeatedItemInRegion *Candidate = (*Group)[I];
    RMI.fillWithEachCandidate(Candidate->MinRegion->Blocks,
                              *RMI.NewBB2OldBBList[I], SourceId, I, NewFuncRoot,
                              Candidate->PrevBB);

    if (Candidate->HasExitExtraPHI) {
      BasicBlock *NewEndBB = RMI.MatchedValues2NBB[Candidate->EndBB];
      IRBuilder<> Builder(NewEndBB);
      for (Instruction *I : Candidate->ExitExtraPHI) {
        if (isa<PHINode>(I)) {
          RMI.VMap[I] = Builder.CreatePHI(I->getType(), 0);
        } else {
          assert(false && "Value should be phi node!");
        }
      }
    }
  }

  // if (Debug) {
  //   raw_fd_ostream *FS = getOutputStreamOfFile(
  //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterFillAll.log");
  //   *FS << *NewFunction << "\n";
  //   delete FS;
  // }

  // Assign Label Operands Value
  // 1. assign match part
  RepeatedItemInRegion *Candidate0 = (*Group)[0];
  for (unsigned I = 0; I < Candidate0->RepeatedInstSet.size(); I++) {
    Instruction *OldInst = Candidate0->RepeatedInstSet[I];
    Instruction *NewI = dyn_cast<Instruction>(RMI.VMap[OldInst]);

    unsigned OperandsNum = OldInst->getNumOperands();
    for (unsigned J = 0; J < OperandsNum; J++) {
      //获取所有对应的操作数到数组中
      std::vector<Value *> OperandsValue;
      std::vector<Value *> OldValueList;
      for (unsigned X = 0; X < (*Group).size(); X++) {
        if ((*Group)[X]->RepeatedInstSet[I]->getNumOperands() > J) {
          Value *OldV = (*Group)[X]->RepeatedInstSet[I]->getOperand(J);
          OldValueList.push_back(OldV);
          //需要先在上一步，把参数的映射添加进去
          Value *NewV = MapValue(OldV, RMI.InputsToArgs);
          if (NewV == nullptr)
            NewV = MapValue(OldV, RMI.VMap);

          if (NewV == nullptr) {
            errs() << "Mapped value should NOT be NULL!\n";
            return false;
          }

          // assert(NewV != nullptr && "Mapped value should NOT be NULL!");
          OperandsValue.push_back(NewV);
        } else {
          errs() << "Match Instr With diff NumOperands!\n";
          return false;
          // assert(false && "Match Instr With diff NumOperands!");
          // OperandsValue.push_back(UndefValue::get(Inst0->getOperand(J)->getType()));
        }
      }

      // handling just label operands for now
      if (!isa<BasicBlock>(OperandsValue[0]))
        continue;

      Value *V1 = OperandsValue[0];
      BasicBlock *BB1 = dyn_cast<BasicBlock>(V1);
      if (!BB1)
        return false;
      std::vector<BasicBlock *> SelectBBList;
      std::vector<unsigned> SourceCandToFix;
      SourceCandToFix.push_back(0);

      for (int X = 1; X < OperandsValue.size(); X++) {
        Value *V2 = OperandsValue[X];
        BasicBlock *BB2 = dyn_cast<BasicBlock>(V2);
        if (!BB2)
          return false;
        if (V2 != V1) {
          BasicBlock *SelectBB = BasicBlock::Create(
              BB1->getContext(), "bb.select", RMI.MergedFunc);
          IRBuilder<> BuilderBB(SelectBB);
          Instruction *Inst2 = (*Group)[X]->RepeatedInstSet[I];
          SelectBBList.push_back(SelectBB);
          // (*RMI.NewBB2OldBBList[LeftId])[SelectBB] = Inst1->getParent();
          (*RMI.NewBB2OldBBList[X])[SelectBB] = Inst2->getParent();
          Value *SourceId = SourceIds[X];
          BuilderBB.CreateCondBr(SourceId, BB2, BB1);
          BB1 = SelectBB;
        } else {
          SourceCandToFix.push_back(X);
        }
      }

      if (dyn_cast<BasicBlock>(OldValueList.front())->isLandingPad()) {
        BasicBlock *OldBB0 = dyn_cast<BasicBlock>(OldValueList.front());
        LandingPadInst *LP0 = OldBB0->getLandingPadInst();

        BasicBlock *LPadBB = BasicBlock::Create(NewFunction->getContext(),
                                                "lpad.bb", NewFunction);
        IRBuilder<> BuilderBB(LPadBB);
        Instruction *NewLP = LP0->clone();
        BuilderBB.Insert(NewLP);
        BuilderBB.CreateBr(dyn_cast<BasicBlock>(BB1));
        BB1 = LPadBB;

        for (unsigned X = 0; X < (*Group).size(); X++) {
          Value *OldV = OldValueList[X];
          BasicBlock *OldBB = dyn_cast<BasicBlock>(OldV);
          LandingPadInst *LP = OldBB->getLandingPadInst();
          assert(LP != nullptr &&
                 "Should be both as per the BasicBlock match!");

          (*RMI.NewBB2OldBBList[X])[LPadBB] =
              (*Group)[X]->RepeatedInstSet[I]->getParent();
          RMI.VMap[LP] = NewLP;
        }
      }

      NewI->setOperand(J, BB1);
      // fix relation of NewBB2OldBBList
      if (SelectBBList.size() > 0) {
        BasicBlock *SelectBB = SelectBBList[0];
        for (int X : SourceCandToFix) {
          (*RMI.NewBB2OldBBList[X])[SelectBB] =
              (*Group)[X]->RepeatedInstSet[I]->getParent();
        }
      }
    }
  }

  // 2. assign mismatch part
  for (int I = 0; I < (*Group).size(); I++) {
    RepeatedItemInRegion *Candidate = (*Group)[I];
    for (BasicBlock *BB : Candidate->MinRegion->Blocks) {
      if (!Candidate->ReleatedBBSet.contains(BB)) {
        for (Instruction &Inst : *BB) {
          if (!RMI.AssignLabelOperands(&Inst, (*RMI.NewBB2OldBBList[I])))
            return false;
        }
      }
    }
  }

  // if (Debug) {
  //   raw_fd_ostream *FS = getOutputStreamOfFile(
  //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterAssignLabel.log");
  //   *FS << *NewFunction << "\n";
  //   delete FS;
  // }

  // Assign Value Operands
  LLVMContext &Context = RMI.MergedFunc->getContext();

  auto MergeValues = [&](Value *V1, Value *V2, Instruction *InsertPt,
                         Value *IsV2, Value *&LastSelect) -> Value * {
    if (V1 == V2) {
      if (LastSelect)
        return LastSelect;
      return V1;
    }

    //暂时不支持此类优化
    // Instruction *IV1 = dyn_cast<Instruction>(V1);
    // Instruction *IV2 = dyn_cast<Instruction>(V2);

    // if (IV1 && IV2) {
    //   // if both IV1 and IV2 are non-merged values
    //   if (BlocksF2.find(IV1->getParent()) == BlocksF2.end() &&
    //       BlocksF1.find(IV2->getParent()) == BlocksF1.end()) {
    //     CoalescingCandidates[IV1][IV2]++;
    //     CoalescingCandidates[IV2][IV1]++;
    //   }
    // }

    IRBuilder<> Builder(InsertPt);
    Value *FalseToSelect = LastSelect == nullptr ? V1 : LastSelect;
    LastSelect = (Instruction *)Builder.CreateSelect(IsV2, V2, FalseToSelect);
    ListSelects.push_back(dyn_cast<Instruction>(LastSelect));
    return LastSelect;
  };

  // assign match part
  for (unsigned InstNum = 0; InstNum < Candidate0->RepeatedInstSet.size();
       InstNum++) {
    Instruction *I1 = Candidate0->RepeatedInstSet[InstNum];
    //跳过phi结点
    if (isa<PHINode>(I1)) {
      continue;
    }
    Instruction *NewI = dyn_cast<Instruction>(RMI.VMap[I1]);

    for (unsigned OprNum = 0; OprNum < I1->getNumOperands(); OprNum++) {

      if (isa<BasicBlock>(I1->getOperand(OprNum)))
        continue;
      Value *LastSelect = nullptr;
      //优先使用InputsToArgs做映射
      Value *V1 = MapValue(I1->getOperand(OprNum), RMI.InputsToArgs);
      if (V1 == nullptr)
        V1 = MapValue(I1->getOperand(OprNum), RMI.VMap);
      assert(V1 != nullptr && "Value1 should NOT be null!");

      for (unsigned CandNum = 1; CandNum < (*Group).size(); CandNum++) {
        RepeatedItemInRegion *Candidate = (*Group)[CandNum];
        Instruction *I2 = Candidate->RepeatedInstSet[InstNum];
        assert(I1->getNumOperands() == I2->getNumOperands() &&
               "Num of Operands SHOULD be EQUAL\n");

        Value *V2 = MapValue(I2->getOperand(OprNum), RMI.InputsToArgs);
        if (V2 == nullptr)
          V2 = MapValue(I2->getOperand(OprNum), RMI.VMap);
        assert(V2 != nullptr && "Value2 should NOT be null!");

        Value *SourceId = SourceIds[CandNum];
        Value *V = MergeValues(V1, V2, NewI, SourceId, LastSelect);
        NewI->setOperand(OprNum, V);
      }
    }
  }

  // assign mismatch part
  for (int I = 0; I < (*Group).size(); I++) {
    RepeatedItemInRegion *Candidate = (*Group)[I];
    for (BasicBlock *BB : Candidate->MinRegion->Blocks) {
      if (!Candidate->ReleatedBBSet.contains(BB)) {
        for (Instruction &Inst : *BB) {
          RMI.AssignValueOperands(&Inst, (*RMI.NewBB2OldBBList[I]));
        }
      }
    }
  }

  // if (Debug) {
  //   raw_fd_ostream *FS = getOutputStreamOfFile(
  //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterAssignValue.log");
  //   *FS << *NewFunction << "\n";
  //   delete FS;
  // }

  if (ListSelects.size() > RAMaxNumSelection) {
    if (Debug)
      errs() << "Bailing out: Operand selection threshold\n";
    return false;
  }

  // Assign Phi Node Value and Label
  // assign match part
  for (unsigned PhiIndex : MatchedPHINodes) {
    Instruction *Inst0 = Candidate0->RepeatedInstSet[PhiIndex];
    assert(isa<PHINode>(Inst0) && "Inst0 should be phi node!");
    PHINode *NewPHI = dyn_cast<PHINode>(RMI.VMap[Inst0]);

    std::map<BasicBlock *, std::vector<Value *>> LastSelectAndDefaultVOfPredBB;

    for (unsigned X = 0; X < (*Group).size(); X++) {
      PHINode *PHI = dyn_cast<PHINode>((*Group)[X]->RepeatedInstSet[PhiIndex]);
      std::map<BasicBlock *, BasicBlock *> &BlocksReMap =
          *RMI.NewBB2OldBBList[X];
      std::set<int> FoundIndices;

      for (auto It = pred_begin(NewPHI->getParent()),
                E = pred_end(NewPHI->getParent());
           It != E; It++) {
        BasicBlock *NewPredBB = *It;
        Value *V = nullptr;
        if (BlocksReMap.find(NewPredBB) != BlocksReMap.end()) {
          BasicBlock *OldPredBB = BlocksReMap[NewPredBB];
          int OldIndex = PHI->getBasicBlockIndex(BlocksReMap[NewPredBB]);
          if (OldIndex >= 0) {
            Value *OldV = PHI->getIncomingValue(OldIndex);
            if (isa<UndefValue>(OldV)) {
              V = UndefValue::get(NewPHI->getType());
            } else {
              V = MapValue(OldV, RMI.InputsToArgs);
              if (V == nullptr)
                V = MapValue(OldV, RMI.VMap);
            }
            assert(V != nullptr && "Value should not be null");
            FoundIndices.insert(OldIndex);
          } else {
            errs() << "NewPredBB:\n" << *NewPredBB << "\n";
            errs() << "OldPredBB:\n" << *OldPredBB << "\n";
            errs() << "OldPhi:\n" << *PHI << "\n";
            errs() << "newPhi:\n" << *NewPHI << "\n";
            errs() << "OldBB:\n" << *PHI->getParent() << "\n";
            errs() << "newBB:\n" << *NewPHI->getParent() << "\n";

            return false;
            assert(false);
          }
        }
        if (V) {
          int Idx = NewPHI->getBasicBlockIndex(NewPredBB);
          if (Idx < 0) {
            NewPHI->addIncoming(V, NewPredBB);
            continue;
          }
          Value *V0 = NewPHI->getIncomingValue(Idx);
          if (V == V0) {
            continue;
          }
          if (V != V0) {
            Value *FalseValue = V0;
            Value *DefaultValue = V0;
            if (LastSelectAndDefaultVOfPredBB.count(NewPredBB)) {
              FalseValue = LastSelectAndDefaultVOfPredBB[NewPredBB][0];
              DefaultValue = LastSelectAndDefaultVOfPredBB[NewPredBB][1];
              if (V == DefaultValue) {
                continue;
              }
              // otherwise, we need to create new select
            }

            Instruction *InsertBefore = NewPredBB->getTerminator();
            assert(InsertBefore && "Terminator Value should not be null!");
            Value *SourceId = SourceIds[X];
            SelectInst *NewSelect = SelectInst::Create(SourceId, V, FalseValue,
                                                       "for_phi", InsertBefore);
            LastSelectAndDefaultVOfPredBB[NewPredBB] = {NewSelect,
                                                        DefaultValue};
            NewPHI->setIncomingValue(Idx, NewSelect);
          }
        } else {
        }
      }
      if (FoundIndices.size() != PHI->getNumIncomingValues())
        return false;
    }

    // check full and try fix
    std::vector<BasicBlock *> Preds(pred_begin(NewPHI->getParent()),
                                    pred_end(NewPHI->getParent()));
    if (NewPHI->getNumIncomingValues() < Preds.size()) {
      for (unsigned X = 0; X < (*Group).size(); X++) {
        PHINode *OldPHI =
            dyn_cast<PHINode>((*Group)[X]->RepeatedInstSet[PhiIndex]);
        OldPHI->dump();
      }
      for (BasicBlock *Pred : Preds) {
        int Idx = NewPHI->getBasicBlockIndex(Pred);
        if (Idx < 0) {
          NewPHI->addIncoming(UndefValue::get(NewPHI->getType()), Pred);
          continue;
        }
      }
    } else if (NewPHI->getNumIncomingValues() > Preds.size()) {
      assert(false);
    }
  }

  // if (Debug) {
  //   raw_fd_ostream *FS = getOutputStreamOfFile(
  //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterAssignPHI0.log");
  //   *FS << *NewFunction << "\n";
  //   delete FS;
  // }

  // assign mismatch part
  for (int I = 0; I < (*Group).size(); I++) {
    RepeatedItemInRegion *Candidate = (*Group)[I];
    std::map<BasicBlock *, BasicBlock *> &BlocksReMap = *RMI.NewBB2OldBBList[I];
    for (BasicBlock *BB : Candidate->MinRegion->Blocks) {
      if (!Candidate->ReleatedBBSet.contains(BB)) {
        for (Instruction &Inst : *BB) {
          if (PHINode *PHI = dyn_cast<PHINode>(&Inst)) {
            PHINode *NewPHI = dyn_cast<PHINode>(RMI.VMap[PHI]);
            std::set<int> FoundIndices;

            for (auto It = pred_begin(NewPHI->getParent()),
                      E = pred_end(NewPHI->getParent());
                 It != E; It++) {

              BasicBlock *NewPredBB = *It;

              Value *V = nullptr;

              if (BlocksReMap.find(NewPredBB) != BlocksReMap.end()) {
                int Index = PHI->getBasicBlockIndex(BlocksReMap[NewPredBB]);
                if (Index >= 0) {
                  V = MapValue(PHI->getIncomingValue(Index), RMI.VMap);
                  FoundIndices.insert(Index);
                }
              }
              if (V == nullptr)
                V = UndefValue::get(NewPHI->getType());
              NewPHI->addIncoming(V, NewPredBB);
            }
            if (FoundIndices.size() != PHI->getNumIncomingValues())
              return false;
          }
        }
      }
    }

    if (Candidate->HasExitExtraPHI) {
      for (Instruction *I : Candidate->ExitExtraPHI) {
        PHINode *PHI = dyn_cast<PHINode>(I);
        assert(PHI && "PHI node should not be nullptr!");
        PHINode *NewPHI = dyn_cast<PHINode>(RMI.VMap[PHI]);
        std::set<int> FoundIndices;

        for (auto It = pred_begin(NewPHI->getParent()),
                  E = pred_end(NewPHI->getParent());
             It != E; It++) {

          BasicBlock *NewPredBB = *It;

          Value *V = nullptr;

          if (BlocksReMap.find(NewPredBB) != BlocksReMap.end()) {
            int Index = PHI->getBasicBlockIndex(BlocksReMap[NewPredBB]);
            if (Index >= 0) {
              V = MapValue(PHI->getIncomingValue(Index), RMI.VMap);
              FoundIndices.insert(Index);
            }
          }
          if (V == nullptr)
            V = UndefValue::get(NewPHI->getType());
          NewPHI->addIncoming(V, NewPredBB);
        }
        if (FoundIndices.size() != PHI->getNumIncomingValues())
          return false;
      }
    }
  }

  //删除不必要的branch指令，合并块

  auto CoalescingBasicBlock = [&](BasicBlock *PrevBB,
                                  BasicBlock *SuccBB) -> void {
    Instruction *TermInst = PrevBB->getTerminator();
    TermInst->eraseFromParent();
    IRBuilder<> Builder(PrevBB);
    std::vector<Instruction *> Inst2Mov;
    for (Instruction &Inst : *SuccBB) {
      Inst2Mov.push_back(&Inst);
    }
    SuccBB->replaceSuccessorsPhiUsesWith(PrevBB);

    for (Instruction *Inst : Inst2Mov) {
      // Inst->eraseFromParent();
      Inst->removeFromParent();
      Builder.Insert(Inst);
    }
    SuccBB->eraseFromParent();
  };

  // for (auto It = RMI.MergedFunc->begin(); It != RMI.MergedFunc->end();) {
  //   BasicBlock *BB = &*It;
  //   if (BB == NewFuncExit) {
  //     It++;
  //     continue;
  //   }
  //   BasicBlock *SuccBB = BB->getSingleSuccessor();
  //   if (SuccBB) {
  //     if (BB == SuccBB->getSinglePredecessor() && SuccBB != NewFuncExit) {
  //       CoalescingBasicBlock(BB, SuccBB);
  //       continue;
  //     }
  //   }
  //   It++;
  // }

  // if (Debug) {
  //   raw_fd_ostream *FS = getOutputStreamOfFile(
  //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterCB.log");
  //   *FS << *NewFunction << "\n";
  //   delete FS;
  // }

  // fix exit bb
  IRBuilder<> ExitBuilder(NewFuncExit);
  Argument *Arg0 = NewFunction->getArg(0);
  Value *Idx[2];
  Idx[0] = Constant::getNullValue(Type::getInt32Ty(NewFuncExit->getContext()));

  for (unsigned I = 0; I < RMI.OutputsTypeList.size(); I++) {
    // ExitBuilder
    // oldValue0可能为nullptr
    int OldValue0Index = Candidate0->OutputsIndex2LocalIndex[I];
    Value *OldValue0 =
        OldValue0Index < 0 ? nullptr : Candidate0->Outputs[OldValue0Index];

    Value *NewValue0 =
        OldValue0 != nullptr ? MapValue(OldValue0, RMI.VMap) : nullptr;
    Value *FinalStoreValue = NewValue0;

    Value *LastSelect = nullptr;
    int X0 = 0;
    for (int X = 1; X < Group->size(); X++) {
      RepeatedItemInRegion *Candidate = (*Group)[X];
      int OldValueIndex = Candidate->OutputsIndex2LocalIndex[I];
      Value *OldValue =
          OldValueIndex < 0 ? nullptr : Candidate->Outputs[OldValueIndex];
      if (OldValue == nullptr)
        continue;

      Value *NewValue = MapValue(OldValue, RMI.VMap);
      if (OldValue0 == nullptr && NewValue != nullptr) {
        OldValue0 = OldValue;
        NewValue0 = NewValue;
        FinalStoreValue = NewValue;
        X0 = X;
        continue;
      }

      if (NewValue == NewValue0)
        continue;
      Value *SourceId = SourceIds[X];
      Value *FalseToSelect = LastSelect == nullptr ? NewValue0 : LastSelect;
      LastSelect = ExitBuilder.CreateSelect(SourceId, NewValue, FalseToSelect);
      ListSelects.push_back(dyn_cast<Instruction>(LastSelect));
      FinalStoreValue = LastSelect;
    }

    assert(FinalStoreValue && "Value Should Not Be Null!");
    Value *StoreInto = nullptr;
    if (RAAggregateArgs.getValue()) {
      Idx[1] = ConstantInt::get(Type::getInt32Ty(NewFuncExit->getContext()),
                                I + RMI.OutputsParamListOffset);
      StoreInto = GetElementPtrInst::Create(
          RMI.StructTy, Arg0, Idx, "gep_output_" + RMI.OutputsNameList[I],
          NewFuncExit);

    } else {
      StoreInto = NewFunction->getArg(RMI.OutputsParamListOffset + I);
    }
    assert(StoreInto && "Value Should Not Be Null!");
    ExitBuilder.CreateStore(FinalStoreValue, StoreInto);
  }
  ExitBuilder.CreateRetVoid();

  // if (Debug) {
  //   raw_fd_ostream *FS = getOutputStreamOfFile(
  //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterFixExit.log");
  //   *FS << *NewFunction << "\n";
  //   delete FS;
  // }

  // errs() << NewFunction->getInstructionCount();

  // fix Instruction dominace
  DominatorTree DT(*NewFunction);

  // find instructions need fix
  for (Instruction &I : instructions(NewFunction)) {
    if (PHINode *PHI = dyn_cast<PHINode>(&I)) {
      for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++) {
        BasicBlock *BB = PHI->getIncomingBlock(i);
        if (BB == nullptr)
          errs() << "Null incoming block\n";
        Value *V = PHI->getIncomingValue(i);
        if (V == nullptr)
          errs() << "Null incoming value\n";
        if (Instruction *IV = dyn_cast<Instruction>(V)) {
          if (BB->getTerminator() == nullptr) {
            if (Debug)
              errs() << "ERROR: Null terminator\n";
            return false;
          }
          if (!DT.dominates(IV, BB->getTerminator())) {
            if (OffendingInsts.count(IV) == 0) {
              OffendingInsts.insert(IV);
              LinearOffendingInsts.push_back(IV);
            }
          }
        }
      }
    } else {
      for (unsigned i = 0; i < I.getNumOperands(); i++) {
        if (I.getOperand(i) == nullptr) {
          if (Debug)
            errs() << "ERROR: Null operand\n";
          return false;
        }
        if (Instruction *IV = dyn_cast<Instruction>(I.getOperand(i))) {
          if (!DT.dominates(IV, &I)) {
            if (OffendingInsts.count(IV) == 0) {
              OffendingInsts.insert(IV);
              LinearOffendingInsts.push_back(IV);
            }
          }
        }
      }
    }
  }

  auto StoreInstIntoAddr = [](Instruction *IV, Value *Addr) {
    IRBuilder<> Builder(IV->getParent());
    if (IV->isTerminator()) {
      BasicBlock *SrcBB = IV->getParent();
      if (InvokeInst *II = dyn_cast<InvokeInst>(IV)) {
        BasicBlock *DestBB = II->getNormalDest();

        Builder.SetInsertPoint(&*DestBB->getFirstInsertionPt());
        // create PHI
        PHINode *PHI = Builder.CreatePHI(IV->getType(), 0);
        for (auto PredIt = pred_begin(DestBB), PredE = pred_end(DestBB);
             PredIt != PredE; PredIt++) {
          BasicBlock *PredBB = *PredIt;
          if (PredBB == SrcBB) {
            PHI->addIncoming(IV, PredBB);
          } else {
            PHI->addIncoming(UndefValue::get(IV->getType()), PredBB);
          }
        }
        Builder.CreateStore(PHI, Addr);
      } else {
        for (auto SuccIt = succ_begin(SrcBB), SuccE = succ_end(SrcBB);
             SuccIt != SuccE; SuccIt++) {
          BasicBlock *DestBB = *SuccIt;

          Builder.SetInsertPoint(&*DestBB->getFirstInsertionPt());
          // create PHI
          PHINode *PHI = Builder.CreatePHI(IV->getType(), 0);
          for (auto PredIt = pred_begin(DestBB), PredE = pred_end(DestBB);
               PredIt != PredE; PredIt++) {
            BasicBlock *PredBB = *PredIt;
            if (PredBB == SrcBB) {
              PHI->addIncoming(IV, PredBB);
            } else {
              PHI->addIncoming(UndefValue::get(IV->getType()), PredBB);
            }
          }
          Builder.CreateStore(PHI, Addr);
        }
      }
    } else {
      Instruction *LastI = nullptr;
      Instruction *InsertPt = nullptr;
      for (Instruction &I : *IV->getParent()) {
        InsertPt = &I;
        if (LastI == IV)
          break;
        LastI = &I;
      }
      if (isa<PHINode>(InsertPt) || isa<LandingPadInst>(InsertPt)) {
        // Builder.SetInsertPoint(&*IV->getParent()->getFirstInsertionPt());
        Builder.SetInsertPoint(IV->getParent()->getTerminator());
      } else
        Builder.SetInsertPoint(InsertPt);

      Builder.CreateStore(IV, Addr);
    }
  };

  auto MemfyInst = [&](std::set<Instruction *> &InstSet) -> AllocaInst * {
    if (InstSet.empty())
      return nullptr;
    IRBuilder<> Builder(&*NewFuncRoot->getFirstInsertionPt());
    AllocaInst *Addr = Builder.CreateAlloca((*InstSet.begin())->getType());

    for (Instruction *I : InstSet) {
      for (auto UIt = I->use_begin(), E = I->use_end(); UIt != E;) {
        Use &UI = *UIt;
        UIt++;

        Instruction *User = cast<Instruction>(UI.getUser());

        if (PHINode *PHI = dyn_cast<PHINode>(User)) {
          /// TODO: make sure getOperandNo is getting the correct incoming edge
          IRBuilder<> Builder(
              PHI->getIncomingBlock(UI.getOperandNo())->getTerminator());
          UI.set(Builder.CreateLoad(Addr));
        } else {
          IRBuilder<> Builder(User);
          UI.set(Builder.CreateLoad(Addr));
        }
      }
    }

    for (Instruction *I : InstSet)
      StoreInstIntoAddr(I, Addr);

    return Addr;
  };

  // start fix
  std::set<Instruction *> Visited;
  for (Instruction *I : LinearOffendingInsts) {
    if (Visited.find(I) != Visited.end())
      continue;

    std::set<Instruction *> InstSet;
    InstSet.insert(I);

    // Create a coalescing group in InstSet
    // if (EnableSALSSACoalescing)
    //   OptimizeCoalescing(I, InstSet, CoalescingCandidates, Visited);

    for (Instruction *OtherI : InstSet)
      Visited.insert(OtherI);

    AllocaInst *Addr = MemfyInst(InstSet);
    if (Addr)
      Allocas.push_back(Addr);
  }

  DominatorTree NDT(*NewFunction);
  PromoteMemToReg(Allocas, NDT, nullptr);

  if (verifyFunction(*NewFunction)) {
    errs() << "ERROR: Produced Broken Function!\n";
    // assert(false);
    return false;
  }

  postProcessFunction(*NewFunction);

  // if (Debug) {
  //   raw_fd_ostream *FS = getOutputStreamOfFile(
  //       "/home/kp4/SWH/llvm-code-size/build-test/log/MergedFunc" +
  //       to_string(CreatedMergedFunctionNum - 1) + ".log");
  //   *FS << *NewFunction << "\n";
  //   delete FS;
  // }

  return true;
}

void RegionAbstractManager::getGroupParamsList(RegionMergeInfo &RMI) {
  assert(RMI.getInputsTypeList());
  assert(RMI.getOutputsTypeList());
}

int RegionAbstractManager::getGroupBenefit(RegionMergeInfo &RMI) {
  TargetTransformInfo TTI(M.getDataLayout());
  return RMI.getNewBenefit(TTI);
}

void RegionAbstractManager::updateNonSplittableBlockSet(
    RepeatedItemInRegion *Region) {
  for (BasicBlock *BB : Region->MinRegion->Blocks) {
    NonSplittableBlockSet.insert(BB);
  }
}

void RegionAbstractManager::removeFromNonSplittableBlockSet(
    RepeatedItemInRegion *Region) {
  for (BasicBlock *BB : Region->MinRegion->Blocks) {
    NonSplittableBlockSet.erase(BB);
  }
}

Instruction *RegionMergeInfo::cloneInst(IRBuilder<> &Builder, Function *MF,
                                        Instruction *I) {
  Instruction *NewI = nullptr;
  if (I->getOpcode() == Instruction::Ret) {
    assert(false && "Should not deal with ret instruction!");
    if (MF->getReturnType()->isVoidTy()) {
      NewI = Builder.CreateRetVoid();
    } else {
      NewI = Builder.CreateRet(UndefValue::get(MF->getReturnType()));
    }
  } else if (isa<PHINode>(I)) {
    NewI = Builder.CreatePHI(I->getType(), 0);
    return NewI;
  } else {
    NewI = I->clone();
    for (unsigned i = 0; i < NewI->getNumOperands(); i++) {
      if (!isa<Constant>(I->getOperand(i)))
        NewI->setOperand(i, nullptr);
    }
    Builder.Insert(NewI);
  }

  SmallVector<std::pair<unsigned, MDNode *>, 8> MDs;
  NewI->getAllMetadata(MDs);
  for (std::pair<unsigned, MDNode *> MDPair : MDs) {
    NewI->setMetadata(MDPair.first, nullptr);
  }

  if (isa<GetElementPtrInst>(NewI)) {
    GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(I);
    dyn_cast<GetElementPtrInst>(NewI)->setIsInBounds(GEP->isInBounds());
  }

  return NewI;
}

void SwhRegion::updateEntry(BasicBlock *NewEntry) {
  EntryBlock = NewEntry;
  if (Blocks.size() == 1) {
    ExitBlock = NewEntry;
    Blocks[0] = EntryBlock;
  } else {
    Blocks[1] = EntryBlock;
  }
}

void SwhRegion::updateExit(BasicBlock *NewExit) {
  ExitBlock = NewExit;
  if (Blocks.size() == 1) {
    EntryBlock = NewExit;
    Blocks[0] = EntryBlock;
  } else {
    Blocks[0] = ExitBlock;
  }
}

PreservedAnalyses RegionAbstractPass::run(Module &M,
                                          ModuleAnalysisManager &AM) {
  // auto &FAM =
  // AM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
  // std::function<TargetTransformInfo *(Function &)> GTTI =
  //     [&FAM](Function &F) -> TargetTransformInfo * {
  //   return &FAM.getResult<TargetIRAnalysis>(F);
  // };

  RegionAbstract RA;
  RA.runOnModule(M);
  return PreservedAnalyses::none();
}
