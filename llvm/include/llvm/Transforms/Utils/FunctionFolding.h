#ifndef LLVM_TRANSFORMS_FUNCTION_FOLDING_H
#define LLVM_TRANSFORMS_FUNCTION_FOLDING_H

#include "llvm/ADT/SetVector.h"
#include "llvm/Analysis/IRSimilarityInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/SuffixTree.h"
#include "llvm/Support/SuffixTreeRepeatedInfos.h"
#include "llvm/Transforms/IPO/RegionAbstract.h"
#include <map>

namespace llvm {

using IRSimilarity::InstrData;

class FunctionFoldingPass : public PassInfoMixin<FunctionFoldingPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

class FunctionFolding {
  Function &F;
  std::vector<RARegionGroup *> CandidateList;
  std::vector<RARegionGroup *> IntraBlockCandidateList;
  unsigned CreatedMergedFunctionNum = 0;
  DenseSet<BasicBlock *> NonSplittableBlockSet;
  

public:
  FunctionFolding(Function &Func) : F(Func) {}

  bool
  getCandidateList(std::vector<RepeatedInfos::RepeatedSubstringByS *> &RSList,
                   std::vector<InstrData *> &InstrList);

  void analysisRegionGroup(RARegionGroup *Group, RegionMergeInfo &RMI);
  bool mergeRegionGroup(RARegionGroup *Group, RegionMergeInfo &RMI, int Benefit);
  int getGroupBenefit(RegionMergeInfo &RMI);
  bool removeOldRegion(RARegionGroup *Group, RegionMergeInfo &RMI, BasicBlock *EntryBB);
  void reuseOldRegion(RARegionGroup *Group, RegionMergeInfo &RMI, BasicBlock *EntryBB);

  BasicBlock *createFoldingRegion(RARegionGroup *Group, RegionMergeInfo &RMI);
  bool fillMergedFunc(RARegionGroup *Group, RegionMergeInfo &RMI, BasicBlock *EntryBB, int Benefit);

  void buildInputRelation(RARegionGroup *Group, RegionMergeInfo &RMI);

  void updateNonSplittableBlockSet(RepeatedItemInRegion *Region) {
    for (BasicBlock *BB : Region->MinRegion->Blocks) {
      NonSplittableBlockSet.insert(BB);
    }
  }

  void removeFromNonSplittableBlockSet(RepeatedItemInRegion *Region) {
    for (BasicBlock *BB : Region->MinRegion->Blocks) {
      NonSplittableBlockSet.erase(BB);
    }
  }
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_FUNCTION_FOLDING_H