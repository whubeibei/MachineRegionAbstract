/*
 * @Author: Wenhan Shang
 * @Email: whu_swh@whu.edu.cn
 * @Date: 2022-01-21 11:34:23
 * @FilePath: /llvm-12-swh/llvm/include/llvm/Transforms/IPO/RegionAbstract.h
 */

#ifndef LLVM_TRANSFORMS_IPO_REGIONABSTRACT_H
#define LLVM_TRANSFORMS_IPO_REGIONABSTRACT_H

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Value.h"
#include "llvm/InitializePasses.h"

#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/IRSimilarityInfo.h"
#include "llvm/Analysis/ProfileSummaryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/Support/SuffixTree.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringSet.h"

#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include "llvm/ADT/SequenceAlignment.h"
#include "llvm/Support/SuffixTreeRepeatedInfos.h"

#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace llvm {

using IRSimilarity::InstrData;

class RegionAbstractPass : public PassInfoMixin<RegionAbstractPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};

struct RepeatedItemInRegion;
struct RegionMergeInfo;
typedef std::vector<RepeatedItemInRegion *> RARegionGroup;

class RegionAbstractOptions {
  unsigned InstrEquivalenceMode = 0;

public:
  RegionAbstractOptions setInstrEquivalenceMode(unsigned Mode) {
    InstrEquivalenceMode = Mode;
    return *this;
  }
};

class RegionAbstract : public ModulePass {
private:
  Module *M;

public:
  static char ID;

  RegionAbstract() : ModulePass(ID) {
    initializeRegionAbstractPass(*PassRegistry::getPassRegistry());
  }
  bool runOnModule(Module &M) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  unsigned analysisOld(SuffixTree &ST, unsigned int RepeatedStrLenLowerLimit);
  void analysisCandidate(std::vector<RepeatedItemInRegion *> &Candidate,
                         RegionMergeInfo &RMI);
  bool mergeCandidate(std::vector<RepeatedItemInRegion *> &Candidate,
                      const RegionAbstractOptions &Options,
                      RegionMergeInfo &RMI);

  bool alignRepeatedItemInRegion(RepeatedItemInRegion *LeftItem,
                                 RepeatedItemInRegion *RightItem,
                                 AlignedSequence<Value *> &AlignedSeq,
                                 RegionMergeInfo &RMI,
                                 const RegionAbstractOptions &Options);

  void alignMisMatchBlock(BasicBlock *MMB, AlignedSequence<Value *> &AlignedSeq,
                          RegionMergeInfo &RMI, bool IsLeft);
  void alignFullMatchBlock(BasicBlock *MMB1, BasicBlock *MMB2,
                           AlignedSequence<Value *> &AlignedSeq,
                           RegionMergeInfo &RMI);
  void
  alignPartialMatchBlock(BasicBlock *MMB1, BasicBlock *MMB2,
                         std::vector<std::pair<int[2], int[2]>> &SameRangePairs,
                         AlignedSequence<Value *> &AlignedSeq,
                         RegionMergeInfo &RMI);
};

class SWHAbstractor {
private:
  LLVMContext *ContextPtr;
  Type *IntPtrTy;

  Value *IsFunc1;

  // BlockListType &Blocks1;
  // BlockListType &Blocks2;
  std::vector<BasicBlock *> Blocks1;
  std::vector<BasicBlock *> Blocks2;

  BasicBlock *EntryBB1;
  BasicBlock *EntryBB2;
  BasicBlock *PreBB;

  Type *ReturnType;

  Function *MergedFunc;

  SmallPtrSet<BasicBlock *, 8> CreatedBBs;
  SmallPtrSet<Instruction *, 8> CreatedInsts;

public:
  SWHAbstractor(std::vector<BasicBlock *> BBS1, std::vector<BasicBlock *> BBS2)
      : Blocks1(BBS1), Blocks2(BBS2) {}

  bool generate(AlignedSequence<Value *> &AlignedSeq, ValueToValueMapTy &VMap,
                const RegionAbstractOptions &Options, RegionMergeInfo &RMI);

  SWHAbstractor &setContext(LLVMContext *ContextPtr) {
    this->ContextPtr = ContextPtr;
    return *this;
  }

  SWHAbstractor &setIntPtrType(Type *IntPtrTy) {
    this->IntPtrTy = IntPtrTy;
    return *this;
  }

  SWHAbstractor &setFunctionIdentifier(Value *IsFunc1) {
    this->IsFunc1 = IsFunc1;
    return *this;
  }

  SWHAbstractor &setEntryPoints(BasicBlock *EntryBB1, BasicBlock *EntryBB2) {
    this->EntryBB1 = EntryBB1;
    this->EntryBB2 = EntryBB2;
    return *this;
  }

  SWHAbstractor &setMergedEntryPoint(BasicBlock *PreBB) {
    this->PreBB = PreBB;
    return *this;
  }

  SWHAbstractor &setMergedReturnType(Type *ReturnType) {
    this->ReturnType = ReturnType;
    return *this;
  }

  SWHAbstractor &setMergedFunction(Function *MergedFunc) {
    this->MergedFunc = MergedFunc;
    return *this;
  }

  Function *getMergedFunction() { return MergedFunc; }
  Type *getMergedReturnType() { return ReturnType; }

  Value *getFunctionIdentifier() { return IsFunc1; }

  LLVMContext &getContext() { return *ContextPtr; }

  std::vector<BasicBlock *> &getBlocks1() { return Blocks1; }
  std::vector<BasicBlock *> &getBlocks2() { return Blocks2; }

  BasicBlock *getEntryBlock1() { return EntryBB1; }
  BasicBlock *getEntryBlock2() { return EntryBB2; }
  BasicBlock *getPreBlock() { return PreBB; }

  Type *getIntPtrType() { return IntPtrTy; }

  void insert(BasicBlock *BB) { CreatedBBs.insert(BB); }
  void insert(Instruction *I) { CreatedInsts.insert(I); }

  void erase(BasicBlock *BB) { CreatedBBs.erase(BB); }
  void erase(Instruction *I) { CreatedInsts.erase(I); }
};

#pragma region swh
struct SwhRegion {
  BasicBlock *EntryBlock;
  BasicBlock *ExitBlock;
  bool NeedFullEntry = false;
  bool NeedFullExit = false;
  std::vector<BasicBlock *> FollowBB;

  unsigned StartInstIndex = 0;
  unsigned EndInstIndex = 0;

  std::vector<BasicBlock *> Blocks;
  // DFS的Blocks
  SwhRegion(Region *SourceRegion);
  // 乱序的Blocks，0-->Exit, 1-->Entry
  SwhRegion(std::vector<BasicBlock *> &ContainedBBs);

  BasicBlock *getEntry() { return EntryBlock; }
  BasicBlock *getExit() { return ExitBlock; }

  void updateEntry(BasicBlock *NewEntry);
  void updateExit(BasicBlock *NewExit);

  /// Check if a Region is the TopLevel region.
  ///
  /// The toplevel region represents the whole function.
  bool isTopLevelRegion() const { return ExitBlock == nullptr; }
};

// alias for RepeatedItemInRegion
typedef RepeatedItemInRegion RARegionCandidate;
struct RepeatedItemInRegion {
  Function *ParentFunc;
  SwhRegion *MinRegion;
  bool RegionSplit = false;
  // case 0, keep 1 Inst in entry block, keep 0 Inst in exit block
  // case 1,  keep full entry block or exit block
  // case 2, keep part of Releated Instructions
  // default, same to case 0
  unsigned EntryBlockSplitMode = 0;
  unsigned ExitBlockSplitMode = 0;

  std::vector<BasicBlock *> ReleatedBlocks;
  DenseSet<BasicBlock *> ReleatedBBSet;

  bool HasExitExtraPHI = false;
  SetVector<Instruction *> ExitExtraPHI;
  //把上面两个合并成下面一个
  // SetVector<BasicBlock *> ReleatedBBs;

  std::vector<InstrData *> RepeatedInstrDatas;
  SetVector<Instruction *> RepeatedInstSet;

  std::map<unsigned, std::vector<std::pair<int[2], int[2]>>> BlockMapping;

  BasicBlock *StartBB = nullptr, *EndBB = nullptr;
  BasicBlock *PrevBB = nullptr, *FollowBB = nullptr;
  bool SplitedEnd = false;
  bool SplitedStart = false;

  SetVector<Value *> Inputs;
  SetVector<Value *> Outputs;

  std::map<Value *, int> InputParamMap;
  // -1,      means not Occupied
  // X >=0,   means Occupied by the Inputs[X]
  std::vector<int> *OccupiedListOfInput;

  std::map<Value *, int> OutputParamMap;
  // -1,      means not Occupied
  // X >=0,   means Occupied by the Outputs[X]
  std::vector<int> *OccupiedListOfOutput;
  // ValueMap<const Value *, WeakTrackingVH> Arg2OldValue;
  std::map<int, int> OutputsIndex2LocalIndex;

  void dump();
  void dumpOnly();
  void printAllInsts();
  void printAllInsts(raw_ostream &OFS);
  bool getMinRegion(RegionInfo *RI);
  bool getMinRegionForIntraBBRS();
  bool updatePhiBlock(BasicBlock *NewBB, BasicBlock *OldBB);
  bool splitRegion(DenseSet<BasicBlock *> &NonSplittableBlockSet,
                   std::set<Function *> &AffectedFuncs);
  bool splitRepeatedSubstring(DenseSet<BasicBlock *> &NonSplittableBlockSet,
                              std::set<Function *> &AffectedFuncs);

  void addInputParam(int InputIndex, int Index);
  void addOutputParam(int OutputIndex, int Index);

private:
  void printInfo();
};

/**
 * RegionMergeInfo : class for managing info of a single candidate group
 */
struct RegionMergeInfo {
  RARegionGroup *CurrGroup;
  RegionMergeInfo(RARegionGroup *Group) : CurrGroup(Group) {}


  //相关统计数据
  // Related statistics
  unsigned TotalInsts = 0;
  unsigned TotalMatches = 0;
  unsigned TotalCoreMatches = 0;

  // to calculate benefit
  unsigned MisMatchEntryCount = 0;
  unsigned MisMatchExitCount = 0;
  unsigned MatchBrToMisMatch = 0;

  //add for Function Folding
  long BrokenDomRelationDefNum = 0;
  long BrokenDomRelationUseNum = 0;
  long FoldedBenefit = 0;

  SetVector<BasicBlock *> CreatedMatchBBs;
  SetVector<BasicBlock *> CreatedMisMatchBBs;
  SetVector<BasicBlock *> CreatedOverheadBBs;

  SetVector<Instruction *> CreatedOverheadBranches;
  SetVector<BasicBlock *> BlocksToDelete;
  SetVector<Instruction *> MisMatchInsrInMatchedBB;

  std::map<Instruction *, Value *> InstrReplacedFrom;
  std::map<Instruction *, std::vector<unsigned>> InstrReplacedOpNums;
  std::map<Instruction *, Value *> InstrReplacedTo;
  std::map<PHINode *, BasicBlock *> PNIncomingAdded;

  std::vector<bool> BlockFullMatch;
  // std::vector<unsigned> TotalInstrStr;
  bool HasInFuncRepeated = false;
  DenseMap<Function *, std::vector<RepeatedItemInRegion *> *> *FuncItemMap;

  std::map<RepeatedItemInRegion *, std::map<Value *, std::vector<Use *>> *>
      RegionOutDefMap;
  std::map<RepeatedItemInRegion *, std::map<Value *, std::vector<Use *>> *>
      RegionOutUseMap;

  SetVector<Value *> Inputs;
  SetVector<Value *> Outputs;

  std::vector<Type *> InputsTypeList;
  std::vector<StringRef> InputsNameList;
  std::map<Type *, std::vector<int>> InputTypeArrangement;
  unsigned InputsParamListOffset = 0;

  std::vector<Type *> OutputsTypeList;
  std::vector<StringRef> OutputsNameList;
  std::map<Type *, std::vector<int>> OutputTypeArrangement;
  unsigned OutputsParamListOffset = 0;

  StructType *StructTy = nullptr;

  Function *MergedFunc = nullptr;
  FunctionType *MergedFuncType = nullptr;
  // std::vector<Type *> ArgumentTypes;
  std::vector<BasicBlock *> OutputStoreBBs;

  std::vector<std::map<BasicBlock *, BasicBlock *> *> NewBB2OldBBList;
  ValueMap<const Value *, WeakTrackingVH> VMap;
  std::unordered_map<Value *, BasicBlock *> MatchedValues2NBB;

  ValueMap<const Value *, WeakTrackingVH> InputsToArgs;

  void addMatchedBBRelation(unsigned OldBBIndex, BasicBlock *NewLabelBB);
  void addMatchedInstRelation(unsigned OldInstIndex,
                              Instruction *NewInstruction);

  void buildArgumentsRelation();
  void coalescingBBsSplitBefore();

  // void addMatchedNewBB2OldBBList();

  // return index
  int addInputParam(Type *ParamType, StringRef ParamName);
  int addOutputParam(Type *ParamType, StringRef ParamName);
  // return -1 if not find, return index(0+) if find;
  int findParamForInput(Value *Input, std::vector<int> &OccupiedList);
  int findParamForOutput(Value *Output, std::vector<int> &OccupiedList);

  //用于实现merging的函数
  // funcs for merging
  bool getInputsTypeList();
  bool getOutputsTypeList();
  bool getInputsTypeListForFF();

  int getCallOverhead();
  int getMergeFunctionOverhead();
  int getCallOverheadForBinary(TargetTransformInfo &TTI);
  int getMergeFunctionOverheadForBinary(TargetTransformInfo &TTI);
  int getNewBenefit(TargetTransformInfo &TTI);
  // tools
  Instruction *cloneInst(IRBuilder<> &Builder, Function *MF, Instruction *I);

  BasicBlock *chainBlocks(BasicBlock *SrcBB, BasicBlock *TargetBB,
                          Value *IsFunc, unsigned CaseValue);
  void fillWithEachCandidate(std::vector<BasicBlock *> &Blocks,
                             std::map<BasicBlock *, BasicBlock *> &BBMap,
                             Value *IsFunc1, unsigned CaseValue,
                             BasicBlock *NewFuncRoot, BasicBlock *SourcePrevBB);
  bool AssignLabelOperands(Instruction *I,
                           std::map<BasicBlock *, BasicBlock *> &BlocksReMap);
  bool AssignValueOperands(Instruction *I,
                           std::map<BasicBlock *, BasicBlock *> &BlocksReMap);

  //打印函数
  // funcs for printing statistics
};

/**
 * RegionAbstractManager : class for managing info of all candidates
 */
class RegionAbstractManager {
public:
  Module &M;
  std::vector<RARegionGroup *> CandidateList;
  std::vector<RARegionGroup *> IntraBlockCandidateList;

  DenseSet<BasicBlock *> NonSplittableBlockSet;
  std::vector<BasicBlock *> BlocksToDelete;
  RegionAbstractManager(Module &M0) : M(M0) {}
  unsigned CreatedMergedFunctionNum = 0;
  std::vector<Function *> CreatedMergedFuncList;
  std::set<Function *> AffectedFuncs;

  // top level
  bool
  getCandidateList(std::vector<RepeatedInfos::RepeatedSubstringByS *> &RSList,
                   std::vector<InstrData *> &InstrList, RegionAbstract &RA);

  bool mergeCandidateList();

  bool getAndMergeCandidateList(
      std::vector<RepeatedInfos::RepeatedSubstringByS *> &RSList,
      std::vector<InstrData *> &InstrList, RegionAbstract &RA);

  // mid level
  void analysisRegionGroup(RARegionGroup *Group, RegionMergeInfo &RMI);
  bool mergeRegionGroup(RARegionGroup *Group, RegionMergeInfo &RMI);

  // bottom/implementation level
  Function *createMergedFunc(RARegionGroup *Group, RegionMergeInfo &RMI,
                             unsigned FunctionNameSuffix);
  bool fillMergedFunc(RARegionGroup *Group, RegionMergeInfo &RMI);
  bool replaceCodeWithCall(RARegionGroup *Group, RegionMergeInfo &RMI);

  void getGroupParamsList(RegionMergeInfo &RMI);
  int getGroupBenefit(RegionMergeInfo &RMI);
  void updateNonSplittableBlockSet(RepeatedItemInRegion *Region);
  void removeFromNonSplittableBlockSet(RepeatedItemInRegion *Region);
  int getFinallBenefit(RegionMergeInfo &RMI) { return 1; }
};

#pragma endregion
} // namespace llvm

#endif