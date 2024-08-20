/*
 * @Author: Zichen Li
 * @Email: zichen.li@whu.edu.cn
 * @Date: 2024-06-13 22:34:23
 * @FilePath: /llvm-14/include/llvm/CodeGen/MachineRegionAbstract.h
 */

#ifndef LLVM_CODEGEN_MACHINEREGIONABSTRACT_H
#define LLVM_CODEGEN_MACHINEREGIONABSTRACT_H

//#define DEBUG_TYPE "machine-region-abstract"

#include "llvm/InitializePasses.h"
#include "llvm/CodeGen/LivePhysRegs.h"
#include "llvm/CodeGen/LiveRegUnits.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/MachineRegionInfo.h"
#include "llvm/CodeGen/MachineRegionInfo.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/MachineOptimizationRemarkEmitter.h"
#include "llvm/Support/SuffixTreeRepeatedInfos.h"
#include "llvm/ADT/SetVector.h"
#include <unordered_map>
#include <iostream>

namespace llvm {
namespace machine_region_abstract
{
    
enum InstrType { Legal, LegalTerminator, Illegal, Invisible };

struct MachineRepeatedItemInRegion;
struct MachineRegionMergeInfo;
typedef std::vector<MachineRepeatedItemInRegion *> MRARegionGroup;

#pragma region Lzc
struct LzcRegion {
  MachineBasicBlock *EntryBlock; // 第一个块
  MachineBasicBlock *ExitBlock; // 最后一个块
  bool NeedFullEntry = false;
  bool NeedFullExit = false;
  std::vector<MachineBasicBlock *> FollowBB;

  unsigned StartInstIndex = 0; //第一条指令在指令序列中的起始位置
  unsigned EndInstIndex = 0;

  std::vector<MachineBasicBlock *> Blocks;
  // DFS的Blocks
  LzcRegion(MachineRegion *SourceRegion);
  // 乱序的Blocks，0-->Exit, 1-->Entry
  LzcRegion(std::vector<MachineBasicBlock *> &ContainedBBs);

  MachineBasicBlock *getEntry() { return EntryBlock; }
  MachineBasicBlock *getExit() { return ExitBlock; }

  void updateEntry(MachineBasicBlock *NewEntry);
  void updateExit(MachineBasicBlock *NewExit);

  /// Check if a Region is the TopLevel region.
  ///
  /// The toplevel region represents the whole function.
  bool isTopLevelRegion() const { return ExitBlock == nullptr; }
};

// alias for MachineRepeatedItemInRegion
typedef MachineRepeatedItemInRegion MRARegionCandidate;
struct MachineRepeatedItemInRegion {
  MachineFunction *ParentFunc;
  LzcRegion *MinRegion;
  bool RegionSplit = false;
  // case 0, keep 1 Inst in entry block, keep 0 Inst in exit block
  // case 1,  keep full entry block or exit block
  // case 2, keep part of Releated Instructions
  // default, same to case 0
  unsigned EntryBlockSplitMode = 0;
  unsigned ExitBlockSplitMode = 0;

  std::vector<MachineBasicBlock *> RelatedMBlocks;
  DenseSet<MachineBasicBlock *> RelatedMBBSet;

  bool HasExitExtraPHI = false;
  SetVector<MachineInstr *> ExitExtraPHI;
  //把上面两个合并成下面一个
  // SetVector<BasicBlock *> ReleatedBBs;

  std::vector<MachineInstr *> RepeatedInstrDatas;
  SetVector<MachineInstr *> RepeatedInstSet;

  std::map<unsigned, std::vector<std::pair<int[2], int[2]>>> BlockMapping;

  MachineBasicBlock *StartBB = nullptr, *EndBB = nullptr;
  MachineBasicBlock *PrevBB = nullptr, *FollowBB = nullptr;
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

  // public:


  void dump();
  void dumpOnly();
  void printAllInsts();
  void printAllInsts(raw_ostream &OFS);
  bool getMinRegion(MachineRegionInfo *MRI);
  bool getMinRegionForIntraBBRS();
  bool updatePhiBlock(MachineBasicBlock *NewBB, MachineBasicBlock *OldBB);
  bool splitRegion(DenseSet<MachineBasicBlock *> &NonSplittableBlockSet,
                   std::set<MachineFunction *> &AffectedFuncs);
  bool splitRepeatedSubstring(DenseSet<MachineBasicBlock *> &NonSplittableBlockSet,
                              std::set<MachineFunction *> &AffectedFuncs);

  void addInputParam(int InputIndex, int Index);
  void addOutputParam(int OutputIndex, int Index);

private:
  void printInfo();




};

/**
 * RegionMergeInfo : class for managing info of a single candidate group
 */
struct MachineRegionMergeInfo {
  MRARegionGroup *CurrGroup;
  MachineRegionMergeInfo(MRARegionGroup *Group) : CurrGroup(Group) {}


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

  SetVector<MachineBasicBlock *> CreatedMatchBBs;
  SetVector<MachineBasicBlock *> CreatedMisMatchBBs;
  SetVector<MachineBasicBlock *> CreatedOverheadBBs;

  SetVector<MachineInstr *> CreatedOverheadBranches;
  SetVector<MachineBasicBlock *> BlocksToDelete;
  SetVector<MachineInstr *> MisMatchInsrInMatchedBB;

  std::map<MachineInstr *, Value *> InstrReplacedFrom;
  std::map<MachineInstr *, std::vector<unsigned>> InstrReplacedOpNums;
  std::map<MachineInstr *, Value *> InstrReplacedTo;
  std::map<PHINode *, MachineBasicBlock *> PNIncomingAdded;

  std::vector<bool> BlockFullMatch;
  // std::vector<unsigned> TotalInstrStr;
  bool HasInFuncRepeated = false;
  DenseMap<MachineFunction *, std::vector<MachineRepeatedItemInRegion *> *> *FuncItemMap;

  std::map<MachineRepeatedItemInRegion *, std::map<Value *, std::vector<Use *>> *>
      RegionOutDefMap;
  std::map<MachineRepeatedItemInRegion *, std::map<Value *, std::vector<Use *>> *>
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

  MachineFunction *MergedFunc = nullptr;
  FunctionType *MergedFuncType = nullptr;
  // std::vector<Type *> ArgumentTypes;
  std::vector<MachineBasicBlock *> OutputStoreBBs;

  std::vector<std::map<MachineBasicBlock *, MachineBasicBlock *> *> NewBB2OldBBList;
  ValueMap<const Value *, WeakTrackingVH> VMap;
  std::unordered_map<Value *, MachineBasicBlock *> MatchedValues2NBB;

  ValueMap<const Value *, WeakTrackingVH> InputsToArgs;

  void addMatchedBBRelation(unsigned OldBBIndex, MachineBasicBlock *NewLabelBB);
  void addMatchedInstRelation(unsigned OldInstIndex,
                              MachineInstr *NewInstruction);

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
  // int getCallOverheadForBinary(TargetTransformInfo &TTI);
  // int getMergeFunctionOverheadForBinary(TargetTransformInfo &TTI);
  // int getNewBenefit(TargetTransformInfo &TTI);
  // tools
  //Instruction *cloneInst(IRBuilder<> &Builder, MachineFunction *MF, Instruction *I);

  MachineBasicBlock *chainBlocks(MachineBasicBlock *SrcBB, MachineBasicBlock *TargetBB,
                          Value *IsFunc, unsigned CaseValue);
  void fillWithEachCandidate(std::vector<MachineBasicBlock *> &Blocks,
                             std::map<MachineBasicBlock *, MachineBasicBlock *> &BBMap,
                             Value *IsFunc1, unsigned CaseValue,
                             MachineBasicBlock *NewFuncRoot, MachineBasicBlock *SourcePrevBB);
  bool AssignLabelOperands(MachineInstr *MI,
                           std::map<MachineBasicBlock *, MachineBasicBlock *> &BlocksReMap);
  bool AssignValueOperands(MachineInstr *MI,
                           std::map<MachineBasicBlock *, MachineBasicBlock *> &BlocksReMap);

  //打印函数
  // funcs for printing statistics
};

struct InstructionMapper {

  /// The next available integer to assign to a \p MachineInstr that
  /// cannot be outlined.
  ///
  /// Set to -3 for compatability with \p DenseMapInfo<unsigned>.
  unsigned IllegalInstrNumber = -3;

  /// The next available integer to assign to a \p MachineInstr that can
  /// be outlined.
  unsigned LegalInstrNumber = 0;

  /// Correspondence from \p MachineInstrs to unsigned integers.
  DenseMap<MachineInstr *, unsigned, MachineInstrExpressionTrait>
      InstructionIntegerMap;

  /// Correspondence between \p MachineBasicBlocks and target-defined flags.
  DenseMap<MachineBasicBlock *, unsigned> MBBFlagsMap;

  /// The vector of unsigned integers that the module is mapped to.
  std::vector<unsigned> UnsignedVec;

  /// Stores the location of the instruction associated with the integer
  /// at index i in \p UnsignedVec for each index i.
  std::vector<MachineBasicBlock::iterator> InstrList;

  // Set if we added an illegal number in the previous step.
  // Since each illegal number is unique, we only need one of them between
  // each range of legal numbers. This lets us make sure we don't add more
  // than one illegal number per range.
  bool AddedIllegalLastTime = false;

  /// Maps \p *It to a legal integer.
  ///
  /// Updates \p CanOutlineWithPrevInstr, \p HaveLegalRange, \p InstrListForMBB,
  /// \p UnsignedVecForMBB, \p InstructionIntegerMap, and \p LegalInstrNumber.
  ///
  /// \returns The integer that \p *It was mapped to.
  unsigned mapToLegalUnsigned(
      MachineBasicBlock::iterator &It, bool &CanOutlineWithPrevInstr,
      bool &HaveLegalRange, unsigned &NumLegalInBlock,
      std::vector<unsigned> &UnsignedVecForMBB,
      std::vector<MachineBasicBlock::iterator> &InstrListForMBB) {
    // We added something legal, so we should unset the AddedLegalLastTime
    // flag.
    AddedIllegalLastTime = false;

    // If we have at least two adjacent legal instructions (which may have
    // invisible instructions in between), remember that.
    if (CanOutlineWithPrevInstr)
      HaveLegalRange = true;
    CanOutlineWithPrevInstr = true;

    // Keep track of the number of legal instructions we insert.
    NumLegalInBlock++;

    // Get the integer for this instruction or give it the current
    // LegalInstrNumber.
    InstrListForMBB.push_back(It);
    MachineInstr &MI = *It;
    bool WasInserted;
    DenseMap<MachineInstr *, unsigned, MachineInstrExpressionTrait>::iterator
        ResultIt;
    std::tie(ResultIt, WasInserted) =
        InstructionIntegerMap.insert(std::make_pair(&MI, LegalInstrNumber));
    unsigned MINumber = ResultIt->second;

    // There was an insertion.
    if (WasInserted)
      LegalInstrNumber++;

    UnsignedVecForMBB.push_back(MINumber);

    // Make sure we don't overflow or use any integers reserved by the DenseMap.
    if (LegalInstrNumber >= IllegalInstrNumber)
      report_fatal_error("Instruction mapping overflow!");

    assert(LegalInstrNumber != DenseMapInfo<unsigned>::getEmptyKey() &&
           "Tried to assign DenseMap tombstone or empty key to instruction.");
    assert(LegalInstrNumber != DenseMapInfo<unsigned>::getTombstoneKey() &&
           "Tried to assign DenseMap tombstone or empty key to instruction.");

    return MINumber;
  }

  /// Maps \p *It to an illegal integer.
  ///
  /// Updates \p InstrListForMBB, \p UnsignedVecForMBB, and \p
  /// IllegalInstrNumber.
  ///
  /// \returns The integer that \p *It was mapped to.
  unsigned mapToIllegalUnsigned(
      MachineBasicBlock::iterator &It, bool &CanOutlineWithPrevInstr,
      std::vector<unsigned> &UnsignedVecForMBB,
      std::vector<MachineBasicBlock::iterator> &InstrListForMBB) {
    // Can't outline an illegal instruction. Set the flag.
    CanOutlineWithPrevInstr = false;

    // Only add one illegal number per range of legal numbers.
    if (AddedIllegalLastTime)
      return IllegalInstrNumber;

    // Remember that we added an illegal number last time.
    AddedIllegalLastTime = true;
    unsigned MINumber = IllegalInstrNumber;

    InstrListForMBB.push_back(It);
    UnsignedVecForMBB.push_back(IllegalInstrNumber);
    IllegalInstrNumber--;

    assert(LegalInstrNumber < IllegalInstrNumber &&
           "Instruction mapping overflow!");

    assert(IllegalInstrNumber != DenseMapInfo<unsigned>::getEmptyKey() &&
           "IllegalInstrNumber cannot be DenseMap tombstone or empty key!");

    assert(IllegalInstrNumber != DenseMapInfo<unsigned>::getTombstoneKey() &&
           "IllegalInstrNumber cannot be DenseMap tombstone or empty key!");

    return MINumber;
  }

  /// Transforms a \p MachineBasicBlock into a \p vector of \p unsigneds
  /// and appends it to \p UnsignedVec and \p InstrList.
  ///
  /// Two instructions are assigned the same integer if they are identical.
  /// If an instruction is deemed unsafe to outline, then it will be assigned an
  /// unique integer. The resulting mapping is placed into a suffix tree and
  /// queried for candidates.
  ///
  /// \param MBB The \p MachineBasicBlock to be translated into integers.
  /// \param TII \p TargetInstrInfo for the function.
  void convertToUnsignedVec(MachineBasicBlock &MBB,
                            const TargetInstrInfo &TII) {
    unsigned Flags = 0;

    // Don't even map in this case.
    if (!TII.isMBBSafeToOutlineFrom(MBB, Flags))
      return;

    // Store info for the MBB for later outlining.
    MBBFlagsMap[&MBB] = Flags;

    MachineBasicBlock::iterator It = MBB.begin();

    // The number of instructions in this block that will be considered for
    // outlining.
    unsigned NumLegalInBlock = 0;

    // True if we have at least two legal instructions which aren't separated
    // by an illegal instruction.
    bool HaveLegalRange = false;

    // True if we can perform outlining given the last mapped (non-invisible)
    // instruction. This lets us know if we have a legal range.
    bool CanOutlineWithPrevInstr = false;

    // FIXME: Should this all just be handled in the target, rather than using
    // repeated calls to getOutliningType?
    std::vector<unsigned> UnsignedVecForMBB;
    std::vector<MachineBasicBlock::iterator> InstrListForMBB;

    unsigned MINumber;
    raw_ostream &OS = dbgs();

    OS << MBB.getFullName() << "\n";

    for (MachineBasicBlock::iterator Et = MBB.end(); It != Et; ++It) {
      // Keep track of where this instruction is in the module.
      switch (TII.getRAType(It, Flags)) {
      case InstrType::Illegal:
        mapToIllegalUnsigned(It, CanOutlineWithPrevInstr, UnsignedVecForMBB,
                             InstrListForMBB);
        break;

      case InstrType::Legal:
        MINumber = mapToLegalUnsigned(It, CanOutlineWithPrevInstr, HaveLegalRange,
                           NumLegalInBlock, UnsignedVecForMBB, InstrListForMBB);
        OS << "   " << MINumber << "   ";
        It->dump();
        break;

      case InstrType::LegalTerminator:
        mapToLegalUnsigned(It, CanOutlineWithPrevInstr, HaveLegalRange,
                           NumLegalInBlock, UnsignedVecForMBB, InstrListForMBB);
        // The instruction also acts as a terminator, so we have to record that
        // in the string.
        mapToIllegalUnsigned(It, CanOutlineWithPrevInstr, UnsignedVecForMBB,
                             InstrListForMBB);
        break;

      case InstrType::Invisible:
        // Normally this is set by mapTo(Blah)Unsigned, but we just want to
        // skip this instruction. So, unset the flag here.
        AddedIllegalLastTime = false;
        break;
      }
    }

    // Are there enough legal instructions in the block for outlining to be
    // possible?
    if (HaveLegalRange) {
      // After we're done every insertion, uniquely terminate this part of the
      // "string". This makes sure we won't match across basic block or function
      // boundaries since the "end" is encoded uniquely and thus appears in no
      // repeated substring.
      //lzc,修改
      // mapToIllegalUnsigned(It, CanOutlineWithPrevInstr, UnsignedVecForMBB,
      //                      InstrListForMBB);
      llvm::append_range(InstrList, InstrListForMBB);
      llvm::append_range(UnsignedVec, UnsignedVecForMBB);
    }
  }

  InstructionMapper() {
    // Make sure that the implementation of DenseMapInfo<unsigned> hasn't
    // changed.
    assert(DenseMapInfo<unsigned>::getEmptyKey() == (unsigned)-1 &&
           "DenseMapInfo<unsigned>'s empty key isn't -1!");
    assert(DenseMapInfo<unsigned>::getTombstoneKey() == (unsigned)-2 &&
           "DenseMapInfo<unsigned>'s tombstone key isn't -2!");
  }
};

// MIR层区域抽象的总控程序
struct MachineRegionAbstract : public ModulePass
{

  static char ID;

  /// Set to true if the outliner should consider functions with
  /// linkonceodr linkage.
  bool OutlineFromLinkOnceODRs = false;
  
  /// The current repeat number of machine outlining.
  unsigned OutlineRepeatedNum = 0;

  /// Set to true if the outliner should run on all functions in the module
  /// considered safe for outlining.
  /// Set to true by default for compatibility with llc's -run-pass option.
  /// Set when the pass is constructed in TargetPassConfig.
  bool RunOnAllFunctions = true;

  StringRef getPassName() const override { return "Machine Region Abstract "; }
    
  //设置依赖关系
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<MachineModuleInfoWrapperPass>();
    AU.addPreserved<MachineModuleInfoWrapperPass>();
    AU.setPreservesAll();
    ModulePass::getAnalysisUsage(AU);
  }

  MachineRegionAbstract() : ModulePass(ID) {
    initializeMachineRegionAbstractPass(*PassRegistry::getPassRegistry());
  }

  // /// Remark output explaining that not outlining a set of candidates would be
  // /// better than outlining that set.
  // void emitNotOutliningCheaperRemark(
  //     unsigned StringLen, std::vector<Candidate> &CandidatesForRepeatedSeq,
  //     OutlinedFunction &OF);

  // /// Remark output explaining that a function was outlined.
  // void emitOutlinedFunctionRemark(OutlinedFunction &OF);

  bool runOnModule(Module &M) override;
  
    /// Populate and \p InstructionMapper with instruction-to-integer mappings.
  /// These are used to construct a suffix tree.
  void populateMapper(InstructionMapper &Mapper, Module &M,
                      MachineModuleInfo &MMI);

};


class MachineRegionAbstractManager {
public:
  Module &M;
  InstructionMapper &Mapper;
  std::vector<MRARegionGroup *> CandidateList;
  std::vector<MRARegionGroup *> IntraBlockCandidateList;

  DenseSet<MachineBasicBlock *> NonSplittableBlockSet;
  std::vector<MachineBasicBlock *> BlocksToDelete;
  unsigned CreatedMergedFunctionNum = 0;
  unsigned NumRAed = 0;
  std::vector<MachineFunction *> CreatedMergedFuncList;
  std::set<MachineFunction *> AffectedFuncs;
  MachineModuleInfo &MMI;//需要获得的MIR层信息

  MachineRegionAbstractManager(Module &M0, MachineModuleInfo &MMI, InstructionMapper &Mapper) : M(M0), MMI(MMI), Mapper(Mapper) {};


  // top level
  bool
  getCandidateList(std::vector<RepeatedInfos::RepeatedSubstringByS *> &RSList,
                   std::vector<MachineBasicBlock::iterator> &InstrList, MachineRegionAbstract &MRA);

  bool mergeCandidateList();

  bool getAndMergeCandidateList(
      std::vector<RepeatedInfos::RepeatedSubstringByS *> &RSList,
      std::vector<MachineBasicBlock::iterator> &InstrList, MachineRegionAbstract &MRA);

  // mid level
  void analysisRegionGroup(MRARegionGroup *Group, MachineRegionMergeInfo &MRMI);
  bool mergeRegionGroup(MRARegionGroup *Group, MachineRegionMergeInfo &MRMI);

  // bottom/implementation level
  MachineFunction *createMergedFunc(MRARegionGroup *Group, MachineRegionMergeInfo &MRMI,
                             unsigned FunctionNameSuffix);
  bool fillMergedFunc(MRARegionGroup *Group, MachineRegionMergeInfo &MRMI);
  bool replaceCodeWithCall(MRARegionGroup *Group, MachineRegionMergeInfo &MRMI);

  void getGroupParamsList(MachineRegionMergeInfo &MRMI);
  int getGroupBenefit(MachineRegionMergeInfo &MRMI);
  void updateNonSplittableBlockSet(MachineRepeatedItemInRegion *Region);
  void removeFromNonSplittableBlockSet(MachineRepeatedItemInRegion *Region);
  int getFinallBenefit(MachineRegionMergeInfo &MRMI) { return 1; }
  bool replaceCall(MRARegionGroup *Group,
                                        MachineRegionMergeInfo &MRMI);

  //工具，用于打印变量
  void printMIR();

  //void setMapper(InstructionMapper)
};




#pragma endregion    

} // namespace machine_region_abstract
} // namespace llvm



#endif