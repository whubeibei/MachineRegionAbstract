#include "llvm/Transforms/Utils/FunctionFolding.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/Support/SuffixTreeRepeatedInfos.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/RegionAbstract.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include <vector>

using namespace llvm;

static cl::opt<bool> Debug("func-folding-debug", cl::init(false), cl::Hidden,
                           cl::desc("Outputs debug information"));

static cl::opt<unsigned> FFLimit(
    "func-folding-limit", cl::init(2), cl::Hidden,
    cl::desc("Lower limit of repeated substring length of function folding"));

static cl::opt<bool> LogAll("func-folding-log-all", cl::init(false), cl::Hidden,
                            cl::desc("Outputs all debug information"));

static cl::opt<bool> FFIB("func-folding-intra-bb", cl::init(true), cl::Hidden,
                          cl::desc("folding intra-basicblock, default true."));

using IRSimilarity::InstrData;

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

PreservedAnalyses FunctionFoldingPass::run(Function &F,
                                           FunctionAnalysisManager &AM) {
  if (F.isDeclaration() ||
      F.getLinkage() == GlobalValue::AvailableExternallyLinkage) {
    return PreservedAnalyses::all();
  }

  // if (F.getName() == "main") {
  //   return PreservedAnalyses::all();
  // }

  // if (F.getName() != "RGBTransformImage") {
  //   return PreservedAnalyses::all();
  // }

  // F.dump();
  // F.viewCFG();

  IRSimilarity::IRInstrMapper IRMapper = IRSimilarity::IRInstrMapper();
  std::vector<InstrData *> InstrList;
  std::vector<unsigned> IntegerMapping;
  IRMapper.populateFunctionDFS(F, InstrList, IntegerMapping);

  SuffixTree ST(IntegerMapping);

  RepeatedInfos ReptInfo(ST, FFLimit.getValue());
  std::vector<RepeatedInfos::RepeatedSubstringByS *> NewRSList =
      ReptInfo.RSList;

  std::vector<unsigned> StrMap = ST.Str;
  RepeatedInfos::elimateInterOverlap(NewRSList, StrMap, 3);

  unsigned NewTotalBenefit = 0;
  std::for_each(NewRSList.begin(), NewRSList.end(),
                [&NewTotalBenefit](RepeatedInfos::RepeatedSubstringByS *RS) {
                  NewTotalBenefit += RS->getPredictBenefit(3);
                });
                

  // to compare two function
  unsigned OldTotalBenefit =
      RepeatedInfos::analysisOld(ST, FFLimit.getValue(), 3);
  int TTInstrCount = F.getInstructionCount();

  if (Debug && (LogAll || NewTotalBenefit > 0 || OldTotalBenefit > 0)) {
    errs() << F.getName() << ", " << OldTotalBenefit << ", " << NewTotalBenefit
           << ", " << TTInstrCount << "\n";
  }

  if (LogAll){
    errs() << F.getName() << ", " << OldTotalBenefit << ", " << NewTotalBenefit
           << ", " << TTInstrCount << "\n";
    return PreservedAnalyses::all();
  }
    

  FunctionFolding FF(F);
  bool Changed = FF.getCandidateList(NewRSList, InstrList);

  int NewIC = F.getInstructionCount();
  if (Debug){
    errs() << F.getName() << ", " << TTInstrCount - NewIC << ", " << TTInstrCount
        << ", " << NewIC << "\n";
  }

  return PreservedAnalyses::none();
  // return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}

bool FunctionFolding::getCandidateList(
    std::vector<RepeatedInfos::RepeatedSubstringByS *> &RSList,
    std::vector<InstrData *> &InstrList) {

  // IntraBlockCandidate for initially implementation.
  int Times = 0;
  if (Debug ) {
    std::string Path0 = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                        F.getName().str() + ".log";
    raw_fd_ostream *FS = getOutputStreamOfFile(Path0);
    *FS << F;
    delete FS;
  }

  //收集到这两个region中
  // std::vector<RARegionGroup *> CandidateList;
  // std::vector<RARegionGroup *> IntraBlockCandidateList;

  // for (RepeatedInfos::RepeatedSubstringByS *RS : RSList) {
  //   errs() << RS->getPredictBenefit(3) << ", repeat " <<
  //   RS->StartIndices.size()
  //          << " times\n";
  //   for (int Idx = 0; Idx < RS->StartIndices.size(); Idx++) {
  //     int StartIdx = RS->StartIndices[Idx];
  //     for (int I = 0; I < RS->Length; I++) {
  //       InstrList[StartIdx + I]->Inst->dump();
  //     }
  //     errs() << "\n";
  //   }
  // }

  //从RSList中找到每个重复的Function、blocks，找到region，判断region之间是否有重叠，有重叠就合并成一个
  for (RepeatedInfos::RepeatedSubstringByS *RS : RSList) {

    if (Debug ) {
      std::string Path0 = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                          F.getName().str() + "before" + to_string(Times) +
                          ".log";
      raw_fd_ostream *FS = getOutputStreamOfFile(Path0);
      *FS << F;
      delete FS;
    }

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
      bool GenEntryError = false;

      for (unsigned InstrIt = StartIdx; InstrIt < StartIdx + RS->Length;
           InstrIt++) {
        InstrData *ID = InstrList[InstrIt];
        assert(ID->IDType >= 0 &&
               "Error: Instruction Data Type should be positive number!");
        Entry->RepeatedInstrDatas.push_back(ID);
        Entry->RepeatedInstSet.insert(ID->Inst);
        BasicBlock *BB = ID->Inst->getParent();
        if (!BB) {
          GenEntryError = true;
          break;
        }
        if (!ReleatedBBs.contains(BB)) {
          ReleatedBBs.insert(BB);
          Entry->ReleatedBlocks.push_back(BB);
        }
      } // end for 3

      if (GenEntryError) {
        delete Entry;
        continue;
      }

      if (ReleatedBBs.size() < 2) {
        if (FFIB.getValue()) {
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
        RegionInfo *RI = nullptr;

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
      if (IntraBlock) {
        IntraBlockCandidateList.push_back(RegionGroup);

        RegionMergeInfo RMI(RegionGroup);
        RMI.MergedFunc = &F;
        analysisRegionGroup(RegionGroup, RMI);

        int Benefit = getGroupBenefit(RMI);
        int LowerLimit = 0;
        if (Benefit > LowerLimit) {
          if (mergeRegionGroup(RegionGroup, RMI, Benefit)) {
          }
        } else {
          RMI.coalescingBBsSplitBefore();
          DominatorTree NDT(F);
        }
        // if (Times == 1)
        //   break;

        if (Debug ) {
          std::string Path0 =
              "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
              F.getName().str() + "after" + to_string(Times) + ".log";
          raw_fd_ostream *FS = getOutputStreamOfFile(Path0);
          *FS << F;
          delete FS;
        }
        if (verifyFunction(F)) {
          verifyFunction(F);
          // errs() << "ERROR: Produced Broken Function: " << F.getName() << "
          // !\n"; F.dump(); assert(false);
        }
        Times++;
      } else {
        CandidateList.push_back(RegionGroup);
      }
    }

    if (FaliedGroup->size() >= 2) {
      if (Debug)
        errs() << "Retry to find region for failed rs.\n";
    }
  }

  // for (RARegionGroup *CandidatePointer : IntraBlockCandidateList) {
  // }

  postProcessFunction(F);

  return true;
  // if (FFIB.getValue()) {
  //   return !CandidateList.empty() || !IntraBlockCandidateList.empty();
  // }
  // return !CandidateList.empty();
}

static bool definedInCaller(const SetVector<BasicBlock *> &Blocks, Value *V,
                            RegionMergeInfo &RMI) {
  //这里不再考虑参数问题
  if (isa<Argument>(V)) {
    RMI.VMap[V] = V;
    return false; // true
  }
  if (Instruction *I = dyn_cast<Instruction>(V)) {
    if (!Blocks.count(I->getParent())) {
      return true;
    }
  }
  return false;
}

bool RegionMergeInfo::getInputsTypeListForFF() {
  RepeatedItemInRegion *Cand0 = CurrGroup->front();
  std::vector<Value *> SameInputs;

  for (Value *Def : Cand0->Inputs) {
    bool IsSameInput = true;
    for (int I = 1; I < CurrGroup->size(); I++) {
      RepeatedItemInRegion *CandI = (*CurrGroup)[I];
      if (!CandI->Inputs.contains(Def)) {
        IsSameInput = false;
        break;
      }
    }

    if (IsSameInput) {
      SameInputs.push_back(Def);
    }
  }

  for (Value *SameInput : SameInputs) {
    Inputs.remove(SameInput);
  }

  for (RepeatedItemInRegion *Candidate : *CurrGroup) {
    for (Value *SameInput : SameInputs) {
      Candidate->Inputs.remove(SameInput);
      VMap[SameInput] = SameInput;
    }

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

void FunctionFolding::analysisRegionGroup(RARegionGroup *Group,
                                          RegionMergeInfo &RMI) {
  if (Group->size() < 2) {
    return;
  }
  if (Debug) {
    std::string Path0 = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                        (*Group)[0]->ParentFunc->getName().str() + ".0.log";
    raw_fd_ostream *FS = getOutputStreamOfFile(Path0);
    *FS << *(*Group)[0]->ParentFunc;
    delete FS;
  }
  DenseMap<Function *, RARegionGroup *> *FuncItemMap =
      new DenseMap<Function *, RARegionGroup *>();

  RARegionGroup MergeableRegions;

  // to delete
  std::set<Function *> AffectedFuncs;
  unsigned SplitIdx = 0;
  for (RepeatedItemInRegion *RegionCandidate : *Group) {
    SplitIdx++;
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
          if (definedInCaller(BlocksInRegion, VDef, RMI)) {
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
    if (Debug) {
      std::string Path0 = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                          (*Group)[0]->ParentFunc->getName().str() + "." +
                          to_string(SplitIdx) + ".log";
      raw_fd_ostream *FS = getOutputStreamOfFile(Path0);
      *FS << *(*Group)[0]->ParentFunc;
      delete FS;
    }
  }

  //获取整个Group的Input和Output
  // after analysis inputs and outputs, try to get the paramsList
  assert(RMI.getInputsTypeListForFF());
  assert(RMI.getOutputsTypeList());
}

int FunctionFolding::getGroupBenefit(RegionMergeInfo &RMI) {
  TargetTransformInfo TTI(
      (*RMI.CurrGroup)[0]->ParentFunc->getParent()->getDataLayout());
  int N = (*RMI.CurrGroup).size();
  int MatchLength = (*RMI.CurrGroup)[0]->RepeatedInstrDatas.size();
  int MatchBenefit = MatchLength * (N - 1);
  int Overhead = 3 * N + RMI.Inputs.size();
  return MatchBenefit - Overhead;
  //  return RMI.getNewBenefit(TTI);
}

bool FunctionFolding::mergeRegionGroup(RARegionGroup *Group,
                                       RegionMergeInfo &RMI, int Benefit) {
  // return false if no need to merge
  if (Group->size() < 2) {
    return false;
  }

  // to delete
  std::set<Function *> AffectedFuncs;
  int SplitIdx = 0;
  for (RepeatedItemInRegion *RegionCandidate : *Group) {
    SplitIdx++;
    RegionCandidate->splitRepeatedSubstring(NonSplittableBlockSet,
                                            AffectedFuncs);
    if (Debug) {
      std::string Path0 = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                          (*Group)[0]->ParentFunc->getName().str() + ".ss." +
                          to_string(SplitIdx) + ".log";
      raw_fd_ostream *FS = getOutputStreamOfFile(Path0);
      *FS << *(*Group)[0]->ParentFunc;
      delete FS;
    }
  }

  BasicBlock *EntryBB = createFoldingRegion(Group, RMI);

  if (fillMergedFunc(Group, RMI, EntryBB, Benefit)) {
    // removeOldRegion(Group, RMI, EntryBB);
    return true;
  } else {
    std::vector<BasicBlock *> CreatedBBs;
    CreatedBBs.insert(CreatedBBs.end(), RMI.CreatedMatchBBs.begin(),
                      RMI.CreatedMatchBBs.end());
    CreatedBBs.insert(CreatedBBs.end(), RMI.CreatedMisMatchBBs.begin(),
                      RMI.CreatedMisMatchBBs.end());
    CreatedBBs.insert(CreatedBBs.end(), RMI.CreatedOverheadBBs.begin(),
                      RMI.CreatedOverheadBBs.end());
    DeleteDeadBlocks(CreatedBBs);
    RMI.coalescingBBsSplitBefore();
    DominatorTree NDT(F);
  }

  return false;
}

BasicBlock *FunctionFolding::createFoldingRegion(RARegionGroup *Group,
                                                 RegionMergeInfo &RMI) {
  LLVMContext &Context = F.getContext();

  BasicBlock *EntryBB = BasicBlock::Create(Context, "ff.entry.bb", &F);
  // F.getBasicBlockList().push_back(EntryBB);

  RMI.InputsParamListOffset++;
  IRBuilder<> Builder(EntryBB);
  PHINode *SourceIdPHI = Builder.CreatePHI(IntegerType::get(Context, 32), 0);
  unsigned Idx = 0;

  for (RepeatedItemInRegion *R0 : *Group) {
    BasicBlock *SourceEntry = R0->ReleatedBlocks[0];

    for (auto It = pred_begin(SourceEntry), E = pred_end(SourceEntry); It != E;
         It++) {
      BasicBlock *NewPredBB = *It;
      SourceIdPHI->addIncoming(ConstantInt::get(Type::getInt32Ty(Context), Idx),
                               NewPredBB);
    }
    Idx++;
  }

  // input relation
  for (unsigned I = 0; I < RMI.InputsTypeList.size(); I++) {

    PHINode *InputPHI = Builder.CreatePHI(RMI.InputsTypeList[I], 0);
    for (RepeatedItemInRegion *Candidate : *RMI.CurrGroup) {

      BasicBlock *SourceEntry = Candidate->ReleatedBlocks[0];

      if (I >= Candidate->OccupiedListOfInput->size())
        continue;
      int InputIndex = (*Candidate->OccupiedListOfInput)[I];
      if (InputIndex < 0)
        continue;

      Value *Input = Candidate->Inputs[InputIndex];
      // RMI.VMap[Input] = InputPHI;
      RMI.InputsToArgs[Input] = InputPHI;

      for (auto It = pred_begin(SourceEntry), E = pred_end(SourceEntry);
           It != E; It++) {
        BasicBlock *NewPredBB = *It;
        InputPHI->addIncoming(Input, NewPredBB);
      }
    }
  }

  // SourceIdPHI->dump();
  // EntryBB->dump();
  // F.dump();
  if (Debug) {
    std::string Path0 = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                        (*Group)[0]->ParentFunc->getName().str() + ".init.log";
    raw_fd_ostream *FS = getOutputStreamOfFile(Path0);
    *FS << *(*Group)[0]->ParentFunc;
    delete FS;
  }
  return EntryBB;
}

bool FunctionFolding::fillMergedFunc(RARegionGroup *Group, RegionMergeInfo &RMI,
                                     BasicBlock *EntryBB, int Benefit) {

  BasicBlock *NewFuncRoot = EntryBB;
  BasicBlock *NewFuncExit = BasicBlock::Create(F.getContext(), "newFuncExit");
  F.getBasicBlockList().push_back(NewFuncExit);
  RMI.CreatedOverheadBBs.insert(NewFuncRoot);
  RMI.CreatedOverheadBBs.insert(NewFuncExit);

  std::vector<Instruction *> ListSelects;
  std::vector<AllocaInst *> Allocas;
  std::vector<unsigned> MatchedPHINodes;

  std::list<Instruction *> LinearOffendingInsts;
  std::set<Instruction *> OffendingInsts;
  std::vector<Value *> SourceIds;

  for (RepeatedItemInRegion *Candidate : *Group) {

    if (Candidate->FollowBB == nullptr) {
      std::vector<BasicBlock *> CreatedBBs;
      CreatedBBs.insert(CreatedBBs.end(), RMI.CreatedMatchBBs.begin(),
                        RMI.CreatedMatchBBs.end());
      CreatedBBs.insert(CreatedBBs.end(), RMI.CreatedMisMatchBBs.begin(),
                        RMI.CreatedMisMatchBBs.end());
      CreatedBBs.insert(CreatedBBs.end(), RMI.CreatedOverheadBBs.begin(),
                        RMI.CreatedOverheadBBs.end());
      DeleteDeadBlocks(CreatedBBs);
      RMI.coalescingBBsSplitBefore();
      DominatorTree NDT(F);
      // postProcessFunction(F);
      return true;
    }

    assert(Candidate->FollowBB != nullptr && "FollowBB is null!");
    // TODO: followBB should be followbb.
    RMI.VMap[Candidate->FollowBB] = NewFuncExit;
  }

  for (int I = 0; I < (*Group).size(); I++) {
    std::map<BasicBlock *, BasicBlock *> *MapI =
        new std::map<BasicBlock *, BasicBlock *>();
    RMI.NewBB2OldBBList.push_back(MapI);
  }
  // finish init

  // build relation for AggregateArgs Value
  Instruction *Arg0 = &NewFuncRoot->getInstList().front();
  Value *Idx[2];
  Idx[0] = Constant::getNullValue(Type::getInt32Ty(NewFuncRoot->getContext()));
  for (int I = 0; I < Group->size(); I++) {
    Value *SourceIdInt =
        ConstantInt::get(Type::getInt32Ty(NewFuncRoot->getContext()), I);
    CmpInst *SourceId =
        CmpInst::Create(Instruction::ICmp, ICmpInst::ICMP_EQ, Arg0, SourceIdInt,
                        "sourceid_" + to_string(I), NewFuncRoot);
    SourceIds.push_back(SourceId);
  }

  // F.dump();

  // Fill In Content
  unsigned CurrentMatchedInstIndex = 0;
  // 1. fill in content for match part
  for (unsigned I = 0; I < (*Group)[0]->ReleatedBlocks.size(); I++) {
    BasicBlock *LabelBB = BasicBlock::Create(F.getContext(), "m.label.bb", &F);
    RMI.CreatedMatchBBs.insert(LabelBB);
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

      BasicBlock *InstBB =
          isa<PHINode>(&Inst)
              ? LabelBB
              : BasicBlock::Create(F.getContext(), "m.inst.bb", &F);
      RMI.CreatedMatchBBs.insert(InstBB);

      IRBuilder<> Builder(InstBB);
      Instruction *NewI = RMI.cloneInst(Builder, &F, &Inst);
      RMI.addMatchedInstRelation(CurrentMatchedInstIndex, NewI);
      if (isa<PHINode>(&Inst)) {
        MatchedPHINodes.push_back(CurrentMatchedInstIndex);
      }

      CurrentMatchedInstIndex++;
    }
  }

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
          BasicBlock *SelectBB =
              BasicBlock::Create(BB1->getContext(), "bb.select", &F);
          RMI.CreatedOverheadBBs.insert(SelectBB);
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

        BasicBlock *LPadBB = BasicBlock::Create(F.getContext(), "lpad.bb", &F);
        RMI.CreatedOverheadBBs.insert(LPadBB);

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
  // Assign Value Operands
  LLVMContext &Context = F.getContext();

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

  for (Instruction *Instr : RMI.MisMatchInsrInMatchedBB) {
    // To Fix: the second param is never used, so it is setted to a wrong value.
    RMI.AssignValueOperands(Instr, (*RMI.NewBB2OldBBList[0]));
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
            ListSelects.push_back(NewSelect);
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

  // IRBuilder<> ExitBuilder(NewFuncExit);
  //     ExitBuilder.CreateBr((*Group).front()->FollowBB);
  if (Debug) {
    std::string Path0 = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                        (*Group)[0]->ParentFunc->getName().str() +
                        ".before-end-fix.log";
    raw_fd_ostream *FS = getOutputStreamOfFile(Path0);
    *FS << *(*Group)[0]->ParentFunc;
    delete FS;
  }

  BasicBlock *CurrBB = NewFuncExit;
  for (int I = 0; I < Group->size(); I++) {
    RepeatedItemInRegion *Candidate = (*Group)[I];
    BasicBlock *TmpBB =
        RMI.chainBlocks(CurrBB, Candidate->FollowBB, SourceIds[I], I);

    if (TmpBB) {
      // CurrBB = TmpBB;
    }

    BasicBlock *ExitBB = Candidate->EndBB;
    BasicBlock *OutSucc = Candidate->FollowBB;
    // OutSucc->dump();
    for (auto II = OutSucc->begin(), IE = OutSucc->end(); II != IE; ++II) {
      PHINode *PN = dyn_cast<PHINode>(II);
      if (!PN)
        break;

      Value *PNV = RMI.VMap[PN->getIncomingValueForBlock(ExitBB)];
      PNV = PNV ? PNV : PN->getIncomingValueForBlock(ExitBB);

      int PNIdx = PN->getBasicBlockIndex(CurrBB);
      if (PNIdx >= 0) {
        Value *LastV = PN->getIncomingValue(PNIdx);
        if (LastV != PNV) {
          IRBuilder<> Builder(CurrBB);
          SelectInst *Sel = SelectInst::Create(SourceIds[I], PNV, LastV);
          ListSelects.push_back(Sel);
          auto InsertPt = CurrBB->getFirstInsertionPt();
          if (CurrBB)
            CurrBB->getInstList().insert(InsertPt, Sel);
          Sel->setName("");
        }

      } else {
        PN->addIncoming(PNV, CurrBB);
        // PN->dump();
      }

      // PN->removeIncomingValue(ExitBB);
    }

    //删除旧块的末尾指令
    // if (Instruction *TI = ExitBB->getTerminator()) {
    //   TI->eraseFromParent();
    // }
  }

  for (Value *SourceId : SourceIds) {
    if (SourceId->user_empty()) {
      Instruction *I = dyn_cast<Instruction>(SourceId);
      // I->removeFromParent();
      I->eraseFromParent();
    }
  }
  if (Debug) {
    std::string Path1 = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                        (*Group)[0]->ParentFunc->getName().str() +
                        ".after-end-fix.log";
    raw_fd_ostream *FS2 = getOutputStreamOfFile(Path1);
    *FS2 << *(*Group)[0]->ParentFunc;
    delete FS2;
  }

  std::vector<BasicBlock *> CreatedBBs;
  CreatedBBs.insert(CreatedBBs.end(), RMI.CreatedMatchBBs.begin(),
                    RMI.CreatedMatchBBs.end());
  CreatedBBs.insert(CreatedBBs.end(), RMI.CreatedMisMatchBBs.begin(),
                    RMI.CreatedMisMatchBBs.end());
  CreatedBBs.insert(CreatedBBs.end(), RMI.CreatedOverheadBBs.begin(),
                    RMI.CreatedOverheadBBs.end());
  for (BasicBlock *BB : CreatedBBs) {
    if (Debug)
      errs() << BB->getName() << "\t";
  }
  if (Debug)
    errs() << "\n";

  // fix start
  //  redirect the predbb to entry
  //  for (RepeatedItemInRegion *Candidate : *RMI.CurrGroup) {
  //    Instruction *TermiI = Candidate->PrevBB->getTerminator();
  //    IRBuilder<> Builder(Candidate->PrevBB);
  //    if (TermiI) {
  //      BranchInst *Br = dyn_cast<BranchInst>(TermiI);
  //      assert(Br && "Branch should not be null!");
  //      Br->eraseFromParent();
  //      Builder.CreateBr(EntryBB);
  //    }
  //  }
  // fix start and end
  Benefit = Benefit - (ListSelects.size() + RMI.CreatedOverheadBranches.size());

  if (Benefit <= 0) {
    DeleteDeadBlocks(CreatedBBs);
    RMI.coalescingBBsSplitBefore();
    DominatorTree NDT(F);
    // postProcessFunction(F);

    return true;
  } else {
    removeOldRegion(Group, RMI, EntryBB);
    // fix input phi nodes
    SmallVector<BasicBlock *, 8> Preds(predecessors(EntryBB));
    for (auto It = EntryBB->begin(), Et = EntryBB->end(); It != Et; It++) {
      PHINode *PN = dyn_cast<PHINode>(It);
      if (!PN)
        continue;
      if (PN->getNumIncomingValues() == Preds.size()) {
        continue;
      }
      for (BasicBlock *Pred : Preds) {
        if (PN->getBasicBlockIndex(Pred) < 0) {
          PN->addIncoming(UndefValue::get(PN->getType()), Pred);
          RMI.PNIncomingAdded[PN] = Pred;
        }
      }
    }
  }

  // fix Instruction dominace
  DominatorTree DT(F);

  if (Debug) {
    std::string Path = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                       (*Group)[0]->ParentFunc->getName().str() + ".fix0.log";
    raw_fd_ostream *FS2 = getOutputStreamOfFile(Path);
    *FS2 << *(*Group)[0]->ParentFunc;
    delete FS2;
  }

  // find instructions need fix
  for (Instruction &I : instructions(F)) {
    if (RMI.BlocksToDelete.contains(I.getParent())) {
      continue;
    }

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
              RMI.BrokenDomRelationDefNum++;
            }
            RMI.BrokenDomRelationUseNum++;
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
              RMI.BrokenDomRelationDefNum++;
            }
            RMI.BrokenDomRelationUseNum++;
          }
        }
      }
    }
  }

  if ((Benefit - RMI.BrokenDomRelationDefNum - RMI.BrokenDomRelationUseNum) <=
      0) {
    // recover
    // reuse old region
    if (Debug) {
      std::string Path1 = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                          (*Group)[0]->ParentFunc->getName().str() +
                          ".after-end-fixM.log";
      raw_fd_ostream *FS2 = getOutputStreamOfFile(Path1);
      *FS2 << *(*Group)[0]->ParentFunc;
      delete FS2;
    }
    reuseOldRegion(Group, RMI, EntryBB);
    if (Debug) {
      std::string Path1 = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                          (*Group)[0]->ParentFunc->getName().str() +
                          ".after-end-fixN.log";
      raw_fd_ostream *FS2 = getOutputStreamOfFile(Path1);
      *FS2 << *(*Group)[0]->ParentFunc;
      delete FS2;
    }
    DeleteDeadBlocks(CreatedBBs);
    RMI.coalescingBBsSplitBefore();
    DominatorTree NDT(F);
    // postProcessFunction(F);
    return true;
  }

  DeleteDeadBlocks(RMI.BlocksToDelete.getArrayRef());

  if (Debug) {
    std::string Pathff1 = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                          (*Group)[0]->ParentFunc->getName().str() + ".ff1.log";
    raw_fd_ostream *FSff1 = getOutputStreamOfFile(Pathff1);
    *FSff1 << *(*Group)[0]->ParentFunc;
    delete FSff1;
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
    IRBuilder<> Builder(&*F.getEntryBlock().getFirstInsertionPt());
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
          if (!DT.dominates(I, UI)) {
            UI.set(Builder.CreateLoad(Addr));
          } else {
            errs() << "";
          }
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

    for (Instruction *OtherI : InstSet)
      Visited.insert(OtherI);

    AllocaInst *Addr = MemfyInst(InstSet);
    if (Addr)
      Allocas.push_back(Addr);
  }

  DominatorTree NDT(F);
  // PromoteMemToReg(Allocas, NDT, nullptr);
  if (Debug) {
    std::string Path1f = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                         (*Group)[0]->ParentFunc->getName().str() +
                         ".final0.log";
    raw_fd_ostream *FSf1 = getOutputStreamOfFile(Path1f);
    *FSf1 << *(*Group)[0]->ParentFunc;
    delete FSf1;
  }
  // F.dump();
  // postProcessFunction(F);

  if (Debug) {
    std::string Path0f = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                         (*Group)[0]->ParentFunc->getName().str() +
                         ".final.log";
    raw_fd_ostream *FSf = getOutputStreamOfFile(Path0f);
    *FSf << *(*Group)[0]->ParentFunc;
    delete FSf;
  }
  if (verifyFunction(F)) {
    verifyFunction(F);
    // errs() << "ERROR: Produced Broken Function: " << F.getName() << " !\n";
    // F.dump();
    // assert(false);
    return true;
  }

  return true;
}

static void CoalescingBB(BasicBlock *PrevBB, BasicBlock *SuccBB) {
  if (PrevBB == SuccBB->getSinglePredecessor()) {
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
  }
}

void RegionMergeInfo::coalescingBBsSplitBefore() {
  for (RepeatedItemInRegion *Rep : *CurrGroup) {
    // EndBB & FollowBB
    if (Rep->EndBB && Rep->FollowBB && Rep->SplitedEnd) {
      CoalescingBB(Rep->EndBB, Rep->FollowBB);
    }

    // PrevBB&StartBB
    if (Rep->PrevBB && Rep->StartBB && Rep->SplitedStart) {
      CoalescingBB(Rep->PrevBB, Rep->StartBB);
    }
  }
}

void FunctionFolding::reuseOldRegion(RARegionGroup *Group, RegionMergeInfo &RMI,
                                     BasicBlock *EntryBB) {
  for (auto Pair : RMI.InstrReplacedFrom) {
    Instruction *I = Pair.first;
    Value *FromV = Pair.second;
    Value *ToV = RMI.InstrReplacedTo[I];
    std::vector<unsigned> OperandNums = RMI.InstrReplacedOpNums[I];
    for (unsigned OpN : OperandNums) {
      I->setOperand(OpN, FromV);
    }
    // I->replaceUsesOfWith(ToV, FromV);
  }

  for (auto Pair : RMI.PNIncomingAdded) {
    PHINode *PN = Pair.first;
    BasicBlock *Pred = Pair.second;
    PN->removeIncomingValue(Pred);
  }
}

bool FunctionFolding::removeOldRegion(RARegionGroup *Group,
                                      RegionMergeInfo &RMI,
                                      BasicBlock *EntryBB) {
  LLVMContext &Context = F.getContext();
  const DataLayout &DL = F.getParent()->getDataLayout();

  if (Debug) {
    std::string PathRM0 = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                          (*Group)[0]->ParentFunc->getName().str() + ".rm0.log";
    raw_fd_ostream *FSRM0 = getOutputStreamOfFile(PathRM0);
    *FSRM0 << *(*Group)[0]->ParentFunc;
    delete FSRM0;
  }

  for (RepeatedItemInRegion *Candidate : *Group) {
    BasicBlock *Header = Candidate->StartBB;

    SetVector<BasicBlock *> Blocks(Candidate->MinRegion->Blocks.begin(),
                                   Candidate->MinRegion->Blocks.end());

    for (Value *Output : Candidate->Outputs) {
      std::vector<User *> Users(Output->user_begin(), Output->user_end());
      for (unsigned U = 0, E = Users.size(); U != E; ++U) {
        Instruction *Inst = cast<Instruction>(Users[U]);
        if (!Blocks.count(Inst->getParent())) {
          std::vector<unsigned> OperandNums;
          for (unsigned i = 0, E = Inst->getNumOperands(); i != E; ++i) {
            if (Inst->getOperand(i) == Output) {
              Inst->setOperand(i, RMI.VMap[Output]);
              OperandNums.push_back(i);
            }
          }
          // Inst->replaceUsesOfWith(Output, RMI.VMap[Output]);
          RMI.InstrReplacedFrom[Inst] = Output;
          RMI.InstrReplacedOpNums[Inst] = OperandNums;
          RMI.InstrReplacedTo[Inst] = RMI.VMap[Output];
        }
      }
    }

    // fix start
    std::vector<User *> Users(Header->user_begin(), Header->user_end());
    for (auto &U : Users)
      if (Instruction *Inst = dyn_cast<Instruction>(U))
        if (Inst->isTerminator() && Inst->getFunction() == &F &&
            !Blocks.count(Inst->getParent())) {
          std::vector<unsigned> OperandNums;
          for (unsigned i = 0, E = Inst->getNumOperands(); i != E; ++i) {
            if (Inst->getOperand(i) == Header) {
              Inst->setOperand(i, EntryBB);
              OperandNums.push_back(i);
            }
          }

          Inst->replaceUsesOfWith(Header, EntryBB);
          RMI.InstrReplacedFrom[Inst] = Header;
          RMI.InstrReplacedOpNums[Inst] = OperandNums;
          RMI.InstrReplacedTo[Inst] = EntryBB;
        }

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
    if (OutSucc != Candidate->FollowBB) {
      errs() << "";
    }

    RMI.BlocksToDelete.insert(Blocks.begin(), Blocks.end());
  }
  if (Debug) {
    std::string Pathff0 = "/home/swh/Projects/f3m/f3m/llvm-project/build-log/" +
                          (*Group)[0]->ParentFunc->getName().str() + ".ff0.log";
    raw_fd_ostream *FSff0 = getOutputStreamOfFile(Pathff0);
    *FSff0 << *(*Group)[0]->ParentFunc;
    delete FSff0;
  }

  // DeleteDeadBlocks(BlocksToDelete.getArrayRef());
  // postProcessFunction(F);

  return true;
}