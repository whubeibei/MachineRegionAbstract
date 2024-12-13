#include "llvm/CodeGen/MachineRegionAbstract.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/Twine.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/MachineRegionInfo.h"
#include "llvm/CodeGen/MachinePostDominators.h"
#include "llvm/CodeGen/MachineDominators.h"
#include "llvm/CodeGen/MIRPrinter.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Mangler.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/SuffixTree.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/SuffixTreeRepeatedInfos.h"
#include "llvm/Support/ScopedPrinter.h"
#include "assert.h"
#include <functional>
#include <tuple>
#include <vector>
#include <iostream>
#include <stack>



#define DEBUG_TYPE "machine-region-abstract"

using namespace llvm;
using namespace ore;
using namespace machine_region_abstract;


static cl::opt<bool> Debug("region-abstract-debug", cl::init(false), cl::Hidden,
                           cl::desc("Outputs debug information"));

static cl::opt<unsigned> RegionFindingMode(
    "region-finding-mode", cl::init(1), cl::Hidden,
    cl::desc("Modes that determines how to find min region, \nwhile 0 mode use "
             "llvm region, 1 mode (default) use a custom function by swh."));

static cl::opt<unsigned> CreateFuncOverHead(
    "create-function-overhead", cl::init(0), cl::Hidden,
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

// register rename
static cl::opt<bool> MRARegisterRename(
    "machine-region-abstract-register-rename", cl::init(false), cl::Hidden,
    cl::desc("Whether use register rename."));

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


namespace llvm


{

void MachineRegionAbstractManager::updateNonSplittableBlockSet(
    MachineRepeatedItemInRegion *MRegion) {
  for (MachineBasicBlock *MBB : MRegion->MinRegion->Blocks) {
    NonSplittableBlockSet.insert(MBB);
  }
}

void LzcRegion::updateEntry(MachineBasicBlock *NewEntry) {
  EntryBlock = NewEntry;
  if (Blocks.size() == 1) {
    ExitBlock = NewEntry;
    Blocks[0] = EntryBlock;
  } else {
    Blocks[1] = EntryBlock;
  }
}

void LzcRegion::updateExit(MachineBasicBlock *NewExit) {
  ExitBlock = NewExit;
  if (Blocks.size() == 1) {
    EntryBlock = NewExit;
    Blocks[0] = EntryBlock;
  } else {
    Blocks[0] = ExitBlock;
  }
}
    
LzcRegion::LzcRegion(MachineRegion *SourceRegion) {
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
    MachineBasicBlock *MBB = *It;
    assert(MBB && "Error: Null Basic Block in Region!");
    // Blocks.insert(BB);
    Blocks.push_back(MBB);
  }
}

LzcRegion::LzcRegion(std::vector<MachineBasicBlock *> &ContainedBBs) {
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

  for (MachineBasicBlock *PredBB : EntryBlock->predecessors()) {
    if (is_contained(ContainedBBs, PredBB)) {
      if (Debug)
        errs() << PredBB->getName() << "-->" << EntryBlock->getName() << "\n";
      NeedFullEntry = true;
      break;
    }
  }

  for (MachineBasicBlock *SuccBB : ExitBlock->successors()) {
    if (is_contained(ContainedBBs, SuccBB)) {
      if (Debug)
        errs() << SuccBB->getName() << "-->" << ExitBlock->getName() << "\n";
      NeedFullExit = true;
    } else {
      // assert(FollowBB == nullptr && "We can only deal with one FollowBB!");
      FollowBB.push_back(SuccBB);
    }
  }

  // 计算最小区域的指令序列是否相同
  RegionHashId = getHashId();
}

unsigned LzcRegion::getHashId() {
    uint64_t combinedHash = 0;

    for (auto *MBB : Blocks) {
        for (auto &MI : *MBB) {
            // 假设 getInstrHash 是你自己实现的用于计算单条指令的哈希值
            uint64_t instrHash = MachineInstrExpressionSimilarTrait::getHashValue(&MI);
            combinedHash ^= (instrHash + 0x9e3779b9 + (combinedHash << 6) + (combinedHash >> 2));
        }
    }

    return combinedHash;
}


bool MachineRepeatedItemInRegion::getMinRegionForIntraBBRS() {
  assert(RelatedMBlocks.size() == 1 && "Should have one related block!");
  MinRegion = new LzcRegion(RelatedMBlocks);
  EntryBlockSplitMode = 2;
  ExitBlockSplitMode = 2;
  return true;
}

// vector version
static LzcRegion *getMinRegionOfBlocks(MachineRegionInfo *MRI,
                                       std::vector<MachineBasicBlock *> &MBBList,
                                       unsigned Mode = 1) {
  if (Mode == 1) {
    // TODO:
    MachineBasicBlock *StartMBB = MBBList[0];
    MachineBasicBlock *EndMBB = MBBList[MBBList.size() - 1];
    MachineFunction *ParentFunc = StartMBB->getParent();
    MachineDominatorTree DT(*ParentFunc);
    MachinePostDominatorTree PDT(*ParentFunc);

    // try to find Region Entry

    // std::vector<BasicBlock *> RegionEntryCandidates = {StartBB};
    SetVector<MachineBasicBlock *> RegionEntryCandidates;
    RegionEntryCandidates.insert(StartMBB);

    MachineBasicBlock *CurrentBB;
    auto DomAll = [&] {
      for (MachineBasicBlock *BB : MBBList) {
        if (!DT.dominates(CurrentBB, BB))
          return false;
      }
      return true;
    };

    bool FindEntrySucc = false;
    for (int I = 0; I < RegionEntryCandidates.size() && I < 2 * MBBList.size();
         I++) {
      CurrentBB = RegionEntryCandidates[I];
      if (DomAll()) {
        FindEntrySucc = true;
        break;
      }
      for (auto PredBB = CurrentBB->pred_begin(); PredBB != CurrentBB->pred_end();
           PredBB++) {
        // RegionEntryCandidates.push_back(*PredBB);
        RegionEntryCandidates.insert(*PredBB);
      }
    }
    if (!FindEntrySucc) {
      return nullptr;
    }
    // find the Entry
    MachineBasicBlock *RegionEntry = CurrentBB;
    // RegionEntry->dump();
    if (Debug)
      errs() << "\tFind Entry Block: " << RegionEntry->getName() << "\n";

    // try to find Region End
    // std::vector<BasicBlock *> RegionExitCandidates = {EndBB};
    SetVector<MachineBasicBlock *> RegionExitCandidates;
    RegionExitCandidates.insert(EndMBB);

    auto PostDomAll = [&] {
      if (!PDT.dominates(CurrentBB, RegionEntry)) {
        // CurrentBB->dump();
        return false;
      }

      if (!DT.dominates(RegionEntry, CurrentBB)) {
        // CurrentBB->dump();
        return false;
      }

      for (MachineBasicBlock *BB : MBBList) {
        if (!PDT.dominates(CurrentBB, BB))
          return false;
      }

      return true;
    };

    bool FindExitSucc = false;

    for (int J = 0; J < RegionExitCandidates.size() && J < 2 * MBBList.size();
         J++) {
      CurrentBB = RegionExitCandidates[J];
      if (PostDomAll()) {
        FindExitSucc = true;
        break;
      }
      for (auto SuccBB = CurrentBB->succ_begin(); SuccBB != CurrentBB->succ_end();
           SuccBB++) {
        // RegionExitCandidates.push_back(*SuccBB);
        RegionExitCandidates.insert(*SuccBB);
      }
    }
    if (!FindExitSucc) {
      return nullptr;
    }

    // find Region End
    MachineBasicBlock *RegionExit = CurrentBB;
    // RegionExit->dump();
    if (Debug)
      errs() << "\tFind Exit Block: " << RegionExit->getName() << "\n";

    // try to find the real Region.
    auto CheckDomi = [&](MachineBasicBlock *BB) {
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

    std::vector<MachineBasicBlock *> RegionMBBs = {RegionExit, RegionEntry};
    int Tmp = std::distance(RegionExit->pred_begin(), RegionExit->pred_end());
    std::vector<int> PredNumOfBBs = {Tmp, 0};
    for (int Index = 1; Index < RegionMBBs.size(); Index++) {
      CurrentBB = RegionMBBs[Index];
      for (auto SuccBB = CurrentBB->succ_begin(); SuccBB != CurrentBB->succ_end();
           SuccBB++) {
        if (CheckDomi(*SuccBB)) {
          auto It = std::find(RegionMBBs.begin(), RegionMBBs.end(), *SuccBB);
          if (It == RegionMBBs.end()) {
            RegionMBBs.push_back(*SuccBB);
            PredNumOfBBs.push_back(
                std::distance((*SuccBB)->pred_begin(), (*SuccBB)->pred_end()) - 1);
          } else {
            long D = std::distance(RegionMBBs.begin(), It);
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

    LzcRegion *MyRegion = new LzcRegion(RegionMBBs);
    if (MyRegion->NeedFullExit && MyRegion->FollowBB.size() > 1) {
      return nullptr;
    }

    return MyRegion;
  }

  // Mode == 0
  llvm::MachineRegion *MinRegion = nullptr;
  for (llvm::MachineBasicBlock *BB : MBBList) {
    llvm::MachineRegion *Region = MRI->getRegionFor(BB);
    if (!MinRegion)
      MinRegion = Region;
    else
      //找到两区域最小的region
      MinRegion = MRI->getCommonRegion(Region, MinRegion);
  }
  return new LzcRegion(MinRegion);
}


bool MachineRepeatedItemInRegion::getMinRegion(MachineRegionInfo *MRI) {

  MinRegion = getMinRegionOfBlocks(MRI, RelatedMBlocks, RegionFindingMode);
  if (MinRegion == nullptr) {
    if (Debug) {
      errs() << "Error: Can not get MinRegion for this candidate!\n";
    }
    return false;
  }

  if (MinRegion->NeedFullEntry) {
    EntryBlockSplitMode = 1;
  } else if (MinRegion->EntryBlock == RelatedMBlocks[0]) {
    EntryBlockSplitMode = 2;
  }

  if (MinRegion->NeedFullExit) {
    ExitBlockSplitMode = 1;
  } else if (MinRegion->ExitBlock == RelatedMBlocks.back()) {
    ExitBlockSplitMode = 2;
  }

  return true;
}

#pragma region getCandidateList
bool MachineRegionAbstractManager::getCandidateList(
    std::vector<RepeatedInfos::RepeatedSubstringByS *> &RSList,
    std::vector<MachineBasicBlock::iterator> &InstrList, MachineRegionAbstract &MRA) {

    //从RSList中找到每个重复的Function、blocks，找到region，判断region之间是否有重叠，有重叠就合并成一个
    for (RepeatedInfos::RepeatedSubstringByS *RS : RSList) {
    //将所有的重复所在的Region、Function取出到局部变量里
    MRARegionGroup *RegionGroup = new MRARegionGroup();
    bool IntraBlock = false;

    MRARegionGroup *FailedGroup = new MRARegionGroup();
    std::vector<MRARegionGroup *> FailedGroups;

    if (Debug)
      errs() << "Region Group info {\n";

    for (unsigned int StartIdx : RS->StartIndices) {
      // ReleatedBBs会被释放，但是因为是深拷贝，所以并不影响
      DenseSet<MachineBasicBlock *> RelatedMBBs;
      MachineRepeatedItemInRegion *Entry = new MachineRepeatedItemInRegion();

      for (unsigned InstrIt = StartIdx; InstrIt < StartIdx + RS->Length;
           InstrIt++) {
        MachineBasicBlock::iterator MII = InstrList[InstrIt];
        MachineInstr * MI = &(*MII);
        // 取消InstrData的判断
        // assert(ID->IDType >= 0 &&
        //        "Error: Instruction Data Type should be positive number!");
        Entry->RepeatedInstrDatas.push_back(MI);
        Entry->RepeatedInstSet.insert(MI);
        MachineBasicBlock *MBB = MI->getParent();
        if (!RelatedMBBs.contains(MBB)) {
          RelatedMBBs.insert(MBB);
          Entry->RelatedMBlocks.push_back(MBB);
        }
      } // end for 3

      if (RelatedMBBs.size() < 2) {
        if (RAAbstractInBlockCandidate.getValue()) {
          Entry->ParentFunc = (*RelatedMBBs.begin())->getParent();
          if (Entry->getMinRegionForIntraBBRS()) {
            Entry->RelatedMBBSet = RelatedMBBs;
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
        Entry->ParentFunc = (*RelatedMBBs.begin())->getParent();
        Entry->RelatedMBBSet = RelatedMBBs;
        // RegionInfo *RI =
        //     RegionFindingMode
        //         ? nullptr
        //         : &RA.getAnalysis<RegionInfoPass>(*Entry->ParentFunc)
        //                .getRegionInfo();

        //暂时不使用MachineRegionInfoPass
        MachineRegionInfo *MRI = nullptr;

        if (Entry->getMinRegion(MRI)) {
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

    if (Debug) {
      errs() << RegionGroup->size() << " RS found region.\n";
      errs() << FailedGroup->size() << " RS cannot find region.\n";
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

    if (FailedGroup->size() >= 2) {
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
bool MachineRegionAbstractManager::getAndMergeCandidateList(
    std::vector<RepeatedInfos::RepeatedSubstringByS *> &RSList,
    std::vector<MachineBasicBlock::iterator > &InstrList, MachineRegionAbstract &MRA) {


  for (RepeatedInfos::RepeatedSubstringByS *RS : RSList) {
    MRARegionGroup *MachineRegionGroup = new MRARegionGroup();
    bool IntraBlock = false;
    MRARegionGroup *FailedGroup = new MRARegionGroup();

    for (unsigned int StartIdx : RS->StartIndices) {
      DenseSet<MachineBasicBlock *> RelatedMBBs;
      MachineRepeatedItemInRegion *Entry = new MachineRepeatedItemInRegion();

      for (unsigned InstrIt = StartIdx; InstrIt < StartIdx + RS->Length;
           InstrIt++) {
        MachineBasicBlock::iterator MII = InstrList[InstrIt];
        MachineInstr * MI = &(*MII);
        // 判断指令是否合法，排除分隔符指令
        // assert(ID->IDType >= 0 &&
        //        "Error: Instruction Data Type should be positive number!");
        Entry->RepeatedInstrDatas.push_back(MI);
        Entry->RepeatedInstSet.insert(MI);
        MachineBasicBlock *MBB = MI->getParent();
        if (!RelatedMBBs.contains(MBB)) {
          RelatedMBBs.insert(MBB);
          Entry->RelatedMBlocks.push_back(MBB);
        }
      } // end for 3

      if (RelatedMBBs.size() < 2) {
        if (RAAbstractInBlockCandidate.getValue()) {
          Entry->ParentFunc = (*RelatedMBBs.begin())->getParent();
          if (Entry->getMinRegionForIntraBBRS()) {
            Entry->RelatedMBBSet = RelatedMBBs;
            MachineRegionGroup->push_back(Entry);
            IntraBlock = true;
          } else {
            delete Entry;
          }
        } else {
          delete Entry;
        }
      } else {

        //如果不是块内重复，生成对应的项，并加入
        Entry->ParentFunc = (*RelatedMBBs.begin())->getParent();
        Entry->RelatedMBBSet = RelatedMBBs;
        // MachineRegionInfo *MRI =
        //     RegionFindingMode
        //         ? nullptr
        //         : &MRA.getAnalysis<MachineRegionInfoPass>(*Entry->ParentFunc)
        //                .getRegionInfo();

        //暂时不使用MachineRegionInfoPass
        MachineRegionInfo *MRI = nullptr;

        if (Entry->getMinRegion(MRI)) {
          // ReleatedBBs会被释放，但是因为是深拷贝，所以并不影响

          // Entry->ReleatedBlocks.insert(Entry->ReleatedBlocks.end(),
          //                              ReleatedBBs.begin(),
          //                              ReleatedBBs.end());
          MachineRegionGroup->push_back(Entry);
        } else {
          FailedGroup->push_back(Entry);
        }
      }
    } // end for 2

    if (MachineRegionGroup->size() < 2)
      delete MachineRegionGroup;
    else {
      if (IntraBlock)
        IntraBlockCandidateList.push_back(MachineRegionGroup);
      else
        CandidateList.push_back(MachineRegionGroup);
    }

    if (FailedGroup->size() >= 2 && RAAbstractInBlockCandidate.getValue()) {
      if (Debug)
        errs() << "Retry to find region for failed rs.\n";

      // FailedGroup拆分成多个IntraBBGroup

      //按基本块拆分
      int Left = 0;
      MachineBasicBlock *LeftBB =
          FailedGroup->front()->RepeatedInstSet[0]->getParent();

      for (int Right = 1; Right < RS->Length; Right++) {

        //找到基本块分界线
        if (FailedGroup->front()->RepeatedInstSet[Right]->getParent() !=
            LeftBB) {
          //创建新的RegionGroup
          MRARegionGroup *MRG = new MRARegionGroup();

          for (int a = 0; a < FailedGroup->size(); a++) {
            MachineRepeatedItemInRegion *OldEntry = (*FailedGroup)[a];
            //根据旧的Entry创建新的Entry
            MachineRepeatedItemInRegion *NewEntry = new MachineRepeatedItemInRegion();
            for (int l = Left; l < Right; l++) {
              NewEntry->RepeatedInstrDatas.push_back(
                  OldEntry->RepeatedInstrDatas[l]);
              NewEntry->RepeatedInstSet.insert(OldEntry->RepeatedInstSet[l]);
            }
            MachineBasicBlock *TmpBB = OldEntry->RepeatedInstSet[Left]->getParent();
            NewEntry->RelatedMBBSet.insert(TmpBB);
            NewEntry->RelatedMBlocks.push_back(TmpBB);

            NewEntry->ParentFunc = TmpBB->getParent();
            if (NewEntry->getMinRegionForIntraBBRS()) {
              //创建新的Entry成功，插入RegionGroup
              MRG->push_back(NewEntry);
            } else {
              //创建新的Entry失败
              delete NewEntry;
            }
          }

          IntraBlockCandidateList.push_back(MRG);

          LeftBB = FailedGroup->front()->RepeatedInstSet[Right]->getParent();
          Left = Right;
        }
      }
    }
  }

  // int CFO = CreateFuncOverHead.getValue();
  auto BenefitOf = [&](MRARegionGroup *Group0) -> int {
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

  llvm::stable_sort(CandidateList, [&](MRARegionGroup *LHS, MRARegionGroup *RHS) {
    return BenefitOf(LHS) > BenefitOf(RHS);
  });

  llvm::stable_sort(IntraBlockCandidateList,
                    [&](MRARegionGroup *LHS, MRARegionGroup *RHS) {
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

//lzc修改了相应的更新操作？
bool MachineRepeatedItemInRegion::updatePhiBlock(MachineBasicBlock *NewMBB,
                                          MachineBasicBlock *OldMBB) {
  bool NeedSplitPHI = false;
  for (MachineInstr &MI : *NewMBB) {
    if (!MI.isPHI()) {
      return true;
    }
    // 获取 PHI 节点
    MachineInstr *PHINode = &MI;

    for (unsigned i = 1, e = PHINode->getNumOperands(); i < e; i += 2) {
      MachineBasicBlock *SourceMBB = PHINode->getOperand(i + 1).getMBB();
      if (RelatedMBBSet.contains(SourceMBB)) {
        MachineInstr *TermMI = &*(SourceMBB->getFirstTerminator());
        for (unsigned j = 0, je = TermMI->getNumOperands(); j < je; ++j) {
          MachineOperand &MO = TermMI->getOperand(j);
          if (MO.isMBB() && MO.getMBB() == OldMBB) {
            MO.setMBB(NewMBB);
          }
        }
      } else {
        if (NeedSplitPHI)
          return false;
        assert(!NeedSplitPHI && "TODO: Need to split PHI node if there is more than one predecessor in PHI node!");
        PHINode->getOperand(i + 1).setMBB(OldMBB);
        NeedSplitPHI = true;
      }
    }
  }

  return true;
}

//lzc
//此处逻辑应该需要更改，MIR中一个块可能存在多条终结指令，和IR中不同
bool MachineRepeatedItemInRegion::splitRegion(
    DenseSet<MachineBasicBlock *> &NonSplittableBlockSet,
    std::set<MachineFunction *> &AffectedFuncs) {
  assert(!RegionSplit && "Region already split!");
  // need to update start region entry

  if (RepeatedInstrDatas.size() < 2)
  {
    return false;
  }
  

  MachineInstr *StartInst, *EndInst;
  switch (EntryBlockSplitMode) {
  case 1:
    StartInst = &*MinRegion->EntryBlock->begin();
    // TODO:需要做特殊的处理
    return false;
    break;
  case 2:
    StartInst = RepeatedInstrDatas[0];
    break;
  default:
  case 0:
    // 获取终止指令
    auto FirstTerminator = MinRegion->EntryBlock->getFirstTerminator();

    // 检查是否找到有效的终止指令
    if (FirstTerminator == MinRegion->EntryBlock->end()) {
        llvm::errs() << "Error: No terminator in EntryBlock\n";
        return false;
    }
    StartInst = &*FirstTerminator;
    break;
  }
  if (StartInst) {
    if (EntryBlockSplitMode == 2) {
      // rs should not start with phi, so we remove it from rs
      //由于不存在直接从phi结点不经过br，跳到新的基本块的情况，所以无需更新Blocks
      while (StartInst->getOpcode() == TargetOpcode::PHI) { //fixme，？？
        if (RepeatedInstrDatas.empty())
          return false;
        RepeatedInstrDatas.erase(RepeatedInstrDatas.begin());
        RepeatedInstSet.remove(StartInst);
        StartInst = RepeatedInstrDatas[0];
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
    // 此时进行切分，目的是只保留起始指令开始的基本块，起始指令之前的块抛掉 
    // lzc：取消对新machinbasicblock的命名，只做分割操作
    // 获取 StartInst 前一条指令
    MachineBasicBlock::iterator It = StartInst->getIterator();
    // if (It != PrevBB->begin()) {//fixme,暂时防止割空，后期可完善切割逻辑
    //   --It; // 获取前一条指令进行切割
    //   // llvm::dbgs() << "StartInst is the first instruction in the block.\n";
    //   // return 1;
    // }
    MachineInstr *SplitInst = &*It;
    // 使用 splitAt 函数分割基本块，确保分界指令被包含在新创建的块中 
    // StartBB = PrevBB->splitAt(*SplitInst);
    StartBB = splitMBB(PrevBB,SplitInst);
    SplitedStart = true;
    AffectedFuncs.insert(PrevBB->getParent());
    MinRegion->updateEntry(StartBB);
    if (EntryBlockSplitMode == 1) {
      if (!updatePhiBlock(StartBB, PrevBB))
        return false;
    } else if (EntryBlockSplitMode == 2) {
      RelatedMBlocks[0] = StartBB;
      RelatedMBBSet.erase(PrevBB); //完成了切割后的更新
      RelatedMBBSet.insert(StartBB);
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
    EndInst = RepeatedInstrDatas[RepeatedInstrDatas.size() - 1];
    if (EndInst->isTerminator()) {
      // //如果是终结符，则特殊处理
      // if (EndInst->getNumSuccessors() == 1) {
      //   EndBB = EndInst->getParent();
      //   //FollowBB = EndInst->getFirstSuccessor();//lzc?,该followBB未使用
      //   EndInst = nullptr;
      //   //此时不需要分割
      // } else {
      //   //如果有多个succ，则我们认为EndInst不能被abstract,直接从EndInst这里分割
      //   RepeatedInstrDatas.pop_back();
      //   RepeatedInstSet.remove(EndInst);
      // }
      
      //lzc，修改，对endinst是终结指令，不予提取
//      if (EndInst->getNumSuccessors() == 1) {
        RepeatedInstrDatas.pop_back();
        RepeatedInstSet.remove(EndInst);
//      }
    } else {
      //否则需要向后移动一位用来做截断
      EndInst = EndInst->getNextNode();
    }
    break;
  default:
  case 0:
    EndInst = &*MinRegion->ExitBlock->getFirstNonPHI();
    break;
  }
  if (EndInst) {
    if (ExitBlockSplitMode == 2) {
      // rs should not follow with phi, so we add it to rs
      //由于不存在直接从phi结点不经过br，跳到新的基本块的情况，所以无需更新Blocks
      while (EndInst->getOpcode() == TargetOpcode::PHI) {
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
    // 获取 EndInst 前一条指令
    MachineBasicBlock::iterator It = EndInst->getIterator();
    if (It != EndBB->begin()) {//fixme，防止割空
      --It; // 获取前一条指令
      // llvm::dbgs() << "StartInst is the first instruction in the block.\n";
      // return 1;
    }
    MachineInstr *SplitInst = &*It;
    FollowBB = EndBB->splitAt(*SplitInst);
    // FollowBB = splitMBB(EndBB,SplitInst);
    SplitedEnd = true;
    AffectedFuncs.insert(EndBB->getParent());

    MinRegion->updateExit(EndBB);
    if (ExitBlockSplitMode == 2) {
      //此时，这条终结指令应该不在Region之中，但是为了完整性，这里放入Region中
      //MachineInstr *MI = &(*EndBB->getFirstTerminator());
      MachineInstr *MI;
      MachineBasicBlock::iterator TermIt = EndBB->getFirstTerminator();
      if (TermIt != EndBB->end()) {
        // 迭代器有效，可以安全解引用
        MI = &(*TermIt);
        // 对 MI 进行处理
        //lzc?      
        RepeatedInstrDatas.push_back(MI);
        RepeatedInstSet.insert(MI);
      } else {
        // 没有找到终结符指令，处理这种情况
        MI = nullptr;  // 或者执行其他适当的处理逻辑
      }
    }
  }

  // update Info
  RegionSplit = true;
  return true;
}


//lzc use-define逻辑需要更改
/**
 * @brief Try to analysis regions of candidate, such as that if there are
 * regions in same region.
 * @param Group vector of regions (or repeated items)
 */
void MachineRegionAbstractManager::analysisRegionGroup(MRARegionGroup *Group,
                                                MachineRegionMergeInfo &MRMI) {
  if (Group->size() < 2) {
    return;
  }

  if (Group->front()->RepeatedInstrDatas.size() < 2)
  {
    return;
  }
  
  DenseMap<MachineFunction *, MRARegionGroup *> *FuncItemMap =
      new DenseMap<MachineFunction *, MRARegionGroup *>();

  MRARegionGroup MergeableRegions;

  for (MachineRepeatedItemInRegion *RegionCandidate : *Group) {

    if (!RegionCandidate->splitRegion(NonSplittableBlockSet, AffectedFuncs)) {
      continue;
    }
    // update NonSplittableBlockSet
    if (RegionCandidate->EntryBlockSplitMode != 2) {
      MRMI.MisMatchEntryCount++;
    }
    if (RegionCandidate->ExitBlockSplitMode != 2) {
      MRMI.MisMatchExitCount++;
    }
    updateNonSplittableBlockSet(RegionCandidate);
    MergeableRegions.push_back(RegionCandidate);

    // if in same function
    if (FuncItemMap->find(RegionCandidate->ParentFunc) == FuncItemMap->end()) {
      std::vector<MachineRepeatedItemInRegion *> *Items =
          new std::vector<MachineRepeatedItemInRegion *>();
      Items->push_back(RegionCandidate);
      (*FuncItemMap)[RegionCandidate->ParentFunc] = Items;
    } else {
      (*FuncItemMap)[RegionCandidate->ParentFunc]->push_back(RegionCandidate);
    }

  }

  // update group
  Group->swap(MergeableRegions);
  if (Group->size() < 2)
    return;

  // 计算group中每个元素的id，判断最小区域的指令序列是否相同
  for (MachineRepeatedItemInRegion *Candidate : *Group) {
    LzcRegion *MinRegion = Candidate->MinRegion;
    MinRegion->updateHashId();
  }

  for (auto Pair : *FuncItemMap) {
    if (Pair.second->size() > 1) {
      if (Debug)
        errs() << Pair.second->size() << " Items In Same Function.\n";
      MRMI.HasInFuncRepeated = true;
    }
  }

  if (MRMI.HasInFuncRepeated == true) {
    MRMI.FuncItemMap = FuncItemMap;
  } else {
    delete FuncItemMap;
  }

  for (MachineBasicBlock *MBB : (*Group)[0]->RelatedMBlocks) {
    if (MBB == (*Group)[0]->MinRegion->ExitBlock)
      continue;
    for (MachineBasicBlock *Succ : MBB->successors()) {
      if (!(*Group)[0]->RelatedMBBSet.contains(Succ)) {
        MRMI.MatchBrToMisMatch++;
      }
    }
  }

  //获取整个Group的Input和Output
  // after analysis inputs and outputs, try to get the paramsList
  //getGroupParamsList(MRMI);
}

void MachineRegionAbstractManager:: preVerifyReplaceMBBControlFlow() {
  for (MachineBasicBlock* replaceMBB : ReplacedBlockSet) {
    const TargetSubtargetInfo &STI = replaceMBB->getParent()->getSubtarget();
    const TargetInstrInfo &TII = *STI.getInstrInfo();
    // 判断后继块是否紧邻替换块，保证fallthrough关系正常
    auto NextIt = std::next(MachineFunction::iterator(replaceMBB));
    auto OutSucc = *replaceMBB->succ_begin();
    if (&*NextIt != OutSucc) {
      // 如果不紧邻，在 replaceMBB 中插入跳转指令到 Succ
      TII.insertUnconditionalBranch(*replaceMBB,OutSucc,DebugLoc());
    }
  }
}

bool MachineRegionAbstractManager::eraseSourceRegion() {
      // 删除整个区域的所有基本块
      for (MachineBasicBlock *MBB : BlocksToErase) {
                MachineFunction *MF = MBB->getParent();
                MF->dump();
        // 删除 MBB 前，先处理它的所有后继或前驱块
        // 清理控制流关系
        MBB->clear();  // 清理前驱后继关系
        MBB->eraseFromParent();
        // //每删一个块，检查一次
        // MachineFunction *MF = MBB->getParent();
        // if (!MF->verify())
        // {
        //   return false;
        // }
      }
      // 在检查之前，先预处理一下replaceMBB的控制流
      preVerifyReplaceMBBControlFlow();
      for (MachineBasicBlock *MBB : BlocksToErase) {
        //每删一个块，检查一次
        MachineFunction *MF = MBB->getParent();
              MF->RenumberBlocks(); // lzc,删除块后重新分配序号？
        if (!MF->verify())
        {
          return false;
        }
      }
    return true;
}

bool MachineRegionAbstractManager::replaceCall(MRARegionGroup *Group,
                                         MachineRegionMergeInfo &MRMI) {
  bool RegionAbstractedSomething = false;
  MachineFunction *MF = MRMI.MergedFunc;
  const TargetSubtargetInfo &STI = MF->getSubtarget();
  const TargetInstrInfo &TII = *STI.getInstrInfo();

      // 处理整个区域的寄存器定义和使用情况
      SmallSet<Register, 2> UseRegs, DefRegs;//避免重复添加
      MRARegionCandidate *example = Group->front();
      MachineFunction *exampleMF = example->MinRegion->Blocks.front()->getParent();
      const MachineRegisterInfo &MRI = exampleMF->getRegInfo();
      const TargetRegisterInfo &TRI = *MRI.getTargetRegisterInfo();
      //使用迭代更新来分析区域的livein和liveout
      // 创建Def和LiveUse集合
      DenseMap<MachineBasicBlock *, BitVector> Def;
      DenseMap<MachineBasicBlock *, BitVector> LiveUse;
      DenseMap<MachineBasicBlock *, BitVector> LiveIn;
      DenseMap<MachineBasicBlock *, BitVector> LiveOut;

      // 初始化每个基本块的Def和LiveUse集合
      for (auto &MBB : *MF) {
          BitVector DefBV(TRI.getNumRegs());
          BitVector LiveUseBV(TRI.getNumRegs());
          
          // 反向遍历每个基本块的指令，更新Def和LiveUse
          MachineBasicBlock::iterator StartIt = MBB.front();
          MachineBasicBlock::iterator EndIt = MBB.back();

          // 在每个块中从下往上遍历
          for (MachineBasicBlock::reverse_iterator
                  Iter = EndIt.getReverse(),
                  Last = std::next(StartIt.getReverse());
              Iter != Last; Iter++) {
            MachineInstr *MI = &*Iter;
            for (MachineOperand &MOP : MI->operands()) {
              // Skip over anything that isn't a register.
              if (!MOP.isReg())
                continue;

              if (MOP.isDef()) {
                // Introduce DefRegs set to skip the redundant register.
                // DefRegs.insert(MOP.getReg());
                DefBV.set(MOP.getReg());  // 记录定义
                if (!MOP.isDead() && DefBV.test(MOP.getReg()))
                  // Since the regiester is modeled as defined,
                  // it is not necessary to be put in use register set.
                  // UseRegs.erase(MOP.getReg());
                  LiveUseBV.reset(MOP.getReg());
              } else if (!MOP.isUndef()) {
                // Any register which is not undefined should
                // be put in the use register set.
                // UseRegs.insert(MOP.getReg());
                LiveUseBV.set(MOP.getReg());  // 记录使用
              }
            }
            if (MI->isCandidateForCallSiteEntry())
              MI->getMF()->eraseCallSiteInfo(MI);
          }
          
          Def[&MBB] = DefBV;
          LiveUse[&MBB] = LiveUseBV;
          LiveIn[&MBB].resize(TRI.getNumRegs());
          LiveOut[&MBB].resize(TRI.getNumRegs());
      }

      bool changed = true;
      
      // 迭代计算LiveIn和LiveOut集合
      while (changed) {
          changed = false;

          // 反向遍历基本块
          for (auto MBBIt = MF->rbegin(); MBBIt != MF->rend(); ++MBBIt) {
              MachineBasicBlock &MBB = *MBBIt;
              BitVector OldLiveIn = LiveIn[&MBB];
              
              // 更新LiveOut集合：从所有后继中取LiveIn的并集
              BitVector LiveOutBV(TRI.getNumRegs());
              for (MachineBasicBlock *Succ : MBB.successors()) {
                  LiveOutBV |= LiveIn[Succ];
              }
              LiveOut[&MBB] = LiveOutBV;

              // 更新LiveIn集合
              BitVector NewLiveIn = LiveUse[&MBB];
              llvm::BitVector TempDef = Def[&MBB];  // 复制 Def
              TempDef.flip();                       // 翻转 TempDef
              llvm::BitVector TempLiveOut = LiveOut[&MBB]; // 复制 LiveOut
              TempLiveOut &= TempDef;// 执行 LiveOut & ~Def 的操作
              NewLiveIn |= TempLiveOut;
              // NewLiveIn |= (LiveOut[&MBB] & ~Def[&MBB]); // LiveUse ∪ (LiveOut - Def)
              
              if (NewLiveIn != OldLiveIn) {
                  changed = true;
                  LiveIn[&MBB] = NewLiveIn;
              }
          }
      }

      // 处理第一个基本块
      if (MachineBasicBlock *FirstMBB = &MF->front()) {
          const BitVector &LiveInBV = LiveIn[FirstMBB];
          for (unsigned Reg = 0; Reg < TRI.getNumRegs(); ++Reg) {
              if (LiveInBV.test(Reg)) {
                  UseRegs.insert(Reg);
              }
          }
      }

      // 处理所有基本块的Def集合
      for (auto &MBB : *MF) {
          const BitVector &DefBV = Def[&MBB];
          for (unsigned Reg = 0; Reg < TRI.getNumRegs(); ++Reg) {
              if (DefBV.test(Reg)) {
                  DefRegs.insert(Reg);
              }
          }
      }

    // Replace occurrences of the sequence with calls to the new function.
    for (MRARegionCandidate *C : *Group) {
      // MachineBasicBlock &MBB = *(C->RelatedMBlocks.front());
      // MachineBasicBlock::iterator StartIt = MBB.front();
      // MachineBasicBlock::iterator EndIt = MBB.back();
      SetVector<MachineBasicBlock *> MRABlocks(C->MinRegion->Blocks.begin(),
                                   C->MinRegion->Blocks.end());
      // std::vector<llvm::MachineBasicBlock *> MRABlocks = C->MinRegion->Blocks;
      MachineBasicBlock *FirstMBB;
      MachineBasicBlock *LastMBB = MRABlocks[0];
      if (MRABlocks.size() < 2)
        FirstMBB = MRABlocks[0];
      else FirstMBB = MRABlocks[1];
      MachineFunction *OriginalMF = LastMBB->getParent();
      // 在原区域之前插入一个新块，用来存放调用和跳转指令，便于后续进行替换
      MachineBasicBlock *replaceMBB = OriginalMF->CreateMachineBasicBlock();
      OriginalMF->insert(FirstMBB->getIterator(), replaceMBB); // 插入到原区域初始块之前

      // MachineBasicBlock *InsertMBB = *FirstMBB->pred_begin();
      MachineBasicBlock::iterator InsertIt = replaceMBB->end();
      //InsertIt--;
      // Insert the call.
      auto CallInst = TII.insertRACall(M, *replaceMBB, InsertIt, *MF);  

      // 处理原区域替换后的控制流关系
      std::vector<MachineBasicBlock*> predecessors;// 因为要做修改删除，所以先添加到另一个容器中
      for (MachineBasicBlock *predMBB : FirstMBB->predecessors()) {
          predecessors.push_back(predMBB);
      }

      for (MachineBasicBlock *predMBB : predecessors) {
          assert((predMBB && MRABlocks.count(predMBB) == 0) && "predMBB should not be null!");
          //对于A->B，跳转情况，需要修改跳转指令的目标块
          // 采用shw regionabstract方法，遍历每一条指令，将目标块修改
          for (MachineInstr &MI : *predMBB) {
              // 遍历每条指令的每个操作数
              for (unsigned i = 0; i < MI.getNumOperands(); ++i) {
                  MachineOperand &MO = MI.getOperand(i);
                  // 检查是否为基本块操作数
                  if (MO.isMBB() && MO.getMBB() == FirstMBB) {
                      // 替换为 replaceMBB
                      MO.setMBB(replaceMBB);                      
                      // 打印日志确认替换成功
                      MI.dump();
                  }
              }
          }
          
          //对于fallthrough情况，无需额外处理
          predMBB->removeSuccessor(FirstMBB);
          predMBB->addSuccessor(replaceMBB);
      }
      // MachineBasicBlock *predMBB = *FirstMBB->pred_begin();
      

      MachineBasicBlock *OutSucc = nullptr;
      for (MachineBasicBlock *Succ : LastMBB->successors()) {
        if (MRABlocks.contains(Succ))
          continue;
        assert(!OutSucc && "Should have only one out successor!");
        OutSucc = Succ;
      }
      assert((OutSucc) && "Out successor of exit machinebasicblock should not be null!");
      LastMBB->removeSuccessor(OutSucc);
      // lzc尝试利用fallthrough，不增加跳转指令
      // // 插入跳转指令，跳到 OutSucc
      // // const TargetInstrInfo *TII = MF.getSubtarget().getInstrInfo();
      // DebugLoc DL;  // 如果有调试信息，你可以在这里传入调试位置信息
      // // 根据目标架构插入合适的跳转指令，以下是一个通用示例
      // TII.insertBranch(*replaceMBB, OutSucc, nullptr, {}, DL);
      // 添加后继关系
      replaceMBB->addSuccessor(OutSucc);
      // 广度优先,对区域自下而上分析，确定区域的livein，liveout(def,并不一定后续被使用)   
      // 队列，用于按广度优先顺序处理块
      std::queue<MachineBasicBlock*> WorkQueue;
      // 集合，用于防止重复处理块
      SmallSet<MachineBasicBlock*, 16> Visited;


      // LivePhysRegs LiveRegs;
      // LiveRegs.init(TRI);  // TRI 是 TargetRegisterInfo
      // LiveRegs.addLiveIns(*replaceMBB);

      // // 将区域的出口块加入队列
      // WorkQueue.push(LastMBB);
      // Visited.insert(LastMBB);

      // while (!WorkQueue.empty()) {
      //     MachineBasicBlock *SourceBB = WorkQueue.front();  // 获取队列中的第一个元素
      //     WorkQueue.pop();  // 然后移除该元素
      //     MachineBasicBlock::iterator StartIt = SourceBB->front();
      //     MachineBasicBlock::iterator EndIt = SourceBB->back();

      //     // 在每个块中从下往上遍历
      //     for (MachineBasicBlock::reverse_iterator
      //             Iter = EndIt.getReverse(),
      //             Last = std::next(StartIt.getReverse());
      //         Iter != Last; Iter++) {
      //       MachineInstr *MI = &*Iter;
      //       for (MachineOperand &MOP : MI->operands()) {
      //         // Skip over anything that isn't a register.
      //         if (!MOP.isReg())
      //           continue;

      //         if (MOP.isDef()) {
      //           // Introduce DefRegs set to skip the redundant register.
      //           DefRegs.insert(MOP.getReg());
      //           if (!MOP.isDead() && UseRegs.count(MOP.getReg()))
      //             // Since the regiester is modeled as defined,
      //             // it is not necessary to be put in use register set.
      //             UseRegs.erase(MOP.getReg());
      //         } else if (!MOP.isUndef()) {
      //           // Any register which is not undefined should
      //           // be put in the use register set.
      //           UseRegs.insert(MOP.getReg());
      //         }
      //       }
      //       if (MI->isCandidateForCallSiteEntry())
      //         MI->getMF()->eraseCallSiteInfo(MI);
      //     }

      //     // 如果当前块是入口块，结束
      //     if (SourceBB == FirstMBB)
      //         continue;

      //     // 将前驱块逆序加入队列
      //     for (auto Pred = SourceBB->pred_rbegin(); Pred != SourceBB->pred_rend(); ++Pred) {
      //         if (!Visited.count(*Pred)) {
      //             WorkQueue.push(*Pred);
      //             Visited.insert(*Pred);
      //         }
      //     }
      // }

      for (const Register &I : DefRegs) {
        CallInst->addOperand(MachineOperand::CreateReg(I, true, true));
      }

      for (const Register &I : UseRegs) {
        CallInst->addOperand(MachineOperand::CreateReg(I, false, true));
      }
      
      // // 将原区域的livein添加到原函数的初始块试试？
      // 遍历入口块的 live-in 寄存器，并将它们添加到 replaceMBB
      for (auto LI = FirstMBB->livein_begin(), LE = FirstMBB->livein_end(); LI != LE; ++LI) {
          replaceMBB->addLiveIn(*LI);
      }

      // // Compute live-in set for original MF
      // const MachineRegisterInfo &MRI = OriginalMF->getRegInfo();
      // const TargetRegisterInfo &TRI = *MRI.getTargetRegisterInfo();
      // LivePhysRegs RegionLiveIns(TRI);
      // for (MachineBasicBlock *MBB : MRABlocks) {
      //   LivePhysRegs BlockLiveIns(TRI);
        
      //   // 计算该基本块的 live-out 集合
      //   BlockLiveIns.addLiveOuts(*MBB);

      //   // 反向遍历指令，计算 live-in 集合
      //   for (const MachineInstr &MI : reverse(*MBB))
      //     BlockLiveIns.stepBackward(MI);

      //   // 合并 BlockLiveIns 到 RegionLiveIns
      //   for (MCPhysReg Reg : BlockLiveIns)
      //     RegionLiveIns.addReg(Reg);
      // }

      // // 在 outlined function 中添加 RegionLiveIns
      // addLiveIns(*replaceMBB, RegionLiveIns);

      // 将区域内所有块标记为待删除
      for (MachineBasicBlock *MBB : MRABlocks) {
        BlocksToErase.push_back(MBB);
      }

      // 将所有替换块放入集合，便于后续检查控制流
      ReplacedBlockSet.insert(replaceMBB);

      // // 删除整个区域的所有基本块
      // for (MachineBasicBlock *MBB : BlocksToErase) {
      //   MBB->eraseFromParent();
      // }
      
      //lzc,todo
      //更新mapper，为了后续进行多次迭代
      // // Keep track of what we removed by marking them all as -1.
      // std::for_each(Mapper.UnsignedVec.begin() + C.getStartIdx(),
      //               Mapper.UnsignedVec.begin() + C.getEndIdx() + 1,
      //               [](unsigned &I) { I = static_cast<unsigned>(-1); });
      RegionAbstractedSomething = true;

      // Statistics.
      NumRAed++;
    }

  return RegionAbstractedSomething;

}

MachineBasicBlock * MachineRepeatedItemInRegion::splitMBB(MachineBasicBlock *MBB, MachineInstr *MI) {
    // 获取 MI 前一条指令
    MachineBasicBlock::iterator It = MI->getIterator();
    if (It != MBB->begin()) {//fixme,暂时防止割空，后期可完善切割逻辑
      --It; // 获取前一条指令
      // llvm::dbgs() << "StartInst is the first instruction in the block.\n";
      // return 1;
    }else return MBB; // 当It为开头指令时，不进行切割,返回当前基本块指针
    MachineInstr *SplitInst = &*It;
    // 使用 splitAt 函数分割基本块，确保分界指令被包含在新创建的块中 
    MachineBasicBlock *NewMBB = MBB->splitAt(*SplitInst);
    return NewMBB;
}

bool MachineRepeatedItemInRegion::splitRepeatedSubstring(
    DenseSet<MachineBasicBlock *> &NonSplittableBlockSet,
    std::set<MachineFunction *> &AffectedFuncs) {
  MachineInstr *RSStartInst = RepeatedInstrDatas.front();
  if (EntryBlockSplitMode != 2 &&
      RSStartInst != (&RSStartInst->getParent()->front())) {

    while (RSStartInst->isPHI()) {
      if (RepeatedInstrDatas.empty())
        return false;
      RepeatedInstrDatas.erase(RepeatedInstrDatas.begin());
      RepeatedInstSet.remove(RSStartInst);
      RSStartInst = RepeatedInstrDatas[0];
    }

    MachineBasicBlock *RSStartBB = RSStartInst->getParent();
    MachineBasicBlock *RSPreBB = RSStartBB;
    std::string OriginalName = RSPreBB->getName().str();
    RSStartBB = splitMBB(RSPreBB, RSStartInst);
    // RSStartBB =
    //     RSPreBB->splitBasicBlock(RSStartInst, OriginalName + "_before_rs");
    AffectedFuncs.insert(RSPreBB->getParent());
    // update ReleatedBlocks and ReleatedBBSet
    RelatedMBlocks[0] = RSStartBB;
    RelatedMBBSet.erase(RSPreBB);
    RelatedMBBSet.insert(RSStartBB);
    // update MinRegion
    MinRegion->Blocks.push_back(RSStartBB);
    NonSplittableBlockSet.insert(RSStartBB);
  }

  MachineInstr *RSEndInst = RepeatedInstrDatas.back();
  if (ExitBlockSplitMode != 2 &&
      RSEndInst != (&RSEndInst->getParent()->back())) {
    MachineBasicBlock *RSEndBB = RSEndInst->getParent();
    MachineBasicBlock *RSPostBB = RSEndBB;
    std::string OriginalName = RSEndBB->getName().str();
    RSPostBB = splitMBB(RSEndBB, RSEndInst);
    // RSPostBB = RSEndBB->splitBasicBlock(RSEndInst->getNextNode(),
    //                                     OriginalName + "_after_rs");
    AffectedFuncs.insert(RSEndBB->getParent());
    // update RepeatedInstrDatas and RepeatedInstSet
    MachineInstr *MI = &*RSEndBB->getFirstTerminator();
    RepeatedInstrDatas.push_back(MI);
    RepeatedInstSet.insert(MI);

    // RSPostBB->dump();

    // update MinRegion
    MinRegion->Blocks.push_back(RSPostBB);
    NonSplittableBlockSet.insert(RSPostBB);
  }
  return true;
}

// 区域指令序列相同性检验
bool isRegionSame(MRARegionGroup *Group) {
  unsigned referenceHashId = Group->front()->MinRegion->RegionHashId;

  // 遍历所有区域，比较哈希值
  for (MachineRepeatedItemInRegion *Candidate : *Group) {
    LzcRegion *MinRegion = Candidate->MinRegion;
    if (MinRegion->RegionHashId != referenceHashId) {
      return false; // 如果有不同的哈希值，返回 false
    }
  }
  return true;
}


bool MachineRegionAbstractManager::mergeRegionGroup(MRARegionGroup *Group,
                                              MachineRegionMergeInfo &MRMI) {
  // return false if no need to merge
  if (Group->size() < 2) {
    return false;
  }

  if (!isRegionSame(Group)) return false;

  // lzc，todo，进行填充时再完成
  // 暂时忽略进一步的切割，splitRegion先切割出区域。splitRepeatedSubstring在区域中进一步切割相同的块出来
  // for (MachineRepeatedItemInRegion *MachineRegionCandidate : *Group) {
  //   MachineRegionCandidate->splitRepeatedSubstring(NonSplittableBlockSet,
  //                                           AffectedFuncs);
  // }

  CreatedMergedFuncList.push_back(
      createMergedFunc(Group, MRMI, CreatedMergedFunctionNum));
  CreatedMergedFunctionNum++;
  if (!fillMergedFunc(Group, MRMI)) {
    CreatedMergedFuncList.pop_back();
    CreatedMergedFunctionNum--;
    //MRMI.MergedFunc->eraseFromParent(); lzc?
    MRMI.MergedFunc = nullptr;
    return false;
  }

  ////替换原region
  replaceCall(Group, MRMI);
  //replaceCodeWithCall(Group, MRMI);

  dbgs() << "替换后";
  printMIR();

  return true;
}

// int MachineRegionMergeInfo::getNewBenefit(TargetTransformInfo &TTI) {
//   if (CurrGroup->size() < 2) {
//     return 0;
//   }

//   int N = (*CurrGroup).size();
//   int MatchLength = (*CurrGroup)[0]->RepeatedInstrDatas.size();

//   if (RABenefitModel.getValue() == 0) {
//     int MatchBenefit = MatchLength * (N - 1);
//     int Overhead = getCallOverhead() + getMergeFunctionOverhead();
//     return MatchBenefit - Overhead;
//   }

//   if (RABenefitModel.getValue() == 1) {
//     MatchLength = estimateInstListSize((*CurrGroup)[0]->RepeatedInstSet, TTI);
//     int MatchBenefit = MatchLength * (N - 1);
//     int Overhead =
//         getCallOverheadForBinary(TTI) + getMergeFunctionOverheadForBinary(TTI);
//     return MatchBenefit - Overhead;
//   }

//   int MatchBenefit = MatchLength * (N - 1);
//   int Overhead =
//       1 + N - 1 + (1 + 2 * OutputsTypeList.size()) * N + OutputsTypeList.size();
//   return MatchBenefit > Overhead ? (MatchBenefit - Overhead) : 0;
// }

int MachineRegionAbstractManager::getGroupBenefit(MachineRegionMergeInfo &MRMI) {
  // TargetTransformInfo TTI(M.getDataLayout());
  // return MRMI.getNewBenefit(TTI);
  int N = MRMI.CurrGroup->size();
  if (N < 2) {
    return 0;
  }
  int MatchLength = (*MRMI.CurrGroup)[0]->RepeatedInstrDatas.size();
  int MatchBenefit = MatchLength * (N - 1);
  // int Overhead = getCallOverhead() + getMergeFunctionOverhead();
  int Overhead = N + 1;
  return MatchBenefit - Overhead;
  // return RAInterBenefitLimit.getValue() + 1;
  //Todo,lzc
}

bool MachineRegionAbstractManager::mergeCandidateList() {
  // int I = 0;
  int TotalBenefit = 0;
  for (MRARegionGroup *CandidatePointer : CandidateList) {
    MachineRegionMergeInfo MRMI(CandidatePointer);
    analysisRegionGroup(CandidatePointer, MRMI);
    int Benefit = getGroupBenefit(MRMI);//调用functionfolding的收益模型？？
    int LowerLimit = RAInterBenefitLimit.getValue();
    if (Benefit > LowerLimit) {
      // if ((*CandidatePointer->begin())
      //         ->RelatedMBlocks[0]
      //         ->getParent()
      //         ->getName() == "_Z17ix86_match_ccmodeP7rtx_def12machine_mode") {
      //   (*CandidatePointer->begin())->printAllInsts(errs());
      //   errs() << "\n";
      //   (*CandidatePointer)[1]->printAllInsts(errs());
      //   errs() << "\n" << (*CandidatePointer).size() << "\n";
      // }
      if (mergeRegionGroup(CandidatePointer, MRMI)) {
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
    for (MRARegionGroup *CandidatePointer : IntraBlockCandidateList) {
      MachineRegionMergeInfo MRMI(CandidatePointer);
      analysisRegionGroup(CandidatePointer, MRMI);
      int Benefit = getGroupBenefit(MRMI);//lzc todo代价模型
      int LowerLimit =
          RABenefitModel.getValue() == 0 ? 0 : RAIntraBenefitLimit.getValue();
      if (Benefit > LowerLimit) {
        if (mergeRegionGroup(CandidatePointer, MRMI)) {
          if (Debug)
            errs() << "Intra-BB MF_" << CreatedMergedFunctionNum - 1
                   << " benefit:\t" << Benefit << "\n";
          TotalBenefit += Benefit;
          if (CreatedMergedFunctionNum >= RACreatedFuncUpperLimit.getValue()) {
            break;
          }
        }
      }
        // if (mergeRegionGroup(CandidatePointer, MRMI)) {
        //   if (Debug)
        //     errs() << "Intra-BB MF_" << CreatedMergedFunctionNum - 1
        //            << " benefit:\t" << Benefit << "\n";
        //   TotalBenefit += Benefit;
        //   if (CreatedMergedFunctionNum >= RACreatedFuncUpperLimit.getValue()) {
        //     break;
        //   }
        
        // }
    }
  }

  // DeleteDeadBlocks(BlocksToDelete);
  // for (Function *Func : AffectedFuncs) {
  //   postProcessFunction(*Func);
  // }

  if (Debug) {
    errs() << "When RAAggregateArgs is :"
           << to_string(RAAggregateArgs.getValue()) << "\n";
    errs() << "Get Total IR Benefit:\t" << to_string(TotalBenefit) << "\n";
  }

  return true;
}

// // MIR层区域抽象的总控程序
// struct MachineRegionAbstract : public ModulePass
// {

//   static char ID;

//   /// Set to true if the outliner should consider functions with
//   /// linkonceodr linkage.
//   bool OutlineFromLinkOnceODRs = false;
  
//   /// The current repeat number of machine outlining.
//   unsigned OutlineRepeatedNum = 0;

//   /// Set to true if the outliner should run on all functions in the module
//   /// considered safe for outlining.
//   /// Set to true by default for compatibility with llc's -run-pass option.
//   /// Set when the pass is constructed in TargetPassConfig.
//   bool RunOnAllFunctions = true;

//   StringRef getPassName() const override { return "Machine Region Abstract "; }
    
//   //设置依赖关系
//   void getAnalysisUsage(AnalysisUsage &AU) const override {
//     AU.addRequired<MachineModuleInfoWrapperPass>();
//     AU.addPreserved<MachineModuleInfoWrapperPass>();
//     AU.setPreservesAll();
//     ModulePass::getAnalysisUsage(AU);
//   }

//   MachineRegionAbstract() : ModulePass(ID) {
//     initializeMachineRegionAbstractPass(*PassRegistry::getPassRegistry());
//   }

//   // /// Remark output explaining that not outlining a set of candidates would be
//   // /// better than outlining that set.
//   // void emitNotOutliningCheaperRemark(
//   //     unsigned StringLen, std::vector<Candidate> &CandidatesForRepeatedSeq,
//   //     OutlinedFunction &OF);

//   // /// Remark output explaining that a function was outlined.
//   // void emitOutlinedFunctionRemark(OutlinedFunction &OF);

//   bool runOnModule(Module &M) override;
  
//     /// Populate and \p InstructionMapper with instruction-to-integer mappings.
//   /// These are used to construct a suffix tree.
//   void populateMapper(InstructionMapper &Mapper, Module &M,
//                       MachineModuleInfo &MMI);

// };


} // namespace

char MachineRegionAbstract::ID = 0;

namespace llvm {
ModulePass *createMachineRegionAbstractPass(bool RunOnAllFunctions) {
  MachineRegionAbstract *MRA = new MachineRegionAbstract();
  MRA->RunOnAllFunctions = RunOnAllFunctions;
  return MRA;
}

} // namespace llvm

//初始化machinepass？
INITIALIZE_PASS(MachineRegionAbstract, DEBUG_TYPE, "Machine Region Abstract", false,
                false)


void MachineRegionAbstract::populateMapper(InstructionMapper &Mapper, Module &M,
                                     MachineModuleInfo &MMI) {
  // Build instruction mappings for each function in the module. Start by
  // iterating over each Function in M.
  //先定义好function分隔符的下限，凡是对应值大于此下限的都是函数分隔符；
  unsigned FuncDelimiterNumber = UINT_MAX - 3;
  //unsigned FuncDelimiterLowerLimit = FuncDelimiterNumber - FunctionsToProcess.size();
  //todo,修改为更合理的值
  unsigned FunctionsToProcessNum = 10000;//暂定为10000,lzc,todo
  unsigned FuncDelimiterLowerLimit = FuncDelimiterNumber - FunctionsToProcessNum;
  // NormalUpperLimit是因为还有DFS造成的分隔符，数目无法确定
  unsigned NormalUpperLimit = FuncDelimiterLowerLimit;
  for (Function &F : M) {

    // If there's nothing in F, then there's no reason to try and outline from
    // it.
    if (F.empty())
      continue;

    // There's something in F. Check if it has a MachineFunction associated with
    // it.
    MachineFunction *MF = MMI.getMachineFunction(F);

    // If it doesn't, then there's nothing to outline from. Move to the next
    // Function.
    if (!MF)
      continue;

    const TargetInstrInfo *TII = MF->getSubtarget().getInstrInfo();

    if (!RunOnAllFunctions && !TII->shouldOutlineFromFunctionByDefault(*MF))
      continue;

    // We have a MachineFunction. Ask the target if it's suitable for outlining.
    // If it isn't, then move on to the next Function in the module.
    if (!TII->isFunctionSafeToOutlineFrom(*MF, OutlineFromLinkOnceODRs))
      continue;

    DenseSet<MachineBasicBlock *> MBBsTraversed;
    std::vector<MachineBasicBlock *> MBBStack;

    MBBStack.push_back(&*MF->begin());
    
    //每个function之间插入的特殊值，用于隔断function.CFG中一条块链深度遍历结束也是如此
    MachineBasicBlock::iterator functionTerminator, blockTerminator;

    while (!MBBStack.empty()) {
      MachineBasicBlock *MBB = MBBStack.back();
      MBBStack.pop_back();
      if (MBBsTraversed.contains(MBB)) {
        blockTerminator = MBB->end();
        Mapper.InstrList.push_back(blockTerminator); //任意添加一个指令，作为空白指令
        Mapper.UnsignedVec.push_back(NormalUpperLimit--);
        continue;
      }
      if (MBB->empty() || MBB->size() < 2)
        continue;

      // Check if MBB could be the target of an indirect branch. If it is, then
      // we don't want to outline from it.
      if (MBB->hasAddressTaken())
        continue;

      // MBB is suitable for outlining. Map it to a list of unsigneds.
      Mapper.convertToUnsignedVec(*MBB, *TII);
      MBBsTraversed.insert(MBB);
    //把所有子节点压入栈内,如果没有子节点，则这一直链结束，需要插入分隔符，即一个特殊值
      if (MBB->succ_size() == 0) {//当没有后继块时，隔断
        // TODO:
        Mapper.InstrList.push_back(MBB->end()); //添加函数之间的隔断，块之间的隔断取消？？
        Mapper.UnsignedVec.push_back(NormalUpperLimit--); //隔断同时反映在映射后的数组中
        continue;
      }
      for (MachineBasicBlock *Succ : reverse(MBB->successors())) {
        MBBStack.push_back(Succ);
      }

      //每个function之间插入的特殊值，用于隔断function
      functionTerminator = MBB->end();

    }
    // Function之间不可能被连接在一起；因此每个Function之间都插入一个特殊值（每个function不同），保证不会被识别为相同
    //同理，每个region之间，每个block之间也应该考虑此值
    Mapper.InstrList.push_back(functionTerminator); //添加函数之间的隔断，块之间的隔断取消？？
    Mapper.UnsignedVec.push_back(FuncDelimiterNumber--); //隔断同时反映在映射后的数组中
  }
}

//swh
//IR层的继承函数属性方法，比MachineOutliner更细致？
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
  // FIXME: This should be changed to check to see if a specifici
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
      case Attribute::NoUnwind: // lzc对于noUnwind无法继承？
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


//先创建空函数，再填充内容
MachineFunction *
MachineRegionAbstractManager::createMergedFunc(MRARegionGroup *Group,
                                        MachineRegionMergeInfo &MRMI,
                                        unsigned int FunctionNameSuffix) {
  assert(!MRMI.MergedFunc && "MachineFunction is already defined!");
  std::string FunctionName = "OUTLINED_FUNCTION_" + std::to_string(FunctionNameSuffix);
  LLVMContext &Context = M.getContext();

  // std::vector<Type *> ParamTy;

  // if (RAAggregateArgs.getValue() && RAAggregateSourceId.getValue()) {
  //   // when RAAggregateSourceId is true, use a i32 to identify source.
  //   ParamTy.push_back(IntegerType::get(Context, 32));
  //   MRMI.InputsParamListOffset++;
  // } else {
  //   for (int I = 0; I < Group->size(); I++) {
  //     ParamTy.push_back(IntegerType::get(Context, 1));
  //     MRMI.InputsParamListOffset++;
  //   }
  // }

  // ParamTy.insert(ParamTy.end(), MRMI.InputsTypeList.begin(),
  //                MRMI.InputsTypeList.end());

  // MRMI.OutputsParamListOffset =
  //     MRMI.InputsParamListOffset + MRMI.InputsTypeList.size();

  // ParamTy.insert(ParamTy.end(), MRMI.OutputsTypeList.begin(),
  //                MRMI.OutputsTypeList.end());

  // errs() << "ParamSize:" << ParamTy.size() << "\n";
  // for (RepeatedItemInRegion *Region : *Group) {
  //   if (Region->MinRegion->Blocks.size() < 10) {
  //     Region->dumpOnly();
  //   }
  // }

  // if (RAAggregateArgs.getValue()) {
  //   MRMI.StructTy = StructType::get(M.getContext(), ParamTy);
  //   ParamTy.clear();
  //   ParamTy.push_back(PointerType::getUnqual(MRMI.StructTy));
  // }

  // MRMI.MergedFuncType =
  //     FunctionType::get(Type::getVoidTy(M.getContext()), ParamTy, false);

  GlobalValue::LinkageTypes RALinkageType = AbstractToPrivateLinkage.getValue()
                                                ? GlobalValue::PrivateLinkage
                                                : GlobalValue::InternalLinkage;
  
  // Create the function using an IR-level function.
  Function *F = Function::Create(FunctionType::get(Type::getVoidTy(Context), false),
                                 Function::ExternalLinkage, FunctionName, M);

  // NOTE: If this is linkonceodr, then we can take advantage of linker deduping
  // which gives us better results when we outline from linkonceodr functions.
  F->setLinkage(GlobalValue::InternalLinkage);
  F->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);

  // Set optsize/minsize, so we don't insert padding between outlined
  // functions.
  F->addFnAttr(Attribute::OptimizeForSize);
  F->addFnAttr(Attribute::MinSize);

  // MRMI.MergedFunc =
  //     MachineFunction::Create(MRMI.MergedFuncType, RALinkageType,
  //                      "ra_ir_func_" + std::to_string(FunctionNameSuffix), M);

  // MRMI.MergedFunc->addFnAttr(Attribute::OptimizeForSize);
  // MRMI.MergedFunc->addFnAttr(Attribute::MinSize);


  //采用swh IR层的继承函数属性的方法，没有使用MachineOutliner的做法
  for (MachineRepeatedItemInRegion *Candidate : *Group) {
    MachineFunction *OldMachineFunc = Candidate->ParentFunc;
    Function *OldFunc = &(OldMachineFunc->getFunction());
    inheritFuncAttr(OldFunc, F);
  }

  BasicBlock *EntryBB = BasicBlock::Create(Context, "entry", F);
  IRBuilder<> Builder(EntryBB);
  Builder.CreateRetVoid();

  //MachineModuleInfo &MMI = getAnalysis<MachineModuleInfoWrapperPass>().getMMI();
  MachineFunction &MF = MMI.getOrCreateMachineFunction(*F);
  MachineBasicBlock &MBB = *MF.CreateMachineBasicBlock();
  const TargetSubtargetInfo &STI = MF.getSubtarget();
  const TargetInstrInfo &TII = *STI.getInstrInfo();

  // Insert the new function into the module.
  //MF.insert(MF.begin(), &MBB);
  MRMI.MergedFunc = &MF;
  //

  // build releation for Arguments
  //lzc,暂时不用。
  //MRMI.buildArgumentsRelation();
  
  return MRMI.MergedFunc;
}

// //以扩充的形式进行函数填写
// bool MachineRegionAbstractManager::fillMergedFunc(MRARegionGroup *Group,
//                                            MachineRegionMergeInfo &MRMI) {
//   // init
//   // SmallPtrSet<BasicBlock *, 1> ExitBlocks;
//   MachineFunction *NewFunction = MRMI.MergedFunc;
//   // 命名MachineBasicBlock
//   //llvm::BasicBlock *BB = llvm::BasicBlock::Create(NewFunction->getFunction().getContext(), "newFuncRoot", &NewFunction->getFunction());
//   // MachineBasicBlock *NewFuncRoot =
//   //     NewFunction->CreateMachineBasicBlock(BB);

//   // BB = llvm::BasicBlock::Create(NewFunction->getFunction().getContext(), "newFuncExit", &NewFunction->getFunction());
//   // MachineBasicBlock *NewFuncExit =
//   //     NewFunction->CreateMachineBasicBlock(BB);

//     MachineBasicBlock *NewFuncRoot =
//       NewFunction->CreateMachineBasicBlock();

//     MachineBasicBlock *NewFuncExit =
//       NewFunction->CreateMachineBasicBlock();

//   //创建块以后，还需要插入到函数中
//   NewFunction->insert(NewFunction->begin(), NewFuncRoot);
//   NewFunction->insert(NewFunction->end(), NewFuncExit);

//   //lzc?,需要将块加入链？
//   // NewFunction->BasicBlockListType.push_back(NewFuncRoot);
//   // MachineBasicBlock *NewFuncExit =
//   //     MachineBasicBlock::Create(NewFunction->getContext(), "newFuncExit");
//   // NewFunction->getBasicBlockList().push_back(NewFuncExit);

//   std::vector<MachineInstr *> ListSelects;
//   std::vector<AllocaInst *> Allocas;
//   std::vector<unsigned> MatchedPHINodes;

//   std::list<MachineInstr *> LinearOffendingInsts;
//   std::set<MachineInstr *> OffendingInsts;

//   std::vector<Value *> SourceIds;//lzc不知道用途,用来处理来源的选择？

//   // Fill In Content
//   unsigned CurrentMatchedInstIndex = 0;
//   // 1. fill in content for match part
//   //for (unsigned I = 0; I < (*Group)[0]->RelatedMBlocks.size(); I++) {
//     // BasicBlock *LabelBB = BasicBlock::Create(NewFunction->getFunction().getContext(),
//     //                                          "m.label.bb", &NewFunction->getFunction());
//     // MachineBasicBlock *LabelMBB = NewFunction->CreateMachineBasicBlock(BB);

//     //填充相同部分情况，直接复制MinRegion
//     MachineRepeatedItemInRegion *Candidate0 = (*Group)[0];
    
//     LzcRegion *MinRegion = Candidate0->MinRegion;
//     MachineFunction *OriginalMF = Candidate0->ParentFunc;
//     // MachineBasicBlock *SourceBB = Candidate0->RelatedMBlocks[I];
//     const std::vector<MCCFIInstruction> &Instrs = OriginalMF->getFrameInstructions();
//     std::unordered_map<MachineBasicBlock *, MachineBasicBlock *> OldToNewBBMap;

//     for (MachineBasicBlock *SourceBB : MinRegion->Blocks)
//     {
//       MachineBasicBlock *LabelMBB = NewFunction->CreateMachineBasicBlock();
//       NewFunction->insert(++(NewFunction->begin()), LabelMBB);//插入到中间位置？
//       //MRMI.addMatchedBBRelation(I, LabelBB);

//       for (MachineInstr &MI : *SourceBB) {
//         if (CurrentMatchedInstIndex >= Candidate0->RepeatedInstSet.size()) {
//           break;
//         }
//         if (&MI != Candidate0->RepeatedInstSet[CurrentMatchedInstIndex]) {
//           MI.dump();
//           Candidate0->RepeatedInstSet[CurrentMatchedInstIndex]->dump();
//           if (Debug) {
//             errs() << "Error: no map for instruction\n";
//           }
//           //return false;
//         }

//       // //lzc，todo,对PHI的特殊处理
//       // BasicBlock *InstBB = MI.isPHI()
//       //                          ? LabelBB
//       //                          : BasicBlock::Create(NewFunction->getFunction().getContext(),
//       //                                               "m.inst.bb", &NewFunction->getFunction());

//       //       if (isa<PHINode>(&MI)) {
//       //   MatchedPHINodes.push_back(CurrentMatchedInstIndex);
//       // }
//       if(MI.isDebugInstr())
//         continue;
//       MachineInstr *NewMI = NewFunction->CloneMachineInstr(&MI);
//       if (MI.isCFIInstruction()) {
//         unsigned CFIIndex = NewMI->getOperand(0).getCFIIndex();
//         MCCFIInstruction CFI = Instrs[CFIIndex];
//         (void)NewFunction->addFrameInst(CFI);
//       }

//       NewMI->dropMemRefs(*NewFunction);
//       // Don't keep debug information for outlined instructions.
//       NewMI->setDebugLoc(DebugLoc());
//       LabelMBB->insert(LabelMBB->end(), NewMI);

//       //lzc,todo? 构建旧指令和新块之间的映射？？
//       //MRMI.addMatchedInstRelation(CurrentMatchedInstIndex, NewI);

//       CurrentMatchedInstIndex++;
//       }
//     }
    
//     // Candidate0->printAllInsts();
//     // errs() << "\n\n" << *SourceBB << "\n";

//   //}
//   // Set normal properties for a late MachineFunction.
//   NewFunction->getProperties().reset(MachineFunctionProperties::Property::IsSSA);
//   NewFunction->getProperties().set(MachineFunctionProperties::Property::NoPHIs);
//   NewFunction->getProperties().set(MachineFunctionProperties::Property::NoVRegs);
//   NewFunction->getProperties().set(MachineFunctionProperties::Property::TracksLiveness);
//   NewFunction->getRegInfo().freezeReservedRegs(*NewFunction);

//   //   // Compute live-in set for outlined fn
//   // const MachineRegisterInfo &MRI = NewFunction->getRegInfo();
//   // const TargetRegisterInfo &TRI = *MRI.getTargetRegisterInfo();
//   // LivePhysRegs LiveIns(TRI);
//   // for (auto &Cand : OF.Candidates) {
//   //   // Figure out live-ins at the first instruction.
//   //   MachineBasicBlock &OutlineBB = *Cand.front()->getParent();
//   //   LivePhysRegs CandLiveIns(TRI);
//   //   CandLiveIns.addLiveOuts(OutlineBB);
//   //   for (const MachineInstr &MI :
//   //        reverse(make_range(Cand.front(), OutlineBB.end())))
//   //     CandLiveIns.stepBackward(MI);

//   //   // The live-in set for the outlined function is the union of the live-ins
//   //   // from all the outlining points.
//   //   for (MCPhysReg Reg : CandLiveIns)
//   //     LiveIns.addReg(Reg);
//   // }
//   // addLiveIns(MBB, LiveIns);

//   // TII.buildOutlinedFrame(MBB, MF, OF);
//   return true;
// }

bool MachineRegionAbstractManager::fillMergedFunc(MRARegionGroup *Group,
                                                   MachineRegionMergeInfo &MRMI) {
  // 初始化
  MachineFunction *NewFunction = MRMI.MergedFunc;

  ///lzc,暂时未用上初始块
  // // 创建根块和退出块
  // MachineBasicBlock *NewFuncRoot = NewFunction->CreateMachineBasicBlock();
  //MachineBasicBlock *NewFuncExit = NewFunction->CreateMachineBasicBlock();
  //NewFunction->insert(NewFunction->begin(), NewFuncRoot);
  //NewFunction->insert(NewFunction->end(), NewFuncExit);

  // 初始化映射，跟踪旧块到新块的映射
  std::unordered_map<MachineBasicBlock *, MachineBasicBlock *> OldToNewBBMap;

  // 复制RegionMBBs（即MinRegion->Blocks中的块）到新函数
  MachineRepeatedItemInRegion *Candidate0 = (*Group)[0];
  LzcRegion *MinRegion = Candidate0->MinRegion;
  MachineFunction *OriginalMF = Candidate0->ParentFunc;
  const std::vector<MCCFIInstruction> &Instrs = OriginalMF->getFrameInstructions();

  MachineBasicBlock *EntryBlock, *ExitBlock;
  if (MinRegion->Blocks.size() < 2) {
    EntryBlock = MinRegion->Blocks[0];
    ExitBlock = MinRegion->Blocks[0];
  } else {
    EntryBlock = MinRegion->Blocks[1];
    ExitBlock = MinRegion->Blocks[0];
  }

    //广度优先进行还原
    // // 队列，用于按广度优先顺序处理块
    // std::queue<MachineBasicBlock*> WorkQueue;
    // 深度优先进行还原
    // 栈，用于按深度优先顺序处理块
    std::stack<MachineBasicBlock*> WorkStack;
    // 集合，用于防止重复处理块
    SmallSet<MachineBasicBlock*, 16> Visited;
    // 被fallthrough的块集合
    SmallSet<MachineBasicBlock*, 16> FallThroughed;

    //fixme,初始化被fallthrough的块集合，可以在别处遍历的时候初始
    for (MachineBasicBlock *MBB : MinRegion->Blocks)
    {
      MachineBasicBlock *fallThroughedMBB = MBB->getFallThrough();
      if (fallThroughedMBB)
      {
        FallThroughed.insert(fallThroughedMBB);
      }   
    }
    // // 将入口块加入队列
    // WorkQueue.push(EntryBlock);
    // Visited.insert(EntryBlock);
    // 将入口块加入栈
    WorkStack.push(EntryBlock);
    Visited.insert(EntryBlock);

    while (!WorkStack.empty()) {
        // MachineBasicBlock *SourceBB = WorkQueue.front();  // 获取队列中的第一个元素
        // WorkQueue.pop();  // 然后移除该元素
        MachineBasicBlock *SourceBB = WorkStack.top();  // 获取栈顶元素
        WorkStack.pop();  // 然后移除该元素

        // 在新函数中为每个旧块创建新块
        MachineBasicBlock *NewBB = NewFunction->CreateMachineBasicBlock();
        NewFunction->insert(NewFunction->end(), NewBB); // 插入到退出块之前
        OldToNewBBMap[SourceBB] = NewBB;

        // 复制指令
        for (MachineInstr &MI : *SourceBB) {
          if (MI.isDebugInstr()) continue;

          MachineInstr *NewMI = NewFunction->CloneMachineInstr(&MI);
          if (MI.isCFIInstruction()) {
            unsigned CFIIndex = NewMI->getOperand(0).getCFIIndex();
            MCCFIInstruction CFI = Instrs[CFIIndex];
            (void)NewFunction->addFrameInst(CFI);
          }
          NewMI->dropMemRefs(*NewFunction);
          NewMI->setDebugLoc(DebugLoc());
          NewBB->insert(NewBB->end(), NewMI);
        }

        // 如果当前块是出口块，结束
        if (SourceBB == ExitBlock)
            continue;

        // // 将后继块逆序加入队列
        // for (auto Succ = SourceBB->succ_rbegin(); Succ != SourceBB->succ_rend(); ++Succ) {
        //     if (!Visited.count(*Succ)) {
        //         WorkQueue.push(*Succ);
        //         Visited.insert(*Succ);
        //     }
        // }

          // 遍历所有后继块
          for (auto Succ = SourceBB->succ_begin(); Succ != SourceBB->succ_end(); ++Succ) {
              // 如果不是fallThroughMBB且未访问，则加入栈
              if (!Visited.count(*Succ) && !FallThroughed.contains(*Succ)) {
                  WorkStack.push(*Succ);
                  Visited.insert(*Succ);
              }
          }

          // 最后入栈处理fallthrough块
          // 保证fallthrough块都在当前块后
          MachineBasicBlock *fallThroughMBB = SourceBB->getFallThrough();
          // 如果存在fallThroughMBB，最后处理它
          if (fallThroughMBB && !Visited.count(fallThroughMBB)) {
              WorkStack.push(fallThroughMBB);
              Visited.insert(fallThroughMBB);
          }     
    }

  // 重新建立新块之间的控制流
  for (MachineBasicBlock *SourceBB : MinRegion->Blocks) {
    MachineBasicBlock *NewBB = OldToNewBBMap[SourceBB];
    for (MachineBasicBlock *SuccBB : SourceBB->successors()) {
      if (OldToNewBBMap.find(SuccBB) != OldToNewBBMap.end()) {
        MachineBasicBlock *NewSuccBB = OldToNewBBMap[SuccBB];
        NewBB->addSuccessor(NewSuccBB);
      }
    }
  }

  // 修正跳转指令和PHI指令
  for (MachineBasicBlock &NewBBRef : *NewFunction) {
    MachineBasicBlock *NewBB = &NewBBRef; 
    for (MachineInstr &MI : *NewBB) {
      if (MI.isBranch() || MI.isCall() || MI.isReturn()) {
        for (auto &Op : MI.operands()) {
          if (Op.isMBB()) {
            MachineBasicBlock *TargetBB = Op.getMBB();
            if (OldToNewBBMap.find(TargetBB) != OldToNewBBMap.end()) {
              Op.setMBB(OldToNewBBMap[TargetBB]);
            }
          }
        }
      } else if (MI.isPHI()) {
        for (unsigned i = 1, e = MI.getNumOperands(); i < e; i += 2) {
          MachineBasicBlock *IncomingBB = MI.getOperand(i + 1).getMBB();
          if (OldToNewBBMap.find(IncomingBB) != OldToNewBBMap.end()) {
            MI.getOperand(i + 1).setMBB(OldToNewBBMap[IncomingBB]);
          }
        }
      }
    }
  }

  const TargetSubtargetInfo &STI = NewFunction->getSubtarget();
  const TargetInstrInfo &TII = *STI.getInstrInfo();

  // 检查 ExitBlock 是否有终结指令
  MachineBasicBlock *NewExitBB = OldToNewBBMap[ExitBlock];
  if (NewExitBB->empty() || !NewExitBB->back().isTerminator()) {
    TII.buildRAFrame(*NewExitBB, *NewFunction);
  }

  // 设置新函数的属性
  NewFunction->getProperties().reset(MachineFunctionProperties::Property::IsSSA);
  NewFunction->getProperties().set(MachineFunctionProperties::Property::NoPHIs);
  NewFunction->getProperties().set(MachineFunctionProperties::Property::NoVRegs);
  NewFunction->getProperties().set(MachineFunctionProperties::Property::TracksLiveness);
  NewFunction->getRegInfo().freezeReservedRegs(*NewFunction);

  // Compute live-in set for outlined fn
  const MachineRegisterInfo &MRI = NewFunction->getRegInfo();
  const TargetRegisterInfo &TRI = *MRI.getTargetRegisterInfo();
  // LivePhysRegs RegionLiveIns(TRI);
  for (MachineBasicBlock *MBB : MinRegion->Blocks) {
    LivePhysRegs BlockLiveIns(TRI);
    
    // 计算该基本块的 live-out 集合
    BlockLiveIns.addLiveOuts(*MBB);

    // 反向遍历指令，计算 live-in 集合
    for (const MachineInstr &MI : reverse(*MBB))
      BlockLiveIns.stepBackward(MI);

    // // 合并 BlockLiveIns 到 RegionLiveIns
    // for (MCPhysReg Reg : BlockLiveIns)
    //   RegionLiveIns.addReg(Reg);

    // 将 BlockLiveIns 添加到相应的 块
    addLiveIns(*OldToNewBBMap[MBB], BlockLiveIns);
  }

  // // 在 outlined function 中添加 RegionLiveIns
  // addLiveIns(NewFunction->front(), RegionLiveIns);

  // lzc 用来保持调制信息的一致性
  //  // If there's a DISubprogram associated with this outlined function, then
  // // emit debug info for the outlined function.
  // Function *F = &NewFunction->getFunction();
  // if (DISubprogram *SP = getSubprogramOrNull(OF)) {
  //   // We have a DISubprogram. Get its DICompileUnit.
  //   DICompileUnit *CU = SP->getUnit();
  //   DIBuilder DB(M, true, CU);
  //   DIFile *Unit = SP->getFile();
  //   Mangler Mg;
  //   // Get the mangled name of the function for the linkage name.
  //   std::string Dummy;
  //   llvm::raw_string_ostream MangledNameStream(Dummy);
  //   Mg.getNameWithPrefix(MangledNameStream, F, false);

  //   DISubprogram *OutlinedSP = DB.createFunction(
  //       Unit /* Context */, F->getName(), StringRef(MangledNameStream.str()),
  //       Unit /* File */,
  //       0 /* Line 0 is reserved for compiler-generated code. */,
  //       DB.createSubroutineType(DB.getOrCreateTypeArray(None)), /* void type */
  //       0, /* Line 0 is reserved for compiler-generated code. */
  //       DINode::DIFlags::FlagArtificial /* Compiler-generated code. */,
  //       /* Outlined code is optimized code by definition. */
  //       DISubprogram::SPFlagDefinition | DISubprogram::SPFlagOptimized);

  //   // Don't add any new variables to the subprogram.
  //   DB.finalizeSubprogram(OutlinedSP);

  //   // Attach subprogram to the function.
  //   F->setSubprogram(OutlinedSP);
  //   // We're done with the DIBuilder.
  //   DB.finalize();
  // } 

  if (!NewFunction->verify())
  {
    return false;
  }

  //NewFunction->viewCFG();
  // llvm::MachineVerifier Verifier;
  // if (Verifier.runOnMachineFunction(NewFunction)) {
  //   llvm::errs() << "MachineFunction verification failed!\n";
  //   return false;
  // }
  // return true;
  
  return true;
}


// void MachineRegionMergeInfo::fillWithEachCandidate(
//     std::vector<MachineBasicBlock *> &Blocks,
//     std::map<MachineBasicBlock *, MachineBasicBlock *> &BBMap, Value *IsFunc,
//     unsigned CaseValue, MachineBasicBlock *NewFuncRoot, MachineBasicBlock *SourcePrevBB) {

//   for (MachineBasicBlock *MBB : Blocks) {
//     MachineBasicBlock *LastMergedBB = nullptr;
//     MachineBasicBlock *NewBB = nullptr;
//     bool BBHasBeenMerged = MatchedValues2NBB.find(MBB) != MatchedValues2NBB.end();
//     if (BBHasBeenMerged) {
//       LastMergedBB = MatchedValues2NBB[MBB];
//     } else {
//       std::string MBBName = "src" + to_string(CaseValue) + ".bb";
//       NewBB = MachineBasicBlock::Create(MergedFunc->getContext(), MBBName, MergedFunc);
//       CreatedMisMatchBBs.insert(NewBB);
//       VMap[BB] = NewBB;
//       BBMap[NewBB] = BB;

//       // IMPORTANT: make sure any use in a blockaddress constant
//       // operation is updated correctly
//       for (User *U : BB->users()) {
//         if (BlockAddress *BA = dyn_cast<BlockAddress>(U)) {
//           VMap[BA] = BlockAddress::get(MergedFunc, NewBB);
//         }
//       }

//       // errs() << "NewBB: " << NewBB->getName() << "\n";
//       IRBuilder<> Builder(NewBB);
//       for (Instruction &I : *BB) {
//         if (isa<PHINode>(&I)) {
//           VMap[&I] = Builder.CreatePHI(I.getType(), 0);
//         }
//       }
//     }
//     for (Instruction &I : *BB) {
//       if (isa<LandingPadInst>(&I))
//         continue;
//       if (isa<PHINode>(&I))
//         continue;

//       bool HasBeenMerged =
//           MatchedValues2NBB.find(&I) != MatchedValues2NBB.end();
//       if (HasBeenMerged) {
//         MachineBasicBlock *NodeBB = MatchedValues2NBB[&I];
//         if (LastMergedBB) {
//           // if (LastMergedBB->getTerminator())
//           MachineBasicBlock *Via =
//               chainBlocks(LastMergedBB, NodeBB, IsFunc, CaseValue);
//           if (Via) {
//             BBMap[Via] = BB;
//           }

//         } else {
//           IRBuilder<> Builder(NewBB);
//           Builder.CreateBr(NodeBB);
//         }
//         // end keep track
//         LastMergedBB = NodeBB;
//       } else {
//         if (LastMergedBB) {
//           std::string BBName = std::string("split.bb");
//           NewBB =
//               MachineBasicBlock::Create(MergedFunc->getContext(), BBName, MergedFunc);
//           CreatedMisMatchBBs.insert(NewBB);

//           MachineBasicBlock *Via = chainBlocks(LastMergedBB, NewBB, IsFunc, CaseValue);
//           if (Via) {
//             BBMap[Via] = BB;
//           }
//           BBMap[NewBB] = BB;
//         }
//         LastMergedBB = nullptr;

//         IRBuilder<> Builder(NewBB);
//         Instruction *NewI = cloneInst(Builder, MergedFunc, &I);
//         VMap[&I] = NewI;

//         //add for Function Folding
//         if (BBHasBeenMerged) {
//           MisMatchInsrInMatchedBB.insert(&I);
//         }
//         //end
        
//       }
//     }
//   }

//   MachineBasicBlock *EntryBB = Blocks.size() == 1 ? Blocks[0] : Blocks[1];
//   MachineBasicBlock *NewEntryBB = dyn_cast<MachineBasicBlock>(VMap[EntryBB]);
//   BBMap[NewFuncRoot] = SourcePrevBB;
//   MachineBasicBlock *Via = chainBlocks(NewFuncRoot, NewEntryBB, IsFunc, CaseValue);
//   if (Via) {
//     BBMap[Via] = SourcePrevBB;
//   }
// }

// bool MachineRegionAbstractManager::fillMergedFunc(MRARegionGroup *Group,
//                                            MachineRegionMergeInfo &MRMI) {
//   // init
//   // SmallPtrSet<BasicBlock *, 1> ExitBlocks;
//   MachineFunction *NewFunction = MRMI.MergedFunc;
//   // 命名MachineBasicBlock
//   llvm::BasicBlock *BB = llvm::BasicBlock::Create(NewFunction->getFunction().getContext(), "newFuncRoot", &NewFunction->getFunction());
//   MachineBasicBlock *NewFuncRoot =
//       NewFunction->CreateMachineBasicBlock(BB);

//   BB = llvm::BasicBlock::Create(NewFunction->getFunction().getContext(), "newFuncExit", &NewFunction->getFunction());
//   MachineBasicBlock *NewFuncExit =
//       NewFunction->CreateMachineBasicBlock(BB);

//   //创建块以后，还需要插入到函数中
//   NewFunction->insert(NewFunction->begin(), NewFuncRoot);
//   NewFunction->insert(NewFunction->end(), NewFuncExit);

//   //lzc?,需要将块加入链？
//   // NewFunction->BasicBlockListType.push_back(NewFuncRoot);
//   // MachineBasicBlock *NewFuncExit =
//   //     MachineBasicBlock::Create(NewFunction->getContext(), "newFuncExit");
//   // NewFunction->getBasicBlockList().push_back(NewFuncExit);

//   std::vector<MachineInstr *> ListSelects;
//   std::vector<AllocaInst *> Allocas;
//   std::vector<unsigned> MatchedPHINodes;

//   std::list<MachineInstr *> LinearOffendingInsts;
//   std::set<MachineInstr *> OffendingInsts;

//   std::vector<Value *> SourceIds;//lzc不知道用途,用来处理来源的选择？

//   for (MachineRepeatedItemInRegion *Candidate : *Group) {
//     assert(Candidate->FollowBB != nullptr && "FollowBB is null!");
//     MRMI.VMap[Candidate->FollowBB] = NewFuncExit;
//   }

//   for (int I = 0; I < (*Group).size(); I++) {
//     std::map<BasicBlock *, BasicBlock *> *MapI =
//         new std::map<BasicBlock *, BasicBlock *>();
//     MRMI.NewBB2OldBBList.push_back(MapI);
//   }
//   // finish init

//   // // build relation for AggregateArgs Value 
//   // if (RAAggregateArgs.getValue()) {
//   //   Argument *Arg0 = NewFunction->getArg(0);
//   //   Value *Idx[2];
//   //   Idx[0] =
//   //       Constant::getNullValue(Type::getInt32Ty(NewFuncRoot->getContext()));
//   //   // source id
//   //   if (RAAggregateSourceId) {
//   //     Idx[1] = ConstantInt::get(Type::getInt32Ty(NewFuncRoot->getContext()), 0);
//   //     GetElementPtrInst *GEP = GetElementPtrInst::Create(
//   //         MRMI.StructTy, Arg0, Idx, "gep_source_num", NewFuncRoot);
//   //     Value *SourceNum = new LoadInst(MRMI.StructTy->getElementType(0), GEP,
//   //                                     "source_num", NewFuncRoot);
//   //     for (int I = 0; I < Group->size(); I++) {
//   //       Value *SourceIdInt =
//   //           ConstantInt::get(Type::getInt32Ty(NewFuncRoot->getContext()), I);
//   //       CmpInst *SourceId = CmpInst::Create(
//   //           Instruction::ICmp, ICmpInst::ICMP_EQ, SourceNum, SourceIdInt,
//   //           "sourceid_" + to_string(I), NewFuncRoot);
//   //       SourceIds.push_back(SourceId);
//   //     }
//   //   } else {
//   //     for (int I = 0; I < MRMI.InputsParamListOffset; I++) {
//   //       Idx[1] =
//   //           ConstantInt::get(Type::getInt32Ty(NewFuncRoot->getContext()), I);
//   //       GetElementPtrInst *GEP = GetElementPtrInst::Create(
//   //           MRMI.StructTy, Arg0, Idx, "gep_sourceid" + to_string(I),
//   //           NewFuncRoot);
//   //       Value *SourceId = new LoadInst(MRMI.StructTy->getElementType(I), GEP,
//   //                                      "sourceid_" + to_string(I), NewFuncRoot);
//   //       SourceIds.push_back(SourceId);
//   //     }
//   //   }

//   //   // inputs
//   //   for (int I = 0; I < MRMI.InputsTypeList.size(); I++) {
//   //     Idx[1] = ConstantInt::get(Type::getInt32Ty(NewFuncRoot->getContext()),
//   //                               I + MRMI.InputsParamListOffset);
//   //     GetElementPtrInst *GEP = GetElementPtrInst::Create(
//   //         MRMI.StructTy, Arg0, Idx, "gep_input_" + MRMI.InputsNameList[I],
//   //         NewFuncRoot);
//   //     Value *NewV = new LoadInst(
//   //         MRMI.StructTy->getElementType(I + MRMI.InputsParamListOffset), GEP,
//   //         "input_" + to_string(I), NewFuncRoot);

//   //     for (RepeatedItemInRegion *Candidate : *Group) {
//   //       if (I >= Candidate->OccupiedListOfInput->size())
//   //         continue;
//   //       int InputIndex = (*Candidate->OccupiedListOfInput)[I];
//   //       if (InputIndex < 0)
//   //         continue;

//   //       Value *Input = Candidate->Inputs[InputIndex];
//   //       MRMI.InputsToArgs[Input] = NewV;
//   //     }
//   //   }
//   // } else {
//   //   for (int I = 0; I < (*Group).size(); I++) {
//   //     SourceIds.push_back(NewFunction->getArg(I));
//   //   }
//   // }

//   // Fill In Content
//   unsigned CurrentMatchedInstIndex = 0;
//   // 1. fill in content for match part
//   for (unsigned I = 0; I < (*Group)[0]->RelatedMBlocks.size(); I++) {
//     BasicBlock *LabelBB = BasicBlock::Create(NewFunction->getFunction().getContext(),
//                                              "m.label.bb", &NewFunction->getFunction());
//     MachineBasicBlock *LabelMBB = NewFunction->CreateMachineBasicBlock(BB);
//     NewFunction->insert((NewFunction->begin())++, LabelMBB);//插入到中间位置？
//     //MRMI.addMatchedBBRelation(I, LabelBB);

//     //填充相同部分情况，任意取一个MF作为母本
//     MachineRepeatedItemInRegion *Candidate0 = (*Group)[0];
    
//     MachineFunction *OriginalMF = Candidate0->ParentFunc;
//     MachineBasicBlock *SourceBB = Candidate0->RelatedMBlocks[I];
//     const std::vector<MCCFIInstruction> &Instrs = OriginalMF->getFrameInstructions();
    
//     // Candidate0->printAllInsts();
//     // errs() << "\n\n" << *SourceBB << "\n";

//     for (MachineInstr &MI : *SourceBB) {
//       if (CurrentMatchedInstIndex >= Candidate0->RepeatedInstSet.size()) {
//         break;
//       }
//       if (&MI != Candidate0->RepeatedInstSet[CurrentMatchedInstIndex]) {
//         MI.dump();
//         Candidate0->RepeatedInstSet[CurrentMatchedInstIndex]->dump();
//         if (Debug) {
//           errs() << "Error: no map for instruction\n";
//         }
//         return false;
//       }

//       // //lzc，todo,对PHI的特殊处理
//       // BasicBlock *InstBB = MI.isPHI()
//       //                          ? LabelBB
//       //                          : BasicBlock::Create(NewFunction->getFunction().getContext(),
//       //                                               "m.inst.bb", &NewFunction->getFunction());

//       //       if (isa<PHINode>(&MI)) {
//       //   MatchedPHINodes.push_back(CurrentMatchedInstIndex);
//       // }
//       if(MI.isDebugInstr())
//         continue;
//       MachineInstr *NewMI = NewFunction->CloneMachineInstr(&MI);
//       if (MI.isCFIInstruction()) {
//         unsigned CFIIndex = NewMI->getOperand(0).getCFIIndex();
//         MCCFIInstruction CFI = Instrs[CFIIndex];
//         (void)NewFunction->addFrameInst(CFI);
//         NewMI->dropMemRefs(*NewFunction);
//         // Don't keep debug information for outlined instructions.
//         NewMI->setDebugLoc(DebugLoc());
//         LabelMBB->insert(LabelMBB->end(), NewMI);
//       }

//       //lzc,todo? 构建旧指令和新块之间的映射？？
//       //MRMI.addMatchedInstRelation(CurrentMatchedInstIndex, NewI);


//       CurrentMatchedInstIndex++;
//     }
//   }

//   // if (Debug) {
//   //   raw_fd_ostream *FS = getOutputStreamOfFile(
//   //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterFillMatch.log");
//   //   *FS << *NewFunction << "\n";
//   //   delete FS;
//   // }

//   // 2. fill in mismatch part
//   for (int I = 0; I < (*Group).size(); I++) {
//     Value *SourceId = SourceIds[I];
//     MachineRepeatedItemInRegion *Candidate = (*Group)[I];
//     MRMI.fillWithEachCandidate(Candidate->MinRegion->Blocks,
//                               *MRMI.NewBB2OldBBList[I], SourceId, I, NewFuncRoot,
//                               Candidate->PrevBB);

//     if (Candidate->HasExitExtraPHI) {
//       BasicBlock *NewEndBB = MRMI.MatchedValues2NBB[Candidate->EndBB];
//       IRBuilder<> Builder(NewEndBB);
//       for (Instruction *I : Candidate->ExitExtraPHI) {
//         if (isa<PHINode>(I)) {
//           MRMI.VMap[I] = Builder.CreatePHI(I->getType(), 0);
//         } else {
//           assert(false && "Value should be phi node!");
//         }
//       }
//     }
//   }

//   // if (Debug) {
//   //   raw_fd_ostream *FS = getOutputStreamOfFile(
//   //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterFillAll.log");
//   //   *FS << *NewFunction << "\n";
//   //   delete FS;
//   // }

//   // Assign Label Operands Value
//   // 1. assign match part
//   RepeatedItemInRegion *Candidate0 = (*Group)[0];
//   for (unsigned I = 0; I < Candidate0->RepeatedInstSet.size(); I++) {
//     Instruction *OldInst = Candidate0->RepeatedInstSet[I];
//     Instruction *NewI = dyn_cast<Instruction>(MRMI.VMap[OldInst]);

//     unsigned OperandsNum = OldInst->getNumOperands();
//     for (unsigned J = 0; J < OperandsNum; J++) {
//       //获取所有对应的操作数到数组中
//       std::vector<Value *> OperandsValue;
//       std::vector<Value *> OldValueList;
//       for (unsigned X = 0; X < (*Group).size(); X++) {
//         if ((*Group)[X]->RepeatedInstSet[I]->getNumOperands() > J) {
//           Value *OldV = (*Group)[X]->RepeatedInstSet[I]->getOperand(J);
//           OldValueList.push_back(OldV);
//           //需要先在上一步，把参数的映射添加进去
//           Value *NewV = MapValue(OldV, MRMI.InputsToArgs);
//           if (NewV == nullptr)
//             NewV = MapValue(OldV, MRMI.VMap);

//           if (NewV == nullptr) {
//             errs() << "Mapped value should NOT be NULL!\n";
//             return false;
//           }

//           // assert(NewV != nullptr && "Mapped value should NOT be NULL!");
//           OperandsValue.push_back(NewV);
//         } else {
//           errs() << "Match Instr With diff NumOperands!\n";
//           return false;
//           // assert(false && "Match Instr With diff NumOperands!");
//           // OperandsValue.push_back(UndefValue::get(Inst0->getOperand(J)->getType()));
//         }
//       }

//       // handling just label operands for now
//       if (!isa<BasicBlock>(OperandsValue[0]))
//         continue;

//       Value *V1 = OperandsValue[0];
//       BasicBlock *BB1 = dyn_cast<BasicBlock>(V1);
//       if (!BB1)
//         return false;
//       std::vector<BasicBlock *> SelectBBList;
//       std::vector<unsigned> SourceCandToFix;
//       SourceCandToFix.push_back(0);

//       for (int X = 1; X < OperandsValue.size(); X++) {
//         Value *V2 = OperandsValue[X];
//         BasicBlock *BB2 = dyn_cast<BasicBlock>(V2);
//         if (!BB2)
//           return false;
//         if (V2 != V1) {
//           BasicBlock *SelectBB = BasicBlock::Create(
//               BB1->getContext(), "bb.select", MRMI.MergedFunc);
//           IRBuilder<> BuilderBB(SelectBB);
//           Instruction *Inst2 = (*Group)[X]->RepeatedInstSet[I];
//           SelectBBList.push_back(SelectBB);
//           // (*MRMI.NewBB2OldBBList[LeftId])[SelectBB] = Inst1->getParent();
//           (*MRMI.NewBB2OldBBList[X])[SelectBB] = Inst2->getParent();
//           Value *SourceId = SourceIds[X];
//           BuilderBB.CreateCondBr(SourceId, BB2, BB1);
//           BB1 = SelectBB;
//         } else {
//           SourceCandToFix.push_back(X);
//         }
//       }

//       if (dyn_cast<BasicBlock>(OldValueList.front())->isLandingPad()) {
//         BasicBlock *OldBB0 = dyn_cast<BasicBlock>(OldValueList.front());
//         LandingPadInst *LP0 = OldBB0->getLandingPadInst();

//         BasicBlock *LPadBB = BasicBlock::Create(NewFunction->getContext(),
//                                                 "lpad.bb", NewFunction);
//         IRBuilder<> BuilderBB(LPadBB);
//         Instruction *NewLP = LP0->clone();
//         BuilderBB.Insert(NewLP);
//         BuilderBB.CreateBr(dyn_cast<BasicBlock>(BB1));
//         BB1 = LPadBB;

//         for (unsigned X = 0; X < (*Group).size(); X++) {
//           Value *OldV = OldValueList[X];
//           BasicBlock *OldBB = dyn_cast<BasicBlock>(OldV);
//           LandingPadInst *LP = OldBB->getLandingPadInst();
//           assert(LP != nullptr &&
//                  "Should be both as per the BasicBlock match!");

//           (*MRMI.NewBB2OldBBList[X])[LPadBB] =
//               (*Group)[X]->RepeatedInstSet[I]->getParent();
//           MRMI.VMap[LP] = NewLP;
//         }
//       }

//       NewI->setOperand(J, BB1);
//       // fix relation of NewBB2OldBBList
//       if (SelectBBList.size() > 0) {
//         BasicBlock *SelectBB = SelectBBList[0];
//         for (int X : SourceCandToFix) {
//           (*MRMI.NewBB2OldBBList[X])[SelectBB] =
//               (*Group)[X]->RepeatedInstSet[I]->getParent();
//         }
//       }
//     }
//   }

//   // 2. assign mismatch part
//   for (int I = 0; I < (*Group).size(); I++) {
//     RepeatedItemInRegion *Candidate = (*Group)[I];
//     for (BasicBlock *BB : Candidate->MinRegion->Blocks) {
//       if (!Candidate->ReleatedBBSet.contains(BB)) {
//         for (Instruction &Inst : *BB) {
//           if (!MRMI.AssignLabelOperands(&Inst, (*MRMI.NewBB2OldBBList[I])))
//             return false;
//         }
//       }
//     }
//   }

//   // if (Debug) {
//   //   raw_fd_ostream *FS = getOutputStreamOfFile(
//   //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterAssignLabel.log");
//   //   *FS << *NewFunction << "\n";
//   //   delete FS;
//   // }

//   // Assign Value Operands
//   LLVMContext &Context = MRMI.MergedFunc->getContext();

//   auto MergeValues = [&](Value *V1, Value *V2, Instruction *InsertPt,
//                          Value *IsV2, Value *&LastSelect) -> Value * {
//     if (V1 == V2) {
//       if (LastSelect)
//         return LastSelect;
//       return V1;
//     }

//     //暂时不支持此类优化
//     // Instruction *IV1 = dyn_cast<Instruction>(V1);
//     // Instruction *IV2 = dyn_cast<Instruction>(V2);

//     // if (IV1 && IV2) {
//     //   // if both IV1 and IV2 are non-merged values
//     //   if (BlocksF2.find(IV1->getParent()) == BlocksF2.end() &&
//     //       BlocksF1.find(IV2->getParent()) == BlocksF1.end()) {
//     //     CoalescingCandidates[IV1][IV2]++;
//     //     CoalescingCandidates[IV2][IV1]++;
//     //   }
//     // }

//     IRBuilder<> Builder(InsertPt);
//     Value *FalseToSelect = LastSelect == nullptr ? V1 : LastSelect;
//     LastSelect = (Instruction *)Builder.CreateSelect(IsV2, V2, FalseToSelect);
//     ListSelects.push_back(dyn_cast<Instruction>(LastSelect));
//     return LastSelect;
//   };

//   // assign match part
//   for (unsigned InstNum = 0; InstNum < Candidate0->RepeatedInstSet.size();
//        InstNum++) {
//     Instruction *I1 = Candidate0->RepeatedInstSet[InstNum];
//     //跳过phi结点
//     if (isa<PHINode>(I1)) {
//       continue;
//     }
//     Instruction *NewI = dyn_cast<Instruction>(MRMI.VMap[I1]);

//     for (unsigned OprNum = 0; OprNum < I1->getNumOperands(); OprNum++) {

//       if (isa<BasicBlock>(I1->getOperand(OprNum)))
//         continue;
//       Value *LastSelect = nullptr;
//       //优先使用InputsToArgs做映射
//       Value *V1 = MapValue(I1->getOperand(OprNum), MRMI.InputsToArgs);
//       if (V1 == nullptr)
//         V1 = MapValue(I1->getOperand(OprNum), MRMI.VMap);
//       assert(V1 != nullptr && "Value1 should NOT be null!");

//       for (unsigned CandNum = 1; CandNum < (*Group).size(); CandNum++) {
//         RepeatedItemInRegion *Candidate = (*Group)[CandNum];
//         Instruction *I2 = Candidate->RepeatedInstSet[InstNum];
//         assert(I1->getNumOperands() == I2->getNumOperands() &&
//                "Num of Operands SHOULD be EQUAL\n");

//         Value *V2 = MapValue(I2->getOperand(OprNum), MRMI.InputsToArgs);
//         if (V2 == nullptr)
//           V2 = MapValue(I2->getOperand(OprNum), MRMI.VMap);
//         assert(V2 != nullptr && "Value2 should NOT be null!");

//         Value *SourceId = SourceIds[CandNum];
//         Value *V = MergeValues(V1, V2, NewI, SourceId, LastSelect);
//         NewI->setOperand(OprNum, V);
//       }
//     }
//   }

//   // assign mismatch part
//   for (int I = 0; I < (*Group).size(); I++) {
//     RepeatedItemInRegion *Candidate = (*Group)[I];
//     for (BasicBlock *BB : Candidate->MinRegion->Blocks) {
//       if (!Candidate->ReleatedBBSet.contains(BB)) {
//         for (Instruction &Inst : *BB) {
//           MRMI.AssignValueOperands(&Inst, (*MRMI.NewBB2OldBBList[I]));
//         }
//       }
//     }
//   }

//   // if (Debug) {
//   //   raw_fd_ostream *FS = getOutputStreamOfFile(
//   //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterAssignValue.log");
//   //   *FS << *NewFunction << "\n";
//   //   delete FS;
//   // }

//   if (ListSelects.size() > RAMaxNumSelection) {
//     if (Debug)
//       errs() << "Bailing out: Operand selection threshold\n";
//     return false;
//   }

//   // Assign Phi Node Value and Label
//   // assign match part
//   for (unsigned PhiIndex : MatchedPHINodes) {
//     Instruction *Inst0 = Candidate0->RepeatedInstSet[PhiIndex];
//     assert(isa<PHINode>(Inst0) && "Inst0 should be phi node!");
//     PHINode *NewPHI = dyn_cast<PHINode>(MRMI.VMap[Inst0]);

//     std::map<BasicBlock *, std::vector<Value *>> LastSelectAndDefaultVOfPredBB;

//     for (unsigned X = 0; X < (*Group).size(); X++) {
//       PHINode *PHI = dyn_cast<PHINode>((*Group)[X]->RepeatedInstSet[PhiIndex]);
//       std::map<BasicBlock *, BasicBlock *> &BlocksReMap =
//           *MRMI.NewBB2OldBBList[X];
//       std::set<int> FoundIndices;

//       for (auto It = pred_begin(NewPHI->getParent()),
//                 E = pred_end(NewPHI->getParent());
//            It != E; It++) {
//         BasicBlock *NewPredBB = *It;
//         Value *V = nullptr;
//         if (BlocksReMap.find(NewPredBB) != BlocksReMap.end()) {
//           BasicBlock *OldPredBB = BlocksReMap[NewPredBB];
//           int OldIndex = PHI->getBasicBlockIndex(BlocksReMap[NewPredBB]);
//           if (OldIndex >= 0) {
//             Value *OldV = PHI->getIncomingValue(OldIndex);
//             if (isa<UndefValue>(OldV)) {
//               V = UndefValue::get(NewPHI->getType());
//             } else {
//               V = MapValue(OldV, MRMI.InputsToArgs);
//               if (V == nullptr)
//                 V = MapValue(OldV, MRMI.VMap);
//             }
//             assert(V != nullptr && "Value should not be null");
//             FoundIndices.insert(OldIndex);
//           } else {
//             errs() << "NewPredBB:\n" << *NewPredBB << "\n";
//             errs() << "OldPredBB:\n" << *OldPredBB << "\n";
//             errs() << "OldPhi:\n" << *PHI << "\n";
//             errs() << "newPhi:\n" << *NewPHI << "\n";
//             errs() << "OldBB:\n" << *PHI->getParent() << "\n";
//             errs() << "newBB:\n" << *NewPHI->getParent() << "\n";

//             return false;
//             assert(false);
//           }
//         }
//         if (V) {
//           int Idx = NewPHI->getBasicBlockIndex(NewPredBB);
//           if (Idx < 0) {
//             NewPHI->addIncoming(V, NewPredBB);
//             continue;
//           }
//           Value *V0 = NewPHI->getIncomingValue(Idx);
//           if (V == V0) {
//             continue;
//           }
//           if (V != V0) {
//             Value *FalseValue = V0;
//             Value *DefaultValue = V0;
//             if (LastSelectAndDefaultVOfPredBB.count(NewPredBB)) {
//               FalseValue = LastSelectAndDefaultVOfPredBB[NewPredBB][0];
//               DefaultValue = LastSelectAndDefaultVOfPredBB[NewPredBB][1];
//               if (V == DefaultValue) {
//                 continue;
//               }
//               // otherwise, we need to create new select
//             }

//             Instruction *InsertBefore = NewPredBB->getTerminator();
//             assert(InsertBefore && "Terminator Value should not be null!");
//             Value *SourceId = SourceIds[X];
//             SelectInst *NewSelect = SelectInst::Create(SourceId, V, FalseValue,
//                                                        "for_phi", InsertBefore);
//             LastSelectAndDefaultVOfPredBB[NewPredBB] = {NewSelect,
//                                                         DefaultValue};
//             NewPHI->setIncomingValue(Idx, NewSelect);
//           }
//         } else {
//         }
//       }
//       if (FoundIndices.size() != PHI->getNumIncomingValues())
//         return false;
//     }

//     // check full and try fix
//     std::vector<BasicBlock *> Preds(pred_begin(NewPHI->getParent()),
//                                     pred_end(NewPHI->getParent()));
//     if (NewPHI->getNumIncomingValues() < Preds.size()) {
//       for (unsigned X = 0; X < (*Group).size(); X++) {
//         PHINode *OldPHI =
//             dyn_cast<PHINode>((*Group)[X]->RepeatedInstSet[PhiIndex]);
//         OldPHI->dump();
//       }
//       for (BasicBlock *Pred : Preds) {
//         int Idx = NewPHI->getBasicBlockIndex(Pred);
//         if (Idx < 0) {
//           NewPHI->addIncoming(UndefValue::get(NewPHI->getType()), Pred);
//           continue;
//         }
//       }
//     } else if (NewPHI->getNumIncomingValues() > Preds.size()) {
//       assert(false);
//     }
//   }

//   // if (Debug) {
//   //   raw_fd_ostream *FS = getOutputStreamOfFile(
//   //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterAssignPHI0.log");
//   //   *FS << *NewFunction << "\n";
//   //   delete FS;
//   // }

//   // assign mismatch part
//   for (int I = 0; I < (*Group).size(); I++) {
//     RepeatedItemInRegion *Candidate = (*Group)[I];
//     std::map<BasicBlock *, BasicBlock *> &BlocksReMap = *MRMI.NewBB2OldBBList[I];
//     for (BasicBlock *BB : Candidate->MinRegion->Blocks) {
//       if (!Candidate->ReleatedBBSet.contains(BB)) {
//         for (Instruction &Inst : *BB) {
//           if (PHINode *PHI = dyn_cast<PHINode>(&Inst)) {
//             PHINode *NewPHI = dyn_cast<PHINode>(MRMI.VMap[PHI]);
//             std::set<int> FoundIndices;

//             for (auto It = pred_begin(NewPHI->getParent()),
//                       E = pred_end(NewPHI->getParent());
//                  It != E; It++) {

//               BasicBlock *NewPredBB = *It;

//               Value *V = nullptr;

//               if (BlocksReMap.find(NewPredBB) != BlocksReMap.end()) {
//                 int Index = PHI->getBasicBlockIndex(BlocksReMap[NewPredBB]);
//                 if (Index >= 0) {
//                   V = MapValue(PHI->getIncomingValue(Index), MRMI.VMap);
//                   FoundIndices.insert(Index);
//                 }
//               }
//               if (V == nullptr)
//                 V = UndefValue::get(NewPHI->getType());
//               NewPHI->addIncoming(V, NewPredBB);
//             }
//             if (FoundIndices.size() != PHI->getNumIncomingValues())
//               return false;
//           }
//         }
//       }
//     }

//     if (Candidate->HasExitExtraPHI) {
//       for (Instruction *I : Candidate->ExitExtraPHI) {
//         PHINode *PHI = dyn_cast<PHINode>(I);
//         assert(PHI && "PHI node should not be nullptr!");
//         PHINode *NewPHI = dyn_cast<PHINode>(MRMI.VMap[PHI]);
//         std::set<int> FoundIndices;

//         for (auto It = pred_begin(NewPHI->getParent()),
//                   E = pred_end(NewPHI->getParent());
//              It != E; It++) {

//           BasicBlock *NewPredBB = *It;

//           Value *V = nullptr;

//           if (BlocksReMap.find(NewPredBB) != BlocksReMap.end()) {
//             int Index = PHI->getBasicBlockIndex(BlocksReMap[NewPredBB]);
//             if (Index >= 0) {
//               V = MapValue(PHI->getIncomingValue(Index), MRMI.VMap);
//               FoundIndices.insert(Index);
//             }
//           }
//           if (V == nullptr)
//             V = UndefValue::get(NewPHI->getType());
//           NewPHI->addIncoming(V, NewPredBB);
//         }
//         if (FoundIndices.size() != PHI->getNumIncomingValues())
//           return false;
//       }
//     }
//   }

//   //删除不必要的branch指令，合并块

//   auto CoalescingBasicBlock = [&](BasicBlock *PrevBB,
//                                   BasicBlock *SuccBB) -> void {
//     Instruction *TermInst = PrevBB->getTerminator();
//     TermInst->eraseFromParent();
//     IRBuilder<> Builder(PrevBB);
//     std::vector<Instruction *> Inst2Mov;
//     for (Instruction &Inst : *SuccBB) {
//       Inst2Mov.push_back(&Inst);
//     }
//     SuccBB->replaceSuccessorsPhiUsesWith(PrevBB);

//     for (Instruction *Inst : Inst2Mov) {
//       // Inst->eraseFromParent();
//       Inst->removeFromParent();
//       Builder.Insert(Inst);
//     }
//     SuccBB->eraseFromParent();
//   };

//   // for (auto It = MRMI.MergedFunc->begin(); It != MRMI.MergedFunc->end();) {
//   //   BasicBlock *BB = &*It;
//   //   if (BB == NewFuncExit) {
//   //     It++;
//   //     continue;
//   //   }
//   //   BasicBlock *SuccBB = BB->getSingleSuccessor();
//   //   if (SuccBB) {
//   //     if (BB == SuccBB->getSinglePredecessor() && SuccBB != NewFuncExit) {
//   //       CoalescingBasicBlock(BB, SuccBB);
//   //       continue;
//   //     }
//   //   }
//   //   It++;
//   // }

//   // if (Debug) {
//   //   raw_fd_ostream *FS = getOutputStreamOfFile(
//   //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterCB.log");
//   //   *FS << *NewFunction << "\n";
//   //   delete FS;
//   // }

//   // fix exit bb
//   IRBuilder<> ExitBuilder(NewFuncExit);
//   Argument *Arg0 = NewFunction->getArg(0);
//   Value *Idx[2];
//   Idx[0] = Constant::getNullValue(Type::getInt32Ty(NewFuncExit->getContext()));

//   for (unsigned I = 0; I < MRMI.OutputsTypeList.size(); I++) {
//     // ExitBuilder
//     // oldValue0可能为nullptr
//     int OldValue0Index = Candidate0->OutputsIndex2LocalIndex[I];
//     Value *OldValue0 =
//         OldValue0Index < 0 ? nullptr : Candidate0->Outputs[OldValue0Index];

//     Value *NewValue0 =
//         OldValue0 != nullptr ? MapValue(OldValue0, MRMI.VMap) : nullptr;
//     Value *FinalStoreValue = NewValue0;

//     Value *LastSelect = nullptr;
//     int X0 = 0;
//     for (int X = 1; X < Group->size(); X++) {
//       RepeatedItemInRegion *Candidate = (*Group)[X];
//       int OldValueIndex = Candidate->OutputsIndex2LocalIndex[I];
//       Value *OldValue =
//           OldValueIndex < 0 ? nullptr : Candidate->Outputs[OldValueIndex];
//       if (OldValue == nullptr)
//         continue;

//       Value *NewValue = MapValue(OldValue, MRMI.VMap);
//       if (OldValue0 == nullptr && NewValue != nullptr) {
//         OldValue0 = OldValue;
//         NewValue0 = NewValue;
//         FinalStoreValue = NewValue;
//         X0 = X;
//         continue;
//       }

//       if (NewValue == NewValue0)
//         continue;
//       Value *SourceId = SourceIds[X];
//       Value *FalseToSelect = LastSelect == nullptr ? NewValue0 : LastSelect;
//       LastSelect = ExitBuilder.CreateSelect(SourceId, NewValue, FalseToSelect);
//       ListSelects.push_back(dyn_cast<Instruction>(LastSelect));
//       FinalStoreValue = LastSelect;
//     }

//     assert(FinalStoreValue && "Value Should Not Be Null!");
//     Value *StoreInto = nullptr;
//     if (RAAggregateArgs.getValue()) {
//       Idx[1] = ConstantInt::get(Type::getInt32Ty(NewFuncExit->getContext()),
//                                 I + MRMI.OutputsParamListOffset);
//       StoreInto = GetElementPtrInst::Create(
//           MRMI.StructTy, Arg0, Idx, "gep_output_" + MRMI.OutputsNameList[I],
//           NewFuncExit);

//     } else {
//       StoreInto = NewFunction->getArg(MRMI.OutputsParamListOffset + I);
//     }
//     assert(StoreInto && "Value Should Not Be Null!");
//     ExitBuilder.CreateStore(FinalStoreValue, StoreInto);
//   }
//   ExitBuilder.CreateRetVoid();

//   // if (Debug) {
//   //   raw_fd_ostream *FS = getOutputStreamOfFile(
//   //       "/home/kp4/SWH/llvm-code-size/build-test/log/AfterFixExit.log");
//   //   *FS << *NewFunction << "\n";
//   //   delete FS;
//   // }

//   // errs() << NewFunction->getInstructionCount();

//   // fix Instruction dominace
//   DominatorTree DT(*NewFunction);

//   // find instructions need fix
//   for (Instruction &I : instructions(NewFunction)) {
//     if (PHINode *PHI = dyn_cast<PHINode>(&I)) {
//       for (unsigned i = 0; i < PHI->getNumIncomingValues(); i++) {
//         BasicBlock *BB = PHI->getIncomingBlock(i);
//         if (BB == nullptr)
//           errs() << "Null incoming block\n";
//         Value *V = PHI->getIncomingValue(i);
//         if (V == nullptr)
//           errs() << "Null incoming value\n";
//         if (Instruction *IV = dyn_cast<Instruction>(V)) {
//           if (BB->getTerminator() == nullptr) {
//             if (Debug)
//               errs() << "ERROR: Null terminator\n";
//             return false;
//           }
//           if (!DT.dominates(IV, BB->getTerminator())) {
//             if (OffendingInsts.count(IV) == 0) {
//               OffendingInsts.insert(IV);
//               LinearOffendingInsts.push_back(IV);
//             }
//           }
//         }
//       }
//     } else {
//       for (unsigned i = 0; i < I.getNumOperands(); i++) {
//         if (I.getOperand(i) == nullptr) {
//           if (Debug)
//             errs() << "ERROR: Null operand\n";
//           return false;
//         }
//         if (Instruction *IV = dyn_cast<Instruction>(I.getOperand(i))) {
//           if (!DT.dominates(IV, &I)) {
//             if (OffendingInsts.count(IV) == 0) {
//               OffendingInsts.insert(IV);
//               LinearOffendingInsts.push_back(IV);
//             }
//           }
//         }
//       }
//     }
//   }

//   auto StoreInstIntoAddr = [](Instruction *IV, Value *Addr) {
//     IRBuilder<> Builder(IV->getParent());
//     if (IV->isTerminator()) {
//       BasicBlock *SrcBB = IV->getParent();
//       if (InvokeInst *II = dyn_cast<InvokeInst>(IV)) {
//         BasicBlock *DestBB = II->getNormalDest();

//         Builder.SetInsertPoint(&*DestBB->getFirstInsertionPt());
//         // create PHI
//         PHINode *PHI = Builder.CreatePHI(IV->getType(), 0);
//         for (auto PredIt = pred_begin(DestBB), PredE = pred_end(DestBB);
//              PredIt != PredE; PredIt++) {
//           BasicBlock *PredBB = *PredIt;
//           if (PredBB == SrcBB) {
//             PHI->addIncoming(IV, PredBB);
//           } else {
//             PHI->addIncoming(UndefValue::get(IV->getType()), PredBB);
//           }
//         }
//         Builder.CreateStore(PHI, Addr);
//       } else {
//         for (auto SuccIt = succ_begin(SrcBB), SuccE = succ_end(SrcBB);
//              SuccIt != SuccE; SuccIt++) {
//           BasicBlock *DestBB = *SuccIt;

//           Builder.SetInsertPoint(&*DestBB->getFirstInsertionPt());
//           // create PHI
//           PHINode *PHI = Builder.CreatePHI(IV->getType(), 0);
//           for (auto PredIt = pred_begin(DestBB), PredE = pred_end(DestBB);
//                PredIt != PredE; PredIt++) {
//             BasicBlock *PredBB = *PredIt;
//             if (PredBB == SrcBB) {
//               PHI->addIncoming(IV, PredBB);
//             } else {
//               PHI->addIncoming(UndefValue::get(IV->getType()), PredBB);
//             }
//           }
//           Builder.CreateStore(PHI, Addr);
//         }
//       }
//     } else {
//       Instruction *LastI = nullptr;
//       Instruction *InsertPt = nullptr;
//       for (Instruction &I : *IV->getParent()) {
//         InsertPt = &I;
//         if (LastI == IV)
//           break;
//         LastI = &I;
//       }
//       if (isa<PHINode>(InsertPt) || isa<LandingPadInst>(InsertPt)) {
//         // Builder.SetInsertPoint(&*IV->getParent()->getFirstInsertionPt());
//         Builder.SetInsertPoint(IV->getParent()->getTerminator());
//       } else
//         Builder.SetInsertPoint(InsertPt);

//       Builder.CreateStore(IV, Addr);
//     }
//   };

//   auto MemfyInst = [&](std::set<Instruction *> &InstSet) -> AllocaInst * {
//     if (InstSet.empty())
//       return nullptr;
//     IRBuilder<> Builder(&*NewFuncRoot->getFirstInsertionPt());
//     AllocaInst *Addr = Builder.CreateAlloca((*InstSet.begin())->getType());

//     for (Instruction *I : InstSet) {
//       for (auto UIt = I->use_begin(), E = I->use_end(); UIt != E;) {
//         Use &UI = *UIt;
//         UIt++;

//         Instruction *User = cast<Instruction>(UI.getUser());

//         if (PHINode *PHI = dyn_cast<PHINode>(User)) {
//           /// TODO: make sure getOperandNo is getting the correct incoming edge
//           IRBuilder<> Builder(
//               PHI->getIncomingBlock(UI.getOperandNo())->getTerminator());
//           UI.set(Builder.CreateLoad(Addr));
//         } else {
//           IRBuilder<> Builder(User);
//           UI.set(Builder.CreateLoad(Addr));
//         }
//       }
//     }

//     for (Instruction *I : InstSet)
//       StoreInstIntoAddr(I, Addr);

//     return Addr;
//   };

//   // start fix
//   std::set<Instruction *> Visited;
//   for (Instruction *I : LinearOffendingInsts) {
//     if (Visited.find(I) != Visited.end())
//       continue;

//     std::set<Instruction *> InstSet;
//     InstSet.insert(I);

//     // Create a coalescing group in InstSet
//     // if (EnableSALSSACoalescing)
//     //   OptimizeCoalescing(I, InstSet, CoalescingCandidates, Visited);

//     for (Instruction *OtherI : InstSet)
//       Visited.insert(OtherI);

//     AllocaInst *Addr = MemfyInst(InstSet);
//     if (Addr)
//       Allocas.push_back(Addr);
//   }

//   DominatorTree NDT(*NewFunction);
//   PromoteMemToReg(Allocas, NDT, nullptr);

//   //lzc修改

//   // if (verifyFunction(*NewFunction)) {
//   //   errs() << "ERROR: Produced Broken Function!\n";
//   //   // assert(false);
//   //   return false;
//   // }

//   postProcessFunction(*NewFunction);

//   // if (Debug) {
//   //   raw_fd_ostream *FS = getOutputStreamOfFile(
//   //       "/home/kp4/SWH/llvm-code-size/build-test/log/MergedFunc" +
//   //       to_string(CreatedMergedFunctionNum - 1) + ".log");
//   //   *FS << *NewFunction << "\n";
//   //   delete FS;
//   // }

//   return true;
// }

unsigned MachineRegionAbstractManager::printMIR() {
  unsigned TotalInstrNums = 0;
  raw_ostream &OS = dbgs();
  OS << "打印MIR\n";
   for (Function &F : M)
   {
    if (F.empty())
      continue;

    MachineFunction *MF = MMI.getMachineFunction(F);
    if (!MF)
      continue;
    MF->dump();
    TotalInstrNums += MF->getInstructionCount();
   }
   return TotalInstrNums;
}

//自定义打印MIR中MF的MIs
static void printMFCustomMIR(const MachineFunction &MF, raw_ostream &OS) {
  OS << "body:             |\n";

  for (const MachineBasicBlock &MBB : MF) {
    OS << "  " << MBB.getFullName() << ":\n";

    // Print live-ins
    if (!MBB.livein_empty()) {
      OS << "    liveins:";
      for (const auto &LI : MBB.liveins()) {
        OS << " $" << printReg(LI.PhysReg, MF.getRegInfo().getTargetRegisterInfo());
      }
      OS << "\n";
    }

    // Print instructions
    for (const MachineInstr &MI : MBB) {
      OS << "    " << MI;
    }
  }
}

//自定义打印MIR中Module的MIs
static void printCustomMIR(Module &M, MachineModuleInfo &MMI){
    for (Function &F : M)
   {
    if (F.empty())
      continue;
    MachineFunction *MF = MMI.getMachineFunction(F);
    //printMFCustomMIR(*MF,dbgs());
    MF->dump();
   }
}

// TargetInstrInfo MachineRegionAbstractManager::getCurrentModuleTII(){
//   // if (M.empty())
//   //   return NULL;
//   MachineFunction *MF = 
//   const TargetSubtargetInfo &STI = M.getSubtarget();
//   const TargetInstrInfo &TII = *STI.getInstrInfo();
// }

unsigned getTotalInstrNums(const Module &M, const MachineModuleInfo &MMI){
  unsigned TotalInstrNums = 0;
  for (const Function &F : M) {
    MachineFunction *MF = MMI.getMachineFunction(F);

    // We only care about MI counts here. If there's no MachineFunction at this
    // point, then there won't be after the outliner runs, so let's move on.
    if (!MF)
      continue;
    TotalInstrNums += MF->getInstructionCount();
    //FunctionToInstrCount[F.getName().str()] = MF->getInstructionCount();
  }
  return TotalInstrNums;
}

bool MachineRegionAbstract::runOnModule(Module &M) {
  // Check if there's anything in the module. If it's empty, then there's
  // nothing to outline.
  if (M.empty())
    return false;

  MachineModuleInfo &MMI = getAnalysis<MachineModuleInfoWrapperPass>().getMMI();

  llvm::outs() << getTotalInstrNums(M,MMI);

  // Number to append to the current outlined function.
  unsigned OutlinedFunctionNum = 0;

  std::vector<MachineFunction> FunctionsToProcess;

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

  //打印MIR
  //print(dbgs(),"打印MIR");
  std::cout << "打印MIR" << std::endl;
  //printMIR(dbgs(),M);
  printCustomMIR(M,MMI);

  // if (MRARegisterRename.getValue()) {
  //   InstructionMapper<MachineInstrExpressionSimilarIgnoringRegisterNameTrait> Mapper;
  // } else {
  //   InstructionMapper<MachineInstrExpressionSimilarTrait> Mapper;
  // }

  InstructionMapper Mapper(MRARegisterRename.getValue());

  // Prepare instruction mappings for the suffix tree.
  populateMapper(Mapper, M, MMI);

  std::vector<unsigned> TestTree;
  TestTree.insert(TestTree.end(), Mapper.UnsignedVec.begin(), Mapper.UnsignedVec.end());
  SuffixTree ST(TestTree);

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
    //testElimateInterOverlap(NewRSList, StrMap);
  }

  unsigned NewTotalBenefit = 0;
  std::for_each(NewRSList.begin(), NewRSList.end(),
                [&NewTotalBenefit](RepeatedInfos::RepeatedSubstringByS *RS) {
                  NewTotalBenefit += RS->getPredictBenefit(CreateFuncOverHead);
                });

  // lzc,todo,可以更为精细？延迟到后续阶段剔除
  // 加入对冗余尾指令为跳转的剔除（后缀树层面）
  // 会影响评估收益，是否影响实际收益？
  RepeatedInfos::eliminateJumpEndStr(JumpOpds,NewRSList,Mapper.UnsignedVec);

    // #ifdef ANALYSIS_TREE_DEBUG
  // unsigned TotalBenefit = analysisOld(ST, RepeatedLowerLimit);
  unsigned TotalBenefit =
      RepeatedInfos::analysisOld(ST, RepeatedLowerLimit, CreateFuncOverHead);

  //unsigned NewTotalBenefit = 0;
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
  }

  if (RAStopAfter.getValue() == 2) {
    return false;
  }


  MachineRegionAbstractManager *MRAM = new MachineRegionAbstractManager(M,MMI,Mapper);
  bool NeedMerge = false;
  if (RAGetAndMerge.getValue()) {
    NeedMerge = MRAM->getAndMergeCandidateList(NewRSList, Mapper.InstrList, *this);
  } else {
    NeedMerge = MRAM->getCandidateList(NewRSList, Mapper.InstrList, *this);
  }



  #ifdef RA_TIME_STEPS_DEBUG
    RATimeGetCandidates.stopTimer();
    RATimeMergeCandidate.startTimer();
  #endif

  //MRAM->Mapper = Mapper;
    if (NeedMerge)
      MRAM->mergeCandidateList();
      MRAM->printMIR();
      MRAM->eraseSourceRegion();
  MRAM->printMIR();
  llvm::outs() << getTotalInstrNums(M,MMI);
  return true;

}