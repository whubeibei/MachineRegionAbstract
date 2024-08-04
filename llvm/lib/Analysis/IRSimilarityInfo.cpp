#include "llvm/Analysis/IRSimilarityInfo.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/User.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/SuffixTree.h"

using namespace llvm;

static cl::opt<unsigned> InstrEquivalenceMode(
    "instr-equivalence-mode", cl::init(0), cl::Hidden,
    cl::desc("Modes that determines whether two instructions are equal"));

using namespace IRSimilarity;

InstrData::InstrData(Instruction &I, bool Legality,
                     IRSimilarity::IRInstructionDataList &IDL,
                     short CompareType)
    : IRInstructionData(I, Legality, IDL), IDType(CompareType) {
  // only the super function IRInstructionData run when CompareType=0
  if (IDType == 1) {
    if (RevisedPredicate) {
      RevisedPredicate = predicateForConsistency(dyn_cast<CmpInst>(&I));
    }
  }
}

InstrData::InstrData(short InstrType, Function *DelimiterOfFunction)
    : IRInstructionData(false), IDType(InstrType) {
  Delimiter.DelimiterOfFunc = DelimiterOfFunction;
}

InstrData::InstrData(short InstrType, BasicBlock *DelimiterOfBasicBlock)
    : IRInstructionData(false), IDType(InstrType) {
  Delimiter.DelimiterOfBB = DelimiterOfBasicBlock;
}

CmpInst::Predicate InstrData::predicateForConsistency(CmpInst *CI) {
  switch (CI->getPredicate()) {
  case CmpInst::FCMP_OGT:
    return CmpInst::FCMP_OLE;
  case CmpInst::FCMP_UGT:
    return CmpInst::FCMP_ULE;
  case CmpInst::FCMP_OGE:
    return CmpInst::FCMP_OLT;
  case CmpInst::FCMP_UGE:
    return CmpInst::FCMP_ULT;
  case CmpInst::ICMP_SGT:
    return CmpInst::ICMP_SLE;
  case CmpInst::ICMP_UGT:
    return CmpInst::ICMP_ULE;
  case CmpInst::ICMP_SGE:
    return CmpInst::ICMP_SLT;
  case CmpInst::ICMP_UGE:
    return CmpInst::ICMP_ULT;
  default:
    return CI->getPredicate();
  }
}

void IRInstrMapper::populateMapperForRA(
    Module &M, std::vector<FunctionData> &FunctionsToProcess,
    std::vector<InstrData *> &InstrList,
    std::vector<unsigned> &IntegerMapping) {
  //先定义好function分隔符的下限，凡是对应值大于此下限的都是函数分隔符；
  FuncDelimiterLowerLimit = FuncDelimiterNumber - FunctionsToProcess.size();

  // All params are reference for we need to insert some data into them;
  for (FunctionData &FD : FunctionsToProcess) {
    Function &F = *FD.F;
    for (BasicBlock &BB : F) {
      std::vector<unsigned> IntegerMappingForBB;
      std::vector<InstrData *> InstrListForBB;
      for (Instruction &I : BB) {
        if (isa<LandingPadInst>(&I))
          continue;
        if (InstrEquivalenceMode == 0) {
          InstrData *ID = new InstrData(I, true, *IDL, 1);
          InstrListForBB.push_back(ID);
          // Add to the instruction list
          bool WasInserted;
          // DenseMap<IRInstructionData *, unsigned,
          //          IRInstructionDataTraits>::iterator ResultIt;
          // SWH:InstrDataTraits
          DenseMap<InstrData *, unsigned, InstrDataTraits>::iterator ResultIt;
          std::tie(ResultIt, WasInserted) = InstructionIntegerMap.insert(
              std::make_pair(ID, NormalInstrNumber));
          unsigned INumber = ResultIt->second;
          // There was an insertion.
          if (WasInserted)
            NormalInstrNumber++;
          IntegerMappingForBB.push_back(INumber);

          assert(NormalInstrNumber < FuncDelimiterNumber &&
                 "Instruction mapping overflow!");
          assert(NormalInstrNumber != DenseMapInfo<unsigned>::getEmptyKey() &&
                 "Tried to assign DenseMap tombstone or empty key to "
                 "instruction.");
          assert(NormalInstrNumber !=
                     DenseMapInfo<unsigned>::getTombstoneKey() &&
                 "Tried to assign DenseMap tombstone or empty key to "
                 "instruction.");
        }
        TotalInsts++;
      }
      llvm::append_range(InstrList, InstrListForBB);
      llvm::append_range(IntegerMapping, IntegerMappingForBB);
    }
    // Function之间不可能被连接在一起；因此每个Function之间都插入一个特殊值（每个function不同），保证不会被识别为相同
    //同理，每个region之间，每个block之间也应该考虑此值
    //
    InstrList.push_back(new InstrData(-1, FD.F));
    IntegerMapping.push_back(FuncDelimiterNumber--);
  }
}

void IRInstrMapper::populateFunctionDFS(
    Function &F, std::vector<InstrData *> &InstrList,
    std::vector<unsigned int> &IntegerMapping) {

  FuncDelimiterLowerLimit = FuncDelimiterNumber;
  NormalUpperLimit = FuncDelimiterLowerLimit;

  DenseSet<BasicBlock *> BBsTraversed;
  std::vector<BasicBlock *> BBStack;
  BBStack.push_back(&F.getEntryBlock());
  while (!BBStack.empty()) {
    BasicBlock *BB = BBStack.back();
    BBStack.pop_back();
    if (BBsTraversed.contains(BB)) {
      InstrList.push_back(new InstrData(-2, BB));
      IntegerMapping.push_back(NormalUpperLimit--);
      continue;
    }

    std::vector<unsigned> IntegerMappingForBB;
    std::vector<InstrData *> InstrListForBB;

    for (Instruction &I : *BB) {
      if (isa<LandingPadInst>(&I))
        continue;
      if (InstrEquivalenceMode == 0) {
        InstrData *ID = new InstrData(I, true, *IDL, 1);
        InstrListForBB.push_back(ID);
        // Add to the instruction list
        bool WasInserted;

        // SWH: repleased by InstrData and InstrDataTraits
        DenseMap<InstrData *, unsigned, InstrDataTraits>::iterator ResultIt;
        std::tie(ResultIt, WasInserted) =
            InstructionIntegerMap.insert(std::make_pair(ID, NormalInstrNumber));
        unsigned INumber = ResultIt->second;
        // There was an insertion.
        if (WasInserted)
          NormalInstrNumber++;
        IntegerMappingForBB.push_back(INumber);

        assert(NormalInstrNumber < NormalUpperLimit &&
               "Instruction mapping overflow!");
        assert(NormalInstrNumber != DenseMapInfo<unsigned>::getEmptyKey() &&
               "Tried to assign DenseMap tombstone or empty key to "
               "instruction.");
        assert(NormalInstrNumber != DenseMapInfo<unsigned>::getTombstoneKey() &&
               "Tried to assign DenseMap tombstone or empty key to "
               "instruction.");
      }
      TotalInsts++;
    }
    llvm::append_range(InstrList, InstrListForBB);
    llvm::append_range(IntegerMapping, IntegerMappingForBB);

    //处理完成后记录
    BBsTraversed.insert(BB);
    //把所有子节点压入栈内,如果没有子节点，则这一直链结束，需要插入分隔符，即一个特殊值
    if (succ_size(BB) == 0) {
      // TODO:
      InstrList.push_back(new InstrData(-2, BB));
      IntegerMapping.push_back(NormalUpperLimit--);
      continue;
    }
    for (BasicBlock *Succ : reverse(successors(BB))) {
      BBStack.push_back(Succ);
    }
  }
}

// #define MAPPER_DEBUG
void IRInstrMapper::populateDFSMapperForRA(
    Module &M, std::vector<FunctionData> &FunctionsToProcess,
    std::vector<InstrData *> &InstrList,
    std::vector<unsigned> &IntegerMapping) {
  //先定义好function分隔符的下限，凡是对应值大于此下限的都是函数分隔符；
  FuncDelimiterLowerLimit = FuncDelimiterNumber - FunctionsToProcess.size();
  // NormalUpperLimit是因为还有DFS造成的分隔符，数目无法确定
  NormalUpperLimit = FuncDelimiterLowerLimit;

  // All params are reference for we need to insert some data into them;
  for (FunctionData &FD : FunctionsToProcess) {
    Function &F = *FD.F;
    DenseSet<BasicBlock *> BBsTraversed;
    std::vector<BasicBlock *> BBStack;
    BBStack.push_back(&F.getEntryBlock());
    while (!BBStack.empty()) {
      BasicBlock *BB = BBStack.back();
      BBStack.pop_back();
      if (BBsTraversed.contains(BB)) {
        InstrList.push_back(new InstrData(-2, BB));
        IntegerMapping.push_back(NormalUpperLimit--);
        continue;
      }

      std::vector<unsigned> IntegerMappingForBB;
      std::vector<InstrData *> InstrListForBB;

      for (Instruction &I : *BB) {
        if (isa<LandingPadInst>(&I))
          continue;
        if (InstrEquivalenceMode == 0) {
          InstrData *ID = new InstrData(I, true, *IDL, 1);
          InstrListForBB.push_back(ID);
          // Add to the instruction list
          bool WasInserted;
          // DenseMap<IRInstructionData *, unsigned,
          //          IRInstructionDataTraits>::iterator ResultIt;

          // SWH: repleased by InstrData and InstrDataTraits
          DenseMap<InstrData *, unsigned, InstrDataTraits>::iterator ResultIt;
          std::tie(ResultIt, WasInserted) = InstructionIntegerMap.insert(
              std::make_pair(ID, NormalInstrNumber));
          unsigned INumber = ResultIt->second;
          // There was an insertion.
          if (WasInserted)
            NormalInstrNumber++;
          IntegerMappingForBB.push_back(INumber);

          assert(NormalInstrNumber < NormalUpperLimit &&
                 "Instruction mapping overflow!");
          assert(NormalInstrNumber != DenseMapInfo<unsigned>::getEmptyKey() &&
                 "Tried to assign DenseMap tombstone or empty key to "
                 "instruction.");
          assert(NormalInstrNumber !=
                     DenseMapInfo<unsigned>::getTombstoneKey() &&
                 "Tried to assign DenseMap tombstone or empty key to "
                 "instruction.");
        }
        TotalInsts++;
      }
      llvm::append_range(InstrList, InstrListForBB);
      llvm::append_range(IntegerMapping, IntegerMappingForBB);

      //处理完成后记录
      BBsTraversed.insert(BB);
      //把所有子节点压入栈内,如果没有子节点，则这一直链结束，需要插入分隔符，即一个特殊值
      if (succ_size(BB) == 0) {
        // TODO:
        InstrList.push_back(new InstrData(-2, BB));
        IntegerMapping.push_back(NormalUpperLimit--);
        continue;
      }
      for (BasicBlock *Succ : reverse(successors(BB))) {
        BBStack.push_back(Succ);
      }
    }
    // Function之间不可能被连接在一起；因此每个Function之间都插入一个特殊值（每个function不同），保证不会被识别为相同
    //同理，每个region之间，每个block之间也应该考虑此值
    InstrList.push_back(new InstrData(-1, FD.F));
    IntegerMapping.push_back(FuncDelimiterNumber--);
  }
}
