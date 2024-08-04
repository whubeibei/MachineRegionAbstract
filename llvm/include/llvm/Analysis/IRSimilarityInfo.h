#include "llvm/Analysis/IRSimilarityIdentifier.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/ScopedPrinter.h"
#include <vector>

#ifndef LLVM_ANALYSIS_IR_SIMILARITY_INFO_H
#define LLVM_ANALYSIS_IR_SIMILARITY_INFO_H

namespace llvm {
namespace IRSimilarity {

struct InstrData : IRInstructionData {
public:
  // 正数表示compareType
  // 负数表示InstrType, -1 FuncDelimiter -2 BlockDelimiter ...
  short IDType;
  union SequenceDelimiter {
    Function *DelimiterOfFunc;
    BasicBlock *DelimiterOfBB;
  } Delimiter;

  InstrData(Instruction &I, bool Legality,
            IRSimilarity::IRInstructionDataList &IDL, short CompareType);

  InstrData(short InstrType, Function *DelimiterOfFunction);
  InstrData(short InstrType, BasicBlock *DelimiterOfBasicBlock);

  friend hash_code hash_value(const InstrData &ID) {
    SmallVector<Type *, 4> OperTypes;
    for (Value *V : ID.OperVals)
      OperTypes.push_back(V->getType());

    if (isa<CmpInst>(ID.Inst))
      return llvm::hash_combine(
          llvm::hash_value(ID.Inst->getOpcode()),
          llvm::hash_value(ID.Inst->getType()),
          llvm::hash_value(ID.getPredicate()),
          llvm::hash_combine_range(OperTypes.begin(), OperTypes.end()));
    if (isa<OverflowingBinaryOperator>(ID.Inst)) {
      return llvm::hash_combine(
          llvm::hash_value(ID.Inst->getOpcode()),
          llvm::hash_value(ID.Inst->getType()),
          llvm::hash_value(ID.Inst->hasNoUnsignedWrap()),
          llvm::hash_value(ID.Inst->hasNoSignedWrap()),
          llvm::hash_combine_range(OperTypes.begin(), OperTypes.end()));
    }
    switch (ID.Inst->getOpcode()) {

    case Instruction::Load: {
      LoadInst *I = dyn_cast<LoadInst>(ID.Inst);
      return llvm::hash_combine(
          llvm::hash_value(I->getOpcode()), llvm::hash_value(I->getType()),
          llvm::hash_value(I->isVolatile()),
          llvm::hash_value(I->getAlignment()),
          llvm::hash_value(I->getOrdering()),
          llvm::hash_combine_range(OperTypes.begin(), OperTypes.end()));
    }
    case Instruction::GetElementPtr: {
      GetElementPtrInst *I = dyn_cast<GetElementPtrInst>(ID.Inst);
      Type *Ty = I->getSourceElementType();
      SmallVector<Value *, 16> Idxs(I->idx_begin(), I->idx_end());
      hash_code TmpHash = llvm::hash_combine(
          llvm::hash_value(ID.Inst->getOpcode()),
          llvm::hash_value(ID.Inst->getType()), llvm::hash_value(Ty),
          llvm::hash_value(Idxs.size()),
          llvm::hash_combine_range(OperTypes.begin(), OperTypes.end()));

      SmallVector<Value *, 16> Types;
      for (unsigned i = 1; i < Idxs.size(); i++) {
        Value *V = Idxs[i];
        if (isa<StructType>(Ty)) {
          TmpHash = llvm::hash_combine(TmpHash, llvm::hash_value(V));
        }
        Ty = GetElementPtrInst::getTypeAtIndex(Ty, V);
        TmpHash = llvm::hash_combine(TmpHash, llvm::hash_value(Ty));
      }
      return TmpHash;
    }
    case Instruction::Switch: {
      const SwitchInst *I = dyn_cast<SwitchInst>(ID.Inst);
      SmallVector<std::string, 4> CaseStrList;
      auto CaseIt = I->case_begin(), CaseEnd = I->case_end();
      do {
        CaseStrList.push_back(to_string(CaseIt->getCaseIndex()) +
                              to_string(*CaseIt->getCaseValue()) +
                              to_string(CaseIt->getCaseSuccessor()));
        ++CaseIt;
      } while (CaseIt != CaseEnd);
      return llvm::hash_combine(
          llvm::hash_value(I->getOpcode()), llvm::hash_value(I->getType()),
          llvm::hash_value(I->getNumCases()),
          llvm::hash_combine_range(CaseStrList.begin(), CaseStrList.end()),
          llvm::hash_combine_range(OperTypes.begin(), OperTypes.end()));
    }
    case Instruction::Call: {
      CallInst *CI = dyn_cast<CallInst>(ID.Inst);
      if (CI->getCalledFunction() != nullptr) {
        return llvm::hash_combine(
            llvm::hash_value(ID.Inst->getOpcode()),
            llvm::hash_value(ID.Inst->getType()), llvm::hash_value(true),
            llvm::hash_value(CI->getCalledFunction()->getName().str()),
            llvm::hash_value(CI->getNumArgOperands()),
            llvm::hash_value(CI->getCallingConv()),
            llvm::hash_combine(CI->getAttributes().begin(),
                               CI->getAttributes().end()),
            llvm::hash_combine_range(OperTypes.begin(), OperTypes.end()));
      }
      return llvm::hash_combine(
          llvm::hash_value(ID.Inst->getOpcode()),
          llvm::hash_value(ID.Inst->getType()), llvm::hash_value(false),
          llvm::hash_value(CI->getNumArgOperands()),
          llvm::hash_value(CI->getCallingConv()),
          llvm::hash_combine(CI->getAttributes().begin(),
                             CI->getAttributes().end()),
          llvm::hash_combine_range(OperTypes.begin(), OperTypes.end()));

      // TODO
    }
    default:
      if (isa<PossiblyExactOperator>(ID.Inst)) {
        if (ID.Inst->isExact())
          return llvm::hash_combine(
              llvm::hash_value(ID.Inst->getOpcode()),
              llvm::hash_value(ID.Inst->getType()),
              llvm::hash_combine_range(OperTypes.begin(), OperTypes.end()),
              llvm::hash_value(true));
      }
      return llvm::hash_combine(
          llvm::hash_value(ID.Inst->getOpcode()),
          llvm::hash_value(ID.Inst->getType()),
          llvm::hash_combine_range(OperTypes.begin(), OperTypes.end()),
          llvm::hash_value(false) // is exact
      );
    };
  }

  static CmpInst::Predicate predicateForConsistency(CmpInst *CI);
};

struct InstrDataTraits : DenseMapInfo<InstrData *> {
  static inline InstrData *getEmptyKey() { return nullptr; }
  static inline InstrData *getTombstoneKey() {
    return reinterpret_cast<InstrData *>(-1);
  }

  static unsigned getHashValue(const InstrData *E) {
    using llvm::hash_value;
    assert(E && "InstrData is a nullptr?");
    return hash_value(*E);
  }

  static bool isEqual(const InstrData *LHS, const InstrData *RHS) {
    if (RHS == getEmptyKey() || RHS == getTombstoneKey() ||
        LHS == getEmptyKey() || LHS == getTombstoneKey())
      return LHS == RHS;

    assert(LHS && RHS && "nullptr should have been caught by getEmptyKey?");
    if (!LHS->Legal || !RHS->Legal)
      return false;

    return getHashValue(LHS) == getHashValue(RHS);
  }
};

class Fingerprint {
public:
  static const size_t MaxOpcode = 68;
  int OpcodeFreq[MaxOpcode];
  Function *F;
  BasicBlock *BB;

  Fingerprint() : F(nullptr), BB(nullptr) {}

  Fingerprint(Function *F) : F(F), BB(nullptr) {
    // memset(OpcodeFreq, 0, sizeof(int) * MaxOpcode);
    for (size_t i = 0; i < MaxOpcode; i++)
      OpcodeFreq[i] = 0;

    for (Instruction &I : instructions(F)) {
      OpcodeFreq[I.getOpcode()]++;
      if (I.isTerminator())
        OpcodeFreq[0] += I.getNumSuccessors();
    }
  }

  Fingerprint(BasicBlock *BB) : F(BB->getParent()), BB(BB) {
    // memset(OpcodeFreq, 0, sizeof(int) * MaxOpcode);
    for (size_t i = 0; i < MaxOpcode; i++)
      OpcodeFreq[i] = 0;

    // NumOfInstructions = 0;
    for (Instruction &I : *BB) {
      OpcodeFreq[I.getOpcode()]++;
      if (I.isTerminator())
        OpcodeFreq[0] += I.getNumSuccessors();
    }
  }

  class Distances {
  public:
    static int manhattan(Fingerprint *FP1, Fingerprint *FP2) {
      int Distance = 0;
      for (size_t i = 0; i < Fingerprint::MaxOpcode; i++) {
        int Freq1 = FP1->OpcodeFreq[i];
        int Freq2 = FP2->OpcodeFreq[i];
        Distance += std::abs(Freq1 - Freq2);
      }
      return Distance;
    }

    static float euclidean(Fingerprint *FP1, Fingerprint *FP2) {
      int Sum = 0;
      for (size_t i = 0; i < Fingerprint::MaxOpcode; i++) {
        int Freq1 = FP1->OpcodeFreq[i];
        int Freq2 = FP2->OpcodeFreq[i];
        int Sub = Freq1 - Freq2;
        Sum += Sub * Sub;
      }
      float Distance = std::sqrt((float)Sum);
      return Distance;
    }

    static float cosine(Fingerprint *FP1, Fingerprint *FP2) {
      int AB = 0;
      int A2 = 0;
      int B2 = 0;
      for (size_t i = 0; i < Fingerprint::MaxOpcode; i++) {
        int Freq1 = FP1->OpcodeFreq[i];
        int Freq2 = FP2->OpcodeFreq[i];
        AB += Freq1 * Freq2;
        A2 += Freq1 * Freq1;
        B2 += Freq2 * Freq2;
      }
      float Similarity =
          ((float)AB) / (std::sqrt((float)A2) * std::sqrt((float)B2));
      float Distance = 1.f - Similarity;
      return Distance;
    }
  };
};

class FunctionData {
public:
  Function *F;
  Fingerprint *FP;
  size_t Size;
  int Distance;
  std::list<FunctionData>::iterator iterator;

  FunctionData() : F(nullptr), FP(nullptr), Size(0), Distance(0) {}
  FunctionData(Function *F, size_t Size) : F(F), Size(Size), Distance(0) {
    FP = new Fingerprint(F);
  }

  FunctionData(Function *F, Fingerprint *FP, size_t Size)
      : F(F), FP(FP), Size(Size), Distance(0) {}
};

struct IRInstrMapper {

  llvm::IRSimilarity::IRInstructionDataList *IDL = nullptr;
  /// The next available integer to assign to a Instruction to.
  unsigned NormalInstrNumber = 0;
  /// The next available integer to assign to a function delimiter to.
  unsigned FuncDelimiterNumber = UINT_MAX - 3;
  // FuncDelimiterLowerLimit equals to FuncDelimiterNumber - FunctionTotalNumber
  unsigned FuncDelimiterLowerLimit;
  unsigned NormalUpperLimit;

  /// Correspondence from IRInstructionData to unsigned integers.
  // DenseMap<IRInstructionData *, unsigned, IRInstructionDataTraits>
  //     InstructionIntegerMap;

  // SWH:InstrDataTraits
  DenseMap<InstrData *, unsigned, InstrDataTraits> InstructionIntegerMap;

  int TotalInsts = 0;

  void populateMapperForRA(Module &M,
                           std::vector<FunctionData> &FunctionsToProcess,
                           std::vector<InstrData *> &InstrList,
                           std::vector<unsigned> &IntegerMapping);

  void populateFunctionDFS(Function &F, std::vector<InstrData *> &InstrList,
                           std::vector<unsigned> &IntegerMapping);

  void populateDFSMapperForRA(Module &M,
                              std::vector<FunctionData> &FunctionsToProcess,
                              std::vector<InstrData *> &InstrList,
                              std::vector<unsigned> &IntegerMapping);
};

} // namespace IRSimilarity
} // namespace llvm

#endif // LLVM_ANALYSIS_IR_SIMILARITY_INFO_H