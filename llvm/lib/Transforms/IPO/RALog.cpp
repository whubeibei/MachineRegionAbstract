#include "llvm/Transforms/IPO/RALog.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

static cl::opt<unsigned> SmallFunctionLimit(
    "log-small-func-limit", cl::init(3), cl::Hidden,
    cl::desc("Upper limit of instruction count of small function, default to 3"));

static cl::opt<bool>
    LogEachFuncSize("log-each-func-size", cl::init(false), cl::Hidden,
                    cl::desc("Whether to log each function's size info, default to false"));

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

PreservedAnalyses RALogPass::run(Module &M, ModuleAnalysisManager &AM) {
  TargetTransformInfo TTI(M.getDataLayout());

  std::vector<Function *> FunctionsToProcess;
  // Sum of instruction counts of Small Functions
  unsigned long SmallFuncCount = 0;
  unsigned long SmallFuncTotalInstrCounts = 0;
  unsigned long SmallFuncTotalEstimateSize = 0;
  unsigned long LargeFuncCount = 0;
  unsigned long LargeFuncTotalInstrCounts = 0;
  unsigned long LargeFuncTotalEstimateSize = 0;

  // int FuncNum = 0;
  for (auto &F : M) {
    if (F.isDeclaration() ||
        F.getLinkage() == GlobalValue::AvailableExternallyLinkage) {
      continue;
    }

    // FuncNum++;
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

    if (LogEachFuncSize.getValue())
      errs() << "FNSize: " << F.getName() << " : " << FuncInsrCount << "\n";

    FunctionsToProcess.push_back(&F);
  }

  errs() << ", Count, Instr Count, Estimate Size\n";
  errs() << "Small Function, " 
         << SmallFuncCount << ", " 
         << SmallFuncTotalInstrCounts << ", " 
         << SmallFuncTotalEstimateSize << "\n";
  errs() << "Large Function, " 
         << LargeFuncCount << ", " 
         << LargeFuncTotalInstrCounts << ", "
         << LargeFuncTotalEstimateSize << "\n";
  errs() << "Total, " 
         << LargeFuncCount + SmallFuncCount << ", "
         << LargeFuncTotalInstrCounts + SmallFuncTotalInstrCounts << ", "
         << LargeFuncTotalEstimateSize + SmallFuncTotalEstimateSize << "\n";

  return PreservedAnalyses::all();
}