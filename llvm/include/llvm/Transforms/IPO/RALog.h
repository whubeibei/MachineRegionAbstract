#include "llvm/IR/PassManager.h"

#ifndef LLVM_TRANSFORMS_RA_LOG_H
#define LLVM_TRANSFORMS_RA_LOG_H

namespace llvm {

class RALogPass : public PassInfoMixin<RALogPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_HELLONEW_HELLOWORLD_H