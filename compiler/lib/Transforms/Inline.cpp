//===- Inline.cpp - the tau-inline pass -----------------------------------===//
//
// Replaces every `tau.call` by the body of the kernel it calls, and then
// removes every function but the last, which is the program.
//
// In the copy of the body:
//
//   * the kernel's buffers become the buffers the call passes,
//   * every pin `at t` becomes `at t + origin`, where `origin` is the `at`
//     of the call.
//
// A function may only call functions defined before it, so a function has no
// calls left by the time it is copied into another. The pass fails on a call
// inside a `tau.for`, and on a call that passes one buffer twice: the copy
// would then let the kernel see through one buffer what it stored to the
// other, which a called kernel may not do (Tau/IR/Source.lean).
//
// Nothing here is proved. `tau-check source.json kernel.json` decides whether
// the kernel computes what the source program computes and keeps its pins.
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
#include "tau/Transforms/Passes.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/Pass/Pass.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringMap.h"

using namespace mlir;

namespace {

struct InlinePass : PassWrapper<InlinePass, OperationPass<ModuleOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(InlinePass)

  StringRef getArgument() const final { return "tau-inline"; }
  StringRef getDescription() const final {
    return "Replace every tau.call by the body of its kernel";
  }

  void runOnOperation() override {
    ModuleOp module = getOperation();
    std::vector<func::FuncOp> funcs;
    for (func::FuncOp func : module.getOps<func::FuncOp>())
      funcs.push_back(func);
    if (funcs.empty())
      return;

    // The functions that have no calls left, by name.
    llvm::StringMap<func::FuncOp> ready;
    for (func::FuncOp func : funcs) {
      std::vector<tau::CallOp> calls;
      func.walk([&](tau::CallOp call) { calls.push_back(call); });
      for (tau::CallOp call : calls) {
        if (call->getParentOp() != func.getOperation()) {
          call.emitError("tau.call must not be inside a tau.for");
          return signalPassFailure();
        }
        auto found = ready.find(call.getCallee());
        if (found == ready.end()) {
          call.emitError("tau.call of a kernel that is not defined earlier");
          return signalPassFailure();
        }
        func::FuncOp callee = found->second;
        if (callee.getNumArguments() != call.getArgs().size()) {
          call.emitError("tau.call passes the wrong number of buffers");
          return signalPassFailure();
        }
        llvm::SmallPtrSet<void *, 8> seen;
        IRMapping mapping;
        for (auto [param, arg] : llvm::zip(callee.getArguments(),
                                           call.getArgs())) {
          if (param.getType() != arg.getType()) {
            call.emitError("tau.call passes a buffer of the wrong size");
            return signalPassFailure();
          }
          if (!seen.insert(arg.getAsOpaquePointer()).second) {
            call.emitError("tau.call passes one buffer twice");
            return signalPassFailure();
          }
          mapping.map(param, arg);
        }

        int64_t origin = call.getAt().value_or(0);
        OpBuilder builder(call);
        for (Operation &op : callee.getBody().front()) {
          if (isa<func::ReturnOp>(op))
            continue;
          Operation *copy = builder.clone(op, mapping);
          copy->walk([&](Operation *inner) {
            if (auto at = inner->getAttrOfType<IntegerAttr>("at"))
              inner->setAttr("at", IntegerAttr::get(at.getType(),
                                                    at.getInt() + origin));
          });
        }
        call.erase();
      }
      ready[func.getSymName()] = func;
    }

    for (size_t i = 0; i + 1 < funcs.size(); ++i)
      funcs[i].erase();
  }
};

} // namespace

std::unique_ptr<Pass> tau::createInlinePass() {
  return std::make_unique<InlinePass>();
}
