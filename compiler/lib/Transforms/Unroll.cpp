//===- Unroll.cpp - the tau-unroll pass -----------------------------------===//
//
// Replaces every `tau.for` by one copy of its body per iteration, with the
// iteration filled into each position: `[base, stride]` becomes
// `[base + stride * k, 0]` in copy number k.
//
// Tau/Passes/Unroll.lean is a copy of this pass in Lean, and
// Tau/Proofs/Passes/Unroll.lean proves the copy keeps what a kernel
// computes. This C++ code is not proved. Its output is checked on every
// compile by tau-check, and compared with the copy's by
// scripts/check-examples.sh.
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
#include "tau/Transforms/Passes.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/IRMapping.h"
#include "mlir/Pass/Pass.h"

using namespace mlir;

namespace {

/// Fix the iteration of one operation to `k`.
template <typename OpT>
static void instantiate(OpT op, uint64_t k) {
  op.setBase(op.getBase() + op.getStride() * k);
  op.setStride(0);
}

static void instantiate(Operation *op, uint64_t k) {
  if (auto load = dyn_cast<tau::LoadOp>(op))
    instantiate(load, k);
  else if (auto store = dyn_cast<tau::StoreOp>(op))
    instantiate(store, k);
  else if (auto matvec = dyn_cast<tau::MatVecOp>(op))
    instantiate(matvec, k);
  else if (auto affine = dyn_cast<tau::AffineOp>(op))
    instantiate(affine, k);
}

struct UnrollPass : PassWrapper<UnrollPass, OperationPass<func::FuncOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(UnrollPass)

  StringRef getArgument() const final { return "tau-unroll"; }
  StringRef getDescription() const final {
    return "Replace every tau.for by copies of its body";
  }

  void runOnOperation() override {
    SmallVector<tau::ForOp> loops;
    getOperation().walk([&](tau::ForOp loop) { loops.push_back(loop); });

    for (tau::ForOp loop : loops) {
      if (isa<tau::ForOp>(loop->getParentOp())) {
        loop.emitError("tau.for must not be nested");
        return signalPassFailure();
      }
      OpBuilder builder(loop);
      for (uint64_t k = 0, n = loop.getN(); k < n; ++k) {
        IRMapping mapping;
        for (Operation &op : loop.getBody().front()) {
          if (isa<tau::ForOp>(op)) {
            op.emitError("tau.for must not be nested");
            return signalPassFailure();
          }
          instantiate(builder.clone(op, mapping), k);
        }
      }
      loop.erase();
    }
  }
};

} // namespace

std::unique_ptr<Pass> tau::createUnrollPass() {
  return std::make_unique<UnrollPass>();
}
