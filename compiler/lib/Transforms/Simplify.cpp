//===- Simplify.cpp - the tau-simplify pass -------------------------------===//
//
// Rewrites that keep the value of every word:
//
//   relu(relu a) -> relu a
//   max(a, a)    -> a
//   min(a, a)    -> a
//
// Tau/Passes/Simplify.lean applies the same rewrites to expressions, and
// Tau/Proofs/Passes/Simplify.lean proves they keep values. This C++ code is
// not proved. Its output is checked on every compile by tau-check.
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
#include "tau/Transforms/Passes.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/PatternMatch.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Transforms/GreedyPatternRewriteDriver.h"

using namespace mlir;

namespace {

struct ReluOfRelu : OpRewritePattern<tau::ReluOp> {
  using OpRewritePattern::OpRewritePattern;

  LogicalResult matchAndRewrite(tau::ReluOp op,
                                PatternRewriter &rewriter) const override {
    auto inner = op.getA().getDefiningOp<tau::ReluOp>();
    if (!inner)
      return failure();
    rewriter.replaceOp(op, inner.getResult());
    return success();
  }
};

template <typename OpT>
struct SameOperands : OpRewritePattern<OpT> {
  using OpRewritePattern<OpT>::OpRewritePattern;

  LogicalResult matchAndRewrite(OpT op,
                                PatternRewriter &rewriter) const override {
    if (op.getA() != op.getB())
      return failure();
    rewriter.replaceOp(op, op.getA());
    return success();
  }
};

struct SimplifyPass : PassWrapper<SimplifyPass, OperationPass<func::FuncOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(SimplifyPass)

  StringRef getArgument() const final { return "tau-simplify"; }
  StringRef getDescription() const final {
    return "Remove repeated relu and max/min of a word with itself";
  }

  void runOnOperation() override {
    RewritePatternSet patterns(&getContext());
    patterns.add<ReluOfRelu, SameOperands<tau::MaxOp>,
                 SameOperands<tau::MinOp>>(&getContext());
    if (failed(applyPatternsGreedily(
            getOperation().getBody(),
            FrozenRewritePatternSet(std::move(patterns)))))
      signalPassFailure();
  }
};

} // namespace

std::unique_ptr<Pass> tau::createSimplifyPass() {
  return std::make_unique<SimplifyPass>();
}
