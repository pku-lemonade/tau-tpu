//===- Route.cpp - the tau-route pass -------------------------------------===//
//
// Gives every travelling word a stream: a direction and a number.
//
// The direction is forced: east if the word's user is at a higher position
// than its producer, west otherwise.
//
// For the number, think of a stream not as a row of fixed slots but as a row
// of slots that move, one position per cycle. A word placed at position p on
// cycle t going east sits in the moving slot numbered p - t, and stays in it
// until it leaves the chip. Going west the slot is p + t. Two words on the
// same stream can only interfere if they are in the same moving slot. So the
// pass gives two words the same stream number only if their moving slots
// differ.
//
// The pass fails if a word needs a stream number the chip does not have.
//
// Nothing here is proved. `tau-check kernel.json compiled.json` decides
// whether the finished program computes what the kernel computes.
//
//===----------------------------------------------------------------------===//

#include "tau/Target/Target.h"
#include "tau/Transforms/Passes.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/Pass/Pass.h"

#include <map>
#include <set>

using namespace llvm;
using namespace mlir;

namespace {

struct RoutePass : PassWrapper<RoutePass, OperationPass<func::FuncOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(RoutePass)

  StringRef getArgument() const final { return "tau-route"; }
  StringRef getDescription() const final {
    return "Give every travelling word a stream";
  }

  void runOnOperation() override {
    func::FuncOp func = getOperation();
    Expected<tau::Chip> chip = tau::chipOf(func);
    if (!chip) {
      func.emitError(toString(chip.takeError()));
      return signalPassFailure();
    }
    Builder builder(func.getContext());

    // For each direction and moving slot, the stream numbers already taken.
    std::map<std::pair<bool, int64_t>, std::set<int64_t>> taken;

    for (Operation &op : func.getBody().front()) {
      if (!tau::isInstr(op))
        continue;
      Value result = tau::streamResult(op);
      if (!result)
        continue;
      std::optional<int64_t> time = tau::optIntAttr(op, "time");
      if (!time) {
        op.emitError("run tau-schedule before tau-route");
        return signalPassFailure();
      }
      if (!result.use_empty() && !result.hasOneUse()) {
        op.emitError("a travelling word has more than one user");
        return signalPassFailure();
      }

      int64_t from = tau::intAttr(op, "slice");
      bool east = true;
      if (!result.use_empty())
        east = tau::intAttr(*result.use_begin()->getOwner(), "slice") >= from;
      int64_t land = *time + chip->delayAt(static_cast<int>(from)) + 1;
      int64_t slot = east ? from - land : from + land;

      std::set<int64_t> &numbers = taken[{east, slot}];
      int64_t stream = 0;
      while (numbers.count(stream))
        ++stream;
      if (stream >= chip->streams) {
        op.emitError("the chip has too few streams for this program");
        return signalPassFailure();
      }
      numbers.insert(stream);

      op.setAttr("east", builder.getBoolAttr(east));
      tau::setIntAttr(op, "stream", stream);
    }
  }
};

} // namespace

std::unique_ptr<Pass> tau::createRoutePass() {
  return std::make_unique<RoutePass>();
}
