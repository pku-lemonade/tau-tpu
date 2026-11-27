//===- Route.cpp - the tau-route pass -------------------------------------===//
//
// Gives every travelling word a stream of the machine: a direction and a
// number. `tau-schedule` gave each word a stream of its own, on a machine
// widened to have enough of them; this pass fits the words onto the streams
// the machine has (`tau.streams`) and puts the machine back as it was.
//
// The direction is forced. A word is on one stream, and every slice it
// passes may read it (Machine 3.2). So it goes east if the instructions that
// use it are at its own position or a higher one, and west if they are at a
// lower one. The pass fails if they lie on both sides.
//
// For the number, think of a stream not as a row of fixed slots but as a row
// of slots that move, one position per cycle. A word placed at position p on
// cycle t going east sits in the moving slot numbered p - t, and stays in it
// until it leaves the machine. Going west the slot is p + t. Two words on the
// same stream can only interfere if they are in the same moving slot. So the
// pass gives two words the same stream number only if their moving slots
// differ.
//
// The pass fails if a word needs a stream number the machine does not have.
//
// Nothing here is proved. `tau-check scheduled.json routed.json` decides
// whether the routed program issues what the scheduled one issues, on the
// same cycles.
//
//===----------------------------------------------------------------------===//

#include "tau/Machine.h"
#include "tau/OpUtils.h"
#include "tau/Passes.h"

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
    Expected<tau::Machine> machine = tau::machineOf(func);
    if (!machine) {
      func.emitError(toString(machine.takeError()));
      return signalPassFailure();
    }
    auto own = func->getAttrOfType<IntegerAttr>("tau.streams");
    if (!own) {
      func.emitError("run tau-schedule before tau-route");
      return signalPassFailure();
    }
    machine->streams = static_cast<int>(own.getInt());
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
      int64_t from = tau::intAttr(op, "slice");
      std::optional<bool> direction = tau::goesEast(op);
      if (!direction) {
        op.emitError("the instructions that use this word lie on both sides "
                     "of the slice that issues it");
        return signalPassFailure();
      }
      bool east = *direction;
      int delay = machine->delayOf(static_cast<int>(from), tau::delayName(op));
      int64_t land = *time + delay + 1;
      int64_t slot = east ? from - land : from + land;

      std::set<int64_t> &numbers = taken[{east, slot}];
      int64_t stream = 0;
      while (numbers.count(stream))
        ++stream;
      if (stream >= machine->streams) {
        op.emitError("the machine has too few streams for this program");
        return signalPassFailure();
      }
      numbers.insert(stream);

      op.setAttr("east", builder.getBoolAttr(east));
      tau::setIntAttr(op, "stream", stream);
    }

    tau::setMachine(func, *machine);
    func->removeAttr("tau.streams");
  }
};

} // namespace

std::unique_ptr<Pass> tau::createRoutePass() {
  return std::make_unique<RoutePass>();
}
