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
// The words of a value are on streams that follow one another, from a number
// that is a multiple of how many they are (Machine 3.5). The words of an
// `install` follow one another too, from any number. Words that an
// instruction takes side by side but
// that different instructions make, such as the reads that bring a value out
// of memory, are in the same moving slot, since they are at one slice on one
// cycle. The pass gives each such run its numbers first, the lowest free run
// that starts where it may, then each result its lowest free run.
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
#include "llvm/ADT/DenseSet.h"

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
    bool failed = false;

    // The direction and the moving slot of the word of `op`.
    auto slotOf = [&](Operation &op) -> std::optional<std::pair<bool, int64_t>> {
      std::optional<int64_t> time = tau::optIntAttr(op, "time");
      if (!time) {
        op.emitError("run tau-schedule before tau-route");
        failed = true;
        return std::nullopt;
      }
      int64_t from = tau::intAttr(op, "slice");
      std::optional<bool> direction = tau::goesEast(op);
      if (!direction) {
        op.emitError("the instructions that use this word lie on both sides "
                     "of the slice that issues it");
        failed = true;
        return std::nullopt;
      }
      bool east = *direction;
      int delay = machine->delayOf(static_cast<int>(from), tau::delayName(op));
      int64_t land = *time + delay + 1;
      return std::make_pair(east, east ? from - land : from + land);
    };
    // Give a run of words the lowest free run of stream numbers that starts
    // at a multiple of `align`. Word `k` of the run is the result of
    // `ops[k]`, or result `k` of the one instruction in `ops`, which is given
    // the stream of its first result.
    llvm::DenseSet<Operation *> routed;
    auto give = [&](ArrayRef<Operation *> ops, int64_t width, int64_t align) {
      std::vector<std::pair<bool, int64_t>> slots;
      for (int64_t k = 0; k < width; ++k) {
        auto slot = slotOf(*ops[ops.size() == 1 ? 0 : k]);
        if (!slot)
          return;
        slots.push_back(*slot);
      }
      int64_t base = 0;
      auto free = [&] {
        for (int64_t k = 0; k < width; ++k)
          if (taken[slots[k]].count(base + k))
            return false;
        return true;
      };
      while (base + width <= machine->streams && !free())
        base += align;
      if (base + width > machine->streams) {
        ops.front()->emitError(
            "the machine has too few streams for this program");
        failed = true;
        return;
      }
      for (int64_t k = 0; k < width; ++k)
        taken[slots[k]].insert(base + k);
      for (size_t k = 0; k < ops.size(); ++k) {
        ops[k]->setAttr("east", builder.getBoolAttr(slots[k].first));
        tau::setIntAttr(*ops[k], "stream", base + static_cast<int64_t>(k));
        routed.insert(ops[k]);
      }
    };

    Block &block = func.getBody().front();
    for (Operation &op : block) {
      if (!tau::isInstr(op) || failed)
        continue;
      Expected<std::vector<tau::SideBySide>> runs = tau::sideBySide(op);
      if (!runs) {
        op.emitError(toString(runs.takeError()));
        return signalPassFailure();
      }
      for (const tau::SideBySide &run : *runs)
        if (!failed)
          give(run.makers, static_cast<int64_t>(run.makers.size()), run.align);
    }
    for (Operation &op : block)
      if (tau::isInstr(op) && tau::streamResult(op) && !routed.count(&op) &&
          !failed) {
        int64_t width = op.getNumResults();
        give({&op}, width, width);
      }
    if (failed)
      return signalPassFailure();

    tau::setMachine(func, *machine);
    func->removeAttr("tau.streams");
  }
};

} // namespace

std::unique_ptr<Pass> tau::createRoutePass() {
  return std::make_unique<RoutePass>();
}
