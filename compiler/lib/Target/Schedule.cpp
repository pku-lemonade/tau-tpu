//===- Schedule.cpp - the tau-schedule pass -------------------------------===//
//
// Gives every instruction the cycle on which it is issued.
//
// Two instructions connected by a value have a fixed distance in time:
//
//   * a word produced at slice p and used at slice q:
//         time(use) = time(def) + delay(p) + 1 + |q - p|
//     This is the timing rule of Tau/SliceLevel/Machine.lean. There is no
//     slack: the word is at q on that cycle and on no other.
//
//   * two instructions of one matrix-vector product: one cycle apart.
//
// So the instructions connected by values form *groups* whose times are all
// fixed relative to each other. The pass works out the relative times of each
// group and then lays the groups out one after another, in the order
// `tau-place` emitted them. A group does not start until the previous one has
// issued its last instruction, so everything a group reads from memory was
// written before it starts.
//
// The pass fails if two instructions would be issued at one slice on one
// cycle. `tau-place` builds groups for which that cannot happen.
//
// Nothing here is proved. `tau-check kernel.json scheduled.json` decides
// whether the timed instructions compute what the kernel computes when every
// word has a stream to itself.
//
//===----------------------------------------------------------------------===//

#include "tau/Target/Target.h"
#include "tau/Transforms/Passes.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Pass/Pass.h"
#include "llvm/ADT/DenseMap.h"

#include <cstdlib>
#include <set>

using namespace llvm;
using namespace mlir;

namespace {

struct SchedulePass : PassWrapper<SchedulePass, OperationPass<func::FuncOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(SchedulePass)

  StringRef getArgument() const final { return "tau-schedule"; }
  StringRef getDescription() const final {
    return "Give every instruction a cycle";
  }

  void runOnOperation() override {
    func::FuncOp func = getOperation();
    Expected<tau::Chip> chip = tau::chipOf(func);
    if (!chip) {
      func.emitError(toString(chip.takeError()));
      return signalPassFailure();
    }

    std::vector<Operation *> instrs;
    for (Operation &op : func.getBody().front())
      if (tau::isInstr(op))
        instrs.push_back(&op);

    // How many cycles after `def` the instruction `use` must be issued.
    auto lag = [&](Operation *def, Operation *use) -> int64_t {
      if (!tau::streamResult(*def))
        return 1; // two instructions of one matrix-vector product
      int p = static_cast<int>(tau::intAttr(*def, "slice"));
      int q = static_cast<int>(tau::intAttr(*use, "slice"));
      return chip->delayAt(p) + 1 + std::abs(q - p);
    };

    llvm::DenseMap<Operation *, int64_t> relative;
    std::set<std::pair<int64_t, int64_t>> busy;
    int64_t now = 0;

    for (Operation *seed : instrs) {
      if (relative.count(seed))
        continue;

      // Collect the group of `seed` and its relative times.
      std::vector<Operation *> group{seed};
      relative[seed] = 0;
      for (size_t next = 0; next < group.size(); ++next) {
        Operation *op = group[next];
        int64_t time = relative[op];
        for (Value operand : op->getOperands()) {
          Operation *def = operand.getDefiningOp();
          if (def && relative.try_emplace(def, time - lag(def, op)).second)
            group.push_back(def);
        }
        for (Value result : op->getResults())
          for (Operation *user : result.getUsers())
            if (relative.try_emplace(user, time + lag(op, user)).second)
              group.push_back(user);
      }

      int64_t first = 0;
      int64_t last = 0;
      bool unusedResult = false;
      for (Operation *op : group) {
        first = std::min(first, relative[op]);
        last = std::max(last, relative[op]);
        if (Value result = tau::streamResult(*op))
          unusedResult |= result.use_empty();
      }

      // Lay the group out to start now.
      for (Operation *op : group) {
        int64_t time = relative[op] - first + now;
        tau::setIntAttr(*op, "time", time);
        if (!busy.insert({tau::intAttr(*op, "slice"), time}).second) {
          op->emitError("two instructions at one slice on cycle ") << time;
          return signalPassFailure();
        }
      }
      now += last - first + 1;
      // A result nobody reads is still inside its slice; let it leave.
      if (unusedResult)
        now += chip->maxDelay() + 1;
    }

    func->setAttr("tau.cycles",
                  Builder(func.getContext()).getI64IntegerAttr(now));
  }
};

} // namespace

std::unique_ptr<Pass> tau::createSchedulePass() {
  return std::make_unique<SchedulePass>();
}
