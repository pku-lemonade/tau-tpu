//===- Schedule.cpp - the tau-schedule pass -------------------------------===//
//
// Gives every instruction the cycle on which it is issued.
//
// Two instructions connected by a value have a fixed distance in time:
//
//   * a word produced at slice p and used at slice q:
//         time(use) = time(def) + delay(p) + 1 + |q - p|
//     This is the timing rule of spec/Tau/Machine/Arch.lean. There is no
//     slack: the word is at q on that cycle and on no other.
//
//   * two instructions of one matrix-vector product: one cycle apart.
//
// So the instructions connected by values form *groups* whose times are all
// fixed relative to each other. The pass works out the relative times of each
// group and then decides when each group starts.
//
//   * A group with a pinned instruction starts where the pin puts it. If the
//     group has several pins they have to agree.
//   * A group with no pin starts when every group before it, in the order
//     `tau-place` emitted them, has issued its last instruction.
//
// Without pins the groups therefore run one after another, and everything a
// group reads from memory was written before it starts. A pin can move a
// group in front of that, so that groups overlap. The pass then makes sure
// that what `tau-place` put in order stays in order where it matters: a word
// of memory is read after the write before it, and written after the reads
// and writes before it; and a matrix slice runs its instructions in the order
// given.
//
// The pass fails if two instructions would be issued at one slice on one
// cycle, if a pin cannot be met, or if a pin breaks that order.
//
// Nothing here is proved. `tau-check placed.json scheduled.json` decides
// whether the timed instructions compute what the placed program computes
// and meet its pins, when every word has a stream to itself.
//
//===----------------------------------------------------------------------===//

#include "tau/Target/Target.h"
#include "tau/Transforms/Passes.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Pass/Pass.h"
#include "llvm/ADT/DenseMap.h"

#include <cstdlib>
#include <map>
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
    Expected<tau::Machine> machine = tau::machineOf(func);
    if (!machine) {
      func.emitError(toString(machine.takeError()));
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
      return machine->delayAt(p) + 1 + std::abs(q - p);
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

      // Where the group starts: where its pin puts it, or now.
      int64_t start = now;
      Operation *pinnedBy = nullptr;
      for (Operation *op : group) {
        std::optional<int64_t> pin = tau::optIntAttr(*op, "pin");
        if (!pin)
          continue;
        int64_t offset = relative[op] - first;
        if (*pin < offset) {
          op->emitError("pinned to cycle ")
              << *pin << ", but it cannot be issued before cycle " << offset;
          return signalPassFailure();
        }
        if (pinnedBy && start != *pin - offset) {
          op->emitError("pinned to cycle ")
              << *pin << ", but another pin in its group puts it on cycle "
              << start + offset;
          return signalPassFailure();
        }
        start = *pin - offset;
        pinnedBy = op;
      }

      for (Operation *op : group) {
        int64_t time = relative[op] - first + start;
        tau::setIntAttr(*op, "time", time);
        if (!busy.insert({tau::intAttr(*op, "slice"), time}).second) {
          op->emitError("two instructions at one slice on cycle ") << time;
          return signalPassFailure();
        }
      }
      int64_t end = start + last - first + 1;
      // A result nobody reads is still inside its slice; let it leave.
      if (unusedResult)
        end += machine->maxDelay() + 1;
      now = std::max(now, end);
    }

    // What `tau-place` put in order must stay in order where it matters.
    // For each word of memory: the cycle of the last write so far and of the
    // last read or write so far. For each matrix slice: the cycle of its
    // last instruction so far.
    std::map<std::pair<int64_t, int64_t>, int64_t> lastWrite, lastUse;
    std::map<int64_t, int64_t> lastMatrix;
    for (Operation *op : instrs) {
      int64_t slice = tau::intAttr(*op, "slice");
      int64_t time = tau::intAttr(*op, "time");
      StringRef name = tau::instrName(*op);
      if (name == "read" || name == "write") {
        std::pair<int64_t, int64_t> cell{slice, tau::intAttr(*op, "addr")};
        const auto &before = name == "read" ? lastWrite : lastUse;
        auto found = before.find(cell);
        if (found != before.end() && found->second >= time) {
          op->emitError("issued on cycle ")
              << time << ", but the word of memory it uses is not ready "
              << "until after cycle " << found->second
              << "; a pin puts it too early";
          return signalPassFailure();
        }
        if (name == "write")
          lastWrite[cell] = time;
        int64_t &use = lastUse.try_emplace(cell, time).first->second;
        use = std::max(use, time);
      } else if (machine->kinds[slice] == "mxm") {
        auto found = lastMatrix.find(slice);
        if (found != lastMatrix.end() && found->second >= time) {
          op->emitError("issued on cycle ")
              << time << ", but its matrix slice is busy with an earlier "
              << "product until after cycle " << found->second
              << "; a pin puts it too early";
          return signalPassFailure();
        }
        lastMatrix[slice] = time;
      }
    }

    func->setAttr("tau.cycles",
                  Builder(func.getContext()).getI64IntegerAttr(now));
  }
};

} // namespace

std::unique_ptr<Pass> tau::createSchedulePass() {
  return std::make_unique<SchedulePass>();
}
