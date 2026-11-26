//===- Slice.cpp - the tau-slice pass -------------------------------------===//
//
// Cuts a routed function into one list of entries per slice.
//
// Up to here an instruction is joined to the instructions it feeds by the
// words it passes on: its result is their operand. The machine has no such
// thing. A slice is told which streams to read and which stream to write
// (`Tau.TimedEntry` in spec/Tau/Isa/Instr.lean), and each slice has its own program.
//
// The pass therefore replaces every instruction by a `tau.entry`:
//
//   * an operand becomes the stream its word travels on, which `tau-route`
//     chose for the instruction that produces it,
//   * the result becomes the stream chosen for the instruction itself,
//   * the cycle stays,
//
// and puts the entries of the slice at position p, in order of time, into a
// `tau.slice p`. Every position of the machine gets one, even if it is empty.
// A pin is dropped: the entry's cycle is the pin, and tau-check has the pin
// in the placed file to compare with.
//
// Nothing here is proved. `tau-check routed.json sliced.json` decides whether
// the entries compute what the routed instructions compute, on the same
// cycles.
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
#include "tau/Machine.h"
#include "tau/OpUtils.h"
#include "tau/Passes.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/Pass/Pass.h"

#include <algorithm>
#include <map>

using namespace llvm;
using namespace mlir;

namespace {

struct SlicePass : PassWrapper<SlicePass, OperationPass<func::FuncOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(SlicePass)

  StringRef getArgument() const final { return "tau-slice"; }
  StringRef getDescription() const final {
    return "Cut the function into one list of entries per slice";
  }

  void runOnOperation() override {
    func::FuncOp func = getOperation();
    Expected<tau::Machine> machine = tau::machineOf(func);
    if (!machine) {
      func.emitError(toString(machine.takeError()));
      return signalPassFailure();
    }
    Block &block = func.getBody().front();
    OpBuilder builder(func.getContext());

    std::vector<Operation *> instrs;
    for (Operation &op : block)
      if (tau::isInstr(op))
        instrs.push_back(&op);

    // The stream of a travelling word, as `tau-route` recorded it on the
    // instruction that produces the word.
    bool failed = false;
    auto streamOf = [&](Value value) -> std::string {
      Operation *def = value.getDefiningOp();
      auto east = def->getAttrOfType<BoolAttr>("east");
      std::optional<int64_t> stream = tau::optIntAttr(*def, "stream");
      if (!east || !stream) {
        def->emitError("run tau-route before tau-slice");
        failed = true;
        return "";
      }
      return (east.getValue() ? "e" : "w") + std::to_string(*stream);
    };

    // The entries of each slice, with their cycles.
    std::map<int64_t, std::vector<std::pair<int64_t, NamedAttrList>>> entries;
    for (Operation *op : instrs) {
      std::optional<int64_t> time = tau::optIntAttr(*op, "time");
      if (!time) {
        op->emitError("run tau-schedule before tau-slice");
        return signalPassFailure();
      }
      StringRef name = tau::instrName(*op);
      NamedAttrList attrs;
      attrs.set("instr", builder.getStringAttr(name));
      attrs.set("time", builder.getI64IntegerAttr(*time));
      for (StringRef key : {"fn", "k", "table", "values", "addr", "j"})
        if (Attribute attr = op->getAttr(key))
          attrs.set(key, attr);
      auto connect = [&](StringRef key, Value value) {
        attrs.set(key, builder.getStringAttr(streamOf(value)));
      };
      if (name == "write" || name == "un" || name == "load" ||
          name == "install")
        connect("src", op->getOperand(0));
      if (name == "mac" || name == "seed")
        connect("src", op->getOperand(1));
      if (name == "bin") {
        connect("a", op->getOperand(0));
        connect("b", op->getOperand(1));
      }
      if (name == "sel") {
        connect("m", op->getOperand(0));
        connect("a", op->getOperand(1));
        connect("b", op->getOperand(2));
      }
      if (Value result = tau::streamResult(*op))
        connect("dst", result);
      if (failed)
        return signalPassFailure();
      entries[tau::intAttr(*op, "slice")].push_back({*time, std::move(attrs)});
    }

    builder.setInsertionPoint(block.getTerminator());
    for (int64_t p = 0, n = machine->kinds.size(); p < n; ++p) {
      auto &list = entries[p];
      std::stable_sort(list.begin(), list.end(),
                       [](const auto &x, const auto &y) {
                         return x.first < y.first;
                       });
      OperationState state(func.getLoc(), "tau.slice");
      state.addAttribute("position", builder.getI64IntegerAttr(p));
      Region *body = state.addRegion();
      body->push_back(new Block);
      Operation *slice = builder.create(state);
      OpBuilder inner = OpBuilder::atBlockEnd(&slice->getRegion(0).front());
      for (auto &entry : list) {
        OperationState entryState(func.getLoc(), "tau.entry");
        entryState.addAttributes(entry.second.getAttrs());
        inner.create(entryState);
      }
    }

    for (auto it = instrs.rbegin(); it != instrs.rend(); ++it)
      (*it)->erase();
  }
};

} // namespace

std::unique_ptr<Pass> tau::createSlicePass() {
  return std::make_unique<SlicePass>();
}
