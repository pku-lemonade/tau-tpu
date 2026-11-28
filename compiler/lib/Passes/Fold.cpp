//===- Fold.cpp - the tau-fold pass ---------------------------------------===//
//
// Merges entries of a slice into repeating entries.
//
// A slice's repeater can issue one entry several times: `repeats` more times
// after the first, `gap` idle cycles apart, with the address of a memory
// instruction or the first installed word of an `install` growing by `stride` each
// time (spec/Tau/Blocks/Repeater.lean, `Tau.TimedEntry` in spec/Tau/Isa/Instr.lean). Reading
// the rows of a matrix on consecutive cycles is one such entry, and so is
// what a slice does once per iteration of a loop that is pinned to a fixed
// spacing.
//
// Within each `tau.slice` the pass looks for entries that are the same but
// for their cycle and their address or column, and whose cycles and
// addresses go up in equal steps. It takes the entries in order of time, and
// for each one not yet merged it collects the longest such run that starts
// there. The entries of a run need not be next to each other: other entries
// of the slice may lie between them. Two entries alone are merged only if
// they are next to each other, so that two unrelated instructions that happen
// to look alike stay apart.
//
// Nothing here is proved. `tau-check sliced.json compiled.json` decides
// whether the folded entries issue what the entries before them issued, on
// the same cycles.
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
#include "tau/Machine.h"
#include "tau/OpUtils.h"
#include "tau/Passes.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/Pass/Pass.h"

using namespace llvm;
using namespace mlir;

namespace {

/// The field of an entry that a repeat can step: the address of a memory
/// instruction or the first installed word of an `install`.
const char *steppedField(tau::EntryOp entry) {
  StringRef instr = entry.getInstr();
  if (instr == "read" || instr == "write")
    return "addr";
  if (instr == "install")
    return "j";
  return nullptr;
}

int64_t stepped(tau::EntryOp entry) {
  const char *field = steppedField(entry);
  return field ? tau::intAttr(*entry, field) : 0;
}

/// Whether two entries are the same but for their cycle and stepped field.
bool sameShape(tau::EntryOp x, tau::EntryOp y) {
  if (x.getInstr() != y.getInstr())
    return false;
  const char *field = steppedField(x);
  NamedAttrList xs(x->getAttrDictionary());
  NamedAttrList ys(y->getAttrDictionary());
  for (NamedAttrList *attrs : {&xs, &ys}) {
    attrs->erase("time");
    if (field)
      attrs->erase(field);
  }
  return xs.getDictionary(x->getContext()) == ys.getDictionary(y->getContext());
}

struct FoldPass : PassWrapper<FoldPass, OperationPass<func::FuncOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(FoldPass)

  StringRef getArgument() const final { return "tau-fold"; }
  StringRef getDescription() const final {
    return "Merge entries of a slice into repeating entries";
  }

  void runOnOperation() override {
    Builder builder(&getContext());
    for (tau::SliceOp slice : getOperation().getBody().front().getOps<tau::SliceOp>()) {
      std::vector<tau::EntryOp> entries;
      for (tau::EntryOp entry : slice.getBody().front().getOps<tau::EntryOp>()) {
        if (entry.getRepeats()) {
          entry.emitError("tau-fold has already been run");
          return signalPassFailure();
        }
        entries.push_back(entry);
      }
      // The entries are in order of time.
      std::vector<bool> merged(entries.size(), false);
      for (size_t i = 0; i < entries.size(); ++i) {
        if (merged[i])
          continue;
        tau::EntryOp first = entries[i];
        // The second entry of a run fixes its spacing and its step.
        std::vector<size_t> run;
        int64_t period = 0, stride = 0;
        for (size_t j = i + 1; j < entries.size(); ++j) {
          if (merged[j] || !sameShape(first, entries[j]))
            continue;
          int64_t dt = entries[j].getTime() - first.getTime();
          int64_t ds = stepped(entries[j]) - stepped(first);
          if (run.empty()) {
            if (dt < 1 || ds < 0)
              break;
            period = dt;
            stride = ds;
            run.push_back(j);
          } else if (dt == period * int64_t(run.size() + 1) &&
                     ds == stride * int64_t(run.size() + 1)) {
            run.push_back(j);
          } else if (dt > period * int64_t(run.size() + 1)) {
            break;
          }
        }
        if (run.empty() || (run.size() == 1 && run[0] != i + 1))
          continue;
        first->setAttr("repeats", builder.getI64IntegerAttr(run.size()));
        first->setAttr("gap", builder.getI64IntegerAttr(period - 1));
        first->setAttr("stride", builder.getI64IntegerAttr(stride));
        for (size_t j : run) {
          merged[j] = true;
          entries[j]->erase();
        }
      }
    }
  }
};

} // namespace

std::unique_ptr<Pass> tau::createFoldPass() {
  return std::make_unique<FoldPass>();
}
