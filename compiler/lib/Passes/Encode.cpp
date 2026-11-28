//===- Encode.cpp - the tau-encode pass -----------------------------------===//
//
// Writes each slice's entries as the numbers its repeater is loaded with.
//
// Each `tau.slice` becomes a `tau.image` at the same position, holding the
// number of entries and then each entry as numbers:
//
//     time, repeats, gap, stride, opcode, operands...
//
// How each is written is Machine 3.10, and this file follows its Lean copy,
// `Program.encode` in spec/Tau/Isa/Encode.lean, function by function. The Lean
// tools read an image with `Image.decode` from the same file, so a difference
// between the two shows up as a rejected image.
//
// Nothing here is proved. `tau-check compiled.json image.json` decides
// whether the image issues what the finished program issues, on the same
// cycles; `tau-check --encode` whether it is the image the Lean copy writes.
//
//===----------------------------------------------------------------------===//

#include "tau/Dialect/TauDialect.h"
#include "tau/OpUtils.h"
#include "tau/Passes.h"

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/Pass/Pass.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Error.h"

using namespace llvm;
using namespace mlir;

namespace {

/// "e3" -> 6, "w3" -> 7: `Stream.encode` in spec/Tau/Isa/Encode.lean.
int64_t streamNumber(StringRef name) {
  int64_t id = 0;
  name.drop_front().getAsInteger(10, id);
  return 2 * id + (name.starts_with("e") ? 0 : 1);
}

/// `encodeInt` in spec/Tau/Isa/Encode.lean.
int64_t intNumber(int64_t value) {
  return value >= 0 ? 2 * value : 2 * (-value) - 1;
}

/// One entry as numbers: `TimedEntry.encode` in spec/Tau/Isa/Encode.lean.
Error encodeEntry(tau::EntryOp entry, SmallVectorImpl<int64_t> &out) {
  auto num = [&](StringRef key) {
    return tau::optIntAttr(*entry, key).value_or(0);
  };
  auto stream = [&](StringRef key) {
    auto name = entry->getAttrOfType<StringAttr>(key);
    return name ? streamNumber(name.getValue()) : 0;
  };
  out.push_back(static_cast<int64_t>(entry.getTime()));
  out.push_back(num("repeats"));
  out.push_back(num("gap"));
  out.push_back(num("stride"));

  StringRef instr = entry.getInstr();
  if (instr == "read") {
    out.push_back(0);
    out.push_back(num("addr"));
    out.push_back(stream("dst"));
  } else if (instr == "write") {
    out.push_back(1);
    out.push_back(stream("src"));
    out.push_back(num("addr"));
  } else if (instr == "un") {
    out.push_back(2);
    out.push_back(tau::typeCode(num("bits")));
    out.push_back(stream("src"));
    out.push_back(stream("dst"));
    static const char *const plain[] = {"relu",  "requant", "neg",    "abs",
                                        "shl",   "addi",    "muli",   "shift",
                                        "rotate", "reverse", "broadcast",
                                        "permute", "widen"};
    StringRef fn = entry.getFn().value_or("");
    int64_t code = -1;
    for (int64_t c = 0; c < 13; ++c)
      if (fn == plain[c])
        code = c;
    if (code < 0)
      return createStringError("cannot encode the operation '" + fn + "'");
    out.push_back(code);
    if (fn == "addi" || fn == "muli") {
      out.push_back(intNumber(num("k")));
    } else if (fn == "widen") {
      out.push_back(tau::typeCode(num("to")));
    } else if (fn == "permute") {
      ArrayRef<int64_t> table = *entry.getTable();
      out.push_back(static_cast<int64_t>(table.size()));
      for (int64_t item : table)
        out.push_back(item);
    } else if (fn != "relu" && fn != "neg" && fn != "abs" && fn != "reverse") {
      out.push_back(num("k"));
    }
  } else if (instr == "bin") {
    static const char *const fns[] = {"add", "sub", "mul", "max", "min",
                                      "and", "or",  "xor", "lt"};
    StringRef fn = entry.getFn().value_or("");
    int64_t code = -1;
    for (int64_t c = 0; c < 9; ++c)
      if (fn == fns[c])
        code = c;
    if (code < 0)
      return createStringError("cannot encode the operation '" + fn + "'");
    out.push_back(3);
    out.push_back(tau::typeCode(num("bits")));
    out.push_back(code);
    out.push_back(stream("a"));
    out.push_back(stream("b"));
    out.push_back(stream("dst"));
  } else if (instr == "product") {
    out.push_back(4);
    out.push_back(num("n"));
    out.push_back(stream("src"));
    out.push_back(stream("dst"));
  } else if (instr == "install") {
    out.push_back(5);
    out.push_back(num("j"));
    out.push_back(num("g"));
    out.push_back(stream("src"));
  } else if (instr == "const") {
    out.push_back(6);
    out.push_back(tau::typeCode(num("bits")));
    out.push_back(stream("dst"));
    ArrayRef<int64_t> values = *entry.getValues();
    out.push_back(static_cast<int64_t>(values.size()));
    for (int64_t value : values)
      out.push_back(intNumber(value));
  } else if (instr == "sel") {
    out.push_back(7);
    out.push_back(tau::typeCode(num("bits")));
    out.push_back(stream("m"));
    out.push_back(stream("a"));
    out.push_back(stream("b"));
    out.push_back(stream("dst"));
  } else {
    return createStringError("cannot encode the instruction '" + instr + "'");
  }
  return Error::success();
}

struct EncodePass : PassWrapper<EncodePass, OperationPass<func::FuncOp>> {
  MLIR_DEFINE_EXPLICIT_INTERNAL_INLINE_TYPE_ID(EncodePass)

  StringRef getArgument() const final { return "tau-encode"; }
  StringRef getDescription() const final {
    return "Write each slice's entries as numbers";
  }

  void runOnOperation() override {
    func::FuncOp func = getOperation();
    std::vector<tau::SliceOp> slices(
        func.getBody().front().getOps<tau::SliceOp>().begin(),
        func.getBody().front().getOps<tau::SliceOp>().end());
    if (slices.empty()) {
      func.emitError("run tau-slice before tau-encode");
      return signalPassFailure();
    }

    // One list per slice: how many entries, then each (`encodeSlice`).
    for (tau::SliceOp slice : slices) {
      SmallVector<int64_t> numbers;
      auto entries = slice.getBody().front().getOps<tau::EntryOp>();
      numbers.push_back(std::distance(entries.begin(), entries.end()));
      for (tau::EntryOp entry : entries)
        if (Error e = encodeEntry(entry, numbers)) {
          entry.emitError(toString(std::move(e)));
          return signalPassFailure();
        }
      OpBuilder builder(slice);
      builder.create<tau::ImageOp>(slice.getLoc(), slice.getPositionAttr(),
                                   builder.getDenseI64ArrayAttr(numbers));
      slice.erase();
    }
  }
};

} // namespace

std::unique_ptr<Pass> tau::createEncodePass() {
  return std::make_unique<EncodePass>();
}
