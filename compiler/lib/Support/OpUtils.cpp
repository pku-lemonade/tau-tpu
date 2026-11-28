#include "tau/OpUtils.h"
#include "tau/Dialect/TauDialect.h"

#include "mlir/IR/Builders.h"

#include <cstring>

using namespace llvm;
using namespace mlir;

bool tau::isInstr(Operation &op) {
  return op.getName().getStringRef().starts_with("tau.i.");
}

StringRef tau::instrName(Operation &op) {
  return op.getName().getStringRef().drop_front(strlen("tau.i."));
}

int64_t tau::intAttr(Operation &op, StringRef name) {
  return op.getAttrOfType<IntegerAttr>(name).getInt();
}

std::optional<int64_t> tau::optIntAttr(Operation &op, StringRef name) {
  if (auto attr = op.getAttrOfType<IntegerAttr>(name))
    return attr.getInt();
  return std::nullopt;
}

void tau::setIntAttr(Operation &op, StringRef name, int64_t value) {
  op.setAttr(name, Builder(op.getContext()).getI64IntegerAttr(value));
}

Value tau::streamResult(Operation &op) {
  StringRef name = instrName(op);
  if (name == "read" || name == "un" || name == "bin" || name == "product" ||
      name == "const" || name == "sel")
    return op.getResult(0);
  return Value();
}

std::string tau::typeName(int64_t bits) { return "i" + std::to_string(bits); }

std::optional<int64_t> tau::streamNumber(Value value) {
  Operation *maker = value.getDefiningOp();
  std::optional<int64_t> first = optIntAttr(*maker, "stream");
  if (!first)
    return std::nullopt;
  return *first + cast<OpResult>(value).getResultNumber();
}

std::vector<Value> tau::installedWords(Operation &op) {
  std::vector<Value> words;
  for (Value operand : op.getOperands())
    if (isa<tau::WordType>(operand.getType()))
      words.push_back(operand);
  return words;
}

std::vector<std::vector<Value>> tau::operandValues(Operation &op) {
  StringRef name = instrName(op);
  std::vector<std::vector<Value>> values;
  if (name == "install") {
    values.push_back(installedWords(op));
    return values;
  }
  // The operands of a vector or rearrangement instruction are its values
  // one after another, each of `bits / 8` words.
  size_t count = name == "un" ? 1 : name == "bin" ? 2 : name == "sel" ? 3 : 0;
  if (count == 0) {
    for (Value operand : op.getOperands())
      values.push_back({operand});
    return values;
  }
  size_t width = static_cast<size_t>(wordsOf(intAttr(op, "bits")));
  for (size_t v = 0; v < count; ++v) {
    std::vector<Value> words;
    for (size_t k = 0; k < width; ++k)
      words.push_back(op.getOperand(v * width + k));
    values.push_back(std::move(words));
  }
  return values;
}

Expected<std::vector<tau::SideBySide>> tau::sideBySide(Operation &op) {
  std::vector<SideBySide> runs;
  bool install = instrName(op) == "install";
  for (const std::vector<Value> &words : operandValues(op)) {
    if (words.size() < 2)
      continue;
    // All the words of one result, in order: side by side as made.
    Operation *first = words.front().getDefiningOp();
    bool whole = first->getNumResults() == words.size();
    bool separate = true;
    for (size_t k = 0; k < words.size(); ++k) {
      Operation *maker = words[k].getDefiningOp();
      whole &= maker == first &&
               cast<OpResult>(words[k]).getResultNumber() == k;
      separate &= maker->getNumResults() == 1;
    }
    if (whole && !install)
      continue;
    if (!separate)
      return createStringError(
          "the words of a value come from different results and cannot be "
          "put side by side");
    SideBySide run;
    for (Value word : words)
      run.makers.push_back(word.getDefiningOp());
    run.align = install ? 1 : static_cast<int64_t>(words.size());
    runs.push_back(std::move(run));
  }
  return runs;
}

std::optional<bool> tau::goesEast(Operation &op) {
  int64_t from = intAttr(op, "slice");
  bool east = true, west = true;
  for (Value result : op.getResults())
    for (Operation *user : result.getUsers()) {
      int64_t to = intAttr(*user, "slice");
      east &= to >= from;
      west &= to <= from;
    }
  if (east)
    return true;
  if (west)
    return false;
  return std::nullopt;
}

StringRef tau::delayName(Operation &op) {
  if (auto un = dyn_cast<tau::IUnOp>(op))
    return un.getFn();
  if (auto bin = dyn_cast<tau::IBinOp>(op))
    return bin.getFn();
  return instrName(op);
}

StringRef tau::kernelName(Operation &op) {
  return op.getName().getStringRef().drop_front(strlen("tau."));
}

bool tau::isRearrangement(StringRef name) {
  return name == "shift" || name == "rotate" || name == "reverse" ||
         name == "broadcast" || name == "permute";
}

bool tau::isUnaryKernelOp(Operation &op) {
  if (!op.getName().getStringRef().starts_with("tau.") || isInstr(op))
    return false;
  StringRef name = kernelName(op);
  return name == "relu" || name == "requant" || name == "neg" ||
         name == "abs" || name == "shl" || name == "addi" || name == "muli" ||
         name == "widen" || isRearrangement(name);
}

bool tau::isBinaryKernelOp(Operation &op) {
  if (!op.getName().getStringRef().starts_with("tau.") || isInstr(op))
    return false;
  StringRef name = kernelName(op);
  return name == "add" || name == "sub" || name == "mul" || name == "max" ||
         name == "min" || name == "and" || name == "or" || name == "xor" ||
         name == "lt";
}
