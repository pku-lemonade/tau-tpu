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
  if (name == "read" || name == "un" || name == "bin" || name == "emit" ||
      name == "const" || name == "sel")
    return op.getResult(0);
  return Value();
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
         isRearrangement(name);
}

bool tau::isBinaryKernelOp(Operation &op) {
  if (!op.getName().getStringRef().starts_with("tau.") || isInstr(op))
    return false;
  StringRef name = kernelName(op);
  return name == "add" || name == "sub" || name == "mul" || name == "max" ||
         name == "min" || name == "and" || name == "or" || name == "xor" ||
         name == "lt";
}
