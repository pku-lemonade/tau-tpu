#include "tau/Dialect/TauDialect.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "llvm/ADT/TypeSwitch.h"

using namespace mlir;
using namespace tau;

#include "tau/Dialect/TauOpsDialect.cpp.inc"

#define GET_TYPEDEF_CLASSES
#include "tau/Dialect/TauOpsTypes.cpp.inc"

#define GET_OP_CLASSES
#include "tau/Dialect/TauOps.cpp.inc"

void TauDialect::initialize() {
  addTypes<
#define GET_TYPEDEF_LIST
#include "tau/Dialect/TauOpsTypes.cpp.inc"
      >();
  addOperations<
#define GET_OP_LIST
#include "tau/Dialect/TauOps.cpp.inc"
      >();
}

/// A value has 8, 16 or 32 bits (Machine 1).
static bool isWidth(unsigned bits) {
  return bits == 8 || bits == 16 || bits == 32;
}

LogicalResult IntType::verify(function_ref<InFlightDiagnostic()> emitError,
                              unsigned bits) {
  if (!isWidth(bits))
    return emitError() << "a value has 8, 16 or 32 bits, not " << bits;
  return success();
}

LogicalResult BufType::verify(function_ref<InFlightDiagnostic()> emitError,
                              unsigned size, unsigned bits) {
  if (!isWidth(bits))
    return emitError() << "a buffer holds values of 8, 16 or 32 bits, not "
                       << bits;
  return success();
}

LogicalResult WidenOp::verify() {
  unsigned from = cast<IntType>(getA().getType()).getBits();
  unsigned to = cast<IntType>(getResult().getType()).getBits();
  if (to < from)
    return emitOpError("widens a value of ")
           << from << " bits to one of " << to;
  return success();
}
