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
