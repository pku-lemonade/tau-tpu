#ifndef TAU_DIALECT_TAUDIALECT_H
#define TAU_DIALECT_TAUDIALECT_H

#include "mlir/Bytecode/BytecodeOpInterface.h"
#include "mlir/IR/Dialect.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"

#include "tau/Dialect/TauOpsDialect.h.inc"

#define GET_TYPEDEF_CLASSES
#include "tau/Dialect/TauOpsTypes.h.inc"

#define GET_OP_CLASSES
#include "tau/Dialect/TauOps.h.inc"

#endif // TAU_DIALECT_TAUDIALECT_H
