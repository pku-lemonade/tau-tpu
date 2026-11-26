//===- OpUtils.h - reading and writing tau operations ---------------------===//
//
// Small helpers that the passes and the writers share.
//
//===----------------------------------------------------------------------===//

#ifndef TAU_OPUTILS_H
#define TAU_OPUTILS_H

#include "mlir/IR/Operation.h"
#include "llvm/ADT/StringRef.h"

#include <cstdint>
#include <optional>

namespace tau {

//===----------------------------------------------------------------------===//
// Instructions (the `tau.i.*` operations)
//===----------------------------------------------------------------------===//

/// Whether `op` is a `tau.i.*` operation.
bool isInstr(mlir::Operation &op);
/// "tau.i.read" -> "read".
llvm::StringRef instrName(mlir::Operation &op);
int64_t intAttr(mlir::Operation &op, llvm::StringRef name);
std::optional<int64_t> optIntAttr(mlir::Operation &op, llvm::StringRef name);
void setIntAttr(mlir::Operation &op, llvm::StringRef name, int64_t value);
/// The result of `op` that travels on a stream, if it has one.
mlir::Value streamResult(mlir::Operation &op);

//===----------------------------------------------------------------------===//
// Kernel operations
//===----------------------------------------------------------------------===//

/// "tau.relu" -> "relu".
llvm::StringRef kernelName(mlir::Operation &op);
/// Whether `op` is a one-word operation such as `tau.relu` or `tau.shift`.
bool isUnaryKernelOp(mlir::Operation &op);
/// Whether `op` is a two-word operation such as `tau.add`.
bool isBinaryKernelOp(mlir::Operation &op);
/// Whether the one-word operation `name` runs on the rearrangement slice.
bool isRearrangement(llvm::StringRef name);

} // namespace tau

#endif // TAU_OPUTILS_H
