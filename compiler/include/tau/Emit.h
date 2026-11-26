//===- Emit.h - write the files the Lean tools read -----------------------===//
//
// One writer for each kind of file in docs/Formats.md. A writer writes what is
// in the IR and changes nothing: every rewrite of the program is a pass
// (tau/Passes.h).
//
//===----------------------------------------------------------------------===//

#ifndef TAU_EMIT_H
#define TAU_EMIT_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

namespace tau {

/// A source or kernel file (lib/Emit/EmitSource.cpp). Valid on a function
/// before `tau-place`. With a `tau.call` in the function the file is a source
/// file; the kernels it calls are looked up in the function's module.
llvm::Expected<llvm::json::Value> emitSource(mlir::func::FuncOp func);

/// A placed file (lib/Emit/EmitMachine.cpp, as are the next two). Valid
/// after `tau-place`.
llvm::Expected<llvm::json::Value> emitPlaced(mlir::func::FuncOp func);

/// A compiled file. Valid after `tau-schedule`, which gives every word a
/// stream, and after `tau-slice`, when it is written from the entries.
llvm::Expected<llvm::json::Value> emitCompiled(mlir::func::FuncOp func);

/// An image file: the numbers of every slice. Valid after `tau-encode`.
llvm::Expected<llvm::json::Value> emitImage(mlir::func::FuncOp func);

} // namespace tau

#endif // TAU_EMIT_H
