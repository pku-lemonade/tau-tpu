#ifndef TAU_TARGET_TARGET_H
#define TAU_TARGET_TARGET_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

#include <optional>
#include <string>
#include <vector>

namespace tau {

/// The shape of a machine. Mirrors `Tau.Config` in spec/Tau/Isa/Instr.lean.
struct Machine {
  /// The kind of slice at each position, west to east: "mem", "vxm", "sxm"
  /// or "mxm".
  std::vector<std::string> kinds;
  int streams = 8;
  /// The number of columns a matrix slice can store.
  int mxmWeights = 8;
  int memDelay = 1;
  int vxmDelay = 1;
  int sxmDelay = 1;
  int mxmDelay = 2;

  /// A nine-slice machine: matrix, rearrangement, two memories, vector, two
  /// memories, rearrangement, matrix.
  static Machine standard();
  static llvm::Expected<Machine> fromJSON(const llvm::json::Value &value);
  static llvm::Expected<Machine> fromFile(llvm::StringRef path);
  llvm::json::Value toJSON() const;

  /// The number of cycles a result spends inside the slice at `pos`.
  int delayAt(int pos) const;
  int maxDelay() const;
};

//===----------------------------------------------------------------------===//
// What `tau-place` records on the function for the later passes
//===----------------------------------------------------------------------===//

/// The machine, as recorded on a placed function.
llvm::Expected<Machine> machineOf(mlir::func::FuncOp func);
void setMachine(mlir::func::FuncOp func, const Machine &machine);

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

//===----------------------------------------------------------------------===//
// Files for the Lean tools (docs/Formats.md)
//===----------------------------------------------------------------------===//

/// A source or kernel file. Valid on a function before `tau-place`. With a
/// `tau.call` in the function the file is a source file; the kernels it
/// calls are looked up in the function's module.
llvm::Expected<llvm::json::Value> emitKernel(mlir::func::FuncOp func);

/// A placed file. Valid after `tau-place`.
llvm::Expected<llvm::json::Value> emitPlaced(mlir::func::FuncOp func);

/// A compiled file. Valid after `tau-schedule`, and after `tau-slice`, when
/// it is written from the entries.
///
/// With `idealRouting`, the streams chosen by `tau-route` are ignored (they
/// need not exist yet): every travelling word gets a stream of its own and
/// the machine is given as many streams as that takes. Checking this file tests
/// the schedule without testing the routing.
llvm::Expected<llvm::json::Value> emitCompiled(mlir::func::FuncOp func,
                                               bool idealRouting);

/// An image file: the entries of every slice as numbers. Valid after
/// `tau-slice`.
llvm::Expected<llvm::json::Value> emitImage(mlir::func::FuncOp func);

} // namespace tau

#endif // TAU_TARGET_TARGET_H
