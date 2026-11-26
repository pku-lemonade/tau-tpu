//===- Machine.h - the machine a program is compiled for ------------------===//
//
// The description of a machine (docs/Formats.md, section 3: `config`), read
// from a file such as machines/tau9.json, and how `tau-place` records it on a
// function for the later passes.
//
//===----------------------------------------------------------------------===//

#ifndef TAU_MACHINE_H
#define TAU_MACHINE_H

#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/JSON.h"

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

} // namespace tau

#endif // TAU_MACHINE_H
