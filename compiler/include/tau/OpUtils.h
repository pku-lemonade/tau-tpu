//===- OpUtils.h - reading and writing tau operations ---------------------===//
//
// Small helpers that the passes and the writers share.
//
//===----------------------------------------------------------------------===//

#ifndef TAU_OPUTILS_H
#define TAU_OPUTILS_H

#include "mlir/IR/Operation.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

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
/// The first word of the result of `op` that travels on streams, if it has
/// such a result. The words of a result are on streams that follow one
/// another, and an instruction records the first.
mlir::Value streamResult(mlir::Operation &op);
/// The stream number of the word `value`, once its maker has one: the
/// maker's first stream plus the place of the word in the result.
std::optional<int64_t> streamNumber(mlir::Value value);
/// The values `op` takes: each a run of its word operands, the low word
/// first (Machine 3.5). A write, a product and a read have no value of more
/// than one word; an `install` takes its words as one run.
std::vector<std::vector<mlir::Value>> operandValues(mlir::Operation &op);
/// The number of words in a value of `bits` bits.
inline int64_t wordsOf(int64_t bits) { return bits / 8; }
/// The name of the type of values of `bits` bits, as Formats writes it:
/// "i8", "i16" or "i32".
std::string typeName(int64_t bits);
/// The number that stands for that type in an image (Machine 3.10).
inline int64_t typeCode(int64_t bits) { return bits == 8 ? 0 : bits == 16 ? 1 : 2; }
/// The words a `tau.i.install` installs, in order: its operands but for the
/// link to the `install` before it.
std::vector<mlir::Value> installedWords(mlir::Operation &op);
/// A run of words that an instruction takes side by side, on streams that
/// follow one another (Machine 3.5), each made by an instruction of its own:
/// those instructions in order, and the multiple the first stream's number
/// has to be of.
struct SideBySide {
  std::vector<mlir::Operation *> makers;
  int64_t align = 1;
};
/// The runs of `op`. A value all of whose words are the result of one
/// instruction is not among them: it is side by side as it is made. Fails
/// if the words of a value come some from one instruction and some from
/// another in a way that cannot be laid side by side.
llvm::Expected<std::vector<SideBySide>> sideBySide(mlir::Operation &op);
/// The direction of the stream that carries the result of `op` to the
/// instructions that use it: east (true) if all of them are at its position
/// or a higher one, west if all are at its position or a lower one, and
/// nothing if they lie on both sides. A word is on one stream, and a stream
/// goes one way (Machine 3.2).
std::optional<bool> goesEast(mlir::Operation &op);
/// The name a machine's `delays` give `op` (Formats 3): the `fn` of
/// `tau.i.un` and `tau.i.bin`, and the instruction otherwise. Mirrors
/// `Instr.name` in spec/Tau/Isa/Instr.lean.
llvm::StringRef delayName(mlir::Operation &op);

//===----------------------------------------------------------------------===//
// Kernel operations
//===----------------------------------------------------------------------===//

/// "tau.relu" -> "relu".
llvm::StringRef kernelName(mlir::Operation &op);
/// Whether `op` is a one-value operation such as `tau.relu` or `tau.shift`.
bool isUnaryKernelOp(mlir::Operation &op);
/// Whether `op` is a two-value operation such as `tau.add`.
bool isBinaryKernelOp(mlir::Operation &op);
/// Whether the one-value operation `name` runs on the rearrangement slice.
bool isRearrangement(llvm::StringRef name);

} // namespace tau

#endif // TAU_OPUTILS_H
