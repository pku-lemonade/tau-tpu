//===- Passes.h - the passes of the compiler ------------------------------===//
//
// One pass for each step of Compiler 4 (docs/Compiler.md), in the order tauc
// runs them. Each is in its own file in lib/Passes/.
//
//===----------------------------------------------------------------------===//

#ifndef TAU_PASSES_H
#define TAU_PASSES_H

#include <memory>

namespace mlir {
class Pass;
} // namespace mlir

namespace tau {

struct Machine;

/// Replaces every `tau.call` by the body of the kernel it calls and removes
/// every function but the last. A pass on the module.
/// Lean model of its input: spec/Tau/IR/Source.lean.
std::unique_ptr<mlir::Pass> createInlinePass();

/// Rewrites `relu(relu a)` to `relu a`, and `max(a, a)` and `min(a, a)` to
/// `a`. The same rewrites on expressions: spec/Tau/Check/Simplify.lean.
std::unique_ptr<mlir::Pass> createSimplifyPass();

/// Replaces every `tau.for` by one copy of its body per iteration.
/// Lean model: spec/Tau/IR/Unroll.lean.
std::unique_ptr<mlir::Pass> createUnrollPass();

/// Chooses a memory slice and address for every buffer and a slice for every
/// operation, and rewrites the kernel into instructions (`tau.i.*`). Decides
/// which values travel directly between slices and which wait in memory.
std::unique_ptr<mlir::Pass> createPlacePass(const Machine &machine);

/// Gives every instruction a cycle (`time`), and every travelling word a
/// stream of its own (`east`, `stream`) on a machine widened to have enough
/// of them. The machine's own number of streams is kept in `tau.streams`.
std::unique_ptr<mlir::Pass> createSchedulePass();

/// Gives every travelling word a stream of the machine's own (`east`,
/// `stream`), sharing a stream between words that never meet.
std::unique_ptr<mlir::Pass> createRoutePass();

/// Replaces the instructions by one list of entries per slice (`tau.slice`,
/// `tau.entry`), which name streams and not the words on them.
std::unique_ptr<mlir::Pass> createSlicePass();

/// Merges entries of a slice into repeating entries.
std::unique_ptr<mlir::Pass> createFoldPass();

/// Replaces each `tau.slice` by a `tau.image`: its entries as the numbers the
/// slice's repeater is loaded with. Lean model: `Program.encode` in
/// spec/Tau/Isa/Encode.lean.
std::unique_ptr<mlir::Pass> createEncodePass();

/// Makes the passes available to `tau-opt` as `--tau-inline`,
/// `--tau-simplify`, `--tau-unroll`, `--tau-place`, `--tau-schedule`,
/// `--tau-route`, `--tau-slice`, `--tau-fold` and `--tau-encode`.
void registerPasses();

} // namespace tau

#endif // TAU_PASSES_H
