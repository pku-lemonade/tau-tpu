#ifndef TAU_TRANSFORMS_PASSES_H
#define TAU_TRANSFORMS_PASSES_H

#include <memory>

namespace mlir {
class Pass;
} // namespace mlir

namespace tau {

struct Chip;

/// Replaces every `tau.call` by the body of the kernel it calls and removes
/// every function but the last. A pass on the module.
/// Lean model of its input: Tau/IR/Source.lean.
std::unique_ptr<mlir::Pass> createInlinePass();

/// Rewrites `relu(relu a)` to `relu a`, and `max(a, a)` and `min(a, a)` to
/// `a`. The same rewrites on expressions: Tau/Check/Simplify.lean.
std::unique_ptr<mlir::Pass> createSimplifyPass();

/// Replaces every `tau.for` by one copy of its body per iteration.
/// Lean model: Tau/Passes/Unroll.lean.
std::unique_ptr<mlir::Pass> createUnrollPass();

/// Chooses a memory slice and address for every buffer and a slice for every
/// operation, and rewrites the kernel into instructions (`tau.i.*`). Decides
/// which values travel directly between slices and which wait in memory.
std::unique_ptr<mlir::Pass> createPlacePass(const Chip &chip);

/// Gives every instruction a cycle (`time`).
std::unique_ptr<mlir::Pass> createSchedulePass();

/// Gives every travelling word a stream (`east`, `stream`).
std::unique_ptr<mlir::Pass> createRoutePass();

/// Replaces the instructions by one list of entries per slice (`tau.slice`,
/// `tau.entry`), which name streams and not the words on them.
std::unique_ptr<mlir::Pass> createSlicePass();

/// Merges entries of a slice into repeating entries.
std::unique_ptr<mlir::Pass> createFoldPass();

/// Makes the passes available to `tau-opt` as `--tau-inline`,
/// `--tau-simplify`, `--tau-unroll`, `--tau-place`, `--tau-schedule`,
/// `--tau-route`, `--tau-slice` and `--tau-fold`.
void registerPasses();

} // namespace tau

#endif // TAU_TRANSFORMS_PASSES_H
