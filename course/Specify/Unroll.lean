import Specify.Support.Tables

set_option linter.unusedVariables false

/-!
# Specify: a copy of the `tau-unroll` pass

Source: `compiler/lib/Transforms/Unroll.cpp`.

The pass is about eighty lines of C++. Most of them are about MLIR: values,
regions, builders, a pass class. Find the few lines that say what the pass
does to a kernel, and write those in Lean on the type `Kernel`.

1. Read the source. Do not open `spec/Tau/IR/Unroll.lean` yet.
2. Write the definition in place of `todo`. You will want helper functions.
3. Put the cursor on the `#eval` lines. The first uses hand-written kernels.
   One of its rows asks the checker of the course (`checkKernels`) whether
   your output computes what the input computes. The second compares your
   output with what the real compiler wrote for one example.
4. Write down what your copy leaves out of the C++, and what it had to
   decide that the C++ does not say. Then remove the `--`.
5. Fill in the statement under "State".
6. Compare with `spec/Tau/IR/Unroll.lean`.
-/

namespace Specify.Unroll

open Tau Specify

/-- A kernel with every loop written out. -/
def unroll (k : Kernel) : List Stmt := todo

#eval report "unroll" (Tables.unroll unroll)
#eval reportIO "unroll, against the compiler"
  (Tables.unrollOnExample unroll "examples/ops/elementwise/stages")

-- #eval report "unroll, what the source leaves open" (Tables.unrollDecisions unroll)

/-! ## State -/

/-- What it means for this pass to be right: the output computes what the
input computes. Say it with `Kernel.run`, for every kernel, every meaning `S`
of the operations and every buffer contents. -/
def KeepsWhatIsComputed : Prop := todo

/-! ## Compare

The definition is `Kernel.unroll` in `spec/Tau/IR/Unroll.lean`, and the
statement is `Kernel.run_unroll` in `spec/Tau/Proofs/IR/Unroll.lean`.
-/

end Specify.Unroll
