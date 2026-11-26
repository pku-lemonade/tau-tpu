import Specify.Support.Tables

set_option linter.unusedVariables false

/-!
# Specify: a copy of the `tau-simplify` pass

Source: `compiler/lib/Transforms/Simplify.cpp`.

There is no copy of this pass in `spec/Tau/`. `spec/Tau/Check/Simplify.lean` makes the
same three rewrites on expressions, which is a different thing: an
expression has no values to rename. Here you write the pass itself, on
kernels.

The C++ says `rewriter.replaceOp(op, inner.getResult())`. In MLIR that
removes an operation and makes every later use of its result use another
value. Your Lean has to do both by hand.

1. Read the source.
2. Write the definition in place of `todo`. You will want helper functions
   and something that remembers which values were replaced by which.
3. Put the cursor on the `#eval` lines. Every row gives a kernel and the
   kernel the pass should make of it. One row asks `checkKernels` whether
   your output computes what the input computes. The second `#eval` compares
   with what the real compiler wrote for the linear layer.
4. Write down what the C++ does not say. Then remove the `--`.
5. Fill in the statement under "State".
6. A solution, with no proof, is in `spec/tests/TauTest/SpecSolutions.lean`.
-/

namespace Specify.Simplify

open Tau Specify

/-- A kernel with repeated `relu` removed, and `max` and `min` of a value
with itself removed. -/
def simplify (k : Kernel) : Kernel := todo

#eval report "simplify" (Tables.simplify simplify)
#eval reportIO "simplify, against the compiler"
  (Tables.simplifyOnExample simplify "examples/nn/linear/stages")

-- #eval report "simplify, what the source leaves open" (Tables.simplifyDecisions simplify)

/-! ## State -/

/-- What it means for this pass to be right. The rewrites are only valid if
the operations obey certain laws; find them in `spec/Tau/Check/Simplify.lean`
(`Sem.Lawful`) and make them a hypothesis. -/
def KeepsWhatIsComputed : Prop := todo

end Specify.Simplify
