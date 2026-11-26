import Specs.Tables

set_option linter.unusedVariables false

/-!
# Specify: the systolic array

Source: `Tau/Docs/Machine.md`, section 2.8.

The steps, which are the same in every file of this folder:

1. Read the source. Do not open the file in `Tau/` yet.
2. Choose the state and write the definition in place of `todo`.
3. Put the cursor on the first `#eval` line. It says which rows of the
   source's table your definition gets right.
4. Write down what the source does not say but your definition had to
   decide. Then remove the `--` in front of the second `#eval` line to see
   what the specification in `Tau/` decided.
5. Fill in the statement under "State".
6. Compare with the file in `Tau/` named at the end.
-/

namespace Specs.SystolicArray

open Tau Specs

/-- The state of a systolic array. `Unit` is a placeholder. -/
abbrev State : Type := Unit

/-- A systolic array that holds the vector `x`, one cell per element. The
input of a cycle is the list of coefficients, one per cell. -/
def systolicArray (x : List Int) : Block State (List Int) Int := todo

#eval report "the systolic array" (Tables.systolicArray systolicArray)

-- #eval report "the systolic array, what the doc leaves open" (Tables.systolicArrayDecisions systolicArray)

/-! ## State -/

/-- "If the coefficient `A i j` is fed to cell `j` at cycle `i + j`, the product
of row `i` with `x` comes out at cycle `i + n`." Write the hypothesis about
the inputs and the conclusion about the output. -/
def ComputesMatVec : Prop := todo

/-! ## Compare

The definition is `systolicArray` in `Tau/Blocks/SystolicArray.lean`. It uses
`Vector` where this file uses `List`, so that the number of cells is part of
the type. The statement is `systolicArray_matvec` in
`Tau/Proofs/Blocks/SystolicArray.lean`.
-/

end Specs.SystolicArray
