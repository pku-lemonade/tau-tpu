import Specify.Support.Tables

set_option linter.unusedVariables false

/-!
# Specify: what a statement of a kernel does

Source: `compiler/include/tau/Dialect/TauOps.td`, the descriptions of
`tau.load`, `tau.store`, the one-word operations and the two-word
operations.

The types are at the top of `spec/Tau/IR/Kernel.lean`: `Idx`, `Stmt`, `Env`. Read
down to `Env.bind` and stop there.

The steps, which are the same in every file of this folder:

1. Read the source. Do not open the file in `spec/Tau/` yet.
2. Write the definition in place of `todo`.
3. Put the cursor on the first `#eval` line. It says which rows of the
   source's table your definition gets right.
4. Write down what the source does not say but your definition had to
   decide. Then remove the `--` in front of the second `#eval` line to see
   what the specification in `spec/Tau/` decided.
5. Fill in the statement under "State".
6. Compare with the file in `spec/Tau/` named at the end.
-/

namespace Specify.Kernel

open Tau Specify

variable {V : Type}

/-- Run one statement on loop iteration `i`. The result is `none` if the
statement cannot be run.

Write the cases for `load`, `store`, `un` and `bin`. Leave the others as
they are. -/
def execStmt (S : Sem V) (i : Nat) (env : Env V) : Stmt → Option (Env V)
  | .load dst buf ix => todo
  | .store src buf ix => todo
  | .un dst op a => todo
  | .bin dst op a b => todo
  | _ => none

#eval report "statements" (Tables.stmt execStmt)

-- #eval report "statements, what the dialect leaves open" (Tables.stmtDecisions execStmt)

/-! ## State -/

/-- A property of `store` that a user relies on: after a store to a position
inside its buffer, a load from the same position gives the stored value. Say
it about your `execStmt`. -/
def LoadAfterStore : Prop := todo

/-! ## Compare

The definition is `Stmt.exec` in `spec/Tau/IR/Kernel.lean`. There is no theorem
like `LoadAfterStore` in `spec/Tau/Proofs/`: nobody needed it. A specification has
many true properties, and you state the ones somebody relies on.
-/

end Specify.Kernel
