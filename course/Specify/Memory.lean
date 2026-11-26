import Specify.Support.Tables

set_option linter.unusedVariables false

/-!
# Specify: the memory

Source: `docs/Machine.md`, section 2.5.

The steps, which are the same in every file of this folder:

1. Read the source. Do not open the file in `spec/Tau/` yet.
2. Choose the state and write the definition in place of `todo`.
3. Put the cursor on the first `#eval` line. It says which rows of the
   source's table your definition gets right.
4. Write down what the source does not say but your definition had to
   decide. Then remove the `--` in front of the second `#eval` line to see
   what the specification in `spec/Tau/` decided.
5. Fill in the statement under "State".
6. Compare with the file in `spec/Tau/` named at the end.
-/

namespace Specify.Memory

open Tau Specify

/-- The state of a memory. `Unit` is a placeholder. -/
abbrev State : Type := Unit

/-- A memory whose words start as `words`. `MemIn` is the command type of
section 2.5: `.idle`, `.read a`, `.write a x`. -/
def memory (words : List Int) : Block State (MemIn Int) (Option Int) := todo

#eval report "the memory" (Tables.memory memory)

-- #eval report "the memory, what the doc leaves open" (Tables.memoryDecisions memory)

/-! ## State -/

/-- "A read returns the value most recently written to that address, or the
starting value if nothing was written." You will need a function that finds
the most recent write to an address before cycle `t`; define it above. -/
def ReadsLastWrite : Prop := todo

/-! ## Compare

The definition is `memory` in `spec/Tau/Blocks/Memory.lean`, with `lastWrite` as
the function that looks back. The statement is `memory_outAt_read` in
`spec/Tau/Proofs/Blocks/Memory.lean`. It has a hypothesis that the address is
valid. Does yours?
-/

end Specify.Memory
