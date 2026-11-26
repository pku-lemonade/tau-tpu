import Specify.Support.Tables

set_option linter.unusedVariables false

/-!
# Specify: the repeater

Source: `docs/Machine.md`, section 2.7.

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

namespace Specify.Repeater

open Tau Specify

/-- The state of a repeater. `Unit` is a placeholder. The doc says which
registers the hardware keeps for each entry. -/
abbrev State : Type := Unit

/-- A repeater for the program `prog`. `Entry` is the record of section 2.7,
with fields `time`, `repeats`, `gap`, `first` and `next`. -/
def repeater (prog : List (Entry Nat)) : Block State Unit (List Nat) := todo

#eval report "the repeater" (Tables.repeater repeater)

-- #eval report "the repeater, what the doc leaves open" (Tables.repeaterDecisions repeater)

/-! ## State -/

/-- What a repeater outputs at cycle `t`, said without mentioning registers.
This needs a second definition: the item an entry issues at cycle `t`, if
any, computed directly from the entry's fields. Define it above. Then the
statement says that the block with registers agrees with it. -/
def IssuesWhatIsDue : Prop := todo

/-! ## Compare

The definition is `repeater` in `spec/Tau/Blocks/Repeater.lean`. That file has
two descriptions of the same thing: `Entry.dueAt`, which mentions no
registers, and `Slot.step`, which is the registers. The statement that they
agree is `repeater_outAt` in `spec/Tau/Proofs/Blocks/Repeater.lean`. Its proof
needs an invariant and is long; read its outline, not its steps.
-/

end Specify.Repeater
