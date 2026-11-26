import Specs.Tables

set_option linter.unusedVariables false

/-!
# Specify: the sequencer

Source: `Tau/Docs/Machine.md`, section 2.6.

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

namespace Specs.Sequencer

open Tau Specs

/-- The state of a sequencer. `Unit` is a placeholder. -/
abbrev State : Type := Unit

/-- A sequencer for the program `prog`: items with the cycle each is due. -/
def sequencer (prog : List (Nat × String)) : Block State Unit (List String) := todo

#eval report "the sequencer" (Tables.sequencer sequencer)

-- #eval report "the sequencer, what the doc leaves open" (Tables.sequencerDecisions sequencer)

/-! ## State -/

/-- What a sequencer outputs at cycle `t`, said without mentioning its state.
You will need a function that picks the items due at `t` out of a program;
define it above. -/
def IssuesWhatIsDue : Prop := todo

/-! ## Compare

The definition is `sequencer` in `Tau/Blocks/Sequencer.lean`, with `dueAt`
as the function that needs no state. The statement is `sequencer_outAt` in
`Tau/Proofs/Blocks/Sequencer.lean`.
-/

end Specs.Sequencer
