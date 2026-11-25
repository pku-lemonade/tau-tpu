import Specs.Tables

set_option linter.unusedVariables false

/-!
# Specify: the pipeline

Source: `course/architecture-manual.md`, section 2.4.

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

namespace Specs.Pipeline

open Tau Specs

/-- The state of a pipeline of depth `d`. `Unit` is a placeholder: choose what
a pipeline has to remember. -/
abbrev State (d : Nat) : Type := Unit

/-- A pipeline of depth `d` that computes `f`, with the given reset value. You
may build it from `Tau.shiftRegister` or from nothing. -/
def pipeline (d : Nat) (f : Int → Int) (reset : Int) : Block (State d) Int Int := todo

#eval report "the pipeline" (Tables.pipeline pipeline)

-- #eval report "the pipeline, what the manual leaves open" (Tables.pipelineDecisions pipeline)

/-! ## State -/

/-- The property of a pipeline that a user relies on: what the output at cycle
`t` is, in terms of the inputs. Say it about `pipeline d f reset`, for every
`d`, `f`, `reset`, every input signal and every cycle. -/
def OutputIsDelayed : Prop := todo

/-! ## Compare

The definition is `pipeline` in `Tau/Blocks/Pipeline.lean`. The statement is
`pipeline_outAt` in `Tau/Proofs/Blocks/Pipeline.lean`. Is your state the
same? If not, both can still be right: the tests look only at outputs.
-/

end Specs.Pipeline
