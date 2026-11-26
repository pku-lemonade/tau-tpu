import Specify.Support.Tables

set_option linter.unusedVariables false

/-!
# Specify: streams and instructions

Source: `docs/Machine.md`, sections 3.2, 3.5 and 3.7.

Two parts of the machine, small enough to write in an afternoon. The types
are the ones in `spec/Tau/Isa/Instr.lean` and at the top of
`spec/Tau/Machine/SliceLevel.lean` (`Slice`, `TrapKind`); read those first. Do not
read `exec` and `advanceRow` further down that file yet.

The steps, which are the same in every file of this folder:

1. Read the source. Do not open the file in `spec/Tau/` yet.
2. Write each definition in place of `todo`.
3. Put the cursor on the first `#eval` line. It says which rows of the
   source's table your definition gets right.
4. Write down what the source does not say but your definition had to
   decide. Then remove the `--` in front of the second `#eval` line to see
   what the specification in `spec/Tau/` decided.
5. Fill in the statement under "State".
6. Compare with the file in `spec/Tau/` named at the end.
-/

namespace Specify.Machine

open Tau Specify

/-! ## Streams -/

/-- One stream going east, after one cycle. `row[p]` is what the stream holds
at position `p` before the cycle. `placed p` is the word, if any, that the
slice at position `p` places on this stream during the cycle. -/
def advanceEast (placed : Nat → Option Int) (row : List (Option Int)) : List (Option Int) :=
  todo

/-- The same for a stream going west. -/
def advanceWest (placed : Nat → Option Int) (row : List (Option Int)) : List (Option Int) :=
  todo

#eval report "stream going east" (Tables.streamEast advanceEast)
#eval report "stream going west" (Tables.streamWest advanceWest)

-- #eval report "streams, what the doc leaves open" (Tables.streamEastDecisions advanceEast)

/-! ## Instructions -/

variable {V : Type}

/-- Carry out one instruction at one slice of the given kind. `rd tr` is what
the stream `tr` holds at this slice. The result is a trap, or the new state
of the slice together with the result of the instruction, if it has one, and
the stream the result is for.

Write the cases for `read`, `write`, `un` and `bin`. Leave the others as
they are. -/
def exec (S : Sem V) (cfg : Config) (kind : Kind) (rd : Stream → Option V) (sl : Slice V) :
    Instr → Except TrapKind (Slice V × Option (Stream × V))
  | .read addr dst => todo
  | .write src addr => todo
  | .un op src dst => todo
  | .bin op a b dst => todo
  | _ => .error .wrongSlice

#eval report "instructions" (Tables.exec exec)

-- #eval report "instructions, what the doc leaves open" (Tables.execDecisions exec)

/-! ## State -/

/-- One cycle of the timing rule, for one stream going east: if the stream
holds `v` at position `p`, and the slice at `p + 1` places nothing, then
after the cycle the stream holds `v` at position `p + 1`. Say it about your
`advanceEast`. Which hypothesis about `p` and the length of the row does it
need? -/
def MovesOnePosition : Prop := todo

/-! ## Compare

The definitions are `advanceRow` and `exec` in `spec/Tau/Machine/SliceLevel.lean`.
The statement for one cycle is `sample_step` in
`spec/Tau/Proofs/Machine/Timing.lean`, and the whole timing rule is
`arrives_east` in the same file.
-/

end Specify.Machine
