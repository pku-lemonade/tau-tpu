import Tau
import Specs.Tables

/-!
# Test: the manual's tables hold of the specification

`course/architecture-manual.md` describes every component in words and with a table of
outputs per cycle. `course/Specs/Tables.lean` has the same tables as tests.
This file runs them on the definitions in `Tau/`. If the specification, the
tables or the manual change apart, the build fails here.
-/

namespace TauTest.Manual

open Tau Specs

/-- The memory of the manual's tables: its words given as a list. -/
def memoryOf (words : List Int) : Block (Vector Int words.length) (MemIn Int) (Option Int) :=
  memory words.length ⟨words.toArray, by simp⟩

/-- The systolic array of the manual's tables: vector and coefficients given
as lists. A missing coefficient counts as 0. -/
def systolicOf (x : List Int) : Block (Vector Int x.length) (List Int) Int :=
  (systolicArray (0 : Int) (⟨x.toArray, by simp⟩ : Vector Int x.length)).mapIn
    fun c => Vector.ofFn fun j : Fin x.length => c[j.val]?.getD 0

#guard passes (Tables.shiftRegister fun n reset => shiftRegister n reset)
#guard passes (Tables.shiftRegisterDecisions fun n reset => shiftRegister n reset)
#guard passes (Tables.accumulator fun zero => accumulator zero)
#guard passes (Tables.accumulatorDecisions fun zero => accumulator zero)
#guard passes (Tables.mac fun zero => mac zero)
#guard passes (Tables.macDecisions fun zero => mac zero)
#guard passes (Tables.pipeline fun d f reset => pipeline d f reset)
#guard passes (Tables.pipelineDecisions fun d f reset => pipeline d f reset)
#guard passes (Tables.memory memoryOf)
#guard passes (Tables.memoryDecisions memoryOf)
#guard passes (Tables.sequencer fun prog => sequencer prog)
#guard passes (Tables.sequencerDecisions fun prog => sequencer prog)
#guard passes (Tables.repeater fun prog => repeater prog)
#guard passes (Tables.repeaterDecisions fun prog => repeater prog)
#guard passes (Tables.systolicArray systolicOf)
#guard passes (Tables.systolicArrayDecisions systolicOf)


/-- One stream after one cycle, as section 3.2 has it: the words the slices
place are given by position. -/
def streamOf (d : Dir) (placed : Nat → Option Int) (row : List (Option Int)) :
    List (Option Int) :=
  advanceRow ((List.range row.length).map fun p => (placed p).map fun v => (⟨d, 0⟩, v)) d 0 row

#guard passes (Tables.streamEast (streamOf .east))
#guard passes (Tables.streamEastDecisions (streamOf .east))
#guard passes (Tables.streamWest (streamOf .west))
#guard passes (Tables.exec exec)
#guard passes (Tables.execDecisions exec)

end TauTest.Manual
