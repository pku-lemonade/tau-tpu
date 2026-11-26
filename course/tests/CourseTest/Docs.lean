import Tau
import Specify.Support.Tables

/-!
# Test: the tables of the docs hold of the specification

`docs/` describes every component in words and with a table of outputs
per cycle, and programs and pins with tables of results. `Specify.Support.Tables` has the same tables as tests.
This file runs them on the definitions in `spec/Tau/`. If the specification, the
tables or the docs change apart, the build fails here.
-/

namespace CourseTest.Docs

open Tau Specify

/-- The memory of the tables: its words given as a list. -/
def memoryOf (words : List Int) : Block (Vector Int words.length) (MemIn Int) (Option Int) :=
  memory words.length ⟨words.toArray, by simp⟩

/-- The systolic array of the tables: vector and coefficients given
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

/-- The event of a pinned statement, as Programs 5 has it: the statement has
run and `env` is what it left. -/
def eventOf (i : Nat) (t : Idx) (s : Stmt) (env : Env Expr) : Option (Event Expr) :=
  (env.issue (t.eval i) (s.target i)).events.head?

#guard passes (Tables.pin eventOf)
#guard passes (Tables.pinDecisions eventOf)

/-- A source program run on names: its final buffers and its pinned words. -/
def runSource (s : Source) (bufs : List (List Expr)) :
    Option (List (List Expr) × List (Event Expr)) :=
  (s.exec exprSem ⟨[], bufs, []⟩).map fun env => (env.bufs, env.events)

#guard passes (Tables.calls runSource)
#guard passes (Tables.issued (issues exprSem))
#guard passes (Tables.numbers Track.encode encodeInt)
#guard passes (Tables.numbersBack Track.decode decodeInt)
#guard passes (Tables.entries Timed.encode)

end CourseTest.Docs
