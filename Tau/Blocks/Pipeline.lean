import Tau.Blocks.ShiftRegister

/-!
# Pipeline

A pipeline computes a function `f` and delivers the result a fixed number of
cycles later. It is a shift register with `f` in front of it.

In tau-tpu every slice is a pipeline: an instruction issued at cycle `t`
produces its result at cycle `t + d`, where `d` depends only on the slice.

Terms to look up: *pipelining*, *latency*.

Docs: Machine 2.4 (`Tau/Docs/`).
-/

namespace Tau

variable {α β : Type}

/-- A pipeline that computes `f` with a delay of `d` cycles.
For the first `d` cycles it outputs `reset`. -/
def pipeline (d : Nat) (f : α → β) (reset : β) : Block (Vector β d) α β :=
  (shiftRegister d reset).mapIn f

example : (pipeline 2 (· * 2) 0).trace (fun t => t + 1) 5 = [0, 0, 2, 4, 6] := by
  decide

end Tau
