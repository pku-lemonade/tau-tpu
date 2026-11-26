import Tau.Blocks.Pipeline
import Tau.Proofs.Blocks.ShiftRegister

/-!
# Pipeline: proofs

The main result is `pipeline_outAt`: the output at cycle `t` is `f` applied to
the input from `d` cycles earlier.
-/

namespace Tau

variable {α β : Type}

/-- A pipeline of depth `d` outputs, at cycle `t`, the function applied to the
input of cycle `t - d`. -/
theorem pipeline_outAt (d : Nat) (f : α → β) (reset : β) (inp : Signal α) (t : Nat) :
    (pipeline d f reset).outAt inp t = if d ≤ t then f (inp (t - d)) else reset := by
  unfold pipeline
  rw [Block.outAt_mapIn, shiftRegister_outAt]

end Tau
