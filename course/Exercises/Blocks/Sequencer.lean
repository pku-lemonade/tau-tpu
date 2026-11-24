/-
Exercise file. Generated from Tau/Proofs/Blocks/Sequencer.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/Blocks/Sequencer.lean.
Build this file alone with:

    lake build Exercises.Blocks.Sequencer
-/

import Tau.Blocks.Sequencer
import Tau.Proofs.Blocks.Basic

/-!
# Sequencer: proofs

The main result is `sequencer_outAt`: at cycle `t` a sequencer outputs exactly
the items of its program that are due at `t`.
-/

namespace Tau

variable {α : Type}

/-- The state of a sequencer at cycle `t` is `t`. -/
theorem sequencer_stateAt (prog : List (Nat × α)) (inp : Signal Unit) (t : Nat) :
    (sequencer prog).stateAt inp t = t := by
  sorry

/-- At cycle `t` a sequencer outputs the items due at `t`. -/
theorem sequencer_outAt (prog : List (Nat × α)) (inp : Signal Unit) (t : Nat) :
    (sequencer prog).outAt inp t = dueAt prog t := by
  sorry

end Tau
