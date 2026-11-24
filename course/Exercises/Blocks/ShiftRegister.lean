/-
Exercise file. Generated from Tau/Proofs/Blocks/ShiftRegister.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/Blocks/ShiftRegister.lean.
Build this file alone with:

    lake build Exercises.Blocks.ShiftRegister
-/

import Tau.Blocks.ShiftRegister
import Tau.Proofs.Blocks.Basic

/-!
# Shift register: proofs

The main result is `shiftRegister_outAt`: a shift register of depth `n` delays
its input by exactly `n` cycles.

Every block theorem in tau-tpu has this form: the output at cycle `t`, written
as a function of the inputs at earlier cycles.
-/

namespace Tau

variable {α : Type}

theorem shiftRegister_init (n : Nat) (reset : α) :
    (shiftRegister n reset).init = Vector.replicate n reset := rfl

theorem shiftRegister_step (n : Nat) (reset : α) (s : Vector α n) (x : α) :
    (shiftRegister n reset).step s x =
      (Vector.ofFn fun i : Fin n =>
          if i.val = 0 then x
          else s[i.val - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt),
       if h : 0 < n then s[n - 1]'(Nat.sub_lt h Nat.zero_lt_one) else x) := rfl

/-- What each slot holds at the start of cycle `t`: slot `i` holds the input
from `i + 1` cycles ago, or `reset` if the register has not run that long. -/
theorem shiftRegister_stateAt (n : Nat) (reset : α) (inp : Signal α)
    (t i : Nat) (hi : i < n) :
    ((shiftRegister n reset).stateAt inp t)[i] =
      if i < t then inp (t - 1 - i) else reset := by
  sorry

/-- A shift register of depth `n` delays its input by exactly `n` cycles.
For the first `n` cycles it outputs `reset`. -/
theorem shiftRegister_outAt (n : Nat) (reset : α) (inp : Signal α) (t : Nat) :
    (shiftRegister n reset).outAt inp t =
      if n ≤ t then inp (t - n) else reset := by
  sorry

end Tau
