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
  -- Outline of one proof:
  -- Induction on the cycle, for every slot at once.
  -- Cycle 0: every slot holds the reset value.
  -- Cycle t + 1: take one step. Slot 0 holds the input of cycle t.
  -- Slot i > 0 holds what slot i - 1 held at cycle t: use the hypothesis there.
  sorry

/-- A shift register of depth `n` delays its input by exactly `n` cycles.
For the first `n` cycles it outputs `reset`. -/
theorem shiftRegister_outAt (n : Nat) (reset : α) (inp : Signal α) (t : Nat) :
    (shiftRegister n reset).outAt inp t =
      if n ≤ t then inp (t - n) else reset := by
  -- Outline of one proof:
  -- If the depth is positive, the output is the last slot: use the theorem
  -- about slots. If the depth is zero, the output is the input.
  sorry

end Tau
