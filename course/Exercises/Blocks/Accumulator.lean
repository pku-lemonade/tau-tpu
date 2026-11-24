/-
Exercise file. Generated from Tau/Proofs/Blocks/Accumulator.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/Blocks/Accumulator.lean.
Build this file alone with:

    lake build Exercises.Blocks.Accumulator
-/

import Tau.Blocks.Accumulator
import Tau.Proofs.Blocks.Basic

/-!
# Accumulator: proofs

The main result is `accumulator_outAt_add`: an accumulator that is told to add
on every cycle outputs, at cycle `t`, the sum of the first `t` inputs.
-/

namespace Tau

variable {α : Type} [Add α]

theorem accumulator_step (zero : α) (s : α) (c : AccIn α) :
    (accumulator zero).step s c =
      match c with
      | .hold => (s, s)
      | .add x => (s + x, s)
      | .clear => (zero, s) := rfl

/-- The output of an accumulator is its total at the start of the cycle. -/
theorem accumulator_outAt (zero : α) (inp : Signal (AccIn α)) (t : Nat) :
    (accumulator zero).outAt inp t = (accumulator zero).stateAt inp t := by
  sorry

/-- After `t` cycles of adding, the total is the sum of the first `t` inputs. -/
theorem accumulator_stateAt_add (zero : α) (x : Signal α) (t : Nat) :
    (accumulator zero).stateAt (fun k => .add (x k)) t = sumTo zero x t := by
  sorry

/-- An accumulator told to add on every cycle outputs, at cycle `t`, the sum of
the first `t` inputs. -/
theorem accumulator_outAt_add (zero : α) (x : Signal α) (t : Nat) :
    (accumulator zero).outAt (fun k => .add (x k)) t = sumTo zero x t := by
  sorry

end Tau
