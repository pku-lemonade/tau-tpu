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
  unfold Block.outAt
  rw [accumulator_step]
  split <;> rfl

/-- After `t` cycles of adding, the total is the sum of the first `t` inputs. -/
theorem accumulator_stateAt_add (zero : α) (x : Signal α) (t : Nat) :
    (accumulator zero).stateAt (fun k => .add (x k)) t = sumTo zero x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Block.stateAt_succ, ih]
    rfl

/-- An accumulator told to add on every cycle outputs, at cycle `t`, the sum of
the first `t` inputs. -/
theorem accumulator_outAt_add (zero : α) (x : Signal α) (t : Nat) :
    (accumulator zero).outAt (fun k => .add (x k)) t = sumTo zero x t := by
  rw [accumulator_outAt, accumulator_stateAt_add]

end Tau
