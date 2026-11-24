import Tau.Blocks.Mac
import Tau.Proofs.Blocks.Accumulator

/-!
# MAC: proofs

The main result is `mac_outAt_add`: a MAC cell fed one pair per cycle outputs,
at cycle `t`, the dot product of the first `t` pairs.

The proof does no new induction. A MAC is an accumulator behind a multiplier,
so the accumulator theorem and `Block.stateAt_mapIn` do all the work.
-/

namespace Tau

variable {α : Type} [Add α] [Mul α]

/-- After `t` cycles the total is `a 0 * b 0 + ... + a (t-1) * b (t-1)`. -/
theorem mac_stateAt_add (zero : α) (a b : Signal α) (t : Nat) :
    (mac zero).stateAt (fun k => .add (a k, b k)) t =
      sumTo zero (fun k => a k * b k) t := by
  unfold mac
  rw [Block.stateAt_mapIn]
  exact accumulator_stateAt_add zero (fun k => a k * b k) t

/-- A MAC cell fed one pair per cycle outputs, at cycle `t`, the dot product of
the first `t` pairs. -/
theorem mac_outAt_add (zero : α) (a b : Signal α) (t : Nat) :
    (mac zero).outAt (fun k => .add (a k, b k)) t =
      sumTo zero (fun k => a k * b k) t := by
  unfold mac
  rw [Block.outAt_mapIn]
  exact accumulator_outAt_add zero (fun k => a k * b k) t

end Tau
