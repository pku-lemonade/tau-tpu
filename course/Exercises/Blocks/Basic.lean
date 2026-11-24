/-
Exercise file. Generated from Tau/Proofs/Blocks/Basic.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/Blocks/Basic.lean.
Build this file alone with:

    lake build Exercises.Blocks.Basic
-/

import Tau.Blocks.Basic

/-!
# Blocks: basic facts

Small facts about `stateAt`, `outAt`, `mapIn` and `sumTo` that the proofs about
individual blocks rely on.
-/

namespace Tau

namespace Block

variable {σ ι ι' ο : Type}

theorem stateAt_zero (b : Block σ ι ο) (inp : Signal ι) :
    b.stateAt inp 0 = b.init := rfl

theorem stateAt_succ (b : Block σ ι ο) (inp : Signal ι) (t : Nat) :
    b.stateAt inp (t + 1) = (b.step (b.stateAt inp t) (inp t)).1 := rfl

/-- Running `b.mapIn f` on `inp` is running `b` on `f` applied to `inp`. -/
theorem stateAt_mapIn (b : Block σ ι ο) (f : ι' → ι) (inp : Signal ι') (t : Nat) :
    (b.mapIn f).stateAt inp t = b.stateAt (fun k => f (inp k)) t := by
  sorry

theorem outAt_mapIn (b : Block σ ι ο) (f : ι' → ι) (inp : Signal ι') (t : Nat) :
    (b.mapIn f).outAt inp t = b.outAt (fun k => f (inp k)) t := by
  sorry

end Block

/-- Two sums are equal if their terms are equal. -/
theorem sumTo_congr {α : Type} [Add α] (zero : α) (f g : Nat → α) (n : Nat)
    (h : ∀ k, k < n → f k = g k) : sumTo zero f n = sumTo zero g n := by
  sorry

end Tau
