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
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [stateAt_succ, stateAt_succ, ih]
    rfl

theorem outAt_mapIn (b : Block σ ι ο) (f : ι' → ι) (inp : Signal ι') (t : Nat) :
    (b.mapIn f).outAt inp t = b.outAt (fun k => f (inp k)) t := by
  unfold outAt
  rw [stateAt_mapIn]
  rfl

end Block

/-- Two sums are equal if their terms are equal. -/
theorem sumTo_congr {α : Type} [Add α] (zero : α) (f g : Nat → α) (n : Nat)
    (h : ∀ k, k < n → f k = g k) : sumTo zero f n = sumTo zero g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold sumTo
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

end Tau
