import Tau.Blocks.SystolicArray
import Tau.Proofs.Blocks.Basic

/-!
# Systolic array: proofs

The main result is `systolicArray_matvec`: if the coefficient `A i j` is fed to
cell `j` at cycle `i + j`, the array outputs entry `i` of the matrix-vector
product at cycle `i + n`.

It follows from `systolicArray_stateAt`, which says what partial sum is stored
after each cell on each cycle, whatever the coefficients are.
-/

namespace Tau

variable {α : Type} [Add α] [Mul α]

theorem systolicArray_step (zero : α) {n : Nat} (x s c : Vector α n) :
    (systolicArray zero x).step s c =
      (Vector.ofFn fun j : Fin n =>
          (if j.val = 0 then zero
           else s[j.val - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt))
            + c[j] * x[j],
       if h : 0 < n then s[n - 1]'(Nat.sub_lt h Nat.zero_lt_one) else zero) := rfl

/-- The partial sum stored after cell `j` at the start of cycle `t`. It has
collected one term from each of the cells `0` to `j`, and the term from cell
`k` used the coefficient that was fed to that cell at cycle `t - 1 - j + k`. -/
theorem systolicArray_stateAt (zero : α) {n : Nat} (x : Vector α n)
    (c : Signal (Vector α n)) (j : Nat) (hj : j < n) (t : Nat) (ht : j + 1 ≤ t) :
    ((systolicArray zero x).stateAt c t)[j] =
      sumTo zero (fun k => (c (t - 1 - j + k))[k]?.getD zero * x[k]?.getD zero) (j + 1) := by
  induction j generalizing t with
  | zero =>
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [Block.stateAt_succ, systolicArray_step]
    simp [sumTo, hj]
  | succ j ih =>
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [Block.stateAt_succ, systolicArray_step]
    simp only [Vector.getElem_ofFn]
    have hterm : t + 1 - 1 - (j + 1) + (j + 1) = t := by omega
    rw [sumTo, hterm]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih (by omega) t (by omega)]
    congr 1
    · apply sumTo_congr
      intro k hk
      have hidx : t - 1 - j + k = t - (j + 1) + k := by omega
      rw [hidx]
    · simp [hj]

/-- If the coefficient `A i j` is fed to cell `j` at cycle `i + j`, the array
outputs `A i 0 * x[0] + ... + A i (n-1) * x[n-1]` at cycle `i + n`. -/
theorem systolicArray_matvec (zero : α) {n : Nat} (hn : 0 < n) (x : Vector α n)
    (A : Nat → Nat → α) (c : Signal (Vector α n))
    (hc : ∀ i j (hj : j < n), (c (i + j))[j] = A i j) (i : Nat) :
    (systolicArray zero x).outAt c (i + n) =
      sumTo zero (fun k => A i k * x[k]?.getD zero) n := by
  unfold Block.outAt
  rw [systolicArray_step]
  simp only [hn, ↓reduceDIte]
  rw [systolicArray_stateAt zero x c (n - 1) (by omega) (i + n) (by omega)]
  have hn1 : n - 1 + 1 = n := by omega
  rw [hn1]
  apply sumTo_congr
  intro k hk
  have hidx : i + n - 1 - (n - 1) + k = i + k := by omega
  rw [hidx]
  simp [hk, hc i k hk]

end Tau
