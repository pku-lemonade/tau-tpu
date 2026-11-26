import Tau.Check.Simplify
import Tau.Proofs.Isa.Word

/-!
# Simplification: proofs

Two results.

* `Expr.denote_simp`: simplifying an expression does not change its value,
  for any operations that obey the laws in `Sem.Lawful`.
* `wordSem_lawful`: the operations on real words obey those laws. The facts
  about single lanes are in `spec/Tau/Proofs/Isa/Word.lean`.
-/

namespace Tau

variable {V : Type}

theorem denote_simpUn (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V)
    (op : UnOp) (a : Expr) :
    (simpUn op a).denote S bufs fill = S.un op (a.denote S bufs fill) := by
  unfold simpUn
  split
  · simp only [Expr.denote, hS.relu_relu]
  · rfl

theorem denote_simpBin (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V)
    (op : BinOp) (a b : Expr) :
    (simpBin op a b).denote S bufs fill =
      S.bin op (a.denote S bufs fill) (b.denote S bufs fill) := by
  unfold simpBin
  split
  · rename_i h
    obtain ⟨hop, rfl⟩ := h
    cases hop with
    | inl h => subst h; exact (hS.max_self _).symm
    | inr h => subst h; exact (hS.min_self _).symm
  · rfl

/-- Simplifying an expression does not change its value. -/
theorem Expr.denote_simp (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V)
    (e : Expr) : e.simp.denote S bufs fill = e.denote S bufs fill := by
  induction e with
  | init buf idx => rfl
  | fill => rfl
  | zero => rfl
  | un op a ih => simp only [Expr.simp, denote_simpUn S hS, ih, Expr.denote]
  | bin op a b iha ihb => simp only [Expr.simp, denote_simpBin S hS, iha, ihb, Expr.denote]
  | mac j acc x w iha ihx ihw => simp only [Expr.simp, Expr.denote, iha, ihx, ihw]
  | const xs => rfl
  | sel m a b ihm iha ihb => simp only [Expr.simp, Expr.denote, ihm, iha, ihb]

/-! ## Real words obey the laws -/

theorem wordSem_lawful (lanes : Nat) : (wordSem lanes).Lawful where
  relu_relu a := by
    apply Vector.ext
    intro i hi
    simp [wordSem, Lane.relu_relu]
  max_self a := by
    apply Vector.ext
    intro i hi
    simp [wordSem, Lane.max_self]
  min_self a := by
    apply Vector.ext
    intro i hi
    simp [wordSem, Lane.min_self]

end Tau
