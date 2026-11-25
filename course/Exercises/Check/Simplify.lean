/-
Exercise file. Generated from Tau/Proofs/Check/Simplify.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/Check/Simplify.lean.
Build this file alone with:

    lake build Exercises.Check.Simplify
-/

import Tau.Check.Simplify
import Tau.Proofs.Data.Lane

/-!
# Simplification: proofs

Two results.

* `Expr.denote_simp`: simplifying an expression does not change its value,
  for any operations that obey the laws in `Sem.Lawful`.
* `wordSem_lawful`: the operations on real words obey those laws. The facts
  about single lanes are in `Tau/Proofs/Data/Lane.lean`.
-/

namespace Tau

variable {V : Type}

theorem denote_simpUn (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V)
    (op : UnOp) (a : Expr) :
    (simpUn op a).denote S bufs fill = S.un op (a.denote S bufs fill) := by
  sorry

theorem denote_simpBin (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V)
    (op : BinOp) (a b : Expr) :
    (simpBin op a b).denote S bufs fill =
      S.bin op (a.denote S bufs fill) (b.denote S bufs fill) := by
  sorry

/-- Simplifying an expression does not change its value. -/
theorem Expr.denote_simp (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V)
    (e : Expr) : e.simp.denote S bufs fill = e.denote S bufs fill := by
  sorry

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
