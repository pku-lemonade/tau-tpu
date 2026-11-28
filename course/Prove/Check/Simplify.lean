/-
Exercise file. Generated from spec/Tau/Proofs/Check/Simplify.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in spec/Tau/Proofs/Check/Simplify.lean.
Only some proofs are taken out. The others are given, and you may use them.
Build this file alone with:

    lake build Prove.Check.Simplify
-/

import Tau.Check.Simplify
import Tau.Proofs.Isa.Word
import Tau.Proofs.Isa.Value

/-!
# Simplification: proofs

Two results.

* `Expr.denote_simp`: simplifying an expression does not change its value,
  for any operations that obey the laws in `Sem.Lawful`.
* `wordSem_lawful`: the operations on real words obey those laws. The facts
  about single elements are in `Tau.Proofs.Isa.Word`, and those about their
  bytes in `Tau.Proofs.Isa.Value`.
-/

namespace Tau

variable {V : Type}

/-! ## A value has as many words as its expression says -/

theorem Exprs.length_denote (S : Sem V) (bufs : List (List V)) (fill : V) :
    (ws : Exprs) → (ws.denote S bufs fill).length = ws.length
  | .nil => rfl
  | .cons e rest => by
    simp only [Exprs.denote, Exprs.length, List.length_cons,
      Exprs.length_denote S bufs fill rest]

theorem VExpr.length_denote (S : Sem V) (hS : S.Sized) (bufs : List (List V)) (fill : V)
    (v : VExpr) : (v.denote S bufs fill).length = v.width := by
  cases v <;>
    simp only [VExpr.denote, VExpr.width, hS.un, hS.bin, hS.matvec, hS.const, hS.sel,
      Exprs.length_denote]

/-! ## Simplifying keeps the value -/

theorem denote_simpUn (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V)
    (ty : DType) (op : UnOp) (a : VExpr) :
    (simpUn ty op a).denote S bufs fill = S.un ty op (a.denote S bufs fill) := by
  sorry

theorem denote_simpBin (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V)
    (ty : DType) (op : BinOp) (a b : VExpr) :
    (simpBin ty op a b).denote S bufs fill =
      S.bin ty op (a.denote S bufs fill) (b.denote S bufs fill) := by
  sorry

mutual

/-- Simplifying the expression of a word does not change the word. -/
theorem Expr.denote_simp (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V) :
    (e : Expr) → e.simp.denote S bufs fill = e.denote S bufs fill
  | .init buf idx => rfl
  | .fill => rfl
  | .zero => rfl
  | .word k v => by
    simp only [Expr.simp, Expr.denote, VExpr.denote_simp S hS bufs fill v]

/-- Simplifying the expression of a value does not change the value. -/
theorem VExpr.denote_simp (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V) :
    (v : VExpr) → v.simp.denote S bufs fill = v.denote S bufs fill
  | .words ws => by
    simp only [VExpr.simp, VExpr.denote, Exprs.denote_simp S hS bufs fill ws]
  | .un ty op a => by
    simp only [VExpr.simp, denote_simpUn S hS, VExpr.denote_simp S hS bufs fill a, VExpr.denote]
  | .bin ty op a b => by
    simp only [VExpr.simp, denote_simpBin S hS, VExpr.denote_simp S hS bufs fill a,
      VExpr.denote_simp S hS bufs fill b, VExpr.denote]
  | .matvec rows x => by
    simp only [VExpr.simp, VExpr.denote, Exprs.denote_simp S hS bufs fill rows,
      Expr.denote_simp S hS bufs fill x]
  | .const ty xs => rfl
  | .sel ty m a b => by
    simp only [VExpr.simp, VExpr.denote, VExpr.denote_simp S hS bufs fill m,
      VExpr.denote_simp S hS bufs fill a, VExpr.denote_simp S hS bufs fill b]

/-- Simplifying a list of words does not change the words. -/
theorem Exprs.denote_simp (S : Sem V) (hS : S.Lawful) (bufs : List (List V)) (fill : V) :
    (ws : Exprs) → ws.simp.denote S bufs fill = ws.denote S bufs fill
  | .nil => rfl
  | .cons e rest => by
    simp only [Exprs.simp, Exprs.denote, Expr.denote_simp S hS bufs fill e,
      Exprs.denote_simp S hS bufs fill rest]

end

/-! ## Real words obey the laws -/

theorem wordSem_sized (lanes : Nat) : (wordSem lanes).Sized where
  un ty op a := by
    simp only [wordSem]
    split
    · rename_i h
      have hout : op.out ty = ty := by cases op <;> simp_all [UnOp.kind, UnOp.out]
      simp [hout, Value.length_fit]
    · exact Value.length_ofElems _ _
  bin ty op a b := Value.length_ofElems _ _
  matvec rows x := Value.length_ofElems _ _
  const ty xs := Value.length_ofElems _ _
  sel ty m a b := Value.length_ofElems _ _

/-- `relu` of an element made of `n` bytes is made of the same `n` bytes. -/
theorem Elem.refit_relu (n : Nat) (e : Elem) (h : Elem.refit n e = e) :
    Elem.refit n (Elem.relu e) = Elem.relu e := by
  unfold Elem.relu
  split
  · exact Elem.refit_zero n
  · exact h

theorem wordSem_lawful (lanes : Nat) : (wordSem lanes).Lawful where
  sized := wordSem_sized lanes
  relu_relu ty a := by
    -- An element of the inner result is `relu` of an element made of
    -- `ty.bytes` bytes, so it is made of those bytes itself: putting the
    -- value together again gives it back, and `relu` of it is itself.
    have hn := ty.bytes_le
    simp only [wordSem, UnOp.kind, UnOp.out, UnOp.elem, Value.mapElems, reduceCtorEq,
      ↓reduceIte]
    rw [Value.fit_of_length _ _ (Value.length_ofElems _ _)]
    congr 1
    funext i
    have he := Value.refit_elem (Value.fit ty.bytes a) i (by rw [Value.length_fit]; exact hn)
    rw [Value.length_fit] at he
    rw [Value.elem_ofElems, Elem.refit_relu _ _ he, Elem.relu_relu]
  max_self ty a h := by
    simp only [wordSem, BinOp.elem, Value.zipElems, Elem.max_self,
      Value.fit_of_length _ _ h]
    rw [← h]
    exact Value.ofElems_elem a (by rw [h]; exact ty.bytes_le)
  min_self ty a h := by
    simp only [wordSem, BinOp.elem, Value.zipElems, Elem.min_self,
      Value.fit_of_length _ _ h]
    rw [← h]
    exact Value.ofElems_elem a (by rw [h]; exact ty.bytes_le)

end Tau
