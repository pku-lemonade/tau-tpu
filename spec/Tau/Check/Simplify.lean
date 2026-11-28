import Tau.Check.Expr

/-!
# Simplifying expressions

Rewrites an expression into a simpler one that has the same value:

* `relu (relu a)` becomes `relu a`,
* `max a a` and `min a a` become `a`.

Every check uses it (`sameExprs` in `Tau.Check.Checker`): two programs
are accepted as equal if their expressions are the same after simplifying.
The compiler's `tau-simplify` pass makes the same three rewrites on a kernel,
which is why its output is accepted.

The rewrites are only valid if the operations obey certain laws
(`Sem.Lawful`). The proof that simplifying does not change an expression's
value, and the proof that real words obey the laws, are in
`Tau.Proofs.Check.Simplify`.

Terms to look up: *peephole optimization*.
-/

namespace Tau

/-- The laws the simplifier relies on. -/
structure Sem.Lawful {V : Type} (S : Sem V) : Prop where
  /-- The operations give values of the right number of words. -/
  sized : S.Sized
  /-- Applying `relu` twice is the same as applying it once. -/
  relu_relu : ∀ ty a, S.un ty .relu (S.un ty .relu a) = S.un ty .relu a
  /-- The maximum of a value with itself is that value. -/
  max_self : ∀ ty a, a.length = ty.bytes → S.bin ty .max a a = a
  /-- The minimum of a value with itself is that value. -/
  min_self : ∀ ty a, a.length = ty.bytes → S.bin ty .min a a = a

/-- Simplify a one-value operation whose operand is already simplified. -/
def simpUn (ty : DType) (op : UnOp) (a : VExpr) : VExpr :=
  match op, a with
  | .relu, .un ty' .relu a' => if ty' = ty then .un ty .relu a' else .un ty op a
  | _, _ => .un ty op a

/-- Simplify a two-value operation whose operands are already simplified. -/
def simpBin (ty : DType) (op : BinOp) (a b : VExpr) : VExpr :=
  if (op = .max ∨ op = .min) ∧ a = b ∧ a.width = ty.bytes then a else .bin ty op a b

mutual

/-- Simplify the expression of a word: simplify the value it is a word of. -/
def Expr.simp : Expr → Expr
  | .word k v => .word k v.simp
  | e => e

/-- Simplify the expression of a value, innermost parts first. -/
def VExpr.simp : VExpr → VExpr
  | .words ws => .words ws.simp
  | .un ty op a => simpUn ty op a.simp
  | .bin ty op a b => simpBin ty op a.simp b.simp
  | .matvec rows x => .matvec rows.simp x.simp
  | .sel ty m a b => .sel ty m.simp a.simp b.simp
  | .const ty xs => .const ty xs

/-- Simplify every word of a list. -/
def Exprs.simp : Exprs → Exprs
  | .nil => .nil
  | .cons e rest => .cons e.simp rest.simp

end

end Tau
