import Tau.IR.Expr

/-!
# Pass: simplification

Rewrites an expression into a simpler one that has the same value:

* `relu (relu a)` becomes `relu a`,
* `max a a` and `min a a` become `a`.

This is the Lean model of the compiler's `tau-simplify` pass. The rewrites are
only valid if the operations obey certain laws (`Sem.Lawful`). The proof that
simplifying does not change an expression's value, and the proof that real
words obey the laws, are in `Tau/Proofs/Passes/Simplify.lean`.

Terms to look up: *peephole optimization*.
-/

namespace Tau

/-- The laws the simplifier relies on. -/
structure Sem.Lawful {V : Type} (S : Sem V) : Prop where
  /-- Applying `relu` twice is the same as applying it once. -/
  relu_relu : ∀ a, S.un .relu (S.un .relu a) = S.un .relu a
  /-- The maximum of a value with itself is that value. -/
  max_self : ∀ a, S.bin .max a a = a
  /-- The minimum of a value with itself is that value. -/
  min_self : ∀ a, S.bin .min a a = a

/-- Simplify a one-word operation whose operand is already simplified. -/
def simpUn : UnOp → Expr → Expr
  | .relu, .un .relu a => .un .relu a
  | op, a => .un op a

/-- Simplify a two-word operation whose operands are already simplified. -/
def simpBin (op : BinOp) (a b : Expr) : Expr :=
  if (op = .max ∨ op = .min) ∧ a = b then a else .bin op a b

/-- Simplify an expression, innermost parts first. -/
def Expr.simp : Expr → Expr
  | .un op a => simpUn op a.simp
  | .bin op a b => simpBin op a.simp b.simp
  | .mac j acc x w => .mac j acc.simp x.simp w.simp
  | .sel m a b => .sel m.simp a.simp b.simp
  | e => e

end Tau
