/-
Exercise file. Generated from spec/Tau/Proofs/Isa/Word.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in spec/Tau/Proofs/Isa/Word.lean.
Build this file alone with:

    lake build Prove.Isa.Word
-/

import Tau.Isa.Word
import Std.Tactic.BVDecide

/-!
# Facts about elements

Two ways to prove a fact about the 32-bit elements a slice computes with.
What ties an element to the bytes it is made of is in
`Tau.Proofs.Isa.Value`.

The first three facts are the laws the simplifier relies on
(`Sem.Lawful` in `Tau.Check.Simplify`). They are proved by splitting on
the comparison and letting `simp_all` finish.

The rest are proved by `bv_decide`. It turns the statement into a question
about 32 bits per variable, hands it to a SAT solver, and checks the solver's
certificate. It needs no insight, and it gives a counterexample when the
statement is false. The price is trust: a `bv_decide` proof relies on Lean's
compiler being correct, which shows up as an extra axiom in `#print axioms`.
For that reason the end-to-end theorem uses only the first three facts.

Terms to look up: *SAT solver*, *bit-blasting*.
-/

namespace Tau.Elem

/-! ## Laws used by the simplifier -/

theorem relu_relu (a : Elem) : relu (relu a) = relu a := by
  sorry

theorem max_self (a : Elem) : max a a = a := by
  sorry

theorem min_self (a : Elem) : min a a = a := by
  sorry

/-! ## The same kind of fact, by `bv_decide` -/

theorem max_comm (a b : Elem) : max a b = max b a := by
  sorry

theorem min_comm (a b : Elem) : min a b = min b a := by
  sorry

/-- `relu` never returns a negative value. -/
theorem relu_nonneg (a : Elem) : (relu a).slt 0 = false := by
  sorry

/-- `relu a` is the larger of `a` and zero. -/
theorem relu_eq_max (a : Elem) : relu a = max a 0 := by
  sorry

/-- `requant` always returns a value from -128 to 127. -/
theorem requant_range (k : Nat) (a : Elem) :
    (requant k a).slt (-128) = false ∧ (127 : Elem).slt (requant k a) = false := by
  sorry

end Tau.Elem
