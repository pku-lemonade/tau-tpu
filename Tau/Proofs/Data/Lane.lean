import Tau.Data.Word
import Std.Tactic.BVDecide

/-!
# Facts about single lanes

Two ways to prove a fact about 32-bit values.

The first three facts are the laws the simplifier relies on
(`Sem.Lawful` in `Tau/Check/Simplify.lean`). They are proved by splitting on
the comparison and letting `simp_all` finish.

The rest are proved by `bv_decide`. It turns the statement into a question
about 32 bits per variable, hands it to a SAT solver, and checks the solver's
certificate. It needs no insight, and it gives a counterexample when the
statement is false. The price is trust: a `bv_decide` proof relies on Lean's
compiler being correct, which shows up as an extra axiom in `#print axioms`.
For that reason the end-to-end theorem uses only the first three facts.

Terms to look up: *SAT solver*, *bit-blasting*.
-/

namespace Tau.Lane

/-! ## Laws used by the simplifier -/

theorem relu_relu (a : Lane) : relu (relu a) = relu a := by
  unfold relu
  by_cases h : a.slt 0 = true <;> simp_all

theorem max_self (a : Lane) : max a a = a := by
  unfold max
  split <;> rfl

theorem min_self (a : Lane) : min a a = a := by
  unfold min
  split <;> rfl

/-! ## The same kind of fact, by `bv_decide` -/

theorem max_comm (a b : Lane) : max a b = max b a := by
  unfold max
  bv_decide

theorem min_comm (a b : Lane) : min a b = min b a := by
  unfold min
  bv_decide

/-- `relu` never returns a negative value. -/
theorem relu_nonneg (a : Lane) : (relu a).slt 0 = false := by
  unfold relu
  bv_decide

/-- `relu a` is the larger of `a` and zero. -/
theorem relu_eq_max (a : Lane) : relu a = max a 0 := by
  unfold relu max
  bv_decide

/-- `requant` always returns a value from -128 to 127. -/
theorem requant_range (k : Nat) (a : Lane) :
    (requant k a).slt (-128) = false ∧ (127 : Lane).slt (requant k a) = false := by
  unfold requant
  bv_decide

end Tau.Lane
