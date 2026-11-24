/-
Exercise file. Generated from Tau/Proofs/Passes/Unroll.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/Passes/Unroll.lean.
Build this file alone with:

    lake build Exercises.Passes.Unroll
-/

import Tau.Passes.Unroll

/-!
# Loop unrolling: proofs

The main result is `Kernel.exec_unroll`: running the unrolled statements does
exactly what running the kernel does. It holds for every `Sem`, every starting
environment, and includes the cases where the kernel fails.
-/

namespace Tau

variable {V : Type}

/-- Once the loop index is fixed to `k`, the iteration no longer matters. -/
theorem Idx.eval_inst (k i : Nat) (ix : Idx) : (ix.inst k).eval i = ix.eval k := by
  sorry

/-- A statement with its loop index fixed to `k` does, on any iteration, what
the original does on iteration `k`. -/
theorem Stmt.exec_inst (S : Sem V) (k i : Nat) (env : Env V) (s : Stmt) :
    (s.inst k).exec S i env = s.exec S k env := by
  sorry

/-- Running two lists of statements one after the other. -/
theorem execStmts_append (S : Sem V) (i : Nat) (env : Env V) (a b : List Stmt) :
    execStmts S i env (a ++ b) =
      match execStmts S i env a with
      | some env' => execStmts S i env' b
      | none => none := by
  sorry

theorem execStmts_map_inst (S : Sem V) (k i : Nat) (env : Env V) (body : List Stmt) :
    execStmts S i env (body.map (Stmt.inst k)) = execStmts S k env body := by
  sorry

/-- A loop written out does what the loop does. -/
theorem execStmts_unrollLoop (S : Sem V) (i : Nat) (env : Env V) (body : List Stmt)
    (n : Nat) : execStmts S i env (unrollLoop body n) = execLoop S body n env := by
  sorry

theorem Item.exec_unroll (S : Sem V) (i : Nat) (env : Env V) (it : Item) :
    execStmts S i env it.unroll = it.exec S env := by
  sorry

/-- Unrolling does not change what a kernel computes. -/
theorem Kernel.exec_unroll (S : Sem V) (i : Nat) (env : Env V) (k : Kernel) :
    execStmts S i env k.unroll = Kernel.exec S env k := by
  sorry

/-- A kernel made only of statements runs them in order. -/
theorem Kernel.exec_stmts (S : Sem V) (env : Env V) (l : List Stmt) :
    Kernel.exec S env (l.map Item.stmt) = execStmts S 0 env l := by
  sorry

/-- The unrolled kernel computes the same buffers as the original. -/
theorem Kernel.run_unroll (S : Sem V) (k : Kernel) (bufs : List (List V)) :
    Kernel.run S (k.unroll.map Item.stmt) bufs = k.run S bufs := by
  sorry

end Tau
