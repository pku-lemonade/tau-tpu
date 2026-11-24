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
  simp [Idx.inst, Idx.eval]

/-- A statement with its loop index fixed to `k` does, on any iteration, what
the original does on iteration `k`. -/
theorem Stmt.exec_inst (S : Sem V) (k i : Nat) (env : Env V) (s : Stmt) :
    (s.inst k).exec S i env = s.exec S k env := by
  cases s <;> simp [Stmt.inst, Stmt.exec, Idx.eval_inst]

/-- Running two lists of statements one after the other. -/
theorem execStmts_append (S : Sem V) (i : Nat) (env : Env V) (a b : List Stmt) :
    execStmts S i env (a ++ b) =
      match execStmts S i env a with
      | some env' => execStmts S i env' b
      | none => none := by
  induction a generalizing env with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.cons_append, execStmts]
    cases s.exec S i env with
    | none => rfl
    | some env' => exact ih env'

theorem execStmts_map_inst (S : Sem V) (k i : Nat) (env : Env V) (body : List Stmt) :
    execStmts S i env (body.map (Stmt.inst k)) = execStmts S k env body := by
  induction body generalizing env with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, execStmts, Stmt.exec_inst]
    cases s.exec S k env with
    | none => rfl
    | some env' => exact ih env'

/-- A loop written out does what the loop does. -/
theorem execStmts_unrollLoop (S : Sem V) (i : Nat) (env : Env V) (body : List Stmt)
    (n : Nat) : execStmts S i env (unrollLoop body n) = execLoop S body n env := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [unrollLoop, execLoop, execStmts_append, ih]
    cases execLoop S body n env with
    | none => rfl
    | some env' => exact execStmts_map_inst S n i env' body

theorem Item.exec_unroll (S : Sem V) (i : Nat) (env : Env V) (it : Item) :
    execStmts S i env it.unroll = it.exec S env := by
  cases it with
  | stmt s =>
    simp only [Item.unroll, execStmts, Stmt.exec_inst, Item.exec]
    cases s.exec S 0 env <;> rfl
  | loop n body => exact execStmts_unrollLoop S i env body n

/-- Unrolling does not change what a kernel computes. -/
theorem Kernel.exec_unroll (S : Sem V) (i : Nat) (env : Env V) (k : Kernel) :
    execStmts S i env k.unroll = Kernel.exec S env k := by
  induction k generalizing env with
  | nil => rfl
  | cons it rest ih =>
    simp only [Kernel.unroll, Kernel.exec, execStmts_append, Item.exec_unroll]
    cases it.exec S env with
    | none => rfl
    | some env' => exact ih env'

/-- A kernel made only of statements runs them in order. -/
theorem Kernel.exec_stmts (S : Sem V) (env : Env V) (l : List Stmt) :
    Kernel.exec S env (l.map Item.stmt) = execStmts S 0 env l := by
  induction l generalizing env with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, Kernel.exec, Item.exec, execStmts]
    cases s.exec S 0 env with
    | none => rfl
    | some env' => exact ih env'

/-- The unrolled kernel computes the same buffers as the original. -/
theorem Kernel.run_unroll (S : Sem V) (k : Kernel) (bufs : List (List V)) :
    Kernel.run S (k.unroll.map Item.stmt) bufs = k.run S bufs := by
  unfold Kernel.run
  rw [Kernel.exec_stmts, Kernel.exec_unroll]

end Tau
