import Tau.IR.Kernel

/-!
# Pass: loop unrolling

Replaces every loop by copies of its body, one per iteration, with the loop
index filled in. The result has no loops.

This is the Lean model of the compiler's `tau-unroll` pass. The proof that it
does not change what a kernel computes is in `Tau/Proofs/Passes/Unroll.lean`.

Docs: Compiler 4, Programs 3 (`Tau/Docs/`).
-/

namespace Tau

/-- Fix the loop index of an index expression to `k`. -/
def Idx.inst (k : Nat) (ix : Idx) : Idx := ⟨ix.eval k, 0⟩

/-- Fix the loop index of a statement to `k`. -/
def Stmt.inst (k : Nat) : Stmt → Stmt
  | .load dst buf ix => .load dst buf (ix.inst k)
  | .store src buf ix => .store src buf (ix.inst k)
  | .un dst op a => .un dst op a
  | .bin dst op a b => .bin dst op a b
  | .matvec dst x buf ix n => .matvec dst x buf (ix.inst k) n
  | .affine dst x bias buf ix n => .affine dst x bias buf (ix.inst k) n
  | .const dst xs => .const dst xs
  | .sel dst m a b => .sel dst m a b
  | .pin t s => .pin (t.inst k) (s.inst k)

/-- The first `n` iterations of a loop body, written out. -/
def unrollLoop (body : List Stmt) : Nat → List Stmt
  | 0 => []
  | n + 1 => unrollLoop body n ++ body.map (Stmt.inst n)

/-- An item with any loop written out. -/
def Item.unroll : Item → List Stmt
  | .stmt s => [s.inst 0]
  | .loop n body => unrollLoop body n

/-- A kernel with every loop written out. -/
def Kernel.unroll : Kernel → List Stmt
  | [] => []
  | it :: rest => it.unroll ++ Kernel.unroll rest

end Tau
