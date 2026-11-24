/-
Exercise file. Generated from Tau/Proofs/IR/Map.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/IR/Map.lean.
Build this file alone with:

    lake build Exercises.IR.Map
-/

import Tau.IR.Kernel

/-!
# A kernel does not look at its values

The same fact as `Tau/Proofs/SliceLevel/Map.lean`, for kernels: a function `f`
that respects the operations commutes with running a kernel. Whether a kernel
fails depends only on the kernel and the buffer sizes, never on the values.

The main result is `Kernel.run_map`.
-/

namespace Tau

variable {V W : Type}

/-- Apply `f` to every value in an environment. -/
def Env.map (f : V → W) (env : Env V) : Env W where
  vars := env.vars.map (Prod.map id f)
  bufs := env.bufs.map (List.map f)

theorem lookup_map (f : V → W) (v : Var) (l : List (Var × V)) :
    (l.map (Prod.map id f)).lookup v = (l.lookup v).map f := by
  sorry

theorem Env.bind_map (f : V → W) (env : Env V) (v : Var) (x : V) :
    (env.map f).bind v (f x) = (env.bind v x).map f := rfl

theorem bufGet_map (f : V → W) (bufs : List (List V)) (b k : Nat) :
    ((bufs.map (List.map f))[b]?.getD [])[k]? = ((bufs[b]?.getD [])[k]?).map f := by
  sorry

theorem matvecFrom_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (x : V)
    (cols : Nat → Option V) (init : V) (n : Nat) :
    matvecFrom T (f x) (fun j => (cols j).map f) (f init) n =
      (matvecFrom S x cols init n).map f := by
  sorry

theorem Stmt.exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (i : Nat)
    (env : Env V) (s : Stmt) :
    s.exec T i (env.map f) = (s.exec S i env).map (Env.map f) := by
  -- Outline of one proof:
  -- One case per statement. Rewrite the fields of the mapped environment as
  -- maps (`hb`, `hv`), move the map out of each lookup, and split on what
  -- the lookups found.
  sorry

theorem execStmts_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (i : Nat)
    (env : Env V) (body : List Stmt) :
    execStmts T i (env.map f) body = (execStmts S i env body).map (Env.map f) := by
  sorry

theorem execLoop_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f)
    (body : List Stmt) (n : Nat) (env : Env V) :
    execLoop T body n (env.map f) = (execLoop S body n env).map (Env.map f) := by
  sorry

theorem Kernel.exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f)
    (env : Env V) (k : Kernel) :
    Kernel.exec T (env.map f) k = (Kernel.exec S env k).map (Env.map f) := by
  sorry

/-- Running a kernel on mapped buffers gives the mapped result, and fails in
exactly the same cases. -/
theorem Kernel.run_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (k : Kernel)
    (bufs : List (List V)) :
    k.run T (bufs.map (List.map f)) = (k.run S bufs).map (List.map (List.map f)) := by
  sorry

end Tau
