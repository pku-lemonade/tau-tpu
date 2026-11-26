import Tau.IR.Kernel

/-!
# A kernel does not look at its values

The same fact as `Tau.Proofs.Machine.Arch`, for kernels: a function `f`
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
  events := env.events.map (Event.map f)

theorem lookup_map (f : V → W) (v : Var) (l : List (Var × V)) :
    (l.map (Prod.map id f)).lookup v = (l.lookup v).map f := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, x⟩ := e
    simp only [List.map_cons, Prod.map, id, List.lookup]
    split
    · rfl
    · exact ih

theorem Env.bind_map (f : V → W) (env : Env V) (v : Var) (x : V) :
    (env.map f).bind v (f x) = (env.bind v x).map f := rfl

theorem Env.issue_map (f : V → W) (env : Env V) (t : Nat) (target : Var × Option (Nat × Nat)) :
    (env.map f).issue t target = (env.issue t target).map f := by
  unfold Env.issue
  have hv : (env.map f).vars = env.vars.map (Prod.map id f) := rfl
  rw [hv, lookup_map]
  cases env.vars.lookup target.1 <;> rfl

theorem bufGet_map (f : V → W) (bufs : List (List V)) (b k : Nat) :
    ((bufs.map (List.map f))[b]?.getD [])[k]? = ((bufs[b]?.getD [])[k]?).map f := by
  simp only [List.getElem?_map]
  cases bufs[b]? with
  | none => rfl
  | some l => simp

theorem matvecFrom_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (x : V)
    (cols : Nat → Option V) (init : V) (n : Nat) :
    matvecFrom T (f x) (fun j => (cols j).map f) (f init) n =
      (matvecFrom S x cols init n).map f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [matvecFrom, ih]
    cases matvecFrom S x cols init n <;> cases cols n <;> simp [h.mac]

theorem Stmt.exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (i : Nat)
    (env : Env V) (s : Stmt) :
    s.exec T i (env.map f) = (s.exec S i env).map (Env.map f) := by
  -- One case per statement. Rewrite the fields of the mapped environment as
  -- maps (`hb`, `hv`), move the map out of each lookup, and split on what
  -- the lookups found. A pinned statement is the statement inside it, then
  -- `Env.issue_map`.
  induction s generalizing env with
  | pin t s ih =>
    simp only [Stmt.exec, ih]
    cases s.exec S i env with
    | none => rfl
    | some env' => simp only [Option.map_some, Env.issue_map]
  | load dst buf ix =>
    simp only [Stmt.exec]
    have hb : (env.map f).bufs = env.bufs.map (List.map f) := rfl
    rw [hb, bufGet_map]
    cases (env.bufs[buf]?.getD [])[ix.eval i]? <;> rfl
  | store src buf ix =>
    simp only [Stmt.exec]
    have hb : (env.map f).bufs = env.bufs.map (List.map f) := rfl
    have hv : (env.map f).vars = env.vars.map (Prod.map id f) := rfl
    rw [hb, hv, lookup_map, List.getElem?_map]
    cases env.vars.lookup src <;> cases env.bufs[buf]? <;>
      simp [Env.map, List.map_set]
  | un dst op a =>
    simp only [Stmt.exec]
    have hv : (env.map f).vars = env.vars.map (Prod.map id f) := rfl
    rw [hv, lookup_map]
    cases env.vars.lookup a with
    | none => rfl
    | some v => simp only [Option.map_some, ← h.un]; rfl
  | bin dst op a b =>
    simp only [Stmt.exec]
    have hv : (env.map f).vars = env.vars.map (Prod.map id f) := rfl
    rw [hv, lookup_map, lookup_map]
    cases env.vars.lookup a with
    | none => rfl
    | some va =>
      cases env.vars.lookup b with
      | none => rfl
      | some vb => simp only [Option.map_some, ← h.bin]; rfl
  | matvec dst x buf ix n =>
    simp only [Stmt.exec]
    have hb : (env.map f).bufs = env.bufs.map (List.map f) := rfl
    have hv : (env.map f).vars = env.vars.map (Prod.map id f) := rfl
    rw [hb, hv, lookup_map]
    cases env.vars.lookup x with
    | none => rfl
    | some xv =>
      simp only [Option.map_some, bufGet_map, ← h.zero, matvecFrom_map S T f h]
      cases matvecFrom S xv (fun j => (env.bufs[buf]?.getD [])[ix.eval i + j]?) S.zero n <;> rfl
  | affine dst x bias buf ix n =>
    simp only [Stmt.exec]
    have hb : (env.map f).bufs = env.bufs.map (List.map f) := rfl
    have hv : (env.map f).vars = env.vars.map (Prod.map id f) := rfl
    rw [hb, hv, lookup_map, lookup_map]
    cases env.vars.lookup x with
    | none => rfl
    | some xv =>
      cases env.vars.lookup bias with
      | none => rfl
      | some bv =>
        simp only [Option.map_some, bufGet_map, matvecFrom_map S T f h]
        cases matvecFrom S xv (fun j => (env.bufs[buf]?.getD [])[ix.eval i + j]?) bv n <;> rfl
  | const dst xs =>
    simp only [Stmt.exec, Option.map_some, ← h.const]
    rfl
  | sel dst m a b =>
    simp only [Stmt.exec]
    have hv : (env.map f).vars = env.vars.map (Prod.map id f) := rfl
    rw [hv, lookup_map, lookup_map, lookup_map]
    cases env.vars.lookup m with
    | none => rfl
    | some vm =>
      cases env.vars.lookup a with
      | none => rfl
      | some va =>
        cases env.vars.lookup b with
        | none => rfl
        | some vb => simp only [Option.map_some, ← h.sel]; rfl

theorem execStmts_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (i : Nat)
    (env : Env V) (body : List Stmt) :
    execStmts T i (env.map f) body = (execStmts S i env body).map (Env.map f) := by
  induction body generalizing env with
  | nil => rfl
  | cons s rest ih =>
    simp only [execStmts, Stmt.exec_map S T f h]
    cases s.exec S i env with
    | none => rfl
    | some env' => exact ih env'

theorem execLoop_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f)
    (body : List Stmt) (n : Nat) (env : Env V) :
    execLoop T body n (env.map f) = (execLoop S body n env).map (Env.map f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [execLoop, ih]
    cases execLoop S body n env with
    | none => rfl
    | some env' => exact execStmts_map S T f h n env' body

theorem Item.exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (env : Env V)
    (it : Item) : it.exec T (env.map f) = (it.exec S env).map (Env.map f) := by
  cases it with
  | stmt s => exact Stmt.exec_map S T f h 0 env s
  | loop n body => exact execLoop_map S T f h body n env

theorem Kernel.exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f)
    (env : Env V) (k : Kernel) :
    Kernel.exec T (env.map f) k = (Kernel.exec S env k).map (Env.map f) := by
  induction k generalizing env with
  | nil => rfl
  | cons it rest ih =>
    simp only [Kernel.exec, Item.exec_map S T f h]
    cases it.exec S env with
    | none => rfl
    | some env' => exact ih env'

/-- Running a kernel on mapped buffers gives the mapped result, and fails in
exactly the same cases. -/
theorem Kernel.run_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (k : Kernel)
    (bufs : List (List V)) :
    k.run T (bufs.map (List.map f)) = (k.run S bufs).map (List.map (List.map f)) := by
  unfold Kernel.run
  have he : (⟨[], bufs.map (List.map f), []⟩ : Env W) = (⟨[], bufs, []⟩ : Env V).map f := rfl
  rw [he, Kernel.exec_map S T f h]
  cases Kernel.exec S ⟨[], bufs, []⟩ k <;> rfl

/-- The timeline of a kernel on mapped buffers is the mapped timeline. -/
theorem Kernel.timeline_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (k : Kernel)
    (bufs : List (List V)) :
    k.timeline T (bufs.map (List.map f)) = (k.timeline S bufs).map (Event.map f) := by
  unfold Kernel.timeline
  have he : (⟨[], bufs.map (List.map f), []⟩ : Env W) = (⟨[], bufs, []⟩ : Env V).map f := rfl
  rw [he, Kernel.exec_map S T f h]
  cases Kernel.exec S ⟨[], bufs, []⟩ k <;> rfl

end Tau
