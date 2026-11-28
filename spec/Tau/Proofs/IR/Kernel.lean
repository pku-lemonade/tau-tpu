import Tau.IR.Kernel
import Tau.Proofs.Isa.Event

/-!
# A kernel does not look at its values

The same fact as `Tau.Proofs.Machine.SliceLevel`, for kernels: a function `f`
that respects the operations commutes with running a kernel. Whether a kernel
fails depends only on the kernel and the buffer sizes, never on the values.

The main result is `Kernel.run_map`.
-/

namespace Tau

variable {V W : Type}

/-- Apply `f` to every word in an environment. -/
def Env.map (f : V → W) (env : Env V) : Env W where
  vars := env.vars.map (Prod.map id (List.map f))
  bufs := env.bufs.map (List.map f)
  events := env.events.map (Event.map f)

theorem lookup_map {α β : Type} (f : α → β) (v : Var) (l : List (Var × α)) :
    (l.map (Prod.map id f)).lookup v = (l.lookup v).map f := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, x⟩ := e
    simp only [List.map_cons, Prod.map, id, List.lookup]
    split
    · rfl
    · exact ih

theorem Env.bind_map (f : V → W) (env : Env V) (v : Var) (x : List V) :
    (env.map f).bind v (x.map f) = (env.bind v x).map f := rfl

theorem Env.get_map (f : V → W) (env : Env V) (ty : DType) (v : Var) :
    (env.map f).get ty v = (env.get ty v).map (List.map f) := by
  unfold Env.get
  have hv : (env.map f).vars = env.vars.map (Prod.map id (List.map f)) := rfl
  rw [hv, lookup_map]
  cases env.vars.lookup v with
  | none => rfl
  | some x =>
    simp only [Option.map_some, List.length_map]
    split <;> rfl

theorem Env.word_map (f : V → W) (env : Env V) (v : Var) :
    (env.map f).word v = (env.word v).map f := by
  unfold Env.word
  have hv : (env.map f).vars = env.vars.map (Prod.map id (List.map f)) := rfl
  rw [hv, lookup_map]
  cases env.vars.lookup v with
  | none => rfl
  | some x =>
    cases x with
    | nil => rfl
    | cons w rest => cases rest <;> rfl

theorem eventsOf_map (f : V → W) (t : Nat) (store : Option (Nat × Nat)) (x : List V) :
    eventsOf t store (x.map f) = (eventsOf t store x).map (Event.map f) := by
  simp only [eventsOf, List.length_map, List.zipWith_map_right, List.map_zipWith]
  rfl

theorem Env.issue_map (f : V → W) (env : Env V) (t : Nat) (target : Var × Option (Nat × Nat)) :
    (env.map f).issue t target = (env.issue t target).map f := by
  unfold Env.issue
  have hv : (env.map f).vars = env.vars.map (Prod.map id (List.map f)) := rfl
  rw [hv, lookup_map]
  cases env.vars.lookup target.1 with
  | none => rfl
  | some x => simp [Env.map, eventsOf_map]

theorem bufGet_map (f : V → W) (bufs : List (List V)) (b : Nat) :
    (bufs.map (List.map f))[b]?.getD [] = (bufs[b]?.getD []).map f := by
  rw [List.getElem?_map]
  cases bufs[b]? <;> rfl

theorem Stmt.exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (i : Nat)
    (env : Env V) (s : Stmt) :
    s.exec T i (env.map f) = (s.exec S i env).map (Env.map f) := by
  -- One case per statement. Rewrite the buffers of the mapped environment
  -- as a map (`hb`), move the map out of each lookup (`Env.get_map`,
  -- `wordsAt_map`), and split on what the lookups found. Where a value is
  -- computed, `h` says `f` commutes with the operation. A pinned statement
  -- is the statement inside it, then `Env.issue_map`.
  have hb : (env.map f).bufs = env.bufs.map (List.map f) := rfl
  induction s generalizing env with
  | pin t s ih =>
    simp only [Stmt.exec, ih env rfl]
    cases s.exec S i env with
    | none => rfl
    | some env' => simp only [Option.map_some, Env.issue_map]
  | load dst ty buf ix =>
    simp only [Stmt.exec, hb, bufGet_map, wordsAt_map]
    cases wordsAt (env.bufs[buf]?.getD []) (ty.bytes * ix.eval i) ty.bytes <;> rfl
  | store src ty buf ix =>
    simp only [Stmt.exec, Env.get_map, hb, List.getElem?_map]
    cases env.get ty src <;> cases env.bufs[buf]? <;>
      simp [Env.map, List.map_set, putAt_map]
  | un dst ty op a =>
    simp only [Stmt.exec, Env.get_map]
    cases env.get ty a with
    | none => rfl
    | some x => simp only [Option.map_some, ← h.un]; rfl
  | bin dst ty op a b =>
    simp only [Stmt.exec, Env.get_map]
    cases env.get ty a with
    | none => rfl
    | some x =>
      cases env.get ty b with
      | none => rfl
      | some y => simp only [Option.map_some, ← h.bin]; rfl
  | matvec dst x buf ix n =>
    simp only [Stmt.exec, Env.word_map, hb, bufGet_map, wordsAt_map]
    cases env.word x with
    | none => rfl
    | some w =>
      cases wordsAt (env.bufs[buf]?.getD []) (ix.eval i) n with
      | none => rfl
      | some rows => simp only [Option.map_some, ← h.matvec]; rfl
  | const dst ty xs =>
    simp only [Stmt.exec, Option.map_some, ← h.const]
    rfl
  | sel dst ty m a b =>
    simp only [Stmt.exec, Env.get_map]
    cases env.get ty m with
    | none => rfl
    | some vm =>
      cases env.get ty a with
      | none => rfl
      | some va =>
        cases env.get ty b with
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
