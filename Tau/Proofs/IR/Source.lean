import Tau.IR.Source
import Tau.Proofs.IR.Map

/-!
# A source program does not look at its values

The same fact as `Tau/Proofs/IR/Map.lean`, for source programs: a function
`f` that respects the operations commutes with running a source program, calls
included. Whether a call can be made depends on how many buffers there are,
never on what they hold.

The main results are `Source.run_map` and `Source.timeline_map`.
`Source.exec_ofKernel` says that a kernel, read as a source program with no
calls, does what the kernel does.
-/

namespace Tau

variable {V W : Type}

theorem Event.rebase_map (f : V → W) (args : List Nat) (origin : Nat) (e : Event V) :
    (e.map f).rebase args origin = (e.rebase args origin).map f := rfl

theorem writeBack_map (f : V → W) (bufs : List (List V)) (args : List Nat)
    (inner : List (List V)) :
    writeBack (bufs.map (List.map f)) args (inner.map (List.map f)) =
      (writeBack bufs args inner).map (List.map f) := by
  induction args generalizing bufs inner with
  | nil => cases inner <;> rfl
  | cons b args ih =>
    cases inner with
    | nil => rfl
    | cons x inner =>
      simp only [List.map_cons, writeBack]
      rw [← List.map_set, ih]

theorem Env.returnFrom_map (f : V → W) (env : Env V) (args : List Nat) (origin : Nat)
    (inner : Env V) :
    (env.map f).returnFrom args origin (inner.map f) =
      (env.returnFrom args origin inner).map f := by
  simp only [Env.returnFrom, Env.map, writeBack_map, List.map_append, List.map_map]
  congr 2

theorem Source.exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (s : Source)
    (env : Env V) : s.exec T (env.map f) = (s.exec S env).map (Env.map f) := by
  -- By induction on the program. An item: `Item.exec_map`. A call: the
  -- mapped environment has as many buffers, so the call can be made in one
  -- run exactly when it can in the other; the buffers handed over are the
  -- mapped buffers; and coming back commutes with `f` (`Env.returnFrom_map`).
  induction s generalizing env with
  | done => rfl
  | item it rest ih =>
    simp only [Source.exec, Item.exec_map S T f h]
    cases it.exec S env with
    | none => rfl
    | some env' => exact ih env'
  | call callee args origin rest ihc ihr =>
    simp only [Source.exec]
    have hlen : (env.map f).bufs.length = env.bufs.length := by simp [Env.map]
    have hin : (⟨[], args.map fun b => (env.map f).bufs[b]?.getD [], []⟩ : Env W) =
        (⟨[], args.map fun b => env.bufs[b]?.getD [], []⟩ : Env V).map f := by
      simp only [Env.map, List.map_map, List.map_nil, Env.mk.injEq, true_and, and_true]
      apply List.map_congr_left
      intro b _
      simp only [Function.comp, List.getElem?_map]
      cases env.bufs[b]? <;> rfl
    rw [hlen]
    split
    · rw [hin, ihc]
      cases callee.exec S ⟨[], args.map fun b => env.bufs[b]?.getD [], []⟩ with
      | none => rfl
      | some inner =>
        simp only [Option.map_some, Env.returnFrom_map]
        exact ihr _
    · rfl

/-- Running a source program on mapped buffers gives the mapped result, and
fails in exactly the same cases. -/
theorem Source.run_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (s : Source)
    (bufs : List (List V)) :
    s.run T (bufs.map (List.map f)) = (s.run S bufs).map (List.map (List.map f)) := by
  unfold Source.run
  have he : (⟨[], bufs.map (List.map f), []⟩ : Env W) = (⟨[], bufs, []⟩ : Env V).map f := rfl
  rw [he, Source.exec_map S T f h]
  cases s.exec S ⟨[], bufs, []⟩ <;> rfl

/-- The timeline of a source program on mapped buffers is the mapped
timeline. -/
theorem Source.timeline_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (s : Source)
    (bufs : List (List V)) :
    s.timeline T (bufs.map (List.map f)) = (s.timeline S bufs).map (Event.map f) := by
  unfold Source.timeline
  have he : (⟨[], bufs.map (List.map f), []⟩ : Env W) = (⟨[], bufs, []⟩ : Env V).map f := rfl
  rw [he, Source.exec_map S T f h]
  cases s.exec S ⟨[], bufs, []⟩ <;> rfl

/-- A kernel read as a source program does what the kernel does. -/
theorem Source.exec_ofKernel (S : Sem V) (k : Kernel) (env : Env V) :
    (Source.ofKernel k).exec S env = Kernel.exec S env k := by
  induction k generalizing env with
  | nil => rfl
  | cons it rest ih =>
    simp only [Source.ofKernel, Source.exec, Kernel.exec]
    cases it.exec S env with
    | none => rfl
    | some env' => exact ih env'

/-- A kernel read as a source program computes what the kernel computes. -/
theorem Source.run_ofKernel (S : Sem V) (k : Kernel) (bufs : List (List V)) :
    (Source.ofKernel k).run S bufs = k.run S bufs := by
  unfold Source.run Kernel.run
  rw [Source.exec_ofKernel]
  cases Kernel.exec S ⟨[], bufs, []⟩ k <;> rfl

/-- A kernel read as a source program has the kernel's timeline. -/
theorem Source.timeline_ofKernel (S : Sem V) (k : Kernel) (bufs : List (List V)) :
    (Source.ofKernel k).timeline S bufs = k.timeline S bufs := by
  unfold Source.timeline Kernel.timeline
  rw [Source.exec_ofKernel]
  cases Kernel.exec S ⟨[], bufs, []⟩ k <;> rfl

end Tau
