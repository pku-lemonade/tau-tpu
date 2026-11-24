import Tau.Check.Stages
import Tau.Proofs.Check.Sound

/-!
# The per-pass checks are sound

Two results, one for each new check in `Tau/Check/Stages.lean`.

* `checkKernels_sound`: two kernels the check accepts compute the same
  buffers, on every input.
* `checkPlaced_sound`: a placed program the check accepts, run from any
  buffer contents, ends with the buffers the kernel computes.

The proofs follow `check_sound`. The new ingredient is `Placed.execute_map`:
like the machine and like a kernel, a placed program does not look at its
values.
-/

namespace Tau

variable {V W : Type}

/-! ## Kernel against kernel -/

/-- **Soundness of `checkKernels`.** Two kernels it accepts compute the same
buffers on every input, and neither fails. -/
theorem checkKernels_sound (S : Sem V) (hS : S.Lawful) (k k' : Kernel)
    (bufs : List (List V)) (fill : V)
    (h : checkKernels k k' (bufs.map List.length) = true) :
    ∃ out, k.run S bufs = some out ∧ k'.run S bufs = some out := by
  -- Split on the two symbolic runs. Each kernel on real buffers is its
  -- symbolic run evaluated (`Kernel.run_of_exprs`), and the two evaluated
  -- results agree (`denote_of_simp_eq`).
  unfold checkKernels at h
  cases ha : kernelExprs k (bufs.map List.length) with
  | none => simp [ha] at h
  | some a =>
    cases hb : kernelExprs k' (bufs.map List.length) with
    | none => simp [ha, hb] at h
    | some b =>
      simp only [ha, hb, beq_iff_eq] at h
      refine ⟨_, Kernel.run_of_exprs S k bufs fill a ha, ?_⟩
      rw [Kernel.run_of_exprs S k' bufs fill b hb, denote_of_simp_eq S hS bufs fill a b h]

/-! ## A placed program does not look at its values -/

/-- Apply `f` to every value in a placed state. -/
def PState.map (f : V → W) (st : PState V) : PState W where
  vars := st.vars.map (Prod.map id f)
  slices := st.slices.map (Slice.map f)

theorem PInstr.exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (kind : Kind)
    (vars : List (Var × V)) (sl : Slice V) (i : PInstr) :
    i.exec T kind (vars.map (Prod.map id f)) (sl.map f) =
      (i.exec S kind vars sl).map fun r => (r.1.map (Prod.map id f), r.2.map f) := by
  -- One case per instruction, as in `exec_map` for the machine: unfold, move
  -- the map out of each lookup (`lookup_map`), split on each check and on
  -- what each lookup found.
  cases i with
  | read dst addr =>
    simp only [PInstr.exec, Slice.map, List.getElem?_map]
    split
    · rfl
    · cases sl.words[addr]? <;> rfl
  | write src addr =>
    simp only [PInstr.exec, Slice.map, List.length_map, lookup_map]
    split
    · rfl
    · split
      · rfl
      · cases vars.lookup src <;> simp [List.map_set]
  | un dst op src =>
    simp only [PInstr.exec, lookup_map]
    split
    · rfl
    · cases vars.lookup src <;> simp [h.un]
  | bin dst op a b =>
    simp only [PInstr.exec, lookup_map]
    split
    · rfl
    · cases vars.lookup a <;> cases vars.lookup b <;> simp [h.bin]
  | load src =>
    simp only [PInstr.exec, lookup_map]
    split
    · rfl
    · cases vars.lookup src <;> simp [Slice.map]
  | mac j src =>
    simp only [PInstr.exec, lookup_map, Slice.map]
    split
    · rfl
    · cases sl.x <;> cases vars.lookup src <;> simp [h.mac]
  | emit dst =>
    simp only [PInstr.exec]
    split
    · rfl
    · simp [Slice.map, h.zero]
  | const dst xs =>
    simp only [PInstr.exec]
    split
    · rfl
    · simp [h.const]
  | sel dst m a b =>
    simp only [PInstr.exec, lookup_map]
    split
    · rfl
    · cases vars.lookup m <;> cases vars.lookup a <;> cases vars.lookup b <;> simp [h.sel]
  | seed src =>
    simp only [PInstr.exec, lookup_map]
    split
    · rfl
    · cases vars.lookup src <;> simp [Slice.map]
  | install j src =>
    simp only [PInstr.exec, lookup_map, Slice.map, List.length_map]
    split
    · rfl
    · split
      · rfl
      · cases vars.lookup src <;> simp [List.map_set]
  | macw j =>
    simp only [PInstr.exec, Slice.map, List.getElem?_map]
    split
    · rfl
    · cases sl.x <;> cases sl.weights[j]? <;> simp [h.mac]

theorem PState.step_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (st : PState V) (p : Nat) (i : PInstr) :
    (st.map f).step T cfg p i = (st.step S cfg p i).map (PState.map f) := by
  unfold PState.step
  have hv : (st.map f).vars = st.vars.map (Prod.map id f) := rfl
  have hs : (st.map f).slices = st.slices.map (Slice.map f) := rfl
  rw [hv, hs, List.getElem?_map]
  cases cfg.kindAt p with
  | none => rfl
  | some kind =>
    cases st.slices[p]? with
    | none => rfl
    | some sl =>
      simp only [Option.map_some, PInstr.exec_map S T f h]
      cases i.exec S kind st.vars sl with
      | none => rfl
      | some r => simp [PState.map, List.map_set]

theorem PState.run_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (st : PState V) (instrs : List (Nat × PInstr)) :
    PState.run T cfg (st.map f) instrs = (PState.run S cfg st instrs).map (PState.map f) := by
  induction instrs generalizing st with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨p, i⟩ := e
    simp only [PState.run, PState.step_map S T f h]
    cases st.step S cfg p i with
    | none => rfl
    | some st' => exact ih st'

/-- Running a placed program on a mapped memory image gives the mapped
result, and fails in exactly the same cases. -/
theorem Placed.execute_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (pl : Placed)
    (image : List (List V)) :
    pl.execute T (image.map (List.map f)) =
      (pl.execute S image).map (List.map (List.map f)) := by
  unfold Placed.execute
  have hinit : (⟨[], (State.init T pl.cfg (image.map (List.map f))).slices⟩ : PState W) =
      (⟨[], (State.init S pl.cfg image).slices⟩ : PState V).map f := by
    rw [State.init_map S T f h]
    rfl
  rw [hinit, PState.run_map S T f h]
  cases PState.run S pl.cfg ⟨[], (State.init S pl.cfg image).slices⟩ pl.instrs with
  | none => rfl
  | some st => simp [PState.map, Slice.map, List.map_map]

/-! ## Placed program against kernel -/

/-- **Soundness of `checkPlaced`.** If it accepts the placed program `pl` for
the kernel `k`, then on any buffer contents the instructions of `pl`, carried
out in order, end with the buffers that `k` computes. -/
theorem checkPlaced_sound (S : Sem V) (hS : S.Lawful) (k : Kernel) (pl : Placed)
    (bufs : List (List V)) (fill : V)
    (h : checkPlaced k (bufs.map List.length) pl = true) :
    ∃ mem out,
      pl.execute S (pl.image bufs fill) = some mem ∧
      k.run S bufs = some out ∧
      extract pl.map mem fill = out := by
  -- The proof of `check_sound` again, with `Placed.execute_map` in place of
  -- `execute_map`.
  let f := Expr.denote S bufs fill
  have hf : exprSem.Hom S f := denote_hom S bufs fill
  unfold checkPlaced at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  unfold placedExprs at h
  cases hx : pl.execute exprSem (image pl.map pl.memSizes Expr.init .fill) with
  | none => simp [hx] at h
  | some memE =>
    cases hk : kernelExprs k (bufs.map List.length) with
    | none => simp [hx, hk] at h
    | some outE =>
      simp only [hx, hk, beq_iff_eq] at h
      have himg : pl.image bufs fill =
          (image pl.map pl.memSizes Expr.init .fill).map (List.map f) := by
        rw [image_map]
        rfl
      have hrun : pl.execute S (pl.image bufs fill) = some (memE.map (List.map f)) := by
        rw [himg, Placed.execute_map exprSem S f hf, hx]
        rfl
      refine ⟨_, _, hrun, Kernel.run_of_exprs S k bufs fill outE hk, ?_⟩
      have hfill : f .fill = fill := rfl
      rw [← hfill, extract_map f pl.map memE .fill]
      exact denote_of_simp_eq S hS bufs fill _ _ h

end Tau
