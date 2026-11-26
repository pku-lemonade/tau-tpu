import Tau.IR.Placed
import Tau.Proofs.Machine.SliceLevel
import Tau.Proofs.IR.Kernel
import Tau.Proofs.IR.MemMap

/-!
# A placed program does not look at its values

The same fact as `Tau.Proofs.Machine.SliceLevel` and `Tau.Proofs.IR.Kernel`,
for the placed IR: a function `f` that respects the operations commutes
with carrying out a placed program. Whether the program fails depends only on
the program and the memory sizes, never on the values.

The main result is `Placed.execute_map`. `checkPlaced_sound`
(`Tau.Proofs.Check.Passes`) uses it.
-/

namespace Tau

variable {V W : Type}

/-- Apply `f` to every value in a placed state. -/
def PState.map (f : V → W) (st : PState V) : PState W where
  vars := st.vars.map (Prod.map id f)
  slices := st.slices.map (Slice.map f)
  issues := st.issues.map (Issue.map f)

theorem PInstr.exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (kind : Kind)
    (vars : List (Var × V)) (sl : Slice V) (i : PInstr) :
    i.exec T kind (vars.map (Prod.map id f)) (sl.map f) =
      (i.exec S kind vars sl).map fun r => (r.1.map (Prod.map id f), r.2.map f) := by
  -- One case per instruction, as in `exec_map` for the machine: unfold, move
  -- the map out of each lookup (`lookup_map`), split on each check and on
  -- what each lookup found. A pinned instruction does what the instruction
  -- inside it does.
  induction i with
  | pin t i ih =>
    simp only [PInstr.exec]
    exact ih
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

theorem PInstr.issues_map (f : V → W) (p : Nat) (i : PInstr) (vars : List (Var × V)) :
    i.issues p (vars.map (Prod.map id f)) = (i.issues p vars).map (Issue.map f) := by
  unfold PInstr.issues
  cases i.target with
  | none => rfl
  | some va =>
    simp only [lookup_map]
    cases vars.lookup va.1 with
    | none => rfl
    | some w => simp [Issue.map, List.map_map, Function.comp_def]

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
      | some r => simp [PState.map, List.map_set, PInstr.issues_map]

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
  have hinit : (⟨[], (State.init T pl.cfg (image.map (List.map f))).slices, []⟩ : PState W) =
      (⟨[], (State.init S pl.cfg image).slices, []⟩ : PState V).map f := by
    rw [State.init_map S T f h]
    rfl
  rw [hinit, PState.run_map S T f h]
  cases PState.run S pl.cfg ⟨[], (State.init S pl.cfg image).slices, []⟩ pl.instrs with
  | none => rfl
  | some st => simp [PState.map, Slice.map, List.map_map]

/-- The timeline of a placed program on a mapped memory image is the mapped
timeline. -/
theorem Placed.timelineFrom_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f)
    (pl : Placed) (image : List (List V)) :
    pl.timelineFrom T (image.map (List.map f)) =
      (pl.timelineFrom S image).map (Event.map f) := by
  unfold Placed.timelineFrom
  have hinit : (⟨[], (State.init T pl.cfg (image.map (List.map f))).slices, []⟩ : PState W) =
      (⟨[], (State.init S pl.cfg image).slices, []⟩ : PState V).map f := by
    rw [State.init_map S T f h]
    rfl
  rw [hinit, PState.run_map S T f h]
  cases PState.run S pl.cfg ⟨[], (State.init S pl.cfg image).slices, []⟩ pl.instrs with
  | none => rfl
  | some st => exact filterMap_event_map f pl.map st.issues

end Tau
