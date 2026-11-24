import Tau.CellLevel.Machine
import Tau.Proofs.Blocks.ShiftRegister
import Tau.Proofs.Blocks.Memory

/-!
# The cell-level machine refines the slice-level machine

The main result is `cellExecute_eq`: for every chip, program, cycle count and
starting memory, the cell-level machine and the slice-level machine on real
words give the same result. They trap on the same cycle for the same reason,
or they end with the same memory contents.

The proof relates the two states by an *abstraction function* (`Cell.abs`,
`CellState.abs`) that forgets how a slice is built: a memory block's vector
becomes a list of words, a shift register's vector becomes a list of pending
results, the per-lane totals become one word. `CellState.step_abs` shows that
taking a step and then abstracting is the same as abstracting and then taking
a slice-level step. Everything else follows by induction on the number of
cycles.

Terms to look up: *refinement*, *simulation relation*, *abstraction function*.
-/

namespace Tau

variable {lanes : Nat}

/-- Forget how a slice is built. -/
def Cell.abs (c : Cell lanes) : Slice (Word lanes) where
  words := c.mem.toList
  x := c.x
  acc := c.acc
  pipe := c.pipe.toList

/-- Forget how the slices are built. The slice-level state has one shared
clock, so the time is supplied from outside. -/
def CellState.abs (t : Nat) (s : CellState lanes) : State (Word lanes) where
  time := t
  east := s.east
  west := s.west
  slices := s.cells.map Cell.abs

def absResult (r : Cell lanes × Option (Track × Word lanes)) :
    Slice (Word lanes) × Option (Track × Word lanes) :=
  (r.1.abs, r.2)

/-! ## The sequencer issues what the slice-level machine looks up -/

theorem forSlice_dueAt (prog : Program) (p t : Nat) :
    dueAt (prog.forSlice p) t = prog.dueAt p t := by
  induction prog with
  | nil => rfl
  | cons e rest ih =>
    simp only [dueAt, Program.forSlice, Program.dueAt] at ih ⊢
    by_cases hp : e.slice = p <;> by_cases ht : e.time = t <;>
      simp [hp, ht, ih]

/-! ## The multiply-accumulate cells compute `Word.mac` -/

theorem macLanes_add (j : Nat) (acc x w : Word lanes) :
    macLanes acc (fun k => .add (x[j]?.getD 0, w[k])) = Word.mac j acc x w := by
  apply Vector.ext
  intro k hk
  simp [macLanes, Word.mac, mac, Block.mapIn, accumulator, AccIn.map]

theorem macLanes_clear (acc : Word lanes) :
    macLanes acc (fun _ => .clear) = Word.zero := by
  apply Vector.ext
  intro k hk
  simp [macLanes, Word.zero, mac, Block.mapIn, accumulator, AccIn.map]

/-! ## The shift register is the slice-level pipe -/

theorem toList_shift {α : Type} (d : Nat) (s : Vector α d) (x : α) :
    (Vector.ofFn fun i : Fin d =>
      if i.val = 0 then x
      else s[i.val - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt)).toList =
      (x :: s.toList).dropLast := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [Vector.length_toList] at h1
    simp only [Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_dropLast,
      List.getElem_cons]
    split <;> simp_all

theorem last_shift {α : Type} (d : Nat) (s : Vector α d) (x dflt : α) :
    (if h : 0 < d then s[d - 1]'(Nat.sub_lt h Nat.zero_lt_one) else x) =
      (x :: s.toList).getLast?.getD dflt := by
  rw [List.getLast?_cons]
  by_cases h : 0 < d
  · have hlt : d - 1 < d := by omega
    simp [h, List.getLast?_eq_getElem?, hlt]
  · have hd : d = 0 := by omega
    subst hd
    have hnil : s.toList = [] := List.eq_nil_of_length_eq_zero (by simp)
    simp [hnil]

theorem cellShift_abs (c : Cell lanes) (r : Option (Track × Word lanes)) :
    absResult (cellShift c r) = shiftPipe c.abs r := by
  simp only [cellShift, absResult, shiftPipe, shiftRegister_step, Cell.abs, toList_shift,
    last_shift c.depth c.pipe r none]

/-! ## One instruction -/

theorem cellExec_abs (cfg : Config) (kind : Kind) (rd : Track → Option (Word lanes))
    (c : Cell lanes) (i : Instr) :
    (cellExec cfg kind rd c i).map absResult = exec (wordSem lanes) cfg kind rd c.abs i := by
  cases i with
  | read addr dst =>
    simp only [cellExec, exec, memory_step, Cell.abs, Vector.getElem?_toList]
    split
    · rfl
    · split
      · rfl
      · cases c.mem[addr]? <;> rfl
  | write src addr =>
    simp only [cellExec, exec, memory_step, Cell.abs, Vector.length_toList]
    split
    · rfl
    · split
      · rfl
      · cases rd src <;> simp [Except.map, absResult, Cell.abs]
  | un op src dst =>
    simp only [cellExec, exec]
    split
    · rfl
    · split
      · rfl
      · cases rd src <;> rfl
  | bin op a b dst =>
    simp only [cellExec, exec]
    split
    · rfl
    · split
      · rfl
      · cases rd a <;> cases rd b <;> rfl
  | load src =>
    simp only [cellExec, exec]
    split
    · rfl
    · cases rd src <;> rfl
  | mac j src =>
    simp only [cellExec, exec, Cell.abs]
    split
    · rfl
    · cases c.x with
      | none => rfl
      | some x =>
        cases rd src with
        | none => rfl
        | some w =>
          simp only [Except.map, absResult, Cell.abs, macLanes_add]
          rfl
  | emit dst =>
    simp only [cellExec, exec]
    split
    · rfl
    · split
      · rfl
      · simp [Except.map, absResult, Cell.abs, macLanes_clear, wordSem]

/-! ## One slice, one cycle -/

theorem CellState.sample_abs (t : Nat) (s : CellState lanes) (p : Nat) :
    (s.abs t).sample p = s.sample p := by
  funext tr
  unfold State.sample CellState.sample State.belt
  cases tr.dir with
  | east =>
    simp only [CellState.abs]
    cases s.east[tr.id]? <;> rfl
  | west =>
    simp only [CellState.abs]
    cases s.west[tr.id]? <;> rfl

theorem cellStep_abs (cfg : Config) (prog : Program) (s : CellState lanes) (p : Nat)
    (c : Cell lanes) :
    (cellStep cfg prog (s.sample p) p c).map absResult =
      stepSlice (wordSem lanes) cfg prog (s.abs c.clock) p c.abs := by
  have hseq : (sequencer (prog.forSlice p)).step c.clock () =
      (c.clock + 1, prog.dueAt p c.clock) := by
    rw [← forSlice_dueAt]
    rfl
  have ht : (s.abs c.clock).time = c.clock := rfl
  unfold cellStep stepSlice
  simp only [hseq, ht, CellState.sample_abs]
  cases prog.dueAt p c.clock with
  | nil => exact congrArg Except.ok (cellShift_abs c none)
  | cons i rest =>
    cases rest with
    | cons j rest => rfl
    | nil =>
      cases cfg.kindAt p with
      | none => rfl
      | some kind =>
        simp only
        rw [← cellExec_abs cfg kind (s.sample p) c i]
        cases cellExec cfg kind (s.sample p) c i with
        | error k => rfl
        | ok r =>
          obtain ⟨c', r⟩ := r
          exact congrArg Except.ok (cellShift_abs c' r)

/-- A slice's clock advances by one on every cycle. -/
theorem cellStep_clock (cfg : Config) (prog : Program) (rd : Track → Option (Word lanes))
    (p : Nat) (c : Cell lanes) (r : Cell lanes × Option (Track × Word lanes))
    (h : cellStep cfg prog rd p c = .ok r) : r.1.clock = c.clock + 1 := by
  unfold cellStep at h
  simp only at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · split at h
      · cases h; rfl
      · cases h
  · cases h

/-! ## Every slice, one cycle -/

theorem cellSteps_abs (cfg : Config) (prog : Program) (s : CellState lanes) (t p : Nat)
    (cells : List (Cell lanes)) (h : ∀ c ∈ cells, c.clock = t) :
    (cellSteps cfg prog s p cells).map (List.map absResult) =
      stepSlices (wordSem lanes) cfg prog (s.abs t) p (cells.map Cell.abs) := by
  induction cells generalizing p with
  | nil => rfl
  | cons c rest ih =>
    have hc : c.clock = t := h c (by simp)
    have h1 := cellStep_abs cfg prog s p c
    rw [hc] at h1
    have h2 := ih (p + 1) (fun c' hc' => h c' (by simp [hc']))
    simp only [cellSteps, List.map_cons, stepSlices]
    rw [← h1, ← h2]
    cases cellStep cfg prog (s.sample p) p c with
    | error e => rfl
    | ok r =>
      cases cellSteps cfg prog s (p + 1) rest with
      | error e => rfl
      | ok rs => rfl

theorem cellSteps_clock (cfg : Config) (prog : Program) (s : CellState lanes) (t p : Nat)
    (cells : List (Cell lanes)) (h : ∀ c ∈ cells, c.clock = t)
    (rs : List (Cell lanes × Option (Track × Word lanes)))
    (hr : cellSteps cfg prog s p cells = .ok rs) : ∀ r ∈ rs, r.1.clock = t + 1 := by
  induction cells generalizing p rs with
  | nil =>
    simp only [cellSteps] at hr
    cases hr
    simp
  | cons c rest ih =>
    simp only [cellSteps] at hr
    cases h1 : cellStep cfg prog (s.sample p) p c with
    | error e => simp [h1] at hr
    | ok r0 =>
      cases h2 : cellSteps cfg prog s (p + 1) rest with
      | error e => simp [h1, h2] at hr
      | ok rs' =>
        simp only [h1, h2] at hr
        cases hr
        intro r hr'
        simp only [List.mem_cons] at hr'
        cases hr' with
        | inl heq =>
          subst heq
          rw [cellStep_clock cfg prog _ p c r h1, h c (by simp)]
        | inr hmem => exact ih (p + 1) (fun c' hc' => h c' (by simp [hc'])) rs' h2 r hmem

/-! ## The whole machine -/

/-- Taking a step and then abstracting is the same as abstracting and then
taking a slice-level step. -/
theorem CellState.step_abs (cfg : Config) (prog : Program) (t : Nat) (s : CellState lanes)
    (h : ∀ c ∈ s.cells, c.clock = t) :
    (s.step cfg prog).map (CellState.abs (t + 1)) =
      Tau.step (wordSem lanes) cfg prog (s.abs t) := by
  have hs : (s.abs t).slices = s.cells.map Cell.abs := rfl
  unfold CellState.step Tau.step
  rw [hs, ← cellSteps_abs cfg prog s t 0 s.cells h]
  cases cellSteps cfg prog s 0 s.cells with
  | error e => rfl
  | ok rs =>
    have h2 : (rs.map absResult).map (·.2) = rs.map (·.2) := by
      simp [List.map_map, absResult]
    have h1 : (rs.map absResult).map (·.1) = (rs.map (·.1)).map Cell.abs := by
      simp [List.map_map, absResult]
    simp only [Except.map, CellState.abs, h1, h2]

theorem CellState.step_clock (cfg : Config) (prog : Program) (t : Nat) (s s' : CellState lanes)
    (h : ∀ c ∈ s.cells, c.clock = t) (hs : s.step cfg prog = .ok s') :
    ∀ c ∈ s'.cells, c.clock = t + 1 := by
  unfold CellState.step at hs
  cases h1 : cellSteps cfg prog s 0 s.cells with
  | error e => simp [h1] at hs
  | ok rs =>
    simp only [h1] at hs
    cases hs
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨r, hr, rfl⟩ := hc
    exact cellSteps_clock cfg prog s t 0 s.cells h rs h1 r hr

theorem CellState.run_abs (cfg : Config) (prog : Program) (n t : Nat) (s : CellState lanes)
    (h : ∀ c ∈ s.cells, c.clock = t) :
    (CellState.run cfg prog n s).map (CellState.abs (t + n)) =
      Tau.run (wordSem lanes) cfg prog n (s.abs t) := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih =>
    simp only [CellState.run, Tau.run]
    rw [← CellState.step_abs cfg prog t s h]
    cases hstep : s.step cfg prog with
    | error e => rfl
    | ok s' =>
      have h' := CellState.step_clock cfg prog t s s' h hstep
      have hih := ih (t + 1) s' h'
      have ht : t + (n + 1) = t + 1 + n := by omega
      simp only [Except.map, ht]
      exact hih

theorem CellState.init_abs (cfg : Config) (image : List (List (Word lanes))) :
    (CellState.init cfg image).abs 0 = State.init (wordSem lanes) cfg image := by
  simp only [CellState.init, CellState.abs, State.init, List.map_map]
  congr 1

theorem CellState.init_clock (cfg : Config) (image : List (List (Word lanes))) :
    ∀ c ∈ (CellState.init cfg image).cells, c.clock = 0 := by
  intro c hc
  simp only [CellState.init, List.mem_map] at hc
  obtain ⟨p, _, rfl⟩ := hc
  rfl

/-- **Refinement.** The cell-level machine and the slice-level machine give
the same result on every program: the same trap, or the same final memory. -/
theorem cellExecute_eq (cfg : Config) (prog : Program) (n : Nat)
    (image : List (List (Word lanes))) :
    cellExecute cfg prog n image = execute (wordSem lanes) cfg prog n image := by
  unfold cellExecute execute
  rw [← CellState.init_abs,
    ← CellState.run_abs cfg prog n 0 _ (CellState.init_clock cfg image)]
  cases CellState.run cfg prog n (CellState.init cfg image) with
  | error e => rfl
  | ok s => simp [Except.map, CellState.abs, State.memory, CellState.memory, Cell.abs]

end Tau
