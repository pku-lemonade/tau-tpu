import Tau.CellLevel.Machine
import Tau.Proofs.Blocks.ShiftRegister
import Tau.Proofs.Blocks.Memory
import Tau.Proofs.Blocks.Repeater

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
  weights := c.weights.toList
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

theorem macLanes_load (acc w : Word lanes) :
    macLanes acc (fun k => .load (w[k], 1)) = w := by
  apply Vector.ext
  intro k hk
  simp [macLanes, mac, Block.mapIn, accumulator, AccIn.map]

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
  -- One case per instruction. Unfold both machines' functions, turn each
  -- block step into what it computes (`memory_step`), and turn vector
  -- operations into list operations. Split on each check and each read.
  -- The matrix cases use the lemmas about `macLanes`.
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
  | const xs dst =>
    simp only [cellExec, exec]
    split
    · rfl
    · split <;> rfl
  | sel m a b dst =>
    simp only [cellExec, exec]
    split
    · rfl
    · split
      · rfl
      · cases rd m <;> cases rd a <;> cases rd b <;> rfl
  | seed src =>
    simp only [cellExec, exec]
    split
    · rfl
    · cases rd src with
      | none => rfl
      | some v =>
        simp only [Except.map, absResult, Cell.abs, macLanes_load]
  | install j src =>
    simp only [cellExec, exec, memory_step, Cell.abs, Vector.length_toList]
    split
    · rfl
    · split
      · rfl
      · cases rd src <;> simp [Except.map, absResult, Cell.abs]
  | macw j =>
    simp only [cellExec, exec, memory_step, Cell.abs, Vector.getElem?_toList]
    split
    · rfl
    · cases c.x with
      | none => rfl
      | some x =>
        cases c.weights[j]? with
        | none => rfl
        | some w =>
          simp only [Except.map, absResult, Cell.abs, macLanes_add]
          rfl

/-! ## The repeaters stay in step

The slice-level machine has one cycle count. The cell-level machine has a
repeater in every slice, each with its own registers. `InSync` says that one
slice's registers are the ones its entries should have at cycle `t`, and
`Synced` says so for a list of slices starting at position `p`. This is the
invariant the refinement carries from cycle to cycle. -/

/-- The slice at position `p` has the registers of cycle `t`. -/
def Cell.InSync (prog : Program) (t p : Nat) (c : Cell lanes) : Prop :=
  c.clock = t ∧ c.slots = (prog.entriesFor p).map fun e => e.slotAt t

/-- The slices `cells`, at positions `p`, `p + 1`, ..., all have the registers
of cycle `t`. -/
def Synced (prog : Program) (t : Nat) : Nat → List (Cell lanes) → Prop
  | _, [] => True
  | p, c :: rest => c.InSync prog t p ∧ Synced prog t (p + 1) rest

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

/-- What a slice's repeater does in one cycle, when it is in step. -/
theorem cellRepeater_step (prog : Program) (t p : Nat) (c : Cell lanes)
    (hc : c.InSync prog t p) :
    (repeater (prog.entriesFor p)).step c.slots () =
      ((prog.entriesFor p).map fun e => e.slotAt (t + 1), prog.dueAt p t) := by
  rw [hc.2, repeater_step]
  rfl

theorem cellStep_abs (cfg : Config) (prog : Program) (s : CellState lanes) (t p : Nat)
    (c : Cell lanes) (hc : c.InSync prog t p) :
    (cellStep cfg prog (s.sample p) p c).map absResult =
      stepSlice (wordSem lanes) cfg prog (s.abs t) p c.abs := by
  -- The repeater, being in step, issues what the slice-level machine looks
  -- up (`cellRepeater_step`). Then split on how many instructions are due,
  -- and use `cellExec_abs` and `cellShift_abs`.
  have hseq := cellRepeater_step prog t p c hc
  have ht : (s.abs t).time = t := rfl
  unfold cellStep stepSlice
  simp only [hseq, ht, hc.1, CellState.sample_abs]
  cases prog.dueAt p t with
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

/-- After one cycle a slice that was in step is in step with the next cycle. -/
theorem cellStep_sync (cfg : Config) (prog : Program) (rd : Track → Option (Word lanes))
    (t p : Nat) (c : Cell lanes) (r : Cell lanes × Option (Track × Word lanes))
    (hc : c.InSync prog t p) (h : cellStep cfg prog rd p c = .ok r) :
    r.1.InSync prog (t + 1) p := by
  have hseq := congrArg Prod.fst (cellRepeater_step prog t p c hc)
  have hclock : c.clock + 1 = t + 1 := congrArg (· + 1) hc.1
  unfold cellStep at h
  simp only at h
  split at h
  · cases h; exact ⟨hclock, hseq⟩
  · split at h
    · cases h
    · split at h
      · cases h; exact ⟨hclock, hseq⟩
      · cases h
  · cases h

/-! ## Every slice, one cycle -/

theorem cellSteps_abs (cfg : Config) (prog : Program) (s : CellState lanes) (t p : Nat)
    (cells : List (Cell lanes)) (h : Synced prog t p cells) :
    (cellSteps cfg prog s p cells).map (List.map absResult) =
      stepSlices (wordSem lanes) cfg prog (s.abs t) p (cells.map Cell.abs) := by
  induction cells generalizing p with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨hc, hrest⟩ := h
    have h1 := cellStep_abs cfg prog s t p c hc
    have h2 := ih (p + 1) hrest
    simp only [cellSteps, List.map_cons, stepSlices]
    rw [← h1, ← h2]
    cases cellStep cfg prog (s.sample p) p c with
    | error e => rfl
    | ok r =>
      cases cellSteps cfg prog s (p + 1) rest with
      | error e => rfl
      | ok rs => rfl

theorem cellSteps_synced (cfg : Config) (prog : Program) (s : CellState lanes) (t p : Nat)
    (cells : List (Cell lanes)) (h : Synced prog t p cells)
    (rs : List (Cell lanes × Option (Track × Word lanes)))
    (hr : cellSteps cfg prog s p cells = .ok rs) :
    Synced prog (t + 1) p (rs.map (·.1)) := by
  induction cells generalizing p rs with
  | nil =>
    simp only [cellSteps] at hr
    cases hr
    trivial
  | cons c rest ih =>
    obtain ⟨hc, hrest⟩ := h
    simp only [cellSteps] at hr
    cases h1 : cellStep cfg prog (s.sample p) p c with
    | error e => simp [h1] at hr
    | ok r0 =>
      cases h2 : cellSteps cfg prog s (p + 1) rest with
      | error e => simp [h1, h2] at hr
      | ok rs' =>
        simp only [h1, h2] at hr
        cases hr
        exact ⟨cellStep_sync cfg prog _ t p c r0 hc h1, ih (p + 1) hrest rs' h2⟩

/-! ## The whole machine -/

/-- Taking a step and then abstracting is the same as abstracting and then
taking a slice-level step. -/
theorem CellState.step_abs (cfg : Config) (prog : Program) (t : Nat) (s : CellState lanes)
    (h : Synced prog t 0 s.cells) :
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

theorem CellState.step_synced (cfg : Config) (prog : Program) (t : Nat)
    (s s' : CellState lanes) (h : Synced prog t 0 s.cells) (hs : s.step cfg prog = .ok s') :
    Synced prog (t + 1) 0 s'.cells := by
  unfold CellState.step at hs
  cases h1 : cellSteps cfg prog s 0 s.cells with
  | error e => simp [h1] at hs
  | ok rs =>
    simp only [h1] at hs
    cases hs
    exact cellSteps_synced cfg prog s t 0 s.cells h rs h1

theorem CellState.run_abs (cfg : Config) (prog : Program) (n t : Nat) (s : CellState lanes)
    (h : Synced prog t 0 s.cells) :
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
      have h' := CellState.step_synced cfg prog t s s' h hstep
      have hih := ih (t + 1) s' h'
      have ht : t + (n + 1) = t + 1 + n := by omega
      simp only [Except.map, ht]
      exact hih

theorem CellState.init_abs (cfg : Config) (prog : Program) (image : List (List (Word lanes))) :
    (CellState.init cfg prog image).abs 0 = State.init (wordSem lanes) cfg image := by
  simp only [CellState.init, CellState.abs, State.init, List.map_map]
  congr 1

theorem synced_map_range' (prog : Program) (f : Nat → Cell lanes)
    (hf : ∀ q, (f q).InSync prog 0 q) (p m : Nat) :
    Synced prog 0 p ((List.range' p m).map f) := by
  induction m generalizing p with
  | zero => trivial
  | succ m ih =>
    simp only [List.range'_succ, List.map_cons, Synced]
    exact ⟨hf p, ih (p + 1)⟩

/-- At cycle 0 every slice is in step. -/
theorem CellState.init_synced (cfg : Config) (prog : Program)
    (image : List (List (Word lanes))) :
    Synced prog 0 0 (CellState.init cfg prog image).cells := by
  simp only [CellState.init, List.range_eq_range']
  exact synced_map_range' prog _ (fun q => ⟨rfl, rfl⟩) 0 _

/-- **Refinement.** The cell-level machine and the slice-level machine give
the same result on every program: the same trap, or the same final memory. -/
theorem cellExecute_eq (cfg : Config) (prog : Program) (n : Nat)
    (image : List (List (Word lanes))) :
    cellExecute cfg prog n image = execute (wordSem lanes) cfg prog n image := by
  -- Both start with the same check of the program. After it, rewrite the
  -- slice-level start state as the abstraction of the cell-level one
  -- (`init_abs`) and the slice-level run as the abstraction of the
  -- cell-level run (`run_abs`, with `init_synced`).
  unfold cellExecute execute
  cases prog.find? fun e => cfg.kinds.length ≤ e.slice with
  | some e => rfl
  | none =>
    simp only
    rw [← CellState.init_abs cfg prog,
      ← CellState.run_abs cfg prog n 0 _ (CellState.init_synced cfg prog image)]
    cases CellState.run cfg prog n (CellState.init cfg prog image) with
    | error e => rfl
    | ok s => simp [Except.map, CellState.abs, State.memory, CellState.memory, Cell.abs]

end Tau
