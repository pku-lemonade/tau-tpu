import Tau.Machine.CellLevel
import Tau.Proofs.Blocks.ShiftRegister
import Tau.Proofs.Blocks.Memory
import Tau.Proofs.Blocks.Repeater

/-!
# The cell-level machine refines the slice-level machine

The main result is `cellExecute_eq`: for every machine, program, cycle count and
starting memory, the cell-level machine and the slice-level machine on real
words give the same result. They trap on the same cycle for the same reason,
or they end with the same memory contents.

The proof relates the two states by an *abstraction function* (`Cell.abs`,
`CellState.abs`) that forgets how a slice is built: a memory block's vector
becomes a list of words (the two banks of a memory slice, one after the
other), a shift register's vector becomes a list of pending
results, the installed words become a list. `CellState.step_abs` shows that
taking a step and then abstracting is the same as abstracting and then taking
a slice-level step. Everything else follows by induction on the number of
cycles.

Terms to look up: *refinement*, *simulation relation*, *abstraction function*.
-/

namespace Tau

variable {lanes : Nat}

/-- Forget how a slice is built. -/
def Cell.abs (c : Cell lanes) : Slice (Word lanes) where
  words := c.lower.toList ++ c.upper.toList
  weights := c.weights.toList
  pipe := c.pipe.toList

/-- Forget how the slices are built. The slice-level state has one shared
clock, so the time is supplied from outside. -/
def CellState.abs (t : Nat) (s : CellState lanes) : State (Word lanes) where
  time := t
  east := s.east
  west := s.west
  slices := s.cells.map Cell.abs

def absResult (r : Cell lanes × Option (Stream × Value lanes)) :
    Slice (Word lanes) × Option (Stream × Value lanes) :=
  (r.1.abs, r.2)

/-! ## The rows of multiply-accumulate cells compute `Word.matvec` -/

/-- A row of cells adds up the dot product of the word it holds with the
word it is given. -/
theorem macRow_eq (w x : Word lanes) : macRow w x = Word.dot w x := by
  simp [macRow, Word.dot, mac, Block.mapIn, accumulator, AccIn.map]

theorem toList_putRows {n : Nat} (ws : Vector (Word lanes) n) (j : Nat)
    (vs : List (Word lanes)) : (putRows ws j vs).toList = putAt ws.toList j vs := by
  induction vs generalizing ws j with
  | nil => rfl
  | cons v vs ih => simp only [putRows, putAt, ih, Vector.toList_setIfInBounds]

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

theorem cellShift_abs (c : Cell lanes) (r : Option (Stream × Value lanes)) (d : Nat) :
    absResult (cellShift c r d) = shiftPipe c.abs r d := by
  -- A result that enters at the front is the register's input. One written
  -- part way along is the same list as the slots with that place set.
  have hlen : c.abs.pipe.length = c.depth := by simp [Cell.abs]
  cases r with
  | none =>
    simp only [cellShift, absResult, shiftPipe, Slice.slots, shiftRegister_step, Cell.abs,
      toList_shift, last_shift c.depth c.pipe none none]
  | some x =>
    by_cases hd : d < c.depth
    · have h' : c.abs.pipe.length - d = c.depth - 1 - d + 1 := by rw [hlen]; omega
      simp only [shiftPipe, Slice.slots, h', List.set_cons_succ]
      simp only [cellShift, hd, ↓reduceIte, absResult, shiftRegister_step, Cell.abs,
        toList_shift, last_shift c.depth _ none none, Vector.toList_setIfInBounds]
    · have h' : c.abs.pipe.length - d = 0 := by rw [hlen]; omega
      simp only [shiftPipe, Slice.slots, h', List.set_cons_zero]
      simp only [cellShift, hd, ↓reduceIte, absResult, shiftRegister_step, Cell.abs,
        toList_shift, last_shift c.depth c.pipe (some x) none]

theorem cellClash_abs (c : Cell lanes) (r : Option (Stream × Value lanes)) (d : Nat) :
    cellClash c r d = c.abs.clash r d := by
  have hlen : c.abs.pipe.length = c.depth := by simp [Cell.abs]
  cases r with
  | none => rfl
  | some x =>
    simp only [cellClash, Slice.clash, hlen, Option.isSome_some, Bool.true_and]
    by_cases hd : d < c.depth
    · rw [show c.depth - d = c.depth - 1 - d + 1 by omega, List.getElem?_cons_succ]
      simp [hd, Cell.abs]
    · rw [show c.depth - d = 0 by omega]
      simp [hd]

/-! ## The two banks are the slice-level memory -/

/-- A read of the bank that holds an address gives the word at that address
of the two banks laid end to end. -/
theorem Cell.stepBank_read (c : Cell lanes) (a : Nat) :
    (c.stepBank a .read).2.2 = (c.lower.toList ++ c.upper.toList)[a]? := by
  -- Below `bank` the address is in the lower bank, or beyond a memory that
  -- has no upper bank. From `bank` on it is in the upper bank, which starts
  -- where the lower one ends if it has any words at all.
  unfold Cell.stepBank
  by_cases h : a < c.bank
  · simp only [h, ↓reduceIte, memory_step]
    by_cases h2 : a < c.size
    · rw [List.getElem?_append_left (by simp; omega)]
      simp
    · rw [List.getElem?_eq_none (by simp; omega)]
      exact Vector.getElem?_eq_none (by omega)
  · simp only [h, ↓reduceIte, memory_step]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [Vector.length_toList, Vector.getElem?_toList]
    by_cases h2 : c.bank ≤ c.size
    · rw [Nat.min_eq_left h2]
    · rw [Vector.getElem?_eq_none (by omega), Vector.getElem?_eq_none (by omega)]

/-- A write to the bank that holds an address sets the word at that address
of the two banks laid end to end. -/
theorem Cell.stepBank_write (c : Cell lanes) (a : Nat) (v : Word lanes) (ha : a < c.size) :
    (c.stepBank a (.write · v)).1.toList ++ (c.stepBank a (.write · v)).2.1.toList =
      (c.lower.toList ++ c.upper.toList).set a v := by
  unfold Cell.stepBank
  by_cases h : a < c.bank
  · simp only [h, ↓reduceIte, memory_step, Vector.toList_setIfInBounds]
    rw [List.set_append_left _ _ (by simp; omega)]
  · simp only [h, ↓reduceIte, memory_step, Vector.toList_setIfInBounds]
    rw [List.set_append_right _ _ (by simp; omega)]
    simp only [Vector.length_toList]
    rw [show a - min c.bank c.size = a - c.bank by omega]

/-! ## One instruction -/

theorem cellExec_abs (cfg : Config) (kind : Kind) (rd : Stream → Option (Word lanes))
    (c : Cell lanes) (i : Instr) :
    (cellExec cfg kind rd c i).map absResult = exec (wordSem lanes) cfg kind rd c.abs i := by
  -- One case per instruction. Unfold both machines' functions, turn each
  -- block step into what it computes (`memory_step`), and turn vector
  -- operations into list operations. Split on each check and each read.
  -- The matrix cases use the lemmas about `macLanes`.
  cases i with
  | read addr dst =>
    simp only [cellExec, exec, Cell.stepBank_read, Cell.abs]
    split
    · rfl
    · split
      · rfl
      · cases (c.lower.toList ++ c.upper.toList)[addr]? <;> rfl
  | write src addr =>
    have hlen : (c.lower.toList ++ c.upper.toList).length = c.size := by
      simp only [List.length_append, Vector.length_toList]
      omega
    simp only [cellExec, exec, Cell.abs, hlen]
    split
    · rfl
    · split
      · rfl
      · rename_i ha
        cases rd src with
        | none => rfl
        | some v =>
          simp only [Except.map, absResult, Cell.abs,
            Cell.stepBank_write c addr v (by omega)]
  | un ty op src dst =>
    simp only [cellExec, exec]
    split
    · rfl
    · split
      · rfl
      · cases readGroup rd src ty.bytes <;> rfl
  | bin ty op a b dst =>
    simp only [cellExec, exec]
    split
    · rfl
    · split
      · rfl
      · cases readGroup rd a ty.bytes <;> cases readGroup rd b ty.bytes <;> rfl
  | const ty xs dst =>
    simp only [cellExec, exec]
    split
    · rfl
    · split <;> rfl
  | sel ty m a b dst =>
    simp only [cellExec, exec]
    split
    · rfl
    · split
      · rfl
      · cases readGroup rd m ty.bytes <;> cases readGroup rd a ty.bytes <;>
          cases readGroup rd b ty.bytes <;> rfl
  | install j g src =>
    simp only [cellExec, exec, Cell.abs, Vector.length_toList]
    split
    · rfl
    · split
      · rfl
      · cases readGroup rd src g <;> simp [Except.map, absResult, Cell.abs, toList_putRows]
  | product n src dst =>
    simp only [cellExec, exec, Cell.abs, Vector.length_toList]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · cases rd src with
          | none => rfl
          | some x =>
            simp only [Except.map, absResult, Cell.abs, wordSem, Value.matvec, macRow_eq]
            congr 5
            funext i
            simp only [List.getElem?_take, Vector.getElem?_toList]
            cases c.weights[i.val]? <;> by_cases hn : i.val < n <;> simp [hn]

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

theorem cellExecBoth_abs (cfg : Config) (kind : Kind) (rd : Stream → Option (Word lanes))
    (c : Cell lanes) (r w : Instr) :
    (cellExecBoth cfg kind rd c r w).map absResult =
      execBoth (wordSem lanes) cfg kind rd c.abs r w := by
  -- `cellExec_abs` for the read, and then for the write on the slice it
  -- leaves.
  unfold cellExecBoth execBoth
  rw [← cellExec_abs cfg kind rd c r]
  cases cellExec cfg kind rd c r with
  | error k => rfl
  | ok a =>
    obtain ⟨c1, res⟩ := a
    simp only [Except.map, absResult]
    rw [← cellExec_abs cfg kind rd c1 w]
    cases cellExec cfg kind rd c1 w with
    | error k => rfl
    | ok b => rfl

theorem cellLeave_abs (p t d : Nat)
    (x : Except TrapKind (Cell lanes × Option (Stream × Value lanes))) :
    (cellLeave p t d x).map absResult = leave p t d (x.map absResult) := by
  cases x with
  | error k => rfl
  | ok a =>
    obtain ⟨c, r⟩ := a
    simp only [cellLeave, leave, Except.map, absResult, ← cellClash_abs]
    by_cases hcl : cellClash c r d = true
    · simp only [hcl, ↓reduceIte]
    · simp only [hcl, Bool.false_eq_true, ↓reduceIte]
      exact congrArg Except.ok (cellShift_abs c r d)

theorem cellStep_abs (cfg : Config) (prog : Program) (s : CellState lanes) (t p : Nat)
    (c : Cell lanes) (hc : c.InSync prog t p) :
    (cellStep cfg prog (s.sample p) p c).map absResult =
      stepSlice (wordSem lanes) cfg prog (s.abs t) p c.abs := by
  -- Counting the cycle and advancing the repeater does not change what the
  -- slice is at the slice level (`htick`). The repeater, being in step,
  -- issues what the slice-level machine looks up (`cellRepeater_step`). Then
  -- split on how many instructions are due, and use `cellExec_abs` or
  -- `cellExecBoth_abs`, and `cellLeave_abs`.
  have hseq := cellRepeater_step prog t p c hc
  have ht : (s.abs t).time = t := rfl
  have htick : ∀ (g : Cell lanes → Cell lanes), (∀ c', (g c').abs = c'.abs) →
      ∀ x : Except Trap (Cell lanes × Option (Stream × Value lanes)),
      (x.map fun r => (g r.1, r.2)).map absResult = x.map absResult := by
    intro g hg x
    cases x with
    | error e => rfl
    | ok r => simp [Except.map, absResult, hg]
  unfold cellStep stepSlice
  simp only [hseq, ht, hc.1, CellState.sample_abs]
  rw [htick (fun c' => { c' with clock := t + 1, slots := _ }) (fun _ => rfl)]
  cases prog.dueAt p t with
  | nil => exact congrArg Except.ok (cellShift_abs c none 0)
  | cons i rest =>
    cases rest with
    | nil =>
      cases cfg.kindAt p with
      | none => rfl
      | some kind =>
        simp only
        rw [cellLeave_abs, cellExec_abs]
    | cons j rest =>
      cases rest with
      | cons k rest => rfl
      | nil =>
        simp only
        cases hrw : Instr.readWrite i j with
        | none => rfl
        | some rw' =>
          obtain ⟨r, w⟩ := rw'
          cases hk : cfg.kindAt p with
          | none => rfl
          | some kind =>
            simp only
            split
            · rfl
            · rw [cellLeave_abs, cellExecBoth_abs]

/-- After one cycle a slice that was in step is in step with the next cycle. -/
theorem cellStep_sync (cfg : Config) (prog : Program) (rd : Stream → Option (Word lanes))
    (t p : Nat) (c : Cell lanes) (r : Cell lanes × Option (Stream × Value lanes))
    (hc : c.InSync prog t p) (h : cellStep cfg prog rd p c = .ok r) :
    r.1.InSync prog (t + 1) p := by
  -- Whatever the instructions did, the clock counted one cycle and the
  -- repeater's registers advanced.
  have hseq := congrArg Prod.fst (cellRepeater_step prog t p c hc)
  have hclock : c.clock + 1 = t + 1 := congrArg (· + 1) hc.1
  unfold cellStep at h
  simp only [Except.map] at h
  split at h
  · cases h
  · cases h
    exact ⟨hclock, hseq⟩

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
    (rs : List (Cell lanes × Option (Stream × Value lanes)))
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
  apply List.map_congr_left
  intro p _
  simp only [Function.comp, Cell.abs, Vector.toList_mk, List.take_append_drop,
    Vector.toList_replicate]
  rfl

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
