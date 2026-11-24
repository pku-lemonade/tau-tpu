/-
Exercise file. Generated from Tau/Proofs/CellLevel/Refine.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/CellLevel/Refine.lean.
Build this file alone with:

    lake build Exercises.CellLevel.Refine
-/

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
  sorry

theorem macLanes_clear (acc : Word lanes) :
    macLanes acc (fun _ => .clear) = Word.zero := by
  sorry

theorem macLanes_load (acc w : Word lanes) :
    macLanes acc (fun k => .load (w[k], 1)) = w := by
  sorry

/-! ## The shift register is the slice-level pipe -/

theorem toList_shift {α : Type} (d : Nat) (s : Vector α d) (x : α) :
    (Vector.ofFn fun i : Fin d =>
      if i.val = 0 then x
      else s[i.val - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt)).toList =
      (x :: s.toList).dropLast := by
  sorry

theorem last_shift {α : Type} (d : Nat) (s : Vector α d) (x dflt : α) :
    (if h : 0 < d then s[d - 1]'(Nat.sub_lt h Nat.zero_lt_one) else x) =
      (x :: s.toList).getLast?.getD dflt := by
  sorry

theorem cellShift_abs (c : Cell lanes) (r : Option (Track × Word lanes)) :
    absResult (cellShift c r) = shiftPipe c.abs r := by
  sorry

/-! ## One instruction -/

theorem cellExec_abs (cfg : Config) (kind : Kind) (rd : Track → Option (Word lanes))
    (c : Cell lanes) (i : Instr) :
    (cellExec cfg kind rd c i).map absResult = exec (wordSem lanes) cfg kind rd c.abs i := by
  -- Outline of one proof:
  -- One case per instruction. Unfold both machines' functions, turn each
  -- block step into what it computes (`memory_step`), and turn vector
  -- operations into list operations. Split on each check and each read.
  -- The matrix cases use the lemmas about `macLanes`.
  sorry

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
  sorry

/-- What a slice's repeater does in one cycle, when it is in step. -/
theorem cellRepeater_step (prog : Program) (t p : Nat) (c : Cell lanes)
    (hc : c.InSync prog t p) :
    (repeater (prog.entriesFor p)).step c.slots () =
      ((prog.entriesFor p).map fun e => e.slotAt (t + 1), prog.dueAt p t) := by
  sorry

theorem cellStep_abs (cfg : Config) (prog : Program) (s : CellState lanes) (t p : Nat)
    (c : Cell lanes) (hc : c.InSync prog t p) :
    (cellStep cfg prog (s.sample p) p c).map absResult =
      stepSlice (wordSem lanes) cfg prog (s.abs t) p c.abs := by
  -- Outline of one proof:
  -- The repeater, being in step, issues what the slice-level machine looks
  -- up (`cellRepeater_step`). Then split on how many instructions are due,
  -- and use `cellExec_abs` and `cellShift_abs`.
  sorry

/-- After one cycle a slice that was in step is in step with the next cycle. -/
theorem cellStep_sync (cfg : Config) (prog : Program) (rd : Track → Option (Word lanes))
    (t p : Nat) (c : Cell lanes) (r : Cell lanes × Option (Track × Word lanes))
    (hc : c.InSync prog t p) (h : cellStep cfg prog rd p c = .ok r) :
    r.1.InSync prog (t + 1) p := by
  sorry

/-! ## Every slice, one cycle -/

theorem cellSteps_abs (cfg : Config) (prog : Program) (s : CellState lanes) (t p : Nat)
    (cells : List (Cell lanes)) (h : Synced prog t p cells) :
    (cellSteps cfg prog s p cells).map (List.map absResult) =
      stepSlices (wordSem lanes) cfg prog (s.abs t) p (cells.map Cell.abs) := by
  sorry

theorem cellSteps_synced (cfg : Config) (prog : Program) (s : CellState lanes) (t p : Nat)
    (cells : List (Cell lanes)) (h : Synced prog t p cells)
    (rs : List (Cell lanes × Option (Track × Word lanes)))
    (hr : cellSteps cfg prog s p cells = .ok rs) :
    Synced prog (t + 1) p (rs.map (·.1)) := by
  sorry

/-! ## The whole machine -/

/-- Taking a step and then abstracting is the same as abstracting and then
taking a slice-level step. -/
theorem CellState.step_abs (cfg : Config) (prog : Program) (t : Nat) (s : CellState lanes)
    (h : Synced prog t 0 s.cells) :
    (s.step cfg prog).map (CellState.abs (t + 1)) =
      Tau.step (wordSem lanes) cfg prog (s.abs t) := by
  sorry

theorem CellState.step_synced (cfg : Config) (prog : Program) (t : Nat)
    (s s' : CellState lanes) (h : Synced prog t 0 s.cells) (hs : s.step cfg prog = .ok s') :
    Synced prog (t + 1) 0 s'.cells := by
  sorry

theorem CellState.run_abs (cfg : Config) (prog : Program) (n t : Nat) (s : CellState lanes)
    (h : Synced prog t 0 s.cells) :
    (CellState.run cfg prog n s).map (CellState.abs (t + n)) =
      Tau.run (wordSem lanes) cfg prog n (s.abs t) := by
  sorry

theorem CellState.init_abs (cfg : Config) (prog : Program) (image : List (List (Word lanes))) :
    (CellState.init cfg prog image).abs 0 = State.init (wordSem lanes) cfg image := by
  sorry

theorem synced_map_range' (prog : Program) (f : Nat → Cell lanes)
    (hf : ∀ q, (f q).InSync prog 0 q) (p m : Nat) :
    Synced prog 0 p ((List.range' p m).map f) := by
  sorry

/-- At cycle 0 every slice is in step. -/
theorem CellState.init_synced (cfg : Config) (prog : Program)
    (image : List (List (Word lanes))) :
    Synced prog 0 0 (CellState.init cfg prog image).cells := by
  sorry

/-- **Refinement.** The cell-level machine and the slice-level machine give
the same result on every program: the same trap, or the same final memory. -/
theorem cellExecute_eq (cfg : Config) (prog : Program) (n : Nat)
    (image : List (List (Word lanes))) :
    cellExecute cfg prog n image = execute (wordSem lanes) cfg prog n image := by
  -- Outline of one proof:
  -- Both start with the same check of the program. After it, rewrite the
  -- slice-level start state as the abstraction of the cell-level one
  -- (`init_abs`) and the slice-level run as the abstraction of the
  -- cell-level run (`run_abs`, with `init_synced`).
  sorry

end Tau
