/-
Exercise file. Generated from Tau/Proofs/Blocks/Repeater.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/Blocks/Repeater.lean.
Build this file alone with:

    lake build Exercises.Blocks.Repeater
-/

import Tau.Blocks.Repeater
import Tau.Proofs.Blocks.Basic

/-!
# Repeater: proofs

The main result is `repeater_outAt`: at every cycle the repeater, with its
counting registers, issues exactly what the specification `Entry.dueAt` says.

The work is in `Entry.slotAt_spec`, an invariant that says what the three
registers of an entry hold at every cycle: if `k` issues have been made so
far, then `left` is the number remaining, `cur` is the item of issue `k`, and
`wait` is the distance in cycles to the time of issue `k`.
-/

namespace Tau

variable {α : Type}

/-! ## The times of the issues increase -/

theorem Entry.timeAt_lt (e : Entry α) (i j : Nat) (h : i < j) : e.timeAt i < e.timeAt j := by
  sorry

/-! ## The specification, read off -/

theorem Entry.dueUpTo_none (e : Entry α) (t n : Nat) (h : ∀ i, i ≤ n → e.timeAt i ≠ t) :
    e.dueUpTo t n = none := by
  sorry

theorem Entry.dueUpTo_some (e : Entry α) (t n k : Nat) (hk : k ≤ n) (hkt : e.timeAt k = t) :
    e.dueUpTo t n = some (e.itemAt k) := by
  sorry

/-! ## What the registers hold -/

/-- At the start of cycle `t`, some number `k` of issues have been made. The
registers hold the number left, the item of issue `k`, and the number of
cycles until issue `k`. -/
theorem Entry.slotAt_spec (e : Entry α) (t : Nat) :
    ∃ k w, k ≤ e.repeats + 1 ∧
      e.slotAt t = ⟨e.repeats + 1 - k, w, e.itemAt k⟩ ∧
      (∀ i, i < k → e.timeAt i < t) ∧
      (k ≤ e.repeats → e.timeAt k = t + w) := by
  -- Outline of one proof:
  -- Induction on the cycle. At cycle 0 no issue has been made (k = 0).
  -- In the step case there are three situations, the three branches of
  -- `Slot.step`: every issue has been made (k stays), the wait is over
  -- (k becomes k + 1), or still waiting (the wait goes down by one).
  sorry

/-- The registers issue exactly what the specification says. -/
theorem Entry.step_slotAt (e : Entry α) (t : Nat) :
    (Slot.step e (e.slotAt t)).2 = e.dueAt t := by
  -- Outline of one proof:
  -- Take the invariant for cycle t and follow the three branches of
  -- `Slot.step`. When nothing is issued, no issue has its time equal to t:
  -- the earlier ones are before t and the later ones after.
  sorry

/-! ## The whole repeater -/

theorem stepSlots_map (prog : List (Entry α)) (g : Entry α → Slot α) :
    stepSlots prog (prog.map g) = prog.map fun e => Slot.step e (g e) := by
  sorry

/-- One cycle of a repeater whose registers are those of cycle `t`: the
registers become those of cycle `t + 1`, and the items issued are those the
specification gives for cycle `t`. -/
theorem repeater_step (prog : List (Entry α)) (t : Nat) :
    (repeater prog).step (prog.map fun e => e.slotAt t) () =
      (prog.map fun e => e.slotAt (t + 1), prog.filterMap fun e => e.dueAt t) := by
  sorry

/-- The state of a repeater at cycle `t` is every entry's registers at `t`. -/
theorem repeater_stateAt (prog : List (Entry α)) (inp : Signal Unit) (t : Nat) :
    (repeater prog).stateAt inp t = prog.map fun e => e.slotAt t := by
  sorry

/-- At cycle `t` a repeater issues, in program order, the item of every entry
that the specification says is due at `t`. -/
theorem repeater_outAt (prog : List (Entry α)) (inp : Signal Unit) (t : Nat) :
    (repeater prog).outAt inp t = prog.filterMap fun e => e.dueAt t := by
  sorry

end Tau
