/-
Exercise file. Generated from Tau/Proofs/Blocks/Repeater.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/Blocks/Repeater.lean.
Only some proofs are taken out. The others are given, and you may use them.
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
  induction j with
  | zero => omega
  | succ j ih =>
    simp only [Entry.timeAt]
    by_cases hij : i = j
    · subst hij; omega
    · have := ih (by omega)
      omega

/-! ## The specification, read off -/

theorem Entry.dueUpTo_none (e : Entry α) (t n : Nat) (h : ∀ i, i ≤ n → e.timeAt i ≠ t) :
    e.dueUpTo t n = none := by
  induction n with
  | zero => simp [Entry.dueUpTo, h 0 (by omega)]
  | succ n ih =>
    simp only [Entry.dueUpTo, h (n + 1) (by omega), ↓reduceIte]
    exact ih (fun i hi => h i (by omega))

theorem Entry.dueUpTo_some (e : Entry α) (t n k : Nat) (hk : k ≤ n) (hkt : e.timeAt k = t) :
    e.dueUpTo t n = some (e.itemAt k) := by
  induction n with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    simp [Entry.dueUpTo, hkt]
  | succ n ih =>
    by_cases hkn : k = n + 1
    · subst hkn
      simp [Entry.dueUpTo, hkt]
    · have hlt := e.timeAt_lt k (n + 1) (by omega)
      have hne : e.timeAt (n + 1) ≠ t := by omega
      simp only [Entry.dueUpTo, hne, ↓reduceIte]
      exact ih (by omega)

/-! ## What the registers hold -/

/-- At the start of cycle `t`, some number `k` of issues have been made. The
registers hold the number left, the item of issue `k`, and the number of
cycles until issue `k`. -/
theorem Entry.slotAt_spec (e : Entry α) (t : Nat) :
    ∃ k w, k ≤ e.repeats + 1 ∧
      e.slotAt t = ⟨e.repeats + 1 - k, w, e.itemAt k⟩ ∧
      (∀ i, i < k → e.timeAt i < t) ∧
      (k ≤ e.repeats → e.timeAt k = t + w) := by
  -- Induction on the cycle. At cycle 0 no issue has been made (k = 0).
  -- In the step case there are three situations, the three branches of
  -- `Slot.step`: every issue has been made (k stays), the wait is over
  -- (k becomes k + 1), or still waiting (the wait goes down by one).
  induction t with
  | zero =>
    refine ⟨0, e.time, by omega, rfl, by omega, ?_⟩
    intro _
    simp [Entry.timeAt]
  | succ t ih =>
    obtain ⟨k, w, hk, hs, hlt, heq⟩ := ih
    simp only [Entry.slotAt, hs, Slot.step]
    by_cases hdone : e.repeats + 1 - k = 0
    · -- every issue has been made
      refine ⟨k, w, hk, by simp [hdone], fun i hi => by have := hlt i hi; omega, by omega⟩
    · have hkr : k ≤ e.repeats := by omega
      have htime := heq hkr
      by_cases hw : w = 0
      · -- the wait is over: issue number `k` happens now
        subst hw
        refine ⟨k + 1, e.gap, by omega, ?_, ?_, ?_⟩
        · simp only [hdone, ↓reduceIte, Entry.itemAt]
          congr 1
        · intro i hi
          by_cases hik : i = k
          · subst hik; omega
          · have := hlt i (by omega); omega
        · intro _
          simp only [Entry.timeAt]
          omega
      · -- still waiting
        refine ⟨k, w - 1, hk, by simp [hdone, hw], fun i hi => by have := hlt i hi; omega, ?_⟩
        intro _
        omega

/-- The registers issue exactly what the specification says. -/
theorem Entry.step_slotAt (e : Entry α) (t : Nat) :
    (Slot.step e (e.slotAt t)).2 = e.dueAt t := by
  -- Take the invariant for cycle t and follow the three branches of
  -- `Slot.step`. When nothing is issued, no issue has its time equal to t:
  -- the earlier ones are before t and the later ones after.
  obtain ⟨k, w, hk, hs, hlt, heq⟩ := e.slotAt_spec t
  unfold Entry.dueAt
  rw [hs]
  simp only [Slot.step]
  by_cases hdone : e.repeats + 1 - k = 0
  · simp only [hdone, ↓reduceIte]
    symm
    apply e.dueUpTo_none
    intro i hi
    have := hlt i (by omega)
    omega
  · have hkr : k ≤ e.repeats := by omega
    have htime := heq hkr
    by_cases hw : w = 0
    · subst hw
      simp only [hdone, ↓reduceIte]
      symm
      exact e.dueUpTo_some t e.repeats k hkr (by omega)
    · simp only [hdone, hw, ↓reduceIte]
      symm
      apply e.dueUpTo_none
      intro i hi
      by_cases hik : i < k
      · have := hlt i hik; omega
      · by_cases hik' : i = k
        · subst hik'; omega
        · have := e.timeAt_lt k i (by omega); omega

/-! ## The whole repeater -/

theorem stepSlots_map (prog : List (Entry α)) (g : Entry α → Slot α) :
    stepSlots prog (prog.map g) = prog.map fun e => Slot.step e (g e) := by
  induction prog with
  | nil => rfl
  | cons e rest ih => simp only [List.map_cons, stepSlots, ih]

/-- One cycle of a repeater whose registers are those of cycle `t`: the
registers become those of cycle `t + 1`, and the items issued are those the
specification gives for cycle `t`. -/
theorem repeater_step (prog : List (Entry α)) (t : Nat) :
    (repeater prog).step (prog.map fun e => e.slotAt t) () =
      (prog.map fun e => e.slotAt (t + 1), prog.filterMap fun e => e.dueAt t) := by
  have hout : (fun e : Entry α => (Slot.step e (e.slotAt t)).2) = fun e => e.dueAt t :=
    funext fun e => e.step_slotAt t
  simp only [repeater, stepSlots_map, List.map_map, List.filterMap_map]
  refine Prod.ext ?_ ?_
  · rfl
  · exact congrArg (fun g => prog.filterMap g) hout

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
