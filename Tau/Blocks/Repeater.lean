import Tau.Blocks.Basic

/-!
# Repeater

A repeater is a sequencer whose entries can repeat. An entry says: issue this
item at this cycle, then issue it again a number of times, waiting a fixed
number of cycles in between, and change the item in a fixed way each time.

A plain sequencer (`Tau/Blocks/Sequencer.lean`) could be built with nothing
but a cycle counter. A repeater needs real state. For every entry it keeps
three registers: how many issues are left, how many cycles until the next
one, and the item it will issue next. No cycle count is compared with
anything. Each entry just counts down.

This file gives two descriptions of the same behaviour.

* `Entry.dueAt` says *what* is issued at each cycle, with no state: issue
  number `i` happens at cycle `timeAt i` and carries `itemAt i`.
* `repeater` says *how*, with the three registers.

`Tau/Proofs/Blocks/Repeater.lean` proves they agree.

In tau-tpu every slice has a repeater. Reading the columns of a matrix out of
memory on consecutive cycles is one entry: read, repeat, and add one to the
address each time.

Terms to look up: *down counter*, *loop counter*.
-/

namespace Tau

variable {α : Type}

/-- One entry of a repeating program. -/
structure Entry (α : Type) where
  /-- The cycle of the first issue. -/
  time : Nat
  /-- The number of further issues after the first. -/
  repeats : Nat
  /-- The number of idle cycles between two issues. -/
  gap : Nat
  /-- The item issued first. -/
  first : α
  /-- How the item changes from one issue to the next. -/
  next : α → α

/-- The item carried by issue number `i`. -/
def Entry.itemAt (e : Entry α) : Nat → α
  | 0 => e.first
  | i + 1 => e.next (e.itemAt i)

/-- The cycle of issue number `i`. -/
def Entry.timeAt (e : Entry α) : Nat → Nat
  | 0 => e.time
  | i + 1 => e.timeAt i + e.gap + 1

/-- The item issued at cycle `t` by one of the issues `0` to `n`, if any. -/
def Entry.dueUpTo (e : Entry α) (t : Nat) : Nat → Option α
  | 0 => if e.timeAt 0 = t then some (e.itemAt 0) else none
  | i + 1 => if e.timeAt (i + 1) = t then some (e.itemAt (i + 1)) else e.dueUpTo t i

/-- The item this entry issues at cycle `t`, if any. This is the
specification of a repeater: it mentions no registers. -/
def Entry.dueAt (e : Entry α) (t : Nat) : Option α := e.dueUpTo t e.repeats

/-- The three registers a repeater keeps for one entry. -/
structure Slot (α : Type) where
  /-- The number of issues still to make. -/
  left : Nat
  /-- The number of cycles until the next issue. -/
  wait : Nat
  /-- The item the next issue will carry. -/
  cur : α

/-- The registers of an entry at cycle 0. -/
def Entry.start (e : Entry α) : Slot α := ⟨e.repeats + 1, e.time, e.first⟩

/-- One cycle of one entry's registers. If nothing is left, nothing happens.
If the wait is over, the item is issued, the count goes down, the wait is
reloaded and the item advances. Otherwise the wait goes down by one. -/
def Slot.step (e : Entry α) (s : Slot α) : Slot α × Option α :=
  if s.left = 0 then (s, none)
  else if s.wait = 0 then (⟨s.left - 1, e.gap, e.next s.cur⟩, some s.cur)
  else (⟨s.left, s.wait - 1, s.cur⟩, none)

/-- One cycle of every entry's registers. -/
def stepSlots : List (Entry α) → List (Slot α) → List (Slot α × Option α)
  | e :: es, s :: ss => Slot.step e s :: stepSlots es ss
  | _, _ => []

/-- A repeater for the program `prog`. Its state is the registers of every
entry. Its output is the items issued this cycle, in program order. -/
def repeater (prog : List (Entry α)) : Block (List (Slot α)) Unit (List α) where
  init := prog.map Entry.start
  step ss _ := ((stepSlots prog ss).map (·.1), (stepSlots prog ss).filterMap (·.2))

/-- The registers of an entry at the start of cycle `t`. -/
def Entry.slotAt (e : Entry α) : Nat → Slot α
  | 0 => e.start
  | t + 1 => (Slot.step e (e.slotAt t)).1

/-- Read addresses 5, 6, 7 on cycles 2, 4, 6. -/
example :
    (repeater [({ time := 2, repeats := 2, gap := 1, first := 5, next := (· + 1) } : Entry Nat)]).trace
      (fun _ => ()) 8
      = [[], [], [5], [], [6], [], [7], []] := by
  decide

end Tau
