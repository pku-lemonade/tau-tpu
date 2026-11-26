import Tau.Blocks.Basic

/-!
# Accumulator

An accumulator holds a running total. On each cycle it is told to add a value,
to hold, to clear back to zero, or to load a new total. Its output is the total at the start of the
cycle.

In tau-tpu the matrix slice has one accumulator per lane.

Terms to look up: *accumulator*, *register with enable*.

Docs: Machine 2.2 (`docs/`).
-/

namespace Tau

/-- What an accumulator is told to do in one cycle. -/
inductive AccIn (α : Type) where
  /-- Keep the total. -/
  | hold
  /-- Add `x` to the total. -/
  | add (x : α)
  /-- Reset the total to zero. -/
  | clear
  /-- Replace the total by `x`. -/
  | load (x : α)
  deriving Repr, DecidableEq

/-- Apply `f` to the value carried by an `add`. -/
def AccIn.map {α β : Type} (f : α → β) : AccIn α → AccIn β
  | .hold => .hold
  | .add x => .add (f x)
  | .clear => .clear
  | .load x => .load (f x)

variable {α : Type}

/-- An accumulator that starts at `zero`. -/
def accumulator [Add α] (zero : α) : Block α (AccIn α) α where
  init := zero
  step s c :=
    match c with
    | .hold => (s, s)
    | .add x => (s + x, s)
    | .clear => (zero, s)
    | .load x => (x, s)

example : (accumulator (0 : Nat)).trace (fun t => .add (t + 1)) 5 = [0, 1, 3, 6, 10] := by
  decide

end Tau
