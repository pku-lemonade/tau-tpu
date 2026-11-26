import Tau.Blocks.Basic

/-!
# Sequencer

A sequencer holds a program: a list of items, each with the cycle at which it
is to be issued. It counts cycles, and on each cycle it outputs the items due.

In tau-tpu every slice has a sequencer. This is where static scheduling lives:
the time of every instruction is fixed in the program, not decided while the
machine runs.

Terms to look up: *program counter*, *static scheduling*.

Docs: Machine 2.6 (`docs/`).
-/

namespace Tau

variable {α : Type}

/-- The items of `prog` that are due at cycle `t`. -/
def dueAt (prog : List (Nat × α)) (t : Nat) : List α :=
  (prog.filter fun e => e.1 == t).map fun e => e.2

/-- A sequencer for the program `prog`. Its state is the cycle count. -/
def sequencer (prog : List (Nat × α)) : Block Nat Unit (List α) where
  init := 0
  step t _ := (t + 1, dueAt prog t)

example :
    (sequencer [(1, "read"), (3, "add"), (3, "write")]).trace (fun _ => ()) 4
      = [[], ["read"], [], ["add", "write"]] := by
  decide

end Tau
