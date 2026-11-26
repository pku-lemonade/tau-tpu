import Tau.Blocks.Basic

/-!
# Memory

A memory is a row of `n` words, each with an address from `0` to `n - 1`. On
each cycle it can read one word, write one word, or do nothing. A read returns
the word in the same cycle. A write takes effect from the next cycle.

In tau-tpu a memory slice is a memory followed by a pipeline.

Terms to look up: *random-access memory*, *address*, *read port*, *write port*.

Docs: Machine 2.5 (`Tau/Docs/`).
-/

namespace Tau

/-- What a memory is told to do in one cycle. -/
inductive MemIn (α : Type) where
  /-- Do nothing. -/
  | idle
  /-- Read the word at `addr`. -/
  | read (addr : Nat)
  /-- Write `x` to the word at `addr`. -/
  | write (addr : Nat) (x : α)
  deriving Repr, DecidableEq

variable {α : Type}

/-- A memory of `n` words with the starting contents `init`.
The output is `some x` for a read of a valid address and `none` otherwise.
A write to an address outside the memory changes nothing. -/
def memory (n : Nat) (init : Vector α n) : Block (Vector α n) (MemIn α) (Option α) where
  init := init
  step s c :=
    match c with
    | .idle => (s, none)
    | .read a => (s, s[a]?)
    | .write a x => (s.setIfInBounds a x, none)

/-- The value most recently written to address `a` before cycle `t`, if any. -/
def lastWrite (inp : Signal (MemIn α)) (a : Nat) : Nat → Option α
  | 0 => none
  | t + 1 =>
    match inp t with
    | .write a' x => if a' = a then some x else lastWrite inp a t
    | _ => lastWrite inp a t

/-- Write 7 to address 1 at cycle 0, then read address 1 and address 0. -/
example :
    (memory 2 #v[10, 11]).trace
      (fun t => if t = 0 then .write 1 7 else if t = 1 then .read 1 else .read 0) 3
      = [none, some 7, some 10] := by
  decide

end Tau
