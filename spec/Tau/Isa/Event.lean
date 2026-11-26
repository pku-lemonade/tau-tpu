/-!
# Pins and events

A program computes buffers. With *pins* it also says when. A pin is attached
to one operation and names a cycle: the operation's word must be issued on
that cycle. For an operation with a result, the word is the result, and it is
issued when the instruction that produces it runs. For a store, the word is
the one stored, and it is issued when it is written.

Every form of a program has pins (`spec/Tau/IR/Source.lean`, `spec/Tau/IR/Kernel.lean`,
`spec/Tau/IR/Placed.lean`). In the last form, `spec/Tau/IR/Compiled.lean`, every
instruction has a cycle, so every instruction is pinned.

What a pin claims is an *event*: this word, on this cycle. Running any form
gives its list of events, its *timeline*. A later form keeps the pins of an
earlier one if its timeline contains the earlier timeline. Every check asks
for that (`covers` in `spec/Tau/Check/Checker.lean`).

An event does not say which slice issues the word. Two operations that
compute the same word on the same cycle make the same event.

Cycles are counted from the start of the program, which is cycle 0.

Terms to look up: *timing constraint*, *observable behaviour*.

Docs: Programs 5 and 6, Machine 3.9 (`docs/`).
-/

namespace Tau

/-- A word issued on a cycle. -/
structure Event (V : Type) where
  /-- The cycle. -/
  time : Nat
  /-- For a store, the buffer and the position in it that the word goes to.
  `none` for a word put on a stream. -/
  store : Option (Nat × Nat)
  /-- The word. -/
  word : V
  deriving DecidableEq, Repr

variable {V W : Type}

/-- Apply `f` to the word of an event. -/
def Event.map (f : V → W) (e : Event V) : Event W := ⟨e.time, e.store, f e.word⟩

/-- A word issued by a slice: the cycle, the position of the slice, the
address if the word is written to memory, and the word. The placed form and
the machine give these; `Issue.event` (`spec/Tau/IR/MemMap.lean`) turns one into
an event. -/
structure Issue (V : Type) where
  /-- The cycle. -/
  time : Nat
  /-- The position of the slice. -/
  slice : Nat
  /-- For a write, the address. -/
  addr : Option Nat
  /-- The word. -/
  word : V
  deriving DecidableEq, Repr

/-- Apply `f` to the word of an issue. -/
def Issue.map (f : V → W) (x : Issue V) : Issue W := ⟨x.time, x.slice, x.addr, f x.word⟩

end Tau
