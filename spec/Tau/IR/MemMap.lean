import Tau.Isa.Event

/-!
# The memory map

A kernel names its buffers by number. On the machine, a buffer is a run of words
in the memory of one slice. The memory map says, for every buffer, which
slice and which addresses. `tau-place` decides it, and every later form of
the program carries it (`spec/Tau/IR/Placed.lean`, `spec/Tau/IR/Compiled.lean`).

`image` turns buffer contents into the starting contents of every memory, and
`extract` reads the buffers back out at the end. Every theorem that says a
program computes a kernel is stated with these two. `Issue.event` says which
buffer word a write at an address is a store to.

The theorems about them are in `spec/Tau/Proofs/IR/MemMap.lean`.

Docs: Compiler 3 (`docs/`).
-/

namespace Tau

/-- Where a buffer lives: a memory slice, a starting address, and a length. -/
structure Placement where
  /-- The position of the memory slice. -/
  slice : Nat
  /-- The address of the buffer's first word. -/
  base : Nat
  /-- The number of words. -/
  size : Nat
  deriving DecidableEq, Repr

/-- The placement of every buffer, by buffer number. -/
abbrev MemMap := List Placement

variable {V : Type}

/-- The buffer word stored at address `a` of slice `p`, if any: the number of
the buffer and the position within it. -/
def MemMap.findFrom (p a : Nat) : Nat → MemMap → Option (Nat × Nat)
  | _, [] => none
  | b, pl :: rest =>
    if pl.slice = p ∧ pl.base ≤ a ∧ a < pl.base + pl.size then some (b, a - pl.base)
    else MemMap.findFrom p a (b + 1) rest

/-- The starting memory contents of every slice. `word b k` is word `k` of
buffer `b`; addresses that belong to no buffer hold `fill`. -/
def image (map : MemMap) (memSizes : List Nat) (word : Nat → Nat → V) (fill : V) :
    List (List V) :=
  (List.range memSizes.length).map fun p =>
    (List.range (memSizes[p]?.getD 0)).map fun a =>
      match MemMap.findFrom p a 0 map with
      | some (b, k) => word b k
      | none => fill

/-- Read the buffers back out of the memory contents. -/
def extract (map : MemMap) (mem : List (List V)) (fill : V) : List (List V) :=
  map.map fun pl =>
    (List.range pl.size).map fun k => (mem[pl.slice]?.getD [])[pl.base + k]?.getD fill

/-- The event an issue makes. A write to a buffer word is a store to that
buffer. A write to scratch memory, which belongs to no buffer, makes no
event. -/
def Issue.event (map : MemMap) (x : Issue V) : Option (Event V) :=
  match x.addr with
  | none => some ⟨x.time, none, x.word⟩
  | some a =>
    match MemMap.findFrom x.slice a 0 map with
    | some bk => some ⟨x.time, some bk, x.word⟩
    | none => none

end Tau
