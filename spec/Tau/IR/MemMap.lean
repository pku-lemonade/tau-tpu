import Tau.Isa.Event

/-!
# The memory map

A kernel names its buffers by number. On the machine, a buffer is a run of words
in the memory of one slice, or of several: its words are then dealt out over
those slices in turn, so that words that follow one another can be read on
one cycle. The memory map says, for every buffer, which slices and which
addresses. `tau-place` decides it, and every later IR of the program carries
it (`Tau.IR.Placed`, `Tau.IR.Compiled`).

`image` turns buffer contents into the starting contents of every memory, and
`extract` reads the buffers back out at the end. Every theorem that says a
program computes a kernel is stated with these two. `Issue.event` says which
buffer word a write at an address is a store to.

The theorems about them are in `Tau.Proofs.IR.MemMap`.

Docs: Compiler 3 (`docs/`).
-/

namespace Tau

/-- One part of a buffer: a memory slice and the address of the part's first
word. -/
structure Part where
  /-- The position of the memory slice. -/
  slice : Nat
  /-- The address of the part's first word. -/
  base : Nat
  deriving DecidableEq, Repr

/-- Where a buffer lives: its parts and its length. The words are dealt out
over the parts in turn. With `g` parts, word `k` is in part `k % g`, `k / g`
words after that part's first. A buffer with one part is a run of words in
one memory. -/
structure Placement where
  /-- The parts, in the order the words are dealt to them. -/
  parts : List Part
  /-- The number of words. -/
  size : Nat
  deriving DecidableEq, Repr

/-- A buffer in one memory: `size` words of the slice at `slice`, from address
`base` on. -/
def Placement.one (slice base size : Nat) : Placement := ⟨[⟨slice, base⟩], size⟩

/-- The slice and the address of word `k` of a buffer. `none` if the buffer
has no parts. -/
def Placement.locate (pl : Placement) (k : Nat) : Option (Nat × Nat) :=
  pl.parts[k % pl.parts.length]?.map fun part =>
    (part.slice, part.base + k / pl.parts.length)

/-- The word of a buffer stored at address `a` of slice `p`, if any: its
position in the buffer. -/
def Placement.find (pl : Placement) (p a : Nat) : Option Nat :=
  (List.range pl.parts.length).findSome? fun i =>
    match pl.parts[i]? with
    | some part =>
      if part.slice = p ∧ part.base ≤ a ∧ (a - part.base) * pl.parts.length + i < pl.size then
        some ((a - part.base) * pl.parts.length + i)
      else none
    | none => none

/-- The placement of every buffer, by buffer number. -/
abbrev MemMap := List Placement

variable {V : Type}

/-- Word `idx` of buffer `buf`, or `fill` if there is no such word. -/
def bufWord (bufs : List (List V)) (fill : V) (buf idx : Nat) : V :=
  (bufs[buf]?.getD [])[idx]?.getD fill

/-- The buffer word stored at address `a` of slice `p`, if any: the number of
the buffer and the position within it. -/
def MemMap.findFrom (p a : Nat) : Nat → MemMap → Option (Nat × Nat)
  | _, [] => none
  | b, pl :: rest =>
    match pl.find p a with
    | some k => some (b, k)
    | none => MemMap.findFrom p a (b + 1) rest

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
    (List.range pl.size).map fun k =>
      match pl.locate k with
      | some (p, a) => (mem[p]?.getD [])[a]?.getD fill
      | none => fill

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
