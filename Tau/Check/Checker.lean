import Tau.SliceLevel.Machine
import Tau.IR.Kernel
import Tau.Passes.Simplify

/-!
# The schedule checker

The compiler turns a kernel into a program for the machine: it decides which
memory holds each buffer, which slice runs each operation, on which cycle, and
on which streams the words travel. Any of those decisions can be wrong.

The checker decides whether a compiled program is right, without looking at how
the compiler made its decisions. It runs the machine on the compiled program
and it runs the kernel, both over expressions instead of real words
(`Tau/IR/Expr.lean`). Each run ends with an expression for every word of every
buffer. If the two runs end with the same expressions, the compiled program
computes what the kernel computes, whatever the buffers hold.

The checker is the machine itself, run on names instead of numbers. That is why
it needs no separate rules about timing, stream reuse or hazards.

The proof that an accepted program is correct is in `Tau/Proofs/Check/`.

Terms to look up: *translation validation*.
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

/-- A compiled program together with the chip it is for. -/
structure Compiled where
  /-- The chip the program is for. -/
  cfg : Config
  /-- The number of words in the memory at each position. -/
  memSizes : List Nat
  /-- Where each buffer lives. -/
  map : MemMap
  /-- The timed instructions. -/
  prog : Program
  /-- The number of cycles to run. -/
  cycles : Nat
  deriving Repr

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

/-- The starting memory contents for the given buffer contents. -/
def Compiled.image (c : Compiled) (bufs : List (List V)) (fill : V) : List (List V) :=
  Tau.image c.map c.memSizes (bufWord bufs fill) fill

/-- Read the buffers back out of the memory contents. -/
def extract (map : MemMap) (mem : List (List V)) (fill : V) : List (List V) :=
  map.map fun pl =>
    (List.range pl.size).map fun k => (mem[pl.slice]?.getD [])[pl.base + k]?.getD fill

/-- Buffers of the given sizes whose words are the expressions `init b k`. -/
def symBufs (sizes : List Nat) : List (List Expr) :=
  (List.range sizes.length).map fun b =>
    (List.range (sizes[b]?.getD 0)).map fun k => Expr.init b k

/-- The expressions the machine ends with, for every word of every buffer.
`none` if the machine traps. -/
def machineExprs (c : Compiled) : Option (List (List Expr)) :=
  match execute exprSem c.cfg c.prog c.cycles (image c.map c.memSizes Expr.init .fill) with
  | .ok mem => some (extract c.map mem .fill)
  | .error _ => none

/-- The expressions the kernel ends with, for every word of every buffer. -/
def kernelExprs (k : Kernel) (sizes : List Nat) : Option (List (List Expr)) :=
  k.run exprSem (symBufs sizes)

/-- Accept or reject a compiled program for the kernel `k`, whose buffers have
the given sizes. -/
def check (k : Kernel) (sizes : List Nat) (c : Compiled) : Bool :=
  c.map.map (·.size) == sizes &&
  match machineExprs c, kernelExprs k sizes with
  | some m, some e => m.map (·.map Expr.simp) == e.map (·.map Expr.simp)
  | _, _ => false

end Tau
