import Tau.SliceLevel.Issues
import Tau.IR.MemMap
import Tau.IR.Expr

/-!
# Compiled programs

The last form a program takes in the compiler: every instruction has a slice,
a cycle and streams. It is the output of `tau-schedule`, `tau-route`,
`tau-slice` and `tau-fold`. The first two differ in how many streams they
use. The last two differ in how the same instructions are written down:
slice by slice, and with runs merged into repeating entries. An image
(`Tau/Isa/Encode.lean`) decodes to this form too.

A compiled program is a `Program` (`Tau/Isa/Instr.lean`) together with the
machine it is for, the memory map and the number of cycles to run. What it
computes is what the machine does with it: `execute` in
`Tau/SliceLevel/Machine.lean`.

Every instruction of a compiled program has a cycle, so every word it issues
is an event (`Tau/Isa/Event.lean`). `Compiled.timeline` lists them. The pins
of the earlier forms are checked against this list.

The four forms, in order: `Tau/IR/Source.lean`, `Tau/IR/Kernel.lean`,
`Tau/IR/Placed.lean`, this file.

Docs: Compiler 2 (`Tau/Docs/`).
-/

namespace Tau

/-- A compiled program together with the machine it is for. -/
structure Compiled where
  /-- The machine the program is for. -/
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

/-- The starting memory contents for the given buffer contents. -/
def Compiled.image (c : Compiled) (bufs : List (List V)) (fill : V) : List (List V) :=
  Tau.image c.map c.memSizes (bufWord bufs fill) fill

/-- The events of a run from a memory image: every word a slice issues, with
its cycle. A write to a buffer word is a store to that buffer. -/
def Compiled.timelineFrom (S : Sem V) (c : Compiled) (image : List (List V)) :
    List (Event V) :=
  (issues S c.cfg c.prog c.cycles image).filterMap (Issue.event c.map)

/-- The events of a run on the given buffer contents. -/
def Compiled.timeline (S : Sem V) (c : Compiled) (bufs : List (List V)) (fill : V) :
    List (Event V) :=
  c.timelineFrom S (c.image bufs fill)

end Tau
