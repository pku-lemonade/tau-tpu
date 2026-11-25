import Tau.Isa.Instr
import Tau.IR.MemMap
import Tau.IR.Expr

/-!
# Compiled programs

The last form a program takes in the compiler: every instruction has a slice,
a cycle and streams. It is the output of `tau-schedule` and of `tau-route`,
which differ only in how many streams they use.

A compiled program is a `Program` (`Tau/Isa/Instr.lean`) together with the
chip it is for, the memory map and the number of cycles to run. What it
computes is what the machine does with it: `execute` in
`Tau/SliceLevel/Machine.lean`.

The three forms, in order: `Tau/IR/Kernel.lean`, `Tau/IR/Placed.lean`, this
file.
-/

namespace Tau

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

/-- The starting memory contents for the given buffer contents. -/
def Compiled.image (c : Compiled) (bufs : List (List V)) (fill : V) : List (List V) :=
  Tau.image c.map c.memSizes (bufWord bufs fill) fill

end Tau
