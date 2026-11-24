import Tau.Isa.Op

/-!
# Instructions and programs

A tau-tpu chip is a row of slices. Between them run *streams*: tracks that
carry words east or west, one slice per cycle. An instruction tells one slice
what to do on one cycle: which stream slots to read, what to compute, and which
stream to put the result on.

A program is a list of instructions, each with its slice and its cycle. There
are no branches and no waiting. Everything that will happen is in the list.

Terms to look up: *instruction set architecture*, *static scheduling*.
-/

namespace Tau

/-- The direction a stream moves in. -/
inductive Dir where
  /-- Towards higher positions. -/
  | east
  /-- Towards lower positions. -/
  | west
  deriving DecidableEq, Repr

/-- A stream: a direction and a number. -/
structure Track where
  /-- The direction the stream moves in. -/
  dir : Dir
  /-- Its number among the streams going that way. -/
  id : Nat
  deriving DecidableEq, Repr

/-- What a slice can be told to do. -/
inductive Instr where
  /-- Memory: put the word at `addr` on `dst`. -/
  | read (addr : Nat) (dst : Track)
  /-- Memory: store the word on `src` at `addr`. -/
  | write (src : Track) (addr : Nat)
  /-- Vector or rearrangement: apply `op` to the word on `src`. -/
  | un (op : UnOp) (src dst : Track)
  /-- Vector: apply `op` to the words on `a` and `b`. -/
  | bin (op : BinOp) (a b dst : Track)
  /-- Matrix: keep the word on `src` as the vector operand. -/
  | load (src : Track)
  /-- Matrix: add lane `j` of the vector operand, times the word on `src`, to
  the accumulator. -/
  | mac (j : Nat) (src : Track)
  /-- Matrix: put the accumulator on `dst` and clear it. -/
  | emit (dst : Track)
  deriving DecidableEq, Repr

/-- An instruction together with its slice and its cycle. -/
structure Timed where
  /-- The position of the slice that executes the instruction. -/
  slice : Nat
  /-- The cycle on which it is issued. -/
  time : Nat
  /-- What the slice is told to do. -/
  instr : Instr
  deriving DecidableEq, Repr

/-- A program: every instruction the chip will execute. -/
abbrev Program := List Timed

/-- The instructions that slice `p` must execute at cycle `t`. -/
def Program.dueAt (prog : Program) (p t : Nat) : List Instr :=
  (prog.filter fun e => e.slice == p && e.time == t).map fun e => e.instr

/-- The shape of a chip. -/
structure Config where
  /-- The kind of slice at each position, from west to east. -/
  kinds : List Kind
  /-- The number of streams in each direction. -/
  streams : Nat
  /-- The number of cycles a result spends inside a memory slice. -/
  memDelay : Nat
  /-- The number of cycles a result spends inside a vector slice. -/
  vxmDelay : Nat
  /-- The number of cycles a result spends inside a rearrangement slice. -/
  sxmDelay : Nat
  /-- The number of cycles a result spends inside a matrix slice. -/
  mxmDelay : Nat
  deriving Repr

/-- The number of cycles a result spends inside a slice of kind `k`. A result
computed at cycle `t` is on the stream, at the slice's position, at cycle
`t + delay + 1`. -/
def Config.delay (cfg : Config) : Kind → Nat
  | .mem => cfg.memDelay
  | .vxm => cfg.vxmDelay
  | .sxm => cfg.sxmDelay
  | .mxm => cfg.mxmDelay

/-- The kind of slice at position `p`. -/
def Config.kindAt (cfg : Config) (p : Nat) : Option Kind := cfg.kinds[p]?

end Tau
