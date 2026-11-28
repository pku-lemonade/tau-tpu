import Tau.Isa.Op
import Tau.Blocks.Repeater

/-!
# Instructions and programs

A tau-tpu machine is a row of slices. Between them run *streams*, which
carry words east or west, one slice per cycle. An instruction tells one slice
what to do on one cycle: which stream slots to read, what to compute, and which
stream to put the result on. A value of several words (`Tau.Isa.Word`) is on
as many streams that follow one another, its low word on the first, and an
instruction names the first. A slice runs one instruction on a cycle. A
memory slice can run two, a read and a write, if they are for different
banks of its memory (`Config.bank`).

A program is a list of instructions, each with its slice and its cycle. There
are no branches and no waiting. Everything that will happen is in the list.

An entry of the list may repeat: issue again a number of times, a fixed
number of cycles apart, with the address, or the first installed word,
stepping by a fixed amount. What an entry issues at each cycle is given by `Entry.dueAt` in
`Tau.Blocks.Repeater`.

Terms to look up: *instruction set architecture*, *static scheduling*.

Docs: Machine 3.1, 3.2, 3.5 and 3.8 (`docs/`).
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
structure Stream where
  /-- The direction the stream moves in. -/
  dir : Dir
  /-- Its number among the streams going that way. -/
  id : Nat
  deriving DecidableEq, Repr

/-- The stream `k` places after `s`, going the same way. An instruction that
takes several words at once names the first stream and takes the next ones
too. -/
def Stream.next (s : Stream) (k : Nat) : Stream := ⟨s.dir, s.id + k⟩

/-- Whether a value of `w` words may start on the stream `s`: the number of
`s` is a multiple of `w`. -/
def Stream.aligned (s : Stream) (w : Nat) : Bool := s.id % w == 0

/-- What a slice can be told to do. -/
inductive Instr where
  /-- Memory: put the word at `addr` on `dst`. -/
  | read (addr : Nat) (dst : Stream)
  /-- Memory: store the word on `src` at `addr`. -/
  | write (src : Stream) (addr : Nat)
  /-- Vector or rearrangement: apply `op` to the value of type `ty` on
  `src`. -/
  | un (ty : DType) (op : UnOp) (src dst : Stream)
  /-- Vector: apply `op` to the values of type `ty` on `a` and `b`. -/
  | bin (ty : DType) (op : BinOp) (a b dst : Stream)
  /-- Vector: put the constant of type `ty` with elements `xs` on `dst`. -/
  | const (ty : DType) (xs : List Int) (dst : Stream)
  /-- Vector: element by element, the value on `a` where the value on `m` is
  not zero and the value on `b` elsewhere. All are of type `ty`. -/
  | sel (ty : DType) (m a b dst : Stream)
  /-- Matrix: keep the words on `src` and the `g - 1` streams after it as
  installed words `j` to `j + g - 1`. -/
  | install (j g : Nat) (src : Stream)
  /-- Matrix: put the product of the first `n` installed words with the word
  on `src` on `dst`, as a value of 32 bits. -/
  | product (n : Nat) (src dst : Stream)
  deriving DecidableEq, Repr

/-- The name of an instruction, as Formats 3 writes it: the operation of `un`
and `bin`, and the instruction itself otherwise. A machine's own delays are
given by these names. -/
def Instr.name : Instr → String
  | .read .. => "read"
  | .write .. => "write"
  | .un _ op .. => op.name
  | .bin _ op .. => op.name
  | .const .. => "const"
  | .sel .. => "sel"
  | .install .. => "install"
  | .product .. => "product"

/-- The address of a memory instruction. Other instructions have none, and
give 0. -/
def Instr.addr : Instr → Nat
  | .read addr _ => addr
  | .write _ addr => addr
  | _ => 0

/-- A read and a write, the read first, if `i` and `j` are one of each in
either order. A memory slice can run such a pair on one cycle. -/
def Instr.readWrite : Instr → Instr → Option (Instr × Instr)
  | .read addr dst, .write src addr' => some (.read addr dst, .write src addr')
  | .write src addr', .read addr dst => some (.read addr dst, .write src addr')
  | _, _ => none

/-- Add `k` to the address of a memory instruction or to the first installed
word of an `install`. Other instructions are unchanged. -/
def Instr.bump (k : Nat) : Instr → Instr
  | .read addr dst => .read (addr + k) dst
  | .write src addr => .write src (addr + k)
  | .install j g src => .install (j + k) g src
  | i => i

/-- An instruction together with its slice and its cycle, and how it
repeats. -/
structure TimedEntry where
  /-- The position of the slice that executes the instruction. -/
  slice : Nat
  /-- The cycle on which it is first issued. -/
  time : Nat
  /-- What the slice is told to do. -/
  instr : Instr
  /-- The number of further issues after the first. -/
  repeats : Nat := 0
  /-- The number of idle cycles between two issues. -/
  gap : Nat := 0
  /-- How much the address, or the first installed word, grows from one issue
  to the next. -/
  stride : Nat := 0
  deriving DecidableEq, Repr

/-- An instruction issued once. -/
def TimedEntry.once (slice time : Nat) (instr : Instr) : TimedEntry := { slice, time, instr }

/-- A timed instruction as an entry of its slice's repeater. -/
def TimedEntry.entry (e : TimedEntry) : Entry Instr :=
  ⟨e.time, e.repeats, e.gap, e.instr, Instr.bump e.stride⟩

/-- A program: every instruction the machine will execute. -/
abbrev Program := List TimedEntry

/-- The instructions of the program that are for slice `p`. -/
def Program.entriesOf (prog : Program) (p : Nat) : Program :=
  prog.filter fun e => e.slice == p

/-- The entries of the program that are for slice `p`, as its repeater takes
them. -/
def Program.entriesFor (prog : Program) (p : Nat) : List (Entry Instr) :=
  (prog.entriesOf p).map TimedEntry.entry

/-- The instructions that slice `p` must execute at cycle `t`. -/
def Program.dueAt (prog : Program) (p t : Nat) : List Instr :=
  (prog.entriesFor p).filterMap fun e => e.dueAt t

/-- The shape of a machine. -/
structure Config where
  /-- The kind of slice at each position, from west to east. -/
  kinds : List Kind
  /-- The number of streams in each direction. -/
  streams : Nat
  /-- The number of lanes of a word. A matrix slice has one installed word
  for each lane. -/
  lanes : Nat
  /-- The number of words in the lower bank of a memory slice. The addresses
  from this number on are the upper bank. -/
  bankSize : Nat
  /-- The number of cycles a result spends inside a memory slice. -/
  memDelay : Nat
  /-- The number of cycles a result spends inside a vector slice. -/
  vxmDelay : Nat
  /-- The number of cycles a result spends inside a rearrangement slice. -/
  sxmDelay : Nat
  /-- The number of cycles a result spends inside a matrix slice. -/
  mxmDelay : Nat
  /-- Instructions and operations whose result spends a different number of
  cycles inside its slice from the rest of its kind: a name (`Instr.name`)
  and that number. -/
  delays : List (String × Nat) := []
  deriving Repr

/-- The delay of a slice of kind `k`: the number of cycles a result spends
inside it, unless the machine gives its instruction a delay of its own. -/
def Config.delay (cfg : Config) : Kind → Nat
  | .mem => cfg.memDelay
  | .vxm => cfg.vxmDelay
  | .sxm => cfg.sxmDelay
  | .mxm => cfg.mxmDelay

/-- The number of cycles the result of `i` spends inside a slice of kind `k`:
its own delay if the machine gives it one, and otherwise the delay of the
kind. A result computed at cycle `t` is on the stream, at the slice's
position, at cycle `t + delayOf k i + 1`. -/
def Config.delayOf (cfg : Config) (k : Kind) (i : Instr) : Nat :=
  ((cfg.delays.find? fun e => decide (e.1 = i.name)).map (·.2)).getD (cfg.delay k)

/-- The longest delay of the machine. Every slice's pipe has this many
slots. -/
def Config.maxDelay (cfg : Config) : Nat :=
  cfg.delays.foldr (fun e m => max e.2 m)
    (max (max cfg.memDelay cfg.vxmDelay) (max cfg.sxmDelay cfg.mxmDelay))

/-- The kind of slice at position `p`. -/
def Config.kindAt (cfg : Config) (p : Nat) : Option Kind := cfg.kinds[p]?

/-- Whether the machine has the `w` streams from `s` on, and a value of `w`
words may start there. -/
def Config.hasGroup (cfg : Config) (s : Stream) (w : Nat) : Bool :=
  s.aligned w && s.id + w ≤ cfg.streams

/-- The bank of a memory slice that holds address `a`: 0 for the lower bank
and 1 for the upper. -/
def Config.bank (cfg : Config) (a : Nat) : Nat := if a < cfg.bankSize then 0 else 1

/-- The instruction whose result the slice at `p` computes on cycle `t`: the
one instruction due, or the read when a read and a write are due together. -/
def Program.computes (prog : Program) (p t : Nat) : Option Instr :=
  match prog.dueAt p t with
  | [i] => some i
  | [i, j] => (Instr.readWrite i j).map (·.1)
  | _ => none

end Tau
