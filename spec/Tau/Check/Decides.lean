import Tau.Check.Passes
import Tau.IR.Unroll

/-!
# What each back-end pass decides

Compiler 4 gives each step of the back end one thing to decide: `tau-place`
decides where, `tau-schedule` when, and `tau-route` on which stream. The
checks of `Tau.Check.Passes` do not ask about that. They ask whether the
output of a pass computes what its input computes, on the same cycles, and
they accept an output that got there by doing another pass's work.

This file has one *rule* for each of the three. A rule compares the
instructions of the output with those of the input, without running either,
and says whether the two differ only in what the pass is there to decide.

| Pass | Rule | Its output |
|---|---|---|
| `tau-place` | `placeOnly` | has one instruction for each operation of the kernel, one write for each store, and no scratch space |
| `tau-schedule` | `scheduleOnly` | has the memory map of its input, every operation and every write to a buffer of its input, each on the same slice, and nothing else but reads of buffer words its input reads and writes and reads of scratch words |
| `tau-route` | `routeOnly` | is its input with other numbers for the streams |

A rule is not a check. It has no soundness theorem and needs none: a program
that breaks a rule can still be right, and the checks decide that. What a
rule says is that a pass left alone what the other passes decide. Each rule
is a conjunction of named parts, so that a tool can say which part failed.

To compare two programs, an instruction is reduced to its *shape*: what it does,
without the words it uses. `read 3 to stream 2 going east`, `read 3 to
variable 7` and the kernel's `load` of the word at address 3 have one shape.

Terms to look up: *frame condition*.

Docs: Compiler 4 and 8 (`docs/`).
-/

namespace Tau

/-- What an instruction does, without the words it uses. -/
inductive Shape where
  /-- Memory: read the word at `addr`. -/
  | read (addr : Nat)
  /-- Memory: write the word at `addr`. -/
  | write (addr : Nat)
  /-- A one-word operation. -/
  | un (op : UnOp)
  /-- A two-word operation. -/
  | bin (op : BinOp)
  /-- Matrix: keep a vector operand. -/
  | load
  /-- Matrix: multiply by a word from a stream and accumulate. -/
  | mac (j : Nat)
  /-- Matrix: give the accumulator. -/
  | emit
  /-- A constant word. -/
  | const (xs : List Int)
  /-- A select. -/
  | sel
  /-- Matrix: replace the accumulator. -/
  | seed
  /-- Matrix: keep stored column `j`. -/
  | install (j : Nat)
  /-- Matrix: multiply by stored column `j` and accumulate. -/
  | macw (j : Nat)
  deriving DecidableEq, Repr

/-- The shape of a placed instruction. A pin is not part of it. -/
def PInstr.shape : PInstr → Shape
  | .read _ addr => .read addr
  | .write _ addr => .write addr
  | .un _ op _ => .un op
  | .bin _ op _ _ => .bin op
  | .load _ => .load
  | .mac j _ => .mac j
  | .emit _ => .emit
  | .const _ xs => .const xs
  | .sel _ _ _ _ => .sel
  | .seed _ => .seed
  | .install j _ => .install j
  | .macw j => .macw j
  | .pin _ i => i.shape

/-- The shape of an instruction of the machine. -/
def Instr.shape : Instr → Shape
  | .read addr _ => .read addr
  | .write _ addr => .write addr
  | .un op _ _ => .un op
  | .bin op _ _ _ => .bin op
  | .load _ => .load
  | .mac j _ => .mac j
  | .emit _ => .emit
  | .const xs _ => .const xs
  | .sel _ _ _ _ => .sel
  | .seed _ => .seed
  | .install j _ => .install j
  | .macw j => .macw j

/-- Whether an instruction of this shape is an operation of a kernel: it
computes a new word. A matrix product counts once, by its `emit`. -/
def Shape.isOperation : Shape → Bool
  | .un _ | .bin _ | .const _ | .sel | .emit => true
  | _ => false

/-- Whether address `a` of the slice at `p` is a word of a buffer. -/
def MemMap.holds (map : MemMap) (p a : Nat) : Bool :=
  (MemMap.findFrom p a 0 map).isSome

/-! ## `tau-place` decides where -/

/-- The shape of the one instruction that issues the word of a kernel's
operation. `none` for a load and a store, which are not operations. -/
def Stmt.operation : Stmt → Option Shape
  | .un _ op _ => some (.un op)
  | .bin _ op _ _ => some (.bin op)
  | .matvec .. => some .emit
  | .affine .. => some .emit
  | .const _ xs => some (.const xs)
  | .sel .. => some .sel
  | .pin _ s => s.operation
  | _ => none

/-- The slice and address a kernel's store writes, by the memory map, on
iteration `i`. `none` for any other statement, and for a buffer the map does
not have. -/
def Stmt.stored (map : MemMap) (i : Nat) : Stmt → Option (Nat × Nat)
  | .store _ buf ix => map[buf]?.map fun pl => (pl.slice, pl.base + ix.eval i)
  | .pin _ s => s.stored map i
  | _ => none

/-- Every word of every memory is a word of a buffer: the placed program has
no scratch space, so no word waits. -/
def Placed.noScratch (pl : Placed) : Bool :=
  (List.range pl.memSizes.length).all fun p =>
    (List.range (pl.memSizes[p]?.getD 0)).all fun a => pl.map.holds p a

/-- The placed program has one instruction for each operation of the kernel,
and no other operation. -/
def sameOperations (k : Kernel) (pl : Placed) : Bool :=
  ((pl.instrs.map (·.2.shape)).filter Shape.isOperation).isPerm
    (k.unroll.filterMap Stmt.operation)

/-- The placed program has one write for each store of the kernel, to the
word the map gives it, and no other write. -/
def sameStores (k : Kernel) (pl : Placed) : Bool :=
  (pl.instrs.filterMap fun (p, i) =>
      match i.shape with
      | .write a => some (p, a)
      | _ => none).isPerm
    (k.unroll.filterMap (Stmt.stored pl.map 0))

/-- `tau-place`: whether the placed program `pl` differs from the kernel `k`
only in what the pass decides, the memory map and the slice of each
operation. -/
def placeOnly (k : Kernel) (pl : Placed) : Bool :=
  pl.noScratch && sameOperations k pl && sameStores k pl

/-! ## `tau-schedule` decides when -/

/-- Whether two machines are the same but for the number of their streams.
`tau-schedule` writes its output for a machine with a stream for every
word. -/
def Config.sameSlices (a b : Config) : Bool :=
  a.kinds == b.kinds && a.mxmWeights == b.mxmWeights && a.memDelay == b.memDelay &&
  a.vxmDelay == b.vxmDelay && a.sxmDelay == b.sxmDelay && a.mxmDelay == b.mxmDelay &&
  a.delays == b.delays

/-- Every instruction an entry issues, with repeats written out. -/
def TimedEntry.written (e : TimedEntry) : List Instr :=
  (List.range (e.repeats + 1)).map e.entry.itemAt

/-- The shapes of the instructions the slice at `p` is given, in a placed
program. -/
def Placed.shapesAt (pl : Placed) (p : Nat) : List Shape :=
  (pl.instrs.filter (·.1 == p)).map (·.2.shape)

/-- The shapes of the instructions the slice at `p` is given, in a compiled
program. -/
def Compiled.shapesAt (c : Compiled) (p : Nat) : List Shape :=
  (c.prog.entriesOf p).flatMap fun e => e.written.map Instr.shape

/-- Whether a shape is a read. -/
def Shape.isRead : Shape → Bool
  | .read _ => true
  | _ => false

/-- Whether an instruction of this shape at the slice at `p` uses a scratch
word: a word of memory that belongs to no buffer. -/
def Shape.usesScratch (map : MemMap) (p : Nat) : Shape → Bool
  | .read a | .write a => !map.holds p a
  | _ => false

/-- At the slice at `p` the compiled program has every instruction of the
placed program but its reads, once each, and beyond those only reads of
buffer words the placed program reads, and writes and reads of scratch
words. How often a word of a buffer is read is the schedule's to decide: once
for each instruction that uses it, or not at all if none does. -/
def sameWorkAt (pl : Placed) (c : Compiled) (p : Nat) : Bool :=
  let before := pl.shapesAt p
  let after := (c.shapesAt p).filter fun s => !s.usesScratch pl.map p
  (after.filter fun s => !s.isRead).isPerm (before.filter fun s => !s.isRead) &&
  (after.filter Shape.isRead).all (before.contains ·)

/-- `tau-schedule`: whether the compiled program `c` differs from the placed
program `pl` only in what the pass decides: the cycles, the streams, and
which words wait in which scratch words. -/
def scheduleOnly (pl : Placed) (c : Compiled) : Bool :=
  c.map == pl.map && c.cfg.sameSlices pl.cfg &&
  (List.range pl.cfg.kinds.length).all (sameWorkAt pl c)

/-! ## `tau-route` decides on which stream -/

/-- The streams an instruction names, in the order it names them. -/
def Instr.streams : Instr → List Stream
  | .read _ dst => [dst]
  | .write src _ => [src]
  | .un _ src dst => [src, dst]
  | .bin _ a b dst => [a, b, dst]
  | .load src => [src]
  | .mac _ src => [src]
  | .emit dst => [dst]
  | .const _ dst => [dst]
  | .sel m a b dst => [m, a, b, dst]
  | .seed src => [src]
  | .install _ src => [src]
  | .macw _ => []

/-- Whether two entries are the same but for the numbers of their streams:
the same slice, cycle and repeats, the same shape, and streams going the
same ways. -/
def TimedEntry.sameButStreams (e e' : TimedEntry) : Bool :=
  e.slice == e'.slice && e.time == e'.time && e.repeats == e'.repeats && e.gap == e'.gap &&
  e.stride == e'.stride && e.instr.shape == e'.instr.shape &&
  e.instr.streams.map (·.dir) == e'.instr.streams.map (·.dir)

/-- The second program has the entries of the first, in the same order, with
other numbers for the streams. -/
def sameEntries (c c' : Compiled) : Bool :=
  c.prog.length == c'.prog.length &&
  (c.prog.zip c'.prog).all fun (e, e') => e.sameButStreams e'

/-- Each stream of the first program has one stream of the second in its
place, wherever it is named. Two streams of the first may share one of the
second. -/
def oneRenaming (c c' : Compiled) : Bool :=
  let pairs := (c.prog.zip c'.prog).flatMap fun (e, e') => e.instr.streams.zip e'.instr.streams
  pairs.all fun (s, s') => pairs.all fun (t, t') => s != t || s' == t'

/-- `tau-route`: whether the compiled program `c'` differs from the compiled
program `c` only in what the pass decides, the number of each stream. -/
def routeOnly (c c' : Compiled) : Bool :=
  c'.map == c.map && c'.memSizes == c.memSizes && c'.cycles == c.cycles &&
  c'.cfg.sameSlices c.cfg && sameEntries c c' && oneRenaming c c'

end Tau
