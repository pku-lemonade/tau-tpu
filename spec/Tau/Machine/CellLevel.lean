import Tau.Machine.SliceLevel
import Tau.Blocks.Repeater
import Tau.Blocks.Memory
import Tau.Blocks.ShiftRegister
import Tau.Blocks.Mac

/-!
# The cell-level machine

This is tau-tpu with each slice opened up. Where the slice-level machine
(`Tau.Machine.SliceLevel`) treats a slice as one box, here a slice is
built from the blocks in `spec/Tau/Blocks/`:

* a **repeater** that issues the slice's instructions, counting down to each
  one with its own registers,
* two **memories** that hold its words, one for each bank; a memory takes one
  command in a cycle, which is why a read and a write on one cycle have to be
  for different banks,
* a **shift register** that carries each result for its delay: as deep as
  the longest delay of the machine, with a shorter result written into the
  slot that leaves after its delay,
* for the matrix slice, a square of **multiply-accumulate cells**: one row
  of them for each lane of the result, and in each row one cell for each
  lane of the word that is multiplied. A cell holds one lane of an installed
  word, and a row adds up its products from cell to cell.

There is no clock shared by the whole machine. Every slice counts for itself, in
the registers of its repeater, and the slices agree only because they all
start together and all advance on every cycle. (Each slice also keeps a cycle
count, used only to report where a trap happened.)

This machine works on real words only. The streams between slices are the
same as at the slice level.

`Tau.Proofs.Machine.CellLevel` proves that this machine and the
slice-level machine cannot be told apart: on every program they trap on the
same cycle for the same reason, or end with the same memory contents.

Docs: Machine 3.11 and 4 (`docs/`).
-/

namespace Tau

variable {lanes : Nat}

/-- The state of one slice, as the states of its blocks. -/
structure Cell (lanes : Nat) where
  /-- The cycle count, used to report traps. -/
  clock : Nat
  /-- Repeater: the registers of every instruction entry. -/
  slots : List (Slot Instr)
  /-- Memory: the number of words. -/
  size : Nat
  /-- Memory: the number of words the lower bank can hold. -/
  bank : Nat
  /-- Memory: the words of the lower bank, from address 0. -/
  lower : Vector (Word lanes) (min bank size)
  /-- Memory: the words of the upper bank, from address `bank`. -/
  upper : Vector (Word lanes) (size - bank)
  /-- Shift register: its depth, which is the longest delay of the machine. -/
  depth : Nat
  /-- Shift register: results on their way out. The last slot leaves in the
  cycle about to run. -/
  pipe : Vector (Option (Stream × Value lanes)) depth
  /-- Matrix slice: the number of installed words. -/
  wsize : Nat
  /-- Matrix slice: the installed words. Lane `j` of word `i` is held by cell
  `j` of row `i`. -/
  weights : Vector (Word lanes) wsize

/-- One row of multiply-accumulate cells: cell `j` holds lane `j` of `w` and
is given lane `j` of `x`, both read as signed integers. The first cell
starts from zero, and each adds its product to the total of 32 bits that the
cell before it hands on. The result is the total after the last cell. -/
def macRow (w x : Word lanes) : Elem :=
  (List.finRange lanes).foldl
    (fun acc j => ((mac (0 : Elem)).step acc (.add (w[j].signExtend 32, x[j].signExtend 32))).1) 0

/-- Put the words `vs` into the installed words from place `j` on. -/
def putRows {n : Nat} : Vector (Word lanes) n → Nat → List (Word lanes) → Vector (Word lanes) n
  | ws, _, [] => ws
  | ws, j, v :: vs => putRows (ws.setIfInBounds j v) (j + 1) vs

/-- Step the memory of the bank that holds address `a`. The command is given
as a function of the address within the bank. Returns the two banks and the
output of the memory that was stepped. -/
def Cell.stepBank (c : Cell lanes) (a : Nat) (cmd : Nat → MemIn (Word lanes)) :
    Vector (Word lanes) (min c.bank c.size) × Vector (Word lanes) (c.size - c.bank) ×
      Option (Word lanes) :=
  if a < c.bank then
    let r := (memory _ c.lower).step c.lower (cmd a)
    (r.1, c.upper, r.2)
  else
    let r := (memory _ c.upper).step c.upper (cmd (a - c.bank))
    (c.lower, r.1, r.2)

/-- Carry out one instruction at one slice, by stepping its blocks. -/
def cellExec (cfg : Config) (kind : Kind) (rd : Stream → Option (Word lanes))
    (c : Cell lanes) : Instr → Except TrapKind (Cell lanes × Option (Stream × Value lanes))
  | .read addr dst =>
    if kind ≠ .mem then .error .wrongSlice
    else if cfg.streams ≤ dst.id then .error .badStream
    else
      match (c.stepBank addr .read).2.2 with
      | none => .error .badAddress
      | some v => .ok (c, some (dst, [v]))
  | .write src addr =>
    if kind ≠ .mem then .error .wrongSlice
    else if c.size ≤ addr then .error .badAddress
    else
      match rd src with
      | none => .error .emptyRead
      | some v =>
        .ok ({ c with
          lower := (c.stepBank addr (.write · v)).1
          upper := (c.stepBank addr (.write · v)).2.1 }, none)
  | .un ty op src dst =>
    if op.kind ≠ kind then .error .wrongSlice
    else if !cfg.hasGroup dst (op.out ty).bytes || !src.aligned ty.bytes then .error .badStream
    else
      match readGroup rd src ty.bytes with
      | none => .error .emptyRead
      | some v => .ok (c, some (dst, (wordSem lanes).un ty op v))
  | .bin ty op a b dst =>
    if kind ≠ .vxm then .error .wrongSlice
    else if !cfg.hasGroup dst ty.bytes || !a.aligned ty.bytes || !b.aligned ty.bytes then
      .error .badStream
    else
      match readGroup rd a ty.bytes, readGroup rd b ty.bytes with
      | some va, some vb => .ok (c, some (dst, (wordSem lanes).bin ty op va vb))
      | _, _ => .error .emptyRead
  | .const ty xs dst =>
    if kind ≠ .vxm then .error .wrongSlice
    else if !cfg.hasGroup dst ty.bytes then .error .badStream
    else .ok (c, some (dst, (wordSem lanes).const ty xs))
  | .sel ty m a b dst =>
    if kind ≠ .vxm then .error .wrongSlice
    else if !cfg.hasGroup dst ty.bytes || !m.aligned ty.bytes || !a.aligned ty.bytes ||
        !b.aligned ty.bytes then
      .error .badStream
    else
      match readGroup rd m ty.bytes, readGroup rd a ty.bytes, readGroup rd b ty.bytes with
      | some vm, some va, some vb => .ok (c, some (dst, (wordSem lanes).sel ty vm va vb))
      | _, _, _ => .error .emptyRead
  | .install j g src =>
    if kind ≠ .mxm then .error .wrongSlice
    else if c.wsize < j + g then .error .badAddress
    else
      match readGroup rd src g with
      | none => .error .emptyRead
      | some vs => .ok ({ c with weights := putRows c.weights j vs }, none)
  | .product n src dst =>
    if kind ≠ .mxm then .error .wrongSlice
    else if !cfg.hasGroup dst DType.i32.bytes then .error .badStream
    else if c.wsize < n then .error .badAddress
    else
      match rd src with
      | none => .error .emptyRead
      | some x =>
        -- Row `i` gives element `i` of the result, a value of 32 bits. Only
        -- the first `n` rows are used.
        .ok (c, some (dst, Value.ofElems DType.i32.bytes fun i : Fin lanes =>
          match c.weights[i.val]? with
          | some w => if i.val < n then macRow w x else 0
          | none => 0))

/-- Whether a result that leaves `d` cycles from now finds its slot of the
shift register taken by an earlier result. The last slot leaves in this
cycle. A result that enters at the front never clashes. -/
def cellClash (c : Cell lanes) (entering : Option (Stream × Value lanes)) (d : Nat) : Bool :=
  match entering with
  | some _ => d < c.depth && (c.pipe[c.depth - 1 - d]?.getD none).isSome
  | none => false

/-- Put a result that leaves `d` cycles from now into a slice's shift register,
step it, and take out the one that leaves it. A result whose delay is the
depth of the register is its input. A result with a shorter delay is written
into the slot that leaves after its delay, and the register steps with no
input. -/
def cellShift (c : Cell lanes) (entering : Option (Stream × Value lanes)) (d : Nat) :
    Cell lanes × Option (Stream × Value lanes) :=
  let out :=
    match entering with
    | some r =>
      if d < c.depth then
        (shiftRegister c.depth none).step (c.pipe.setIfInBounds (c.depth - 1 - d) (some r)) none
      else (shiftRegister c.depth none).step c.pipe (some r)
    | none => (shiftRegister c.depth none).step c.pipe none
  ({ c with pipe := out.1 }, out.2)

/-- Carry out a read and then a write at one slice. The result is the word
read. -/
def cellExecBoth (cfg : Config) (kind : Kind) (rd : Stream → Option (Word lanes))
    (c : Cell lanes) (r w : Instr) :
    Except TrapKind (Cell lanes × Option (Stream × Value lanes)) :=
  match cellExec cfg kind rd c r with
  | .error k => .error k
  | .ok (c', res) =>
    match cellExec cfg kind rd c' w with
    | .error k => .error k
    | .ok (c'', _) => .ok (c'', res)

/-- The end of a slice's cycle, given what its instructions did: a trap is
reported with the slice and the cycle, and a result enters the shift register
to leave `d` cycles from now, unless its slot is taken. -/
def cellLeave (p t : Nat) (d : Nat) :
    Except TrapKind (Cell lanes × Option (Stream × Value lanes)) →
      Except Trap (Cell lanes × Option (Stream × Value lanes))
  | .error k => .error ⟨k, p, t⟩
  | .ok (c, r) =>
    if cellClash c r d then .error ⟨.twoResults, p, t⟩ else .ok (cellShift c r d)

/-- One cycle of the slice at position `p`. The repeater issues the
instructions due and advances its registers. Each bank of the memory is one
memory block and takes one command, so a read and a write are both carried
out only if they are for different banks. -/
def cellStep (cfg : Config) (prog : Program) (rd : Stream → Option (Word lanes)) (p : Nat)
    (c : Cell lanes) : Except Trap (Cell lanes × Option (Stream × Value lanes)) :=
  let issued := (repeater (prog.entriesFor p)).step c.slots ()
  let carried : Except Trap (Cell lanes × Option (Stream × Value lanes)) :=
    match issued.2 with
    | [] => .ok (cellShift c none 0)
    | [i] =>
      match cfg.kindAt p with
      | none => .error ⟨.noSlice, p, c.clock⟩
      | some kind => cellLeave p c.clock (cfg.delayOf kind i) (cellExec cfg kind rd c i)
    | [i, j] =>
      match Instr.readWrite i j, cfg.kindAt p with
      | none, _ => .error ⟨.twoInstructions, p, c.clock⟩
      | some _, none => .error ⟨.noSlice, p, c.clock⟩
      | some (r, w), some kind =>
        if cfg.bank r.addr = cfg.bank w.addr then .error ⟨.sameBank, p, c.clock⟩
        else cellLeave p c.clock (cfg.delayOf kind r) (cellExecBoth cfg kind rd c r w)
    | _ => .error ⟨.twoInstructions, p, c.clock⟩
  carried.map fun r => ({ r.1 with clock := c.clock + 1, slots := issued.1 }, r.2)

/-- The state of the whole machine: the streams and the slices. -/
structure CellState (lanes : Nat) where
  /-- `east[id][p]` is what stream `id` going east holds at position `p`. -/
  east : List (List (Option (Word lanes)))
  /-- `west[id][p]` is what stream `id` going west holds at position `p`. -/
  west : List (List (Option (Word lanes)))
  /-- The state of the slice at each position. -/
  cells : List (Cell lanes)

/-- What stream `tr` holds at position `p`. -/
def CellState.sample (s : CellState lanes) (p : Nat) (tr : Stream) : Option (Word lanes) :=
  match (match tr.dir with | .east => s.east | .west => s.west)[tr.id]? with
  | some row => row[p]?.getD none
  | none => none

/-- One cycle of every slice, starting from position `p`. -/
def cellSteps (cfg : Config) (prog : Program) (s : CellState lanes) :
    Nat → List (Cell lanes) → Except Trap (List (Cell lanes × Option (Stream × Value lanes)))
  | _, [] => .ok []
  | p, c :: rest =>
    match cellStep cfg prog (s.sample p) p c with
    | .error e => .error e
    | .ok r =>
      match cellSteps cfg prog s (p + 1) rest with
      | .error e => .error e
      | .ok rs => .ok (r :: rs)

/-- One cycle of the machine. -/
def CellState.step (cfg : Config) (prog : Program) (s : CellState lanes) :
    Except Trap (CellState lanes) :=
  match cellSteps cfg prog s 0 s.cells with
  | .error e => .error e
  | .ok rs =>
    .ok {
      east := advance (rs.map (·.2)) .east 0 s.east
      west := advance (rs.map (·.2)) .west 0 s.west
      cells := rs.map (·.1) }

/-- `n` cycles of the machine. -/
def CellState.run (cfg : Config) (prog : Program) :
    Nat → CellState lanes → Except Trap (CellState lanes)
  | 0, s => .ok s
  | n + 1, s =>
    match s.step cfg prog with
    | .error e => .error e
    | .ok s' => CellState.run cfg prog n s'

/-- The state at cycle 0, for the given program and starting memory contents.
Each slice's repeater is loaded with that slice's entries. -/
def CellState.init (cfg : Config) (prog : Program) (image : List (List (Word lanes))) :
    CellState lanes where
  east := List.replicate cfg.streams (List.replicate cfg.kinds.length none)
  west := List.replicate cfg.streams (List.replicate cfg.kinds.length none)
  cells := (List.range cfg.kinds.length).map fun p =>
    { clock := 0
      slots := (prog.entriesFor p).map Entry.start
      size := (image[p]?.getD []).length
      bank := cfg.bankSize
      lower := ⟨((image[p]?.getD []).take cfg.bankSize).toArray, by simp⟩
      upper := ⟨((image[p]?.getD []).drop cfg.bankSize).toArray, by simp⟩
      depth := cfg.maxDelay
      pipe := Vector.replicate _ none
      wsize := cfg.lanes
      weights := Vector.replicate _ Word.zero }

/-- The contents of every slice's memory. -/
def CellState.memory (s : CellState lanes) : List (List (Word lanes)) :=
  s.cells.map fun c => c.lower.toList ++ c.upper.toList

/-- Run a program for `n` cycles from a memory image and return the final
memory contents. -/
def cellExecute (cfg : Config) (prog : Program) (n : Nat) (image : List (List (Word lanes))) :
    Except Trap (List (List (Word lanes))) :=
  match prog.find? fun e => cfg.kinds.length ≤ e.slice with
  | some e => .error ⟨.noSlice, e.slice, e.time⟩
  | none =>
    match CellState.run cfg prog n (CellState.init cfg prog image) with
    | .error e => .error e
    | .ok s => .ok s.memory

end Tau
