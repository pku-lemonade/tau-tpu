import Tau.SliceLevel.Machine
import Tau.Blocks.Repeater
import Tau.Blocks.Memory
import Tau.Blocks.ShiftRegister
import Tau.Blocks.Mac

/-!
# The cell-level machine

This is tau-tpu with each slice opened up. Where the slice-level machine
(`Tau/SliceLevel/Machine.lean`) treats a slice as one box, here a slice is
built from the blocks in `Tau/Blocks/`:

* a **repeater** that issues the slice's instructions, counting down to each
  one with its own registers,
* a **memory** that holds its words,
* a **shift register** that carries each result for the slice's delay,
* one **multiply-accumulate cell** per lane, for the matrix slice,
* a second small **memory** for the columns a matrix slice stores.

There is no clock shared by the whole chip. Every slice counts for itself, in
the registers of its repeater, and the slices agree only because they all
start together and all advance on every cycle. (Each slice also keeps a cycle
count, used only to report where a trap happened.)

This machine works on real words only. The streams between slices are the
same as at the slice level.

`Tau/Proofs/CellLevel/Refine.lean` proves that this machine and the
slice-level machine cannot be told apart: on every program they trap on the
same cycle for the same reason, or end with the same memory contents.
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
  /-- Memory: the stored words. -/
  mem : Vector (Word lanes) size
  /-- Shift register: its depth, which is the slice's delay. -/
  depth : Nat
  /-- Shift register: results on their way out. -/
  pipe : Vector (Option (Track × Word lanes)) depth
  /-- Matrix slice: the vector operand. -/
  x : Option (Word lanes)
  /-- Matrix slice: the total held by the multiply-accumulate cell of each lane. -/
  acc : Vector Lane lanes
  /-- Matrix slice: the number of columns it can store. -/
  wsize : Nat
  /-- Matrix slice: the stored columns, kept in a small memory. -/
  weights : Vector (Word lanes) wsize

/-- Step the multiply-accumulate cell of every lane. `cmd k` is what the cell
of lane `k` is told to do. -/
def macLanes (acc : Vector Lane lanes) (cmd : Fin lanes → AccIn (Lane × Lane)) :
    Vector Lane lanes :=
  Vector.ofFn fun k => ((mac (0 : Lane)).step acc[k] (cmd k)).1

/-- Carry out one instruction at one slice, by stepping its blocks. -/
def cellExec (cfg : Config) (kind : Kind) (rd : Track → Option (Word lanes))
    (c : Cell lanes) : Instr → Except TrapKind (Cell lanes × Option (Track × Word lanes))
  | .read addr dst =>
    if kind ≠ .mem then .error .wrongSlice
    else if cfg.streams ≤ dst.id then .error .badTrack
    else
      match ((memory c.size c.mem).step c.mem (.read addr)).2 with
      | none => .error .badAddress
      | some v => .ok (c, some (dst, v))
  | .write src addr =>
    if kind ≠ .mem then .error .wrongSlice
    else if c.size ≤ addr then .error .badAddress
    else
      match rd src with
      | none => .error .emptyRead
      | some v =>
        .ok ({ c with mem := ((memory c.size c.mem).step c.mem (.write addr v)).1 }, none)
  | .un op src dst =>
    if op.kind ≠ kind then .error .wrongSlice
    else if cfg.streams ≤ dst.id then .error .badTrack
    else
      match rd src with
      | none => .error .emptyRead
      | some v => .ok (c, some (dst, (wordSem lanes).un op v))
  | .bin op a b dst =>
    if kind ≠ .vxm then .error .wrongSlice
    else if cfg.streams ≤ dst.id then .error .badTrack
    else
      match rd a, rd b with
      | some va, some vb => .ok (c, some (dst, (wordSem lanes).bin op va vb))
      | _, _ => .error .emptyRead
  | .load src =>
    if kind ≠ .mxm then .error .wrongSlice
    else
      match rd src with
      | none => .error .emptyRead
      | some v => .ok ({ c with x := some v }, none)
  | .mac j src =>
    if kind ≠ .mxm then .error .wrongSlice
    else
      match c.x, rd src with
      | none, _ => .error .noOperand
      | some _, none => .error .emptyRead
      | some x, some w =>
        -- Lane `k` adds lane `j` of the vector operand times lane `k` of `w`.
        .ok ({ c with acc := macLanes c.acc fun k => .add (x[j]?.getD 0, w[k]) }, none)
  | .emit dst =>
    if kind ≠ .mxm then .error .wrongSlice
    else if cfg.streams ≤ dst.id then .error .badTrack
    else .ok ({ c with acc := macLanes c.acc fun _ => .clear }, some (dst, c.acc))
  | .const xs dst =>
    if kind ≠ .vxm then .error .wrongSlice
    else if cfg.streams ≤ dst.id then .error .badTrack
    else .ok (c, some (dst, (wordSem lanes).const xs))
  | .sel m a b dst =>
    if kind ≠ .vxm then .error .wrongSlice
    else if cfg.streams ≤ dst.id then .error .badTrack
    else
      match rd m, rd a, rd b with
      | some vm, some va, some vb => .ok (c, some (dst, (wordSem lanes).sel vm va vb))
      | _, _, _ => .error .emptyRead
  | .seed src =>
    if kind ≠ .mxm then .error .wrongSlice
    else
      match rd src with
      | none => .error .emptyRead
      -- Lane `k` loads lane `k` of the word.
      | some v => .ok ({ c with acc := macLanes c.acc fun k => .load (v[k], 1) }, none)
  | .install j src =>
    if kind ≠ .mxm then .error .wrongSlice
    else if c.wsize ≤ j then .error .badAddress
    else
      match rd src with
      | none => .error .emptyRead
      | some v =>
        .ok ({ c with
          weights := ((memory c.wsize c.weights).step c.weights (.write j v)).1 }, none)
  | .macw j =>
    if kind ≠ .mxm then .error .wrongSlice
    else
      match c.x, ((memory c.wsize c.weights).step c.weights (.read j)).2 with
      | none, _ => .error .noOperand
      | some _, none => .error .badAddress
      | some x, some w =>
        .ok ({ c with acc := macLanes c.acc fun k => .add (x[j]?.getD 0, w[k]) }, none)

/-- Push a result into a slice's shift register and take out the one that
leaves it. -/
def cellShift (c : Cell lanes) (entering : Option (Track × Word lanes)) :
    Cell lanes × Option (Track × Word lanes) :=
  let r := (shiftRegister c.depth none).step c.pipe entering
  ({ c with pipe := r.1 }, r.2)

/-- One cycle of the slice at position `p`. The repeater issues the
instructions due and advances its registers. -/
def cellStep (cfg : Config) (prog : Program) (rd : Track → Option (Word lanes)) (p : Nat)
    (c : Cell lanes) : Except Trap (Cell lanes × Option (Track × Word lanes)) :=
  let issued := (repeater (prog.entriesFor p)).step c.slots ()
  let tick (r : Cell lanes × Option (Track × Word lanes)) :
      Cell lanes × Option (Track × Word lanes) :=
    ({ r.1 with clock := c.clock + 1, slots := issued.1 }, r.2)
  match issued.2 with
  | [] => .ok (tick (cellShift c none))
  | [i] =>
    match cfg.kindAt p with
    | none => .error ⟨.noSlice, p, c.clock⟩
    | some kind =>
      match cellExec cfg kind rd c i with
      | .ok (c', r) => .ok (tick (cellShift c' r))
      | .error k => .error ⟨k, p, c.clock⟩
  | _ => .error ⟨.twoInstructions, p, c.clock⟩

/-- The state of the whole machine: the streams and the slices. -/
structure CellState (lanes : Nat) where
  /-- `east[id][p]` is what stream `id` going east holds at position `p`. -/
  east : List (List (Option (Word lanes)))
  /-- `west[id][p]` is what stream `id` going west holds at position `p`. -/
  west : List (List (Option (Word lanes)))
  /-- The state of the slice at each position. -/
  cells : List (Cell lanes)

/-- What stream `tr` holds at position `p`. -/
def CellState.sample (s : CellState lanes) (p : Nat) (tr : Track) : Option (Word lanes) :=
  match (match tr.dir with | .east => s.east | .west => s.west)[tr.id]? with
  | some row => row[p]?.getD none
  | none => none

/-- One cycle of every slice, starting from position `p`. -/
def cellSteps (cfg : Config) (prog : Program) (s : CellState lanes) :
    Nat → List (Cell lanes) → Except Trap (List (Cell lanes × Option (Track × Word lanes)))
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
      mem := ⟨(image[p]?.getD []).toArray, by simp⟩
      depth := cfg.delay ((cfg.kinds[p]?).getD .vxm)
      pipe := Vector.replicate _ none
      x := none
      acc := Vector.replicate lanes 0
      wsize := cfg.mxmWeights
      weights := Vector.replicate _ Word.zero }

/-- The contents of every slice's memory. -/
def CellState.memory (s : CellState lanes) : List (List (Word lanes)) :=
  s.cells.map fun c => c.mem.toList

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
