import Tau.Isa.Instr

/-!
# The slice-level machine

This is tau-tpu with each slice treated as one box: an instruction goes in at
one cycle and its result comes out a fixed number of cycles later, the delay
of the instruction. What happens inside the box is the subject of
`Tau.Machine.CellLevel`.

One cycle of the machine (`step`) does three things.

1. Each slice looks up the instruction due this cycle, reads its operands from
   the stream slots at its own position, and computes a result.
2. The result enters the slice's pipe, at the slot from which it leaves
   after its delay, and the result whose delay is up comes out. If that slot
   already holds a result, the two would leave on one cycle, and the machine
   traps.
3. Every stream moves one position, and the results that came out are placed
   on their streams at the slice's position.

So a result computed at slice `p` on cycle `t` can be read at slice `q` on
cycle `t + delay + 1 + |q - p|`, and on no other cycle, where `delay` is the
delay of the instruction that computed it (`Config.delayOf`). A program that
reads a slot on the wrong cycle finds it empty, and the machine traps.

The machine is written for an arbitrary type `V` of values. See `Tau.Isa.Op`.

Docs: Machine 3.3, 3.5 and 3.7 (`docs/`).
-/

namespace Tau

/-- Why the machine stopped. -/
inductive TrapKind where
  /-- An instruction read a stream slot that held nothing. -/
  | emptyRead
  /-- An instruction named a stream that does not exist. -/
  | badStream
  /-- A memory address was out of range. -/
  | badAddress
  /-- An instruction was sent to a slice of the wrong kind. -/
  | wrongSlice
  /-- Two instructions were due at one slice on one cycle. -/
  | twoInstructions
  /-- An instruction's result would leave its slice on the same cycle as an
  earlier result. -/
  | twoResults
  /-- A matrix slice was told to multiply before it was given a vector. -/
  | noOperand
  /-- The program names a slice that does not exist. -/
  | noSlice
  deriving DecidableEq, Repr

/-- A trap: what went wrong, at which slice, on which cycle. -/
structure Trap where
  /-- What went wrong. -/
  kind : TrapKind
  /-- The position of the slice where it happened. -/
  slice : Nat
  /-- The cycle on which it happened. -/
  time : Nat
  deriving DecidableEq, Repr

variable {V : Type}

/-- The state of one slice. A slice uses only the parts that fit its kind. -/
structure Slice (V : Type) where
  /-- Memory slices: the stored words. -/
  words : List V
  /-- Matrix slices: the vector operand. -/
  x : Option V
  /-- Matrix slices: the accumulator. -/
  acc : V
  /-- Matrix slices: the stored columns. -/
  weights : List V
  /-- Results on their way out. The last leaves in the cycle about to run,
  the one before it a cycle later, and so on. -/
  pipe : List (Option (Stream × V))

/-- The state of the whole machine at the start of a cycle. -/
structure State (V : Type) where
  /-- The number of the cycle about to run. -/
  time : Nat
  /-- `east[id][p]` is what stream `id` going east holds at position `p`. -/
  east : List (List (Option V))
  /-- `west[id][p]` is what stream `id` going west holds at position `p`. -/
  west : List (List (Option V))
  /-- The state of the slice at each position. -/
  slices : List (Slice V)

/-- The streams going in direction `d`. -/
def State.belt (s : State V) : Dir → List (List (Option V))
  | .east => s.east
  | .west => s.west

/-- What stream `tr` holds at position `p`. -/
def State.sample (s : State V) (p : Nat) (tr : Stream) : Option V :=
  match (s.belt tr.dir)[tr.id]? with
  | some row => row[p]?.getD none
  | none => none

/-- Carry out one instruction at one slice. Returns the new state of the slice
and the result, if any, with the stream it is meant for. -/
def exec (S : Sem V) (cfg : Config) (kind : Kind) (rd : Stream → Option V)
    (sl : Slice V) : Instr → Except TrapKind (Slice V × Option (Stream × V))
  | .read addr dst =>
    if kind ≠ .mem then .error .wrongSlice
    else if cfg.streams ≤ dst.id then .error .badStream
    else
      match sl.words[addr]? with
      | none => .error .badAddress
      | some v => .ok (sl, some (dst, v))
  | .write src addr =>
    if kind ≠ .mem then .error .wrongSlice
    else if sl.words.length ≤ addr then .error .badAddress
    else
      match rd src with
      | none => .error .emptyRead
      | some v => .ok ({ sl with words := sl.words.set addr v }, none)
  | .un op src dst =>
    if op.kind ≠ kind then .error .wrongSlice
    else if cfg.streams ≤ dst.id then .error .badStream
    else
      match rd src with
      | none => .error .emptyRead
      | some v => .ok (sl, some (dst, S.un op v))
  | .bin op a b dst =>
    if kind ≠ .vxm then .error .wrongSlice
    else if cfg.streams ≤ dst.id then .error .badStream
    else
      match rd a, rd b with
      | some va, some vb => .ok (sl, some (dst, S.bin op va vb))
      | _, _ => .error .emptyRead
  | .load src =>
    if kind ≠ .mxm then .error .wrongSlice
    else
      match rd src with
      | none => .error .emptyRead
      | some v => .ok ({ sl with x := some v }, none)
  | .mac j src =>
    if kind ≠ .mxm then .error .wrongSlice
    else
      match sl.x, rd src with
      | none, _ => .error .noOperand
      | some _, none => .error .emptyRead
      | some x, some w => .ok ({ sl with acc := S.mac j sl.acc x w }, none)
  | .emit dst =>
    if kind ≠ .mxm then .error .wrongSlice
    else if cfg.streams ≤ dst.id then .error .badStream
    else .ok ({ sl with acc := S.zero }, some (dst, sl.acc))
  | .const xs dst =>
    if kind ≠ .vxm then .error .wrongSlice
    else if cfg.streams ≤ dst.id then .error .badStream
    else .ok (sl, some (dst, S.const xs))
  | .sel m a b dst =>
    if kind ≠ .vxm then .error .wrongSlice
    else if cfg.streams ≤ dst.id then .error .badStream
    else
      match rd m, rd a, rd b with
      | some vm, some va, some vb => .ok (sl, some (dst, S.sel vm va vb))
      | _, _, _ => .error .emptyRead
  | .seed src =>
    if kind ≠ .mxm then .error .wrongSlice
    else
      match rd src with
      | none => .error .emptyRead
      | some v => .ok ({ sl with acc := v }, none)
  | .install j src =>
    if kind ≠ .mxm then .error .wrongSlice
    else if sl.weights.length ≤ j then .error .badAddress
    else
      match rd src with
      | none => .error .emptyRead
      | some v => .ok ({ sl with weights := sl.weights.set j v }, none)
  | .macw j =>
    if kind ≠ .mxm then .error .wrongSlice
    else
      match sl.x, sl.weights[j]? with
      | none, _ => .error .noOperand
      | some _, none => .error .badAddress
      | some x, some w => .ok ({ sl with acc := S.mac j sl.acc x w }, none)

/-- The slots of a slice's pipe in the cycle a result enters it: a free slot
in front, then the pipe. The last slot leaves this cycle, the one before it
on the next cycle, and so on; the result is written into the slot that
leaves `d` cycles from now. -/
def Slice.slots (sl : Slice V) (entering : Option (Stream × V)) (d : Nat) :
    List (Option (Stream × V)) :=
  match entering with
  | none => none :: sl.pipe
  | some r => (none :: sl.pipe).set (sl.pipe.length - d) (some r)

/-- Whether a result that leaves `d` cycles from now finds its slot taken by
an earlier result, which would then leave on the same cycle. -/
def Slice.clash (sl : Slice V) (entering : Option (Stream × V)) (d : Nat) : Bool :=
  entering.isSome && ((none :: sl.pipe)[sl.pipe.length - d]?.getD none).isSome

/-- Put a result that leaves `d` cycles from now into a slice's pipe, and take
out the result that leaves this cycle. -/
def shiftPipe (sl : Slice V) (entering : Option (Stream × V)) (d : Nat) :
    Slice V × Option (Stream × V) :=
  ({ sl with pipe := (sl.slots entering d).dropLast },
   (sl.slots entering d).getLast?.getD none)

/-- One cycle of the slice at position `p`. -/
def stepSlice (S : Sem V) (cfg : Config) (prog : Program) (s : State V) (p : Nat)
    (sl : Slice V) : Except Trap (Slice V × Option (Stream × V)) :=
  match prog.dueAt p s.time with
  | [] => .ok (shiftPipe sl none 0)
  | [i] =>
    match cfg.kindAt p with
    | none => .error ⟨.noSlice, p, s.time⟩
    | some kind =>
      match exec S cfg kind (s.sample p) sl i with
      | .ok (sl', r) =>
        if sl'.clash r (cfg.delayOf kind i) then .error ⟨.twoResults, p, s.time⟩
        else .ok (shiftPipe sl' r (cfg.delayOf kind i))
      | .error k => .error ⟨k, p, s.time⟩
  | _ => .error ⟨.twoInstructions, p, s.time⟩

/-- One cycle of every slice, starting from position `p`. -/
def stepSlices (S : Sem V) (cfg : Config) (prog : Program) (s : State V) :
    Nat → List (Slice V) → Except Trap (List (Slice V × Option (Stream × V)))
  | _, [] => .ok []
  | p, sl :: rest =>
    match stepSlice S cfg prog s p sl with
    | .error e => .error e
    | .ok r =>
      match stepSlices S cfg prog s (p + 1) rest with
      | .error e => .error e
      | .ok rs => .ok (r :: rs)

/-- The value, if any, that the slice at position `p` places on stream
`(d, id)` this cycle. `outs[p]` is what came out of the slice at `p`. -/
def inject (outs : List (Option (Stream × V))) (d : Dir) (id p : Nat) : Option V :=
  match outs[p]?.getD none with
  | some (tr, v) => if tr.dir = d ∧ tr.id = id then some v else none
  | none => none

/-- One stream after one cycle: every word moves one position in direction `d`,
and a newly placed result replaces whatever arrives at its position. -/
def advanceRow (outs : List (Option (Stream × V))) (d : Dir) (id : Nat)
    (row : List (Option V)) : List (Option V) :=
  (List.range row.length).map fun p =>
    match inject outs d id p with
    | some v => some v
    | none =>
      match d with
      | .east => if p = 0 then none else row[p - 1]?.getD none
      | .west => row[p + 1]?.getD none

/-- All streams in direction `d` after one cycle, starting from stream `id`. -/
def advance (outs : List (Option (Stream × V))) (d : Dir) :
    Nat → List (List (Option V)) → List (List (Option V))
  | _, [] => []
  | id, row :: rest => advanceRow outs d id row :: advance outs d (id + 1) rest

/-- One cycle of the machine. -/
def step (S : Sem V) (cfg : Config) (prog : Program) (s : State V) :
    Except Trap (State V) :=
  match stepSlices S cfg prog s 0 s.slices with
  | .error e => .error e
  | .ok rs =>
    .ok {
      time := s.time + 1
      east := advance (rs.map (·.2)) .east 0 s.east
      west := advance (rs.map (·.2)) .west 0 s.west
      slices := rs.map (·.1) }

/-- `n` cycles of the machine. -/
def run (S : Sem V) (cfg : Config) (prog : Program) : Nat → State V → Except Trap (State V)
  | 0, s => .ok s
  | n + 1, s =>
    match step S cfg prog s with
    | .error e => .error e
    | .ok s' => run S cfg prog n s'

/-- The state at cycle 0. `image[p]` is the starting contents of the slice at
position `p`; it should be empty unless that slice is a memory. -/
def State.init (S : Sem V) (cfg : Config) (image : List (List V)) : State V where
  time := 0
  east := List.replicate cfg.streams (List.replicate cfg.kinds.length none)
  west := List.replicate cfg.streams (List.replicate cfg.kinds.length none)
  slices := (List.range cfg.kinds.length).map fun p =>
    { words := image[p]?.getD []
      x := none
      acc := S.zero
      weights := List.replicate cfg.mxmWeights S.zero
      pipe := List.replicate cfg.maxDelay none }

/-- The contents of every slice's memory. -/
def State.memory (s : State V) : List (List V) := s.slices.map (·.words)

/-- Run a program for `n` cycles from a memory image and return the final
memory contents. -/
def execute (S : Sem V) (cfg : Config) (prog : Program) (n : Nat)
    (image : List (List V)) : Except Trap (List (List V)) :=
  -- An instruction for a slice the machine does not have is a trap before the
  -- first cycle.
  match prog.find? fun e => cfg.kinds.length ≤ e.slice with
  | some e => .error ⟨.noSlice, e.slice, e.time⟩
  | none =>
    match run S cfg prog n (State.init S cfg image) with
    | .error e => .error e
    | .ok s => .ok s.memory

end Tau
