import Tau.Tools.Json
import Tau.IR.Unroll

/-!
# Running programs on real words

The functions the command-line tools call. `runStage` runs the output of any
compiler stage and `timelineOf` gives its events. `checkPair` picks the check
for two stage files, and `explainPair` says why it rejected.
-/

namespace Tau.Tools

def showStream (tr : Stream) : String :=
  (match tr.dir with | .east => "east" | .west => "west") ++ s!" stream {tr.id}"

def showTrap (t : Trap) : String :=
  let what := match t.kind with
    | .emptyRead => "read a stream slot that held nothing"
    | .badStream => "named a stream that does not exist"
    | .badAddress => "used a memory address that is out of range"
    | .wrongSlice => "was sent to a slice of the wrong kind"
    | .twoInstructions => "had more instructions due on one cycle than it can run"
    | .sameBank => "had a read and a write of the same bank due on one cycle"
    | .twoResults => "had two results due to leave on the same cycle"
    | .noSlice => "does not exist"
  s!"trap at cycle {t.time}: slice {t.slice} {what}"

/-- The buffers as words: each value is as many words as its type has
bytes, the low byte of every element first. -/
def toWords (lanes : Nat) (bufs : List Json.Buffer) : List (List (Word lanes)) :=
  bufs.map fun (ty, values) => values.flatMap (Value.ofInts ty)

/-- The values of type `ty` that a row of words holds. -/
def toValues {lanes : Nat} (ty : DType) : Nat → List (Word lanes) → List (List Int)
  | 0, _ => []
  | _, [] => []
  | fuel + 1, ws => Value.toInts (ws.take ty.bytes) :: toValues ty fuel (ws.drop ty.bytes)

/-- Words as buffers, each with the type the buffer had in `inputs`. A buffer
that is not among them is shown as values of 8 bits. -/
def ofWords {lanes : Nat} (inputs : List Json.Buffer) (words : List (List (Word lanes))) :
    List Json.Buffer :=
  words.zipIdx.map fun (ws, b) =>
    let shown := (inputs[b]?.map (·.1)).getD .i8
    (shown, toValues shown ws.length ws)

/-- Run a compiled program on the given buffer contents. -/
def simulate (c : Compiled) (lanes : Nat) (bufs : List (List (Word lanes))) :
    Except String (List (List (Word lanes))) :=
  match execute (wordSem lanes) c.cfg c.prog c.cycles (c.image bufs Word.zero) with
  | .error t => .error (showTrap t)
  | .ok mem => .ok (extract c.map mem Word.zero)

def kernelFailed : String :=
  "the kernel uses a variable with no value of the type it needs or a position outside a buffer"

def sourceFailed : String :=
  "the program uses a variable with no value of the type it needs or a position outside a buffer, or makes a call it may not make"

def placedFailed : String :=
  "an instruction is on the wrong kind of slice, uses a bad address, or uses a word that does not exist"

/-- Run a kernel directly on the given buffer contents. -/
def reference (k : Kernel) (lanes : Nat) (bufs : List (List (Word lanes))) :
    Except String (List (List (Word lanes))) :=
  match k.run (wordSem lanes) bufs with
  | none => .error kernelFailed
  | some out => .ok out

/-- Run a source program directly on the given buffer contents. -/
def referenceSource (s : Source) (lanes : Nat) (bufs : List (List (Word lanes))) :
    Except String (List (List (Word lanes))) :=
  match s.run (wordSem lanes) bufs with
  | none => .error sourceFailed
  | some out => .ok out

/-- Carry out a placed program on the given buffer contents. -/
def simulatePlaced (pl : Placed) (lanes : Nat) (bufs : List (List (Word lanes))) :
    Except String (List (List (Word lanes))) :=
  match pl.execute (wordSem lanes) (pl.image bufs Word.zero) with
  | none => .error placedFailed
  | some mem => .ok (extract pl.map mem Word.zero)

/-- What kind of file a stage is, for messages. -/
def stageName : Json.Stage → String
  | .source .. => "source program"
  | .kernel .. => "kernel"
  | .placed _ => "placed program"
  | .compiled _ => "compiled program"

/-- The sizes of the buffers of a stage, as its file declares them. -/
def stageSizes : Json.Stage → List Nat
  | .source sizes _ => sizes
  | .kernel sizes _ => sizes
  | .placed pl => pl.map.map (·.size)
  | .compiled c => c.map.map (·.size)

/-- The words of the buffers for a stage: the buffers given, and words of
zeros for any buffer the file leaves out. A program's scratch buffers come
after the buffers the user fills. -/
def padBuffers (st : Json.Stage) (lanes : Nat) (bufs : List Json.Buffer) :
    List (List (Word lanes)) :=
  toWords lanes bufs ++ ((stageSizes st).drop bufs.length).map fun n =>
    List.replicate n Word.zero

/-- Run the output of any compiler stage. -/
def runStage (st : Json.Stage) (lanes : Nat) (bufs : List Json.Buffer) :
    Except String (List Json.Buffer) :=
  let words := padBuffers st lanes bufs
  -- A machine runs words of at most its own number of lanes (Machine 1).
  let fits (cfg : Config) (run : Except String (List (List (Word lanes)))) :=
    if cfg.lanes < lanes then
      .error s!"the buffers have words of {lanes} lanes and the machine has {cfg.lanes}"
    else run
  let out := match st with
    | .source _ s => referenceSource s lanes words
    | .kernel _ k => reference k lanes words
    | .placed pl => fits pl.cfg (simulatePlaced pl lanes words)
    | .compiled c => fits c.cfg (simulate c lanes words)
  out.map (ofWords bufs)

/-- The events of any compiler stage on the given buffer contents, in order
of time: the pinned words of a source program, a kernel or a placed program,
and every word a compiled program issues. A word is shown as the signed
integers of its lanes. -/
def timelineOf (st : Json.Stage) (lanes : Nat) (bufs : List Json.Buffer) :
    List (Event (List Int)) :=
  let words := padBuffers st lanes bufs
  let events : List (Event (Word lanes)) := match st with
    | .source _ s => s.timeline (wordSem lanes) words
    | .kernel _ k => k.timeline (wordSem lanes) words
    | .placed pl => pl.timeline (wordSem lanes) words Word.zero
    | .compiled c => c.timeline (wordSem lanes) words Word.zero
  ((events.map (Event.map Word.toInts)).toArray.qsort fun a b =>
    a.time < b.time || (a.time == b.time && a.store.isNone && b.store.isSome)).toList

/-- The first word on which two results differ: buffer and position. -/
def firstDiff (a b : List (List Expr)) : Option (Nat × Nat) :=
  (a.zip b).zipIdx.findSome? fun ((x, y), buf) =>
    ((x.zip y).zipIdx.findSome? fun ((e1, e2), k) =>
      if e1.simp == e2.simp then none else some (buf, k))

/-- Which check compares two stage files, and its verdict. Each case is a
check with soundness theorems (`spec/Tau/Proofs/Check/`). `none` if no check
compares these two kinds of file. -/
def checkPair : Json.Stage → Json.Stage → Option Bool
  | .source sizes s, .kernel _ k => some (checkInlined s k sizes)
  | .source sizes s, .compiled c => some (check s sizes c)
  | .kernel sizes k, .kernel _ k' => some (checkKernels k k' sizes)
  | .kernel sizes k, .placed pl => some (checkPlaced k sizes pl)
  | .kernel sizes k, .compiled c => some (check (Source.ofKernel k) sizes c)
  | .placed pl, .compiled c => some (checkScheduled pl c)
  | .compiled c, .compiled c' => some (checkRouted c c')
  | _, _ => none

/-- What one side of a check ends with, on expressions, or why it has no
result. -/
def stageExprs : Json.Stage → Except String (List (List Expr))
  | .source sizes s =>
    match sourceExprs s sizes with
    | some e => .ok e
    | none => .error sourceFailed
  | .kernel sizes k =>
    match kernelExprs k sizes with
    | some e => .ok e
    | none => .error kernelFailed
  | .placed pl =>
    match placedExprs pl with
    | some e => .ok e
    | none => .error ("in the placed program, " ++ placedFailed)
  | .compiled c =>
    match execute exprSem c.cfg c.prog c.cycles (image c.map c.memSizes Expr.init .fill) with
    | .ok mem => .ok (extract c.map mem .fill)
    | .error t => .error (showTrap t)

/-- The events of one side of a check, on expressions. -/
def stageEvents : Json.Stage → List (Event Expr)
  | .source sizes s => sourceEvents s sizes
  | .kernel sizes k => kernelEvents k sizes
  | .placed pl => placedEvents pl
  | .compiled c => machineEvents c

/-- The first event of `a` that is not an event of `b`. -/
def firstLate (a b : List (Event Expr)) : Option (Event Expr) :=
  let b' := b.map (Event.map Expr.simp)
  a.reverse.find? fun e => !b'.contains (e.map Expr.simp)

/-- Why `checkPair` rejected. Only used to print a message. -/
def explainPair (before after : Json.Stage) : String :=
  match stageExprs before, stageExprs after with
  | .error e, _ => s!"first file: {e}"
  | _, .error e => e
  | .ok a, .ok b =>
    if stageSizes before != stageSizes after then
      "the two files do not give the buffers the same sizes"
    else
      let same := stageName before == stageName after
      let first := if same then s!"first {stageName before}" else stageName before
      let second := if same then s!"second {stageName after}" else stageName after
      match firstDiff a b with
      | some (buf, pos) =>
        s!"buffer {buf}, word {pos}: the {second} does not compute what the {first} computes"
      | none =>
        if sameExprs a b then
          match firstLate (stageEvents before) (stageEvents after) with
          | some e =>
            let what := match e.store with
              | some (buf, pos) => s!"the store to buffer {buf}, word {pos},"
              | none => "a word"
            s!"cycle {e.time}: {what} that the {first} issues on this cycle is not issued then by the {second}"
          | none => s!"the {second} and the {first} disagree"
        else s!"the {second} and the {first} end with different buffers"

/-! ## Holding a pass to what it decides

The rules of `Tau.Check.Decides`, for two stage files. Like the comparisons
below, this is a test of the compiler and no theorem depends on it. -/

/-- The parts of the rule for two stage files, each with what it says, in
the order they are tried. `none` if no rule compares these two kinds of
file. -/
def decidesParts : Json.Stage → Json.Stage → Option (List (String × Bool))
  | .kernel _ k, .placed pl => some
    [ ("the placed program has scratch space: a word of memory that belongs to no buffer",
        pl.noScratch),
      ("the placed program does not have one instruction for each operation of the kernel",
        sameOperations k pl),
      ("the placed program does not have one write for each store of the kernel",
        sameStores k pl) ]
  | .placed pl, .compiled c => some
    ([ ("the compiled program has another memory map", c.map == pl.map),
       ("the compiled program is for another machine", c.cfg.sameSlices pl.cfg) ] ++
     (List.range pl.cfg.kinds.length).map fun p =>
       (s!"slice {p}: the compiled program does not have the placed program's instructions, " ++
          "with nothing added but reads of the same buffer words and uses of scratch words",
        sameWorkAt pl c p))
  | .compiled c, .compiled c' => some
    [ ("the second program has another memory map, other memory sizes or another length",
        c'.map == c.map && c'.memSizes == c.memSizes && c'.cycles == c.cycles),
      ("the second program is for another machine", c'.cfg.sameSlices c.cfg),
      ("the second program does not have the entries of the first with other stream numbers",
        sameEntries c c'),
      ("a stream of the first program has two streams of the second in its place",
        oneRenaming c c') ]
  | _, _ => none

/-- Which rule compares two stage files, and its verdict: `placeOnly`,
`scheduleOnly` or `routeOnly`. -/
def decidesPair (before after : Json.Stage) : Option Bool :=
  (decidesParts before after).map fun parts => parts.all (·.2)

/-- The first part of the rule that does not hold. -/
def explainDecides (before after : Json.Stage) : String :=
  match (decidesParts before after).bind fun parts => parts.find? fun part => !part.2 with
  | some (what, _) => what
  | none => "the rule holds"

/-! ## Comparing a pass with its Lean model

`Kernel.unroll` (`Tau.IR.Unroll`) is the Lean model of the compiler's
`tau-unroll`. The functions below decide whether the two gave the same kernel
for one input. This is a test of the compiler against the model. It is not
covered by a proof and no theorem depends on it. -/

/-- Give the value a statement defines the number `next`, and its operands
the numbers `m` gives them. `m` maps old numbers to new ones, most recent
first. Returns the statement, the new map and the next free number. `none` if
the statement uses a value before it is defined. -/
def renumberStmt (m : List (Var × Var)) (next : Nat) :
    Stmt → Option (Stmt × List (Var × Var) × Nat)
  | .load dst ty buf ix => some (.load next ty buf ix, (dst, next) :: m, next + 1)
  | .store src ty buf ix => do
    let src ← m.lookup src
    pure (.store src ty buf ix, m, next)
  | .un dst ty op a => do
    let a ← m.lookup a
    pure (.un next ty op a, (dst, next) :: m, next + 1)
  | .bin dst ty op a b => do
    let a ← m.lookup a
    let b ← m.lookup b
    pure (.bin next ty op a b, (dst, next) :: m, next + 1)
  | .matvec dst x buf ix n => do
    let x ← m.lookup x
    pure (.matvec next x buf ix n, (dst, next) :: m, next + 1)
  | .const dst ty xs => some (.const next ty xs, (dst, next) :: m, next + 1)
  | .sel dst ty c a b => do
    let c ← m.lookup c
    let a ← m.lookup a
    let b ← m.lookup b
    pure (.sel next ty c a b, (dst, next) :: m, next + 1)
  | .pin t s => do
    let (s', m', next') ← renumberStmt m next s
    pure (.pin t s', m', next')

/-- Give every value of a kernel without loops a number in order of
definition. -/
def renumber (m : List (Var × Var)) (next : Nat) : List Stmt → Option (List Stmt)
  | [] => some []
  | s :: rest => do
    let (s', m', next') ← renumberStmt m next s
    (renumber m' next' rest).map (s' :: ·)

/-- Whether `after` is the kernel that `Kernel.unroll` gives for `before`, up
to the numbering of values. -/
def sameUnroll (before after : Kernel) : Bool :=
  after.all (fun | .stmt _ => true | .loop _ _ => false) &&
  match renumber [] 0 (Kernel.unroll before), renumber [] 0 (Kernel.unroll after) with
  | some a, some b => a == b
  | _, _ => false

/-! ## Comparing the image with the Lean encoding

`Program.encode` (`Tau.Isa.Encode`) is the Lean copy of the compiler's
last step. This is a test of the compiler against the copy, as above. -/

/-- Whether `img` is the image that `Program.encode` gives for the compiled
program `c`. -/
def sameImage (c : Compiled) (img : Image) : Bool :=
  c.prog.encode c.cfg.kinds.length == img

end Tau.Tools
