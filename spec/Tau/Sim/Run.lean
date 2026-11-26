import Tau.Sim.Json
import Tau.IR.Unroll

/-!
# Running programs on real words

The functions the command-line tools call. `runStage` runs the output of any
compiler stage and `timelineOf` gives its events. `checkPair` picks the check
for two stage files, and `explainPair` says why it rejected.
-/

namespace Tau.Sim

def showTrack (tr : Track) : String :=
  (match tr.dir with | .east => "east" | .west => "west") ++ s!" stream {tr.id}"

def showTrap (t : Trap) : String :=
  let what := match t.kind with
    | .emptyRead => "read a stream slot that held nothing"
    | .badTrack => "named a stream that does not exist"
    | .badAddress => "used a memory address that is out of range"
    | .wrongSlice => "was sent to a slice of the wrong kind"
    | .twoInstructions => "had two instructions due on the same cycle"
    | .noOperand => "was told to multiply before it was given a vector"
    | .noSlice => "does not exist"
  s!"trap at cycle {t.time}: slice {t.slice} {what}"

/-- The buffers as words. -/
def toWords (lanes : Nat) (bufs : List (List (List Int))) : List (List (Word lanes)) :=
  bufs.map (·.map Word.ofInts)

/-- Run a compiled program on the given buffer contents. -/
def simulate (c : Compiled) (lanes : Nat) (bufs : List (List (List Int))) :
    Except String (List (List (List Int))) :=
  match execute (wordSem lanes) c.cfg c.prog c.cycles (c.image (toWords lanes bufs) Word.zero) with
  | .error t => .error (showTrap t)
  | .ok mem => .ok ((extract c.map mem Word.zero).map (·.map Word.toInts))

def kernelFailed : String :=
  "the kernel uses a variable with no value or a position outside a buffer"

def sourceFailed : String :=
  "the program uses a variable with no value or a position outside a buffer, or makes a call it may not make"

def placedFailed : String :=
  "an instruction is on the wrong kind of slice, uses a bad address, or uses a word that does not exist"

/-- Run a kernel directly on the given buffer contents. -/
def reference (k : Kernel) (lanes : Nat) (bufs : List (List (List Int))) :
    Except String (List (List (List Int))) :=
  match k.run (wordSem lanes) (toWords lanes bufs) with
  | none => .error kernelFailed
  | some out => .ok (out.map (·.map Word.toInts))

/-- Run a source program directly on the given buffer contents. -/
def referenceSource (s : Source) (lanes : Nat) (bufs : List (List (List Int))) :
    Except String (List (List (List Int))) :=
  match s.run (wordSem lanes) (toWords lanes bufs) with
  | none => .error sourceFailed
  | some out => .ok (out.map (·.map Word.toInts))

/-- Carry out a placed program on the given buffer contents. -/
def simulatePlaced (pl : Placed) (lanes : Nat) (bufs : List (List (List Int))) :
    Except String (List (List (List Int))) :=
  match pl.execute (wordSem lanes) (pl.image (toWords lanes bufs) Word.zero) with
  | none => .error placedFailed
  | some mem => .ok ((extract pl.map mem Word.zero).map (·.map Word.toInts))

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

/-- Buffer contents for a stage: the buffers given, and words of zeros for
any buffer the file leaves out. A program's scratch buffers come after the
buffers the user fills. -/
def padBuffers (st : Json.Stage) (lanes : Nat) (bufs : List (List (List Int))) :
    List (List (List Int)) :=
  bufs ++ ((stageSizes st).drop bufs.length).map fun n =>
    List.replicate n (List.replicate lanes 0)

/-- Run the output of any compiler stage. -/
def runStage (st : Json.Stage) (lanes : Nat) (bufs : List (List (List Int))) :
    Except String (List (List (List Int))) :=
  let bufs := padBuffers st lanes bufs
  match st with
  | .source _ s => referenceSource s lanes bufs
  | .kernel _ k => reference k lanes bufs
  | .placed pl => simulatePlaced pl lanes bufs
  | .compiled c => simulate c lanes bufs

/-- The events of any compiler stage on the given buffer contents, in order
of time: the pinned words of a source program, a kernel or a placed program,
and every word a compiled program issues. -/
def timelineOf (st : Json.Stage) (lanes : Nat) (bufs : List (List (List Int))) :
    List (Event (List Int)) :=
  let words := toWords lanes (padBuffers st lanes bufs)
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
  | .load dst buf ix => some (.load next buf ix, (dst, next) :: m, next + 1)
  | .store src buf ix => do
    let src ← m.lookup src
    pure (.store src buf ix, m, next)
  | .un dst op a => do
    let a ← m.lookup a
    pure (.un next op a, (dst, next) :: m, next + 1)
  | .bin dst op a b => do
    let a ← m.lookup a
    let b ← m.lookup b
    pure (.bin next op a b, (dst, next) :: m, next + 1)
  | .matvec dst x buf ix n => do
    let x ← m.lookup x
    pure (.matvec next x buf ix n, (dst, next) :: m, next + 1)
  | .affine dst x bias buf ix n => do
    let x ← m.lookup x
    let bias ← m.lookup bias
    pure (.affine next x bias buf ix n, (dst, next) :: m, next + 1)
  | .const dst xs => some (.const next xs, (dst, next) :: m, next + 1)
  | .sel dst c a b => do
    let c ← m.lookup c
    let a ← m.lookup a
    let b ← m.lookup b
    pure (.sel next c a b, (dst, next) :: m, next + 1)
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

end Tau.Sim
