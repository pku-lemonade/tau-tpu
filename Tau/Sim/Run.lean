import Tau.Sim.Json
import Tau.Passes.Unroll

/-!
# Running programs on real words

The functions the command-line tools call. `simulate` runs a compiled program
on the slice-level machine. `reference` runs a kernel directly. `checkPair`
picks the check for two stage files, and `explainPair` says why it rejected.
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

/-- Run a compiled program on the given buffer contents. -/
def simulate (c : Compiled) (lanes : Nat) (bufs : List (List (List Int))) :
    Except String (List (List (List Int))) :=
  let words : List (List (Word lanes)) := bufs.map (·.map Word.ofInts)
  match execute (wordSem lanes) c.cfg c.prog c.cycles (c.image words Word.zero) with
  | .error t => .error (showTrap t)
  | .ok mem => .ok ((extract c.map mem Word.zero).map (·.map Word.toInts))

/-- Run a kernel directly on the given buffer contents. -/
def reference (k : Kernel) (lanes : Nat) (bufs : List (List (List Int))) :
    Except String (List (List (List Int))) :=
  let words : List (List (Word lanes)) := bufs.map (·.map Word.ofInts)
  match k.run (wordSem lanes) words with
  | none => .error "the kernel uses a variable with no value or a position outside a buffer"
  | some out => .ok (out.map (·.map Word.toInts))

/-- Carry out a placed program on the given buffer contents. -/
def simulatePlaced (pl : Placed) (lanes : Nat) (bufs : List (List (List Int))) :
    Except String (List (List (List Int))) :=
  let words : List (List (Word lanes)) := bufs.map (·.map Word.ofInts)
  match pl.execute (wordSem lanes) (pl.image words Word.zero) with
  | none => .error "an instruction is on the wrong kind of slice, uses a bad address, or uses a word that does not exist"
  | some mem => .ok ((extract pl.map mem Word.zero).map (·.map Word.toInts))

/-- Run the output of any compiler stage. -/
def runStage (st : Json.Stage) (lanes : Nat) (bufs : List (List (List Int))) :
    Except String (List (List (List Int))) :=
  match st with
  | .kernel _ k => reference k lanes bufs
  | .placed pl => simulatePlaced pl lanes bufs
  | .compiled c => simulate c lanes bufs

/-- The first word on which two results differ: buffer and position. -/
def firstDiff (a b : List (List Expr)) : Option (Nat × Nat) :=
  (a.zip b).zipIdx.findSome? fun ((x, y), buf) =>
    ((x.zip y).zipIdx.findSome? fun ((e1, e2), k) =>
      if e1.simp == e2.simp then none else some (buf, k))

/-- What kind of file a stage is, for messages. -/
def stageName : Json.Stage → String
  | .kernel .. => "kernel"
  | .placed _ => "placed program"
  | .compiled _ => "compiled program"

/-- Which check compares two stage files, and its verdict. Each case is a
check with a soundness theorem (`Tau/Proofs/Check/`). `none` if no check
compares these two kinds of file. -/
def checkPair : Json.Stage → Json.Stage → Option Bool
  | .kernel sizes k, .kernel _ k' => some (checkKernels k k' sizes)
  | .kernel sizes k, .placed pl => some (checkPlaced k sizes pl)
  | .kernel sizes k, .compiled c => some (check k sizes c)
  | .placed pl, .compiled c => some (checkScheduled pl c)
  | .compiled c, .compiled c' => some (checkRouted c c')
  | _, _ => none

/-- What one side of a check ends with, on expressions, or why it has no
result. -/
def stageExprs : Json.Stage → Except String (List (List Expr))
  | .kernel sizes k =>
    match kernelExprs k sizes with
    | some e => .ok e
    | none => .error "the kernel uses a variable with no value or a position outside a buffer"
  | .placed pl =>
    match placedExprs pl with
    | some e => .ok e
    | none => .error "an instruction of the placed program is on the wrong kind of slice, uses a bad address, or uses a word that does not exist"
  | .compiled c =>
    match execute exprSem c.cfg c.prog c.cycles (image c.map c.memSizes Expr.init .fill) with
    | .ok mem => .ok (extract c.map mem .fill)
    | .error t => .error (showTrap t)

/-- The sizes of the buffers of a stage, as its file declares them. -/
def stageSizes : Json.Stage → List Nat
  | .kernel sizes _ => sizes
  | .placed pl => pl.map.map (·.size)
  | .compiled c => c.map.map (·.size)

/-- Why `checkPair` rejected. Only used to print a message. -/
def explainPair (before after : Json.Stage) : String :=
  match stageExprs before, stageExprs after with
  | .error e, _ => s!"first file: {e}"
  | _, .error e => e
  | .ok a, .ok b =>
    if stageSizes before != stageSizes after then
      "the two files do not give the buffers the same sizes"
    else
      match firstDiff a b with
      | some (buf, pos) =>
        s!"buffer {buf}, word {pos}: the {stageName after} does not compute what the " ++
          s!"{stageName before} computes"
      | none => s!"the {stageName after} and the {stageName before} end with different buffers"

/-! ## Comparing a pass with its Lean model

`Kernel.unroll` (`Tau/Passes/Unroll.lean`) is the Lean model of the compiler's
`tau-unroll`. The functions below decide whether the two gave the same kernel
for one input. This is a test of the compiler against the model. It is not
covered by a proof and no theorem depends on it. -/

/-- Give every value of a kernel without loops a number in order of
definition. `m` maps old numbers to new ones, most recent first; `next` is
the next free number. `none` if a statement uses a value before it is
defined. -/
def renumber (m : List (Var × Var)) (next : Nat) : List Stmt → Option (List Stmt)
  | [] => some []
  | s :: rest =>
    let def_ (dst : Var) (s' : Stmt) : Option (List Stmt) :=
      (renumber ((dst, next) :: m) (next + 1) rest).map (s' :: ·)
    match s with
    | .load dst buf ix => def_ dst (.load next buf ix)
    | .store src buf ix => do
      let src ← m.lookup src
      (renumber m next rest).map (Stmt.store src buf ix :: ·)
    | .un dst op a => do
      let a ← m.lookup a
      def_ dst (.un next op a)
    | .bin dst op a b => do
      let a ← m.lookup a
      let b ← m.lookup b
      def_ dst (.bin next op a b)
    | .matvec dst x buf ix n => do
      let x ← m.lookup x
      def_ dst (.matvec next x buf ix n)
    | .affine dst x bias buf ix n => do
      let x ← m.lookup x
      let bias ← m.lookup bias
      def_ dst (.affine next x bias buf ix n)
    | .const dst xs => def_ dst (.const next xs)
    | .sel dst c a b => do
      let c ← m.lookup c
      let a ← m.lookup a
      let b ← m.lookup b
      def_ dst (.sel next c a b)

/-- Whether `after` is the kernel that `Kernel.unroll` gives for `before`, up
to the numbering of values. -/
def sameUnroll (before after : Kernel) : Bool :=
  after.all (fun | .stmt _ => true | .loop _ _ => false) &&
  match renumber [] 0 (Kernel.unroll before), renumber [] 0 (Kernel.unroll after) with
  | some a, some b => a == b
  | _, _ => false

end Tau.Sim
