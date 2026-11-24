import Tau.Sim.Json

/-!
# Running programs on real words

The functions the command-line tools call. `simulate` runs a compiled program
on the slice-level machine. `reference` runs a kernel directly. `explain` says
why the checker rejected a program.
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
  | .kernel k => reference k lanes bufs
  | .placed pl => simulatePlaced pl lanes bufs
  | .compiled c => simulate c lanes bufs

/-- The first word on which two results differ: buffer and position. -/
def firstDiff (a b : List (List Expr)) : Option (Nat × Nat) :=
  (a.zip b).zipIdx.findSome? fun ((x, y), buf) =>
    ((x.zip y).zipIdx.findSome? fun ((e1, e2), k) =>
      if e1.simp == e2.simp then none else some (buf, k))

/-- Why `check` rejected a compiled program. Only used to print a message. -/
def explain (k : Kernel) (sizes : List Nat) (c : Compiled) : String :=
  if c.map.map (·.size) != sizes then
    "the memory map does not give every buffer its declared size"
  else
    match execute exprSem c.cfg c.prog c.cycles (image c.map c.memSizes Expr.init .fill) with
    | .error t => showTrap t
    | .ok mem =>
      match kernelExprs k sizes with
      | none => "the kernel uses a variable with no value or a position outside a buffer"
      | some e =>
        match firstDiff (extract c.map mem .fill) e with
        | some (buf, pos) =>
          s!"buffer {buf}, word {pos}: the program does not compute what the kernel computes"
        | none => "the program and the kernel end with different buffers"

/-- The verdict on the output of any compiler stage, against the kernel `k`.
Each case is a check with a soundness theorem. -/
def checkStage (k : Kernel) (sizes : List Nat) : Json.Stage → Bool
  | .kernel k' => checkKernels k k' sizes
  | .placed pl => checkPlaced k sizes pl
  | .compiled c => check k sizes c

/-- Why `checkStage` rejected. Only used to print a message. -/
def explainStage (k : Kernel) (sizes : List Nat) : Json.Stage → String
  | .compiled c => explain k sizes c
  | .kernel k' =>
    match kernelExprs k sizes, kernelExprs k' sizes with
    | none, _ => "the kernel uses a variable with no value or a position outside a buffer"
    | _, none => "the rewritten kernel uses a variable with no value or a position outside a buffer"
    | some a, some b =>
      match firstDiff a b with
      | some (buf, pos) => s!"buffer {buf}, word {pos}: the two kernels compute different things"
      | none => "the two kernels end with different buffers"
  | .placed pl =>
    if pl.map.map (·.size) != sizes then
      "the memory map does not give every buffer its declared size"
    else
      match placedExprs pl, kernelExprs k sizes with
      | none, _ => "an instruction is on the wrong kind of slice, uses a bad address, or uses a word that does not exist"
      | _, none => "the kernel uses a variable with no value or a position outside a buffer"
      | some m, some e =>
        match firstDiff m e with
        | some (buf, pos) =>
          s!"buffer {buf}, word {pos}: the instructions do not compute what the kernel computes"
        | none => "the instructions and the kernel end with different buffers"

end Tau.Sim
