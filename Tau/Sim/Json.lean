import Lean.Data.Json
import Tau.Check.Passes
import Tau.Isa.Encode

/-!
# Reading and writing JSON

The compiler, the frontend and the Lean tools exchange five kinds of file.

* A *source* file: the buffer sizes and the body of a source program. With
  no calls in it, it is a *kernel* file.
* A *placed* file: the machine, the memory map and the instructions in order.
* A *compiled* file: the machine, the memory map and the timed program.
* An *image* file: a compiled file with the program as numbers.
* A *buffers* file: the number of lanes and the contents of every buffer, as
  signed integers.

This module is not covered by any proof: a mistake here shows up as a wrong
file being read, not as an unsound theorem.

Docs: README 5 (`Tau/Docs/`).
-/

namespace Tau.Json

open Lean (Json)

def nat (j : Json) (key : String) : Except String Nat := j.getObjValAs? Nat key

def str (j : Json) (key : String) : Except String String := j.getObjValAs? String key

def int (j : Json) (key : String) : Except String Int := j.getObjValAs? Int key

/-- A number that may be left out, in which case it is `default`. -/
def natOr (j : Json) (key : String) (default : Nat) : Nat :=
  (nat j key).toOption.getD default

def arr (j : Json) (key : String) : Except String (List Json) := do
  let a ← (← j.getObjVal? key).getArr?
  pure a.toList

def nats (j : Json) (key : String) : Except String (List Nat) := do
  (← arr j key).mapM fun n => n.getNat?

def ints (j : Json) (key : String) : Except String (List Int) := do
  (← arr j key).mapM fun n => n.getInt?

def kind : String → Except String Kind
  | "mem" => pure .mem
  | "vxm" => pure .vxm
  | "sxm" => pure .sxm
  | "mxm" => pure .mxm
  | s => throw s!"unknown slice kind '{s}'"

def track (j : Json) (key : String) : Except String Track := do
  let t ← j.getObjVal? key
  let d ← match ← str t "dir" with
    | "east" => pure Dir.east
    | "west" => pure Dir.west
    | s => throw s!"unknown direction '{s}'"
  pure ⟨d, ← nat t "id"⟩

def unOp (j : Json) : Except String UnOp := do
  match ← str j "fn" with
  | "relu" => pure .relu
  | "requant" => pure (.requant (← nat j "k"))
  | "neg" => pure .neg
  | "abs" => pure .abs
  | "shl" => pure (.shl (← nat j "k"))
  | "addi" => pure (.addi (← int j "k"))
  | "muli" => pure (.muli (← int j "k"))
  | "shift" => pure (.shift (← nat j "k"))
  | "rotate" => pure (.rotate (← nat j "k"))
  | "reverse" => pure .reverse
  | "broadcast" => pure (.broadcast (← nat j "k"))
  | "permute" => pure (.permute (← nats j "table"))
  | s => throw s!"unknown one-word operation '{s}'"

def binOp (j : Json) : Except String BinOp := do
  match ← str j "fn" with
  | "add" => pure .add
  | "sub" => pure .sub
  | "mul" => pure .mul
  | "max" => pure .max
  | "min" => pure .min
  | "and" => pure .and
  | "or" => pure .or
  | "xor" => pure .xor
  | "lt" => pure .lt
  | s => throw s!"unknown two-word operation '{s}'"

def instr (j : Json) : Except String Instr := do
  match ← str j "op" with
  | "read" => pure (.read (← nat j "addr") (← track j "dst"))
  | "write" => pure (.write (← track j "src") (← nat j "addr"))
  | "un" => pure (.un (← unOp j) (← track j "src") (← track j "dst"))
  | "bin" => pure (.bin (← binOp j) (← track j "a") (← track j "b") (← track j "dst"))
  | "load" => pure (.load (← track j "src"))
  | "mac" => pure (.mac (← nat j "j") (← track j "src"))
  | "emit" => pure (.emit (← track j "dst"))
  | "const" => pure (.const (← ints j "values") (← track j "dst"))
  | "sel" => pure (.sel (← track j "m") (← track j "a") (← track j "b") (← track j "dst"))
  | "seed" => pure (.seed (← track j "src"))
  | "install" => pure (.install (← nat j "j") (← track j "src"))
  | "macw" => pure (.macw (← nat j "j"))
  | s => throw s!"unknown instruction '{s}'"

def timed (j : Json) : Except String Timed := do
  pure {
    slice := ← nat j "slice"
    time := ← nat j "time"
    instr := ← instr j
    repeats := natOr j "repeats" 0
    gap := natOr j "gap" 0
    stride := natOr j "stride" 0 }

def config (j : Json) : Except String Config := do
  let ks ← (← arr j "kinds").mapM fun k => do kind (← k.getStr?)
  pure {
    kinds := ks
    streams := ← nat j "streams"
    mxmWeights := natOr j "mxmWeights" 8
    memDelay := ← nat j "memDelay"
    vxmDelay := ← nat j "vxmDelay"
    sxmDelay := ← nat j "sxmDelay"
    mxmDelay := ← nat j "mxmDelay" }

def placement (j : Json) : Except String Placement := do
  pure ⟨← nat j "slice", ← nat j "base", ← nat j "size"⟩

def compiled (j : Json) : Except String Compiled := do
  pure {
    cfg := ← config (← j.getObjVal? "config")
    memSizes := ← (← arr j "memSizes").mapM fun n => n.getNat?
    map := ← (← arr j "map").mapM placement
    prog := ← (← arr j "program").mapM timed
    cycles := ← nat j "cycles" }

def pinstr (j : Json) : Except String (Nat × PInstr) := do
  let i ← match ← str j "op" with
    | "read" => pure (PInstr.read (← nat j "dst") (← nat j "addr"))
    | "write" => pure (PInstr.write (← nat j "src") (← nat j "addr"))
    | "un" => pure (PInstr.un (← nat j "dst") (← unOp j) (← nat j "src"))
    | "bin" => pure (PInstr.bin (← nat j "dst") (← binOp j) (← nat j "a") (← nat j "b"))
    | "load" => pure (PInstr.load (← nat j "src"))
    | "mac" => pure (PInstr.mac (← nat j "j") (← nat j "src"))
    | "emit" => pure (PInstr.emit (← nat j "dst"))
    | "const" => pure (PInstr.const (← nat j "dst") (← ints j "values"))
    | "sel" => pure (PInstr.sel (← nat j "dst") (← nat j "m") (← nat j "a") (← nat j "b"))
    | "seed" => pure (PInstr.seed (← nat j "src"))
    | "install" => pure (PInstr.install (← nat j "j") (← nat j "src"))
    | "macw" => pure (PInstr.macw (← nat j "j"))
    | s => throw s!"unknown instruction '{s}'"
  -- A pinned instruction has the cycle it must be issued on.
  let i := match (nat j "pin").toOption with
    | some t => PInstr.pin t i
    | none => i
  pure (← nat j "slice", i)

def placed (j : Json) : Except String Placed := do
  pure {
    cfg := ← config (← j.getObjVal? "config")
    memSizes := ← (← arr j "memSizes").mapM fun n => n.getNat?
    map := ← (← arr j "map").mapM placement
    instrs := ← (← arr j "instructions").mapM pinstr }

def idx (j : Json) : Except String Idx := do
  pure ⟨← nat j "base", ← nat j "stride"⟩

/-- A statement without its pin. -/
def bareStmt (j : Json) : Except String Stmt := do
  match ← str j "op" with
  | "load" => pure (.load (← nat j "dst") (← nat j "buf") (← idx j))
  | "store" => pure (.store (← nat j "src") (← nat j "buf") (← idx j))
  | "un" => pure (.un (← nat j "dst") (← unOp j) (← nat j "a"))
  | "bin" => pure (.bin (← nat j "dst") (← binOp j) (← nat j "a") (← nat j "b"))
  | "matvec" =>
    pure (.matvec (← nat j "dst") (← nat j "x") (← nat j "buf") (← idx j) (← nat j "n"))
  | "affine" =>
    pure (.affine (← nat j "dst") (← nat j "x") (← nat j "bias") (← nat j "buf") (← idx j)
      (← nat j "n"))
  | "const" => pure (.const (← nat j "dst") (← ints j "values"))
  | "sel" => pure (.sel (← nat j "dst") (← nat j "m") (← nat j "a") (← nat j "b"))
  | s => throw s!"unknown statement '{s}'"

/-- A statement. A pinned one has `at`, the cycle its word is issued on, and
may have `every`, how far that cycle moves on each iteration of a loop. -/
def stmt (j : Json) : Except String Stmt := do
  let s ← bareStmt j
  match (nat j "at").toOption with
  | some t => pure (.pin ⟨t, natOr j "every" 0⟩ s)
  | none => pure s

def item (j : Json) : Except String Item := do
  match ← str j "op" with
  | "loop" => pure (.loop (← nat j "n") (← (← arr j "body").mapM stmt))
  | _ => pure (.stmt (← stmt j))

/-- A kernel file: the buffer sizes and the kernel. -/
def kernel (j : Json) : Except String (List Nat × Kernel) := do
  let sizes ← (← arr j "buffers").mapM fun n => n.getNat?
  let body ← (← arr j "body").mapM item
  pure (sizes, body)

/-- The body of a source program: items and calls. A call has the caller's
buffers it passes (`args`), the cycle its pins count from (`at`, 0 if left
out), and the body of the kernel it calls. -/
partial def sourceBody : List Json → Except String Source
  | [] => pure .done
  | j :: rest => do
    let more ← sourceBody rest
    match ← str j "op" with
    | "call" =>
      let callee ← sourceBody (← arr j "body")
      pure (.call callee (← nats j "args") (natOr j "at" 0) more)
    | _ => pure (.item (← item j) more)

/-- A source file: the buffer sizes and the source program. -/
def source (j : Json) : Except String (List Nat × Source) := do
  let sizes ← (← arr j "buffers").mapM fun n => n.getNat?
  pure (sizes, ← sourceBody (← arr j "body"))

/-- An image file: a compiled file whose program is numbers, one list per
slice. Returns the compiled program with nothing in it yet, and the image. -/
def imageFile (j : Json) : Except String (Compiled × Image) := do
  let img ← (← arr j "image").mapM fun ws => do
    (← ws.getArr?).toList.mapM fun n => n.getNat?
  pure ({
    cfg := ← config (← j.getObjVal? "config")
    memSizes := ← (← arr j "memSizes").mapM fun n => n.getNat?
    map := ← (← arr j "map").mapM placement
    prog := []
    cycles := ← nat j "cycles" }, img)

/-- The output of one compiler stage. A source program or a kernel comes with
the sizes of its buffers. -/
inductive Stage where
  | source (sizes : List Nat) (s : Source)
  | kernel (sizes : List Nat) (k : Kernel)
  | placed (p : Placed)
  | compiled (c : Compiled)

/-- Read a stage file. The kind of file is told from its fields: a source
program or a kernel has `body`, a placed program has `instructions`, a
compiled program has `program`, and an image has `image`. A body with a call
in it is a source program; without one it is a kernel. An image is decoded
(`Image.decode`) and is from then on a compiled program. -/
def stage (j : Json) : Except String Stage := do
  if (j.getObjVal? "body").toOption.isSome then
    let hasCall := (← arr j "body").any fun it => (str it "op").toOption == some "call"
    if hasCall then
      let (sizes, s) ← source j
      pure (.source sizes s)
    else
      let (sizes, k) ← kernel j
      pure (.kernel sizes k)
  else if (j.getObjVal? "instructions").toOption.isSome then
    pure (.placed (← placed j))
  else if (j.getObjVal? "program").toOption.isSome then
    pure (.compiled (← compiled j))
  else if (j.getObjVal? "image").toOption.isSome then
    let (c, img) ← imageFile j
    match img.decode with
    | some prog => pure (.compiled { c with prog := prog })
    | none => throw "the image is not well formed"
  else
    throw "not a source, kernel, placed, compiled or image file"

/-- A buffers file: the number of lanes and, for every buffer, its words as
lists of signed integers. -/
def buffers (j : Json) : Except String (Nat × List (List (List Int))) := do
  let lanes ← nat j "lanes"
  let bufs ← (← arr j "buffers").mapM fun b => do
    (← b.getArr?).toList.mapM fun w => do
      (← w.getArr?).toList.mapM fun x => x.getInt?
  pure (lanes, bufs)

def ofBuffers (lanes : Nat) (bufs : List (List (List Int))) : Json :=
  Json.mkObj [
    ("lanes", Lean.toJson lanes),
    ("buffers", Lean.toJson bufs) ]

/-- A timeline as JSON: for each event its cycle, its word, and for a store
the buffer and the position. -/
def ofTimeline (events : List (Event (List Int))) : Json :=
  Lean.Json.arr (events.map fun e =>
    Json.mkObj ([("time", Lean.toJson e.time), ("word", Lean.toJson e.word)] ++
      match e.store with
      | some (b, k) => [("buf", Lean.toJson b), ("pos", Lean.toJson k)]
      | none => [])).toArray

/-- Read and parse a JSON file. -/
def readFile (path : String) : IO Json := do
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- Turn a parse result into an `IO` action, naming the file on failure. -/
def orFail {α : Type} (path : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{path}: {e}")

end Tau.Json
