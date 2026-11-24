import Lean.Data.Json
import Tau.Check.Stages

/-!
# Reading and writing JSON

The compiler and the Lean tools exchange four kinds of file.

* A *kernel* file: the buffer sizes and the statements of a kernel.
* A *placed* file: the chip, the memory map and the instructions in order.
* A *compiled* file: the chip, the memory map and the timed program.
* A *buffers* file: the number of lanes and the contents of every buffer, as
  signed integers.

`docs/formats.md` describes the files. This module is not covered by any
proof: a mistake here shows up as a wrong file being read, not as an unsound
theorem.
-/

namespace Tau.Json

open Lean (Json)

def nat (j : Json) (key : String) : Except String Nat := j.getObjValAs? Nat key

def str (j : Json) (key : String) : Except String String := j.getObjValAs? String key

def arr (j : Json) (key : String) : Except String (List Json) := do
  let a ← (← j.getObjVal? key).getArr?
  pure a.toList

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
  | "shift" => pure (.shift (← nat j "k"))
  | "rotate" => pure (.rotate (← nat j "k"))
  | s => throw s!"unknown one-word operation '{s}'"

def binOp (j : Json) : Except String BinOp := do
  match ← str j "fn" with
  | "add" => pure .add
  | "sub" => pure .sub
  | "mul" => pure .mul
  | "max" => pure .max
  | "min" => pure .min
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
  | s => throw s!"unknown instruction '{s}'"

def timed (j : Json) : Except String Timed := do
  pure ⟨← nat j "slice", ← nat j "time", ← instr j⟩

def config (j : Json) : Except String Config := do
  let ks ← (← arr j "kinds").mapM fun k => do kind (← k.getStr?)
  pure {
    kinds := ks
    streams := ← nat j "streams"
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
    | s => throw s!"unknown instruction '{s}'"
  pure (← nat j "slice", i)

def placed (j : Json) : Except String Placed := do
  pure {
    cfg := ← config (← j.getObjVal? "config")
    memSizes := ← (← arr j "memSizes").mapM fun n => n.getNat?
    map := ← (← arr j "map").mapM placement
    instrs := ← (← arr j "instructions").mapM pinstr }

def idx (j : Json) : Except String Idx := do
  pure ⟨← nat j "base", ← nat j "stride"⟩

def stmt (j : Json) : Except String Stmt := do
  match ← str j "op" with
  | "load" => pure (.load (← nat j "dst") (← nat j "buf") (← idx j))
  | "store" => pure (.store (← nat j "src") (← nat j "buf") (← idx j))
  | "un" => pure (.un (← nat j "dst") (← unOp j) (← nat j "a"))
  | "bin" => pure (.bin (← nat j "dst") (← binOp j) (← nat j "a") (← nat j "b"))
  | "matvec" =>
    pure (.matvec (← nat j "dst") (← nat j "x") (← nat j "buf") (← idx j) (← nat j "n"))
  | s => throw s!"unknown statement '{s}'"

def item (j : Json) : Except String Item := do
  match ← str j "op" with
  | "loop" => pure (.loop (← nat j "n") (← (← arr j "body").mapM stmt))
  | _ => pure (.stmt (← stmt j))

/-- A kernel file: the buffer sizes and the kernel. -/
def kernel (j : Json) : Except String (List Nat × Kernel) := do
  let sizes ← (← arr j "buffers").mapM fun n => n.getNat?
  let body ← (← arr j "body").mapM item
  pure (sizes, body)

/-- The output of one compiler stage. -/
inductive Stage where
  | kernel (k : Kernel)
  | placed (p : Placed)
  | compiled (c : Compiled)

/-- Read a stage file. The kind of file is told from its fields: a kernel has
`body`, a placed program has `instructions`, a compiled program has
`program`. -/
def stage (j : Json) : Except String Stage := do
  if (j.getObjVal? "body").toOption.isSome then
    pure (.kernel (← kernel j).2)
  else if (j.getObjVal? "instructions").toOption.isSome then
    pure (.placed (← placed j))
  else if (j.getObjVal? "program").toOption.isSome then
    pure (.compiled (← compiled j))
  else
    throw "not a kernel, placed or compiled file"

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
