import Tau.CellLevel.Machine

/-!
# Test: operations, repeats and stored columns

Small checks of the lane operations on real words, and of two machine
features on hand-written programs: an instruction that repeats, and a matrix
slice that stores its columns.
-/

namespace TauTest.Features

open Tau

/-- Apply a one-word operation to a four-lane word. -/
def un (op : UnOp) (xs : List Int) : List Int :=
  ((wordSem 4).un op (Word.ofInts xs)).toInts

/-- Apply a two-word operation to four-lane words. -/
def bin (op : BinOp) (xs ys : List Int) : List Int :=
  ((wordSem 4).bin op (Word.ofInts xs) (Word.ofInts ys)).toInts

#guard un .neg [1, -2, 0, 7] == [-1, 2, 0, -7]
#guard un .abs [1, -2, 0, -7] == [1, 2, 0, 7]
#guard un (.shl 3) [1, -2, 0, 5] == [8, -16, 0, 40]
#guard un (.addi (-3)) [1, -2, 0, 5] == [-2, -5, -3, 2]
#guard un (.muli (-2)) [1, -2, 0, 5] == [-2, 4, 0, -10]
#guard un (.requant 1) [300, -300, 5, -5] == [127, -128, 2, -3]
#guard un (.shift 1) [1, 2, 3, 4] == [0, 1, 2, 3]
#guard un (.rotate 1) [1, 2, 3, 4] == [2, 3, 4, 1]
#guard un .reverse [1, 2, 3, 4] == [4, 3, 2, 1]
#guard un (.broadcast 2) [1, 2, 3, 4] == [3, 3, 3, 3]
#guard un (.permute [3, 3, 0]) [1, 2, 3, 4] == [4, 4, 1, 0]
#guard bin .and [12, -1, 0, 5] [10, 7, 9, 4] == [8, 7, 0, 4]
#guard bin .or [12, 0, 0, 5] [10, 7, 9, 2] == [14, 7, 9, 7]
#guard bin .xor [12, -1, 0, 5] [10, 0, 9, 5] == [6, -1, 9, 0]
#guard bin .lt [1, -2, 3, 3] [2, -3, 3, 4] == [1, 0, 0, 1]
#guard ((wordSem 4).sel (Word.ofInts [1, 0, -5, 0]) (Word.ofInts [10, 20, 30, 40])
          (Word.ofInts [1, 2, 3, 4])).toInts == [10, 2, 30, 4]
#guard ((wordSem 4).const [7, -7]).toInts == [7, -7, 0, 0]

/-! ## A machine for the programs below -/

def cfg : Config where
  kinds := [.mxm, .mem, .vxm, .mem]
  streams := 2
  mxmWeights := 2
  memDelay := 1
  vxmDelay := 1
  sxmDelay := 1
  mxmDelay := 1

def e (id : Nat) : Track := ⟨.east, id⟩
def w (id : Nat) : Track := ⟨.west, id⟩

def words (rows : List (List Int)) : List (Word 2) := rows.map Word.ofInts

/-- Run on both machines and return slice 3's memory, or `none` on a trap or
if the two machines disagree. -/
def run (prog : Program) (cycles : Nat) (image : List (List (Word 2))) :
    Option (List (List Int)) :=
  match execute (wordSem 2) cfg prog cycles image, cellExecute cfg prog cycles image with
  | .ok mem, .ok mem' =>
    if mem == mem' then some ((mem[3]?.getD []).map Word.toInts) else none
  | _, _ => none

/-! ## Repeat: copy three words with two instructions -/

/-- Slice 1 reads addresses 0, 1, 2 on cycles 0, 2, 4. Each word reaches
slice 3 four cycles after its read, where slice 3 writes addresses 0, 1, 2. -/
def copy3 : Program :=
  [ { slice := 1, time := 0, instr := .read 0 (e 0), repeats := 2, gap := 1, stride := 1 },
    { slice := 3, time := 4, instr := .write (e 0) 0, repeats := 2, gap := 1, stride := 1 } ]

#guard run copy3 9 [[], words [[1, 2], [3, 4], [5, 6]], [], words [[0, 0], [0, 0], [0, 0]]]
        == some [[1, 2], [3, 4], [5, 6]]

-- With the wrong gap on the write, the second word is missed.
#guard run (copy3.map fun i => if i.slice = 3 then { i with gap := 0 } else i) 9
        [[], words [[1, 2], [3, 4], [5, 6]], [], words [[0, 0], [0, 0], [0, 0]]]
        == none

/-! ## Stored columns: install once, multiply twice -/

/-- Slice 1 holds the two columns of a matrix at addresses 0 and 1 and two
vectors at addresses 2 and 3. The columns are installed in the matrix slice
once. Each vector is then loaded and multiplied with `macw`, and the two
products are written to slice 3. -/
def twice : Program :=
  [ -- columns: read on cycles 0, 1; they arrive at slice 0 on cycles 3, 4
    { slice := 1, time := 0, instr := .read 0 (w 0), repeats := 1, stride := 1 },
    { slice := 0, time := 3, instr := .install 0 (w 0), repeats := 1, stride := 1 },
    -- first vector: arrives on cycle 5
    .once 1 2 (.read 2 (w 0)),
    .once 0 5 (.load (w 0)),
    { slice := 0, time := 6, instr := .macw 0, repeats := 1, stride := 1 },
    .once 0 8 (.emit (e 0)),
    -- second vector: arrives on cycle 9
    .once 1 6 (.read 3 (w 0)),
    .once 0 9 (.load (w 0)),
    { slice := 0, time := 10, instr := .macw 0, repeats := 1, stride := 1 },
    .once 0 12 (.emit (e 0)),
    -- the products leave slice 0 two cycles after each emit and take three
    -- more to reach slice 3
    .once 3 13 (.write (e 0) 0),
    .once 3 17 (.write (e 0) 1) ]

-- Columns (1, 3) and (2, 4): the matrix with rows (1, 2) and (3, 4).
-- Times (10, 100) is (210, 430). Times (1, 1) is (3, 7).
#guard run twice 18
        [[], words [[1, 3], [2, 4], [10, 100], [1, 1]], [], words [[0, 0], [0, 0]]]
        == some [[210, 430], [3, 7]]

end TauTest.Features
