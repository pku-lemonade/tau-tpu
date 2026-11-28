import Tau.Machine.CellLevel
import Tau.Machine.Issues
import Tau.IR.MemMap

/-!
# Test: operations, repeats, installed words and banks

Small checks of the lane operations on real words, and of four machine
features on hand-written programs: an instruction that repeats, a matrix
slice that multiplies by its installed words, an operation with a delay of
its own, and a
memory slice that reads one bank while it writes the other. And of a memory
map that deals a buffer out over two memories.
-/

namespace TauTest.Features

open Tau

/-- Apply a one-value operation of type `ty` to a value of four elements. -/
def un (ty : DType) (op : UnOp) (xs : List Int) : List Int :=
  Value.toInts ((wordSem 4).un ty op (Value.ofInts ty xs))

/-- Apply a two-value operation of type `ty` to values of four elements. -/
def bin (ty : DType) (op : BinOp) (xs ys : List Int) : List Int :=
  Value.toInts ((wordSem 4).bin ty op (Value.ofInts ty xs) (Value.ofInts ty ys))

#guard un .i8 .neg [1, -2, 0, 7] == [-1, 2, 0, -7]
#guard un .i8 .abs [1, -2, 0, -7] == [1, 2, 0, 7]
#guard un .i8 (.shl 3) [1, -2, 0, 5] == [8, -16, 0, 40]
#guard un .i8 (.addi (-3)) [1, -2, 0, 5] == [-2, -5, -3, 2]
#guard un .i8 (.muli (-2)) [1, -2, 0, 5] == [-2, 4, 0, -10]
#guard un .i32 (.requant 1) [300, -300, 5, -5] == [127, -128, 2, -3]
#guard un .i8 (.shift 1) [1, 2, 3, 4] == [0, 1, 2, 3]
#guard un .i8 (.rotate 1) [1, 2, 3, 4] == [2, 3, 4, 1]
#guard un .i8 .reverse [1, 2, 3, 4] == [4, 3, 2, 1]
#guard un .i8 (.broadcast 2) [1, 2, 3, 4] == [3, 3, 3, 3]
#guard un .i8 (.permute [3, 3, 0]) [1, 2, 3, 4] == [4, 4, 1, 0]
#guard bin .i8 .and [12, -1, 0, 5] [10, 7, 9, 4] == [8, 7, 0, 4]
#guard bin .i8 .or [12, 0, 0, 5] [10, 7, 9, 2] == [14, 7, 9, 7]
#guard bin .i8 .xor [12, -1, 0, 5] [10, 0, 9, 5] == [6, -1, 9, 0]
#guard bin .i8 .lt [1, -2, 3, 3] [2, -3, 3, 4] == [1, 0, 0, 1]
#guard Value.toInts ((wordSem 4).sel .i8 (Value.ofInts .i8 [1, 0, -5, 0])
          (Value.ofInts .i8 [10, 20, 30, 40]) (Value.ofInts .i8 [1, 2, 3, 4])) == [10, 2, 30, 4]
#guard Value.toInts ((wordSem 4).const .i8 [7, -7]) == [7, -7, 0, 0]

/-! ## Types: the same operation at 8, 16 and 32 bits -/

-- Arithmetic wraps at the width of the type.
#guard bin .i8 .add [100, -100, 127, 1] [100, -100, 1, 1] == [-56, 56, -128, 2]
#guard bin .i16 .add [100, -100, 127, 1] [100, -100, 1, 1] == [200, -200, 128, 2]
#guard bin .i16 .mul [300, -300, 2, 256] [300, 2, -2, 256] == [24464, -600, -4, 0]
#guard bin .i32 .mul [300, -300, 2, 65536] [300, 2, -2, 65536] == [90000, -600, -4, 0]
#guard un .i8 .abs [-128, 127, 0, -1] == [-128, 127, 0, 1]

-- A value of 16 bits is two words and one of 32 bits four, the low byte of
-- every element first.
#guard ((Value.ofInts .i16 [258, -2] : Value 4).map Word.toInts) == [[2, -2, 0, 0], [1, -1, 0, 0]]
#guard (Value.ofInts .i32 [1, 2] : Value 4).length == 4

-- Rearranging the elements of a value does the same to each of its words.
#guard un .i32 (.rotate 1) [100000, -2, 3, 4] == [-2, 3, 4, 100000]
#guard un .i16 .reverse [1000, 2, 3, -1000] == [-1000, 3, 2, 1000]

-- `requant` gives a value of 8 bits whatever it takes, and `widen` keeps
-- the elements and their signs.
#guard ((wordSem 4).un .i32 (.requant 4) (Value.ofInts .i32 [1600, -1600, 100000, -1])).length == 1
#guard un .i32 (.requant 4) [1600, -1600, 100000, -1] == [100, -100, 127, -1]
#guard Value.toInts ((wordSem 4).un .i8 (.widen .i32) (Value.ofInts .i8 [5, -5, 127, -128]))
        == [5, -5, 127, -128]
#guard ((wordSem 4).un .i8 (.widen .i16) (Value.ofInts .i8 [5, -5, 127, -128])).map Word.toInts
        == [[5, -5, 127, -128], [0, -1, 0, -1]]

-- A product is a value of 32 bits: the rows and the word are read as signed
-- bytes.
#guard Value.toInts ((wordSem 4).matvec [Word.ofInts [100, 100, 100, 100], Word.ofInts [-1, 2, -3, 4]]
          (Word.ofInts [100, 100, 100, -100])) == [20000, -600, 0, 0]

/-! ## A machine for the programs below -/

def cfg : Config where
  kinds := [.mxm, .mem, .vxm, .mem]
  streams := 4
  lanes := 2
  bankSize := 8
  memDelay := 1
  vxmDelay := 1
  sxmDelay := 1
  mxmDelay := 1

def e (id : Nat) : Stream := ⟨.east, id⟩
def w (id : Nat) : Stream := ⟨.west, id⟩

def words (rows : List (List Int)) : List (Word 2) := rows.map Word.ofInts

/-- Run on both machines and return slice 3's memory, or `none` on a trap or
if the two machines disagree. -/
def run (prog : Program) (cycles : Nat) (image : List (List (Word 2))) (c : Config := cfg) :
    Option (List (List Int)) :=
  match execute (wordSem 2) c prog cycles image, cellExecute c prog cycles image with
  | .ok mem, .ok mem' =>
    if mem == mem' then some ((mem[3]?.getD []).map Word.toInts) else none
  | _, _ => none

/-- Run on both machines and return the trap, or `none` if there is none or
the two machines disagree. -/
def trapOn (c : Config) (prog : Program) (cycles : Nat) (image : List (List (Word 2))) :
    Option Trap :=
  match execute (wordSem 2) c prog cycles image, cellExecute c prog cycles image with
  | .error t, .error t' => if t = t' then some t else none
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

/-! ## Installed words: install once, multiply twice -/

/-- Slice 1 holds row 0 of a matrix and two vectors, and slice 3 holds row 1.
The two rows are read so as to reach the matrix slice together, on two
streams side by side, and one `install` takes both. Each vector is then
multiplied, one cycle after the other. A product is a value of 32 bits on
the four streams going east; its low word is written to slice 3. -/
def twice : Program :=
  [ -- row 1 from slice 3 and row 0 from slice 1 both arrive on cycle 5
    .once 3 0 (.read 0 (w 1)),
    .once 1 2 (.read 0 (w 0)),
    .once 0 5 (.install 0 2 (w 0)),
    -- the vectors arrive on cycles 6 and 7
    { slice := 1, time := 3, instr := .read 1 (w 0), repeats := 1, stride := 1 },
    { slice := 0, time := 6, instr := .product 2 (w 0) (e 0), repeats := 1 },
    -- a product leaves slice 0 one cycle after it is computed and takes four
    -- more to reach slice 3
    { slice := 3, time := 11, instr := .write (e 0) 1, repeats := 1, stride := 1 } ]

def twiceImage : List (List (Word 2)) :=
  [[], words [[1, 2], [10, 20], [1, 1]], [], words [[3, 4], [0, 0], [0, 0]]]

-- The matrix with rows (1, 2) and (3, 4). Times (10, 20) is (50, 110).
-- Times (1, 1) is (3, 7). The low word of each product is written.
#guard run twice 13 twiceImage == some [[3, 4], [50, 110], [3, 7]]

-- A product with the first row only: element 1 of it is zero.
#guard run (twice.map fun i =>
          match i.instr with
          | .product _ src dst => { i with instr := .product 1 src dst }
          | _ => i) 13 twiceImage
        == some [[3, 4], [50, 0], [3, 0]]

-- The slice has two installed words: there is no third to install or to
-- multiply by.
#guard trapOn cfg [.once 1 0 (.read 0 (w 0)), .once 0 3 (.install 2 1 (w 0))] 4 twiceImage
        == some ⟨.badAddress, 0, 3⟩
#guard trapOn cfg [.once 1 0 (.read 0 (w 0)), .once 0 3 (.product 3 (w 0) (e 0))] 4 twiceImage
        == some ⟨.badAddress, 0, 3⟩

-- An `install` of two words finds the second stream empty.
#guard trapOn cfg [.once 1 0 (.read 0 (w 0)), .once 0 3 (.install 0 2 (w 0))] 4 twiceImage
        == some ⟨.emptyRead, 0, 3⟩

/-! ## A delay of its own: a slow multiply -/

/-- The machine above, with a multiply that takes three cycles. -/
def slowMul : Config := { cfg with delays := [("mul", 3)] }

/-- Slice 1 holds `a` and slice 3 holds `b`; each sends its word to slice 2
on cycles 0 and 1, and the two arrive together on cycles 3 and 4. Slice 2
multiplies on cycle 3 and adds on cycle 4. The add takes one cycle and the
multiply three, so the sum reaches slice 3 on cycle 7, before the product,
which arrives on cycle 8. -/
def mulThenAdd : Program :=
  [ { slice := 1, time := 0, instr := .read 0 (e 0), repeats := 1 },
    { slice := 3, time := 0, instr := .read 0 (w 0), repeats := 1 },
    .once 2 3 (.bin .i8 .mul (e 0) (w 0) (e 0)),
    .once 2 4 (.bin .i8 .add (e 0) (w 0) (e 0)),
    .once 3 7 (.write (e 0) 1),
    .once 3 8 (.write (e 0) 0) ]

def abImage : List (List (Word 2)) := [[], words [[2, 3]], [], words [[5, 7], [0, 0]]]

#guard run mulThenAdd 9 abImage slowMul == some [[10, 21], [7, 10]]

-- With a multiply of one cycle the product arrives on cycle 6, and the write
-- on cycle 8 finds the stream empty.
#guard trapOn cfg mulThenAdd 9 abImage == some ⟨.emptyRead, 3, 8⟩

/-- A multiply on cycle 3 and an add on cycle 5 would both leave slice 2 on
cycle 6 (Machine 3.4), even though they are for different streams. -/
def clashing : Program :=
  [ { slice := 1, time := 0, instr := .read 0 (e 0), repeats := 1, gap := 1 },
    { slice := 3, time := 0, instr := .read 0 (w 0), repeats := 1, gap := 1 },
    .once 2 3 (.bin .i8 .mul (e 0) (w 0) (e 0)),
    .once 2 5 (.bin .i8 .add (e 0) (w 0) (e 1)) ]

#guard trapOn slowMul clashing 9 abImage == some ⟨.twoResults, 2, 5⟩

-- With a multiply of one cycle they leave on cycles 4 and 6.
#guard trapOn cfg clashing 9 abImage == none


/-! ## Values on streams that follow one another -/

/-- The vector slice makes a value of 16 bits with the elements 258 and -2,
on streams 0 and 1 going east, where it finds it again two cycles later. It
negates the value, given the stream `src` as the first of the two, to
streams 2 and 3. The low word of the result passes slice 3 on cycle 5. -/
def wide (src : Stream) : Program :=
  [ .once 2 0 (.const .i16 [258, -2] (e 0)),
    .once 2 2 (.un .i16 .neg src (e 2)),
    .once 3 5 (.write (e 2) 0) ]

def wideImage : List (List (Word 2)) :=
  [[], words [[7, 7]], [], words [[0, 0]]]

-- The low word of -258 and of 2.
#guard run (wide (e 0)) 6 wideImage == some [[-2, 2]]

-- A value of two words starts on a stream with an even number, and one of
-- four words on a stream whose number is a multiple of four.
#guard trapOn cfg (wide (e 1)) 6 wideImage == some ⟨.badStream, 2, 2⟩
#guard trapOn cfg [.once 2 0 (.const .i16 [1] (e 1))] 2 wideImage == some ⟨.badStream, 2, 0⟩
#guard trapOn cfg [.once 2 0 (.const .i32 [1] (e 2))] 2 wideImage == some ⟨.badStream, 2, 0⟩
#guard trapOn cfg [.once 2 0 (.const .i32 [1] (e 0))] 2 wideImage == none

-- A word from memory is one word: an instruction that takes it as the low
-- word of a value finds the next stream empty.
#guard trapOn cfg [.once 1 0 (.read 0 (e 0)), .once 2 3 (.un .i16 .neg (e 0) (e 2))] 4 wideImage
        == some ⟨.emptyRead, 2, 3⟩

/-! ## Two banks: a read and a write on one cycle -/

/-- The machine above, with two words in the lower bank of each memory. -/
def banked : Config := { cfg with bankSize := 2 }

/-- Slice 1 sends the word at its address 0 east. It reaches slice 3 on cycle
4. On that cycle slice 3 writes it at address `a` and reads its own address 0
for a stream going west, which slice 1 writes at its address 1 on cycle 8. -/
def swap (a : Nat) : Program :=
  [ .once 1 0 (.read 0 (e 0)),
    .once 3 4 (.write (e 0) a),
    .once 3 4 (.read 0 (w 0)),
    .once 1 8 (.write (w 0) 1) ]

def swapImage : List (List (Word 2)) :=
  [[], words [[1, 2], [0, 0]], [], words [[5, 6], [0, 0], [0, 0]]]

/-- The memories of slices 1 and 3 after a run on both machines. -/
def run13 (prog : Program) (c : Config) : Option (List (List Int) × List (List Int)) :=
  match execute (wordSem 2) c prog 9 swapImage, cellExecute c prog 9 swapImage with
  | .ok mem, .ok mem' =>
    if mem == mem' then
      some ((mem[1]?.getD []).map Word.toInts, (mem[3]?.getD []).map Word.toInts)
    else none
  | _, _ => none

-- Address 2 is in the upper bank and address 0 in the lower: both run.
#guard run13 (swap 2) banked == some ([[1, 2], [5, 6]], [[5, 6], [0, 0], [1, 2]])

-- The order the two are listed in does not matter.
#guard run13 (swap 2).reverse banked == some ([[1, 2], [5, 6]], [[5, 6], [0, 0], [1, 2]])

-- Address 1 is in the lower bank, as address 0 is.
#guard trapOn banked (swap 1) 9 swapImage == some ⟨.sameBank, 3, 4⟩

-- With eight words in the lower bank, address 2 is in it too.
#guard trapOn cfg (swap 2) 9 swapImage == some ⟨.sameBank, 3, 4⟩

-- Two reads on one cycle are one too many, whatever their banks.
#guard trapOn banked [.once 3 0 (.read 0 (w 0)), .once 3 0 (.read 2 (w 1))] 2 swapImage
        == some ⟨.twoInstructions, 3, 0⟩

-- So is a read and a write with a third instruction.
#guard trapOn banked (swap 2 ++ [.once 3 4 (.read 1 (w 1))]) 9 swapImage
        == some ⟨.twoInstructions, 3, 4⟩

-- Both words are issued on cycle 4: the one read and the one written.
#guard ((issues (wordSem 2) banked (swap 2) 9 swapImage).filter (·.time == 4)).map
        (fun x => (x.slice, x.addr, x.word.toInts)) == [(3, none, [5, 6]), (3, some 2, [1, 2])]

/-! ## A buffer dealt out over two memories -/

/-- The buffer of Compiler 3: five words with the parts (slice 2, address 0)
and (slice 3, address 4). Buffer 1 is one word of slice 2, after it. -/
def dealt : MemMap := [⟨[⟨2, 0⟩, ⟨3, 4⟩], 5⟩, .one 2 3 1]

#guard (List.range 5).map (Placement.locate ⟨[⟨2, 0⟩, ⟨3, 4⟩], 5⟩ ·) ==
        [some (2, 0), some (3, 4), some (2, 1), some (3, 5), some (2, 2)]

-- Loading the buffers puts each word where the map says, and reading them
-- back gives the buffers.
#guard image dealt [0, 0, 4, 6] (fun b k => (10 * b + k : Nat)) 99 ==
        [[], [], [0, 2, 4, 10], [99, 99, 99, 99, 1, 3]]
#guard extract dealt (image dealt [0, 0, 4, 6] (fun b k => (10 * b + k : Nat)) 99) 99 ==
        [[0, 1, 2, 3, 4], [10]]

-- An address past the last word of a part belongs to no buffer.
#guard MemMap.findFrom 3 6 0 dealt == none
#guard MemMap.findFrom 3 5 0 dealt == some (0, 3)
#guard MemMap.findFrom 2 3 0 dealt == some (1, 0)

end TauTest.Features
