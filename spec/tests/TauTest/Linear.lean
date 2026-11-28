import Tau.Machine.SliceLevel
import Tau.Check.Passes
import Tau.IR.Unroll
import Tau.Tools.Run
import Tau.Machine.CellLevel

/-!
# Test: a quantized linear layer, scheduled by hand

Computes `y = relu (requant (W * x + b))` with two lanes on a nine-slice machine.
`x`, `b` and the rows of `W` are values of 8 bits, the product is one of 32
bits, on four streams, and `b` is widened to 32 bits to be added to it. The
schedule below was worked out by hand from the timing rule in
`Tau.Machine.SliceLevel`.
-/

namespace TauTest.Linear

open Tau

/-- Positions 0 to 8: matrix, rearrangement, two memories, vector, two
memories, rearrangement, matrix. -/
def cfg : Config where
  kinds := [.mxm, .sxm, .mem, .mem, .vxm, .mem, .mem, .sxm, .mxm]
  streams := 4
  lanes := 2
  bankSize := 8
  memDelay := 1
  vxmDelay := 1
  sxmDelay := 1
  mxmDelay := 2

def e (id : Nat) : Stream := ⟨.east, id⟩
def w (id : Nat) : Stream := ⟨.west, id⟩

/-- Slice 2 holds `x` at address 0 and `b` at address 1. Slice 3 holds the two
rows of `W`. Slice 5 receives `y` at address 0. -/
def image : List (List (Word 2)) :=
  [[], [],
   [Word.ofInts [3, -2], Word.ofInts [10, -20]],
   [Word.ofInts [1, 2], Word.ofInts [3, 4]],
   [],
   [Word.zero],
   [], [], []]

def prog : Program :=
  [ -- the rows of W leave slice 3 on consecutive cycles and are installed
    -- in the matrix slice on cycles 5 and 6
    .once 3 0 (.read 0 (w 1)),
    .once 3 1 (.read 1 (w 1)),
    .once 0 5 (.install 0 1 (w 1)),
    .once 0 6 (.install 1 1 (w 1)),
    -- x leaves slice 2 going west and reaches the matrix slice at cycle 7
    .once 2 3 (.read 0 (w 0)),
    -- W * x leaves the matrix slice going east, on streams 0 to 3, and
    -- reaches slice 4 at cycle 14
    .once 0 7 (.product 2 (w 0) (e 0)),
    -- b reaches slice 4 at cycle 12 and is widened to 32 bits, on the four
    -- streams going west, where the vector slice finds it at cycle 14
    .once 2 8 (.read 1 (e 0)),
    .once 4 12 (.un .i8 (.widen .i32) (e 0) (w 0)),
    .once 4 14 (.bin .i32 .add (e 0) (w 0) (e 0)),
    .once 4 16 (.un .i32 (.requant 0) (e 0) (e 0)),
    .once 4 18 (.un .i8 .relu (e 0) (e 0)),
    -- the result moves one slice east and is stored
    .once 5 21 (.write (e 0) 0) ]

/-- The word stored at slice 5, address 0, or `none` if the machine trapped. -/
def result (prog : Program) : Option (List Int) :=
  match execute (wordSem 2) cfg prog 22 image with
  | .error _ => none
  | .ok mem => some ((mem[5]?.getD [])[0]?.getD Word.zero).toInts

-- W * x = (-1, 1); adding b gives (9, -19); relu gives (9, 0).
#guard result prog == some [9, 0]

/-- Issuing the add one cycle early reads empty slots. -/
def early : Program :=
  prog.map fun i => if i.slice = 4 ∧ i.time = 14 then { i with time := 13 } else i

#guard result early == none

/-! ## The same layer as a kernel, and the checker's verdict -/

/-- Buffers: 0 is `x`, 1 is `b`, 2 is `W` (two rows), 3 is `y`. -/
def kernel : Kernel :=
  [ .stmt (.load 0 .i8 0 ⟨0, 0⟩),
    .stmt (.matvec 1 0 2 ⟨0, 0⟩ 2),
    .stmt (.load 2 .i8 1 ⟨0, 0⟩),
    .stmt (.un 3 .i8 (.widen .i32) 2),
    .stmt (.bin 4 .i32 .add 1 3),
    .stmt (.un 5 .i32 (.requant 0) 4),
    .stmt (.un 6 .i8 .relu 5),
    .stmt (.store 6 .i8 3 ⟨0, 0⟩) ]

def sizes : List Nat := [1, 1, 2, 1]

def compiled (prog : Program) : Compiled where
  cfg := cfg
  memSizes := [0, 0, 2, 2, 0, 1, 0, 0, 0]
  map := [.one 2 0 1, .one 2 1 1, .one 3 0 2, .one 5 0 1]
  prog := prog
  cycles := 22

-- The hand-written schedule is accepted.
#guard check (Source.ofKernel kernel) sizes (compiled prog)

-- The schedule with the add one cycle early is rejected.
#guard !check (Source.ofKernel kernel) sizes (compiled early)

-- A schedule that feeds the rows of W in the wrong order runs without a
-- trap but computes something else, and is rejected.
def swapped : Program :=
  prog.map fun i =>
    if i.slice = 3 ∧ i.time = 0 then { i with instr := .read 1 (w 1) }
    else if i.slice = 3 ∧ i.time = 1 then { i with instr := .read 0 (w 1) }
    else i

#guard (result swapped).isSome
#guard !check (Source.ofKernel kernel) sizes (compiled swapped)

-- The kernel run directly on real words gives the same answer as the machine.
#guard (kernel.run (wordSem 2)
          [[Word.ofInts [3, -2]], [Word.ofInts [10, -20]],
           [Word.ofInts [1, 2], Word.ofInts [3, 4]], [Word.zero]]).map
        (fun bufs => ((bufs[3]?.getD [])[0]?.getD Word.zero).toInts) == some [9, 0]

/-! ## Checking the earlier compiler stages -/

-- Unrolling: the kernel against its unrolled form.
#guard checkKernels kernel (kernel.unroll.map Item.stmt) sizes

-- The comparison the examples script makes between the compiler's unrolled
-- kernel and the Lean model's: equal up to the numbering of values.
#guard Tools.sameUnroll
  [.loop 2 [.load 0 .i8 0 ⟨0, 1⟩, .un 1 .i8 .relu 0, .store 1 .i8 1 ⟨0, 1⟩]]
  [.stmt (.load 0 .i8 0 ⟨0, 0⟩), .stmt (.un 1 .i8 .relu 0), .stmt (.store 1 .i8 1 ⟨0, 0⟩),
   .stmt (.load 2 .i8 0 ⟨1, 0⟩), .stmt (.un 3 .i8 .relu 2), .stmt (.store 3 .i8 1 ⟨1, 0⟩)]
#guard !Tools.sameUnroll
  [.loop 2 [.load 0 .i8 0 ⟨0, 1⟩, .un 1 .i8 .relu 0, .store 1 .i8 1 ⟨0, 1⟩]]
  [.stmt (.load 0 .i8 0 ⟨0, 0⟩), .stmt (.un 1 .i8 .relu 0), .stmt (.store 1 .i8 1 ⟨0, 0⟩),
   .stmt (.load 2 .i8 0 ⟨1, 0⟩), .stmt (.un 3 .i8 .relu 2), .stmt (.store 1 .i8 1 ⟨1, 0⟩)]

-- A kernel that stores the wrong value is rejected.
#guard !checkKernels kernel (kernel.take 7 ++ [.stmt (.store 5 .i8 3 ⟨0, 0⟩)]) sizes

/-- The same layer after placement: instructions in order, with slices but no
cycles and no streams. -/
def placed : Placed where
  cfg := cfg
  memSizes := [0, 0, 2, 2, 0, 1, 0, 0, 0]
  map := [.one 2 0 1, .one 2 1 1, .one 3 0 2, .one 5 0 1]
  instrs :=
    [ (3, .read 0 0), (0, .install 0 [0]),
      (3, .read 1 1), (0, .install 1 [1]),
      (2, .read 2 0),
      (0, .product [3, 4, 5, 6] 2 2),
      (2, .read 7 1),
      (4, .un [8, 9, 10, 11] .i8 (.widen .i32) [7]),
      (4, .bin [12, 13, 14, 15] .i32 .add [3, 4, 5, 6] [8, 9, 10, 11]),
      (4, .un [16] .i32 (.requant 0) [12, 13, 14, 15]),
      (4, .un [17] .i8 .relu [16]),
      (5, .write 17 0) ]

#guard checkPlaced kernel sizes placed

-- Sending the add to a memory slice is rejected.
#guard !checkPlaced kernel sizes
  { placed with instrs := placed.instrs.map fun (p, i) =>
      match i with
      | .bin .. => (3, i)
      | _ => (p, i) }

-- Scheduling: the hand-written schedule against the placed program. The two
-- keep their buffers at different addresses, which the check does not mind.
#guard checkScheduled placed (compiled prog)

-- A schedule that issues an instruction too early is rejected.
#guard !checkScheduled placed (compiled early)

-- Routing: a program against itself, and against one that computes
-- something else.
#guard checkRouted (compiled prog) (compiled prog)
#guard !checkRouted (compiled prog) (compiled swapped)

/-! ## The cell-level machine gives the same answers -/

#guard (cellExecute cfg prog 22 image).toOption == (execute (wordSem 2) cfg prog 22 image).toOption
#guard (cellExecute cfg early 22 image).toOption.isNone

end TauTest.Linear
