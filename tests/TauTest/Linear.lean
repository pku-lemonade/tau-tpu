import Tau.SliceLevel.Machine
import Tau.Check.Stages
import Tau.Passes.Unroll
import Tau.CellLevel.Machine

/-!
# Test: a quantized linear layer, scheduled by hand

Computes `y = relu (requant (W * x + b))` with two lanes on a nine-slice chip.
The schedule below was worked out by hand from the timing rule in
`Tau/SliceLevel/Machine.lean`.
-/

namespace TauTest.Linear

open Tau

/-- Positions 0 to 8: matrix, rearrangement, two memories, vector, two
memories, rearrangement, matrix. -/
def cfg : Config where
  kinds := [.mxm, .sxm, .mem, .mem, .vxm, .mem, .mem, .sxm, .mxm]
  streams := 4
  memDelay := 1
  vxmDelay := 1
  sxmDelay := 1
  mxmDelay := 2

def e (id : Nat) : Track := ⟨.east, id⟩
def w (id : Nat) : Track := ⟨.west, id⟩

/-- Slice 2 holds `x` at address 0 and `b` at address 1. Slice 3 holds the two
columns of `W`. Slice 5 receives `y` at address 0. -/
def image : List (List (Word 2)) :=
  [[], [],
   [Word.ofInts [3, -2], Word.ofInts [10, -20]],
   [Word.ofInts [1, 3], Word.ofInts [2, 4]],
   [],
   [Word.zero],
   [], [], []]

def prog : Program :=
  [ -- x leaves slice 2 going west and reaches the matrix slice at cycle 4
    ⟨2, 0, .read 0 (w 0)⟩,
    ⟨0, 4, .load (w 0)⟩,
    -- the columns of W leave slice 3 on consecutive cycles
    ⟨3, 0, .read 0 (w 1)⟩,
    ⟨3, 1, .read 1 (w 1)⟩,
    ⟨0, 5, .mac 0 (w 1)⟩,
    ⟨0, 6, .mac 1 (w 1)⟩,
    -- W * x leaves the matrix slice going east and reaches slice 4 at cycle 14
    ⟨0, 7, .emit (e 0)⟩,
    -- b is timed to arrive at slice 4 on the same cycle
    ⟨2, 10, .read 1 (e 1)⟩,
    ⟨4, 14, .bin .add (e 0) (e 1) (e 0)⟩,
    ⟨4, 16, .un (.requant 0) (e 0) (e 0)⟩,
    ⟨4, 18, .un .relu (e 0) (e 0)⟩,
    -- the result moves one slice east and is stored
    ⟨5, 21, .write (e 0) 0⟩ ]

/-- The word stored at slice 5, address 0, or `none` if the machine trapped. -/
def result (prog : Program) : Option (List Int) :=
  match execute (wordSem 2) cfg prog 22 image with
  | .error _ => none
  | .ok mem => some ((mem[5]?.getD [])[0]?.getD Word.zero).toInts

-- W * x = (-1, 1); adding b gives (9, -19); relu gives (9, 0).
#guard result prog == some [9, 0]

/-- Issuing the add one cycle early reads an empty slot. -/
def early : Program :=
  prog.map fun i => if i.slice = 4 ∧ i.time = 14 then { i with time := 13 } else i

#guard result early == none

/-! ## The same layer as a kernel, and the checker's verdict -/

/-- Buffers: 0 is `x`, 1 is `b`, 2 is `W` (two columns), 3 is `y`. -/
def kernel : Kernel :=
  [ .stmt (.load 0 0 ⟨0, 0⟩),
    .stmt (.matvec 1 0 2 ⟨0, 0⟩ 2),
    .stmt (.load 2 1 ⟨0, 0⟩),
    .stmt (.bin 3 .add 1 2),
    .stmt (.un 4 (.requant 0) 3),
    .stmt (.un 5 .relu 4),
    .stmt (.store 5 3 ⟨0, 0⟩) ]

def sizes : List Nat := [1, 1, 2, 1]

def compiled (prog : Program) : Compiled where
  cfg := cfg
  memSizes := [0, 0, 2, 2, 0, 1, 0, 0, 0]
  map := [⟨2, 0, 1⟩, ⟨2, 1, 1⟩, ⟨3, 0, 2⟩, ⟨5, 0, 1⟩]
  prog := prog
  cycles := 22

-- The hand-written schedule is accepted.
#guard check kernel sizes (compiled prog)

-- The schedule with the add one cycle early is rejected.
#guard !check kernel sizes (compiled early)

-- A schedule that feeds the columns of W in the wrong order runs without a
-- trap but computes something else, and is rejected.
def swapped : Program :=
  prog.map fun i =>
    if i.slice = 3 ∧ i.time = 0 then { i with instr := .read 1 (w 1) }
    else if i.slice = 3 ∧ i.time = 1 then { i with instr := .read 0 (w 1) }
    else i

#guard (result swapped).isSome
#guard !check kernel sizes (compiled swapped)

-- The kernel run directly on real words gives the same answer as the machine.
#guard (kernel.run (wordSem 2)
          [[Word.ofInts [3, -2]], [Word.ofInts [10, -20]],
           [Word.ofInts [1, 3], Word.ofInts [2, 4]], [Word.zero]]).map
        (fun bufs => ((bufs[3]?.getD [])[0]?.getD Word.zero).toInts) == some [9, 0]

/-! ## Checking the earlier compiler stages -/

-- Unrolling: the kernel against its unrolled form.
#guard checkKernels kernel (kernel.unroll.map Item.stmt) sizes

-- A kernel that stores the wrong value is rejected.
#guard !checkKernels kernel (kernel.take 5 ++ [.stmt (.store 3 3 ⟨0, 0⟩)]) sizes

/-- The same layer after placement: instructions in order, with slices but no
cycles and no streams. -/
def placed : Placed where
  cfg := cfg
  memSizes := [0, 0, 2, 2, 0, 1, 0, 0, 0]
  map := [⟨2, 0, 1⟩, ⟨2, 1, 1⟩, ⟨3, 0, 2⟩, ⟨5, 0, 1⟩]
  instrs :=
    [ (2, .read 0 0), (0, .load 0),
      (3, .read 1 0), (0, .mac 0 1),
      (3, .read 2 1), (0, .mac 1 2),
      (0, .emit 3),
      (2, .read 4 1),
      (4, .bin 5 .add 3 4),
      (4, .un 6 (.requant 0) 5),
      (4, .un 7 .relu 6),
      (5, .write 7 0) ]

#guard checkPlaced kernel sizes placed

-- Sending the add to a memory slice is rejected.
#guard !checkPlaced kernel sizes
  { placed with instrs := placed.instrs.map fun (p, i) =>
      match i with
      | .bin .. => (3, i)
      | _ => (p, i) }

/-! ## The cell-level machine gives the same answers -/

#guard (cellExecute cfg prog 22 image).toOption == (execute (wordSem 2) cfg prog 22 image).toOption
#guard (cellExecute cfg early 22 image).toOption.isNone

end TauTest.Linear
