import Tau.Check.Passes
import Tau.Isa.Encode
import Tau.Passes.Unroll

/-!
# Test: pins, calls and the image

Small checks of the three things the flow has beyond buffers: a pinned
operation and the event it makes, a kernel called from another, and a program
written as numbers and read back.
-/

namespace TauTest.Pins

open Tau

/-! ## A pinned kernel and a program that meets its pin -/

/-- Memory, vector, memory, with one stream each way. -/
def machine : Config where
  kinds := [.mem, .vxm, .mem]
  streams := 1
  memDelay := 1
  vxmDelay := 1
  sxmDelay := 1
  mxmDelay := 1

/-- `y[0] = relu x[0]`, with the relu pinned to cycle `t`. -/
def reluAt (t : Nat) : Kernel :=
  [ .stmt (.load 0 0 ⟨0, 0⟩),
    .stmt (.pin ⟨t, 0⟩ (.un 1 .relu 0)),
    .stmt (.store 1 1 ⟨0, 0⟩) ]

def east : Track := ⟨.east, 0⟩

/-- Read at cycle `t`, relu three cycles later, write three cycles after
that: the timing rule with a delay of 1 and a distance of 1. -/
def compiled (t : Nat) : Compiled where
  cfg := machine
  memSizes := [1, 0, 1]
  map := [⟨0, 0, 1⟩, ⟨2, 0, 1⟩]
  prog := [ .once 0 t (.read 0 east), .once 1 (t + 3) (.un .relu east east),
            .once 2 (t + 6) (.write east 0) ]
  cycles := t + 7

-- The kernel's one event: the relu of the word, on cycle 3.
#guard kernelEvents (reluAt 3) [1, 1] == [⟨3, none, .un .relu (.init 0 0)⟩]

-- The machine issues three words: what it read, the relu, and the store.
#guard machineEvents (compiled 0) ==
  [ ⟨0, none, .init 0 0⟩, ⟨3, none, .un .relu (.init 0 0)⟩,
    ⟨6, some (1, 0), .un .relu (.init 0 0)⟩ ]

-- The program that starts on cycle 0 has its relu on cycle 3.
#guard check (Source.ofKernel (reluAt 3)) [1, 1] (compiled 0)

-- The same program one cycle late computes the same buffers and misses the
-- pin. Without the pin it is accepted.
#guard !check (Source.ofKernel (reluAt 3)) [1, 1] (compiled 1)
#guard check (Source.ofKernel (reluAt 4)) [1, 1] (compiled 1)
#guard checkKernels (reluAt 3) (reluAt 3) [1, 1]
#guard !checkKernels (reluAt 3) (reluAt 4) [1, 1]

-- Between two compiled programs every instruction counts as pinned.
#guard checkRouted (compiled 0) (compiled 0)
#guard !checkRouted (compiled 0) (compiled 1)

-- A pin on a store claims the cycle of the write.
def storeAt (t : Nat) : Kernel :=
  [ .stmt (.load 0 0 ⟨0, 0⟩),
    .stmt (.un 1 .relu 0),
    .stmt (.pin ⟨t, 0⟩ (.store 1 1 ⟨0, 0⟩)) ]

#guard check (Source.ofKernel (storeAt 6)) [1, 1] (compiled 0)
#guard !check (Source.ofKernel (storeAt 3)) [1, 1] (compiled 0)

-- In a loop a pin moves with the iteration, and unrolling fills it in.
def paced : Kernel :=
  [ .loop 3 [ .load 0 0 ⟨0, 1⟩, .pin ⟨5, 4⟩ (.un 1 .relu 0), .store 1 1 ⟨0, 1⟩ ] ]

#guard (kernelEvents paced [3, 3]).map (·.time) == [13, 9, 5]
#guard checkKernels paced ((Kernel.unroll paced).map Item.stmt) [3, 3]

/-! ## A kernel called from another -/

/-- `b1[0] = relu b0[0]`, pinned to cycle 3 of the kernel. -/
def callee : Source := Source.ofKernel (reluAt 3)

/-- Call it on buffers 0 and 2 from cycle 0, then on buffers 2 and 1 from
cycle 10. -/
def twice : Source :=
  .call callee [0, 2] 0 (.call callee [2, 1] 10 .done)

/-- The same with the calls copied in. -/
def twiceInlined : Kernel :=
  [ .stmt (.load 0 0 ⟨0, 0⟩),
    .stmt (.pin ⟨3, 0⟩ (.un 1 .relu 0)),
    .stmt (.store 1 2 ⟨0, 0⟩),
    .stmt (.load 2 2 ⟨0, 0⟩),
    .stmt (.pin ⟨13, 0⟩ (.un 3 .relu 2)),
    .stmt (.store 3 1 ⟨0, 0⟩) ]

#guard checkInlined twice twiceInlined [1, 1, 1]

-- The second call's pin counts from cycle 10.
#guard (sourceEvents twice [1, 1, 1]).map (·.time) == [13, 3]

-- A copy that forgets to move the pin is rejected.
#guard !checkInlined twice
  (twiceInlined.set 4 (.stmt (.pin ⟨3, 0⟩ (.un 3 .relu 2)))) [1, 1, 1]

-- A call that passes one buffer twice has no meaning.
#guard (sourceExprs (.call callee [0, 0] 0 .done) [1, 1]).isNone

/-! ## The image -/

def prog : Program :=
  [ { slice := 2, time := 6, instr := .write east 0 },
    { slice := 0, time := 0, instr := .read 0 east, repeats := 3, gap := 1, stride := 1 },
    { slice := 1, time := 3, instr := .un (.permute [1, 0]) east ⟨.west, 2⟩ },
    { slice := 1, time := 5, instr := .const [3, -4] east },
    { slice := 1, time := 7, instr := .un (.addi (-2)) east east } ]

-- One list of numbers per slice: how many entries, then each.
#guard prog.encode 3 ==
  [ [1, 0, 3, 1, 1, 0, 0, 0],
    [3, 3, 0, 0, 0, 2, 0, 5, 11, 2, 1, 0,
        5, 0, 0, 0, 7, 0, 2, 6, 7,
        7, 0, 0, 0, 2, 0, 0, 5, 3],
    [1, 6, 0, 0, 0, 1, 0, 0] ]

-- Read back, it is the program again, slice by slice.
#guard Image.decode (prog.encode 3) ==
  some (prog.entriesOf 0 ++ prog.entriesOf 1 ++ prog.entriesOf 2)

-- An image with a number missing is not well formed.
#guard (Image.decode [[1, 0, 3, 1, 1, 0, 0]]).isNone

end TauTest.Pins
