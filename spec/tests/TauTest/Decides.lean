import Tau.Check.Decides

/-!
# Test: what each back-end pass decides

One kernel, taken by hand through placing, scheduling and routing, on a
machine of four slices. Each output is accepted by the check of its pass and
keeps the rule of its pass (`Tau.Check.Decides`). Then, for each rule, an
output that the check still accepts and the rule does not: it computes the
same buffers by doing another pass's work.

The kernel computes one word and stores it twice, so its word has two
readers. In the schedule both take it from the stream, one cycle apart,
without a copy in memory (Machine 3.2).
-/

namespace TauTest.Decides

open Tau

def cfg (streams : Nat) : Config where
  kinds := [.mem, .vxm, .mem, .mem]
  streams := streams
  lanes := 2
  bankSize := 8
  memDelay := 1
  vxmDelay := 1
  sxmDelay := 1
  mxmDelay := 1

def e (id : Nat) : Stream := ⟨.east, id⟩

/-- `y[0] = z[0] = relu x[0]`. -/
def kernel : Kernel :=
  [ .stmt (.load 0 .i8 0 ⟨0, 0⟩),
    .stmt (.un 1 .i8 .relu 0),
    .stmt (.store 1 .i8 1 ⟨0, 0⟩),
    .stmt (.store 1 .i8 2 ⟨0, 0⟩) ]

def sizes : List Nat := [1, 1, 1]

/-- `x` in slice 0, `y` in slice 2, `z` in slice 3. -/
def map : MemMap := [.one 0 0 1, .one 2 0 1, .one 3 0 1]

/-! ## Place -/

def placed : Placed where
  cfg := cfg 1
  memSizes := [1, 0, 1, 1]
  map := map
  instrs := [(0, .read 0 0), (1, .un [1] .i8 .relu [0]), (2, .write 1 0), (3, .write 1 0)]

#guard checkPlaced kernel sizes placed
#guard placeOnly kernel placed

/-- The same, but the result waits in a scratch word of slice 2 before it is
stored to `z`. That is a decision about time, and not for `tau-place`. -/
def placedWaiting : Placed where
  cfg := cfg 1
  memSizes := [1, 0, 2, 1]
  map := map
  instrs :=
    [(0, .read 0 0), (1, .un [1] .i8 .relu [0]), (2, .write 1 0), (2, .write 1 1), (2, .read 2 1),
     (3, .write 2 0)]

#guard checkPlaced kernel sizes placedWaiting
#guard !placedWaiting.noScratch
#guard !placeOnly kernel placedWaiting

/-- The same as `placed`, with a relu that nothing uses. -/
def placedTwice : Placed :=
  { placed with instrs := placed.instrs ++ [(1, .un [2] .i8 .relu [0])] }

#guard checkPlaced kernel sizes placedTwice
#guard !sameOperations kernel placedTwice

/-! ## Schedule -/

/-- The read on cycle 0 reaches slice 1 on cycle 3. The relu's word is at
slice 2 on cycle 6 and at slice 3 on cycle 7, and each writes it. -/
def scheduled : Compiled where
  cfg := cfg 2
  memSizes := [1, 0, 1, 1]
  map := map
  prog :=
    [ .once 0 0 (.read 0 (e 0)),
      .once 1 3 (.un .i8 .relu (e 0) (e 1)),
      .once 2 6 (.write (e 1) 0),
      .once 3 7 (.write (e 1) 0) ]
  cycles := 8

#guard checkScheduled placed scheduled
#guard scheduleOnly placed scheduled

/-- A later store to `z`: the word waits in a scratch word of slice 2, and
`x` is read a second time, for nothing. Both are for `tau-schedule` to
decide. -/
def scheduledWaiting : Compiled where
  cfg := cfg 4
  memSizes := [1, 0, 2, 1]
  map := map
  prog :=
    [ .once 0 0 (.read 0 (e 0)),
      .once 0 1 (.read 0 (e 3)),
      .once 1 3 (.un .i8 .relu (e 0) (e 1)),
      .once 2 6 (.write (e 1) 0),
      -- the same word again, into scratch on cycle 7, out on cycle 8
      .once 1 4 (.un .i8 .relu (e 3) (e 3)),
      .once 2 7 (.write (e 3) 1),
      .once 2 8 (.read 1 (e 2)),
      .once 3 11 (.write (e 2) 0) ]
  cycles := 12

-- It is right, and it runs relu twice, which is one operation more than the
-- placed program has.
#guard checkScheduled placed scheduledWaiting
#guard !scheduleOnly placed scheduledWaiting

/-- The same with one relu: its word goes to `y` from the stream and to `z`
through the scratch word. -/
def scheduledOnce : Compiled :=
  { scheduledWaiting with
    prog :=
      [ .once 0 0 (.read 0 (e 0)),
        .once 0 1 (.read 0 (e 3)),
        .once 1 3 (.un .i8 .relu (e 0) (e 1)),
        .once 2 6 (.write (e 1) 1),
        .once 2 7 (.read 1 (e 2)),
        .once 2 9 (.write (e 2) 0),
        .once 2 10 (.read 1 (e 0)),
        .once 3 13 (.write (e 0) 0) ]
    cycles := 14 }

#guard checkScheduled placed scheduledOnce
#guard scheduleOnly placed scheduledOnce

/-- A schedule may not move a buffer. -/
def scheduledMoved : Compiled :=
  { scheduled with map := [.one 0 0 1, .one 3 0 1, .one 2 0 1] }

#guard !scheduleOnly placed scheduledMoved

/-! ## Route -/

/-- The two words are never in one moving slot, so one stream carries both. -/
def routed : Compiled where
  cfg := cfg 1
  memSizes := [1, 0, 1, 1]
  map := map
  prog :=
    [ .once 0 0 (.read 0 (e 0)),
      .once 1 3 (.un .i8 .relu (e 0) (e 0)),
      .once 2 6 (.write (e 0) 0),
      .once 3 7 (.write (e 0) 0) ]
  cycles := 8

#guard checkRouted scheduled routed
#guard routeOnly scheduled routed

/-- Everything one cycle later is another schedule, not another routing. -/
def routedLate : Compiled :=
  { routed with prog := routed.prog.map fun en => { en with time := en.time + 1 }, cycles := 9 }

#guard !sameEntries scheduled routedLate
#guard !routeOnly scheduled routedLate

/-- The relu's word is put on stream 0 and looked for on stream 1. -/
def routedApart : Compiled :=
  { routed with
    cfg := cfg 2
    prog :=
      [ .once 0 0 (.read 0 (e 0)),
        .once 1 3 (.un .i8 .relu (e 0) (e 0)),
        .once 2 6 (.write (e 1) 0),
        .once 3 7 (.write (e 1) 0) ] }

#guard sameEntries scheduled routedApart
#guard !oneRenaming scheduled routedApart
#guard !checkRouted scheduled routedApart

end TauTest.Decides
