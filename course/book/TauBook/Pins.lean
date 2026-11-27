import VersoManual
import Tau
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Pins" =>
*Terms to look up:* timing constraint, initiation interval, pipelining,
observable behaviour.

*Sources:* `docs/Programs.md`, sections 5 and 6; `docs/Machine.md`,
section 3.9; the opening comments of `compiler/lib/Passes/Place.cpp` and
`Schedule.cpp`, for what they say about pins.

*Specify:* `course/Specify/IR/Pins.lean`.

*Read:* `spec/Tau/Isa/Event.lean`, `spec/Tau/Machine/Issues.lean`; the `pin` case of
`Stmt.exec` in `spec/Tau/IR/Kernel.lean`; `covers` and `agree` in
`spec/Tau/Check/Checker.lean`.

*Proofs:* three short ones are exercises: `check_pins` in
`Prove/Check/Checker.lean`, `checkKernels_pins` and `passes_pins` in
`Prove/Check/Passes.lean`. `spec/Tau/Proofs/Machine/Issues.lean` is for
reading.

*Time:* two days.

# The problem

The checker of the last chapter says what a compiled program computes. It
says nothing about when. A program that takes a million cycles is accepted as
readily as one that takes twenty, and two programs that end with the same
buffers are the same program to it.

For a kernel on its own that is the right answer. A kernel says nothing about
time, so the compiler may choose. But the people who use a machine like this
care about time in two ways the kernel cannot express. Someone who feeds the
machine one word every four cycles needs the fourth word to be handled sixteen
cycles after the first, not whenever the compiler finds room. And someone who
runs one kernel after another needs to know when the first has finished.

So a program may take the decision back, one operation at a time. That is a
_pin_.

# What a pin claims

A pin is attached to one operation and names a cycle. Read section 5 of
`docs/Programs.md`, and do the first part of `course/Specify/IR/Pins.lean` now, before you
read on.

What a pin claims is an _event_.

{docstring Tau.Event}

In a kernel a pinned statement is the statement wrapped in `Stmt.pin`. Here
is the kernel of the chapter on kernels again, with its relu pinned to cycle
`t`.

```lean
def reluAt (t : Nat) : Kernel :=
  [ .stmt (.load 0 0 ⟨0, 0⟩),
    .stmt (.pin ⟨t, 0⟩ (.un 1 .relu 0)),
    .stmt (.store 1 1 ⟨0, 0⟩) ]
```

Running a kernel gives its buffers, as before, and its _timeline_: the events
of its pinned statements. Run on names, the timeline of this kernel has one
event. It says: the relu of the word that started at position 0 of buffer 0,
on cycle 3.

```lean
example :
    kernelEvents (reluAt 3) [1, 1]
      = [⟨3, none, .un .relu (.init 0 0)⟩] := by
  rfl
```

A pin does not change what a kernel computes. `Stmt.exec` runs the statement
inside and then writes the event down.

# What the machine issues

A compiled program has a cycle for every instruction, so it has an event for
every word it issues. Read Machine 3.9: a slice _issues_ a word
when it runs an instruction that has a result, or one that writes.

{docstring Tau.issues}

A small machine and a program for the kernel above: read on cycle `t`, relu
three cycles later, write three cycles after that. The distances are the
timing rule, with a delay of 1 and a distance of 1.

```lean
def pinMachine : Tau.Config where
  kinds := [.mem, .vxm, .mem]
  streams := 1
  memDelay := 1
  vxmDelay := 1
  sxmDelay := 1
  mxmDelay := 1

def reluProgram (t : Nat) : Compiled where
  cfg := pinMachine
  memSizes := [1, 0, 1]
  map := [⟨0, 0, 1⟩, ⟨2, 0, 1⟩]
  prog :=
    [ .once 0 t (.read 0 ⟨.east, 0⟩),
      .once 1 (t + 3) (.un .relu ⟨.east, 0⟩ ⟨.east, 0⟩),
      .once 2 (t + 6) (.write ⟨.east, 0⟩ 0) ]
  cycles := t + 7
```

Its timeline has three events: what it read, the relu, and the store.

```lean
example :
    machineEvents (reluProgram 0)
      = [ ⟨0, none, .init 0 0⟩,
          ⟨3, none, .un .relu (.init 0 0)⟩,
          ⟨6, some (1, 0), .un .relu (.init 0 0)⟩ ] := by
  rfl
```

The second is the kernel's event. The program that starts on cycle 0 keeps
the pin.

# The check

A program in a later IR keeps the pins of an earlier one if its timeline contains the
earlier timeline.

{docstring Tau.covers}

{docstring Tau.agree}

`check` and every per-pass check is `agree` on the two programs it compares.

```lean
example :
    check (Source.ofKernel (reluAt 3)) [1, 1] (reluProgram 0) = true := by
  rfl
```

The same program started one cycle later computes the same buffers. Against
the kernel pinned to cycle 3 it is rejected, and against the kernel pinned to
cycle 4 it is accepted.

```lean
example :
    check (Source.ofKernel (reluAt 3)) [1, 1] (reluProgram 1) = false := by
  rfl

example :
    check (Source.ofKernel (reluAt 4)) [1, 1] (reluProgram 1) = true := by
  rfl
```

# Every IR has a timeline

A source program, a kernel and a placed program have the events of their
pinned operations. A compiled program has every word it issues. So as a
program goes through the compiler its timeline only grows, and each check
asks that nothing was lost:

* `checkInlined`, `checkKernels` and `checkPlaced`: the pins are still there.
* `checkScheduled`: the pinned instructions are issued on their cycles.
* `checkRouted`: every instruction of the first program is issued by the
  second on the same cycle.

The last line is new in what it asks. Between two compiled programs every
instruction counts as pinned. A router that moved an instruction by one cycle
would be rejected even if the buffers came out the same.

```lean
example : checkRouted (reluProgram 0) (reluProgram 0) = true := by
  rfl

example : checkRouted (reluProgram 0) (reluProgram 1) = false := by
  rfl
```

# The theorem

Each check now has two theorems. The one you proved says what is computed.
The other says when.

```lean
example (s : Source) (c : Compiled) (bufs : List (List (Word 4)))
    (h : check s (bufs.map List.length) c = true) :
    s.timeline (wordSem 4) bufs ⊆ c.timeline (wordSem 4) bufs Word.zero :=
  check_pins (wordSem 4) (wordSem_lawful 4) s c bufs Word.zero h
```

In words: on any buffer contents, every event of the source program is an
event of the machine. The checker saw one run on names; the theorem is about
every run on real words.

The bridge is the one from the last chapter. The machine does not look at its
values, so the cycle on which it issues a word cannot depend on the word.
`issues_map` says so: what a run issues from a mapped memory image is what
the run from the image issues, on the same cycles, with the function applied
to the words. Read its statement. Its proof is `execute_map` again, one layer
at a time.

# What a pin does not say

An event is a word and a cycle. It does not say which slice issued the word,
or which instruction. Two consequences:

* A program may compute a pinned word early, park it in memory, and read it
  out again on the pinned cycle. The read issues the word, so the pin is
  kept.
* If two operations compute the same word and one is pinned, the compiler may
  issue either one on that cycle.

Both are decisions, made in `spec/Tau/Isa/Event.lean`. A stronger claim would have
to say which instruction of the compiled program stands for which operation
of the source. No check in tau-tpu knows that, by design: a check does not
look at how a pass got from its input to its output.

# How the compiler meets a pin

Read the paragraphs on pins at the top of `Place.cpp` and `Schedule.cpp`.

`tau-place` puts each pin on the instruction that issues the word, and
decides nothing about time. `tau-schedule` gives every pinned instruction its
cycle before it schedules anything else. The timing rule has no slack: a word
issued at one slice is at another a fixed number of cycles later, and on no
other cycle. So a word goes directly into a pinned instruction only from an
instruction exactly that many cycles before it. The scheduler therefore
works backward from each pin through the instructions whose words have to
reach it, and puts each as late as it can be. Everything else it schedules
forward, from cycle 0. Two pinned instructions joined by a word are the right
distance apart or they are not. If they are not, and the second is later
than that, the word waits in memory, which is the only place a word can wait.
If the second is earlier, the compiler refuses the program.

`examples/pinned-chain/kernel.py` has both cases: three pins that agree, and
three of which one is much later.

`examples/paced/kernel.py` pins a loop to one iteration every four cycles:

```
PYTHONPATH=compiler/python python3 -m tau examples/paced/kernel.py -o out
compiler/build/bin/tauc out/kernel.mlir -o out
lake exe tau-sim --timeline out/source.json examples/paced/buffers.json
lake exe tau-check out/source.json out/compiled.json
```

One iteration takes seven cycles from its read to its write, so with four
cycles between iterations two are always in flight. Open `out/compiled.json`:
the whole loop is three entries, each issued four times, four cycles apart.
A loop at a fixed spacing is what a repeating entry is.

```
cycle:   2   4   6   8  10  12  14  16  18  20  22
iter 0:  R───────V─────W
iter 1:          R───────V─────W
iter 2:                  R───────V─────W
iter 3:                          R───────V─────W
         (R = read at slice 2, V = relu at slice 4, W = write at slice 3)
```

# How to work through it

1. Do `course/Specify/IR/Pins.lean`, including the four questions under "Judge".
2. Read `spec/Tau/Isa/Event.lean` and `spec/Tau/Machine/Issues.lean`. Redo the small
   example above in your scratch file with a pin on the store.
3. Read `covers` and `agree`. Then prove `check_pins` in
   `Prove/Check/Checker.lean`, and `checkKernels_pins` and `passes_pins` in
   `Prove/Check/Passes.lean`.
4. Read the statement of `issues_map` in
   `spec/Tau/Proofs/Machine/Issues.lean`, and the proof of `State.issue_map`.
5. Run the four commands above. Then do the exercises "By hand".

# Lean you will need

* `a ⊆ b` on lists means: every element of `a` is an element of `b`. To prove
  it, `intro e he` gives you an element `e` and the fact `he` that it is in
  `a`. To use it, apply it to such a fact: if `h : a ⊆ b` and `he : e ∈ a`
  then `h he : e ∈ b`.
* `rw [lemma]` with a lemma that says `x = y` replaces `x` by `y` in the
  goal. The two `_of_events` lemmas say that a timeline on real words is the
  timeline on names, evaluated.

# Exercises

*Specify.* `course/Specify/IR/Pins.lean`.

*State.* In the same file: what it means for a compiled program to keep the
pins of a source program.

*Prove.* `check_pins`, `checkKernels_pins` and `passes_pins`.

*Claims.* Add to `course/Work/Claims.md` a row for what a pin claims and a row
for what it does not.

*By hand.* In `examples/paced/kernel.py`, change the spacing from 4 to 2,
then 1, then 0, and compile each (work on a copy, or change it back
afterwards). Write down first how many cycles you expect
each to take. One of them does not compile: read the error, find in
`Schedule.cpp` the line that prints it, and say what on the machine is asked to
do two things at once. For the smallest spacing that works, say how many
iterations are in flight at once.

*By hand.* Write a kernel with two pinned operations joined by a value.
First find, with `tau-sim --timeline` on the image of the unpinned kernel,
the cycles the compiler gives the two, and pin both to those. Then move the
second one cycle earlier, and compile. Then move it twenty cycles later, and
find in `out/scheduled.json` the write and the read that `tau-schedule` put
between them. `out/placed.json` has neither: say why.

*By hand.* Break the compiler, as in the last chapter, and say first which
stage you expect to be rejected. For one of the three the answer is none;
say why that change is harmless.

1. In `compiler/lib/Passes/Schedule.cpp`, in `Scheduler::run`, replace
   `if (hasPins) {` by `if (false) {`, so that pins are ignored.
2. In `compiler/lib/Passes/Inline.cpp`, replace `at.getInt() + origin` by
   `at.getInt()`, so that a called kernel's pins are not moved.
3. In `compiler/lib/Passes/Unroll.cpp`, delete the line
   `op->removeAttr("every");`.

*Challenge.* Make a pin say which slice. Decide what the event has to hold,
which IRs can know it, and which checks would have to change. You do not
have to build it. Write down the first IR of a program in which "the slice
of this operation" has a meaning, and what that says about pins in the IRs
before it.

# Hints

For `check_pins`: rewrite both timelines with the two `_of_events` lemmas.
What is left is `covers_denote`, applied to what `agree_events` gets out of
the second half of `h`.

For `checkKernels_pins`: the same with a kernel on both sides.

For `passes_pins`: `intro e he`, then carry `he` through the eight theorems,
one `have` for each.

# Checkpoint

`lake build Prove.Check.Checker Prove.Check.Passes` prints no `sorry`
warning. You can say what an event is, why a compiled program has more of
them than its source, and what a pin leaves undecided. You can say why the
cycle on which the machine issues a word cannot depend on the buffers.
