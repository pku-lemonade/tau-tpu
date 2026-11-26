import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The slice-level machine" =>
*Terms to look up:* instruction set architecture, SIMD.

*Source:* `docs/Machine.md`, section 3.

*Specify:* `course/Specify/Machine/SliceLevel.lean`.

*Read:* `spec/Tau/Isa/Op.lean` and `spec/Tau/Isa/Instr.lean` now.
`spec/Tau/Machine/SliceLevel.lean` and `spec/tests/TauTest/Linear.lean` after you have
specified.

*Proofs:* `spec/Tau/Proofs/Machine/Timing.lean`,
`spec/Tau/Proofs/Machine/SliceLevel.lean`. For reading.

*Time:* three days.

The components are done. This chapter puts a machine together. You specify
two parts of it from the doc, read the specification of the whole, and
then program the machine by hand.

# Specify two parts of it first

Read section 3 of `Machine.md`, all of it. Then read `spec/Tau/Isa/Op.lean`,
`spec/Tau/Isa/Instr.lean`, and the first eighty lines of
`spec/Tau/Machine/SliceLevel.lean`, down to the definition of `State`. Those are
the types: operations, instructions, traps, the state of a slice. Stop
there.

The whole machine is too large to write in a day. `course/Specify/Machine/SliceLevel.lean`
asks for the two parts that everything else follows from: how a stream moves
in one cycle, and what four of the instructions do, traps included. Follow
the steps at the top of the file and come back when the three reports say
that all rows agree.

# The instruction set

{docstring Tau.Kind}

{docstring Tau.Stream}

{docstring Tau.Instr}

{docstring Tau.TimedEntry}

`TimedEntry.once slice time instr` is an instruction issued once. The other three
fields make it repeat, and are explained below.

A program is a list of timed instructions, and a machine is described by a
`Config`:

{docstring Tau.Config}

# The machine

Its state is the contents of every stream slot and of every slice.

{docstring Tau.State}

One cycle is the function `step`. Read it in `spec/Tau/Machine/SliceLevel.lean`
together with the comment at the top of the file. Read the functions in the
order they are defined: `exec`, `shiftPipe`, `stepSlice`, `stepSlices`,
`inject`, `advanceRow`, `advance`, `step`.

Two pieces of syntax appear throughout. `{ sl with words := ... }` is a copy
of the slice state `sl` with one field replaced. `rs.map (·.2)` takes the
second component of every pair in a list.

Many of them return an `Except`. A value of `Except Trap α` is either
`.ok x`, a normal result, or `.error t`, a trap. The machine stops at the
first trap.

{docstring Tau.TrapKind}

A trap is not an error message added for convenience. It is part of the
specification: it says which programs the hardware gives no meaning to.

# The timing rule, on the smallest example

Here is a machine with three slices: a memory, a vector slice, a memory. Each
has a delay of one cycle and there is one stream in each direction.

```
──east──▶ [ 0: mem ] ──▶ [ 1: vxm ] ──▶ [ 2: mem ]
◀─west──
```

```lean
def tinyMachine : Tau.Config where
  kinds := [.mem, .vxm, .mem]
  streams := 1
  memDelay := 1
  vxmDelay := 1
  sxmDelay := 1
  mxmDelay := 1
```

This program copies word 0 of the left memory to word 0 of the right memory.
`.once slice time instruction` is a timed instruction, and `⟨.east, 0⟩` is
stream 0 going east.

```lean
def copyProgram : Program :=
  [ .once 0 0 (.read 0 ⟨.east, 0⟩),
    .once 2 4 (.write ⟨.east, 0⟩ 0) ]
```

Why cycle 4? Follow the word.

* Cycle 0: slice 0 is told to read. The word enters the slice's pipe.
* Cycle 1: the word leaves the pipe, because the delay is 1.
* Cycle 2: the word is on the stream at position 0.
* Cycle 3: it is at position 1.
* Cycle 4: it is at position 2, where slice 2 is told to write it.

That is the timing rule from Machine 3.4 (also stated at the top of
`spec/Tau/Machine/SliceLevel.lean`): a result computed at slice
`p` on cycle `t` can be read at slice `q` on cycle
`t + delay + 1 + |q - p|`, where `delay` is the delay of the instruction
that computed it. Here that is 0 + 1 + 1 + 2 = 4.

The definition of the machine does not contain this rule. `step` says what
happens in one cycle: a result enters the pipe of its slice at the slot that
leaves after its delay, the last slot of the pipe comes out, and every stream
moves one position. The rule is what
follows from that over many cycles, in the same way as `shiftRegister_outAt`
follows from the one-cycle definition of the shift register. It is a theorem,
in `spec/Tau/Proofs/Machine/Timing.lean`:

{docstring Tau.arrives_east}

Three definitions appear in its statement. `IsRun` says that `st` lists the
states of a run that does not trap, `st u` being the state at the start of
cycle `u`. `State.result` is what a slice computes in a cycle, and
`State.out` is what comes out of its pipe and is placed on a stream. The
hypothesis `hfree` is the condition "if nothing else is put on that stream in
its path": no slice on the way places a word of its own in the slot just as
the travelling word arrives there. `arrives_west` is the mirror image.

The theorem says the word is there on that cycle. It does not say the word
is there on no other cycle.

Run it. So that you can see what moves where, the memory holds names instead
of numbers: `.init 0 0` is a name for "the word that started in buffer 0",
and `.fill` is a name for "whatever was there". The chapter on expressions
explains these. `exprSem` tells the machine to compute with names.

```lean
def startImage : List (List Expr) := [[.init 0 0], [], [.fill]]

example :
    execute exprSem tinyMachine copyProgram 5 startImage
      = .ok [[.init 0 0], [], [.init 0 0]] := by
  rfl
```

The right memory now holds the word from the left.

Issue the write one cycle late and the word has gone past. The machine traps
at slice 2 on cycle 5:

```lean
def lateProgram : Program :=
  [ .once 0 0 (.read 0 ⟨.east, 0⟩),
    .once 2 5 (.write ⟨.east, 0⟩ 0) ]

example :
    execute exprSem tinyMachine lateProgram 6 startImage
      = .error ⟨.emptyRead, 2, 5⟩ := by
  rfl
```

# Repeats

An entry of a program can repeat. This one reads addresses 0 and 1 on cycles
0 and 1: issue once more (`repeats := 1`) and add one to the address each
time (`stride := 1`). The write does the same four cycles later.

```lean
def copyTwo : Program :=
  [ { slice := 0, time := 0, instr := .read 0 ⟨.east, 0⟩, repeats := 1, stride := 1 },
    { slice := 2, time := 4, instr := .write ⟨.east, 0⟩ 0, repeats := 1, stride := 1 } ]

example :
    execute exprSem tinyMachine copyTwo 6 [[.init 0 0, .init 0 1], [], [.fill, .fill]]
      = .ok [[.init 0 0, .init 0 1], [], [.init 0 0, .init 0 1]] := by
  rfl
```

What a repeating entry issues on each cycle is defined in the chapter on the
repeater. `gap` is the number of idle cycles between two issues, so `gap := 0`
means consecutive cycles.

# Values the machine never looks at

The machine is written for an arbitrary type of values, with the operations
supplied from outside:

{docstring Tau.Sem}

`exprSem` above is one `Sem`. `wordSem lanes` is another: real words of
32-bit lanes. The machine moves values and hands them to these operations. It
never inspects one to decide what to do. Which slots are read, and whether a
trap happens, depend only on the program. Look through `exec` and confirm
this for yourself: no `if` or `match` in it tests a value of type `V`.

The chapter on the checker turns this observation into the key lemma of the
course.

# A real program

`spec/tests/TauTest/Linear.lean` contains a quantized linear layer scheduled by
hand on a nine-slice machine, with a comment on each instruction. Follow one
value through it: the word `x` leaves slice 2 on cycle 0 and is used by slice
0 on cycle 4. Check that against the rule: 0 + 1 + 1 + 2 = 4. Then check the
arrival of `W * x` and of `b` at slice 4 on cycle 14.

The file also runs the checker on the same schedule. Ignore that part for
now.

# How to work through it

1. Read section 3 of `Machine.md`, and the types, as above.
2. Specify streams and instructions in `course/Specify/Machine/SliceLevel.lean`.
3. Read `spec/Tau/Machine/SliceLevel.lean` top to bottom. Compare `advanceRow` and
   `exec` with yours. In which order does the repository's `exec` make its
   checks? The doc does not say, and the `Decisions` table shows that the
   order can be seen from outside.
4. Copy the tiny example above into your scratch file and change it: move the
   read to cycle 3, make the word travel west from slice 2 to slice 0, add a
   `relu` at slice 1 on the way. Then give `relu` a delay of its own, with
   `{ tinyMachine with delays := [("relu", 3)] }`. Predict each result before
   you run it.
5. Work through the hand schedule in `spec/tests/TauTest/Linear.lean`.
6. Read the statements of `out_delay`, `sample_step` and `arrives_east` in
   `spec/Tau/Proofs/Machine/Timing.lean`, and the outline of `arrives_east`.
   Compare `sample_step` with your own statement about one cycle.
7. Do the exercises.

# Exercises

*Specify.* `course/Specify/Machine/SliceLevel.lean`.

*State.* `MovesOnePosition` in that file.

*By hand.* On the nine-slice machine of `spec/tests/TauTest/Linear.lean`, write a
schedule that adds a word held in slice 2 to a word held in slice 3 and
stores the sum in slice 5. Make a file `course/Work/Add.lean` that starts
with the machine and the helpers of that test, and fill in the four times:

```
import TauTest.Linear
open Tau TauTest.Linear

def addProgram : Program :=
  [ .once 2 sorry (.read 0 (e 0)),
    .once 3 sorry (.read 0 (e 1)),
    .once 4 sorry (.bin .add (e 0) (e 1) (e 0)),
    .once 5 sorry (.write (e 0) 0) ]

def addImage : List (List (Word 2)) :=
  [[], [], [Word.ofInts [1, 2]], [Word.ofInts [10, 20]], [], [Word.zero], [], [], []]

#guard (match execute (wordSem 2) cfg addProgram 12 addImage with
        | .ok mem => ((mem[5]?.getD [])[0]?.getD Word.zero).toInts == [11, 22]
        | .error _ => false)
```

Both operands must be at slice 4 on the same cycle, and they start at
different distances from it. You are done when the guard passes. Then make
the program one cycle shorter, or convince yourself that it cannot be done.
You are doing by hand what the compiler's scheduler does.

*By hand.* Write seven small programs for `tinyMachine`, each of which traps with
a different one of the seven kinds of trap, and check each with an
`example ... := by rfl` as above. One of the seven is raised by `execute`
before the first cycle.

*State.* The theorem `arrives_east` has the hypothesis `hfree`. Write a
program for `tinyMachine` in which `hfree` is false, run it, and say what the
slice at the far end reads. Then answer: is the statement without `hfree`
false, or only harder to prove?

*Questions.* Section 3 leaves at least six things open. Two to start you
off: what happens when a word arrives at a position on the cycle a slice
places a result there, and which trap is reported when an instruction is
wrong in two ways.

*Claims.* Add to `course/Work/Claims.md` a row for each thing you wrote in this
chapter: what it is, and how it stands.

# Checkpoint

The three reports say that all rows agree. Your add schedule passes its
guard. Given a schedule and the machine, you can say on which cycle a given word
is at a given position, and which theorem says so.
