import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The slice-level machine" =>
*Terms to look up:* instruction set architecture, SIMD.

*Read:* `Tau/Isa/Op.lean`, `Tau/Isa/Instr.lean`,
`Tau/SliceLevel/Machine.lean`, `tests/TauTest/Linear.lean`.

*Time:* three days.

This chapter has no proofs. You read the specification of a whole machine,
and then you program the machine by hand.

# The instruction set

{docstring Tau.Kind}

{docstring Tau.Track}

{docstring Tau.Instr}

{docstring Tau.Timed}

`Timed.once slice time instr` is an instruction issued once. The other three
fields make it repeat, and are explained below.

A program is a list of timed instructions, and a chip is described by a
`Config`:

{docstring Tau.Config}

# The machine

Its state is the contents of every stream slot and of every slice.

{docstring Tau.State}

One cycle is the function `step`. Read it in `Tau/SliceLevel/Machine.lean`
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

Here is a chip with three slices: a memory, a vector slice, a memory. Each
has a delay of one cycle and there is one stream in each direction.

```lean
def tinyChip : Tau.Config where
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

That is the rule from the top of `Machine.lean`: a result computed at slice
`p` on cycle `t` can be read at slice `q` on cycle
`t + delay + 1 + |q - p|`. Here that is 0 + 1 + 1 + 2 = 4.

Run it. So that you can see what moves where, the memory holds names instead
of numbers: `.init 0 0` is a name for "the word that started in buffer 0",
and `.fill` is a name for "whatever was there". The chapter on expressions
explains these. `exprSem` tells the machine to compute with names.

```lean
def startImage : List (List Expr) := [[.init 0 0], [], [.fill]]

example :
    execute exprSem tinyChip copyProgram 5 startImage
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
    execute exprSem tinyChip lateProgram 6 startImage
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
    execute exprSem tinyChip copyTwo 6 [[.init 0 0, .init 0 1], [], [.fill, .fill]]
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

`tests/TauTest/Linear.lean` contains a quantized linear layer scheduled by
hand on a nine-slice chip, with a comment on each instruction. Follow one
value through it: the word `x` leaves slice 2 on cycle 0 and is used by slice
0 on cycle 4. Check that against the rule: 0 + 1 + 1 + 2 = 4. Then check the
arrival of `W * x` and of `b` at slice 4 on cycle 14.

The file also runs the checker on the same schedule. Ignore that part for
now.

# How to work through it

1. Read `Tau/Isa/Op.lean` and `Tau/Isa/Instr.lean`.
2. Read `Tau/SliceLevel/Machine.lean` top to bottom.
3. Copy the tiny example above into your scratch file and change it: move the
   read to cycle 3, make the word travel west from slice 2 to slice 0, add a
   `relu` at slice 1 on the way. Predict each result before you run it.
4. Work through the hand schedule in `tests/TauTest/Linear.lean`.
5. Do the exercises.

# Exercises

There is no guided file for this chapter.

*Open.* On the nine-slice chip of `tests/TauTest/Linear.lean`, write a
schedule that adds a word held in slice 2 to a word held in slice 3 and
stores the sum in slice 5. Make a file `course/Work/Add.lean` that starts
with the chip and the helpers of that test, and fill in the four times:

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

*Open.* Write seven small programs for `tinyChip`, each of which traps with a
different one of the seven kinds of trap, and check each with an
`example ... := by rfl` as above. This shows whether you have understood
`step` and `execute`. One of the seven is raised by `execute` before the
first cycle.

*Challenge.* State and prove the transit lemma for one stream: if a value is
placed on an east-going stream at position `p` on cycle `t`, and no slice
between `p` and `q` places anything on that stream in the meantime, then the
value is at position `q` on cycle `t + (q - p)`. Stating it precisely, in
terms of `advanceRow`, is most of the work. Compare your statement with
`shiftRegister_outAt`.

# Checkpoint

Your add schedule passes its guard. Given a schedule and the chip, you can
say on which cycle a given word is at a given position.
