import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Start here" =>
This course teaches you to write specifications in Lean 4. It takes you
through one real development from the bottom up. The development is tau-tpu:
a small machine for tensor programs, a compiler for it, and proofs that connect the two.

A specification is a definition, in Lean, of what something does. The
hardware is described in words and the compiler is written in C++. Neither
is precise enough to prove anything about. By the end you will have turned
both into Lean yourself: the components, the machine, the compiler's input,
two of its passes. You will have stated what each should satisfy. And you
will have read a theorem that says a compiled program computes what its
source says, on hardware built from the components you specified.

You will write few proofs. In real work on a machine or a compiler the proofs
are long, and an AI agent writes most of them. What cannot be handed to an
agent is deciding what the definitions and the statements should say. That is
what the course is about. The first chapters still have you prove things, so
that you know what a proof is and can read one.

# Who this is for

You can program, and you have seen proof by induction. You have not
necessarily used Lean, and you have not necessarily taken a course in digital
design, computer architecture or compilers.

The course teaches the Lean and the method. It does not teach the other
three subjects.
Where a chapter needs a term from one of them, it lists the term under "Terms
to look up", and the reading list at the end of the book says where to look
each one up. Ten minutes per term is enough.

# What tau-tpu is

A tau-tpu machine is a row of _slices_ connected by directional _streams_
that carry words east or west, one slice per cycle. A program for the
machine is a fixed timetable of instructions with no branches and no queues:
if an instruction reads a stream slot on the wrong cycle, the slot is empty
and the machine traps.

Users write programs in Python or MLIR as operations on buffers, and may
_pin_ individual operations to cycles. An untrusted compiler turns a program
into per-slice timetables and a numeric _image_, while a Lean checker
validates each compiled output against its source.

```
9-slice machine (1 slice/cycle on east & west streams):
  ──east──▶ [0:mxm] [1:sxm] [2:mem] [3:mem] [4:vxm] [5:mem] [6:mem] [7:sxm] [8:mxm]
  ◀─west──

Flow:
  kernel.py / kernel.mlir ─tauc─▶ source → ... → compiled → image
                                    │                        │
                                    └─────── tau-check ──────┘ & tau-sim
```

The machine, its programs, and what a compiler must deliver are described in
`docs/README.md` and its companion files (`Machine.md`, `Programs.md`,
`Compiler.md`). This design follows the tensor streaming processors described
by Abts and others at ISCA 2020 and ISCA 2022.

# The tour

Before learning any Lean, see the finished thing work. Do "Setup" in the
repository's `README.md` first. The example below runs a quantized linear
layer `relu(requant(W * x + b))` on 2-lane words: with `x = [3, -2]`,
`b = [10, -20]`, and `W` having rows `[1, 2]` and `[3, 4]`, `W * x + b`
is `[9, -19]`, and `relu` leaves `[9, 0]`. `x`, `W` and the result are
integers of 8 bits; the product and `b` are integers of 32.

In a terminal in the repository folder:

```
compiler/build/bin/tauc examples/nn/linear/kernel.mlir -o out --print-mlir
```

It prints the program after each of the compiler's nine passes and writes
the stage files into `out/`. Compare `out/source.json` and
`out/compiled.json`: `source.json` lists buffer sizes and operations
(`load`, `matvec`, `add`, `requant`, `relu`, `store`) with no slices or
cycles, while `compiled.json` assigns each instruction a slice, a cycle
(`time`), and directional streams (`east` and `west`).

```
lake exe tau-check out/source.json out/compiled.json
```

This prints `ACCEPT`. That one word is backed by a theorem: for every
possible input, running that program on the machine gives what the program in
`out/source.json` computes. Now open `out/compiled.json`, find an
intermediate instruction such as `"op": "bin"` on slice 6, add one to its
`time` (`17` to `18`), and run the check again. It prints `REJECT` and
reports a trap: slice 6 read a stream slot that held nothing. (Change the
`time` back afterwards.)

```
lake exe tau-sim out/compiled.json examples/nn/linear/buffers.json
```

This runs the program and prints the buffers. The last buffer holds `[[9, 0]]`,
matching `relu([9, -19])`. The simulator is not a separate piece of software.
It is the Lean specification of the machine, compiled.

If you have not built the compiler, skip the first command and copy
`examples/nn/linear/stages/` to `out/` (`cp -r examples/nn/linear/stages out`)
before inspecting or editing `out/compiled.json`. Six chapters run the
compiler or inspect its output: start here, kernels, expressions, the
checker, pins, and from Python to an image. The first four each name a
`stages/` folder to read instead; the last two work without the compiler for
their Lean examples and exercises.

`lake exe` builds a tool if it needs to and then runs it. Like every `lake`
command, it works only in the repository folder.

You do not need to understand any of this yet. Come back to these three
commands after the chapter on the slice-level machine and after the chapter
on the checker, and see how much more they say.

# How each chapter works

The course moves through five phases: two introductory chapters, three warmup
chapters where you read existing definitions and write short proofs yourself,
"Writing a specification" setting out the method, ten specification chapters
where you specify from prose or C++ before reading `spec/Tau/`, and finally two
proof-reading chapters plus "Extending the machine".

When a chapter introduces new Lean code or exercises, it uses these parts:

* *Terms to look up*. Look them up in the reading list.
* *Source*: what you specify from. A section of a doc, such as
  `docs/Machine.md`, or a C++ file of the compiler.
* *Specify*: the file under `course/Specify/` in which you write your
  definition.
* *Read*: the definition files of the repository. In the three block warmup
  chapters you open them at once. From the chapter "Writing a specification"
  on, you open them after you have written your own.
* *Proofs*: proof files. A few of their proofs are exercises. The rest are
  for reading.
* *The idea*, with something you can run.
* *How to work through it*: numbered steps. Do them in order.
* *Exercises*.
* *Hints*, to read only when stuck.
* *Checkpoint*: how to tell you are done.

The exercises come in three main kinds (some chapters also omit `Prove` and
use hand-written programs or proof reading instead):

* *Specify.* You write a definition from the source, in a file under
  `course/Specify/`. Tests in the file say which rows of the source's table
  your definition gets right. Then you list what the source did not say.
* *State.* You write, as a proposition, a property the thing you defined
  should have. There is nothing to check a statement against except your
  judgement, the statement in the repository, and an agent's attempt to
  prove it.
* *Prove.* A file under `course/Prove/` in which a few proofs have been
  replaced by `sorry`. They are the short proofs that show what a
  specification means. The solution is the file of the same name under
  `spec/Tau/Proofs/`.

Do every "Specify" and every "State". Do the "Prove" exercises of the first
three component chapters (through "Multiply-accumulate") yourself. After
that you may give them to an agent, as long as you review what comes back
the way the chapter "Writing a specification" shows.

Some chapters add a *Challenge*, which is larger and optional.

# How the Lean code is laid out

Definitions and theorems live in separate trees.
`spec/Tau/Blocks/ShiftRegister.lean` says what a shift register is.
`spec/Tau/Proofs/Blocks/ShiftRegister.lean` says what is true of it. When you want
to know what something does, read the first kind of file. It contains no
proofs.

That split is also the split of the work. A person writes and judges what is
outside `spec/Tau/Proofs/`. What is inside it, Lean checks, and an agent can
write. Every proof of the development is there, for the whole machine and
the whole compiler, whether or not the course asks you for it.

`spec/README.md` says in a few pages what the parts are and names the
doc section, the definition and the theorem for each. In `docs/` are the
docs that the chapters specify from: `Machine.md` for the hardware chapters,
`Programs.md` and `Compiler.md` for the later ones.

# A plan

One day means about six hours of focused work. The numbers are estimates, and
nobody has yet been timed. `course/Work/Log.md` is a table for your own
times.

* Day 0: this chapter and "Working in Lean".
* Days 1 to 4: the shift register, the accumulator, the multiply-accumulate
  cell. You read a specification and prove what it does.
* Day 5: "Writing a specification". The method for everything after it.
* Days 6 to 11: pipeline and sequencer, memory, repeater, systolic array.
  You write each from its section of `Machine.md`.
* Days 12 to 14: the slice-level machine. You specify its streams and some
  of its instructions, and program it by hand.
* Days 15 to 17: kernels, loop unrolling, expressions and simplification.
  You turn compiler passes in C++ into Lean.
* Days 18 to 20: the checker, per-pass checks, three ways to specify a
  pass, and a rule for schedules.
* Days 21 to 22: pins and timelines. You specify what timing constraints
  guarantee.
* Days 23 to 24: from Python to an image. The frontend, calls, slicing,
  folding and encoding.
* Day 25: the cell-level machine. You read the largest proof.
* Day 26: end to end, and your claims table.
* After that: the chapter "Extending the machine" has as much homework as you
  want.

If you fall behind, skip challenge exercises first, then "Prove" exercises
after day 5. Do not skip a "Specify" by reading the definition in `spec/Tau/`.
The tests tell you how far you are, and that is worth more than the
answer.

# Before day one

Play the first three worlds of the Natural Number Game, which takes about two
hours. The link is in the reading list.
