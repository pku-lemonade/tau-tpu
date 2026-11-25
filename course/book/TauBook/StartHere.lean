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
a small tensor processor, a compiler for it, and proofs that connect the two.

A specification is a definition, in Lean, of what something does. The
hardware is described in a manual and the compiler is written in C++. Neither
is precise enough to prove anything about. By the end you will have turned
both into Lean yourself: the components, the machine, the compiler's input,
two of its passes. You will have stated what each should satisfy. And you
will have read a theorem that says a compiled program computes what its
source says, on hardware built from the components you specified.

You will write few proofs. In real work on a chip or a compiler the proofs
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

A tau-tpu chip is a row of _slices_. Each slice does one kind of job: store
words, do arithmetic on them, rearrange them, or multiply by a matrix. Between
the slices run _streams_, which carry words east or west, one slice per cycle.

A program for the chip is a timetable. It lists every instruction together
with the slice that executes it and the cycle on which it does so. The chip
has no branches, no queues, and nothing that waits. If an instruction looks
for its operand on a stream one cycle too early, the operand is not there yet
and the chip traps.

Deciding the timetable is the compiler's job. A design like this is called
_statically scheduled_. It follows the tensor streaming processors described
by Abts and others at ISCA 2020 and ISCA 2022.

# The tour

Before learning any Lean, see the finished thing work. Do "Setup" in the
repository's `README.md` first. Then, in a terminal in the repository
folder:

```
compiler/build/bin/tauc examples/linear/kernel.mlir -o out --print-mlir
```

This compiles a quantized linear layer. It prints the program after each of
the compiler's five passes and writes six files into `out/`. Open
`out/compiled.json` and read the `program` list. Each entry is one line of
the timetable: a slice, a cycle, and an instruction.

```
lake exe tau-check out/kernel.json out/compiled.json
```

This prints `ACCEPT`. That one word is backed by a theorem: for every
possible input, running that program on the chip gives what the kernel
computes. Now open `out/compiled.json`, find the last instruction, add one to
its `time`, and run the check again. It prints `REJECT` and says why.

```
lake exe tau-sim out/compiled.json examples/linear/buffers.json
```

This runs the program and prints the buffers. The last buffer is the result.
The simulator is not a separate piece of software. It is the Lean
specification of the chip, compiled.

If you have not built the compiler, skip the first command and use the
folder `examples/linear/stages/` in place of `out/`. It holds the same six
files. The chapters on kernels, on expressions and on the checker run the
compiler again, and each names a `stages/` folder to read instead.

`lake exe` builds a tool if it needs to and then runs it. Like every `lake`
command, it works only in the repository folder.

You do not need to understand any of this yet. Come back to these three
commands after the chapter on the slice-level machine and after the chapter
on the checker, and see how much more they say.

# How each chapter works

Every chapter has the same parts.

* *Terms to look up*. Look them up in the reading list.
* *Source*: what you specify from. A section of the manual,
  `course/architecture-manual.md`, or a C++ file of the compiler.
* *Specify*: the file under `course/Specs/` in which you write your
  definition.
* *Read*: the definition files of the repository. In the first three
  chapters you open them at once. From the chapter "Writing a specification"
  on, you open them after you have written your own.
* *Proofs*: proof files. A few of their proofs are exercises. The rest are
  for reading.
* *The idea*, with something you can run.
* *How to work through it*: numbered steps. Do them in order.
* *Exercises*.
* *Hints*, to read only when stuck.
* *Checkpoint*: how to tell you are done.

The exercises come in three kinds, and every chapter after the fifth has all
three.

* *Specify.* You write a definition from the source, in a file under
  `course/Specs/`. Tests in the file say which rows of the source's table
  your definition gets right. Then you list what the source did not say.
* *State.* You write, as a proposition, a property the thing you defined
  should have. There is nothing to check a statement against except your
  judgement, the statement in the repository, and an agent's attempt to
  prove it.
* *Prove.* A file under `course/Exercises/` in which a few proofs have been
  replaced by `sorry`. They are the short proofs that show what a
  specification means. The solution is the file of the same name under
  `Tau/Proofs/`.

Do every "Specify" and every "State". Do the "Prove" exercises of the first
five chapters yourself. After that you may give them to an agent, as long as
you review what comes back the way the chapter "Writing a specification"
shows.

Some chapters add a *Challenge*, which is larger and optional.

# How the Lean code is laid out

Definitions and theorems live in separate trees.
`Tau/Blocks/ShiftRegister.lean` says what a shift register is.
`Tau/Proofs/Blocks/ShiftRegister.lean` says what is true of it. When you want
to know what something does, read the first kind of file. It contains no
proofs.

That split is also the split of the work. A person writes and judges what is
outside `Tau/Proofs/`. What is inside it, Lean checks, and an agent can
write. Every proof of the development is there, for the whole machine and
the whole compiler, whether or not the course asks you for it.

`docs/overview.md` says in two pages what the parts are and names the
definition and the theorem for each. `course/architecture-manual.md` is the architecture
manual that the hardware chapters specify from.

# A plan

One day means about six hours of focused work. The numbers are estimates, and
nobody has yet been timed. `course/Work/Log.md` is a table for your own
times.

* Day 0: this chapter and "Working in Lean".
* Days 1 to 4: the shift register, the accumulator, the multiply-accumulate
  cell. You read a specification and prove what it does.
* Day 5: "Writing a specification". The method for everything after it.
* Days 6 to 11: pipeline and sequencer, memory, repeater, systolic array.
  You write each from its page of the manual.
* Days 12 to 14: the slice-level machine. You specify its streams and some
  of its instructions, and program it by hand.
* Days 15 to 17: kernels, and two compiler passes that you write in Lean
  from their C++.
* Days 18 to 20: the checker, three ways to specify a pass, and a rule for
  schedules.
* Day 21: the cell-level machine. You read the largest proof.
* Day 22: the end-to-end theorem, and your claims table.
* After that: the chapter "Extending the machine" has as much homework as you
  want.

If you fall behind, skip challenge exercises first, then "Prove" exercises
after day 5. Do not skip a "Specify" by reading the definition in `Tau/`.
The tests tell you how far you are, and that is worth more than the
answer.

# Before day one

Play the first three worlds of the Natural Number Game, which takes about two
hours. The link is in the reading list.
