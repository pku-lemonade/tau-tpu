import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Start here" =>
This course teaches Lean 4 by taking you through one real development from
the bottom up. The development is tau-tpu: a small tensor processor, a
compiler for it, and proofs that connect the two. By the end you will have
proved, or at least read closely, a theorem that says a compiled program
computes what its source says, on a model of the hardware built from
components you specified yourself.

# Who this is for

You can program, and you have seen proof by induction. You have not
necessarily used Lean, and you have not necessarily taken a course in digital
design, computer architecture or compilers.

The course teaches the Lean. It does not teach the other three subjects.
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

Before learning any Lean, see the finished thing work. Build everything as
the repository's `README.md` describes. Then, from the root of the
repository:

```
compiler/build/bin/tauc examples/linear/kernel.mlir -o out --print-mlir
```

This compiles a quantized linear layer. It prints the program after each of
the compiler's five passes and writes six files into `out/`. Open
`out/compiled.json` and read the `program` list. Each entry is one line of
the timetable: a slice, a cycle, and an instruction.

```
.lake/build/bin/tau-check out/kernel.json out/compiled.json
```

This prints `ACCEPT`. That one word is backed by a theorem: for every
possible input, running that program on the chip gives what the kernel
computes. Now open `out/compiled.json`, find the last instruction, add one to
its `time`, and run the check again. It prints `REJECT` and says why.

```
.lake/build/bin/tau-sim out/compiled.json examples/linear/buffers.json
```

This runs the program and prints the buffers. The last buffer is the result.
The simulator is not a separate piece of software. It is the Lean
specification of the chip, compiled.

If you have not built the compiler, skip the first command and use the
folder `examples/linear/stages/` in place of `out/`. It holds the same six
files. The chapters on kernels, on expressions and on the checker ask you to
run the compiler again; the repository's `docker/` folder has a container
with everything installed, and VS Code can open the repository inside it
("Reopen in Container").

You do not need to understand any of this yet. Come back to these three
commands after the chapter on the slice-level machine and after the chapter
on the checker, and see how much more they say.

# How each chapter works

Every chapter has the same parts.

* *Terms to look up*. Look them up in the reading list.
* *Read*: definition files. Open them now.
* *Solutions*: proof files. They are the solutions to the chapter's guided
  exercises. Do not open them until the list in "Working in Lean" tells you
  to.
* *The idea*, with something you can run.
* *What to prove*, with the statement of the main theorem.
* *How to work through it*: numbered steps. Do them in order.
* *Exercises*, in three kinds.
* *Hints*, to read only when stuck.
* *Checkpoint*: how to tell you are done.

The three kinds of exercise are these.

* *Guided.* A file under `course/Exercises/` in which the proofs have been
  replaced by `sorry`. Proofs that are a single `rfl` are left in, and a long
  proof is replaced by a `sorry` with an outline above it. You fill the
  proofs in. The solution is the file of the same name under `Tau/Proofs/`.
* *Open.* You write the definition or the statement yourself, in a file of
  your own. There is no solution to compare with. This is the hard part and
  the useful part: deciding what a specification should say is a skill that a
  proof assistant cannot check for you.
* *Challenge.* Larger, and optional.

Do every guided exercise and at least one open exercise per chapter.

# How the Lean code is laid out

Definitions and theorems live in separate trees.
`Tau/Blocks/ShiftRegister.lean` says what a shift register is.
`Tau/Proofs/Blocks/ShiftRegister.lean` says what is true of it. When you want
to know what something does, read the first kind of file. It contains no
proofs.

# A plan

One day means about six hours of focused work. The numbers are estimates, and
nobody has yet been timed.

* Day 0: this chapter and "Working in Lean".
* Days 1 to 12: seven chapters on hardware blocks. The repeater takes two of
  those days and the systolic array three.
* Days 13 to 15: the slice-level machine. No proofs. You program it by hand.
* Days 16 to 19: kernels, a compiler pass, expressions, a simplifier.
* Days 20 to 24: the checker. The longest proofs of the course.
* Days 25 to 29: the cell-level machine and refinement.
* Day 30: the end-to-end theorem.
* After that: the chapter "Extending the machine" has as much homework as you
  want.

If you fall behind, skip challenge exercises first, then the open exercises
of the block chapters. Do not skip a guided exercise file by reading its
solution. Read one line of the solution and go back to work.

# Before day one

Play the first three worlds of the Natural Number Game, which takes about two
hours. The link is in the reading list.
