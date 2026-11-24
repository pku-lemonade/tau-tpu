import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Start here" =>
This course teaches Lean 4 by taking you through one real development from the
bottom up. The development is tau-tpu: a small tensor processor, a compiler
for it, and proofs that connect the two. By the end you will have proved, or
at least read closely, a theorem that says a compiled program computes what
its source says, on a model of the hardware built from components you
specified yourself.

# Who this is for

You can program, and you have seen proof by induction. You have not
necessarily taken a course in digital design, computer architecture or
compilers. Where a chapter needs a term from one of those fields it names the
term under "Terms to look up" and does not explain it. The reading list at the
end of the book says where to look.

# What tau-tpu is

A tau-tpu chip is a row of _slices_. Each slice does one kind of job: store
words, do arithmetic on them, rearrange them, or multiply by a matrix. Between
the slices run _streams_, which carry words east or west, one slice per cycle.

A program for the chip is a timetable. It lists every instruction together
with the slice that executes it and the cycle on which it does so. The chip
has no branches, no queues, and nothing that waits. If an instruction looks
for its operand on a stream one cycle too early, the operand is not there yet
and the chip traps.

Deciding the timetable is the compiler's job. This kind of design is called
_statically scheduled_. It follows the tensor streaming processors described
by Abts and others at ISCA 2020 and ISCA 2022.

# The tour

Before learning any Lean, see the finished thing work. From the root of the
repository, build the tools and the compiler as the README describes, then
run:

```
compiler/build/bin/tauc examples/linear/kernel.mlir -o out --print-mlir
.lake/build/bin/tau-check out/kernel.json out/compiled.json
.lake/build/bin/tau-sim out/compiled.json examples/linear/buffers.json
```

The first command compiles a quantized linear layer and prints it after the
compiler's passes. Open `out/compiled.json` and read the `program` list. Each
entry is one line of the timetable.

The second command prints `ACCEPT`. That one word is backed by a theorem: for
every possible input, running that program on the chip gives what the kernel
computes. Now edit one `time` in `out/compiled.json`, add one to it, and run
the check again.

The third command runs the program on the simulator. The simulator is not a
separate piece of software. It is the Lean specification of the chip,
compiled.

# How to work

* Read each chapter, then read the Lean files it names, in VS Code, with the
  cursor moving through the proofs so that you can watch the goal change.
* Do the guided exercises: files under `course/Exercises/` in which every
  proof has been replaced by `sorry`.
* Do at least one open exercise per chapter. In an open exercise you write
  the definition or the statement yourself. This is the hard part and the
  useful part.

Solutions to the guided exercises are the files of the same name under
`Tau/Proofs/`.

# How the Lean code is laid out

Definitions and theorems live in separate trees. `Tau/Blocks/ShiftRegister.lean`
says what a shift register is. `Tau/Proofs/Blocks/ShiftRegister.lean` says
what is true of it. When you want to know what something does, read the first
kind of file. It contains no proofs.

# Before day one

Play the first few worlds of the Natural Number Game, and read the first two
chapters of _Functional Programming in Lean_. Both are in the reading list.
