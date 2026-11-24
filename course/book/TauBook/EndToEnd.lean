import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "End to end" =>
*Read:* `tests/TauTest/Axioms.lean`.

*Solutions, not to be opened yet:* `Tau/Proofs/EndToEnd.lean`.

*Time:* one day.

# The theorem

```lean
example (lanes : Nat) (k : Kernel) (c : Compiled) (bufs : List (List (Word lanes)))
    (h : check k (bufs.map List.length) c = true) :
    ∃ mem out,
      cellExecute c.cfg c.prog c.cycles (c.image bufs Word.zero) = .ok mem ∧
      k.run (wordSem lanes) bufs = some out ∧
      extract c.map mem Word.zero = out :=
  end_to_end lanes k c bufs h
```

In words. Take a kernel and a compiled program that the checker accepts. Load
any buffer contents into the chip and run the program on the machine built
from shift registers, memories, sequencers and multiply-accumulate cells. The
machine does not trap, and what it leaves in memory is what the kernel
computes.

The proof is three lines. Each layer did its part: the checker is sound for
the slice-level machine, the cell-level machine equals the slice-level
machine, and real words obey the simplifier's laws.

# How to work through it

1. Do `Exercises/EndToEnd.lean`. Each proof names the theorems from earlier
   chapters and does nothing else. If you know what each earlier theorem
   says, this takes an hour.
2. In your scratch file run `#print axioms Tau.end_to_end`.
3. Go back to the three commands in "Start here" and run them again. Say what
   each one does, in terms of definitions you have now read.

# What it rests on

`#print axioms Tau.end_to_end` lists three axioms that almost every Lean
development uses, and nothing else. In particular there is no `sorryAx`,
which is what an unfinished proof would leave behind. The file
`tests/TauTest/Axioms.lean` makes the build fail if that list changes.

# What it does not say

Being exact about the limits of a theorem is part of the skill.

* It says nothing about the C++ compiler. If the compiler is wrong, its
  output is rejected. The theorem is about accepted programs only.
* It trusts the code that reads JSON files into Lean values. If that code
  misreads a file, the checker checks the wrong program.
* It trusts the statement. `Kernel.run`, `cellExecute`, `extract` and
  `Compiled.image` are definitions somebody wrote. Read them and decide
  whether they mean what the sentence above claims.
* It trusts the operations. `Lane.requant` is whatever
  `Tau/Data/Word.lean` says it is. Nothing checks that against an intention.
* It is about a model. No hardware is involved.
* It says nothing about speed. A program that takes a million cycles is as
  correct as one that takes twenty.

# Exercises

*Guided.* `Exercises/EndToEnd.lean`.

*Open.* Write one page, for someone who has not taken this course, that says
what `tau-check` printing `ACCEPT` guarantees and what it does not. Use no
Lean. Then give it to someone and ask them what they think is guaranteed.

# Where to go next

* Prove something about the scheduler itself, in Lean: for instance, that a
  schedule built by `tau-schedule` from the output of `tau-place` always
  satisfies the timing rule. This is a research-sized problem. Start with
  groups of one operation.
* Lean-MLIR is a framework for verifying rewrites on MLIR-style
  representations, with far more automation than this course uses.
* CompCert is a C compiler proved correct in another proof assistant. Its
  register allocator is validated by a proved checker, which is the approach
  of the chapter on the checker.
* _Software Foundations_ is the standard introduction to proving things about
  programming languages.

# Checkpoint

You can state what a verified toolchain guarantees, and what it does not.
