import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "End to end" =>
*Read:* `Tau/Claims.lean`; `tests/TauTest/Axioms.lean`; `Tau/Docs/README.md`,
sections 3 and 4, after you have finished your own.

*Proofs:* `Tau/Proofs/EndToEnd.lean`. All of them are exercises, and each is
a few lines.

*Time:* one day.

# The theorem

```lean
example (lanes : Nat) (s : Source) (c : Compiled) (bufs : List (List (Word lanes)))
    (h : check s (bufs.map List.length) c = true) :
    ∃ mem out,
      cellExecute c.cfg c.prog c.cycles (c.image bufs Word.zero) = .ok mem ∧
      s.run (wordSem lanes) bufs = some out ∧
      extract c.map mem Word.zero = out ∧
      s.timeline (wordSem lanes) bufs ⊆ c.timeline (wordSem lanes) bufs Word.zero :=
  end_to_end lanes s c bufs h
```

In words. Take a source program and a compiled program that the checker
accepts. Load any buffer contents into the machine and run the program on the
machine built from shift registers, memories, repeaters and
multiply-accumulate cells. The machine does not trap, and what it leaves in
memory is what the source program computes. And every word the source
program pins to a cycle is issued on that cycle.

The proof is a few lines. Each layer did its part: the checker is sound for
the slice-level machine, in what is computed and in when; the cell-level
machine equals the slice-level machine; and real words obey the simplifier's
laws.

`Tau/Proofs/EndToEnd.lean` and `Tau/Claims.lean` also contain
`end_to_end_passes`, which proves the same conclusion from the eight
per-pass checks (`passes_sound` and `passes_pins`) from "The checker" and
"Pins".

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
* It says nothing about Python. The source program is what the frontend
  recorded on one run. That the record is what the author of the Python file
  meant is tested on examples and not stated anywhere.
* Its last line is about the slice-level machine. The cell-level machine is
  proved to end with the same memory. That it issues the same words on the
  same cycles is not stated.
* A pin names a word and a cycle. The theorem does not say which slice
  issues the word.
* It trusts the code that reads JSON files into Lean values. If that code
  misreads a file, the checker checks the wrong program.
* It trusts the statement. `Source.run`, `Source.timeline`, `cellExecute`,
  `extract` and `Compiled.image` are definitions somebody wrote. Read them and decide
  whether they mean what the sentence above claims.
* It trusts the operations. `Lane.requant` is whatever
  `Tau/Data/Word.lean` says it is. Nothing checks that against an intention.
* It says nothing about how a pass did its work. A check asks whether the
  output computes what the input computes. No Lean statement says what a
  valid placement, schedule or routing is.
* It is about a model. No hardware is involved.
* It says nothing about speed. A program that takes a million cycles is as
  correct as one that takes twenty.

# Exercises

*Prove.* `Exercises/EndToEnd.lean`.

*Claims.* Bring `course/Work/Claims.md` up to date: one row for everything
you defined, stated, had proved, tested or decided in this course. Then
compare it with `Tau/Claims.lean`, which has every main statement of the
development as a named proposition, and with the table in section 4 of `Tau/Docs/README.md`,
which also says what is not claimed. Which rows of
that table did you not think of? The row about `source.json` is one that
most people miss.

*State.* Write one page, for someone who has not taken this course, that says
what `tau-check` printing `ACCEPT` guarantees and what it does not. Use no
Lean. Then give it to someone and ask them what they think is guaranteed.

# Where to go next

* Write down, in Lean, what a valid schedule of a placed program is: the same
  instructions, each operand read on the cycle the timing rule gives, and no
  two words in one stream slot. Then prove that a valid schedule computes what
  the placed program computes. `Tau/Proofs/SliceLevel/Timing.lean` is the
  first lemma. This is a large project.
* Prove something about the scheduler itself, in Lean: for instance, that a
  schedule built by `tau-schedule` from the output of `tau-place` is always
  valid in that sense. This is a research-sized problem. Start with groups of
  one operation.
* Lean-MLIR is a framework for verifying rewrites on MLIR-style
  representations, with far more automation than this course uses.
* CompCert is a C compiler proved correct in another proof assistant. Its
  register allocator is validated by a proved checker, which is the approach
  of the chapter on the checker.
* _Software Foundations_ is the standard introduction to proving things about
  programming languages.

# Checkpoint

You can state what a verified toolchain guarantees, and what it does not.
