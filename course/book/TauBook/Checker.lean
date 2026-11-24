import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The checker" =>
*Terms to look up:* translation validation, symbolic execution, homomorphism.

*Files:* `Tau/Check/Checker.lean`, `Tau/Check/Stages.lean`,
`Tau/Proofs/SliceLevel/Map.lean`, `Tau/Proofs/IR/Map.lean`,
`Tau/Proofs/Check/Sound.lean`, `Tau/Proofs/Check/Stages.lean`,
`compiler/lib/Target/`.

# The problem

The compiler's back end decides where every buffer lives, which slice runs
each operation, on which cycle, and on which stream each word travels. It
does so in three passes: `tau-place`, `tau-schedule` and `tau-route`. Read the
comment at the top of each file in `compiler/lib/Target/`. Together they are
a few hundred lines of heuristics, and they will change. Proving it correct would be
a large project that had to be redone with every change.

There is another way. Do not prove the compiler. Check each program it
produces, and prove the checker.

# The checker

{docstring Tau.check}

The checker runs the machine on the compiled program and runs the kernel,
both over expressions. Each run ends with an expression for every word of
every buffer. If the expressions agree after simplification, the program is
accepted.

The checker has no rules about timing, stream reuse or traps. It does not
need them. It is the machine of chapter 8 run on names instead of numbers, so
whatever the machine does with a program, the checker sees.

# Why one run is enough

The checker ran the machine once. The theorem is about all inputs:

```lean
example (k : Kernel) (c : Compiled) (bufs : List (List (Word 4)))
    (h : check k (bufs.map List.length) c = true) :
    ∃ mem out,
      execute (wordSem 4) c.cfg c.prog c.cycles (c.image bufs Word.zero) = .ok mem ∧
      k.run (wordSem 4) bufs = some out ∧
      extract c.map mem Word.zero = out :=
  check_sound (wordSem 4) (wordSem_lawful 4) k c bufs Word.zero h
```

What bridges the gap is the observation from chapter 8: the machine never
looks at its values. Stated precisely: take any function `f` from one kind of
value to another that respects the operations. Then running the machine and
applying `f` to the result is the same as applying `f` first and running the
machine. That is `execute_map`, and `Kernel.run_map` says the same of kernels.

Evaluating an expression is such a function. So the run on real words is the
run on expressions, evaluated. Two runs that end with the same expressions
therefore end with the same words, for every input.

# The proofs

`Tau/Proofs/SliceLevel/Map.lean` proves `execute_map`. It is the longest
proof file so far and the least clever. It has one lemma for each function in
the machine, in the order in which they are defined, each saying that the
function commutes with `f`. Most are a case split followed by `simp`. Proofs
about real systems often look like this: long, shallow, and shaped exactly
like the code.

`Tau/Proofs/Check/Sound.lean` then assembles the theorem in about thirty
lines.

# Checking each pass on its own

When `check` rejects a finished program it does not say which pass was
wrong. So the compiler writes a file after every pass, and each file has its
own check against the kernel. They are in `Tau/Check/Stages.lean`.

The first two passes produce kernels:

{docstring Tau.checkKernels}

`tau-place` produces instructions in order, with slices and addresses but no
cycles and no streams:

{docstring Tau.Placed}

{docstring Tau.checkPlaced}

`tau-schedule` adds cycles. Its output is checked by `check` itself, using a
routing that cannot be wrong: every word gets a stream to itself.

Run the compiler on an example and check the five files in order:

```
compiler/build/bin/tauc examples/residual/kernel.mlir -o out
for f in simplified unrolled placed scheduled compiled; do
  .lake/build/bin/tau-check out/kernel.json out/$f.json
done
```

The soundness proofs in `Tau/Proofs/Check/Stages.lean` repeat the pattern of
`check_sound`. The placed level needs its own version of the key lemma,
`Placed.execute_map`, and nothing else is new.

# Exercises

*Guided.* `Exercises/IR/Map.lean` first, since it is the smaller of the two,
then `Exercises/SliceLevel/Map.lean`, then `Exercises/Check/Sound.lean`, then
`Exercises/Check/Stages.lean`. Budget five days.

*Open.* Break the compiler, one pass at a time. In
`compiler/lib/Target/Schedule.cpp` remove the `+ 1` from the timing rule,
rebuild, and run `scripts/check-examples.sh`. Note which stage is the first
to be rejected. Undo that and break `Route.cpp` so that every word gets
stream 0. Then break `Place.cpp` so that a value that should wait in memory
does not. In each case predict the first rejected stage before you look.

*Open.* The checker rejects some correct programs. Find one. Hint: the
simplifier knows three rewrites, and `add` is commutative. Then say what you
would have to add, and prove, for the checker to accept it.

*Challenge.* Change `exec` in the machine so that one instruction looks at a
value, for example a `write` that does nothing when the word is all zeros.
Find where `exec_map` fails. Then explain why the checker would be unsound
for the changed machine, with a concrete program.

# Checkpoint

You understand translation validation, you have proved a checker sound, and
you know the property of the machine that the proof rests on.
