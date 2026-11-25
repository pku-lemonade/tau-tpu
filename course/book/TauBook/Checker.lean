import VersoManual
import Tau
import TauBook.SliceLevel
import TauBook.Kernels
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The checker" =>
*Terms to look up:* translation validation, symbolic execution, homomorphism.

*Sources:* `compiler/lib/Target/Place.cpp`, `Schedule.cpp` and `Route.cpp`,
for their opening comments; `course/architecture-manual.md`, section 3.4.

*Specify:* `course/Specs/OnTime.lean`.

*Read:* `Tau/IR/MemMap.lean`, `Tau/IR/Compiled.lean`,
`Tau/Check/Checker.lean`, `Tau/IR/Placed.lean`, `Tau/Check/Passes.lean`.

*Proofs:* `Tau/Proofs/Check/Sound.lean` and `Tau/Proofs/Check/Passes.lean`:
four short ones are exercises. `Tau/Proofs/SliceLevel/Map.lean`,
`Tau/Proofs/IR/Map.lean`, `Tau/Proofs/IR/MemMap.lean` and
`Tau/Proofs/IR/Placed.lean` are for reading.

*Time:* three days.

# The problem

The compiler has five passes. `tau-simplify` and `tau-unroll` rewrite the
kernel. You have seen a Lean copy of `tau-unroll`, and the rewrites that
`tau-simplify` makes. The other three are the back
end: `tau-place` decides where every buffer lives and which slice runs each
operation, `tau-schedule` decides the cycle of every instruction, and
`tau-route` decides on which stream each word travels. Read
the comment at the top of each file in `compiler/lib/Target/`. Together they
are a few hundred lines of heuristics, and they will change. Proving them
correct would be a large project that had to be redone with every change.

There is another way. Do not prove the compiler. Check each program it
produces, and prove the checker. This is called _translation validation_.

# The checker

{docstring Tau.Compiled}

{docstring Tau.check}

The checker runs the machine on the compiled program and runs the kernel,
both on names. Each run ends with an expression for every word of every
buffer. If the expressions agree after simplification, the program is
accepted.

# On the smallest example

Take `tinyChip`, `copyProgram` and `lateProgram` from the chapter on the
slice-level machine, and `reluKernel` from the chapter on kernels. To follow
along, put those definitions and the ones below in one file under
`course/Work/`.

The kernel the copy program should implement loads word 0 of buffer 0 and
stores it to word 0 of buffer 1.

```lean
def copyKernel : Kernel :=
  [ .stmt (.load 0 0 ⟨0, 0⟩),
    .stmt (.store 0 1 ⟨0, 0⟩) ]
```

A compiled program also says where the buffers live. Buffer 0 is at slice 0
and buffer 1 at slice 2, each one word long.

```lean
def tinyCompiled (prog : Program) (cycles : Nat) : Compiled where
  cfg := tinyChip
  memSizes := [1, 0, 1]
  map := [⟨0, 0, 1⟩, ⟨2, 0, 1⟩]
  prog := prog
  cycles := cycles
```

The two runs the checker makes, and their results:

```lean
example :
    machineExprs (tinyCompiled copyProgram 5)
      = some [[.init 0 0], [.init 0 0]] := by
  rfl

example :
    kernelExprs copyKernel [1, 1]
      = some [[.init 0 0], [.init 0 0]] := by
  rfl
```

Both say: buffer 0 ends as it started, and buffer 1 ends holding the word
that started in buffer 0. They agree, so:

```lean
example : check copyKernel [1, 1] (tinyCompiled copyProgram 5) = true := by
  rfl
```

The late program traps, so its run produces nothing and it is rejected:

```lean
example : machineExprs (tinyCompiled lateProgram 6) = none := by
  rfl

example : check copyKernel [1, 1] (tinyCompiled lateProgram 6) = false := by
  rfl
```

A program can also run without a trap and still be wrong. Against the kernel
that applies `relu`, the copy program is rejected, because the expressions
differ:

```lean
example : check reluKernel [1, 1] (tinyCompiled copyProgram 5) = false := by
  rfl
```

The checker has no rules about timing, stream reuse or traps. It does not
need them. It is the machine itself run on names instead of numbers, so
whatever the machine does with a program, the checker sees.

# Why one run is enough

The checker ran the machine once, on names. The theorem is about all inputs:

```lean
example (k : Kernel) (c : Compiled) (bufs : List (List (Word 4)))
    (h : check k (bufs.map List.length) c = true) :
    ∃ mem out,
      execute (wordSem 4) c.cfg c.prog c.cycles (c.image bufs Word.zero) = .ok mem ∧
      k.run (wordSem 4) bufs = some out ∧
      extract c.map mem Word.zero = out :=
  check_sound (wordSem 4) (wordSem_lawful 4) k c bufs Word.zero h
```

Read the conclusion in three parts. The machine, started from memory that
holds the buffers `bufs`, finishes with some memory `mem` and no trap. The
kernel on the same buffers finishes with some `out`. And the buffers read
back out of `mem` are `out`.

What bridges one run and all inputs is the observation from the chapter on
the slice-level machine: the machine never looks at its values. Stated
precisely: take any function `f` from one kind of value to another that
respects the operations.

{docstring Tau.Sem.Hom}

Then running the machine and applying `f` to the result is the same as
applying `f` first and running the machine. That is `execute_map`, and
`Kernel.run_map` says the same of kernels.

Evaluating an expression, `Expr.denote`, is such a function. So the run on
real words is the run on names, evaluated. Two runs that end with the same
expressions therefore end with the same words, for every input.

# The proofs

`Tau/Proofs/SliceLevel/Map.lean` proves `execute_map`. It is the longest
proof file so far and the least clever. It has one lemma for each function in
the machine, in the order in which they are defined, each saying that the
function commutes with `f`. Most are a case split followed by `simp`. Proofs
about real systems often look like this: long, shallow, and shaped exactly
like the code.

`Tau/Proofs/Check/Sound.lean` then assembles the theorem, in three lemmas of a
few lines each and one that puts them together.

You are not asked to write `execute_map`. It is the kind of proof an agent
does well: no idea in it is new after the first case, and Lean checks every
step. You are asked to know what it says, and to see that the whole checker
stands on it. If someone changed the machine so that one instruction looked
at a value, this is the proof that would stop, and the checker would be
wrong from that day on.

# Checking each pass on its own

`check` compares the finished program with the kernel. That covers all five
passes at once, so when it rejects it does not say which pass was wrong. And
it is not the usual way to say what a pass must do. The usual specification
of a compiler pass is: the output computes what the input computes.

So the compiler writes a file after every pass, and
`Tau/Check/Passes.lean` has one check for each pass. Each compares the
output of the pass with its input, in the same way as `check`: run both sides
on names and compare the expressions.

A program takes three forms on the way. A kernel you know. `tau-place`
produces instructions in order, with slices and addresses but no cycles and
no streams; this form and its meaning are in `Tau/IR/Placed.lean`:

{docstring Tau.Placed}

`tau-schedule` and `tau-route` both produce a `Compiled` program. The first
gives every word a stream to itself, on a chip with as many streams as that
takes, so that the schedule can be checked before any stream is shared. The
second fits the words onto the streams the chip has.

`tau-simplify` and `tau-unroll`, kernel to kernel:

{docstring Tau.checkKernels}

`tau-place`, kernel to placed program:

{docstring Tau.checkPlaced}

`tau-schedule`, placed program to compiled program:

{docstring Tau.checkScheduled}

`tau-route`, compiled program to compiled program:

{docstring Tau.checkRouted}

Each has a soundness theorem of the same shape as `check_sound`. For
example, for the scheduler:

```lean
example (pl : Placed) (c : Compiled) (bufs : List (List (Word 4)))
    (h : checkScheduled pl c = true) :
    ∃ mem mem',
      pl.execute (wordSem 4) (pl.image bufs Word.zero) = some mem ∧
      execute (wordSem 4) c.cfg c.prog c.cycles (c.image bufs Word.zero) = .ok mem' ∧
      extract c.map mem' Word.zero = extract pl.map mem Word.zero :=
  checkScheduled_sound (wordSem 4) (wordSem_lawful 4) pl c bufs Word.zero h
```

In words: the placed program can be carried out, the machine runs the timed
program without a trap, and the two end with the same buffers.

`passes_sound` chains the five theorems. If every pass is accepted, the
finished program computes the kernel, which is the conclusion of
`check_sound`.

Run the compiler on an example and check the five passes in order. `tau-check`
takes the input of a pass and its output. Each line prints `ACCEPT`.

```
compiler/build/bin/tauc examples/residual/kernel.mlir -o out
lake exe tau-check out/kernel.json out/simplified.json
lake exe tau-check out/simplified.json out/unrolled.json
lake exe tau-check out/unrolled.json out/placed.json
lake exe tau-check out/placed.json out/scheduled.json
lake exe tau-check out/scheduled.json out/compiled.json
```

Without the compiler, use `examples/residual/stages` in place of `out`.

A rejection names the faulty pass.

Notice what these checks do not ask. `checkScheduled` accepts any timed
program that computes what the placed program computes, even one that uses
different instructions. Nothing in Lean says what a valid schedule is. The
chapter "End to end" comes back to this.

# Three ways to specify a pass

You have now seen two of the three ways to say, in Lean, what a compiler
pass must do. This is the choice you will make most often on a real
compiler, once for every pass.

* *A copy.* You write the pass itself, as a Lean function. What gets proved:
  the copy keeps what is computed. What it costs: the C++ is only tested
  against the copy, and every change to the C++ must be made twice.
* *A check.* You write a function that compares the input and the output of
  the pass. What gets proved: when it says yes, the output computes what the
  input computes. What it costs: it says nothing about how the pass should
  work, and it can reject a correct output.
* *A rule.* You write a condition the output must meet, given the input.
  What gets proved: an output that meets the rule computes what the input
  computes. What it costs: the proof is hard, and the rule must be complete.

tau-tpu has a copy of one pass, `tau-unroll`, and a check for all five. It
has no rule. A copy fits a pass that is small, has one right output, and
rarely changes. A check fits a pass whose output is one of many right
answers, chosen by heuristics that will change: the check does not care how
the answer was found. A rule fits when somebody needs to be told what a right
answer is, which is what the writer of a scheduler needs.

`course/Specs/OnTime.lean` has you write one part of a rule for schedules:
every operand arrives on the cycle it is read. You do not prove it. You test
it against the machine.

# How to work through it

1. Read `Tau/IR/MemMap.lean`, `Tau/IR/Compiled.lean` and
   `Tau/Check/Checker.lean`. Redo the small example above in your scratch
   file with a program of your own.
2. Read the statements of `execute_map` and `Kernel.run_map`, and the proof
   of one case of `exec_map`, in `Tau/Proofs/SliceLevel/Map.lean`. Every
   other case is the same.
3. In `Exercises/Check/Sound.lean`, read the statements of the three lemmas
   that are given: `Kernel.run_of_exprs`, `execute_of_exprs` and
   `denote_of_sameExprs`. Then prove `check_sound` from them, and
   `check_safe`.
4. Read `Tau/IR/Placed.lean` and `Tau/Check/Passes.lean`. In
   `Exercises/Check/Passes.lean`, prove `checkKernels_sound` and
   `passes_sound`.
5. Run the five per-pass commands above on an example.
6. Read the opening comments of `Place.cpp`, `Schedule.cpp` and `Route.cpp`,
   and section 3.4 of the manual. Specify the rule in
   `course/Specs/OnTime.lean`.
7. Do the exercise "Choose".

# Lean you will need

* `unfold check at h` unfolds in the hypothesis `h`, not in the goal.
* `cases hx : e with` splits on `e` and records which case you are in as
  `hx`. When a check accepted, both of its runs succeeded; the cases in which
  one failed are closed by `simp [hx] at h`.
* `obtain ⟨mem, hrun, hx⟩ := lemma ...` takes apart what a lemma of the form
  "there is a `mem` such that ..." gives.
* `refine ⟨mem, _, hrun, hker, ?_⟩` supplies a five-part answer in which the
  second part is to be worked out by Lean and the last is left as the new
  goal.

# Exercises

*Specify.* `course/Specs/OnTime.lean`.

*State.* What would it mean for your rule to be right? State it: if the rule
accepts a program, the machine does not trap with an empty read. Do not
prove it. Then answer: which of the other six traps does your rule not
exclude, and what does a program that passes your rule still have to satisfy
to compute what the placed program computes?

*Choose.* For each of the five passes of tau-tpu, say which of the three ways
you would use if you were starting again, and why. Then do the same for five
passes tau-tpu does not have: constant folding, removal of stores that are
never read, a register allocator, a scheduler that calls an integer-program
solver, and an encoder that turns instructions into bits. For the encoder,
what is the property, and is it about one pass or about two? Then read
`course/Specs/ChooseAnswers.md` and note where you disagree.

*Prove.* `check_sound` and `check_safe` in `Exercises/Check/Sound.lean`;
`checkKernels_sound` and `passes_sound` in `Exercises/Check/Passes.lean`.

*Claims.* Add to `course/Work/Claims.md` a row for your rule and a row for what
it does not cover.

*By hand.* Break the compiler, one pass at a time. After each change rebuild
with `cmake --build compiler/build` and run `scripts/check-examples.sh`.
Write down which stage you expect to be the first rejected before you look,
and undo the change afterwards.

1. In `compiler/lib/Target/Schedule.cpp`, in the function `lag`, remove the
   `+ 1` from the timing rule.
2. In `compiler/lib/Target/Route.cpp`, delete the loop
   `while (numbers.count(stream)) ++stream;`, so that every word gets
   stream 0.
3. In `compiler/lib/Target/Place.cpp`, at the end of `placeComputed`, delete
   the line `emitWrite(flight, scratch);`, so that a value that should wait
   in memory is never written there.

*By hand.* The checker rejects some correct programs. Find one. A hint: the
simplifier knows three rewrites, and addition is commutative. Write the
kernel and a compiled program as Lean values, as in the small example, and
show `check` returns `false`. Then say what you would have to add, and what
would then have to be proved, for the checker to accept it.

*Challenge.* On a branch, as in the chapter on expressions, change `exec` in
the machine so that one instruction looks at a value, for example a `write` that does nothing when the word equals some
fixed word. You will need an equality test on `V`, which already tells you
something. Find where `exec_map` fails. Then explain, with a concrete
program and two inputs, why the checker would be unsound for the changed
machine.

# Hints

For `check_sound`: follow the outline. After the two `cases`, the three given
lemmas supply the machine's run, the kernel's run, and the equation between
the two tables.

For `checkKernels_sound`: the same with a kernel on both sides.

For `passes_sound`: `obtain` the conclusion of each of the five theorems.
Two neighbouring theorems speak about the same run in the middle, so their
results are equal: `Option.some.inj (h.symm.trans h')` for a run that gives
`some`, `Except.ok.inj` for one that gives `.ok`. Then chain the equations
with `rw`.

# Checkpoint

`lake build Exercises.Check.Sound Exercises.Check.Passes` prints no `sorry`
warning. Your rule agrees with the machine on the examples. You can say, in
two sentences, why checking one run on names proves something about every
input, and which property of the machine that relies on. You can say for a
pass you have never seen which of the three ways you would specify it.
