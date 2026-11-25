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

*Read:* `Tau/IR/MemMap.lean`, `Tau/IR/Compiled.lean`,
`Tau/Check/Checker.lean`, `Tau/IR/Placed.lean`, `Tau/Check/Passes.lean`,
`compiler/lib/Target/`.

*Solutions, not to be opened yet:* `Tau/Proofs/SliceLevel/Map.lean`,
`Tau/Proofs/IR/Map.lean`, `Tau/Proofs/IR/MemMap.lean`,
`Tau/Proofs/Check/Sound.lean`, `Tau/Proofs/IR/Placed.lean`,
`Tau/Proofs/Check/Passes.lean`.

*Time:* five days.

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

`Tau/Proofs/Check/Sound.lean` then assembles the theorem.

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

# How to work through it

1. Read `Tau/IR/MemMap.lean`, `Tau/IR/Compiled.lean` and
   `Tau/Check/Checker.lean`. Redo the small example above in your scratch
   file with a program of your own.
2. Do `Exercises/IR/Map.lean`. It is the smaller of the two "does not look at
   its values" proofs and shows the pattern.
3. Do `Exercises/SliceLevel/Map.lean`. Go in the order of the file. Each
   lemma is about one function of the machine; have that function's
   definition open next to the proof.
4. Do `Exercises/IR/MemMap.lean`, then `Exercises/Check/Sound.lean`.
5. Read `Tau/IR/Placed.lean` and `Tau/Check/Passes.lean`. Do
   `Exercises/IR/Placed.lean`, then `Exercises/Check/Passes.lean`.

# Lean you will need

* `cases i with`, one case per instruction, each handled the same way: unfold
  `exec`, split on the `if`s, split on the operands.
* `simp only [..., List.getElem?_map]` and its relatives. Most steps say that
  mapping a function over a list commutes with some list operation. Lean's
  library has these lemmas; `simp?` will name them.
* `Except.map` and `Option.map`. `(r.map f)` applies `f` inside a successful
  result and leaves a trap or `none` as it is.
* `obtain ⟨a, b⟩ := r`, to name the two parts of a pair.

# Exercises

*Guided.* `Exercises/IR/Map.lean`, `Exercises/SliceLevel/Map.lean`,
`Exercises/IR/MemMap.lean`, `Exercises/Check/Sound.lean`,
`Exercises/IR/Placed.lean`, `Exercises/Check/Passes.lean`.

*Open.* Break the compiler, one pass at a time. After each change rebuild
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

*Open.* The checker rejects some correct programs. Find one. A hint: the
simplifier knows three rewrites, and addition is commutative. Write the
kernel and a compiled program as Lean values, as in the small example, and
show `check` returns `false`. Then say what you would have to add, and prove,
for the checker to accept it.

*Challenge.* On a branch, as in the chapter on expressions, change `exec` in
the machine so that one instruction looks at a value, for example a `write` that does nothing when the word equals some
fixed word. You will need an equality test on `V`, which already tells you
something. Find where `exec_map` fails. Then explain, with a concrete
program and two inputs, why the checker would be unsound for the changed
machine.

# Hints

Every long proof in these files has an outline in the exercise file, above
its `sorry`. Read it first.

*`Exercises/IR/Map.lean`.*

* `lookup_map`: induction on the list; take the head pair apart with
  `obtain ⟨k, x⟩ := e`; unfold `List.lookup`; `split`.
* `bufGet_map`: `simp only [List.getElem?_map]`, then `cases` on whether the
  buffer exists.
* `matvecFrom_map`: induction on `n`; split on the two things matched.
* `Stmt.exec_map`: do the `load` case first and copy its shape. In each
  case, name the mapped environment's fields
  (`have hv : (env.map f).vars = env.vars.map (Prod.map id f) := rfl`),
  rewrite with them and with `lookup_map`, then `cases` on each lookup. Where
  a value is computed, rewrite backwards with the fact that `f` respects the
  operation, for example `← h.un`, and finish with `rfl`.
* `execStmts_map`, `execLoop_map`, `Kernel.exec_map`: induction on the list
  or the count; each uses the one before.

*`Exercises/SliceLevel/Map.lean`.*

* `State.sample_map`: unfold, `cases` on the direction, then on whether the
  stream and the slot exist.
* `exec_map`: one case per instruction. `simp only [exec, hrd]`, then
  `split` once for each `if`, then `cases` on each read. A case that returns
  a value ends with `simp [Except.map, mapResult, h.un]` or the like.
* `shiftPipe_map`: first show, by `rfl`, that the mapped pipe with the mapped
  result in front is the map of the original list. Then `List.getLast?_map`.
* `stepSlice_map`: `cases` on the list of due instructions: none, one, more.
* `inject_map`, `advanceRow_map`: unfold; `List.map_congr_left` reduces an
  equation between two maps over the same list to an equation between the
  functions at each element.
* `step_map`, `run_map`, `execute_map`: each uses the one before.

*`Exercises/IR/MemMap.lean`.*

* `image_map`, `extract_map`: `simp only [List.map_map]`, then
  `apply List.map_congr_left` and `intro`, twice, once for each level of
  nesting. `Function.comp` is `∘`; `simp only [Function.comp]` unfolds it.

*`Exercises/Check/Sound.lean`.*

* `range_map_getD`: `apply List.ext_getElem`, which asks for equal lengths
  and equal elements at each index.
* `symBufs_denote`, `Kernel.run_of_exprs`, `denote_of_sameExprs`: follow the
  outlines.
* `execute_of_exprs`: follow the outline. Three pieces of syntax are new.
  `unfold machineExprs at h` unfolds in the hypothesis `h`, not in the goal.
  `cases hx : e with` splits on `e` and records which case you are in as
  `hx`. `refine ⟨memE.map (List.map f), ?_, ?_⟩` supplies the memory the
  theorem says exists and leaves the two facts about it as new goals.
* `check_sound`: follow the outline. `obtain ⟨mem, hrun, hx⟩ := ...` takes
  apart what `execute_of_exprs` gives. `refine ⟨mem, _, hrun, hker, ?_⟩`
  supplies a five-part answer in which the second part is to be worked out by
  Lean and the last is left as the new goal.

*`Exercises/IR/Placed.lean` and `Exercises/Check/Passes.lean`.* Everything
here repeats a proof from the other files. `PInstr.exec_map` is `exec_map`
again with lookups in place of reads. `Placed.execute_of_exprs` is
`execute_of_exprs` again. The four soundness theorems are `check_sound` again
with different sides. `passes_sound` is new: `obtain` the conclusion of each
of the five theorems, note that two neighbours speak about the same run in
the middle, and chain the equations with `rw`.

# Checkpoint

The six exercise files build with no `sorry` warning: `lake build
Exercises.IR.Map Exercises.SliceLevel.Map Exercises.IR.MemMap
Exercises.Check.Sound Exercises.IR.Placed Exercises.Check.Passes`. You can say, in two
sentences, why checking one run on names proves something about every input,
and which property of the machine that relies on.
