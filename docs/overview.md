# Overview

This page says in words what tau-tpu sets out to show, what the parts are,
and where each part is defined in Lean. It is for reading the code without
taking the course.

The Lean files are the specification. This page names things and points to
them. It does not repeat a definition, so when you want to know exactly what
something does, open the file it names.

The course has a description of the chip in words and tables,
[`course/architecture-manual.md`](../course/architecture-manual.md). It is
what students specify from, it says less than the Lean does on purpose, and
it is not the specification.

## Two things, kept apart

tau-tpu does two things. Each has its own specification and its own
question.

| | 1. A machine | 2. A compiler for it |
|---|---|---|
| The question | Does the machine built from components do what the machine is specified to do? | Does a compiled program, run on the machine, compute what its kernel says? |
| Specification | The machine specification: what the chip does with a program, cycle by cycle. `execute` in `Tau/SliceLevel/Machine.lean`. | The kernel specification: what a kernel computes, with no chip in sight. `Kernel.run` in `Tau/IR/Kernel.lean`. |
| What is measured against it | The machine built from blocks, `cellExecute` in `Tau/CellLevel/Machine.lean`. | Every program the compiler produces, run by `execute`. |
| How | A theorem, once, for all programs. | A check, on each compiled program, and a theorem that the check can be trusted. |
| Main theorem | `cellExecute_eq` | `check_sound` |

The machine specification appears on both sides. In part 1 it is the
standard that the detailed machine must meet. In part 2 it is what "running a
compiled program" means, and the kernel specification is the standard.

`end_to_end` (`Tau/Proofs/EndToEnd.lean`) joins the two parts: a compiled
program that the check accepts, run on the machine built from blocks,
finishes without a trap and leaves in memory the buffers its kernel computes.

## The words

**Definition.** Lean code that says what something is or does. It runs.
Nothing proves a definition right: you read it and decide whether it says
what you intend.

**Specification.** A definition that is the standard: other things are
measured against it and it is measured against nothing. There are two, the
machine specification and the kernel specification.

**Theorem.** A statement about definitions, with a proof that Lean has
verified. It is proved once and holds for every input and every size.

**Check.** A definition that takes two programs, answers yes or no, and runs
once for every program the compiler produces. A check is a program, and a
program can be wrong, so each check has a theorem that says its yes can be
trusted. A no proves nothing: the program may still be right.

**Test.** A run on particular inputs: `tests/`, `scripts/check-examples.sh`.
It shows something for the inputs it ran and no others.

"Model" is not in this list because it is not a separate kind of thing. Every
definition here is a model of something outside Lean: the machine
specification is a model of a chip, and `Kernel.unroll` is a model of a C++
pass. This page avoids the word.

Definitions are under `Tau/<Area>/`. Theorems about them are under
`Tau/Proofs/<Area>/`. `Tau/Claims.lean` has every main statement named on
this page as a proposition of its own, so that all of them can be read in
one place without opening a proof.

## Part 1: the machine

| What | Definition | Theorems |
|---|---|---|
| The machine specification: each slice is one box with a delay | `step` (one cycle) and `execute` (a whole program) in `Tau/SliceLevel/Machine.lean` | the two derived properties below |
| The components | `Tau/Blocks/` | `Tau/Proofs/Blocks/`: for each block, its output at cycle `t` in terms of earlier inputs |
| The machine with each slice built from those components | `cellExecute` in `Tau/CellLevel/Machine.lean` | `cellExecute_eq`: it gives the same result as `execute` on every program |

`step` says what happens in one cycle. Two properties of many cycles follow
from it and are proved.

- **The timing rule** (`arrives_east` and `arrives_west` in
  `Tau/Proofs/SliceLevel/Timing.lean`). A result that the slice at `p`
  computes on cycle `t` is on its stream at the slice at `q` on cycle
  `t + delay + 1 + |q - p|`, if no other result is put on that stream in its
  path. This is the rule a person uses to write a schedule. Nothing else in
  the repository depends on it.
- **The machine does not look at its values** (`execute_map` in
  `Tau/Proofs/SliceLevel/Map.lean`). The machine moves and combines words but
  never decides anything from what a word holds. So one run on names tells
  what every run on real words does. Every check in part 2 rests on this.

## Part 2: the compiler

### What is to be shown

The compiler is C++ (`compiler/`) and none of it is proved. What is shown
instead is a statement about each program it produces:

> Put the buffers in memory, run the compiled program on the machine
> specification, and read the buffers back. The machine does not trap, and
> the buffers are the ones the kernel specification gives.

Putting buffers in memory and reading them back are `image` and `extract` in
`Tau/IR/MemMap.lean`. The statement in Lean is the conclusion of
`check_sound`.

### The three forms of a program

A program takes three forms on its way through the compiler. Each has a
definition of what it is and a definition of what it computes.

| Form | What it is | What it computes | Files `tauc` writes |
|---|---|---|---|
| Kernel | `Kernel` in `Tau/IR/Kernel.lean`: loads, operations and stores on buffers, with no slices and no time | `Kernel.run`, the kernel specification | `kernel.json`, `simplified.json`, `unrolled.json` |
| Placed | `Placed` in `Tau/IR/Placed.lean`: instructions in order, each with a slice; buffers have addresses | `Placed.execute` | `placed.json` |
| Compiled | `Compiled` in `Tau/IR/Compiled.lean`: instructions with a slice, a cycle and streams | `execute`, the machine specification | `scheduled.json`, `compiled.json` |

The placed form is a step between the two specifications. Nothing outside the
compiler is measured against it.

The same forms as files are described in [`formats.md`](formats.md). The
kernel as MLIR text is the `tau` dialect, defined in
`compiler/include/tau/Dialect/TauOps.td`.

### The checks

A check takes two programs and decides whether the second computes what the
first computes. There is one for the whole compiler and one for each pass.
They are in `Tau/Check/`, and their theorems are in `Tau/Proofs/Check/`.

| Covers | First program | Second program | Check | Theorem |
|---|---|---|---|---|
| the whole compiler | kernel | compiled | `check` | `check_sound` |
| `tau-simplify` | kernel | kernel | `checkKernels` | `checkKernels_sound` |
| `tau-unroll` | kernel | kernel | `checkKernels` | `checkKernels_sound` |
| `tau-place` | kernel | placed | `checkPlaced` | `checkPlaced_sound` |
| `tau-schedule` | placed | compiled | `checkScheduled` | `checkScheduled_sound` |
| `tau-route` | compiled | compiled | `checkRouted` | `checkRouted_sound` |

**What each theorem says.** If the check accepts, then on every buffer
contents the second program can be run to the end, and it ends with the
buffers that the first program ends with. For a pass this is the usual
specification of a compiler pass: the output computes what the input
computes.

**Two routes to one conclusion.** `check` alone gives the statement above.
So do the five per-pass checks together: `passes_sound` chains their
theorems. The per-pass route says in addition which pass was wrong when
something is rejected. `scripts/check-examples.sh` runs both.

**How a check works.** It runs both programs on names instead of numbers
(`Tau/IR/Expr.lean`), which gives for every word of every buffer an
expression that says how it was computed. It accepts if the two tables of
expressions are the same after simplifying (`Expr.simp` in
`Tau/Check/Simplify.lean`). Because neither program looks at its values,
equal expressions mean equal results on every input. This is called
translation validation.

**What a check does not ask.** It does not look at how a pass got from its
input to its output. `checkScheduled` accepts any timed program that computes
what the placed program computes, even one with different instructions.
There is no Lean statement of what a valid schedule or a valid routing is.

### One pass proved another way

A check verifies one output at a time. The other way to verify a pass is to
prove the pass itself, once. tau-tpu does this for one pass, on a copy of it
written in Lean.

`Kernel.unroll` (`Tau/Passes/Unroll.lean`) is a Lean copy of `tau-unroll`.
`Kernel.run_unroll` proves that unrolling does not change what a kernel
computes. The theorem is about the Lean function. That the C++ pass produces
what the Lean function produces is tested on the examples
(`tau-check --unroll`), not proved.

The final guarantee does not need this, since `checkKernels` already covers
the output of `tau-unroll`. It is there to show the second method on a pass
small enough to prove.

## How the theorems add up

```
kernel ─simplify→ kernel ─unroll→ kernel ─place→ placed ─schedule→ compiled ─route→ compiled
       checkKernels      checkKernels     checkPlaced     checkScheduled      checkRouted
└────────────────────────────────── check ──────────────────────────────────────────┘

compiled, on the machine specification  =  compiled, on the machine built from blocks
                                 cellExecute_eq
```

| Theorem | Says | Built from |
|---|---|---|
| `check_sound` | part 2, by the one check | |
| `passes_sound` | part 2, by the five checks | the five per-pass theorems |
| `cellExecute_eq` | part 1 | the block theorems |
| `end_to_end` | parts 1 and 2 | `check_sound`, `cellExecute_eq` |
| `end_to_end_passes` | parts 1 and 2 | `passes_sound`, `cellExecute_eq` |

What these theorems leave out, and what is only tested or trusted, is the
table under "What is proved" in the [README](../README.md#what-is-proved).
The two specifications head that list: nothing checks that they say what was
intended.

## Reading the code

In this order, each file's opening comment says what it defines:

1. `Tau/Data/Word.lean`, `Tau/Isa/Op.lean`, `Tau/Isa/Instr.lean`: values,
   operations, instructions.
2. `Tau/SliceLevel/Machine.lean`: the machine specification. Then
   `Tau/SliceLevel/Timing.lean`: the words the timing rule is stated with.
3. `Tau/IR/Kernel.lean`: the kernel specification.
4. `Tau/IR/MemMap.lean`, `Tau/IR/Placed.lean`, `Tau/IR/Compiled.lean`: the
   other two forms.
5. `Tau/IR/Expr.lean`, `Tau/Check/Checker.lean`, `Tau/Check/Passes.lean`:
   the checks.
6. `Tau/Blocks/` and `Tau/CellLevel/Machine.lean`: the machine built from
   components.
7. `Tau/Claims.lean`: every main statement. Nothing under `Tau/Proofs/` has
   to be read to know what is claimed.

The course in `course/` covers the same ground in a different order. It has
students write the definitions and the statements themselves, from a
description in words and from the C++, and leaves most proofs to be read.
