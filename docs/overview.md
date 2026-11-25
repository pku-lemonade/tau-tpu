# Overview

This page says in words what the parts of tau-tpu are and where each one is
defined in Lean. It is for reading the code without taking the course.

The Lean files are the specification. This page names things and points to
them. It does not repeat a definition, so when you want to know exactly what
something does, open the file it names.

## The words

Everything written in Lean here is a definition or a theorem.

**Definition.** Lean code that says what something is or does. It runs.
Nothing proves a definition right: you read it and decide whether it says
what you intend.

In the wide sense of the word, every definition here is a *model*: Lean code
that stands for something outside Lean. The machine is a model of a chip, and
`Kernel.unroll` is a model of a C++ pass. What differs between definitions is
the role each plays.

| Role | The question it answers | Examples |
|---|---|---|
| Specification | What is right? Everything else is measured against it, and it is measured against nothing. | the machine (`step`, `execute`); what a kernel computes (`Kernel.run`) |
| Pass model | What does this pass of the C++ compiler do? It is measured against the specification. | `Kernel.unroll` |
| Check | Is this output of the compiler right? It takes the input and the output of a pass, answers yes or no, and runs once for every program the compiler produces. | `checkPlaced` |

So "model" says what a definition stands for, and "specification" says
whether it is the standard. The machine is both: a model of hardware that
does not exist, and the specification the compiler is held to. Where this
page says "model" without more, it means a pass model.

**Theorem.** A statement about definitions, with a proof that Lean has
verified. It is proved once and holds for every input and every size. A
specification, a pass model and a check are tied together by theorems:

- about a specification: a property that follows from it, such as the timing
  rule;
- about a pass model: its output computes what its input computes;
- about a check: when it answers yes, the output computes what the input
  computes.

A check is a program, and a program can be wrong. The theorem about a check
is what makes its yes worth trusting. A check that answers yes is not a
proof, but together with the theorem about that check it amounts to one, for
that one program and every buffer contents. A check that answers no proves
nothing: the program may still be right.

The word "specification" is also used for what a pass must do: its output
must compute what its input computes. Here that is not a separate definition.
It is the statement of the theorem about the pass's check.

**Test.** A run on particular inputs: `tests/`, `scripts/check-examples.sh`.
A test shows something for the inputs it ran and no others.

Definitions are under `Tau/<Area>/`. Theorems about them are under
`Tau/Proofs/<Area>/`.

## The machine

| What | Definition | Theorems |
|---|---|---|
| The hardware components | `Tau/Blocks/` | `Tau/Proofs/Blocks/`: for each block, its output at cycle `t` in terms of earlier inputs |
| The machine, each slice one box with a delay | `step` and `execute` in `Tau/SliceLevel/Machine.lean` | the timing rule and "does not look at its values", below |
| The machine, each slice built from blocks | `cellExecute` in `Tau/CellLevel/Machine.lean` | `cellExecute_eq`: it gives the same result as `execute` on every program |

`step` defines one cycle. Two properties of many cycles are derived from it.

- **The timing rule** (`arrives_east` and `arrives_west` in
  `Tau/Proofs/SliceLevel/Timing.lean`). A result that the slice at `p`
  computes on cycle `t` is on its stream at the slice at `q` on cycle
  `t + delay + 1 + |q - p|`, if no other result is put on that stream in its
  path. Whoever writes a schedule, by hand or in the compiler, is using this
  rule.
- **The machine does not look at its values** (`execute_map` in
  `Tau/Proofs/SliceLevel/Map.lean`). The machine moves and combines words but
  never decides anything from what a word holds. So one run on names tells
  what every run on real words does. The checks below rest on this.

## The three forms of a program

A program takes three forms on its way through the compiler. Each has a
definition of what it is and a definition of what it computes.

| Form | What it is | What it computes | Files `tauc` writes |
|---|---|---|---|
| Kernel | `Kernel` in `Tau/IR/Kernel.lean`: loads, operations and stores on buffers, with no slices and no time | `Kernel.run` | `kernel.json`, `simplified.json`, `unrolled.json` |
| Placed | `Placed` in `Tau/IR/Placed.lean`: instructions in order, each with a slice; buffers have addresses | `Placed.execute` | `placed.json` |
| Compiled | `Compiled` in `Tau/IR/Compiled.lean`: instructions with a slice, a cycle and streams | `execute`, the machine itself | `scheduled.json`, `compiled.json` |

`Kernel.run` is what "correct" means for everything after it.

The placed and compiled forms keep each buffer in the memory of some slice.
`Tau/IR/MemMap.lean` says where (`MemMap`), how buffer contents become memory
contents at the start (`image`), and how buffers are read back at the end
(`extract`).

The same forms as files are described in [`formats.md`](formats.md). The
kernel as MLIR text is the `tau` dialect, defined in
`compiler/include/tau/Dialect/TauOps.td`.

## The five passes

The passes are C++ (`compiler/`). None of the C++ is proved. Lean has two
things to say about a pass: a model of it, and a check of its output.

| Pass | From | To | Model | Check | Theorem about the check |
|---|---|---|---|---|---|
| `tau-simplify` | kernel | kernel | `Expr.simp`, on expressions only | `checkKernels` | `checkKernels_sound` |
| `tau-unroll` | kernel | kernel | `Kernel.unroll` | `checkKernels` | `checkKernels_sound` |
| `tau-place` | kernel | placed | none | `checkPlaced` | `checkPlaced_sound` |
| `tau-schedule` | placed | compiled | none | `checkScheduled` | `checkScheduled_sound` |
| `tau-route` | compiled | compiled | none | `checkRouted` | `checkRouted_sound` |
| all five | kernel | compiled | | `check` | `check_sound` |

The models are in `Tau/Passes/`, the checks in `Tau/Check/`, and the theorems
in the folders of the same names under `Tau/Proofs/`.

**What a check's theorem says.** If the check accepts, then on every buffer
contents the output of the pass can be run to the end, and it ends with the
buffers that the input of the pass ends with. This is the usual
specification of a compiler pass: output and input compute the same thing.

**What a check does not say.** It does not look at how the pass got from
input to output. `checkScheduled` accepts any timed program that computes
what the placed program computes, even one with different instructions.
There is no Lean statement of what a valid schedule or a valid routing is.

**How a check works.** It runs both sides on names instead of numbers
(`Tau/IR/Expr.lean`), which gives for every word of every buffer an
expression that says how it was computed. It accepts if the two tables of
expressions are the same after simplifying. Because neither side looks at
its values, equal expressions mean equal results on every input. This is
called translation validation.

**What a model's theorem says.** `Kernel.run_unroll`: unrolling a kernel does
not change what it computes. `Expr.denote_simp`: simplifying an expression
does not change its value. These are about the Lean functions. That the C++
`tau-unroll` produces what `Kernel.unroll` produces is tested on the examples
(`tau-check --unroll`), not proved.

## How the theorems add up

```
kernel ─simplify→ kernel ─unroll→ kernel ─place→ placed ─schedule→ compiled ─route→ compiled
       checkKernels      checkKernels     checkPlaced     checkScheduled      checkRouted
└────────────────────────────────── check ──────────────────────────────────────────┘
```

- `passes_sound` (`Tau/Proofs/Check/Passes.lean`): if all five per-pass
  checks accept, the compiled program, run on the slice-level machine,
  computes the kernel. `check_sound` reaches the same conclusion from the one
  check of the whole compiler.
- `cellExecute_eq`: the cell-level machine gives the same result.
- `end_to_end` and `end_to_end_passes` (`Tau/Proofs/EndToEnd.lean`) put these
  together: an accepted program, run on the machine built from blocks,
  finishes without a trap and leaves in memory the buffers the kernel
  computes.

What these theorems leave out, and what is only tested or trusted, is the
table under "What is proved" in the [README](../README.md#what-is-proved).

## Reading the code

In this order, each file's opening comment says what it defines:

1. `Tau/Data/Word.lean`, `Tau/Isa/Op.lean`, `Tau/Isa/Instr.lean`: values,
   operations, instructions.
2. `Tau/SliceLevel/Machine.lean`: the machine. Then the statements in
   `Tau/Proofs/SliceLevel/Timing.lean`.
3. `Tau/IR/Kernel.lean`, `Tau/IR/MemMap.lean`, `Tau/IR/Placed.lean`,
   `Tau/IR/Compiled.lean`: the three forms.
4. `Tau/IR/Expr.lean`, `Tau/Check/Checker.lean`, `Tau/Check/Passes.lean`:
   the checks.
5. The statements, not the proofs, of `check_sound`, the theorems in
   `Tau/Proofs/Check/Passes.lean`, and `end_to_end`.
6. `Tau/Blocks/`, `Tau/CellLevel/Machine.lean`, and the statement of
   `cellExecute_eq`.

The course in `course/` covers the same ground in a different order, with
the proofs as exercises.
