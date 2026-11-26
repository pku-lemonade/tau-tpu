# The Lean specification (`spec/`)

`spec/` is tau-tpu's verified side: the Lean 4 specification of the machine
and programs (`Tau/`), the executable CLI tools (`tools/`: `tau-sim` and
`tau-check`), and the compile-time test suite (`tests/`).

The prose design documents live in [`docs/`](../docs/README.md). The
untrusted Python + MLIR compiler lives in [`compiler/`](../compiler/README.md).

Lean paths below start inside `spec/Tau/`: `IR/Source.lean` is
`spec/Tau/IR/Source.lean`.

Contents:
- [The specification](#the-specification)
- [The map](#the-map)
- [Reading order](#reading-order)
- [Status](#status)

## The specification

### Four kinds of text

| Kind of text | Where | What it is for | Who judges it |
|---|---|---|---|
| Doc | `../docs/` | The intent, in words and tables, as a designer would write it. | A person, against what was meant. |
| Definition | `Tau/<Area>/` | The specification itself, in Lean. It runs: the simulator and the checker are these definitions, compiled. | A person, against the docs; and the docs' tables, run as tests. |
| Statement | `Tau/Claims.lean` | Every main theorem as a named proposition, readable without a proof. | A person: is this what a user relies on? |
| Proof | `Tau/Proofs/<Area>/` | Why each statement is true. | Lean. |

### Inside and outside

Everything outside `spec/Tau/` is measured against it and specified by it.

| Outside | What it is | How it is held to `spec/Tau/` |
|---|---|---|
| `compiler/` | Python frontend + C++/MLIR compiler | each file it writes is judged by a check from `Check/`; Python traces are compared with the compiler and with `Tau` |
| `tools/` | `tau-sim` and `tau-check` | they are the definitions, with a command line |
| `tests/`, `examples/` | runs on particular inputs | |
| `course/` | a course in writing all of this | its students write the definitions from the docs and compare with the ones in `spec/Tau/`; `course/tests/` runs the docs' tables on `spec/Tau/` and checks that every exercise can be solved |

Nothing in `spec/Tau/` depends on anything outside it.

### Two specifications

tau-tpu specifies two things. Each has its own question.

| | 1. The machine | 2. The path to it |
|---|---|---|
| Doc | `docs/Machine.md` | `docs/Programs.md`, `docs/Compiler.md` |
| The question | Does the machine built from components do what the slice-level machine says it does? | Does a compiled program, run on the machine, compute what its source says, when its source says? |
| Specification | The slice-level machine: what the machine does with a program, cycle by cycle, with each slice one box with a delay. `execute` in `Machine/SliceLevel.lean`. | The source specification: what a program computes and on which cycles, with no machine in sight. `Source.run` and `Source.timeline` in `IR/Source.lean`. |
| Measured against it | The cell-level machine, with each slice built from blocks: `cellExecute` in `Machine/CellLevel.lean`. | Every program a compiler produces, run by `execute`. |
| How | A theorem, once, for all programs. | A check, on each compiled program, and theorems that the check can be trusted. |
| Main theorem | `cellExecute_eq` | `check_sound`, `check_pins` |

`Machine/SliceLevel.lean` appears on both sides. In part 1 it is the standard that
`Machine/CellLevel.lean` must meet. In part 2 it is what "running a compiled
program" means, and the source specification is the standard.

`end_to_end` (`Proofs/EndToEnd.lean`) joins the two.

### The words

**Definition.** Lean code that says what something is or does. It runs.
Nothing proves a definition right: you read it and decide whether it says
what the doc intends.

**Specification.** A definition that is the standard: other things are
measured against it and it is measured against nothing but its doc. There
are two, named above.

**Theorem.** A statement about definitions, with a proof that Lean has
verified. It is proved once and holds for every input and every size.

**Check.** A definition that takes two programs, answers yes or no, and runs
once for every program a compiler produces. A check is a program, and a
program can be wrong, so each check has theorems that say its yes can be
trusted. A no proves nothing: the program may still be right.

**Test.** A run on particular inputs. It shows something for the inputs it
ran and no others.

**Pin, event, timeline.** A pin is a cycle attached to one statement of a
program. An event is a word and the cycle it is issued on. A timeline is the
events of one run. `Isa/Event.lean`.

"Model" is not in this list because it is not a separate kind of thing. Every
definition here is a model of something outside Lean.

## The map

### Part 1: the machine

| `docs/Machine.md` | Definition | Theorems |
|---|---|---|
| 1, lanes and words | `Isa/Word.lean` | `Proofs/Isa/Word.lean` |
| 2, the blocks | `Blocks/` | `Proofs/Blocks/`: for each block, its output at cycle `t` in terms of earlier inputs |
| 3.1 to 3.3 and 3.5 to 3.8, the slice-level machine | `Isa/Op.lean`, `Isa/Instr.lean`; `step` and `execute` in `Machine/SliceLevel.lean` | `execute_map` (`Proofs/Machine/SliceLevel.lean`) |
| 3.4, the timing rule | derived from `step`; stated with `Machine/Timing.lean` | `arrives_east`, `arrives_west` (`Proofs/Machine/Timing.lean`) |
| 3.9, what a slice issues | `issues` in `Machine/Issues.lean` | `issues_map` (`Proofs/Machine/Issues.lean`) |
| 3.10, the image | `Program.encode`, `Image.decode` in `Isa/Encode.lean` | `Image.decode_encode` (`Proofs/Isa/Encode.lean`) |
| 4, the cell-level machine | `cellExecute` in `Machine/CellLevel.lean` | `cellExecute_eq` (`Proofs/Machine/CellLevel.lean`) |

Two of these carry everything else.

- **The machine does not look at its values** (`execute_map`,
  `issues_map`). It moves and combines words but never decides anything from
  what a word holds. So one run on names tells what every run on real words
  computes, and on which cycle it issues each word. Every check in part 2
  rests on this.
- **Refinement** (`cellExecute_eq`). The cell-level machine, built from blocks,
  gives on every program the result the slice-level machine gives.

The timing rule is proved from `step` and nothing depends on it. It is the
rule a person uses to write a schedule.

### Part 2: the path to the machine

**The IRs.**

| `docs/Compiler.md` 2, IR | Definition | What it computes, and when |
|---|---|---|
| Source | `Source` in `IR/Source.lean` | `Source.run`, `Source.timeline` |
| Kernel | `Kernel` in `IR/Kernel.lean` | `Kernel.run`, `Kernel.timeline` |
| Placed | `Placed` in `IR/Placed.lean` | `Placed.execute`, `Placed.timeline` |
| Compiled | `Compiled` in `IR/Compiled.lean` | `execute`, `Compiled.timeline` |

The memory map, with `image` to load buffers and `extract` to read them
back, is `IR/MemMap.lean`. Running on names is `Check/Expr.lean`.

**The checks.** Compiler 5 says what every step must keep: the buffers, and
the words issued on fixed cycles. A check decides that for one input and
one output, as Compiler 7 describes. There is one for the whole path and one
for each step.

| Step | From | To | Check | Theorems |
|---|---|---|---|---|
| all of them | source | compiled | `check` | `check_sound`, `check_pins` |
| inline | source | kernel | `checkInlined` | `checkInlined_sound`, `checkInlined_pins` |
| simplify, unroll | kernel | kernel | `checkKernels` | `checkKernels_sound`, `checkKernels_pins` |
| place | kernel | placed | `checkPlaced` | `checkPlaced_sound`, `checkPlaced_pins` |
| schedule | placed | compiled | `checkScheduled` | `checkScheduled_sound`, `checkScheduled_pins` |
| route, slice, fold | compiled | compiled | `checkRouted` | `checkRouted_sound`, `checkRouted_pins` |
| encode | compiled | compiled, decoded from the image | `checkRouted` | the same |

The checks are in `Check/`. `Check/Checker.lean` has `check` and what all of
them share: `sameExprs` for the buffers, `covers` for the timelines, `agree`
for both. (`Proofs/Check/Checker.lean` proves `check_sound` and `check_pins`;
`Proofs/Check/Passes.lean` proves the per-pass theorems.)

Each check has two theorems. `_sound`: if the check accepts, then on every
buffer contents the output can be run to the end and ends with the buffers
the input ends with. `_pins`: the timeline of the output contains the
timeline of the input.

`passes_sound` and `passes_pins` chain the per-step theorems: if every step
is accepted, the result is that of `check_sound` and `check_pins`, reached
one step at a time. The per-step route says in addition which step was wrong.

**Two steps proved another way.** A check judges one output at a time. The
other way is to prove the step itself, once, on a copy of it written in
Lean.

| Step | Copy | Theorems |
|---|---|---|
| unroll | `Kernel.unroll` in `IR/Unroll.lean` | `Kernel.run_unroll`, `Kernel.timeline_unroll` |
| encode | `Program.encode` in `Isa/Encode.lean` | `Image.decode_encode` |

These theorems are about the Lean functions. That a compiler produces what
they produce is a test (`tau-check --unroll`, `tau-check --encode`). The
checks already cover both steps; the copies are there to show the second
method on steps small enough for it.

### How the theorems add up

```
source ─inline→ kernel ─simplify→ kernel ─unroll→ kernel ─place→ placed
     checkInlined    checkKernels     checkKernels     checkPlaced

placed ─schedule→ compiled ─route→ compiled ─slice→ compiled ─fold→ compiled ─encode→ image
      checkScheduled      checkRouted      checkRouted     checkRouted     checkRouted

└──────────────────────────────── check ─────────────────────────────────────┘

compiled, on Machine/SliceLevel.lean        =  compiled, on Machine/CellLevel.lean
                               cellExecute_eq
```

| Theorem | Says | Built from |
|---|---|---|
| `check_sound`, `check_pins` | part 2, by the one check | |
| `passes_sound`, `passes_pins` | part 2, by the per-step checks | the per-step theorems |
| `cellExecute_eq` | part 1 | the block theorems |
| `end_to_end` | parts 1 and 2 | `check_sound`, `check_pins`, `cellExecute_eq` |
| `end_to_end_passes` | parts 1 and 2 | `passes_sound`, `passes_pins`, `cellExecute_eq` |

### The folders

In `spec/Tau/`, in dependency order: a folder imports only from the folders
above it, and `spec/Tau.lean` lists the modules in the same order.

| Folder | Contents |
|---|---|
| `Blocks/` | Clocked components: shift register, accumulator, multiply-accumulate, pipeline, memory, sequencer, repeater, systolic array. |
| `Isa/` | Lanes and words (`Word.lean`), slice kinds, operations (`Op.lean`), instructions and programs (`Instr.lean`, whose entries are the repeater's), events (`Event.lean`), and the image (`Encode.lean`). |
| `Machine/` | The machine: the slice-level machine (`SliceLevel.lean`), the timing rule (`Timing.lean`), issued words (`Issues.lean`), and the cell-level machine, built from blocks (`CellLevel.lean`). |
| `IR/` | The four IRs of a program (`Source.lean`, `Kernel.lean`, `Placed.lean`, `Compiled.lean`), the memory map (`MemMap.lean`), and the Lean copy of unroll (`Unroll.lean`). |
| `Check/` | Symbolic expressions (`Expr.lean`), expression simplification (`Simplify.lean`), and the checks (`Checker.lean`, `Passes.lean`). |
| `Tools/` | What the command-line tools call: the JSON readers (`Json.lean`), and running and checking stage files (`Run.lean`). The entry points are in `spec/tools/`. |
| `Claims.lean` | Every main statement. |
| `Proofs/` | The theorems, mirroring `Blocks/`, `Isa/`, `Machine/`, `IR/`, `Check/`, plus `Claims.lean` and `EndToEnd.lean`. |

Outside `spec/Tau/`, `spec/tools/` holds the CLI entry points (`TauSim.lean`,
`TauCheck.lean`) and `spec/tests/` the compile-time tests of the
specification. Nothing in `spec/` imports from `course/`; the tests that need
the course's tables, including the test that the docs' tables hold of the
definitions, are in `course/tests/`.

A definition goes under `spec/Tau/<Area>/`. A theorem about it goes under
`spec/Tau/Proofs/<Area>/`, in a file of the same name. Every definition file
begins with a comment that says what the thing is, where tau-tpu uses it,
which terms a newcomer should look up, and which section of `docs/` it
specifies.

## Reading order

Each step is a section of a doc, then the file in `spec/Tau/` that specifies
it.

1. Machine 1, 3.5, 3.6: `Isa/Word.lean`, `Isa/Op.lean`, `Isa/Instr.lean`.
2. Machine 3.1 to 3.4, 3.7, 3.8: `Machine/SliceLevel.lean`, then `Machine/Timing.lean`.
3. Machine 3.9: `Isa/Event.lean`, `Machine/Issues.lean`.
4. Programs: `IR/Kernel.lean`, `IR/Source.lean`.
5. Compiler 2 and 3: `IR/MemMap.lean`, `IR/Placed.lean`, `IR/Compiled.lean`.
6. Compiler 5 and 7: `Check/Expr.lean`, `Check/Checker.lean`, `Check/Passes.lean`.
7. Machine 3.10: `Isa/Encode.lean`.
8. Machine 2 and 4: `Blocks/`, `Machine/CellLevel.lean`.
9. `Claims.lean`, then [Status](#status) below. Nothing under `Proofs/` has
   to be read to know what is claimed.

## Status

### The main result

`spec/Tau/Proofs/EndToEnd.lean` states it. If the checker accepts a compiled
program for a source program, then for every contents of the buffers:

- the cell-level machine (`Machine/CellLevel.lean`) runs the program without a trap,
- it leaves in memory exactly the buffers the source program computes, and
- the slice-level machine (`Machine/SliceLevel.lean`) issues every word the source
  pins to a cycle on that cycle.

The theorem rests on Lean's three standard axioms and nothing else.
`spec/tests/TauTest/Axioms.lean` fails the build if that changes.

### Four ways to stand

| Standing | Means |
|---|---|
| proved | a Lean theorem, for every input and every size |
| checked | `tau-check` decides it for each compiled program, and its yes is proved to be right |
| tested | it holds on the examples |
| trusted | nothing checks it |

### Every claim

| Claim | Standing | Where |
|---|---|---|
| Each block gives the stated output at cycle `t` | proved | `Proofs/Blocks/` |
| The cell-level machine equals the slice-level machine | proved | `cellExecute_eq` (`Proofs/Machine/CellLevel.lean`) |
| A finished program that `check` accepts computes its source, without a trap | proved | `check_sound`, `end_to_end` |
| It issues every word its source pins to a cycle on that cycle | proved, for `Machine/SliceLevel.lean` | `check_pins`, `end_to_end` |
| The output of a pass that the pass's check accepts computes what the input computes, and keeps its pins | proved | `checkInlined_sound`, `checkKernels_sound`, `checkPlaced_sound`, `checkScheduled_sound`, `checkRouted_sound`, and the same names ending in `_pins` |
| If all eight per-pass checks accept, the finished program computes its source and keeps its pins | proved | `passes_sound`, `passes_pins`, `end_to_end_passes` |
| `Kernel.unroll`, the Lean copy of `tau-unroll`, keeps what a kernel computes and its pins; the simplifier inside the checks keeps the value of an expression | proved | `Kernel.run_unroll`, `Kernel.timeline_unroll`, `Expr.denote_simp` |
| An image written by the Lean encoding, read back, is the program | proved | `Image.decode_encode` |
| The output of each C++ pass computes what its input computes and keeps its pins | checked | `tau-check`, once per pass |
| The image is the finished program | checked | `tau-check`, on the image decoded |
| The compiler's output is accepted | tested, on the examples | `scripts/check-examples.sh` |
| The tables of the docs hold of the definitions | tested | `course/tests/CourseTest/Docs.lean` |
| The C++ `tau-unroll` gives the kernel that its Lean copy gives; the C++ writes the image that the Lean encoding gives | tested, on the examples | `tau-check --unroll`, `tau-check --encode` |
| The frontend's trace of a Python program is what the compiler reads from the frontend's MLIR | tested, on the examples written in Python | `scripts/check-examples.sh` |
| A Python program run on real numbers ends with the buffers, and issues the pinned words, that its trace does | tested, on the same examples | `scripts/check-examples.sh` |
| What a Python file means | not stated; the trace of one run is the program | `compiler/python/tau/__init__.py` |
| The other six passes have a Lean copy, or a rule for how the output is built from the input | no; a check asks only whether the output computes the same thing on the same cycles | |
| The timing rule: a result is on its stream at slice `q` on cycle `t + delay + 1 + \|q - p\|` | proved, when nothing else is put on that stream in its path | `arrives_east`, `arrives_west` |
| The result is there on no other cycle | not stated | |
| A pinned word is issued by the slice the user had in mind | not stated; a pin names a word and a cycle, not a slice | `Isa/Event.lean` |
| The cell-level machine issues the words the slice-level machine issues, on the same cycles | not stated; only its final memory is compared | |
| `source.json` says what `kernel.mlir` says | trusted; for programs written in Python, tested against the frontend's own file | MLIR's parser, `compiler/lib/Emit/EmitSource.cpp` |
| The JSON files are read correctly | trusted | `Tools/Json.lean` |
| The definitions in the theorems mean what is intended | trusted; read them against the docs | `Source.run`, `Source.timeline`, `cellExecute`, `Isa/Word.lean` |
| The docs say what was meant | trusted; nothing can check it | `docs/` |
| Lean checks proofs and compiles `tau-check` correctly | trusted | |
| Anything about hardware | no; the machine is a Lean model | |

### Where trust begins

A bug in a pass of the compiler gives a program the checker rejects, not a
wrong answer. The exception is the step that writes `source.json`: the chain
of checks starts from that file, so a program misread there is checked
faithfully against the wrong source. For a program written in Python that
step is tested, because the frontend writes the same file on its own.

Below that file, the trust is in the definitions and the docs: that
`Source.run` says what a program should compute, that `execute` says what
the machine should do, and that both say what their docs intend.
