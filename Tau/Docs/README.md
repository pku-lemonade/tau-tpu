# The docs

`Tau/` is tau-tpu's specification: what the machine does, what a program
means, and what a compiler between them has to deliver. This folder holds
all of its prose. Everything else in `Tau/` is Lean.

Together, tau-tpu consists of a statically scheduled row-of-slices machine
with fixed-cycle streams, programs written in Python or MLIR with optional
cycle pins, an untrusted C++/MLIR compiler that lowers each program through
intermediate forms into slice timetables and a numeric image, and Lean
proofs that connect a component-built machine to the slice-level machine and
validate the checker that judges every compiler output against its source.

| Doc | Describes | Specified in |
|---|---|---|
| [`Machine.md`](Machine.md) | The machine: components, slices, streams, one cycle, the timing rule, instructions, traps, the image. | `Tau/Data/`, `Tau/Blocks/`, `Tau/Isa/`, `Tau/SliceLevel/`, `Tau/CellLevel/` |
| [`Programs.md`](Programs.md) | What a user writes: buffers, statements, loops, calls, pins; and what a program promises. | `Tau/IR/Kernel.lean`, `Tau/IR/Source.lean`, `Tau/Isa/Event.lean` |
| [`Compiler.md`](Compiler.md) | What any compiler for the machine must deliver: the forms a program takes and what every step between them must keep. | `Tau/IR/`, `Tau/Check/` |
| this README | How the docs and the Lean fit together (1 to 3), how every claim stands (4), and the files the tools exchange (5). | `Tau/Claims.lean`, `Tau/Sim/Json.lean` |

Read the three docs in that order. Each begins with a table that says what
it describes and what it leaves to another doc.

Contents of this README:

1. [The docs and the Lean](#1-the-docs-and-the-lean)
2. [The specification](#2-the-specification)
3. [The map](#3-the-map)
4. [Status](#4-status)
5. [Files](#5-files)

Lean paths in sections 2 and 3 start inside `Tau/`: `IR/Source.lean` is
`Tau/IR/Source.lean`.

## 1. The docs and the Lean

A doc says in words and tables what one part of tau-tpu is meant to be, the
way its designer would hand it to someone who has to specify it. The Lean
files named in its table are that specification.

**Lean decides.** A doc is not the specification. Where a doc and the Lean
disagree, the Lean is right and the doc has a mistake.

**A doc says less.** It gives the intent and the cases a designer thinks
of. It leaves things unsaid, and where it is silent the Lean has decided.
Those decisions are worth knowing: for each table in a doc,
`course/Specs/Tables.lean` has a second table, named `...Decisions`, of what
the doc left open and the Lean settled.

**A table is a test.** Every table in a doc that gives a result for an
input has the same rows in `course/Specs/Tables.lean`, and
`tests/TauTest/Docs.lean` runs them on the definitions in `Tau/`. If the
doc, the rows and the definition come apart, the build fails. Change the
three together.

**One place for each fact.** The three docs describe the machine, programs
and compilers, and nothing about this repository. What is in `Tau/` and how
it fits together is sections 2 and 3 here, how each claim stands is
section 4, and the files are section 5. Outside `Tau/`, each part documents
itself only: `compiler/README.md` says how this compiler does its job and
its limits, the comment at the top of `frontend/tau/__init__.py` how the
Python frontend records a program, and the root `README.md` how to set up
and try the project.

**Sections keep their numbers.** Sections are numbered within each doc,
and other files cite them as "Machine 3.4", "Programs 5" or "README 5.3".
A section keeps its number when the text around it changes. A new section
goes at the end of its chapter.

**The course reads the docs.** The course in `course/` has its students
write the Lean from these docs, one section at a time, and then compare with
the Lean in `Tau/`. That is why a doc must keep saying less than the Lean: a
doc that restated every definition would leave nothing to specify.

## 2. The specification

### 2.1 Four kinds of text

| Kind of text | Where | What it is for | Who judges it |
|---|---|---|---|
| Doc | `Docs/` | The intent, in words and tables, as a designer would write it. | A person, against what was meant. |
| Definition | `<Area>/` | The specification itself, in Lean. It runs: the simulator and the checker are these definitions, compiled. | A person, against the docs; and the docs' tables, run as tests. |
| Statement | `Claims.lean` | Every main theorem as a named proposition, readable without a proof. | A person: is this what a user relies on? |
| Proof | `Proofs/<Area>/` | Why each statement is true. | Lean. |

### 2.2 Inside and outside

Everything outside `Tau/` is measured against it and specified by it.

| Outside | What it is | How it is held to `Tau/` |
|---|---|---|
| `compiler/` | a compiler in C++, on MLIR | each file it writes is judged by a check from `Check/` |
| `frontend/` | a way to write programs in Python | its record of a program is compared with the compiler's; its run on real numbers with the definitions |
| `tools/` | `tau-sim` and `tau-check` | they are the definitions, with a command line |
| `tests/`, `examples/` | runs on particular inputs | |
| `course/` | a course in writing all of this | its students write the definitions from the docs and compare with the ones in `Tau/` |

Nothing in `Tau/` depends on anything outside it.

### 2.3 Two specifications

tau-tpu specifies two things. Each has its own question.

| | 1. The machine | 2. The path to it |
|---|---|---|
| Doc | `Machine.md` | `Programs.md`, `Compiler.md` |
| The question | Does the machine built from components do what the slice-level machine says it does? | Does a compiled program, run on the machine, compute what its source says, when its source says? |
| Specification | The slice-level machine: what the machine does with a program, cycle by cycle, with each slice one box with a delay. `execute` in `SliceLevel/Machine.lean`. | The source specification: what a program computes and on which cycles, with no machine in sight. `Source.run` and `Source.timeline` in `IR/Source.lean`. |
| Measured against it | The cell-level machine, with each slice built from components: `cellExecute` in `CellLevel/Machine.lean`. | Every program a compiler produces, run by `execute`. |
| How | A theorem, once, for all programs. | A check, on each compiled program, and theorems that the check can be trusted. |
| Main theorem | `cellExecute_eq` | `check_sound`, `check_pins` |

The slice-level machine appears on both sides. In part 1 it is the standard
that the cell-level machine must meet. In part 2 it is what "running a
compiled program" means, and the source specification is the standard.

`end_to_end` (`Proofs/EndToEnd.lean`) joins the two.

### 2.4 The words

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

## 3. The map

### 3.1 Part 1: the machine

| `Machine.md` | Definition | Theorems |
|---|---|---|
| 1, lanes and words | `Data/Word.lean` | `Proofs/Data/Lane.lean` |
| 2, the components | `Blocks/` | `Proofs/Blocks/`: for each block, its output at cycle `t` in terms of earlier inputs |
| 3.1 to 3.3 and 3.5 to 3.8, the slice-level machine | `Isa/Op.lean`, `Isa/Instr.lean`; `step` and `execute` in `SliceLevel/Machine.lean` | `execute_map` |
| 3.4, the timing rule | derived from `step`; stated with `SliceLevel/Timing.lean` | `arrives_east`, `arrives_west` |
| 3.9, what a slice issues | `issues` in `SliceLevel/Issues.lean` | `issues_map` |
| 3.10, the image | `Program.encode`, `Image.decode` in `Isa/Encode.lean` | `Image.decode_encode` |
| 4, the cell-level machine | `cellExecute` in `CellLevel/Machine.lean` | `cellExecute_eq` |

Two of these carry everything else.

- **The machine does not look at its values** (`execute_map`,
  `issues_map`). It moves and combines words but never decides anything from
  what a word holds. So one run on names tells what every run on real words
  computes, and on which cycle it issues each word. Every check in part 2
  rests on this.
- **Refinement** (`cellExecute_eq`). The cell-level machine gives, on every
  program, the result the slice-level machine gives.

The timing rule is proved from `step` and nothing depends on it. It is the
rule a person uses to write a schedule.

### 3.2 Part 2: the path to the machine

**The forms.**

| `Compiler.md` 2, form | Definition | What it computes, and when |
|---|---|---|
| Source | `Source` in `IR/Source.lean` | `Source.run`, `Source.timeline` |
| Kernel | `Kernel` in `IR/Kernel.lean` | `Kernel.run`, `Kernel.timeline` |
| Placed | `Placed` in `IR/Placed.lean` | `Placed.execute`, `Placed.timeline` |
| Compiled | `Compiled` in `IR/Compiled.lean` | `execute`, `Compiled.timeline` |

The memory map, with `image` to load buffers and `extract` to read them
back, is `IR/MemMap.lean`. Running on names is `IR/Expr.lean`.

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
for both.

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
| unroll | `Kernel.unroll` in `Passes/Unroll.lean` | `Kernel.run_unroll`, `Kernel.timeline_unroll` |
| encode | `Program.encode` in `Isa/Encode.lean` | `Image.decode_encode` |

These theorems are about the Lean functions. That a compiler produces what
they produce is a test (`tau-check --unroll`, `tau-check --encode`). The
checks already cover both steps; the copies are there to show the second
method on steps small enough for it.

### 3.3 How the theorems add up

```
source ─inline→ kernel ─simplify→ kernel ─unroll→ kernel ─place→ placed
     checkInlined    checkKernels     checkKernels     checkPlaced

placed ─schedule→ compiled ─route→ compiled ─slice→ compiled ─fold→ compiled ─encode→ image
      checkScheduled      checkRouted      checkRouted     checkRouted     checkRouted

└──────────────────────────────── check ─────────────────────────────────────┘

compiled, on the slice-level machine  =  compiled, on the cell-level machine
                               cellExecute_eq
```

| Theorem | Says | Built from |
|---|---|---|
| `check_sound`, `check_pins` | part 2, by the one check | |
| `passes_sound`, `passes_pins` | part 2, by the per-step checks | the per-step theorems |
| `cellExecute_eq` | part 1 | the block theorems |
| `end_to_end` | parts 1 and 2 | `check_sound`, `check_pins`, `cellExecute_eq` |
| `end_to_end_passes` | parts 1 and 2 | `passes_sound`, `passes_pins`, `cellExecute_eq` |

### 3.4 The folders

In dependency order.

| Folder | Contents |
|---|---|
| `Docs/` | This README and the three docs. |
| `Data/` | Lanes and words: 32-bit values and the operations on them. |
| `Blocks/` | Clocked components: shift register, accumulator, multiply-accumulate, pipeline, memory, sequencer, repeater, systolic array. |
| `Isa/` | Slice kinds, operations, instructions, programs, the shape of a machine; events; the image. |
| `SliceLevel/` | The slice-level machine, and what it issues on each cycle. |
| `CellLevel/` | The cell-level machine: each slice built from blocks. |
| `IR/` | The four forms of a program, the memory map, and expressions. |
| `Passes/` | The Lean copy of unroll. |
| `Check/` | The checks, and the simplifier they use. |
| `Sim/` | The file readers and the functions behind `tau-sim` and `tau-check`. |
| `Claims.lean` | Every main statement. |
| `Proofs/` | The theorems, in folders of the same names. |

A definition goes under `Tau/<Area>/`. A theorem about it goes under
`Tau/Proofs/<Area>/`, in a file of the same name. Every definition file
begins with a comment that says what the thing is, where tau-tpu uses it,
which terms a newcomer should look up, and which section of the docs it
specifies.

### 3.5 Reading order

Each step is a section of a doc, then the file that specifies it.

1. Machine 1, 3.5, 3.6: `Data/Word.lean`, `Isa/Op.lean`, `Isa/Instr.lean`.
2. Machine 3.1 to 3.4, 3.7, 3.8: `SliceLevel/Machine.lean`, then
   `SliceLevel/Timing.lean`.
3. Machine 3.9: `Isa/Event.lean`, `SliceLevel/Issues.lean`.
4. Programs: `IR/Kernel.lean`, `IR/Source.lean`.
5. Compiler 2 and 3: `IR/MemMap.lean`, `IR/Placed.lean`, `IR/Compiled.lean`.
6. Compiler 5 and 7: `IR/Expr.lean`, `Check/Checker.lean`,
   `Check/Passes.lean`.
7. Machine 3.10: `Isa/Encode.lean`.
8. Machine 2 and 4: `Blocks/`, `CellLevel/Machine.lean`.
9. `Claims.lean`, then section 4. Nothing under `Proofs/` has to be read to
   know what is claimed.

## 4. Status

### 4.1 The main result

`Tau/Proofs/EndToEnd.lean` states it. If the checker accepts a compiled
program for a source program, then for every contents of the buffers:

- the cell-level machine runs the program without a trap,
- it leaves in memory exactly the buffers the source program computes, and
- the slice-level machine issues every word the source pins to a cycle on
  that cycle.

The theorem rests on Lean's three standard axioms and nothing else.
`tests/TauTest/Axioms.lean` fails the build if that changes.

### 4.2 Four ways to stand

| Standing | Means |
|---|---|
| proved | a Lean theorem, for every input and every size |
| checked | `tau-check` decides it for each compiled program, and its yes is proved to be right |
| tested | it holds on the examples |
| trusted | nothing checks it |

### 4.3 Every claim

| Claim | Standing | Where |
|---|---|---|
| Each block gives the stated output at cycle `t` | proved | `Tau/Proofs/Blocks/` |
| The cell-level machine equals the slice-level machine | proved | `cellExecute_eq` |
| A finished program that `check` accepts computes its source, without a trap | proved | `check_sound`, `end_to_end` |
| It issues every word its source pins to a cycle on that cycle | proved, for the slice-level machine | `check_pins`, `end_to_end` |
| The output of a pass that the pass's check accepts computes what the input computes, and keeps its pins | proved | `checkInlined_sound`, `checkKernels_sound`, `checkPlaced_sound`, `checkScheduled_sound`, `checkRouted_sound`, and the same names ending in `_pins` |
| If all eight per-pass checks accept, the finished program computes its source and keeps its pins | proved | `passes_sound`, `passes_pins`, `end_to_end_passes` |
| `Kernel.unroll`, the Lean copy of `tau-unroll`, keeps what a kernel computes and its pins; the simplifier inside the checks keeps the value of an expression | proved | `Kernel.run_unroll`, `Kernel.timeline_unroll`, `Expr.denote_simp` |
| An image written by the Lean encoding, read back, is the program | proved | `Image.decode_encode` |
| The output of each C++ pass computes what its input computes and keeps its pins | checked | `tau-check`, once per pass |
| The image is the finished program | checked | `tau-check`, on the image decoded |
| The compiler's output is accepted | tested, on the examples | `scripts/check-examples.sh` |
| The tables of the docs hold of the definitions | tested | `tests/TauTest/Docs.lean` |
| The C++ `tau-unroll` gives the kernel that its Lean copy gives; the C++ writes the image that the Lean encoding gives | tested, on the examples | `tau-check --unroll`, `tau-check --encode` |
| The frontend's record of a Python program is what the compiler reads from the frontend's MLIR | tested, on the examples written in Python | `scripts/check-examples.sh` |
| A Python program run on real numbers ends with the buffers, and issues the pinned words, that its record does | tested, on the same examples | `scripts/check-examples.sh` |
| What a Python file means | not stated; the record of one run is the program | `frontend/tau/__init__.py` |
| The other six passes have a Lean copy, or a rule for how the output is built from the input | no; a check asks only whether the output computes the same thing on the same cycles | |
| The timing rule: a result is on its stream at slice `q` on cycle `t + delay + 1 + \|q - p\|` | proved, when nothing else is put on that stream in its path | `arrives_east`, `arrives_west` |
| The result is there on no other cycle | not stated | |
| A pinned word is issued by the slice the user had in mind | not stated; a pin names a word and a cycle, not a slice | `Tau/Isa/Event.lean` |
| The cell-level machine issues the words the slice-level machine issues, on the same cycles | not stated; only its final memory is compared | |
| `source.json` says what `kernel.mlir` says | trusted; for programs written in Python, tested against the frontend's own file | MLIR's parser, `compiler/lib/Target/EmitKernel.cpp` |
| The JSON files are read correctly | trusted | `Tau/Sim/Json.lean` |
| The definitions in the theorems mean what is intended | trusted; read them against the docs | `Source.run`, `Source.timeline`, `cellExecute`, `Tau/Data/Word.lean` |
| The docs say what was meant | trusted; nothing can check it | `Tau/Docs/` |
| Lean checks proofs and compiles `tau-check` correctly | trusted | |
| Anything about hardware | no; the machine is a Lean model | |

### 4.4 Where trust begins

A bug in a pass of the compiler gives a program the checker rejects, not a
wrong answer. The exception is the step that writes `source.json`: the chain
of checks starts from that file, so a program misread there is checked
faithfully against the wrong source. For a program written in Python that
step is tested, because the frontend writes the same file on its own.

Below that file, the trust is in the definitions and the docs: that
`Source.run` says what a program should compute, that `execute` says what
the machine should do, and that both say what their docs intend.

## 5. Files

The JSON files that the frontend, the compiler and the Lean tools exchange:
what is in each, and which tool writes which. What the contents mean is in
the docs: a statement and a pin in `Programs.md`, an instruction and the
numbers of an image in `Machine.md`, a form in `Compiler.md`.

The reader, `Tau/Sim/Json.lean`, is the specification. The writers are
`compiler/lib/Target/` and, for source files, also `frontend/tau/`. No table
here is a test; `scripts/check-examples.sh` reads every kind of file on
every example.

Each form of a program (Compiler 2) has a file. The Lean tools tell the kind
of a file from the fields present.

### 5.1 Source file and kernel file

A program before it has slices: buffers, statements, loops and calls. With a
call in it the file is a *source* file (`Tau.Source`); with none it is a
*kernel* file (`Tau.Kernel`). `tau-inline` turns the first into the second.

```json
{
  "buffers": [1, 1, 2, 1],
  "body": [
    {"op": "load", "dst": 0, "buf": 0, "base": 0, "stride": 0},
    {"op": "matvec", "dst": 1, "x": 0, "buf": 2, "base": 0, "stride": 0, "n": 2},
    {"op": "bin", "fn": "add", "dst": 3, "a": 1, "b": 2},
    {"op": "un", "fn": "requant", "k": 0, "dst": 4, "a": 3},
    {"op": "store", "src": 4, "buf": 3, "base": 0, "stride": 0},
    {"op": "loop", "n": 4, "body": [
      {"op": "un", "fn": "relu", "dst": 6, "a": 5, "at": 6, "every": 4}
    ]},
    {"op": "call", "args": [0, 3], "at": 40, "body": [
      {"op": "load", "dst": 0, "buf": 0, "base": 0, "stride": 0}
    ]}
  ]
}
```

- `buffers` gives the number of words in each buffer. Buffers are numbered
  from 0 in this order.
- `dst`, `src`, `a`, `b` and `x` are value numbers.
- A position is `base + stride * i`, where `i` is the iteration of the
  enclosing loop, or 0 outside a loop.
- One-word functions (`un`): `relu`, `neg`, `abs`, `reverse` take nothing;
  `requant`, `shl`, `addi`, `muli`, `shift`, `rotate`, `broadcast` take an
  integer `k`; `permute` takes a list `table`.
- Two-word functions (`bin`): `add`, `sub`, `mul`, `max`, `min`, `and`, `or`,
  `xor`, `lt`.
- Other statements: `{"op": "const", "dst": 0, "values": [1, 2]}`,
  `{"op": "sel", "dst": 3, "m": 0, "a": 1, "b": 2}`, and `affine`, which is
  `matvec` with one more field, `bias`.
- A `loop` body holds statements only. Loops do not nest.
- A statement with `at` is pinned (Programs 5). In a loop the cycle is
  `at + every * i`. `every` may be left out, and is then 0.
- A `call` (Programs 4) carries the called kernel's statements as its
  `body`, with value numbers and buffer numbers of their own: the kernel's
  buffer `j` is the caller's buffer `args[j]`. `at` is the origin.
- A program's scratch buffers, which the frontend's `tau.alloc` makes, come
  after the buffers the user fills.

### 5.2 Placed file

The output of `tau-place`: the machine, the memory map, and the instructions
in the order they must take effect. There are no cycles and no streams yet.

```json
{
  "config": {"kinds": ["mxm", "sxm", "mem", "mem", "vxm", "mem", "mem", "sxm", "mxm"],
             "streams": 8, "memDelay": 1, "vxmDelay": 1, "sxmDelay": 1, "mxmDelay": 2},
  "memSizes": [0, 0, 2, 1, 0, 2, 1, 0, 0],
  "map": [{"slice": 2, "base": 0, "size": 1}],
  "instructions": [
    {"op": "read", "slice": 2, "addr": 0, "dst": 0},
    {"op": "load", "slice": 0, "src": 0},
    {"op": "read", "slice": 5, "addr": 0, "dst": 1},
    {"op": "mac", "slice": 0, "j": 0, "src": 1},
    {"op": "emit", "slice": 0, "dst": 2},
    {"op": "bin", "fn": "add", "slice": 4, "a": 2, "b": 3, "dst": 4},
    {"op": "write", "slice": 6, "addr": 0, "src": 4}
  ]
}
```

- `dst`, `src`, `a`, `b` and `m` are numbers naming words in transit. Each
  is produced once and used by one instruction.
- An instruction with `pin` must be issued on that cycle. `tau-place` puts
  the pin of a kernel statement on the instruction that issues its word: the
  `read` of a load, the `write` of a store, the `emit` of a matrix product.
- Instructions (`op`): `read`, `write`, `un`, `bin`, `const`, `sel`, `load`,
  `seed`, `mac`, `install`, `macw`, `emit`.
- The fields are those of `Tau.PInstr` in `Tau/IR/Placed.lean`.

### 5.3 Compiled file

The machine, the memory map and the timed program. `tauc` writes four of
these: `scheduled.json` after `tau-schedule`, in which every word has a
stream to itself and `streams` is raised to make room; `routed.json` after
`tau-route`; `sliced.json` after `tau-slice`, with the entries listed slice
by slice; and `compiled.json` after `tau-fold`.

```json
{
  "config": {
    "kinds": ["mxm", "sxm", "mem", "mem", "vxm", "mem", "mem", "sxm", "mxm"],
    "streams": 8, "mxmWeights": 8,
    "memDelay": 1, "vxmDelay": 1, "sxmDelay": 1, "mxmDelay": 2
  },
  "memSizes": [0, 0, 2, 1, 0, 2, 1, 0, 0],
  "map": [{"slice": 2, "base": 0, "size": 1}],
  "cycles": 25,
  "program": [
    {"slice": 5, "time": 0, "op": "read", "addr": 0, "dst": {"dir": "west", "id": 0},
     "repeats": 1, "gap": 0, "stride": 1},
    {"slice": 0, "time": 6, "op": "load", "src": {"dir": "west", "id": 0}}
  ]
}
```

- `config` is the shape of the machine (Machine 3.1). A file containing only
  this object is a machine file, such as `chips/tau9.json`, accepted by
  `tauc --chip`.
- `memSizes` gives the number of words of memory at each position.
- `map` places each buffer, in buffer order: its slice, first address and
  length. Memory words outside every buffer are scratch space.
- `cycles` is how long to run.
- `mxmWeights` is the number of columns a matrix slice can store. It may be
  left out, and is then 8.
- Instructions (`op`): `read`, `write`, `un`, `bin`, `const`, `sel`, `load`,
  `seed`, `mac`, `install`, `macw`, `emit`. Their fields are those of
  `Tau.Instr` in `Tau/Isa/Instr.lean`.
- An entry with `repeats`, `gap` and `stride` is issued `repeats` more times
  after the first, with `gap` idle cycles between issues, and with its `addr`
  (for `read` and `write`) or `j` (for `mac`, `install` and `macw`) growing by
  `stride` each time. All three may be left out, and are then 0. `tau-fold`
  makes such entries; the files before it have none.

### 5.4 Image file

A compiled file with the program as numbers: `image` in place of `program`,
with one list of numbers for each slice of the machine. It is what the
machine would be loaded with.

```json
{
  "config": {"kinds": ["mxm", "sxm", "mem", "mem", "vxm", "mem", "mem", "sxm", "mxm"],
             "streams": 8, "mxmWeights": 8,
             "memDelay": 1, "vxmDelay": 1, "sxmDelay": 1, "mxmDelay": 2},
  "memSizes": [0, 0, 4, 4, 0, 0, 0, 0, 0],
  "map": [{"slice": 2, "base": 0, "size": 4}, {"slice": 3, "base": 0, "size": 4}],
  "cycles": 22,
  "image": [
    [0],
    [0],
    [1, 2, 3, 3, 1, 0, 0, 0],
    [1, 9, 3, 3, 1, 1, 1, 0],
    [1, 6, 3, 3, 0, 2, 0, 1, 0],
    [0], [0], [0], [0]
  ]
}
```

This is `examples/paced`. Slice 2 has one entry: from cycle 2, three more
times, 3 idle cycles apart, the address growing by 1; opcode 0, `read`,
address 0, onto stream 0 going east.

The numbers are those of Machine 3.10: for each slice the count of its
entries and then each entry, as `time, repeats, gap, stride, opcode,
operands`. The tools read an image back with `Image.decode`
(`Tau/Isa/Encode.lean`), and to them an image is the compiled program it
decodes to.

### 5.5 What the tools write

| File | Kind | After |
|---|---|---|
| `kernel.mlir`, `traced.json` | MLIR text, source | the frontend, `python3 -m tau kernel.py -o out` |
| `source.json` | source or kernel | parsing |
| `kernel.json` | kernel | `tau-inline` |
| `simplified.json` | kernel | `tau-simplify` |
| `unrolled.json` | kernel | `tau-unroll` |
| `placed.json` | placed | `tau-place` |
| `scheduled.json` | compiled | `tau-schedule` |
| `routed.json` | compiled | `tau-route` |
| `sliced.json` | compiled | `tau-slice` |
| `compiled.json` | compiled | `tau-fold` |
| `image.json` | image | encoding |

`traced.json` and `source.json` are the same program written by two
programs, the frontend and `tauc`; `scripts/check-examples.sh` fails if they
differ.

`tau-sim <file> buffers.json` runs any of them, and
`tau-sim --timeline <file> buffers.json` prints its events. `tau-check
<before> <after>` compares two of them: a pass's input with its output, or
`source.json` with `image.json`. Both tools tell the kind of a file from the
fields present.

### 5.6 Buffers file

Buffer contents for a run, as signed integers.

```json
{
  "lanes": 2,
  "buffers": [
    [[3, -2]],
    [[1, 3], [2, 4]]
  ]
}
```

Each buffer is a list of words, and each word is a list of `lanes` integers.
`tau-sim` prints its result in the same format. A buffer the file leaves out
starts as zeros, so a file that fills a program's own buffers serves every
stage, scratch buffers included.

### 5.7 Timeline

What `tau-sim --timeline` and the frontend's `--timeline` print: the events
of a run, as a list.

```json
[
  {"time": 6, "word": [1, 0]},
  {"time": 9, "word": [1, 0], "buf": 1, "pos": 0}
]
```

An event with `buf` and `pos` is a store to that word of that buffer. For a
source program, a kernel or a placed program the events are those of the
pinned operations. For a compiled program or an image they are every word a
slice issues.
