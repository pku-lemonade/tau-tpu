# The docs

What tau-tpu is meant to be, in words and tables: what the machine does,
what a program means, what any compiler between them must deliver, and the
JSON formats the tools exchange. The Lean in [`spec/`](../spec/README.md)
specifies each doc; the compiler in [`compiler/`](../compiler/README.md) is
one compiler that `docs/Compiler.md` describes, and is checked against that
specification.

| Doc | Describes | Specified in |
|---|---|---|
| [`Machine.md`](Machine.md) | The machine: blocks, slices, streams, one cycle, the timing rule, instructions, traps, the image. | `spec/Tau/Isa/`, `spec/Tau/Blocks/`, `spec/Tau/Machine/` |
| [`Programs.md`](Programs.md) | What a user writes: buffers, statements, loops, calls, pins; and what a program promises. | `spec/Tau/IR/Kernel.lean`, `spec/Tau/IR/Source.lean`, `spec/Tau/Isa/Event.lean` |
| [`Compiler.md`](Compiler.md) | What any compiler for the machine must deliver: the IRs a program takes and what every step between them must keep. | `spec/Tau/IR/`, `spec/Tau/Check/`, `spec/Tau/Isa/Encode.lean` |
| [`Formats.md`](Formats.md) | The JSON formats the frontend, compiler and Lean tools exchange. | `spec/Tau/Tools/Json.lean` |
| [`../spec/README.md`](../spec/README.md) | How the Lean development fits together, its reading order, and how every claim stands. | `spec/Tau/Claims.lean` |

Read `Machine.md`, `Programs.md` and `Compiler.md` in that order;
`Formats.md` is a reference for the files. Each doc begins with a table: what
it describes, what it leaves to another doc, which Lean specifies it, and
which test runs its tables. Other files cite a section by doc and number:
"Machine 3.4", "Programs 5", "Formats 3", "Docs/README 1".

## 1. The docs and the Lean

A doc says in words and tables what one part of tau-tpu is meant to be, the
way its designer would hand it to someone who has to specify it. The Lean
files named in its table are that specification. Six rules keep the two
together.

1. **Lean decides.** A doc is not the specification. Where a doc and the
   Lean disagree, the Lean is right and the doc has a mistake.
2. **A doc says less.** It gives the intent and the cases a designer thinks
   of, and where it is silent the Lean has decided. For each table in a doc,
   `course/Specify/Support/Tables.lean` has a second table, named
   `...Decisions`, of what the doc left open and the Lean settled.
3. **A table is a test.** Every table in a doc that gives a result for an
   input has the same rows in `course/Specify/Support/Tables.lean`, and
   `course/tests/CourseTest/Docs.lean` runs them on the definitions in
   `spec/Tau/`. If the doc, the rows and the definition come apart, the
   build fails, so change the three together.
4. **A fact is stated once.** The three docs describe the machine, programs
   and compilers, and nothing about this repository; `Formats.md` describes
   the files the tools exchange. How the repository fits together is in the
   README of each folder.
5. **A section keeps its number** when the text around it changes. A new
   section goes at the end of its chapter.
6. **The course reads the docs.** Its students write the Lean from these
   docs, one section at a time, and then compare with `spec/Tau/`. That is
   why a doc keeps saying less than the Lean: a doc that restated every
   definition would leave nothing to specify.
