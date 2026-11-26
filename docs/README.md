# The docs

This folder holds the shared prose specification of tau-tpu: what the
machine does, what a program means, what any compiler between them must
deliver, and the JSON formats the tools exchange.

Each doc describes the contract shared by both sides of the repository: the
verified Lean development in [`spec/`](../spec/README.md) and the untrusted
Python + MLIR compiler in [`compiler/`](../compiler/README.md).

| Doc | Describes | Specified in |
|---|---|---|
| [`Machine.md`](Machine.md) | The machine: components, slices, streams, one cycle, the timing rule, instructions, traps, the image. | `spec/Tau/Isa/`, `spec/Tau/Blocks/`, `spec/Tau/Machine/` |
| [`Programs.md`](Programs.md) | What a user writes: buffers, statements, loops, calls, pins; and what a program promises. | `spec/Tau/IR/Kernel.lean`, `spec/Tau/IR/Source.lean`, `spec/Tau/Isa/Event.lean` |
| [`Compiler.md`](Compiler.md) | What any compiler for the machine must deliver: the forms a program takes and what every step between them must keep. | `spec/Tau/IR/`, `spec/Tau/Check/`, `spec/Tau/Isa/Encode.lean` |
| [`Formats.md`](Formats.md) | The JSON formats the frontend, compiler and Lean tools exchange. | `spec/Tau/Sim/Json.lean` |
| [`../spec/README.md`](../spec/README.md) | How the Lean development fits together, its reading order, and how every claim stands. | `spec/Tau/Claims.lean` |

Read the first three docs in that order. Each begins with a table that says what
it describes and what it leaves to another doc.

## 1. The docs and the Lean

A doc says in words and tables what one part of tau-tpu is meant to be, the
way its designer would hand it to someone who has to specify it. The Lean
files named in its table are that specification.

**Lean decides.** A doc is not the specification. Where a doc and the Lean
disagree, the Lean is right and the doc has a mistake.

**A doc says less.** It gives the intent and the cases a designer thinks
of. It leaves things unsaid, and where it is silent the Lean has decided.
Those decisions are worth knowing: for each table in a doc,
`course/Specify/Support/Tables.lean` has a second table, named `...Decisions`,
of what the doc left open and the Lean settled.

**A table is a test.** Every table in a doc that gives a result for an
input has the same rows in `course/Specify/Support/Tables.lean`, and
`spec/tests/TauTest/Docs.lean` runs them on the definitions in `spec/Tau/`. If
the doc, the rows and the definition come apart, the build fails. Change the
three together.

**One place for each fact.** The three docs describe the machine, programs
and compilers, and nothing about this repository. [`Formats.md`](Formats.md)
describes the JSON formats the tools exchange. What is in `spec/` and how it
fits together — along with the claim-status table and trust boundary — is in
[`spec/README.md`](../spec/README.md). Outside `docs/` and `spec/`, each part
documents itself only: [`compiler/README.md`](../compiler/README.md) says how
this compiler does its job and its limits, the comment at the top of
[`compiler/python/tau/__init__.py`](../compiler/python/tau/__init__.py) how
the Python frontend records a program, and the root [`README.md`](../README.md)
how to set up and try the project.

**Sections keep their numbers.** Sections are numbered within each doc,
and other files cite them as "Machine 3.4", "Programs 5", "Formats 3" or
"Docs/README 1". A section keeps its number when the text around it changes.
A new section goes at the end of its chapter.

**The course reads the docs.** The course in `course/` has its students
write the Lean from these docs, one section at a time, and then compare with
the Lean in `spec/Tau/`. That is why a doc must keep saying less than the Lean:
a doc that restated every definition would leave nothing to specify.
