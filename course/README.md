# The course

A self-paced course in Lean 4, built on the tau-tpu development. It assumes
programming experience and a first course in discrete mathematics. It does not
assume a course in digital design, computer architecture or compilers; where a
term from those fields is needed, the chapter names it and the reading list
says where to look it up.

Plan for about 30 days of roughly six focused hours each. The day counts are
estimates; nobody has been timed.

## Start

1. Install [elan](https://github.com/leanprover/elan) and
   [VS Code](https://code.visualstudio.com/) with the Lean 4 extension, or use
   the container in `docker/`.
2. From the repository root run `lake build`. The first build downloads Lean.
3. Open the repository folder (the whole folder) in VS Code.
4. Read the book, starting with "Start here" and "Working in Lean".

## The book

The chapters are the files in `book/TauBook/`, in the order listed in
`book/TauBook.lean`. You can read them there directly: the text after the
`#doc` line is the chapter. To read them as web pages:

```bash
cd course/book
lake exe tau-book        # writes the HTML to _out/html-multi/
python3 -m http.server -d _out/html-multi 8000
```

The first build compiles Verso and takes about ten minutes. Every Lean
example in the book is checked when the book is built.

## Three places for three kinds of file

| Folder | What is in it | Who edits it |
|---|---|---|
| `Tau/` | The finished development. `Tau/Proofs/` holds the solutions. | Nobody, except in the exercises that say to work on a branch |
| `course/Exercises/` | The same proof files with each proof replaced by `sorry`. | You fill in the proofs |
| `course/Work/` | Your own files: a scratch file, and the open exercises. | You |

## Guided exercises

Each chapter names its files. Open one in VS Code, put the cursor before a
`sorry`, read the goal in the infoview, and replace the `sorry` with a proof.
A long proof has an outline above its `sorry`.

A file is finished when this prints no warning about `sorry`:

```bash
lake build Exercises.Blocks.ShiftRegister
```

An exercise file imports the finished library, not other exercise files, so
you can skip one and come back.

The solution to `course/Exercises/X.lean` is `Tau/Proofs/X.lean`. When you
are stuck, follow the list in the chapter "Working in Lean", which ends with
reading one line of the solution and going back to work.

## Open and challenge exercises

These have no solution. Write them in `course/Work/`. Every chapter gives a
starting point. A file `course/Work/Foo.lean` is the module `Work.Foo`; check
it with `lake build Work.Foo`, and use it from another file with
`import Work.Foo`.

## Without the C++ compiler

Everything in Lean works without it. Three chapters ask you to run the
compiler (kernels, expressions, the checker). For those, either use the
container in `docker/`, or read the files in `examples/linear/stages/`, which
are what the compiler writes for `examples/linear/kernel.mlir`.

## Order

| Days | Chapter | Guided exercise files |
|---|---|---|
| 0 | Start here; Working in Lean | none |
| 1-2 | The shift register | `Blocks/Basic`, `Blocks/ShiftRegister` |
| 3 | The accumulator | `Blocks/Accumulator` |
| 4 | Multiply-accumulate | `Blocks/Mac`, `Data/Lane` |
| 5 | Pipeline and sequencer | `Blocks/Pipeline`, `Blocks/Sequencer` |
| 6-7 | Memory | `Blocks/Memory` |
| 8-9 | The repeater | `Blocks/Repeater` |
| 10-12 | The systolic array | `Blocks/SystolicArray` |
| 13-15 | The slice-level machine | none; you write schedules |
| 16-17 | Kernels and loop unrolling | `Passes/Unroll` |
| 18-19 | Expressions and simplification | `Passes/Simplify` |
| 20-24 | The checker | `IR/Map`, `SliceLevel/Map`, `Check/Sound`, `Check/Stages` |
| 25-29 | The cell-level machine | `CellLevel/Refine` |
| 30 | End to end | `EndToEnd` |
| after | Extending the machine | none; you add features |

The book ends with a tactic reference and a reading list.

## Working with an AI assistant

`AGENTS.md` at the repository root asks assistants to give hints before
answers and to leave the `sorry`s to you unless you ask. An assistant can fill
most of the guided exercises by itself, so the open exercises are where you
learn the most: deciding what a specification should say is the part that
cannot be delegated.
