# The course

A self-paced course in Lean 4, built on the tau-tpu development. It assumes
programming experience and a first course in discrete mathematics. It does not
assume a course in digital design, computer architecture or compilers; where a
term from those fields is needed, the chapter names it and points to something
to read.

Plan for about 28 days of roughly six focused hours each.

## Start

1. Install [elan](https://github.com/leanprover/elan) and
   [VS Code](https://code.visualstudio.com/) with the Lean 4 extension, or use
   the container in `docker/`.
2. From the repository root run `lake build`. The first build downloads Lean.
3. Read the book, starting with "Start here". The source is in `book/`; build
   it with the commands below, or read the `.lean` files directly.
4. Do the exercises in `Exercises/`.

## The book

```bash
cd course/book
lake exe tau-book        # writes the HTML to _out/
```

The first build compiles Verso and takes a while.

## The exercises

Each file under `Exercises/` is a finished proof file from `Tau/Proofs/` with
the proofs replaced by `sorry`. Open one in VS Code, put the cursor after a
`sorry`, and replace it with a proof. Build one file with, for example:

```bash
lake build Exercises.Blocks.ShiftRegister
```

An exercise file imports the finished library, not other exercise files. You
can skip a file and come back.

The solutions are the files of the same name under `Tau/Proofs/`. Looking is
allowed; the point is to be able to write the proof afterwards without
looking.

Every chapter also has open exercises, where you write the definition or the
theorem statement yourself, and challenge exercises. Those have no file. Make
your own under `Exercises/` and import what you need.

## Order

| Days | Chapter | Exercise files |
|---|---|---|
| 0 | Start here | none |
| 1-2 | Shift register | `Blocks/Basic`, `Blocks/ShiftRegister` |
| 3 | Accumulator | `Blocks/Accumulator` |
| 4 | Multiply-accumulate | `Blocks/Mac`, `Data/Lane` |
| 5 | Pipeline and sequencer | `Blocks/Pipeline`, `Blocks/Sequencer` |
| 6-7 | Memory | `Blocks/Memory` |
| 8-10 | Systolic array | `Blocks/SystolicArray` |
| 11-13 | The slice-level machine | none; you write schedules |
| 14-15 | Kernels and loop unrolling | `Passes/Unroll` |
| 16-17 | Expressions and simplification | `Passes/Simplify` |
| 18-22 | The checker | `SliceLevel/Map`, `IR/Map`, `Check/Sound`, `Check/Stages` |
| 23-27 | The cell-level machine | `CellLevel/Refine` |
| 28 | End to end | `EndToEnd` |

## Working with an AI assistant

`AGENTS.md` at the repository root asks assistants to give hints before
answers and to leave the `sorry`s to you unless you ask. An assistant can fill
most of the guided exercises by itself, so the open exercises are where you
learn the most: deciding what a specification should say is the part that
cannot be delegated.
