# The course

A self-paced course in writing specifications in Lean 4, built on the
tau-tpu development. You learn to turn descriptions written in words, a compiler
written in C++ and a frontend written in Python into Lean definitions and
statements. You prove a few short
things yourself, so that you know what a proof is, and learn to hand the
long proofs to an AI agent and judge what comes back.

It assumes programming experience and a first course in discrete
mathematics. It does not assume a course in digital design, computer
architecture or compilers; where a term from those fields is needed, the
chapter names it and the reading list says where to look it up.

Plan for about 27 days (Day 0 plus 26 days) of roughly six focused hours
each. The day counts are estimates; nobody has been timed. `Work/Log.md`
is a table for your own times.

## Start

1. Do "Setup" in the [root README](../README.md#setup). The compiler part
   is optional.
2. In VS Code, open `course/Work/Scratch.lean`. Nothing should be underlined
   in red.
3. Read the book, starting with "Start here" and "Working in Lean".
4. Before Day 1, play the first three worlds of the Natural Number Game
   (about two hours; linked in the reading list at the end of the book).

## The book

The chapters are the files in `book/TauBook/`, in the order listed in
`book/TauBook.lean`. You can read them there directly: the text after the
`#doc` line is the chapter. Note that `{docstring Tau.Foo}` lines do not
expand in raw `.lean` files; when reading them directly in VS Code, use
Go to Definition (`F12` or Cmd/Ctrl-click) on the name to view the
definition and its docstring. To read them as web pages:

```bash
cd course/book
lake exe tau-book        # writes the HTML to _out/html-multi/
python3 -m http.server -d _out/html-multi 8000
```

Then open `http://localhost:8000` in a browser. The first build downloads
and compiles Verso, the tool the book is written in, and takes about ten
minutes. Every Lean
example in the book is checked when the book is built.

## Where things are

| Place | What is in it | Who edits it |
|---|---|---|
| `docs/` | The shared prose specs: the machine, programs, the compiler and JSON formats, as their designers would write them. The source for most chapters, and what you specify from. They say less than the Lean on purpose. | Nobody |
| `compiler/` | The Python tracing frontend (`compiler/python/tau/`) and the C++/MLIR compiler. The source for the compiler and frontend chapters. | Nobody |
| `course/Specify/` | One file per thing you specify, with support code under `Support/` and notes under `Answers/`. | You write the definitions and the statements |
| `course/Prove/` | A few proof files with some proofs replaced by `sorry`. | You fill in the proofs |
| `course/Work/` | Your own files: a scratch file, your questions for the architect, your claims table, your times. | You |
| `spec/` | The finished Lean development (`spec/Tau/`), its tools (`tau-sim`, `tau-check`), its tests (`spec/tests/`), its map (`spec/README.md`), and `spec/Tau/Claims.lean`. | Nobody, except in the exercises that say to work on a branch |

## The three kinds of exercise

**Specify.** Each chapter from "Writing a specification" on names a source
and a file under `course/Specify/`. Read the source, then write your
definition in the file in place of `todo`. The file has `#eval report`
lines; put the cursor on one in VS Code to see which rows of the source's
table your definition gets right. The steps are at the top of every file.

```bash
lake build Specify.Memory    # prints the same reports in a terminal
```

There is one rule: write your definition before you open the one in `spec/Tau/`.
The docs are in `docs/` and you read them first. It is the Lean files
under `spec/Tau/<Area>/` that you leave closed until you have written your own.

**State.** In the same file, under "State", write as a proposition what
should be true of what you defined. Nothing checks a statement but your
judgement, the statement in `spec/Tau/Proofs/`, and an attempt to prove it.

**Prove.** A file under `course/Prove/` in which a few proofs have been
replaced by `sorry`. They are the short proofs that show what a
specification means; the long ones are for reading. Put the cursor before a
`sorry`, read the goal in the infoview, and replace the `sorry` with a
proof. A file is finished when this prints no warning about `sorry`:

```bash
lake build Prove.Blocks.ShiftRegister
```

The solution to `course/Prove/X.lean` is `spec/Tau/Proofs/X.lean`. When you
are stuck, follow the list in the chapter "Working in Lean".

Some chapters also have exercises "by hand" (writing a program for the machine)
and a larger, optional challenge.

## Without the C++ compiler

Everything in Lean works without it. Six chapters run the compiler: start
here, kernels, expressions, the checker, pins, and from Python to an image.
The first four each name a folder `examples/.../stages/` that holds what
the compiler writes for that example, so you can read the output instead of
producing it. The last two are about what the compiler does with a pin and
with the end of the flow, and are best read with the compiler built; their
Lean examples and their exercises under `course/Specify/` work without it.

## Order

| Days | Chapter | Specify (`course/Specify/`) | Prove (`course/Prove/`) |
|---|---|---|---|
| 0 | Start here; Working in Lean | | |
| 1-2 | The shift register | | `Blocks/Basic`, `Blocks/ShiftRegister` |
| 3 | The accumulator | | `Blocks/Accumulator` |
| 4 | Multiply-accumulate | | `Blocks/Mac`, `Isa/Word` |
| 5 | Writing a specification | `Candidates`, `Review`, `Repair`, `Provable` | |
| 6 | Pipeline and sequencer | `Pipeline`, `Sequencer` | `Blocks/Pipeline`, `Blocks/Sequencer` |
| 7 | Memory | `Memory` | `Blocks/Memory`, one proof |
| 8-9 | The repeater | `Repeater` | `Blocks/Repeater`, two proofs |
| 10-11 | The systolic array | `SystolicArray` | `Blocks/SystolicArray`, one proof |
| 12-14 | The slice-level machine | `Machine` | none; you write schedules |
| 15-16 | Kernels and loop unrolling | `Kernel`, `Unroll`, `ReadCpp` | `IR/Unroll`, three proofs |
| 17 | Expressions and simplification | `Simplify` | `Check/Simplify` |
| 18-20 | The checker | `OnTime` | `Check/Checker`, `Check/Passes`, two proofs each |
| 21-22 | Pins | `Pins` | `Check/Checker`, one proof; `Check/Passes`, two proofs |
| 23-24 | From Python to an image | `Encode` | none; you read two proofs |
| 25 | The cell-level machine | a statement | none; you read the proof |
| 26 | End to end | your claims table | `EndToEnd` |
| after | Extending the machine | you add features | |

The book ends with a tactic reference and a reading list.

## Working with an AI assistant

The course expects you to use one, in a particular division of work.

- **You** write every definition and every statement. Deciding what a
  specification should say is the part that cannot be handed over.
- **You** do the "Prove" exercises of the first three component chapters
  (through "Multiply-accumulate") yourself, so that you can read a proof
  and a goal.
- **The assistant** may write the other proofs. You review what comes back,
  as the chapter "Writing a specification" shows: the statement is the one
  you asked for, its hypotheses can be met, it is about your definition, it
  rests on no `sorry`, and no definition was changed.

`AGENTS.md` at the repository root tells an assistant these rules.
