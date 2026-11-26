# Working in tau-tpu

## Build and test

```bash
lake build                                   # library, proofs, both test suites, tools
lake build Specify Prove Work                # the course's exercise files
cmake -S compiler -B compiler/build -G Ninja -DMLIR_DIR=/usr/lib/llvm-21/lib/cmake/mlir
cmake --build compiler/build                 # tauc and tau-opt
scripts/check-examples.sh                    # compile every example; check and run every stage
python3 scripts/make-exercises.py            # regenerate course/Prove/
PYTHONPATH=compiler/python python3 -m tau examples/paced/kernel.py -o out   # trace a Python program
(cd course/book && lake build)               # check every Lean example in the book
```

Run every command from the repository folder. Installing the tools is
"Setup" in `README.md`. The Lean version is pinned in `lean-toolchain`. The
library has no dependencies; do not add Mathlib. The book in `course/book/`
is a separate Lake package because it depends on Verso.

## Rules for each folder

Before you change files in one of these folders, read its own rules:

- `spec/AGENTS.md`: the Lean specification, its proofs and its tests.
- `compiler/AGENTS.md`: the C++ compiler and the Python frontend.
- `course/AGENTS.md`: the course's exercises and tests.
- Docs/README 1 (`docs/README.md`): the docs.

These hold everywhere:

- A fact is stated once. What the machine, a program and a compiler are
  meant to be is in `docs/`, and nowhere else: cite a section ("Machine
  3.4") instead of restating it, and do not add another docs folder. Each
  folder's README says what is in that folder and nothing more.
- Every rewrite of a program is a pass with a file of its own and a check.
- Sizes are parameters. A theorem holds for every size; a check at one fixed
  size is a test.
- To add a feature, follow the book chapter "Extending the machine"
  (`course/book/TauBook/Extending.lean`).

## Change these together

| When you change | Also change |
|---|---|
| the install commands in `README.md` ("Setup") | `.github/workflows/ci.yml` and `docker/Dockerfile` |
| a table in a doc | its rows in `course/Specify/Support/Tables.lean` and the definition in `spec/Tau/` (Docs/README 1) |
| the image (Machine 3.10) | `spec/Tau/Isa/Encode.lean` and `encodeEntry` in `compiler/lib/Passes/Encode.cpp`; `tau-check --encode` fails until they agree |
| what the compiler writes | `examples/*/*/stages/`, with `UPDATE_STAGES=1 scripts/check-examples.sh`; and `docs/Formats.md` if a format changes |
| `compiler/lib/Passes/Unroll.cpp` or `Schedule.cpp` | the line numbers that `course/Specify/IR/ReadCpp.lean` and `course/Specify/Support/Tables.lean` quote; a test fails until you do |
| a proof under `spec/Tau/Proofs/` | `course/Prove/`, by rerunning `scripts/make-exercises.py` |
| a main theorem | its statement in `spec/Tau/Claims.lean` and the line that proves it in `spec/Tau/Proofs/Claims.lean` |
| an IR, step, check or main theorem, added or renamed | "The map" and "Status" in `spec/README.md`, which name every one and say how each claim stands |
| a kernel operation in the dialect | a function in `compiler/python/tau/` that traces it and computes it |

## Words

One word for each thing, in the docs, the Lean, the C++ and all prose.

| Say | For | Also fine | Not |
|---|---|---|---|
| machine | what the docs describe; `Machine/SliceLevel.lean` and `Machine/CellLevel.lean` are two descriptions of it | machine config, for its description (`Tau.Config`, `tau::Machine`, `machines/`) | chip, processor |
| slice-level machine, cell-level machine | those two descriptions | | architectural, circuit |
| block | a clocked component, `Tau.Block` | component | |
| IR | one of the representations a program takes in the compiler (Compiler 2) | | form |
| stream | what carries words between slices, `Tau.Stream` | | track |
| entry | one item of a slice's program, `Tau.TimedEntry`, `tau.entry` | timed entry | |
| trace | what the Python frontend does to a program | | record |
| pin | a cycle attached to an operation | `at`, its name in Python and MLIR | |

## Helping a student

The course teaches writing specifications. The student writes definitions
and statements from a source that is not Lean; proofs are mostly yours to
write and theirs to review. When someone is working through the course:

- Never write a definition for a file under `course/Specify/`, and never
  replace a `todo` there. That is the exercise. If asked, give a hint: which
  sentence of the source to read again, or one input on which their
  definition and the table differ.
- Never write a statement under "State" for them. Discuss whether theirs
  says the right thing: is it what a user relies on, can its hypotheses be
  met, would a wrong definition also satisfy it?
- In the first five chapters (through "Multiply-accumulate"), do not fill in
  a `sorry` in `course/Prove/` unless the student asks for the solution.
  Give a hint first: name the tactic or the lemma, then show the next goal.
  The solutions are the files under `spec/Tau/Proofs/`.
- After that, you may prove what the student asks you to prove. Prove exactly
  the statement you were given, about the definition you were given.
  - Do not change a definition or a statement. If the statement is false,
    say so and show an input that makes it false.
  - If you are stuck, show the goal you are stuck on. Do not add a
    hypothesis to get past it without saying so.
  - Leave no `sorry`. If part is unproved, say which part.
  - Report every file you changed.
- `course/Specify/Method/Review.lean` contains proofs that are wrong on
  purpose. Do not point out what is wrong with them unless asked for the
  answer.
- Do not explain digital design or compiler theory at length. Name the term
  and point to the reading list in the book.
