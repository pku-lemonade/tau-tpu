# Working in tau-tpu

## Build and test

```bash
lake build Tau TauTest tau-sim tau-check     # library, proofs, tests, tools
lake build Specs Exercises Work              # the course's exercise files
cmake -S compiler -B compiler/build -G Ninja -DMLIR_DIR=/usr/lib/llvm-21/lib/cmake/mlir
cmake --build compiler/build                 # tauc and tau-opt
scripts/check-examples.sh                    # compile every example; check and run every stage
python3 scripts/make-exercises.py            # regenerate course/Exercises/
```

Run every command from the repository folder. Installing the tools is
"Setup" in `README.md`. CI (`.github/workflows/ci.yml`) and
`docker/Dockerfile` run the same install commands; change all three
together.

The Lean version is pinned in `lean-toolchain`. The library has no
dependencies; do not add Mathlib. The book in `course/book/` is a separate
Lake package because it depends on Verso.

## Conventions

- Definitions go under `Tau/<Area>/`. Theorems about them go under
  `Tau/Proofs/<Area>/`, in a file with the same name.
- No `sorry` under `Tau/`. `tests/TauTest/Axioms.lean` pins the axioms of the
  main theorems.
- A person writes and judges what is outside `Tau/Proofs/`; what is inside it
  only has to compile. So a main theorem's statement is also a named
  proposition in `Tau/Claims.lean`, proved in `Tau/Proofs/Claims.lean` by
  that theorem, and a definition that a main statement needs goes in the
  definitions tree, not in a proof file. Add both lines when you add a main
  theorem.
- Every hardware component is a `Tau.Block` (`Tau/Blocks/Basic.lean`). Every
  block theorem gives the output at cycle `t` as a function of earlier inputs.
- Sizes are parameters. A theorem holds for every size; a check at one fixed
  size is a test.
- The machine and the kernel semantics are written for an arbitrary `Sem`
  (`Tau/Isa/Op.lean`) and must never inspect a value to decide what to do. The
  checker's proof depends on this.
- Each definition file starts with a module comment that says what the thing
  is, where tau-tpu uses it, and which terms a newcomer should look up. It
  does not teach digital design or compilers.
- `course/Work/` is for a student's own files. Do not put project code
  there.
- `course/Exercises/` is generated. Change the proof under `Tau/Proofs/` and
  rerun `scripts/make-exercises.py`; never edit an exercise file by hand in a
  commit. The script lists which proofs are exercises; the course asks only
  for short ones. A comment at the top level of a proof (`  -- ...`) is kept
  in the exercise as an outline, so write such comments in long proofs.
- `course/Specs/` holds the specification exercises: a definition for the
  student to write from a source, with tests. `Specs/Tables.lean` has the
  tests, and `tests/TauTest/Manual.lean` and `tests/TauTest/SpecSolutions.lean`
  run them on a solution, so an exercise that cannot be solved fails the
  build. Commit these files with `todo` in place of the definitions.
- `course/architecture-manual.md` is course material: the chip in words and
  tables, which the hardware exercises specify from. It says less than the
  Lean on purpose and is not documentation of the repository. Each of its
  tables is a row in `Specs/Tables.lean`; change the two together, and the
  definition in `Tau/` with them.
- `course/Specs/ReadCpp.lean` quotes lines of the C++ by number. After
  changing `Unroll.cpp` or `Schedule.cpp`, renumber it; a test fails until
  you do.
- To add a feature, follow the path in the book chapter "Extending the
  machine" (`course/book/TauBook/Extending.lean`).
- `examples/*/stages/` (linear, elementwise, residual) are copies of
  `tauc`'s output, for readers without the compiler; the book points to
  them. After changing the compiler, refresh them with
  `UPDATE_STAGES=1 scripts/check-examples.sh`.
- After changing the compiler or the JSON formats, run
  `scripts/check-examples.sh` and update `docs/formats.md`.
- `docs/overview.md` names every form, pass, check and main theorem, and the
  README table "What is proved" says how each claim stands. Update both when
  you add or rename one. They point to Lean files and do not restate
  definitions.

## Helping a student

The course teaches writing specifications. The student writes definitions
and statements from a source that is not Lean; proofs are mostly yours to
write and theirs to review. When someone is working through the course:

- Never write a definition for a file under `course/Specs/`, and never
  replace a `todo` there. That is the exercise. If asked, give a hint: which
  sentence of the source to read again, or one input on which their
  definition and the table differ.
- Never write a statement under "State" for them. Discuss whether theirs
  says the right thing: is it what a user relies on, can its hypotheses be
  met, would a wrong definition also satisfy it?
- In the first five chapters (through "Multiply-accumulate"), do not fill in
  a `sorry` in `course/Exercises/` unless the student asks for the solution.
  Give a hint first: name the tactic or the lemma, then show the next goal.
  The solutions are the files under `Tau/Proofs/`.
- After that, you may prove what the student asks you to prove. Prove exactly
  the statement you were given, about the definition you were given.
  - Do not change a definition or a statement. If the statement is false,
    say so and show an input that makes it false.
  - If you are stuck, show the goal you are stuck on. Do not add a
    hypothesis to get past it without saying so.
  - Leave no `sorry`. If part is unproved, say which part.
  - Report every file you changed.
- `course/Specs/Review.lean` contains proofs that are wrong on purpose. Do
  not point out what is wrong with them unless asked for the answer.
- Do not explain digital design or compiler theory at length. Name the term
  and point to the reading list in the book.
