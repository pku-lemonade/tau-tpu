# Working in tau-tpu

## Build and test

```bash
lake build Tau TauTest tau-sim tau-check     # library, proofs, tests, tools
lake build Specify Prove Work                # the course's exercise files
cmake -S compiler -B compiler/build -G Ninja -DMLIR_DIR=/usr/lib/llvm-21/lib/cmake/mlir
cmake --build compiler/build                 # tauc and tau-opt
scripts/check-examples.sh                    # compile every example; check and run every stage
python3 scripts/make-exercises.py            # regenerate course/Prove/
PYTHONPATH=compiler/python python3 -m tau examples/paced/kernel.py -o out   # record a Python program
(cd course/book && lake build)               # check every Lean example in the book
```

Run every command from the repository folder. Installing the tools is
"Setup" in `README.md`. CI (`.github/workflows/ci.yml`) and
`docker/Dockerfile` run the same install commands; change all three
together.

The Lean version is pinned in `lean-toolchain`. The library has no
dependencies; do not add Mathlib. The book in `course/book/` is a separate
Lake package because it depends on Verso.

## Conventions

- Definitions go under `spec/Tau/<Area>/`. Theorems about them go under
  `spec/Tau/Proofs/<Area>/`, in a file with the same name.
- No `sorry` under `spec/Tau/`. `spec/tests/TauTest/Axioms.lean` pins the
  axioms of the main theorems.
- A person writes and judges what is outside `spec/Tau/Proofs/`; what is inside it
  only has to compile. So a main theorem's statement is also a named
  proposition in `spec/Tau/Claims.lean`, proved in `spec/Tau/Proofs/Claims.lean` by
  that theorem, and a definition that a main statement needs goes in the
  definitions tree, not in a proof file. Add both lines when you add a main
  theorem.
- Every hardware component is a `Tau.Block` (`spec/Tau/Blocks/Basic.lean`). Every
  block theorem gives the output at cycle `t` as a function of earlier inputs.
- Every form of a program has two meanings: what it computes (`run`,
  `execute`) and its timeline, the words it issues on fixed cycles
  (`spec/Tau/Isa/Event.lean`). Every check compares both, and has two theorems,
  `_sound` and `_pins`. A new form or check needs both.
- Every rewrite of a program is a pass with a file of its own and a check.
  Do not put a rewrite in a file writer.
- Sizes are parameters. A theorem holds for every size; a check at one fixed
  size is a test.
- The machine and the kernel semantics are written for an arbitrary `Sem`
  (`spec/Tau/Isa/Op.lean`) and must never inspect a value to decide what to do. The
  checker's proof depends on this.
- Each definition file starts with a module comment that says what the thing
  is, where tau-tpu uses it, and which terms a newcomer should look up, and
  ends with the doc sections it specifies (`Docs: Machine 2.5`). It does not
  teach digital design or compilers.
- `course/Work/` is for a student's own files. Do not put project code
  there.
- `course/Prove/` is generated. Change the proof under `spec/Tau/Proofs/` and
  rerun `scripts/make-exercises.py`; never edit an exercise file by hand in a
  commit. The script lists which proofs are exercises; the course asks only
  for short ones. A comment at the top level of a proof (`  -- ...`) is kept
  in the exercise as an outline, so write such comments in long proofs.
- `course/Specify/` holds the specification exercises: a definition for the
  student to write from a source, with tests. `course/Specify/Support/Tables.lean`
  has the tests, and `spec/tests/TauTest/Docs.lean` and
  `spec/tests/TauTest/SpecSolutions.lean` run them on a solution, so an
  exercise that cannot be solved fails the build. Commit these files with
  `todo` in place of the definitions.
- All shared prose about the specification is in `docs/`, and a fact is
  stated there once. `Machine.md`, `Programs.md` and `Compiler.md` give the
  intent, as a designer would write it. `Formats.md` describes the JSON
  formats the tools exchange. `docs/README.md` has the rules for the docs
  (section 1). Do not add another docs folder, and do not restate a doc in a
  module comment, another README or the book: cite its section, as
  "Machine 3.4", "Formats 3" or "Docs/README 1".
- Call the thing the docs describe *the machine*: `spec/Tau/Machine/Arch.lean`
  (the slice-level machine) and `spec/Tau/Machine/Circuit.lean` (the cell-level
  machine) are two descriptions of it. Do not call it a chip or a processor in
  prose. Use `machine` consistently across docs, Lean, C++ (`tau::Machine`,
  `--machine`), and `machines/`.
- A doc says less than the Lean on purpose, and the Lean decides where they
  differ. It belongs to the project, and the course specifies from it, so do
  not fill in what a doc leaves open: the `...Decisions` tables in
  `course/Specify/Support/Tables.lean` list what must stay unsaid. A section
  keeps its number.
- Every table in a doc that gives a result for an input is a row in
  `course/Specify/Support/Tables.lean`, run on the definitions by
  `spec/tests/TauTest/Docs.lean`. Change the table, the rows and the definition
  in `spec/Tau/` together.
- Outside `docs/` and `spec/`, each part documents itself and nothing else:
  `compiler/README.md` says how this compiler works and its limits, the
  comment at the top of `compiler/python/tau/__init__.py` how the frontend
  records, `spec/README.md` the Lean map and claim status, and the root
  `README.md` how to set up and try the project.
- `course/Specify/ReadCpp.lean` quotes lines of the C++ by number. After
  changing `Unroll.cpp` or `Schedule.cpp`, renumber it; a test fails until
  you do.
- To add a feature, follow the path in the book chapter "Extending the
  machine" (`course/book/TauBook/Extending.lean`).
- `examples/*/stages/` (`nn/linear`, `ops/elementwise`, `nn/residual`) are
  copies of `tauc`'s output, for readers without the compiler; the book points
  to them. After changing the compiler, refresh them with
  `UPDATE_STAGES=1 scripts/check-examples.sh`.
- After changing the compiler or the JSON formats, run
  `scripts/check-examples.sh` and update `docs/Formats.md`.
- The image is described in section 3.10 of `docs/Machine.md`, specified
  in `spec/Tau/Isa/Encode.lean`, and written by `encodeEntry` in
  `compiler/lib/Target/EmitMachine.cpp`. Change them together. Its tables
  are tested against the Lean, and `tau-check --encode` fails until the C++
  agrees with it.
- The frontend (`compiler/python/tau/`) is one Python module with no dependencies.
  It records; it does not translate. An operation added to the dialect needs
  a function there with both behaviours, recording and computing, and the
  computing one must follow `spec/Tau/Isa/Word.lean`. An example written in
  Python is `examples/.../kernel.py` and binds its program to `kernel`.
- `spec/README.md` ("The map" and "Status") names every form, step, check and
  main theorem, and says how each claim stands. Update both when you add or
  rename one. They point to Lean files and doc sections and do not restate
  definitions.

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
- `course/Specify/Review.lean` contains proofs that are wrong on purpose. Do
  not point out what is wrong with them unless asked for the answer.
- Do not explain digital design or compiler theory at length. Name the term
  and point to the reading list in the book.
