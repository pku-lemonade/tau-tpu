# Working in tau-tpu

## Build and test

```bash
lake build Tau TauTest tau-sim tau-check     # library, proofs, tests, tools
cmake -S compiler -B compiler/build -G Ninja -DMLIR_DIR=/usr/lib/llvm-21/lib/cmake/mlir
cmake --build compiler/build                 # tauc and tau-opt
scripts/check-examples.sh                    # compile every example; check and run every stage
python3 scripts/make-exercises.py            # regenerate course/Exercises/
```

The Lean version is pinned in `lean-toolchain`. The library has no
dependencies; do not add Mathlib. The book in `course/book/` is a separate
Lake package because it depends on Verso.

## Conventions

- Definitions go under `Tau/<Area>/`. Theorems about them go under
  `Tau/Proofs/<Area>/`, in a file with the same name.
- No `sorry` under `Tau/`. `tests/TauTest/Axioms.lean` pins the axioms of the
  main theorems.
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
  commit. A comment at the top level of a proof (`  -- ...`) is kept in the
  exercise as an outline, so write such comments in long proofs.
- To add a feature, follow the path in the book chapter "Extending the
  machine" (`course/book/TauBook/Extending.lean`).
- `examples/linear/stages/` is a copy of `tauc`'s output. After changing the
  compiler, refresh it with `UPDATE_STAGES=1 scripts/check-examples.sh`.
- After changing the compiler or the JSON formats, run
  `scripts/check-examples.sh` and update `docs/formats.md`.

## Helping a student

When someone is working through the course:

- Give a hint before an answer. A good first hint names the tactic or the
  lemma; a second hint shows the next goal.
- Do not fill in a `sorry` in `course/Exercises/` unless the student asks for
  the solution. The solutions are the files under `Tau/Proofs/`; point there
  when asked.
- For the open exercises, where the student writes a specification or a
  theorem statement, first discuss whether it says the right thing. Help with
  the proof only after that.
- Do not explain digital design or compiler theory at length. Name the term
  and point to the reading list in the book.
