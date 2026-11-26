# Working in spec/

The root `AGENTS.md` comes first; these rules add to it. `spec/README.md`
is the map of what is here.

## Where things go

- Definitions go under `spec/Tau/<Area>/`. Theorems about them go under
  `spec/Tau/Proofs/<Area>/`, in a file with the same name. `spec/Tau.lean`
  lists every module, by area, in dependency order; a folder imports only
  from the folders before it.
- A person writes and judges what is outside `spec/Tau/Proofs/`; what is
  inside it only has to compile. So a main theorem's statement is also a
  named proposition in `spec/Tau/Claims.lean`, proved in
  `spec/Tau/Proofs/Claims.lean` by that theorem, and a definition that a
  main statement needs goes in the definitions tree, not in a proof file.
- Nothing in `spec/` imports from `course/`. `spec/tests/` (`TauTest`) tests
  the specification alone; a test that needs the course's tables or
  exercises goes in `course/tests/` (`CourseTest`).

## What a definition must be

- No `sorry` under `spec/Tau/`. `spec/tests/TauTest/Axioms.lean` pins the
  axioms of the main theorems.
- Every block is a `Tau.Block` (`Tau.Blocks.Basic`). Every block theorem
  gives the output at cycle `t` as a function of earlier inputs.
- Every IR of a program has two meanings: what it computes (`run`,
  `execute`) and its timeline, the words it issues on fixed cycles
  (`Tau.Isa.Event`). Every check compares both and has two theorems,
  `_sound` and `_pins`. A new IR or check needs both.
- The machine and the kernel semantics are written for an arbitrary `Sem`
  (`Tau.Isa.Op`) and must never inspect a value to decide what to do. The
  checker's proof depends on this.

## How a file is written

- Each definition file starts with a module comment that says what the
  thing is, where tau-tpu uses it, and which terms a newcomer should look
  up, and ends with the doc sections it specifies (`Docs: Machine 2.5`). It
  does not teach digital design or compilers.
- In a comment, name another Lean file by its module (`Tau.Machine.SliceLevel`),
  not its path, so that moving a folder does not change the comment. Name
  folders, and files that are not Lean, by their path.
- A comment at the top level of a long proof (`  -- ...`) is kept as an
  outline in the exercise that `scripts/make-exercises.py` makes from it, so
  write such comments.
