# Working in course/

The root `AGENTS.md` comes first; these rules add to it, and its section
"Helping a student" says how to help someone taking the course.
`course/README.md` says what is where.

- `course/Work/` is for a student's own files. Do not put project code
  there.
- `course/Prove/` is generated. Change the proof under `spec/Tau/Proofs/`
  and rerun `scripts/make-exercises.py`; never edit an exercise file by hand
  in a commit. The script lists which proofs are exercises; the course asks
  only for short ones.
- `course/Specify/` holds the specification exercises: a definition for the
  student to write from a source, with tests. It has the folders of
  `spec/Tau/`, as `course/Prove/` has those of `spec/Tau/Proofs/`: an
  exercise about `spec/Tau/<Area>/` goes in `course/Specify/<Area>/`, under
  the name of the file it asks for when there is one. The exercises about
  the method are in `course/Specify/Method/`.
- `course/Specify/Support/Tables.lean` has the tests. `course/tests/`
  (`CourseTest`) runs them on the definitions in `spec/Tau/` and on a
  solution, so an exercise that cannot be solved fails the build. Commit the
  exercise files with `todo` in place of the definitions.
- The `...Decisions` tables in `Tables.lean` list what a doc leaves unsaid
  (Docs/README 1). Do not fill it in in the doc.
