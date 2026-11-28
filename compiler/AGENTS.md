# Working in compiler/

The root `AGENTS.md` comes first; these rules add to it.
`compiler/README.md` says how the compiler works.

## The C++ compiler

- Each pass is one file in `lib/Passes/`, named after the pass, and is
  judged by a check in `spec/Tau/Check/`. A writer in `lib/Emit/` writes what
  the IR holds and changes nothing: a rewrite in a writer has no file of its
  own and no check that can name it. If a step needs an operation the dialect
  does not have, add the operation.
- After changing the compiler, run `scripts/check-examples.sh`.

## The Python frontend

- `python/tau/` is one Python module with no dependencies. It traces; it
  does not translate.
- A kernel operation added to the dialect needs a function there with both
  behaviours, tracing and computing. The computing one follows
  `spec/Tau/Isa/Word.lean` and `spec/Tau/Isa/Value.lean`.
