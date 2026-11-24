# The tau compiler

A small compiler on MLIR 21. It reads a kernel in the `tau` dialect and writes
a timed program for a tau-tpu chip.

```
include/tau/Dialect/     the dialect: types, kernel operations, instructions
lib/Dialect/             the dialect's C++
lib/Transforms/          passes on kernels: simplify, unroll
lib/Target/              passes towards the chip: place, schedule, route;
                         and the writers of the JSON files
tools/tau-opt/           run passes and print MLIR
tools/tauc/              the compiler driver
```

## The passes

| Pass | From | To |
|---|---|---|
| `tau-simplify` | a kernel | a kernel without repeated `relu` or `max`/`min` of a word with itself |
| `tau-unroll` | a kernel | a kernel with no loops |
| `tau-place` | a kernel with no loops | instructions (`tau.i.*`), each with a slice; buffers have addresses |
| `tau-schedule` | instructions | instructions, each with a cycle (`time`) |
| `tau-route` | timed instructions | timed instructions whose results have streams (`east`, `stream`) |

Each pass is an ordinary MLIR pass and leaves its result in the IR. The
comment at the top of each file in `lib/Target/` explains its method.

## Tools

`tau-opt` runs passes and prints the result. Passes can be run one at a time,
feeding the printed MLIR back in:

```bash
build/bin/tau-opt ../examples/linear/kernel.mlir --tau-simplify --tau-unroll --tau-place
build/bin/tau-opt ../examples/linear/kernel.mlir --tau-simplify --tau-unroll --tau-place \
  | build/bin/tau-opt --tau-schedule \
  | build/bin/tau-opt --tau-route
```

`tau-place` takes the chip as an option: `--tau-place='chip=../chips/tau9.json'`.

`tauc` runs all five passes and writes what each produced:

```bash
build/bin/tauc ../examples/linear/kernel.mlir -o out
build/bin/tauc ../examples/linear/kernel.mlir -o out --chip ../chips/tau9.json --print-mlir
```

The files are listed in `../docs/formats.md`.

## Checking each pass

Nothing in this directory is proved. Each pass is checked through its output:

```bash
tau-check out/kernel.json out/simplified.json
tau-check out/kernel.json out/unrolled.json
tau-check out/kernel.json out/placed.json
tau-check out/kernel.json out/scheduled.json
tau-check out/kernel.json out/compiled.json
```

Every check compares against the kernel as written, and each has a soundness
theorem in `Tau/Proofs/Check/`. The first file rejected names the faulty
pass. If a pass has a bug, the result is a rejected file, not a wrong answer.

`scheduled.json` is the schedule with a routing that cannot be wrong: every
word has a stream to itself, on a chip given enough streams. So a schedule
that is accepted followed by a finished program that is rejected means the
routing is at fault.

In addition, `Tau/Passes/Simplify.lean` and `Tau/Passes/Unroll.lean` are Lean
models of the first two passes, proved to keep what a kernel computes. Those
proofs are about the models, not about the C++.

## Limits

- Loops do not nest.
- Each kind of operation runs on the first slice of that kind; the second
  matrix and rearrangement slices of the standard chip are unused.
- A value that is not consumed by the very next operation waits in memory.
- Groups of instructions run one after another; two groups never overlap in
  time, even when they could.
