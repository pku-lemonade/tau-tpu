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
| `tau-place` | a kernel with no loops | instructions (`tau.i.*`), each with a slice; buffers have addresses; decides which matrices to store in a matrix slice |
| `tau-schedule` | instructions | instructions, each with a cycle (`time`) |
| `tau-route` | timed instructions | timed instructions whose results have streams (`east`, `stream`) |

Each pass is an ordinary MLIR pass and leaves its result in the IR. The
comment at the top of each file in `lib/Target/` explains its method.

## Tools

Commands here are run from the repository folder, after building as in
"Setup" in the [root README](../README.md#setup).

`tau-opt` runs passes and prints the result. Passes can be run one at a time,
feeding the printed MLIR back in:

```bash
compiler/build/bin/tau-opt examples/linear/kernel.mlir --tau-simplify --tau-unroll --tau-place
compiler/build/bin/tau-opt examples/linear/kernel.mlir --tau-simplify --tau-unroll --tau-place \
  | compiler/build/bin/tau-opt --tau-schedule \
  | compiler/build/bin/tau-opt --tau-route
```

`tau-place` takes the chip as an option: `--tau-place='chip=chips/tau9.json'`.

`tauc` runs all five passes and writes what each produced:

```bash
compiler/build/bin/tauc examples/linear/kernel.mlir -o out
compiler/build/bin/tauc examples/linear/kernel.mlir -o out --chip chips/tau9.json --print-mlir
```

The files are described in [`docs/formats.md`](../docs/formats.md).

## Checking each pass

Nothing in this directory is proved. Each pass is checked through its output:
`tau-check` takes the input of a pass and its output, and decides whether
they compute the same thing on every buffer contents.

```bash
lake exe tau-check out/kernel.json out/simplified.json      # tau-simplify
lake exe tau-check out/simplified.json out/unrolled.json    # tau-unroll
lake exe tau-check out/unrolled.json out/placed.json        # tau-place
lake exe tau-check out/placed.json out/scheduled.json       # tau-schedule
lake exe tau-check out/scheduled.json out/compiled.json     # tau-route
lake exe tau-check out/kernel.json out/compiled.json        # all five at once
```

Each of the six is a different check with its own soundness theorem in
`Tau/Proofs/Check/`; `tau-check` picks the check from the kinds of the two
files. If a pass has a bug, the result is a rejected file that names the
pass, not a wrong answer. [`docs/overview.md`](../docs/overview.md) lists the
checks and theorems.

A check asks only whether the output computes what the input computes. It
does not ask whether the scheduler kept the instructions that placement
chose, or whether the router kept the cycles that the scheduler chose.

`scheduled.json` is the schedule with a routing that cannot be wrong: every
word has a stream to itself, on a chip given enough streams. `tau-route` then
fits the words onto the streams the chip has.

In addition, `Tau/Passes/Simplify.lean` and `Tau/Passes/Unroll.lean` are Lean
models of the first two passes, proved to keep what a kernel computes. Those
proofs are about the models, not about the C++. For `tau-unroll` the two are
compared: `scripts/check-examples.sh` fails unless the compiler's
`unrolled.json` is the kernel the model gives, up to the numbering of values.

```bash
lake exe tau-check --unroll out/simplified.json out/unrolled.json
```

The model of `tau-simplify` rewrites expressions, not kernels, so it has no
output to compare with the compiler's.

Runs of instructions that one slice issues at a fixed spacing are merged into
repeating entries when the program file is written. This is a property of the
file, not of the IR: in the MLIR every instruction is still separate.

## Limits

- Loops do not nest.
- An operation runs on the slice of its kind nearest to its operand. Nothing
  balances load between two slices of a kind.
- A value that is not consumed by the very next operation waits in memory.
- Groups of instructions run one after another; two groups never overlap in
  time, even when they could. Storing a matrix therefore saves instructions
  but not cycles.
