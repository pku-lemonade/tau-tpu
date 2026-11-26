# The tau compiler

A small compiler on MLIR 21. It reads a program in the `tau` dialect and
writes a timed program for a tau-tpu machine, and its image.

This page says how *this* compiler works and where it stops. What any
compiler for the machine has to deliver, the forms a program takes and what
every step must keep, is [`Tau/Docs/Compiler.md`](../Tau/Docs/Compiler.md).
The files it writes are section 5 of
[`Tau/Docs/README.md`](../Tau/Docs/README.md).

```
include/tau/Dialect/     the dialect: types, kernel operations, instructions,
                         entries
lib/Dialect/             the dialect's C++
lib/Transforms/          passes on kernels: inline, simplify, unroll
lib/Target/              passes towards the machine: place, schedule, route,
                         slice, fold; and the writers of the JSON files
tools/tau-opt/           run passes and print MLIR
tools/tauc/              the compiler driver
```

## The passes

One pass for each step of Compiler 4, but the last: the image is written
from the result of `tau-fold` by `lib/Target/Emit.cpp`.

| Pass | Step | Method |
|---|---|---|
| `tau-inline` | inline | copies each called kernel in, and adds the call's origin to its pins |
| `tau-simplify` | simplify | three rewrites: `relu` of `relu`, and `max` or `min` of a word with itself; never removes a pinned operation |
| `tau-unroll` | unroll | one copy of the body per iteration, with the iteration filled into positions and pins |
| `tau-place` | place | buffers over the memories in turn; each operation on the nearest slice of its kind; chains of operations into *groups* whose words travel directly |
| `tau-schedule` | schedule | the timing rule fixes the cycles within a group; a pinned group starts where its pin puts it, any other after the groups before it |
| `tau-route` | route | two words share a stream only if they are never in the same moving slot |
| `tau-slice` | slice | replaces each operand by the stream its word is on, and sorts the entries by slice |
| `tau-fold` | fold | in each slice, the longest runs of like entries at equal steps of cycle and address |

Each pass is an ordinary MLIR pass and leaves its result in the IR. The
comment at the top of each file in `lib/Transforms/` and `lib/Target/`
explains its method in full.

The program takes three shapes in the IR. Up to `tau-place` it is kernel
operations (`tau.load`, `tau.add`). From `tau-place` to `tau-route` it is
instructions joined by the words they pass on: the result of one is the
operand of another. After `tau-slice` it is what the machine has: each slice's
own list of entries, which name streams.

## How a pin is met

`tau-place` puts each pin on the instruction that issues the word. The
instructions of a group are a fixed distance apart, so the pins of a group
have to agree with those distances. The pass works the distances out as it
builds a group: a pinned operation joins only if its pin agrees with the pins
already there, and otherwise the value between the two waits in memory.
`tau-schedule` then starts each pinned group where its pins put it. Groups
overlap in time when pins ask for it.

The compiler refuses, with the line of the operation:

- a pin too early for the instructions before it in its group;
- two instructions at one slice on one cycle;
- a read of memory put before the write it depends on, or a matrix slice
  given two products at once.

The distance between two operations depends on the machine and on which memory
`tau-place` gave each buffer. To pin a chain of operations that should stay
together, compile once without pins and read the cycles off
`tau-sim --timeline out/image.json`.

## Tools

Commands here are run from the repository folder, after building as in
"Setup" in the [root README](../README.md#setup).

`tau-opt` runs passes and prints the result. Passes can be run one at a time,
feeding the printed MLIR back in:

```bash
compiler/build/bin/tau-opt examples/linear/kernel.mlir --tau-simplify --tau-unroll --tau-place
compiler/build/bin/tau-opt examples/linear/kernel.mlir --tau-simplify --tau-unroll --tau-place \
  | compiler/build/bin/tau-opt --tau-schedule \
  | compiler/build/bin/tau-opt --tau-route \
  | compiler/build/bin/tau-opt --tau-slice --tau-fold
```

`tau-place` takes the machine as an option: `--tau-place='chip=chips/tau9.json'`.

`tauc` runs all eight passes and writes what each produced:

```bash
compiler/build/bin/tauc examples/linear/kernel.mlir -o out
compiler/build/bin/tauc examples/linear/kernel.mlir -o out --chip chips/tau9.json --print-mlir
```

The program is the last function of the file; the functions before it are
kernels it may call. The input can be written by hand or recorded from
Python:

```bash
PYTHONPATH=frontend python3 -m tau examples/paced/kernel.py -o out   # out/kernel.mlir
compiler/build/bin/tauc out/kernel.mlir -o out
```

## Nothing here is proved

Each pass is judged through its output (Compiler 7). `tau-check` takes the
input of a pass and its output:

```bash
lake exe tau-check out/source.json out/kernel.json          # tau-inline
lake exe tau-check out/kernel.json out/simplified.json      # tau-simplify
lake exe tau-check out/simplified.json out/unrolled.json    # tau-unroll
lake exe tau-check out/unrolled.json out/placed.json        # tau-place
lake exe tau-check out/placed.json out/scheduled.json       # tau-schedule
lake exe tau-check out/scheduled.json out/routed.json       # tau-route
lake exe tau-check out/routed.json out/sliced.json          # tau-slice
lake exe tau-check out/sliced.json out/compiled.json        # tau-fold
lake exe tau-check out/compiled.json out/image.json         # the image
lake exe tau-check out/source.json out/image.json           # all of it at once
```

If a pass has a bug, the result is a rejected file that names the pass, not
a wrong answer. The checks and their theorems are listed in section 3 of
[`Tau/Docs/README.md`](../Tau/Docs/README.md).

Two steps also have a copy in Lean, and the compiler is compared with the
copy on every example:

```bash
lake exe tau-check --unroll out/simplified.json out/unrolled.json
lake exe tau-check --encode out/compiled.json out/image.json
```

`tau-simplify` has no copy. Its three rewrites are the ones the checks apply
to expressions before comparing them (`Tau/Check/Simplify.lean`), which is
why its output is accepted.

## Limits

- Loops do not nest, and a call is not inside a loop.
- A loop is unrolled before placement. A program is as large as its
  iterations until `tau-fold` merges what it can, and compiling and checking
  take time in proportion.
- An operation runs on the slice of its kind nearest to its operand. Nothing
  balances load between two slices of a kind.
- A value that is not consumed by the very next operation waits in memory.
- Without pins, groups of instructions run one after another; two groups
  never overlap in time, even when they could. Storing a matrix therefore
  saves instructions but not cycles. A pin is the only way to make groups
  overlap.
- A pinned load with more than one use is read into a scratch word, even if
  one of its uses could have taken it directly.
- The image is a list of numbers of no fixed width, not bit fields.
