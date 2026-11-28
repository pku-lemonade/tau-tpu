# The examples

Programs for the machine, each with the buffers to run it on, and how to try
them. Run every command from the repository folder, after "Setup" in the
[root README](../README.md#setup). `out/` can be any folder; `tauc` makes it.

Contents:
- [Try it](#try-it)
- [What is in a folder](#what-is-in-a-folder)
- [The examples](#the-examples)

## Try it

### 1. Without the compiler

Lean alone can check and run the compiler's output for three examples, kept
in their `stages/` folders:

```bash
lake exe tau-check examples/nn/linear/stages/source.json examples/nn/linear/stages/image.json
lake exe tau-sim examples/nn/linear/stages/image.json examples/nn/linear/buffers.json
```

`tau-check` prints `ACCEPT` if the image computes what the source computes;
`tau-sim` prints the buffers at the end. The same program can also be run
in Python, with no compiler and no Lean:

```bash
PYTHONPATH=compiler/python python3 -m tau examples/nn/linear/kernel.py --run examples/nn/linear/buffers.json
```

### 2. From Python

```bash
PYTHONPATH=compiler/python python3 -m tau examples/nn/linear/kernel.py -o out   # out/kernel.mlir and out/traced.json
compiler/build/bin/tauc out/kernel.mlir -o out                                  # one file per pass
lake exe tau-check out/source.json out/image.json                              # the whole compiler at once
lake exe tau-sim out/image.json examples/nn/linear/buffers.json                # run the image
```

### 3. From MLIR

```bash
compiler/build/bin/tauc examples/nn/linear/kernel.mlir -o out
lake exe tau-check out/source.json out/image.json
lake exe tau-sim out/image.json examples/nn/linear/buffers.json
```

`nn/linear`, `nn/residual` and `ops/elementwise` have the same program as
both `kernel.py` and `kernel.mlir`.

### 4. Pins and timelines

`paced` pins a loop to one iteration every cycle. `--timeline` prints
words and their cycles instead of buffers:

```bash
PYTHONPATH=compiler/python python3 -m tau examples/paced/kernel.py -o out
compiler/build/bin/tauc out/kernel.mlir -o out
lake exe tau-check out/source.json out/image.json                          # buffers and pins
lake exe tau-sim --timeline out/source.json examples/paced/buffers.json   # the pinned words
lake exe tau-sim --timeline out/image.json examples/paced/buffers.json    # every word the machine issues
```

### 5. One pass at a time

`tauc` writes one file per pass (Formats 5), and each can be checked against
the file before it and run on its own. A rejection names the pass that went
wrong:

```bash
lake exe tau-check out/placed.json out/scheduled.json   # tau-schedule
lake exe tau-sim out/placed.json examples/paced/buffers.json
```

`compiler/README.md` ("Nothing here is proved") lists the pair for every pass.

### 6. Every example

```bash
scripts/check-examples.sh   # every line should start with "ok"
```

The script compiles every example, checks every pass against its input,
runs every file, and confirms that a damaged copy of each file is rejected,
and for a program with pins a copy that is one cycle late. For an example
written in Python it also compares the frontend with the compiler and with
the Lean tools.

## What is in a folder

| File | What it is |
|---|---|
| `kernel.py` | the program in Python, bound to the name `kernel` (`compiler/python/tau/__init__.py`) |
| `kernel.mlir` | the program in the `tau` dialect; an example has this, `kernel.py`, or both, and both must give the same `source.json` |
| `buffers.json` | the contents of the buffers to run it on (Formats 6) |
| `machine` | optional: one line, the machine file to compile for, such as `machines/tau17.json`; without it `tauc` uses the thirteen-slice machine, `machines/tau13.json` |
| `stages/` | optional: a copy of every file `tauc` writes for the example, for readers without the compiler; `UPDATE_STAGES=1 scripts/check-examples.sh` refreshes it |

`linear-by-hand/` is different: a kernel file and a compiled file written by
hand, with no program for `tauc`. The script skips it. Check and run it
with

```bash
lake exe tau-check examples/linear-by-hand/kernel.json examples/linear-by-hand/compiled.json
lake exe tau-sim examples/linear-by-hand/compiled.json examples/linear-by-hand/buffers.json
```

## The examples

Programs with pins and calls are at the top, neural-network layers under
`nn/`, and single operations and memory hazards under `ops/`.

The pins of `paced`, `two-layer` and `pinned-end` are on the cycles of the
shortest schedule the compiler finds for the program, so they cost nothing.
`paced-axpy` and `pinned-chain` say what theirs cost.

| Example | Input | What it exercises |
|---|---|---|
| `paced` | Python | a loop pinned to one iteration every cycle, the fastest pace there is, which folds into three repeating entries |
| `paced-axpy` | Python | a loop of three operations paced by one pin: two cycles longer than the compiler's own schedule, and a quarter the entries |
| `two-layer` | Python | one kernel called twice, the second call from the first cycle on which its input is ready, with a scratch buffer between |
| `pinned-chain` | Python | three pins that agree, so the word goes directly, and three that do not, so it waits in memory |
| `pinned-end` | Python | one pin at the end of a chain, on the earliest cycle it can have; what comes before it is scheduled backward from it, so nothing waits |
| `linear-by-hand` | JSON | the linear layer scheduled by hand |
| `nn/linear` | Python & MLIR | one quantized linear layer: input and weights of 8 bits, product and bias of 32; a redundant `relu` for the simplifier |
| `nn/residual` | Python & MLIR | a residual block; one value used twice |
| `nn/affine-batch` | MLIR | two affine layers in a loop, each with its own matrix |
| `nn/batch-linear` | MLIR | a matrix multiplied four times; its rows are installed in the matrix slice once |
| `nn/two-matrices` | MLIR | two matrices that take turns as one matrix slice's installed words; the first product is requantized to feed the second |
| `nn/mlp` | MLIR | two linear layers in a row |
| `nn/mlp-wide` | MLIR | the same kernel on the 17-slice machine (`machines/tau17.json`) |
| `nn/gemv8` | MLIR | an 8 x 8 matrix times a vector; the matrix is dealt out over two memories and installed two rows a cycle |
| `nn/conv1d` | MLIR | a three-tap convolution along the lanes, using lane shifts |
| `nn/conv-taps` | Python | a Python loop over constant taps inside a `tau.loop` |
| `nn/maxpool` | MLIR | pooling over neighbouring lanes, using lane rotation |
| `ops/elementwise` | Python & MLIR | a loop of add, subtract and max over four values of 16 bits |
| `ops/axpy` | MLIR | scaled add, updating a buffer in place |
| `ops/axpy-slow-mul` | MLIR | the same kernel on a machine whose multiply takes three cycles (`machines/tau13-slow-mul.json`) |
| `ops/clip` | MLIR | clamping values of 32 bits between two bounds |
| `ops/leaky-relu` | MLIR | a constant word, a lane compare and a lane-wise select |
| `ops/bitops` | MLIR | absolute value, negation, constant add and multiply, shifts, and, or, xor, on values of 16 bits |
| `ops/lanes` | MLIR | reverse, broadcast and permute |
| `ops/shuffle` | MLIR | the rearrangement slice, and a value that waits in memory |
| `ops/east-side` | MLIR | buffers east of the vector slice; uses the east matrix and rearrangement slices |
| `ops/overwrite` | MLIR | a running sum in one word, and a load that must survive a store |
| `ops/unused` | MLIR | two operations whose words nothing uses: the simplifier removes the one without a pin and keeps the pinned one |
| `ops/neighbours` | MLIR | two words of one memory slice needed on one cycle; one goes round through a second memory slice |
