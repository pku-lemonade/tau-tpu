# The examples

Programs for the machine, each with the buffers to run it on. They are what
`scripts/check-examples.sh` compiles and checks; the comment at the top of
the script says what it checks on each.

## What is in a folder

| File | What it is |
|---|---|
| `kernel.py` | the program in Python, bound to the name `kernel` (`compiler/python/tau/__init__.py`) |
| `kernel.mlir` | the program in the `tau` dialect; an example has this, `kernel.py`, or both, and both must give the same `source.json` |
| `buffers.json` | the contents of the buffers to run it on (Formats 6) |
| `machine` | optional: one line, the machine file to compile for, such as `machines/tau17.json`; without it `tauc` uses the nine-slice machine |
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
`nn/`, and single operations and memory hazards under `ops/`. Three have a
`stages/` folder: `nn/linear`, `nn/residual` and `ops/elementwise`.

| Example | Input | What it exercises |
|---|---|---|
| `paced` | Python | a loop pinned to one iteration every four cycles, which folds into three repeating entries |
| `two-layer` | Python | one kernel called twice, the second call from a later cycle, with a scratch buffer between |
| `pinned-chain` | Python | three pins that agree and stay in one group, and three that do not, so a word waits in memory |
| `linear-by-hand` | JSON | the linear layer scheduled by hand |
| `nn/linear` | Python & MLIR | one quantized linear layer; a redundant `relu` for the simplifier |
| `nn/residual` | Python & MLIR | a residual block; one value used twice |
| `nn/affine` | MLIR | the linear layer with the bias added inside the matrix slice |
| `nn/affine-batch` | MLIR | two affine layers in a loop, each with its own matrix |
| `nn/batch-linear` | MLIR | a matrix multiplied four times; its columns are stored in the matrix slice once |
| `nn/mlp` | MLIR | two linear layers in a row |
| `nn/mlp-wide` | MLIR | the same kernel on the 17-slice machine (`machines/tau17.json`) |
| `nn/gemv8` | MLIR | an 8 x 8 matrix times a vector |
| `nn/conv1d` | MLIR | a three-tap convolution along the lanes, using lane shifts |
| `nn/conv-taps` | Python | a Python loop over constant taps inside a `tau.loop` |
| `nn/maxpool` | MLIR | pooling over neighbouring lanes, using lane rotation |
| `ops/elementwise` | Python & MLIR | a loop of add, subtract and max over four words |
| `ops/axpy` | MLIR | scaled add, updating a buffer in place |
| `ops/clip` | MLIR | clamping between two bounds |
| `ops/leaky-relu` | MLIR | a constant word, a lane compare and a lane-wise select |
| `ops/bitops` | MLIR | absolute value, negation, constant add and multiply, shifts, and, or, xor |
| `ops/lanes` | MLIR | reverse, broadcast and permute |
| `ops/shuffle` | MLIR | the rearrangement slice, and a value that waits in memory |
| `ops/east-side` | MLIR | buffers east of the vector slice; uses the east matrix and rearrangement slices |
| `ops/overwrite` | MLIR | a running sum in one word, and a load that must survive a store |
