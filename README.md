# tau-tpu

tau-tpu is a small statically scheduled tensor processor, its compiler, and
the proofs that connect them.

- The processor is specified in Lean 4. The specification is also the
  simulator: the definitions the theorems are about are the code that runs.
- The compiler is written in C++ on MLIR. It turns a kernel into a timed
  program for the processor.
- A checker, written and proved correct in Lean, decides for every compiled
  program whether it computes what the kernel computes. It can check the
  output of each compiler pass separately.

**Taking the course?** Start in [`course/`](course/README.md). The rest of
this file describes the project the course is about.

## What is proved

`Tau/Proofs/EndToEnd.lean` states the main result. If the checker accepts a
compiled program for a kernel, then for every choice of buffer contents the
cell-level machine runs the program without a trap and leaves in memory
exactly the buffers the kernel computes.

The theorem rests on Lean's three standard axioms and nothing else;
`tests/TauTest/Axioms.lean` fails the build if that changes.

What is not proved:

- The C++ compiler. A wrong compiler produces programs the checker rejects.
- The JSON readers that the tools use.
- Anything about hardware. The machine is a Lean model.

## Build

Lean, with [elan](https://github.com/leanprover/elan) installed:

```bash
lake build                  # the library and every proof
lake build TauTest          # the tests
lake build tau-sim tau-check
```

The compiler, with LLVM and MLIR 21 development packages installed:

```bash
cmake -S compiler -B compiler/build -G Ninja \
  -DMLIR_DIR=/usr/lib/llvm-21/lib/cmake/mlir
cmake --build compiler/build
```

Or use the container in [`docker/`](docker/Dockerfile), which has both. VS
Code can open the repository inside it through `.devcontainer/`. Neither has
been tested yet.

Without the compiler you can still build and use everything in Lean:
`examples/linear/stages/` holds a copy of what `tauc` writes for one example,
and `examples/linear-by-hand/` is a program written by hand.

## Try it

```bash
compiler/build/bin/tauc examples/linear/kernel.mlir -o out
.lake/build/bin/tau-check out/kernel.json out/compiled.json
.lake/build/bin/tau-sim out/compiled.json examples/linear/buffers.json
```

`tauc` writes one file per pass, and each can be checked and run on its own:

| File | Written after | What it is |
|---|---|---|
| `kernel.json` | parsing | the kernel as written |
| `simplified.json` | `tau-simplify` | a kernel |
| `unrolled.json` | `tau-unroll` | a kernel with no loops |
| `placed.json` | `tau-place` | instructions in order, with slices and addresses |
| `scheduled.json` | `tau-schedule` | timed instructions, one stream per word |
| `compiled.json` | `tau-route` | the finished program |

```bash
.lake/build/bin/tau-check out/kernel.json out/placed.json
.lake/build/bin/tau-sim out/placed.json examples/linear/buffers.json
```

The first stage that `tau-check` rejects names the pass that went wrong.

`scripts/check-examples.sh` compiles every example, checks and runs all five
stages, and confirms that a damaged copy of each stage is rejected.

## Examples

| Example | What it exercises |
|---|---|
| `linear` | one quantized linear layer; a redundant `relu` for the simplifier |
| `affine` | the same layer with the bias added inside the matrix slice |
| `mlp` | two linear layers in a row |
| `mlp-wide` | the same kernel on the 17-slice chip |
| `batch-linear` | a matrix multiplied four times; its columns are stored in the matrix slice once |
| `residual` | a residual block; one value used twice |
| `gemv8` | an 8 x 8 matrix times a vector |
| `east-side` | buffers east of the vector slice; uses the east matrix and rearrangement slices |
| `elementwise` | a loop of add, subtract and max over four words |
| `clip` | clamping between two bounds |
| `leaky-relu` | a constant word, a lane compare and a lane-wise select |
| `bitops` | absolute value, negation, constant add and multiply, shifts, and, or, xor |
| `axpy` | scaled add, updating a buffer in place |
| `conv1d` | a three-tap convolution along the lanes, using lane shifts |
| `maxpool` | pooling over neighbouring lanes, using lane rotation |
| `lanes` | reverse, broadcast and permute |
| `shuffle` | the rearrangement slice, and a value that waits in memory |
| `overwrite` | a running sum in one word, and a load that must survive a store |
| `linear-by-hand` | the linear layer scheduled by hand, as JSON only |

## What the machine has

| | |
|---|---|
| Vector slice | add, subtract, multiply, max, min, and, or, xor, compare; relu, requantize, negate, absolute value, shift bits left, add or multiply by a constant; a constant word; lane-wise select |
| Rearrangement slice | shift lanes, rotate, reverse, broadcast one lane, permute by a table |
| Matrix slice | load a vector, multiply-accumulate with a streamed or a stored column, seed the accumulator, store columns, emit |
| Memory slice | read and write |
| Every slice | instructions that repeat at a fixed spacing with a stepping address or column |

What it does not have: floating point, lanes narrower than 32 bits, delays
that differ between the operations of one slice, and addresses computed from
data.

## Layout

Lean folders are listed in dependency order.

| Folder | Contents |
|---|---|
| `Tau/Data/` | Lanes and words: 32-bit values and the operations on them |
| `Tau/Blocks/` | Clocked components: shift register, accumulator, multiply-accumulate, pipeline, memory, sequencer, repeater, systolic array |
| `Tau/Isa/` | Slice kinds, operations, instructions, programs, chip configuration |
| `Tau/SliceLevel/` | The machine with each slice as one box with a delay |
| `Tau/CellLevel/` | The machine with each slice opened into its blocks |
| `Tau/IR/` | Kernels (the Lean model of the compiler's dialect) and symbolic expressions |
| `Tau/Passes/` | Lean models of the compiler's `simplify` and `unroll` passes |
| `Tau/Check/` | The checker for finished programs, and the checks for each pass |
| `Tau/Sim/` | JSON readers and the functions behind the command-line tools |
| `Tau/Proofs/` | Theorems about everything above, in a mirrored folder structure |
| `tools/` | Entry points of `tau-sim` and `tau-check` |
| `tests/` | Lean tests, run at build time |
| `compiler/` | The C++ compiler: `tauc` and `tau-opt` |
| `examples/` | Kernels with input buffers |
| `chips/` | Chip descriptions: 9 slices and 17 slices |
| `course/` | The course: a book and exercise files |
| `docs/` | File formats |

Definitions and theorems are kept apart. A file outside `Tau/Proofs/` says
what something is. The file of the same name under `Tau/Proofs/` says what is
true of it.

## The machine in one paragraph

A chip is a row of slices of four kinds: memory, vector, rearrangement and
matrix. Streams run between them, carrying words east or west, one slice per
cycle. A program lists every instruction with its slice and its cycle; an
entry may repeat at a fixed spacing. There are no branches, no queues and no
waiting. A result computed at slice `p` on
cycle `t` can be read at slice `q` on cycle `t + delay + 1 + |q - p|`, and on
no other cycle. The compiler's job is to make every operand arrive on time.

The design follows the published descriptions of tensor streaming processors
(Abts et al., ISCA 2020 and ISCA 2022). It is a teaching model and does not
describe any product.
