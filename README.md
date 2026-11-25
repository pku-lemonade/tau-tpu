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

Every part of the project stands in one of four ways. *Proved* means a Lean
theorem, for every input and every size. *Checked* means `tau-check` decides
it for each compiled program. *Tested* means it holds on the examples.
*Trusted* means nothing checks it.

| Claim | Standing | Where |
|---|---|---|
| Each block gives the stated output at cycle `t` | proved | `Tau/Proofs/Blocks/` |
| The cell-level machine equals the slice-level machine | proved | `cellExecute_eq` |
| A finished program that `check` accepts computes its kernel, without a trap | proved | `check_sound`, `end_to_end` |
| The output of a pass that the pass's check accepts computes what the input computes | proved | `checkKernels_sound`, `checkPlaced_sound`, `checkScheduled_sound`, `checkRouted_sound` |
| If all five per-pass checks accept, the finished program computes its kernel | proved | `passes_sound`, `end_to_end_passes` |
| `Kernel.unroll`, the Lean copy of `tau-unroll`, keeps what a kernel computes; the simplifier inside the checks keeps the value of an expression | proved | `Kernel.run_unroll`, `Expr.denote_simp` |
| The output of each C++ pass computes what its input computes | checked | `tau-check`, once per pass |
| The compiler's output is accepted | tested, on 19 kernels | `scripts/check-examples.sh` |
| The tables of the course's architecture manual hold of the specification | tested | `tests/TauTest/Manual.lean` |
| The C++ `tau-unroll` gives the kernel that its Lean copy gives | tested, on 19 kernels | `tau-check --unroll` |
| The other four passes have a Lean copy, or a rule for how the output is built from the input | no; a check asks only whether the output computes the same thing | |
| The timing rule: a result is on its stream at slice `q` on cycle `t + delay + 1 + \|q - p\|` | proved, when nothing else is put on that stream in its path | `arrives_east`, `arrives_west` |
| The result is there on no other cycle | not stated | |
| `kernel.json` says what `kernel.mlir` says | trusted | MLIR's parser, `compiler/lib/Target/EmitKernel.cpp` |
| The JSON files are read correctly | trusted | `Tau/Sim/Json.lean` |
| The definitions in the theorems mean what is intended | trusted; read them | `Kernel.run`, `cellExecute`, `Tau/Data/Word.lean` |
| Lean checks proofs and compiles `tau-check` correctly | trusted | |
| Anything about hardware | no; the machine is a Lean model | |

A bug in a C++ pass gives a program the checker rejects, not a wrong answer.
The exception is the step that writes `kernel.json`: the chain of checks
starts from that file, so a kernel misread there is checked faithfully
against the wrong kernel.

[`docs/overview.md`](docs/overview.md) says in words what each part is and
names the definition and the theorem for it.

## Setup

On Linux (on Windows, inside WSL):

```bash
git clone https://github.com/pku-lemonade/tau-tpu.git && cd tau-tpu

# Lean. elan installs the Lean version named in lean-toolchain;
# lake, which comes with it, is the build tool.
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
source ~/.elan/env
lake build Tau TauTest tau-sim tau-check    # a few minutes the first time

# Editor
code --install-extension leanprover.lean4
code .
```

Open the repository folder in VS Code, not a subfolder, or `import Tau` is
not found.

The compiler is optional and needs LLVM and MLIR 21. Without it,
`examples/*/stages/` holds its output for three examples.

```bash
sudo apt install cmake ninja-build g++ wget lsb-release gnupg software-properties-common
wget https://apt.llvm.org/llvm.sh && sudo bash llvm.sh 21 && rm llvm.sh
sudo apt install llvm-21-dev libmlir-21-dev mlir-21-tools
cmake -S compiler -B compiler/build -G Ninja -DMLIR_DIR=/usr/lib/llvm-21/lib/cmake/mlir
cmake --build compiler/build
scripts/check-examples.sh                   # every line should start with "ok"
```

Or use the container in [`docker/`](docker/Dockerfile), which has
everything.

## Try it

```bash
compiler/build/bin/tauc examples/linear/kernel.mlir -o out
lake exe tau-check out/kernel.json out/compiled.json
lake exe tau-sim out/compiled.json examples/linear/buffers.json
```

Without the compiler, use `examples/linear/stages` in place of `out`.

`tauc` writes one file per pass, and each can be checked and run on its own:

| File | Written after | What it is |
|---|---|---|
| `kernel.json` | parsing | the kernel as written |
| `simplified.json` | `tau-simplify` | a kernel |
| `unrolled.json` | `tau-unroll` | a kernel with no loops |
| `placed.json` | `tau-place` | instructions in order, with slices and addresses |
| `scheduled.json` | `tau-schedule` | timed instructions, one stream per word |
| `compiled.json` | `tau-route` | the finished program |

`tau-check` takes the input of a pass and its output, and decides whether
they compute the same thing:

```bash
lake exe tau-check out/kernel.json out/simplified.json      # tau-simplify
lake exe tau-check out/simplified.json out/unrolled.json    # tau-unroll
lake exe tau-check out/unrolled.json out/placed.json        # tau-place
lake exe tau-check out/placed.json out/scheduled.json       # tau-schedule
lake exe tau-check out/scheduled.json out/compiled.json     # tau-route
lake exe tau-sim out/placed.json examples/linear/buffers.json
```

A rejection names the pass that went wrong.

`scripts/check-examples.sh` compiles every example, checks every pass against
its input, runs every file, and confirms that a damaged copy of each file is
rejected.

## Examples

| Example | What it exercises |
|---|---|
| `linear` | one quantized linear layer; a redundant `relu` for the simplifier |
| `affine` | the same layer with the bias added inside the matrix slice |
| `affine-batch` | two affine layers in a loop, each with its own matrix |
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
| `Tau/IR/` | The three forms a program takes in the compiler (kernel, placed, compiled), the memory map, and symbolic expressions |
| `Tau/Passes/` | A Lean copy of the `unroll` pass |
| `Tau/Check/` | The check of the whole compiler, the checks for each pass, and the simplifier they use |
| `Tau/Sim/` | JSON readers and the functions behind the command-line tools |
| `Tau/Claims.lean` | Every main statement, as a named proposition |
| `Tau/Proofs/` | Theorems about everything above, in a mirrored folder structure |
| `tools/` | Entry points of `tau-sim` and `tau-check` |
| `tests/` | Lean tests, run at build time |
| `compiler/` | The C++ compiler: `tauc` and `tau-opt` |
| `examples/` | Kernels with input buffers |
| `chips/` | Chip descriptions: 9 slices and 17 slices |
| `course/` | The course: a book, an architecture manual to specify from, and exercise files |
| `docs/` | What each part is and where it is defined; file formats |
| `docker/`, `.devcontainer/` | A container with everything installed |
| `.vscode/` | Recommended editor extension and settings |

Definitions and theorems are kept apart. A file outside `Tau/Proofs/` says
what something is. The file of the same name under `Tau/Proofs/` says what is
true of it. `Tau/Claims.lean` collects the main statements, so that what is
claimed can be read without opening a proof.

## The machine in one paragraph

A chip is a row of slices of four kinds: memory, vector, rearrangement and
matrix. Streams run between them, carrying words east or west, one slice per
cycle. A program lists every instruction with its slice and its cycle; an
entry may repeat at a fixed spacing. There are no branches, no queues and no
waiting. A result computed at slice `p` on
cycle `t` can be read at slice `q` on cycle `t + delay + 1 + |q - p|`, and on
no other cycle. The compiler's job is to make every operand arrive on time.
The first half of that rule is a theorem, in
`Tau/Proofs/SliceLevel/Timing.lean`.

The design follows the published descriptions of tensor streaming processors
(Abts et al., ISCA 2020 and ISCA 2022). It is a teaching model and does not
describe any product.

## The compiler in one paragraph

The input is a kernel: one MLIR function in the `tau` dialect, written by
hand as text. Its operations are loads and stores on buffers of words,
arithmetic on words, rearrangement of lanes, matrix times vector, and a loop
with a fixed count that does not nest. There is no front-end language and no
import from a framework such as PyTorch or ONNX; nothing lowers into the
dialect from another one. Five passes take the kernel to a program.
`tau-simplify` and `tau-unroll` rewrite the kernel, `tau-place` gives each
operation a slice and each buffer an address, `tau-schedule` gives each
instruction a cycle, and `tau-route` gives each result a stream. The passes
are C++ and none is proved. Each one's output is written as a JSON file, and
`tau-check` decides whether it computes what the pass's input computes. The
passes and their limits are in [`compiler/README.md`](compiler/README.md).
