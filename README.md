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

## Setup

All commands are typed in a terminal, from the repository folder. CI runs
the same steps on Debian 12 (`.github/workflows/ci.yml`); Ubuntu should
behave the same. On Windows, install
[WSL 2](https://learn.microsoft.com/windows/wsl/install) with Ubuntu and do
everything inside it. On macOS, steps 1 to 4 should work as written (not yet tried); for step 5 see
the note there.

**1. Get the code.** On Debian or Ubuntu, first
`sudo apt install git curl`.

```bash
git clone https://github.com/pku-lemonade/tau-tpu.git
cd tau-tpu
```

**2. Install Lean.** You do not install Lean itself. You install
[elan](https://github.com/leanprover/elan), which manages Lean versions the
way `rustup` manages Rust's. Lean comes with Lake, its build tool, which
plays the part of `make` or `cargo`. The file `lean-toolchain` names the
Lean version this project uses, and elan downloads that version the first
time you run `lake` in this folder.

```bash
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
source ~/.elan/env        # or open a new terminal
lake --version            # downloads Lean the first time, then prints its version
```

**3. Build the Lean side.** This builds the library, every proof, the tests
and the two tools. The first time takes a few minutes. It should end with
`Build completed successfully`.

```bash
lake build Tau TauTest tau-sim tau-check
```

**4. Set up the editor.** Lean is written in an editor that shows the proof
state as you type. Use [VS Code](https://code.visualstudio.com/) with the
Lean 4 extension:

```bash
code --install-extension leanprover.lean4
code .                    # open the repository folder itself
```

Always open the repository folder, the one with `lakefile.toml` in it. With
a subfolder or a single file open, `import Tau` is not found. If VS Code was
already running when you installed elan, quit it and start it again, so that
it can find `lake`. If the `code` command is not found: on macOS, run
"Shell Command: Install 'code' command in PATH" from VS Code's command
palette; under WSL, install VS Code on Windows with its WSL extension.

**5. Build the compiler (optional).** The compiler needs LLVM and MLIR 21.
Everything in Lean works without it, and `examples/*/stages/` holds what it
writes for three examples. On Debian or Ubuntu, this installs LLVM through
its [official installer](https://apt.llvm.org/) and builds the compiler:

```bash
sudo apt install cmake ninja-build g++ wget lsb-release gnupg software-properties-common
wget https://apt.llvm.org/llvm.sh && sudo bash llvm.sh 21 && rm llvm.sh
sudo apt install llvm-21-dev libmlir-21-dev mlir-21-tools
cmake -S compiler -B compiler/build -G Ninja -DMLIR_DIR=/usr/lib/llvm-21/lib/cmake/mlir
cmake --build compiler/build
```

On macOS, or where those packages are not available, use the container in
[`docker/`](docker/Dockerfile), which installs the same packages. It has not
been tested yet.

**6. Check the setup.** If the compiler is built, this compiles every
example and checks every stage. Each line should start with `ok`.

```bash
scripts/check-examples.sh
```

Without the compiler, `lake build Tau TauTest` succeeding is the check.

## Try it

```bash
compiler/build/bin/tauc examples/linear/kernel.mlir -o out
lake exe tau-check out/kernel.json out/compiled.json
lake exe tau-sim out/compiled.json examples/linear/buffers.json
```

Without the compiler, use `examples/linear/stages` in place of `out`.
`lake exe` builds a tool if needed and then runs it; the built tools are
also in `.lake/build/bin/`.

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
lake exe tau-check out/kernel.json out/placed.json
lake exe tau-sim out/placed.json examples/linear/buffers.json
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
| `docker/`, `.devcontainer/` | A container with everything installed |
| `.vscode/` | Recommended editor extension and settings |

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
