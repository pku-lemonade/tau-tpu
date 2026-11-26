# tau-tpu

tau-tpu is a small, statically scheduled machine for tensor programs, a
compiler for it, and the proofs that connect them.

- The machine is specified in Lean 4. The specification is also the
  simulator: the definitions the theorems are about are the code that runs.
- A program is written in Python, with a small frontend that records the
  operations it calls, or as MLIR text. It may pin an operation to a cycle.
- The compiler is written in C++ on MLIR. It turns the program into a timed
  program for the machine, and that into an image: the numbers each slice
  is loaded with.
- A checker, written and proved correct in Lean, decides for every compiled
  program whether it computes what its source computes and issues every
  pinned word on its cycle. It can check the output of each compiler pass
  separately.

```
Machine (9 slices, 1 hop/cycle along east & west streams):
  ──east──▶ [0:mxm] [1:sxm] [2:mem] [3:mem] [4:vxm] [5:mem] [6:mem] [7:sxm] [8:mxm]
  ◀─west──

Flow:
  kernel.py ─frontend→ kernel.mlir ─tauc→ source → ... → compiled → image
                                            │                        │
                                            └─────── tau-check ──────┘ (proved sound)
                                                       compiled = cell-level (cellExecute_eq)
```

**Taking the course?** Start in [`course/`](course/README.md). The rest of
this file describes the project the course is about.

## What is proved

`Tau/Proofs/EndToEnd.lean` states the main result (`end_to_end`). If the
checker accepts a compiled program for a source program, then for every
contents of the buffers the cell-level machine runs the program without a
trap and leaves in memory exactly the buffers the source program computes;
and the slice-level machine issues every word the source pins to a cycle on
that cycle.

The theorem rests on Lean's three standard axioms and nothing else;
`tests/TauTest/Axioms.lean` fails the build if that changes. The compiler
and the frontend are not proved: a bug in a compiler pass gives a program
the checker rejects, not a wrong answer. Trust begins at `source.json` (for
Python programs, tested against the frontend's `traced.json`), the JSON
readers (`Tau/Sim/Json.lean`), and the Lean definitions against `Tau/Docs/`.
Section 4 of [`Tau/Docs/README.md`](Tau/Docs/README.md) lists every claim
and how it stands, including what is only tested and what is trusted.

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
`examples/*/stages/` holds its output for three examples. The frontend needs
Python 3 and nothing else.

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

A program written as MLIR text:

```bash
compiler/build/bin/tauc examples/linear/kernel.mlir -o out
lake exe tau-check out/source.json out/image.json
lake exe tau-sim out/image.json examples/linear/buffers.json
```

Without the compiler, use `examples/linear/stages` in place of `out`.

A program written in Python, with a loop pinned to one iteration every four
cycles:

```bash
PYTHONPATH=frontend python3 -m tau examples/paced/kernel.py -o out    # writes out/kernel.mlir
compiler/build/bin/tauc out/kernel.mlir -o out
lake exe tau-check out/source.json out/image.json
lake exe tau-sim --timeline out/source.json examples/paced/buffers.json   # the pinned words
lake exe tau-sim --timeline out/image.json examples/paced/buffers.json    # every word the machine issues
```

`tauc` writes one JSON file per pass (listed in section 5 of
[`Tau/Docs/README.md`](Tau/Docs/README.md)), and each stage can be checked
and run on its own; a rejection names the pass that went wrong:

```bash
lake exe tau-check out/placed.json out/scheduled.json   # check tau-schedule
lake exe tau-sim out/placed.json examples/paced/buffers.json
```

`scripts/check-examples.sh` compiles every example, checks every pass against
its input, runs every file, and confirms that a damaged copy of each file is
rejected, and for a program with pins a copy that is one cycle late. For the
examples written in Python it also compares the frontend with the compiler
and with the Lean tools.

## Where to read

| For | Read |
|---|---|
| the specification, and the map from its docs to its Lean | [`Tau/Docs/README.md`](Tau/Docs/README.md), sections 1 to 3 |
| the machine, in words | [`Tau/Docs/Machine.md`](Tau/Docs/Machine.md) |
| what a program is and what it promises | [`Tau/Docs/Programs.md`](Tau/Docs/Programs.md) |
| what a compiler has to deliver | [`Tau/Docs/Compiler.md`](Tau/Docs/Compiler.md) |
| what is proved, checked, tested or trusted | [`Tau/Docs/README.md`](Tau/Docs/README.md), section 4 |
| the files the tools exchange | [`Tau/Docs/README.md`](Tau/Docs/README.md), section 5 |
| how this compiler works, and its limits | [`compiler/README.md`](compiler/README.md) |
| the course | [`course/README.md`](course/README.md) |

## Layout

| Folder | Contents |
|---|---|
| `Tau/` | Lean specification, proofs, and `Tau/Docs/` |
| `frontend/` | The Python frontend: `python3 -m tau` |
| `compiler/` | The C++ compiler: `tauc` and `tau-opt` |
| `tools/` | Entry points of `tau-sim` and `tau-check` |
| `tests/` | Lean tests, run at build time |
| `examples/` | Programs with input buffers, as MLIR or as Python |
| `chips/` | Machine descriptions: 9 slices and 17 slices |
| `course/` | The course: a book and exercise files |
| `scripts/` | The examples script and the exercise generator |
| `docker/`, `.devcontainer/` | A container with everything installed |
| `.vscode/` | Recommended editor extension and settings |

## Examples

| Example | What it exercises |
|---|---|
| `linear` | one quantized linear layer; a redundant `relu` for the simplifier |
| `affine` | the same layer with the bias added inside the matrix slice |
| `affine-batch` | two affine layers in a loop, each with its own matrix |
| `mlp` | two linear layers in a row |
| `mlp-wide` | the same kernel on the 17-slice machine |
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
| `paced` | written in Python; a loop pinned to one iteration every four cycles, which folds into three repeating entries |
| `two-layer` | written in Python; one kernel called twice, the second call from a later cycle, with a scratch buffer between |
| `conv-taps` | written in Python; a Python loop over constant taps inside a `tau.loop` |
| `pinned-chain` | written in Python; three pins that agree and stay in one group, and three that do not, so a word waits in memory |

## Background

The design follows the published descriptions of tensor streaming processors
(Abts et al., ISCA 2020 and ISCA 2022). It is a teaching model and does not
describe any product. There is no floating point, no lane narrower than 32
bits, no delay that differs between the operations of one slice, no address
computed from data, and no import from a framework such as PyTorch or ONNX.
