# tau-tpu

## Background

tau-tpu is a small, statically scheduled machine for tensor programs, a
compiler for it, and the Lean 4 proofs that connect them. Its design follows
the published descriptions of tensor streaming processors (Abts et al., ISCA
2020 and ISCA 2022).

- **Machine & specification (Lean 4):** The specification *is* the simulator —
  the definitions the theorems are about are the code that runs.
- **Frontend (Python or MLIR):** A program is written in Python (a small
  frontend records the operations it calls) or as MLIR text, and may pin an
  operation to a cycle.
- **Compiler (C++ on MLIR):** Turns a program into a timed program for the
  machine, and encodes it into an image (the numbers each slice is loaded
  with).
- **Checker (Lean 4):** Written and proved sound in Lean; decides for every
  compiled program whether it computes what its source computes and issues
  every pinned word on its cycle, end to end or one compiler pass at a time.

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

Two main results hold for every input and every machine size, using only
Lean's standard axioms (checked by `tests/TauTest/Axioms.lean`):

- **The machine matches its component build.** Running a program on the
  machine built from hardware blocks (shift registers, memories, systolic
  arrays, etc.) produces the same result as the high-level slice
  specification.
- **The checker is sound (translation validation).** The C++ compiler and
  Python frontend are *not* proved correct. Instead, `tau-check` validates
  each compiled program (or each compiler pass) against its source. A
  compiler bug produces a program the checker rejects rather than a wrong
  answer; if the checker accepts, the compiled program is proved to run
  without error, compute the exact source results, and meet every cycle pin.

For every theorem statement, what is proved vs. checked vs. tested, and where
trust begins, see [`spec/Tau/Claims.lean`](spec/Tau/Claims.lean) and
[`spec/README.md`](spec/README.md#status).

## Setup

- **Required:** Lean 4 (via `elan`) — enough for all specifications, proofs,
  the simulator, the checker, and the course.
- **Optional:** Python 3 for the frontend (no extra packages), and LLVM/MLIR
  21 for the C++ compiler (`tauc`). Without the compiler,
  `examples/*/stages/` holds its output for three examples.
- **All-in-one alternative:** Use the Docker container or VS Code Dev
  Container below.

### 1. Lean and editor (required)

Works on Linux, macOS, and Windows (inside WSL):

```bash
git clone https://github.com/pku-lemonade/tau-tpu.git && cd tau-tpu

# Install Lean via elan (uses the version in lean-toolchain; lake is the build tool)
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
source ~/.elan/env

# Build the library, proofs, tests, simulator, and checker (a few minutes the first time)
lake build Tau TauTest tau-sim tau-check
```

For VS Code:

```bash
code --install-extension leanprover.lean4
code .
```

Open the repository root in VS Code, not a subfolder, or `import Tau` will
not be found.

### 2. C++ compiler (optional)

Needs LLVM and MLIR 21 (plus Python 3 for `scripts/check-examples.sh`).

**Linux (Debian / Ubuntu, or WSL):**

```bash
sudo apt install cmake ninja-build g++ wget lsb-release gnupg software-properties-common
wget https://apt.llvm.org/llvm.sh && sudo bash llvm.sh 21 && rm llvm.sh
sudo apt install llvm-21-dev libmlir-21-dev mlir-21-tools

cmake -S compiler -B compiler/build -G Ninja -DMLIR_DIR=/usr/lib/llvm-21/lib/cmake/mlir
cmake --build compiler/build
scripts/check-examples.sh                   # every line should start with "ok"
```

**macOS (Homebrew):**

```bash
brew install llvm@21 cmake ninja

cmake -S compiler -B compiler/build -G Ninja -DMLIR_DIR=$(brew --prefix llvm@21)/lib/cmake/mlir
cmake --build compiler/build
scripts/check-examples.sh                   # every line should start with "ok"
```

### 3. Alternative: Docker / Dev Container

[`docker/Dockerfile`](docker/Dockerfile) comes with Lean, Python 3, and
LLVM/MLIR 21 pre-installed.

- **VS Code Dev Containers:** Open the repository in VS Code and run
  **Dev Containers: Reopen in Container** (configured in
  [`.devcontainer/devcontainer.json`](.devcontainer/devcontainer.json)).
- **Docker CLI:**

  ```bash
  docker build -f docker/Dockerfile -t tau-tpu .
  docker run --rm -it -v "$PWD:/work" -w /work tau-tpu bash
  ```

## Try it

Programs can start from **Python** (`kernel.py`) or **MLIR** (`kernel.mlir`).
`examples/nn/linear`, `examples/ops/elementwise`, and `examples/nn/residual`
include both side by side.

Starting from Python:

```bash
PYTHONPATH=compiler/python python3 -m tau examples/nn/linear/kernel.py -o out   # writes out/kernel.mlir and out/traced.json
compiler/build/bin/tauc out/kernel.mlir -o out
lake exe tau-check out/source.json out/image.json
lake exe tau-sim out/image.json examples/nn/linear/buffers.json
```

Starting from MLIR:

```bash
compiler/build/bin/tauc examples/nn/linear/kernel.mlir -o out
lake exe tau-check out/source.json out/image.json
lake exe tau-sim out/image.json examples/nn/linear/buffers.json
```

Without the C++ compiler, run the Python program directly with
`PYTHONPATH=compiler/python python3 -m tau examples/nn/linear/kernel.py --run examples/nn/linear/buffers.json`,
and pass `examples/nn/linear/stages` in place of `out` to `tau-check` and `tau-sim`.

A Python program with cycle pins (a loop pinned to one iteration every four
cycles):

```bash
PYTHONPATH=compiler/python python3 -m tau examples/paced/kernel.py -o out    # writes out/kernel.mlir
compiler/build/bin/tauc out/kernel.mlir -o out
lake exe tau-check out/source.json out/image.json
lake exe tau-sim --timeline out/source.json examples/paced/buffers.json   # the pinned words
lake exe tau-sim --timeline out/image.json examples/paced/buffers.json    # every word the machine issues
```

`tauc` writes one JSON file per pass (listed in
[`docs/Formats.md`](docs/Formats.md)), and each stage can be checked
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
| the shared docs index and doc-to-Lean rules | [`docs/README.md`](docs/README.md) |
| the machine, in words | [`docs/Machine.md`](docs/Machine.md) |
| what a program is and what it promises | [`docs/Programs.md`](docs/Programs.md) |
| what a compiler has to deliver | [`docs/Compiler.md`](docs/Compiler.md) |
| the JSON formats the tools exchange | [`docs/Formats.md`](docs/Formats.md) |
| the Lean map, reading order, and proof status | [`spec/README.md`](spec/README.md) |
| how this compiler works, and its limits | [`compiler/README.md`](compiler/README.md) |
| how the Python frontend records a program | [`compiler/python/tau/__init__.py`](compiler/python/tau/__init__.py) (opening docstring) |
| the course | [`course/README.md`](course/README.md) |

## Layout

| Folder | Contents |
|---|---|
| `docs/` | Shared prose contracts (`Machine.md`, `Programs.md`, `Compiler.md`, `Formats.md`) |
| `machines/` | Shared machine descriptions (`tau9.json`, `tau17.json`) |
| `spec/` | Lean specification (`Tau/`), proofs (`Tau/Proofs/`), `tau-sim`/`tau-check` (`tools/`), and tests (`tests/`) |
| `compiler/` | Python tracing frontend (`python/tau/`) and C++/MLIR compiler (`tauc`, `tau-opt`) |
| `examples/` | Timed examples at root; `nn/` neural layers; `ops/` operator and memory-hazard kernels |
| `course/` | Self-paced specification course: `book/`, `Specify/`, `Prove/`, and `Work/` |
| `scripts/` | Example verification (`check-examples.sh`) and exercise generator (`make-exercises.py`) |
| `docker/`, `.devcontainer/` | Container with Lean, Python 3, and LLVM/MLIR 21 |
| `.vscode/` | Recommended editor extension and settings |

## Examples

Timed / pinned programs sit directly in `examples/`, neural layers under `examples/nn/`,
and single-op / memory-hazard tests under `examples/ops/`:

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

## Limitations

tau-tpu is a teaching model and does not describe any product:

- No floating point, and no lane narrower than 32 bits.
- No delay that differs between the operations of one slice.
- No address computed from data.
- No import from a framework such as PyTorch or ONNX.

Compiler-specific limits are listed in
[`compiler/README.md`](compiler/README.md#limits).
