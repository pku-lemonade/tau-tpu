# tau-tpu

## Background

tau-tpu is a small, statically scheduled machine for tensor programs, a
compiler for it, and the Lean 4 proofs that connect them. Its design follows
the published descriptions of tensor streaming processors (Abts et al., ISCA
2020 and ISCA 2022).

- **Machine & specification (Lean 4):** The specification *is* the simulator —
  the definitions the theorems are about are the code that runs.
- **Frontend (Python or MLIR):** A program is written in Python (a small
  frontend traces the operations it calls) or as MLIR text, and may pin an
  operation to a cycle.
- **Compiler (C++ on MLIR):** Turns a program into a timed program for the
  machine, and encodes it into an image (the numbers each slice is loaded
  with).
- **Checker (Lean 4):** Written and proved sound in Lean; decides for every
  compiled program whether it computes what its source computes and issues
  every pinned word on its cycle, end to end or one compiler pass at a time.

```
Machine (13 slices, 1 hop/cycle along east & west streams of byte lanes):
  ──east──▶ [0:mxm] [1:sxm] [2..5:mem] [6:vxm] [7..10:mem] [11:sxm] [12:mxm]
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
Lean's standard axioms (checked by `spec/tests/TauTest/Axioms.lean`):

- **The cell-level machine matches the slice-level machine.** Running a
  program on the machine built from blocks (shift registers, memories,
  systolic arrays, etc.) produces the same result as the slice-level
  machine, which treats each slice as one box.
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
  `examples/*/*/stages/` holds its output for three examples.
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
lake build
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

With Lean alone, check and run the compiler's output for one linear layer:

```bash
lake exe tau-check examples/nn/linear/stages/source.json examples/nn/linear/stages/image.json   # ACCEPT
lake exe tau-sim examples/nn/linear/stages/image.json examples/nn/linear/buffers.json           # the buffers at the end
```

[`examples/README.md`](examples/README.md) goes on from there: compiling from
Python or MLIR, pins and timelines, checking one pass at a time, and every
example with what it exercises.

## Layout

Each folder's README says what is in it and where to start.

| Folder | Contents |
|---|---|
| [`docs/`](docs/README.md) | What the machine, a program and a compiler are meant to be, in words and tables, and the JSON formats the tools exchange |
| [`spec/`](spec/README.md) | The Lean specification and its proofs, `tau-sim` and `tau-check`, and the tests of the specification; the map of the claims and how each stands |
| [`compiler/`](compiler/README.md) | The Python frontend and the C++/MLIR compiler (`tauc`, `tau-opt`): how they work and their limits |
| [`examples/`](examples/README.md) | Programs with their buffers, and how to try them |
| `machines/` | Machine descriptions for `tauc --machine` (Formats 3) |
| [`course/`](course/README.md) | The course: the book and the exercises |
| `scripts/` | `check-examples.sh` and `make-exercises.py`; the comment at the top of each says what it does |

## Limitations

tau-tpu is a teaching model and does not describe any product:

- No floating point, and no lane narrower than 32 bits (Machine 1).
- No address computed from data.
- No loop inside a loop, and no call inside a loop (Programs 3 and 4).
- No bit fields in the image: its numbers have no fixed width (Machine 3.10).

Compiler-specific limits are listed in
[`compiler/README.md`](compiler/README.md#limits).
