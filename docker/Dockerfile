# A container with everything needed to build tau-tpu: Lean (through elan),
# and LLVM/MLIR 21 for the compiler.
#
#   docker build -f docker/Dockerfile -t tau-tpu .
#   docker run --rm -it -v "$PWD:/work" -w /work tau-tpu bash
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git gnupg python3 cmake ninja-build g++ \
    && curl -fsSL https://apt.llvm.org/llvm-snapshot.gpg.key \
       | gpg --dearmor -o /usr/share/keyrings/llvm.gpg \
    && echo "deb [signed-by=/usr/share/keyrings/llvm.gpg] http://apt.llvm.org/bookworm/ llvm-toolchain-bookworm-21 main" \
       > /etc/apt/sources.list.d/llvm.list \
    && apt-get update && apt-get install -y --no-install-recommends \
      llvm-21-dev libmlir-21-dev mlir-21-tools \
    && rm -rf /var/lib/apt/lists/*

RUN curl -sSf https://elan.lean-lang.org/elan-init.sh \
    | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"
