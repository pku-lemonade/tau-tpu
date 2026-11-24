# A container with everything needed to build tau-tpu: Lean (through elan),
# and LLVM/MLIR 21 for the compiler. It runs the install steps of README.md
# ("Setup"), without `sudo`. CI builds it and runs every check inside it.
#
#   docker build -f docker/Dockerfile -t tau-tpu .
#   docker run --rm -it -v "$PWD:/work" -w /work tau-tpu bash
FROM debian:bookworm-slim

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
    && apt-get install -y git curl ca-certificates python3 \
       cmake ninja-build g++ wget lsb-release gnupg software-properties-common \
    && wget https://apt.llvm.org/llvm.sh && bash llvm.sh 21 && rm llvm.sh \
    && apt-get install -y llvm-21-dev libmlir-21-dev mlir-21-tools \
    && rm -rf /var/lib/apt/lists/*

RUN curl -sSf https://elan.lean-lang.org/elan-init.sh \
    | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"
