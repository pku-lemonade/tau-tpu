import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Reading list" =>
The course does not teach the following subjects. These are places to learn
the terms each chapter lists.

# Lean

* [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4).
  A first hour of proving, in the browser.
* [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/).
  Lean as a programming language. Chapters 1 to 4 cover what this course uses.
* [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/).
  The logic and the tactics, in depth.
* [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/). A gentle
  introduction to writing proofs, in Lean.
* [The Lean Language Reference](https://lean-lang.org/doc/reference/latest/).
  Look things up here, including `omega`, `simp` and `bv_decide`.

# Digital hardware

* [Nand to Tetris](https://www.nand2tetris.org/). Builds a computer from
  gates. The first three projects cover registers, memory and the clock.
* Harris and Harris, _Digital Design and Computer Architecture_. A standard
  textbook. Look up: flip-flop, register, shift register, pipelining, memory
  array.
* H. T. Kung, "Why Systolic Architectures?", IEEE Computer, 1982. The
  original argument for systolic arrays. Short and readable.

# The architecture

* Abts and others, "Think Fast: A Tensor Streaming Processor (TSP) for
  Accelerating Deep Learning Workloads", ISCA 2020.
* Abts and others, "A Software-defined Tensor Streaming Multiprocessor for
  Large-scale Machine Learning", ISCA 2022.

# Compilers

* [CS 6120: Advanced Compilers](https://www.cs.cornell.edu/courses/cs6120/2020fa/self-guided/),
  the self-guided version. Look up: intermediate representation, SSA,
  dataflow analysis.
* [The MLIR Toy tutorial](https://mlir.llvm.org/docs/Tutorials/Toy/). How a
  dialect and its passes are written.

# Verified compilation

* [Software Foundations](https://softwarefoundations.cis.upenn.edu/), volumes
  1 and 2. Proving things about programs and languages.
* Leroy, "Formal verification of a realistic compiler", Communications of the
  ACM, 2009. The CompCert overview.
* Rideau and Leroy, "Validating register allocation and spilling", 2010. A
  proved checker in place of a proved algorithm.
* Bhat and others, "Verifying Peephole Rewriting in SSA Compiler IRs", ITP
  2024. Lean-MLIR.
