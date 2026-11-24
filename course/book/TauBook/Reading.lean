import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Reading list" =>
The course does not teach the subjects below. This list says where to look up
the terms each chapter names. Ten minutes on a term is usually enough.

# Lean

* [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4).
  A first two hours of proving, in the browser. Do the Tutorial, Addition and
  Multiplication worlds before day one.
* [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/).
  Lean as a programming language. Read "Getting to Know Lean" alongside the
  chapter "Working in Lean", and the sections on structures, datatypes and
  polymorphism before the shift register.
* [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/).
  The logic and the tactics in depth. Read "Tactics" and "Induction and
  Recursion" during the block chapters.
* [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/). A gentle
  introduction to writing proofs, in Lean. Use it if proof by cases or by
  induction feels unfamiliar.
* [The Lean Language Reference](https://lean-lang.org/doc/reference/latest/).
  Look things up here, including `omega`, `simp` and `bv_decide`.

# Digital hardware

For the terms of the block chapters: flip-flop, register, register with
enable, shift register, clock cycle, accumulator, down counter, loop counter,
program counter, random-access memory, address, read port, write port,
pipelining, latency.

* [Nand to Tetris](https://www.nand2tetris.org/), chapter 3, "Memory". Covers
  flip-flops, registers, memory and the clock in about twenty pages.
* Harris and Harris, _Digital Design and Computer Architecture_. Chapter 3
  for registers and timing, chapter 5 for memory arrays, chapter 7 for
  pipelining.

For two's complement, overflow and saturating arithmetic: Harris and Harris,
chapter 1, or any introduction to computer arithmetic.

For dot product and matrix-vector product: the first chapter of any linear
algebra text, or the Wikipedia articles of those names.

For systolic arrays and multiply-accumulate:

* H. T. Kung, "Why Systolic Architectures?", IEEE Computer, 1982. The
  original argument. Short and readable.

For SAT solvers, the first chapter of any SAT handbook, or the Wikipedia
article on the Boolean satisfiability problem, is enough.

# The architecture

For static scheduling, instruction set architecture, SIMD, and the design
tau-tpu follows:

* Abts and others, "Think Fast: A Tensor Streaming Processor (TSP) for
  Accelerating Deep Learning Workloads", ISCA 2020. Read sections 1 to 3.
* Abts and others, "A Software-defined Tensor Streaming Multiprocessor for
  Large-scale Machine Learning", ISCA 2022.

# Compilers

For intermediate representation, abstract syntax tree, SSA form, compiler
pass, loop unrolling and peephole optimization:

* [CS 6120: Advanced Compilers](https://www.cs.cornell.edu/courses/cs6120/2020fa/self-guided/),
  the self-guided version. Lessons 2 and 3 cover representations and local
  optimization; lesson 5 covers SSA.
* [The MLIR Toy tutorial](https://mlir.llvm.org/docs/Tutorials/Toy/).
  Chapters 2 and 3 show how a dialect and a rewrite are written.

# Verified compilation

For translation validation, symbolic execution, homomorphism (a function
that respects the operations on both sides), refinement, simulation relation
and abstraction function:

* [Software Foundations](https://softwarefoundations.cis.upenn.edu/), volumes
  1 and 2. Proving things about programs and languages.
* Leroy, "Formal verification of a realistic compiler", Communications of the
  ACM, 2009. The CompCert overview; section 2 explains verified compilers
  against validated ones.
* Rideau and Leroy, "Validating register allocation and spilling", 2010. A
  proved checker in place of a proved algorithm.
* Bhat and others, "Verifying Peephole Rewriting in SSA Compiler IRs", ITP
  2024. Lean-MLIR.
