import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Kernels and loop unrolling" =>
*Terms to look up:* intermediate representation, SSA form, compiler pass,
loop unrolling, MLIR.

*Files:* `Tau/IR/Kernel.lean`, `Tau/Passes/Unroll.lean`,
`Tau/Proofs/Passes/Unroll.lean`, `compiler/include/tau/Dialect/TauOps.td`,
`compiler/lib/Transforms/Unroll.cpp`.

# The idea

A kernel is the program a user writes. It loads words from buffers, computes,
and stores words back. It says nothing about slices, streams or cycles.

The compiler represents kernels in MLIR, in a dialect called `tau`. Read
`examples/elementwise/kernel.mlir`, then run:

```
compiler/build/bin/tau-opt examples/elementwise/kernel.mlir --tau-unroll
```

The pass replaced the loop by four copies of its body.

The Lean type `Kernel` is a model of that dialect:

{docstring Tau.Stmt}

{docstring Tau.Item}

What a kernel computes is given by `Kernel.run`. That function is the
definition of correctness for the whole compiler: a compiled program is right
if it leaves in the buffers what `Kernel.run` says.

# A pass and its proof

`Tau/Passes/Unroll.lean` is the same transformation as the C++ pass, written
in Lean:

{docstring Tau.Kernel.unroll}

The theorem says that running the unrolled statements does exactly what
running the kernel does, including when the kernel fails:

```lean
example (S : Sem Nat) (i : Nat) (env : Env Nat) (k : Kernel) :
    execStmts S i env k.unroll = Kernel.exec S env k :=
  Kernel.exec_unroll S i env k
```

The proof is a stack of small lemmas, each about one layer of the definition:
an index, a statement, a list of statements, a loop, an item, a kernel. Each
is proved by induction or case analysis on that layer and uses the one below.
When you write a function by recursion on a structure, expect to prove things
about it by induction on the same structure.

# What the proof does and does not cover

The proof is about the Lean function `Kernel.unroll`. It is not about the C++
in `compiler/lib/Transforms/Unroll.cpp`. Nothing in this repository proves
that the two do the same thing. Open both and compare them by eye. That is all
the assurance there is at this step, and it is why the course goes on to a
checker.

# Exercises

*Guided.* `Exercises/Passes/Unroll.lean`.

*Open.* Write a pass that removes a `store` which is immediately followed by
another `store` to the same position of the same buffer. Write the theorem
that says it keeps what a kernel computes, and prove it. Be careful about
what "the same position" means inside a loop.

*Challenge.* Add nested loops to `Item`, with positions that may depend on
both indices. Extend `Kernel.exec` and `Kernel.unroll` and redo the proof.
Lean will make you deal with a type that contains lists of itself.

# Checkpoint

You can give a small language a meaning in Lean, write a transformation on
it, and prove the transformation keeps the meaning. You can also say exactly
what such a proof leaves unproved.
