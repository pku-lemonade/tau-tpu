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

*Read:* `Tau/IR/Kernel.lean`, `Tau/Passes/Unroll.lean`,
`compiler/include/tau/Dialect/TauOps.td`,
`compiler/lib/Transforms/Unroll.cpp`.

*Solutions, not to be opened yet:* `Tau/Proofs/Passes/Unroll.lean`.

*Time:* two days.

# The idea

A kernel is the program a user writes. It loads words from buffers, computes,
and stores words back. It says nothing about slices, streams or cycles.

The compiler represents kernels in MLIR, in a dialect called `tau`. Read
`examples/elementwise/kernel.mlir`. In it, `%a[0, 1]` means position
`0 + 1 * i` of buffer `%a`, where `i` is the iteration of the enclosing loop.
Then run:

```
compiler/build/bin/tau-opt examples/elementwise/kernel.mlir --tau-unroll
```

The pass replaced the loop by four copies of its body, with positions
`[0, 0]`, `[1, 0]`, `[2, 0]` and `[3, 0]`.

The Lean type `Kernel` is a model of that dialect.

{docstring Tau.Idx}

{docstring Tau.Stmt}

{docstring Tau.Item}

Variables and buffers are numbers. A kernel that loads word 0 of buffer 0,
applies `relu`, and stores the result to word 0 of buffer 1:

```lean
def reluKernel : Kernel :=
  [ .stmt (.load 0 0 ⟨0, 0⟩),
    .stmt (.un 1 .relu 0),
    .stmt (.store 1 1 ⟨0, 0⟩) ]
```

# What a kernel means

`Kernel.run` gives the meaning: from the starting contents of the buffers to
their final contents, or `none` if the kernel uses a variable that has no
value or a position outside a buffer. Read it in `Tau/IR/Kernel.lean`, from
`Stmt.exec` up to `Kernel.run`.

Like the machine, it works for any `Sem`. Run on names, the kernel above ends
with buffer 1 holding "`relu` of the word that started in buffer 0":

```lean
example :
    reluKernel.run exprSem [[.init 0 0], [.init 1 0]]
      = some [[.init 0 0], [.un .relu (.init 0 0)]] := by
  rfl
```

`Kernel.run` is the definition of correctness for the whole compiler: a
compiled program is right if it leaves in the buffers what `Kernel.run` says.

# A pass and its proof

`Tau/Passes/Unroll.lean` is the same transformation as the C++ pass, written
in Lean.

{docstring Tau.Kernel.unroll}

A loop of two iterations that copies buffer 0 to buffer 1, unrolled:

```lean
example :
    Kernel.unroll [.loop 2 [.load 0 0 ⟨0, 1⟩, .store 0 1 ⟨0, 1⟩]]
      = [ .load 0 0 ⟨0, 0⟩, .store 0 1 ⟨0, 0⟩,
          .load 0 0 ⟨1, 0⟩, .store 0 1 ⟨1, 0⟩ ] := by
  rfl
```

The theorem says that running the unrolled statements does exactly what
running the kernel does, including when the kernel fails:

```lean
example (S : Sem Nat) (i : Nat) (env : Env Nat) (k : Kernel) :
    execStmts S i env k.unroll = Kernel.exec S env k :=
  Kernel.exec_unroll S i env k
```

The `i` on the left is the loop iteration at which the unrolled statements
are run. Any `i` will do, because unrolling fixes every position: a position
`[base, stride]` in iteration `k` has become `[base + stride * k, 0]`, and
with a stride of 0 the iteration no longer matters.

The proof is a stack of small lemmas, one for each layer of the definition:
an index, a statement, a list of statements, a loop, an item, a kernel. Each
is proved by induction or case analysis on that layer and uses the one below.
When you write a function by recursion on a structure, expect to prove things
about it by induction on the same structure.

# What the proof does and does not cover

The proof is about the Lean function `Kernel.unroll`. It is not about the C++
in `compiler/lib/Transforms/Unroll.cpp`. Nothing in this repository proves
that the two do the same thing. Open both and compare them by eye. That is
all the assurance a model gives, and it is why the course goes on to a
checker.

# How to work through it

1. Read `Tau/IR/Kernel.lean`. Write a kernel of your own in your scratch file
   and run it on names, as above.
2. Read `Tau/Passes/Unroll.lean` and evaluate `Kernel.unroll` on a kernel
   with a loop of three iterations.
3. Do `Exercises/Passes/Unroll.lean` in the order of the file. Each lemma is
   used by the next.

# Lean you will need

* Induction on a list: `induction body generalizing env with`, with cases
  `nil` and `cons s rest ih`. `generalizing env` is needed because the
  environment changes as statements run.
* `cases h : e with`, to split on the result of running one statement, which
  is `none` or `some env'`.
* `simp only [name1, name2]`, to unfold exactly the definitions you name and
  nothing else.

# Exercises

*Guided.* `Exercises/Passes/Unroll.lean`.

*Open.* Write a pass that removes a `store` which is immediately followed by
another `store` to the same position of the same buffer, in a list of
statements:

```
def dropDeadStores : List Stmt → List Stmt
  | .store _ b ix :: .store src b' ix' :: rest => sorry
  | s :: rest => s :: dropDeadStores rest
  | [] => []
```

State the theorem that it keeps what the statements compute, and prove it.
Be careful about one thing: the first store can fail, when its variable has
no value, where your optimized list would not. Decide what your theorem
should say about that case. There is more than one reasonable answer, and the
statement must make the choice explicit.

*Challenge.* Add nested loops to `Item`, with positions that may depend on
both indices. Extend `Kernel.exec` and `Kernel.unroll` and redo the proof.
Lean will make you deal with a type that contains lists of itself.

# Hints

For `Stmt.exec_inst`: `cases s`, then `simp` with the definitions of
`Stmt.inst` and `Stmt.exec` and the lemma `Idx.eval_inst`.

For `execStmts_append` and `execStmts_map_inst`: induction on the list,
generalizing the environment. After unfolding, split on the result of the
first statement.

For `execStmts_unrollLoop`: induction on `n`. Use `execStmts_append`, then
the induction hypothesis, then split on the result of the first `n`
iterations.

# Checkpoint

`lake build Exercises.Passes.Unroll` prints no `sorry` warning. You can say
exactly what `Kernel.exec_unroll` leaves unproved about the compiler.
