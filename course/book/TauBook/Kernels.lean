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

*Sources:* `Tau/Docs/Programs.md`, sections 1 to 3;
`compiler/include/tau/Dialect/TauOps.td`,
`compiler/lib/Transforms/Unroll.cpp`.

*Specify:* `course/Specs/Kernel.lean`, `course/Specs/Unroll.lean`.

*Read side by side:* `course/Specs/ReadCpp.lean`.

*Read, after you have specified:* `Tau/IR/Kernel.lean`,
`Tau/Passes/Unroll.lean`.

*Proofs:* `Tau/Proofs/Passes/Unroll.lean`. Three short ones are exercises.

*Time:* two days.

# The source is code now

Until here the source was a doc. For the compiler it is code: the
definition of the compiler's input language in `TauOps.td`, and a pass in
C++.

Code differs from a doc in two ways that matter to you.

* *It says too much.* `Unroll.cpp` is about ninety lines, and most are about
  MLIR: values, regions, builders, a pass class. A handful say what the pass
  does to a kernel. Your first job is to find them.
* *It never says why.* Code is exact about what it does and silent about
  what it is for. The statement "the output computes what the input
  computes" appears nowhere in the C++. You have to supply it.

Read this chapter to the end of "What a kernel means" with
`course/Specs/Kernel.lean` open, and write `execStmt` before you read
`Stmt.exec`. Then read `Unroll.cpp` and write `course/Specs/Unroll.lean`
before you read "A pass and its proof".

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
`[0, 0]`, `[1, 0]`, `[2, 0]` and `[3, 0]`. Without the compiler, compare
`examples/elementwise/stages/kernel.json` with `unrolled.json` in the same
folder: the same kernel before and after the pass, written as JSON.

The last constructor of `Stmt` below, `pin`, and the third field of `Env`,
`events`, are for saying when a statement happens. No kernel in this chapter
uses them. The chapter "Pins" is about them.

The Lean type `Kernel` says in Lean what that dialect says in MLIR.

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
that the two do the same thing. They are compared on the examples:

```
lake exe tau-check --unroll out/simplified.json out/unrolled.json
```

prints `SAME` if the compiler's output is the kernel that `Kernel.unroll`
gives. That is a test. A Lean copy of a pass gives a proof about the copy
and a test of the original, and no more. It is why the course goes on to a
checker.

# How to work through it

1. Read `examples/elementwise/kernel.mlir` and run `tau-opt` on it as above.
2. Read the descriptions of `tau.load`, `tau.store` and the operations in
   `TauOps.td`. Specify what a statement does, in
   `course/Specs/Kernel.lean`.
3. Read `Tau/IR/Kernel.lean` from `Stmt.exec` to `Kernel.run`. Write a kernel
   of your own in your scratch file and run it on names, as above.
4. Read `Unroll.cpp` with a pencil. Mark each group of lines "about MLIR" or
   "about the kernel".
5. Specify the pass, in `course/Specs/Unroll.lean`. One of its tests compares
   your output with what the real compiler wrote.
6. Read `Tau/Passes/Unroll.lean` beside the C++, and do
   `course/Specs/ReadCpp.lean`: for each group of lines of the C++, what it
   is about, and which Lean definition says the same.
7. In `Exercises/Passes/Unroll.lean`, read the statements of the lemmas in
   order: one for each layer of the definition. Prove the first two and the
   last one. The ones between are given.

# Exercises

*Specify.* `course/Specs/Kernel.lean`: what a statement does.

*Specify.* `course/Specs/Unroll.lean`: a copy of the pass.

*State.* `LoadAfterStore` and `KeepsWhatIsComputed` in those two files.

*Read side by side.* `course/Specs/ReadCpp.lean`. For nine groups of lines of
`Unroll.cpp`, say whether the group is about MLIR, about the kernel, or a
limit, and name the Lean definition that says the same. Then four questions
about where the C++ and its copy differ. The file ends with what this
exercise found in the compiler when it was first written.

Afterwards answer in a comment: how many of the ninety lines are about the
kernel? The C++ gives every copy of the loop body new values, and
`Kernel.unroll` reuses the same numbers in every copy; why is that still the
same pass, and why does `tau-check --unroll` have to compare "up to the
numbering of values"?

*Specify and state.* Write a pass that removes a `store` which is immediately
followed by another `store` to the same position of the same buffer, in a
list of statements:

```
def dropDeadStores : List Stmt → List Stmt
  | .store _ b ix :: .store src b' ix' :: rest => sorry
  | s :: rest => s :: dropDeadStores rest
  | [] => []
```

State the theorem that it keeps what the statements compute. Be careful
about one thing: the first store can fail, when its variable has no value,
where your optimized list would not. Decide what your theorem should say
about that case. There is more than one reasonable answer, and the statement
must make the choice explicit. Then give the proof to an agent and review
what comes back.

*Prove.* `Idx.eval_inst`, `Stmt.exec_inst` and `Kernel.run_unroll` in
`Exercises/Passes/Unroll.lean`.

*Questions.* The descriptions in `TauOps.td` leave at least four things open
about what a statement does.

*Claims.* Add to `course/Work/Claims.md` a row for each thing you wrote in this
chapter: what it is, and how it stands.

*Challenge.* Add nested loops to `Item`, with positions that may depend on
both indices. Extend `Kernel.exec` and `Kernel.unroll`, and say which lemmas
of the proof have to change. Lean will make you deal with a type that
contains lists of itself.

# Hints

For `Stmt.exec_inst`: `cases s`, then `simp` with the definitions of
`Stmt.inst` and `Stmt.exec` and the lemma `Idx.eval_inst`.

For `Kernel.run_unroll`: unfold `Kernel.run`, then rewrite with the two
lemmas just above it.

# Checkpoint

The reports of the three files say that all rows agree, and your copy of the
pass gives the kernel the compiler gave. `lake build Exercises.Passes.Unroll` prints no
`sorry` warning. You can say exactly what `Kernel.run_unroll` leaves
unproved about the compiler.
