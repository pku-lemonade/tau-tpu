import VersoManual
import Tau
import TauBook.Kernels
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Expressions and simplification" =>
*Terms to look up:* symbolic execution, abstract syntax tree, peephole
optimization.

*Source:* `compiler/lib/Transforms/Simplify.cpp`.

*Specify:* `course/Specs/Simplify.lean`.

*Read:* `Tau/IR/Expr.lean`, `Tau/Check/Simplify.lean`.

*Proofs:* `Tau/Proofs/Check/Simplify.lean`. All of them are exercises, and
short.

*Time:* one day.

# The idea

An expression describes a value by how it was computed.

{docstring Tau.Expr}

You have already used two of these as names: `.init 0 0` and `.fill`.

Expressions are themselves a `Sem`: applying an operation to expressions
builds a bigger expression.

{docstring Tau.exprSem}

So the machine and the kernels, which work for any `Sem`, can be run on
expressions. The result is, for every word of memory, a record of how it was
computed from the inputs. This is called _symbolic execution_. The previous
two chapters did it without saying so.

`Expr.denote` goes the other way: given real buffer contents, it computes the
value an expression stands for. Read its definition. It replaces each `init`
by the word from the buffer and applies the real operations.

# A simplifier

{docstring Tau.Expr.simp}

```lean
example :
    (Expr.un .relu (.un .relu (.init 0 0))).simp = .un .relu (.init 0 0) := by
  rfl

example : (Expr.bin .max (.init 0 0) (.init 0 0)).simp = .init 0 0 := by
  rfl
```

The compiler's `tau-simplify` pass does the same rewrites on MLIR. See it
work on `examples/linear/kernel.mlir`, which has a `relu` of a `relu`:

```
compiler/build/bin/tau-opt examples/linear/kernel.mlir --tau-simplify
```

Without the compiler, compare `examples/linear/stages/kernel.json` with
`simplified.json` in the same folder.

# What to prove

Simplifying must not change the value. That is only true if the operations
obey certain laws:

{docstring Tau.Sem.Lawful}

The proof has two halves, and they are separate on purpose.

The first half is about expressions and works for any operations that obey
the laws:

```lean
example (S : Sem Nat) (hS : S.Lawful) (bufs : List (List Nat)) (fill : Nat) (e : Expr) :
    e.simp.denote S bufs fill = e.denote S bufs fill :=
  Expr.denote_simp S hS bufs fill e
```

The second half shows that real words obey the laws, using the facts about
lanes from the chapter on the MAC:

```lean
example : (wordSem 4).Lawful := wordSem_lawful 4
```

This separation is worth copying. The first half would survive a change of
number format untouched.

# How to work through it

1. Read `Tau/IR/Expr.lean` and `Tau/Check/Simplify.lean`.
2. In your scratch file, build an expression that `simp` reduces in two
   places, and check the result with `rfl`.
3. Do `Exercises/Check/Simplify.lean`: first `denote_simpUn` and
   `denote_simpBin`, then `Expr.denote_simp` by induction on the expression.
4. Read `compiler/lib/Transforms/Simplify.cpp`. It makes the same three
   rewrites, on a kernel.
5. Specify that pass in Lean, in `course/Specs/Simplify.lean`. It is the
   hardest "Specify" of the course.
6. Compare what you wrote with `Expr.simp`. The same three rewrites take five
   lines on expressions and several times that on kernels. Say why.

# Lean you will need

* Induction on an inductive type you defined: `induction e with`, one case
  per constructor, with an induction hypothesis for each sub-expression.
* `unfold simpUn` followed by `split`, to follow the cases of a function
  defined by pattern matching.
* `obtain ⟨h1, rfl⟩ := h`, to take a conjunction apart and substitute an
  equation at once.

# Exercises

*Prove.* `Exercises/Check/Simplify.lean`.

*Specify.* `course/Specs/Simplify.lean`: a copy of `tau-simplify`, on
kernels. One of its tests is the check of the next chapter, `checkKernels`,
asked whether your output computes what your input computes.

*State.* `KeepsWhatIsComputed` in that file. It needs the laws as a
hypothesis.

*Questions.* `Simplify.cpp` leaves at least three things open. One to start
you off: is `max` of two separate loads of the same word simplified?

*Claims.* Add to `course/Work/Claims.md` a row for each thing you wrote in this
chapter: what it is, and how it stands.

The next two exercises change files under `Tau/`, which the rest of the
course leaves alone. Do them on a branch: run `git switch -c my-simplifier`
first. While `Tau/Check/Simplify.lean` and its proofs disagree, `lake build`
fails and every file that imports `Tau` shows errors; that is expected, and
it stops when both proofs are repaired. To go back, commit or discard your
changes and run `git switch main`.

*Specify.* Add a rewrite of your own. A candidate: `max a (max a b)` becomes
`max a b`. Add the law it needs to `Sem.Lawful` and the case to `simpBin`.
Before asking anyone to prove your law for words, state it for a single lane
and try `bv_decide`. If the law is false you will get a counterexample in
seconds. Then have an agent repair `denote_simpBin` and `wordSem_lawful`, in
`Tau/Proofs/Check/Simplify.lean`, and review the change. It should touch
those two proofs and nothing else.

*State.* Add a rewrite that is wrong, for example `sub a a` becomes `a`. Find
the exact place where the proof stops working, and read the goal Lean shows
you there. It is the statement of the false law. This is what a stuck proof
looks like when the specification is at fault.

*Challenge.* The simplifier makes one pass from the leaves up. Find an
expression it does not fully simplify, define a simplifier that does, and
state that yours keeps values.

# Hints

For `denote_simpUn`: `unfold simpUn`, `split`. In the first case the goal
becomes the law `relu_relu` after `simp only [Expr.denote]`. The second case
is `rfl`.

For `denote_simpBin`: `unfold simpBin`, `split`. In the first case take the
hypothesis apart; the operation is `max` or `min` and the two operands are
equal.

For `Expr.denote_simp`: in the `un` and `bin` cases use the two lemmas and
the induction hypotheses. The other cases are `rfl` or `simp only` with the
definitions.

For `course/Specs/Simplify.lean`: walk the statements in order and carry two
things along, the values that were replaced and by what, and the values that
are the result of a `relu`. Apply the replacements to the operands of every
statement before you look at it.

# Checkpoint

`lake build Exercises.Check.Simplify` prints no `sorry` warning, and the
report for your copy of the pass says that all rows agree. You can say why
the proof is split into a part about any operations that obey the laws and a
part about one number format.
