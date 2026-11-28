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

*Source:* `compiler/lib/Passes/Simplify.cpp`.

*Specify:* `course/Specify/IR/Simplify.lean`.

*Read:* `spec/Tau/Check/Expr.lean`, `spec/Tau/Check/Simplify.lean`.

*Proofs:* `spec/Tau/Proofs/Check/Simplify.lean`. The two about `simpUn` and
`simpBin` are exercises, and short. The rest are for reading.

*Time:* one day.

# The idea

An expression describes a word by how it was computed.

{docstring Tau.Expr}

You have already used two of these as names: `.init 0 0` and `.fill`.

A word is computed as part of a value: an operation takes values and gives a
value, and a value is one, two or four words. So there is a second kind of
expression, for a value, and the two are defined together. A word is "word
`k` of this value", and a value is an operation applied to values, or some
words side by side.

{docstring Tau.VExpr}

`VExpr.ofWords` makes a value of a list of words. If they are all the words
of one value, in order, it gives that value back, so an expression stays as
small as the computation it describes.

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

{docstring Tau.VExpr.simp}

Here `a` is the value whose one word started at position 0 of buffer 0.

```lean
def a : VExpr := .words (.cons (.init 0 0) .nil)

example : (VExpr.un .i8 .relu (.un .i8 .relu a)).simp = .un .i8 .relu a := by
  decide

example : (VExpr.bin .i8 .max a a).simp = a := by
  decide
```

A word is simplified by simplifying the value it is a word of
(`Expr.simp`).

The compiler's `tau-simplify` pass does the same rewrites on MLIR. See it
work on `examples/nn/linear/kernel.mlir`, which has a `relu` of a `relu`:

```
compiler/build/bin/tau-opt examples/nn/linear/kernel.mlir --tau-simplify
```

Without the compiler, compare `examples/nn/linear/stages/inlined.json` with
`simplified.json` in the same folder.

# What to prove

Simplifying must not change the value. That is only true if the operations
obey certain laws:

{docstring Tau.Sem.Lawful}

The proof has two halves, and they are separate on purpose.

The first half is about expressions and works for any operations that obey
the laws:

```lean
example (S : Sem Nat) (hS : S.Lawful) (bufs : List (List Nat)) (fill : Nat) (v : VExpr) :
    v.simp.denote S bufs fill = v.denote S bufs fill :=
  VExpr.denote_simp S hS bufs fill v
```

The second half shows that real words obey the laws, using the facts about
elements from the chapter on the MAC:

```lean
example : (wordSem 4).Lawful := wordSem_lawful 4
```

This separation is worth copying. The first half would survive a change of
number format untouched.

# How to work through it

1. Read `spec/Tau/Check/Expr.lean` and `spec/Tau/Check/Simplify.lean`.
2. In your scratch file, build an expression that `simp` reduces in two
   places, and check the result with `rfl`.
3. Do `Prove/Check/Simplify.lean`: `denote_simpUn` and `denote_simpBin`.
   Then read `Expr.denote_simp`, `VExpr.denote_simp` and `Exprs.denote_simp`
   below them, which use your two.
4. Read `compiler/lib/Passes/Simplify.cpp`. It makes the same three
   rewrites, on a kernel.
5. Specify that pass in Lean, in `course/Specify/IR/Simplify.lean`. It is the
   hardest "Specify" of the course.
6. Compare what you wrote with `Expr.simp`. The same three rewrites take five
   lines on expressions and several times that on kernels. Say why.

# Lean you will need

* Recursion over types that are defined together. `Expr`, `VExpr` and
  `Exprs` each mention the others, so a fact about one needs the same fact
  about the others, and `induction` does not apply. The three theorems are
  written as functions by pattern matching, one case per constructor, and
  call each other on the parts of the expression. Lean checks that every
  such call is on a smaller expression.
* `unfold simpUn` followed by `split`, to follow the cases of a function
  defined by pattern matching.
* `obtain ⟨h1, rfl⟩ := h`, to take a conjunction apart and substitute an
  equation at once.

# Exercises

*Prove.* `Prove/Check/Simplify.lean`.

*Specify.* `course/Specify/IR/Simplify.lean`: a copy of `tau-simplify`, on
kernels. One of its tests is the check of the next chapter, `checkKernels`,
asked whether your output computes what your input computes.

*State.* `KeepsWhatIsComputed` in that file. It needs the laws as a
hypothesis.

*Questions.* `Simplify.cpp` leaves at least three things open. One to start
you off: is `max` of two separate loads of the same word simplified?

*Claims.* Add to `course/Work/Claims.md` a row for each thing you wrote in this
chapter: what it is, and how it stands.

The next two exercises change files under `spec/Tau/`, which the rest of the
course leaves alone. Do them on a branch: run `git switch -c my-simplifier`
first. While `spec/Tau/Check/Simplify.lean` and its proofs disagree, `lake build`
fails and every file that imports `Tau` shows errors; that is expected, and
it stops when both proofs are repaired. To go back, commit or discard your
changes and run `git switch main`.

*Specify.* Add a rewrite of your own. A candidate: `max a (max a b)` becomes
`max a b`. Add the law it needs to `Sem.Lawful` and the case to `simpBin`.
Before asking anyone to prove your law for words, state it for a single
element and try `bv_decide`. If the law is false you will get a counterexample in
seconds. Then have an agent repair `denote_simpBin` and `wordSem_lawful`, in
`spec/Tau/Proofs/Check/Simplify.lean`, and review the change. It should touch
those two proofs and nothing else.

*State.* Add a rewrite that is wrong, for example `sub a a` becomes `a`. Find
the exact place where the proof stops working, and read the goal Lean shows
you there. It is the statement of the false law. This is what a stuck proof
looks like when the specification is at fault.

*Challenge.* The simplifier makes one pass from the leaves up. Find an
expression it does not fully simplify, define a simplifier that does, and
state that yours keeps values.

# Hints

For `denote_simpUn`: `unfold simpUn`, `split`. The first case has an `if` on
the two types, so `split` again. Where they are equal, `subst` the equation
and the goal becomes the law `relu_relu` after `simp only [VExpr.denote]`.
The other cases are `rfl`.

For `denote_simpBin`: `unfold simpBin`, `split`. In the first case take the
hypothesis apart; the operation is `max` or `min`, the two operands are
equal, and the operand has as many words as the type. The laws ask for the
last as a fact about the value, not about its expression:
`VExpr.length_denote` turns one into the other.

For `course/Specify/IR/Simplify.lean`: walk the statements in order and carry two
things along, the values that were replaced and by what, and the values that
are the result of a `relu`. Apply the replacements to the operands of every
statement before you look at it.

# Checkpoint

`lake build Prove.Check.Simplify` prints no `sorry` warning, and the
report for your copy of the pass says that all rows agree. You can say why
the proof is split into a part about any operations that obey the laws and a
part about one number format.
