import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Expressions and simplification" =>
*Terms to look up:* symbolic execution, abstract syntax tree, peephole
optimization.

*Files:* `Tau/IR/Expr.lean`, `Tau/Passes/Simplify.lean`,
`Tau/Proofs/Passes/Simplify.lean`, `compiler/lib/Transforms/Simplify.cpp`.

# The idea

An expression describes a value by how it was computed.

{docstring Tau.Expr}

Expressions are themselves a `Sem`: applying an operation to expressions
builds a bigger expression.

{docstring Tau.exprSem}

So the machine of chapter 8 and the kernels of chapter 9, which work for any
`Sem`, can be run on expressions. The result is, for every word of memory, a
record of how it was computed from the inputs. Try it:

```lean
example :
    Kernel.run exprSem [.stmt (.load 0 0 ⟨0, 0⟩), .stmt (.un 1 .relu 0),
                        .stmt (.store 1 1 ⟨0, 0⟩)]
      [[.init 0 0], [.init 1 0]]
    = some [[.init 0 0], [.un .relu (.init 0 0)]] := by
  decide
```

`Expr.denote` goes the other way: given real buffer contents, it computes the
value an expression stands for.

# A simplifier and its proof

{docstring Tau.Expr.simp}

Simplifying must not change the value. That is only true if the operations
obey certain laws:

{docstring Tau.Sem.Lawful}

The proof has two halves, and they are separate on purpose. The first half,
`Expr.denote_simp`, is an induction on the expression and works for any
operations that obey the laws. The second half, `wordSem_lawful`, shows that
real words obey them, using the facts about lanes from chapter 4.

This separation is worth copying. The first half would survive a change of
number format untouched.

# Exercises

*Guided.* `Exercises/Passes/Simplify.lean`.

*Open.* Add a rewrite of your own to `simpBin` or `simpUn`, add the law it
needs to `Sem.Lawful`, and repair both proofs. A candidate: `relu` of a `max`
with a `relu` inside it. Before proving your law for words, test it with
`bv_decide` on single lanes.

*Open.* Add a rewrite that is wrong, for example `sub a a` becomes `a`. Find
the exact place where the proof stops working and read the goal Lean shows
you there.

*Challenge.* The simplifier makes one pass from the leaves up. Give an
expression that it does not fully simplify, define a simplifier that does,
and prove that yours terminates and keeps values.

# Checkpoint

You can run a program on symbols, and you have a verified optimizer whose
proof is split into a generic part and a part about a particular number
format.
