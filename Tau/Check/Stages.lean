import Tau.Check.Checker
import Tau.IR.Placed

/-!
# Checking each compiler pass on its own

`check` (`Tau/Check/Checker.lean`) decides whether the finished program is
right. When it says no, it does not say which pass went wrong. This file adds
a check for the output of each earlier pass, so that the first rejected stage
names the faulty pass.

Every check compares against the kernel as the user wrote it, in the same
way: run both sides on expressions and compare the results.

| Pass | Its output | Checked by |
|---|---|---|
| `tau-simplify` | a kernel | `checkKernels` |
| `tau-unroll` | a kernel | `checkKernels` |
| `tau-place` | instructions in order, no cycles (`Placed`) | `checkPlaced` |
| `tau-schedule` | a program in which every word has its own stream | `check` |
| `tau-route` | the finished program | `check` |

The schedule can be checked before routing because a routing in which no two
words share a stream cannot be wrong. The compiler writes the scheduled
program with such a routing, on a chip with as many streams as that takes.

The placed form and its meaning are in `Tau/IR/Placed.lean`.

The soundness proofs are in `Tau/Proofs/Check/Stages.lean`.
-/

namespace Tau

/-- The expressions a placed program ends with, for every word of every
buffer. -/
def placedExprs (pl : Placed) : Option (List (List Expr)) :=
  match pl.execute exprSem (image pl.map pl.memSizes Expr.init .fill) with
  | some mem => some (extract pl.map mem .fill)
  | none => none

/-- Accept or reject the output of `tau-place` for the kernel `k`. -/
def checkPlaced (k : Kernel) (sizes : List Nat) (pl : Placed) : Bool :=
  pl.map.map (·.size) == sizes &&
  match placedExprs pl, kernelExprs k sizes with
  | some m, some e => m.map (·.map Expr.simp) == e.map (·.map Expr.simp)
  | _, _ => false

/-- Accept or reject a kernel `k'` produced from the kernel `k` by a pass
that should not change what it computes. -/
def checkKernels (k k' : Kernel) (sizes : List Nat) : Bool :=
  match kernelExprs k sizes, kernelExprs k' sizes with
  | some a, some b => a.map (·.map Expr.simp) == b.map (·.map Expr.simp)
  | _, _ => false

end Tau
