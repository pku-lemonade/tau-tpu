import Tau.Check.Checker
import Tau.IR.Placed

/-!
# Checking each compiler pass on its own

`check` (`Tau/Check/Checker.lean`) compares the compiled program with the
kernel. That covers the whole compiler at once. This file has one check for
each pass. Each compares the output of the pass with its input, so a
rejection names the pass that went wrong.

| Pass | Input | Output | Check |
|---|---|---|---|
| `tau-simplify` | a kernel | a kernel | `checkKernels` |
| `tau-unroll` | a kernel | a kernel | `checkKernels` |
| `tau-place` | a kernel | a placed program | `checkPlaced` |
| `tau-schedule` | a placed program | a compiled program | `checkScheduled` |
| `tau-route` | a compiled program | a compiled program | `checkRouted` |

Every check works the same way. It runs both sides on expressions, which
gives an expression for every word of every buffer, and compares the two
tables after simplifying them. The kernel side is `kernelExprs`, the placed
side is `placedExprs`, and the compiled side is `machineExprs`.

Each check asks whether the output computes what the input computes. It does
not ask how the pass got there: `checkScheduled` accepts any timed program
that ends with the buffers of the placed program, including one whose
instructions are different.

`tau-schedule` writes its output with a stream for every word, on a chip with
as many streams as that takes, so that the schedule can be checked before
any stream is shared. `tau-route` then fits the words onto the streams the
chip has.

The forms are in `Tau/IR/`. The soundness theorems, one for each check, are
in `Tau/Proofs/Check/Passes.lean`.

Terms to look up: *translation validation*.
-/

namespace Tau

/-- The expressions a placed program ends with, for every word of every
buffer. `none` if an instruction cannot be carried out. -/
def placedExprs (pl : Placed) : Option (List (List Expr)) :=
  match pl.execute exprSem (image pl.map pl.memSizes Expr.init .fill) with
  | some mem => some (extract pl.map mem .fill)
  | none => none

/-- `tau-simplify` and `tau-unroll`: accept or reject the kernel `k'` as a
rewriting of the kernel `k`. -/
def checkKernels (k k' : Kernel) (sizes : List Nat) : Bool :=
  match kernelExprs k sizes, kernelExprs k' sizes with
  | some a, some b => sameExprs a b
  | _, _ => false

/-- `tau-place`: accept or reject the placed program `pl` for the kernel
`k`. -/
def checkPlaced (k : Kernel) (sizes : List Nat) (pl : Placed) : Bool :=
  pl.map.map (·.size) == sizes &&
  match kernelExprs k sizes, placedExprs pl with
  | some a, some b => sameExprs a b
  | _, _ => false

/-- `tau-schedule`: accept or reject the compiled program `c` as a schedule
of the placed program `pl`. -/
def checkScheduled (pl : Placed) (c : Compiled) : Bool :=
  match placedExprs pl, machineExprs c with
  | some a, some b => sameExprs a b
  | _, _ => false

/-- `tau-route`: accept or reject the compiled program `c'` as a routing of
the compiled program `c`. -/
def checkRouted (c c' : Compiled) : Bool :=
  match machineExprs c, machineExprs c' with
  | some a, some b => sameExprs a b
  | _, _ => false

end Tau
