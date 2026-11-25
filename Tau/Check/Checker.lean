import Tau.SliceLevel.Machine
import Tau.IR.Kernel
import Tau.IR.Compiled
import Tau.Passes.Simplify

/-!
# The schedule checker

The compiler turns a kernel into a program for the machine: it decides which
memory holds each buffer, which slice runs each operation, on which cycle, and
on which streams the words travel. Any of those decisions can be wrong.

The checker decides whether a compiled program is right, without looking at how
the compiler made its decisions. It runs the machine on the compiled program
and it runs the kernel, both over expressions instead of real words
(`Tau/IR/Expr.lean`). Each run ends with an expression for every word of every
buffer. If the two runs end with the same expressions, the compiled program
computes what the kernel computes, whatever the buffers hold.

The checker is the machine itself, run on names instead of numbers. That is why
it needs no separate rules about timing, stream reuse or hazards.

The proof that an accepted program is correct is in `Tau/Proofs/Check/`.

Terms to look up: *translation validation*.
-/

namespace Tau

/-- Buffers of the given sizes whose words are the expressions `init b k`. -/
def symBufs (sizes : List Nat) : List (List Expr) :=
  (List.range sizes.length).map fun b =>
    (List.range (sizes[b]?.getD 0)).map fun k => Expr.init b k

/-- The expressions the machine ends with, for every word of every buffer.
`none` if the machine traps. -/
def machineExprs (c : Compiled) : Option (List (List Expr)) :=
  match execute exprSem c.cfg c.prog c.cycles (image c.map c.memSizes Expr.init .fill) with
  | .ok mem => some (extract c.map mem .fill)
  | .error _ => none

/-- The expressions the kernel ends with, for every word of every buffer. -/
def kernelExprs (k : Kernel) (sizes : List Nat) : Option (List (List Expr)) :=
  k.run exprSem (symBufs sizes)

/-- Whether two tables of expressions are the same after simplifying. -/
def sameExprs (a b : List (List Expr)) : Bool :=
  a.map (·.map Expr.simp) == b.map (·.map Expr.simp)

/-- Accept or reject a compiled program for the kernel `k`, whose buffers have
the given sizes. -/
def check (k : Kernel) (sizes : List Nat) (c : Compiled) : Bool :=
  c.map.map (·.size) == sizes &&
  match kernelExprs k sizes, machineExprs c with
  | some a, some b => sameExprs a b
  | _, _ => false

end Tau
