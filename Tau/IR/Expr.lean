import Tau.Isa.Op

/-!
# Expressions

An expression is a value described by how it was computed, not by what it is:
"the word at position 0 of buffer 2, added to ..., then relu".

Expressions form a `Sem` (`exprSem`): applying an operation just builds a
bigger expression. Running the machine or a kernel over `exprSem` therefore
yields, for every word of memory, a record of how the program computes it. This
is called *symbolic execution*.

`Expr.denote` turns an expression back into a value, given real buffer
contents.

Terms to look up: *symbolic execution*, *abstract syntax tree*.
-/

namespace Tau

/-- A value described by how it is computed. -/
inductive Expr where
  /-- The starting contents of word `idx` of buffer `buf`. -/
  | init (buf idx : Nat)
  /-- The starting contents of a memory word that belongs to no buffer. -/
  | fill
  /-- A one-word operation applied to `a`. -/
  | un (op : UnOp) (a : Expr)
  /-- A two-word operation applied to `a` and `b`. -/
  | bin (op : BinOp) (a b : Expr)
  /-- A cleared accumulator. -/
  | zero
  /-- The accumulator `acc` after adding lane `j` of `x` times `w`. -/
  | mac (j : Nat) (acc x w : Expr)
  /-- The constant word with lanes `xs`. -/
  | const (xs : List Int)
  /-- Lane by lane, `a` where `m` is not zero and `b` elsewhere. -/
  | sel (m a b : Expr)
  deriving DecidableEq, Repr

/-- The operations on expressions: each one builds a bigger expression. -/
def exprSem : Sem Expr where
  un := .un
  bin := .bin
  zero := .zero
  mac := .mac
  const := .const
  sel := .sel

variable {V : Type}

/-- Word `idx` of buffer `buf`, or `fill` if there is no such word. -/
def bufWord (bufs : List (List V)) (fill : V) (buf idx : Nat) : V :=
  (bufs[buf]?.getD [])[idx]?.getD fill

/-- The value of an expression, given the starting buffer contents. -/
def Expr.denote (S : Sem V) (bufs : List (List V)) (fill : V) : Expr → V
  | .init buf idx => bufWord bufs fill buf idx
  | .fill => fill
  | .un op a => S.un op (a.denote S bufs fill)
  | .bin op a b => S.bin op (a.denote S bufs fill) (b.denote S bufs fill)
  | .zero => S.zero
  | .mac j acc x w =>
    S.mac j (acc.denote S bufs fill) (x.denote S bufs fill) (w.denote S bufs fill)
  | .const xs => S.const xs
  | .sel m a b =>
    S.sel (m.denote S bufs fill) (a.denote S bufs fill) (b.denote S bufs fill)

end Tau
