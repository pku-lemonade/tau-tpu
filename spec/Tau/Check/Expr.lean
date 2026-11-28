import Tau.Isa.Op
import Tau.IR.MemMap

/-!
# Expressions

An expression is a word described by how it was computed, not by what it is:
"the low word of: the value at position 0 of buffer 2, added to ..., then
relu".

A word is computed as part of a value (`Tau.Isa.Word`), so there are two
kinds of expression: `Expr` for a word and `VExpr` for a value. A word is
"word `k` of this value"; a value is an operation applied to values. When the
words of a value are put side by side again, they are that value: this keeps
an expression as small as the computation it describes.

Expressions form a `Sem` (`exprSem`): applying an operation just builds a
bigger expression. Running the machine or a kernel over `exprSem` therefore
yields, for every word of memory, a record of how the program computes it. This
is called *symbolic execution*.

`Expr.denote` turns an expression back into a word, given real buffer
contents.

Terms to look up: *symbolic execution*, *abstract syntax tree*.

Docs: Compiler 7 (`docs/`).
-/

namespace Tau

mutual

/-- A word described by how it is computed. -/
inductive Expr where
  /-- The starting contents of word `idx` of buffer `buf`. -/
  | init (buf idx : Nat)
  /-- The starting contents of a memory word that belongs to no buffer. -/
  | fill
  /-- The word with every lane zero. -/
  | zero
  /-- Word `k` of the value `v`. -/
  | word (k : Nat) (v : VExpr)
  deriving DecidableEq, Repr

/-- A value described by how it is computed. -/
inductive VExpr where
  /-- The value whose words are `ws`, the low word first. -/
  | words (ws : Exprs)
  /-- A one-value operation of type `ty` applied to `a`. -/
  | un (ty : DType) (op : UnOp) (a : VExpr)
  /-- A two-value operation of type `ty` applied to `a` and `b`. -/
  | bin (ty : DType) (op : BinOp) (a b : VExpr)
  /-- The product of the matrix with the rows `rows` and the word `x`. -/
  | matvec (rows : Exprs) (x : Expr)
  /-- The constant of type `ty` with elements `xs`. -/
  | const (ty : DType) (xs : List Int)
  /-- Element by element, `a` where `m` is not zero and `b` elsewhere. -/
  | sel (ty : DType) (m a b : VExpr)
  deriving DecidableEq, Repr

/-- A list of words, each described by how it is computed. It is a type of
its own so that an expression can hold one. -/
inductive Exprs where
  /-- No words. -/
  | nil
  /-- The word `e`, and then the words `rest`. -/
  | cons (e : Expr) (rest : Exprs)
  deriving DecidableEq, Repr

end

/-- A list of expressions as an `Exprs`. -/
def Exprs.ofList : List Expr → Exprs
  | [] => .nil
  | e :: rest => .cons e (Exprs.ofList rest)

/-- The number of words. -/
def Exprs.length : Exprs → Nat
  | .nil => 0
  | .cons _ rest => rest.length + 1

/-- The number of words of a value. -/
def VExpr.width : VExpr → Nat
  | .words ws => ws.length
  | .un ty op _ => (op.out ty).bytes
  | .bin ty _ _ _ => ty.bytes
  | .matvec _ _ => DType.i32.bytes
  | .const ty _ => ty.bytes
  | .sel ty _ _ _ => ty.bytes

/-- Whether `e` is word `k` of `v`. Two expressions that are one object in
memory are equal without being compared, which is the usual case here. -/
def Expr.isWord (e : Expr) (k : Nat) (v : VExpr) : Bool :=
  match e with
  | .word k' v' => k' == k && withPtrEq v' v (fun _ => v' == v) (by simp)
  | _ => false

/-- Whether `es` are the words `k`, `k + 1`, ... of `v`. -/
def VExpr.hasWords (v : VExpr) : Nat → List Expr → Bool
  | _, [] => true
  | k, e :: rest => e.isWord k v && v.hasWords (k + 1) rest

/-- The value with the words `es`. If they are all the words of one value, in
order, it is that value. -/
def VExpr.ofWords (es : List Expr) : VExpr :=
  match es with
  | .word 0 v :: rest =>
    if v.width = rest.length + 1 ∧ v.hasWords 1 rest then v else .words (Exprs.ofList es)
  | _ => .words (Exprs.ofList es)

/-- The first `n` words of a value. -/
def VExpr.toWords (n : Nat) (v : VExpr) : List Expr :=
  (List.range n).map fun k => .word k v

/-- The operations on expressions: each one builds a bigger expression. -/
def exprSem : Sem Expr where
  un ty op a := (VExpr.un ty op (.ofWords a)).toWords (op.out ty).bytes
  bin ty op a b := (VExpr.bin ty op (.ofWords a) (.ofWords b)).toWords ty.bytes
  zero := .zero
  matvec rows x := (VExpr.matvec (Exprs.ofList rows) x).toWords DType.i32.bytes
  const ty xs := (VExpr.const ty xs).toWords ty.bytes
  sel ty m a b := (VExpr.sel ty (.ofWords m) (.ofWords a) (.ofWords b)).toWords ty.bytes

variable {V : Type}

mutual

/-- The word an expression stands for, given the starting buffer contents. -/
def Expr.denote (S : Sem V) (bufs : List (List V)) (fill : V) : Expr → V
  | .init buf idx => bufWord bufs fill buf idx
  | .fill => fill
  | .zero => S.zero
  | .word k v => (v.denote S bufs fill)[k]?.getD S.zero

/-- The value an expression stands for. -/
def VExpr.denote (S : Sem V) (bufs : List (List V)) (fill : V) : VExpr → List V
  | .words ws => ws.denote S bufs fill
  | .un ty op a => S.un ty op (a.denote S bufs fill)
  | .bin ty op a b => S.bin ty op (a.denote S bufs fill) (b.denote S bufs fill)
  | .matvec rows x => S.matvec (rows.denote S bufs fill) (x.denote S bufs fill)
  | .const ty xs => S.const ty xs
  | .sel ty m a b =>
    S.sel ty (m.denote S bufs fill) (a.denote S bufs fill) (b.denote S bufs fill)

/-- The words a list of expressions stands for. -/
def Exprs.denote (S : Sem V) (bufs : List (List V)) (fill : V) : Exprs → List V
  | .nil => []
  | .cons e rest => e.denote S bufs fill :: rest.denote S bufs fill

end

end Tau
