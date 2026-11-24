import Tau.Data.Word

/-!
# Operations

The kinds of slice, the operations they can apply to words, and what those
operations compute.

The meaning of the operations is packaged as a `Sem` ("semantics"). The machine
and the compiler's intermediate representation are both written against an
arbitrary `Sem`, so the same definitions can run on real words (`wordSem`) or
on symbolic expressions (`Tau/IR/Expr.lean`). The schedule checker depends on
this.
-/

namespace Tau

/-- The four kinds of slice. -/
inductive Kind where
  /-- Memory: reads and writes words. -/
  | mem
  /-- Vector: lane-by-lane arithmetic. -/
  | vxm
  /-- Rearrangement: moves lanes around. -/
  | sxm
  /-- Matrix: multiply-accumulate. -/
  | mxm
  deriving DecidableEq, Repr

/-- Operations on one word. -/
inductive UnOp where
  /-- Replace negative lanes by zero. -/
  | relu
  /-- Divide by `2 ^ k`, rounding down, then clamp to -128 .. 127. -/
  | requant (k : Nat)
  /-- Move every lane up by `k` places; the lowest `k` lanes become zero. -/
  | shift (k : Nat)
  /-- Rotate the lanes by `k` places. -/
  | rotate (k : Nat)
  deriving DecidableEq, Repr

/-- Operations on two words. -/
inductive BinOp where
  /-- Lane-by-lane addition, wrapping on overflow. -/
  | add
  /-- Lane-by-lane subtraction, wrapping on overflow. -/
  | sub
  /-- Lane-by-lane multiplication, wrapping on overflow. -/
  | mul
  /-- Lane-by-lane signed maximum. -/
  | max
  /-- Lane-by-lane signed minimum. -/
  | min
  deriving DecidableEq, Repr

/-- The kind of slice that can apply a one-word operation. -/
def UnOp.kind : UnOp → Kind
  | .relu | .requant _ => .vxm
  | .shift _ | .rotate _ => .sxm

/-- What the operations compute, over some type `V` of values. -/
structure Sem (V : Type) where
  /-- What a one-word operation computes. -/
  un : UnOp → V → V
  /-- What a two-word operation computes. -/
  bin : BinOp → V → V → V
  /-- A cleared accumulator. -/
  zero : V
  /-- `mac j acc x w`: the accumulator after adding lane `j` of `x` times `w`. -/
  mac : Nat → V → V → V → V

/-- `f` carries the operations of `S` to the operations of `T`. -/
structure Sem.Hom {V W : Type} (S : Sem V) (T : Sem W) (f : V → W) : Prop where
  /-- `f` commutes with every one-word operation. -/
  un : ∀ o a, f (S.un o a) = T.un o (f a)
  /-- `f` commutes with every two-word operation. -/
  bin : ∀ o a b, f (S.bin o a b) = T.bin o (f a) (f b)
  /-- `f` carries the cleared accumulator to the cleared accumulator. -/
  zero : f S.zero = T.zero
  /-- `f` commutes with the multiply-accumulate step. -/
  mac : ∀ j acc x w, f (S.mac j acc x w) = T.mac j (f acc) (f x) (f w)

/-- The operations on real words. -/
def wordSem (lanes : Nat) : Sem (Word lanes) where
  un
    | .relu, a => a.map Lane.relu
    | .requant k, a => a.map (Lane.requant k)
    | .shift k, a => a.shift k
    | .rotate k, a => a.rotate k
  bin
    | .add, a, b => Vector.zipWith (· + ·) a b
    | .sub, a, b => Vector.zipWith (· - ·) a b
    | .mul, a, b => Vector.zipWith (· * ·) a b
    | .max, a, b => Vector.zipWith Lane.max a b
    | .min, a, b => Vector.zipWith Lane.min a b
  zero := Word.zero
  mac := Word.mac

end Tau
