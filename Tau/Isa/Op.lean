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
  /-- Negate every lane. -/
  | neg
  /-- The absolute value of every lane. -/
  | abs
  /-- Shift the bits of every lane left by `k`. -/
  | shl (k : Nat)
  /-- Add the constant `c` to every lane. -/
  | addi (c : Int)
  /-- Multiply every lane by the constant `c`. -/
  | muli (c : Int)
  /-- Move every lane up by `k` places; the lowest `k` lanes become zero. -/
  | shift (k : Nat)
  /-- Rotate the lanes by `k` places. -/
  | rotate (k : Nat)
  /-- Put the lanes in the opposite order. -/
  | reverse
  /-- Copy lane `j` to every lane. -/
  | broadcast (j : Nat)
  /-- Lane `i` takes the value of lane `table[i]`. -/
  | permute (table : List Nat)
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
  /-- Bit-by-bit and. -/
  | and
  /-- Bit-by-bit or. -/
  | or
  /-- Bit-by-bit exclusive or. -/
  | xor
  /-- Lane by lane: 1 where the first is less than the second, else 0. -/
  | lt
  deriving DecidableEq, Repr

/-- The kind of slice that can apply a one-word operation. -/
def UnOp.kind : UnOp → Kind
  | .relu | .requant _ | .neg | .abs | .shl _ | .addi _ | .muli _ => .vxm
  | .shift _ | .rotate _ | .reverse | .broadcast _ | .permute _ => .sxm

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
  /-- The word whose lanes are the given integers. -/
  const : List Int → V
  /-- `sel m a b`: lane by lane, `a` where `m` is not zero and `b` elsewhere. -/
  sel : V → V → V → V

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
  /-- `f` carries each constant to the same constant. -/
  const : ∀ xs, f (S.const xs) = T.const xs
  /-- `f` commutes with selection. -/
  sel : ∀ m a b, f (S.sel m a b) = T.sel (f m) (f a) (f b)

/-- The operations on real words. -/
def wordSem (lanes : Nat) : Sem (Word lanes) where
  un
    | .relu, a => a.map Lane.relu
    | .requant k, a => a.map (Lane.requant k)
    | .neg, a => a.map fun x : Lane => -x
    | .abs, a => a.map Lane.abs
    | .shl k, a => a.map fun x : Lane => x <<< k
    | .addi c, a => a.map fun x : Lane => x + BitVec.ofInt 32 c
    | .muli c, a => a.map fun x : Lane => x * BitVec.ofInt 32 c
    | .shift k, a => a.shift k
    | .rotate k, a => a.rotate k
    | .reverse, a => a.reverse
    | .broadcast j, a => a.broadcast j
    | .permute table, a => a.permute table
  bin
    | .add, a, b => Vector.zipWith (· + ·) a b
    | .sub, a, b => Vector.zipWith (· - ·) a b
    | .mul, a, b => Vector.zipWith (· * ·) a b
    | .max, a, b => Vector.zipWith Lane.max a b
    | .min, a, b => Vector.zipWith Lane.min a b
    | .and, a, b => Vector.zipWith (· &&& ·) a b
    | .or, a, b => Vector.zipWith (· ||| ·) a b
    | .xor, a, b => Vector.zipWith (· ^^^ ·) a b
    | .lt, a, b => Vector.zipWith Lane.lt a b
  zero := Word.zero
  mac := Word.mac
  const := Word.ofInts
  sel := Word.sel

end Tau
