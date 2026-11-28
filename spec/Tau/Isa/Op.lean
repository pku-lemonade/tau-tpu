import Tau.Isa.Value

/-!
# Operations

The kinds of slice, the operations they can apply to values, and what those
operations compute.

An operation has a type (`DType`): it takes values of that type, each a list
of that many words, and gives a value. The meaning of the operations is
packaged as a `Sem` ("semantics"). The machine and the compiler's
intermediate representation are both written against an arbitrary `Sem`, so
the same definitions can run on real words (`wordSem`) or on symbolic
expressions (`Tau.Check.Expr`). The schedule checker depends on this.

Docs: Machine 3.1 and 3.6 (`docs/`).
-/

namespace Tau

/-- The four kinds of slice. -/
inductive Kind where
  /-- Memory: reads and writes words. -/
  | mem
  /-- Vector: arithmetic on values, element by element. -/
  | vxm
  /-- Rearrangement: moves the elements of a value around. -/
  | sxm
  /-- Matrix: the product of a matrix with a word. -/
  | mxm
  deriving DecidableEq, Repr

/-- Operations on one value. -/
inductive UnOp where
  /-- Replace negative elements by zero. -/
  | relu
  /-- Divide by `2 ^ k`, rounding down, then clamp to -128 .. 127. The result
  is a value of 8 bits. -/
  | requant (k : Nat)
  /-- Negate every element. -/
  | neg
  /-- The absolute value of every element. -/
  | abs
  /-- Shift the bits of every element left by `k`. -/
  | shl (k : Nat)
  /-- Add the constant `c` to every element. -/
  | addi (c : Int)
  /-- Multiply every element by the constant `c`. -/
  | muli (c : Int)
  /-- The same elements as a value of the type `to`, which has at least as
  many bits. -/
  | widen (to : DType)
  /-- Move every element up by `k` places; the lowest `k` become zero. -/
  | shift (k : Nat)
  /-- Rotate the elements by `k` places. -/
  | rotate (k : Nat)
  /-- Put the elements in the opposite order. -/
  | reverse
  /-- Copy element `j` to every element. -/
  | broadcast (j : Nat)
  /-- Element `i` takes the value of element `table[i]`. -/
  | permute (table : List Nat)
  deriving DecidableEq, Repr

/-- Operations on two values of one type, element by element. -/
inductive BinOp where
  /-- Addition, wrapping on overflow. -/
  | add
  /-- Subtraction, wrapping on overflow. -/
  | sub
  /-- Multiplication, wrapping on overflow. -/
  | mul
  /-- Signed maximum. -/
  | max
  /-- Signed minimum. -/
  | min
  /-- Bit-by-bit and. -/
  | and
  /-- Bit-by-bit or. -/
  | or
  /-- Bit-by-bit exclusive or. -/
  | xor
  /-- 1 where the first is less than the second, else 0. -/
  | lt
  deriving DecidableEq, Repr

/-- The kind of slice that can apply a one-value operation. -/
def UnOp.kind : UnOp → Kind
  | .relu | .requant _ | .neg | .abs | .shl _ | .addi _ | .muli _ | .widen _ => .vxm
  | .shift _ | .rotate _ | .reverse | .broadcast _ | .permute _ => .sxm

/-- The name of a one-value operation, as Formats 3 writes it in `fn`. -/
def UnOp.name : UnOp → String
  | .relu => "relu"
  | .requant _ => "requant"
  | .neg => "neg"
  | .abs => "abs"
  | .shl _ => "shl"
  | .addi _ => "addi"
  | .muli _ => "muli"
  | .widen _ => "widen"
  | .shift _ => "shift"
  | .rotate _ => "rotate"
  | .reverse => "reverse"
  | .broadcast _ => "broadcast"
  | .permute _ => "permute"

/-- The name of a two-value operation, as Formats 3 writes it in `fn`. -/
def BinOp.name : BinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .max => "max"
  | .min => "min"
  | .and => "and"
  | .or => "or"
  | .xor => "xor"
  | .lt => "lt"

/-- The type of the result of a one-value operation on a value of type `ty`. -/
def UnOp.out (ty : DType) : UnOp → DType
  | .requant _ => .i8
  | .widen to => to
  | _ => ty

/-- What the operations compute, over some type `V` of words. A value is a
list of words, and an operation of type `ty` takes values of `ty.bytes`
words. -/
structure Sem (V : Type) where
  /-- What a one-value operation computes: a value of `(op.out ty).bytes`
  words. -/
  un : DType → UnOp → List V → List V
  /-- What a two-value operation computes: a value of `ty.bytes` words. -/
  bin : DType → BinOp → List V → List V → List V
  /-- The word with every lane zero. -/
  zero : V
  /-- `matvec rows x`: the product of a matrix with the word `x`, a value of
  32 bits. Element `i` of it is the dot product of `rows[i]` with `x`, and
  zero if there is no such row. -/
  matvec : List V → V → List V
  /-- The value of type `ty` whose elements are the given integers. -/
  const : DType → List Int → List V
  /-- `sel ty m a b`: element by element, `a` where `m` is not zero and `b`
  elsewhere. -/
  sel : DType → List V → List V → List V → List V

/-- `f` carries the operations of `S` to the operations of `T`. -/
structure Sem.Hom {V W : Type} (S : Sem V) (T : Sem W) (f : V → W) : Prop where
  /-- `f` commutes with every one-value operation. -/
  un : ∀ ty o a, (S.un ty o a).map f = T.un ty o (a.map f)
  /-- `f` commutes with every two-value operation. -/
  bin : ∀ ty o a b, (S.bin ty o a b).map f = T.bin ty o (a.map f) (b.map f)
  /-- `f` carries the zero word to the zero word. -/
  zero : f S.zero = T.zero
  /-- `f` commutes with the product of a matrix and a word. -/
  matvec : ∀ rows x, (S.matvec rows x).map f = T.matvec (rows.map f) (f x)
  /-- `f` carries each constant to the same constant. -/
  const : ∀ ty xs, (S.const ty xs).map f = T.const ty xs
  /-- `f` commutes with selection. -/
  sel : ∀ ty m a b, (S.sel ty m a b).map f = T.sel ty (m.map f) (a.map f) (b.map f)

/-- The operations give values of the right number of words, whatever they
are given. -/
structure Sem.Sized {V : Type} (S : Sem V) : Prop where
  /-- A one-value operation gives a value of its result type. -/
  un : ∀ ty o a, (S.un ty o a).length = (o.out ty).bytes
  /-- A two-value operation gives a value of its type. -/
  bin : ∀ ty o a b, (S.bin ty o a b).length = ty.bytes
  /-- A product is a value of 32 bits. -/
  matvec : ∀ rows x, (S.matvec rows x).length = DType.i32.bytes
  /-- A constant is a value of its type. -/
  const : ∀ ty xs, (S.const ty xs).length = ty.bytes
  /-- A selection is a value of its type. -/
  sel : ∀ ty m a b, (S.sel ty m a b).length = ty.bytes

/-- What a one-value operation of the vector slice does to one element. -/
def UnOp.elem : UnOp → Elem → Elem
  | .relu => Elem.relu
  | .requant k => Elem.requant k
  | .neg => fun x => -x
  | .abs => Elem.abs
  | .shl k => fun x => x <<< k
  | .addi c => fun x => x + BitVec.ofInt 32 c
  | .muli c => fun x => x * BitVec.ofInt 32 c
  | _ => id

/-- What a one-value operation of the rearrangement slice does to one word.
It moves elements, and so does the same to every word of a value. -/
def UnOp.move {lanes : Nat} : UnOp → Word lanes → Word lanes
  | .shift k => Word.shift k
  | .rotate k => Word.rotate k
  | .reverse => Word.reverse
  | .broadcast j => Word.broadcast j
  | .permute table => Word.permute table
  | _ => id

/-- What a two-value operation does to one pair of elements. -/
def BinOp.elem : BinOp → Elem → Elem → Elem
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .max => Elem.max
  | .min => Elem.min
  | .and => (· &&& ·)
  | .or => (· ||| ·)
  | .xor => (· ^^^ ·)
  | .lt => Elem.lt

/-- Put the words `vs` into the row of words `ws`, from place `j` on. -/
def putAt {V : Type} : List V → Nat → List V → List V
  | ws, _, [] => ws
  | ws, j, v :: vs => putAt (ws.set j v) (j + 1) vs

/-- The `n` words of the row `ws` from place `k` on. `none` if the row ends
before them. -/
def wordsAt {V : Type} (ws : List V) (k n : Nat) : Option (List V) :=
  if k + n ≤ ws.length then some ((ws.drop k).take n) else none

/-- The operations on real words. -/
def wordSem (lanes : Nat) : Sem (Word lanes) where
  un ty op a :=
    if op.kind = .sxm then List.map op.move (Value.fit ty.bytes a)
    else Value.mapElems ty.bytes (op.out ty).bytes op.elem a
  bin ty op a b := Value.zipElems ty.bytes op.elem a b
  zero := Word.zero
  matvec := Value.matvec
  const := Value.ofInts
  sel ty := Value.sel ty.bytes

end Tau
