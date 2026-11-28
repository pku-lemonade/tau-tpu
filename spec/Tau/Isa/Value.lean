import Tau.Isa.Word

/-!
# Values

A *value* is 1, 2 or 4 words: word `k` holds byte `k` of every element, the
low byte first. So a value of type `i32` on a machine of 8 lanes is four
words, and lane `i` of the four holds the four bytes of element `i`.

A buffer and a stream hold words. Everything that computes takes the
elements of its values out of their words (`Value.elem`), computes with them
in 32 bits, and puts the low bytes of the results back (`Value.ofElems`).

Terms to look up: *little-endian*, *bit plane*, *structure of arrays*.

Docs: Machine 1 (`docs/`).
-/

namespace Tau

namespace Elem

/-- Byte `k` of an element, counted from the low byte. -/
def byte (x : Elem) (k : Nat) : Lane := (x >>> (8 * k)).setWidth 8

/-- The element whose bytes are `bs`, the low byte first. The last of them
gives the sign. -/
def ofBytes : List Lane → Elem
  | [] => 0
  | [b] => b.signExtend 32
  | b :: bs => (ofBytes bs <<< 8) ||| b.setWidth 32

/-- An element put together from the first `n` of its own bytes. -/
def refit (n : Nat) (x : Elem) : Elem := ofBytes ((List.range n).map x.byte)

end Elem

/-- A value: its words, the low byte of every element first. -/
abbrev Value (lanes : Nat) := List (Word lanes)

namespace Value

variable {lanes : Nat}

/-- The first `n` words of a value. A word it does not have is zero. -/
def fit (n : Nat) (v : Value lanes) : Value lanes :=
  (List.range n).map fun k => v[k]?.getD Word.zero

/-- Element `i` of a value: its bytes are lane `i` of each word. -/
def elem (v : Value lanes) (i : Fin lanes) : Elem := Elem.ofBytes (v.map (·[i]))

/-- The value of `n` words whose element `i` is `f i`. -/
def ofElems (n : Nat) (f : Fin lanes → Elem) : Value lanes :=
  (List.range n).map fun k => Vector.ofFn fun i => (f i).byte k

/-- The value of type `ty` with the given elements. Missing elements are
zero. -/
def ofInts (ty : DType) (xs : List Int) : Value lanes :=
  ofElems ty.bytes fun i => BitVec.ofInt 32 (xs[i.val]?.getD 0)

/-- The elements of a value as signed integers. -/
def toInts (v : Value lanes) : List Int :=
  (List.finRange lanes).map fun i => (v.elem i).toInt

/-- Apply `f` to every element of a value of `n` words, and keep `m` words of
the result. -/
def mapElems (n m : Nat) (f : Elem → Elem) (v : Value lanes) : Value lanes :=
  ofElems m fun i => f ((v.fit n).elem i)

/-- Apply `f` to the elements of two values of `n` words, pair by pair. -/
def zipElems (n : Nat) (f : Elem → Elem → Elem) (a b : Value lanes) : Value lanes :=
  ofElems n fun i => f ((a.fit n).elem i) ((b.fit n).elem i)

/-- Element by element: the element of `a` where the element of `m` is not
zero, and the element of `b` elsewhere. -/
def sel (n : Nat) (m a b : Value lanes) : Value lanes :=
  ofElems n fun i => Elem.sel ((m.fit n).elem i) ((a.fit n).elem i) ((b.fit n).elem i)

/-- The product of a matrix with the word `x`, a value of 32 bits. Each word
of `rows` holds the weights of one element of the result: element `i` is the
dot product of `rows[i]` with `x`, and zero if there is no such row. -/
def matvec (rows : List (Word lanes)) (x : Word lanes) : Value lanes :=
  ofElems DType.i32.bytes fun i =>
    match rows[i.val]? with
    | some w => w.dot x
    | none => 0

end Value

end Tau
