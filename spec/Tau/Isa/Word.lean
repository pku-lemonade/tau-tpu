/-!
# Lanes, words and elements

A *lane* carries one byte. A *word* is a fixed number of lanes side by side. A
word is what one stream slot holds, and what one memory address holds.

A program computes with *values*: for every lane one signed integer of 8, 16
or 32 bits, an *element* of the value. The type of a value, `DType`, is the
size of its elements. `Tau.Isa.Value` says how a value is held in words.

A slice computes with elements of 32 bits (`Elem`). An element of a shorter
type is extended to 32 bits with its sign, and of a result the low bytes are
kept. So arithmetic wraps around on overflow, as it does in hardware.

Terms to look up: *two's complement*, *sign extension*, *SIMD*,
*saturating arithmetic*, *arithmetic shift*.

Docs: Machine 1 (`docs/`).
-/

namespace Tau

/-- One lane: a byte. -/
abbrev Lane := BitVec 8

/-- A word: `lanes` lanes side by side. -/
abbrev Word (lanes : Nat) := Vector Lane lanes

/-- The type of a value: how many bits each of its elements has. -/
inductive DType where
  /-- Signed integers of 8 bits: one word. -/
  | i8
  /-- Signed integers of 16 bits: two words. -/
  | i16
  /-- Signed integers of 32 bits: four words. -/
  | i32
  deriving DecidableEq, Repr

/-- The number of bytes of an element, which is the number of words of a
value. -/
def DType.bytes : DType → Nat
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4

/-- The name of a type, as Formats writes it. -/
def DType.name : DType → String
  | .i8 => "i8"
  | .i16 => "i16"
  | .i32 => "i32"

/-- An element of a value as a slice computes with it: 32 bits, read as a
signed integer. -/
abbrev Elem := BitVec 32

namespace Elem

/-- Negative values become zero. -/
def relu (a : Elem) : Elem := if a.slt 0 then 0 else a

/-- The larger of two signed values. -/
def max (a b : Elem) : Elem := if a.slt b then b else a

/-- The smaller of two signed values. -/
def min (a b : Elem) : Elem := if a.slt b then a else b

/-- The absolute value. The most negative value stays as it is. -/
def abs (a : Elem) : Elem := if a.slt 0 then -a else a

/-- 1 if `a` is less than `b` as signed values, and 0 otherwise. -/
def lt (a b : Elem) : Elem := if a.slt b then 1 else 0

/-- `a` if the mask `m` is not zero, and `b` otherwise. -/
def sel (m a b : Elem) : Elem := if m = 0 then b else a

/-- Scale a wide value back to 8 bits: divide by `2 ^ k`, rounding down, then
clamp to the range -128 to 127. -/
def requant (k : Nat) (a : Elem) : Elem :=
  let s := a.sshiftRight k
  if s.slt (-128) then -128 else if (127 : Elem).slt s then 127 else s

end Elem

namespace Word

variable {lanes : Nat}

/-- The word with every lane zero. -/
def zero : Word lanes := Vector.replicate lanes 0

/-- Build a word from signed integers, one byte each. Missing lanes are
zero. -/
def ofInts (xs : List Int) : Word lanes :=
  Vector.ofFn fun i : Fin lanes => BitVec.ofInt 8 (xs[i.val]?.getD 0)

/-- The lanes of a word as signed integers. -/
def toInts (w : Word lanes) : List Int := w.toList.map BitVec.toInt

/-- Move every lane up by `k` places. The lowest `k` lanes become zero. -/
def shift (k : Nat) (w : Word lanes) : Word lanes :=
  Vector.ofFn fun i : Fin lanes => if k ≤ i.val then w[i.val - k]?.getD 0 else 0

/-- Rotate the lanes by `k` places: lane `i` takes the value of lane `i + k`,
wrapping around. -/
def rotate (k : Nat) (w : Word lanes) : Word lanes :=
  Vector.ofFn fun i : Fin lanes => w[(i.val + k) % lanes]?.getD 0

/-- The lanes in the opposite order. -/
def reverse (w : Word lanes) : Word lanes :=
  Vector.ofFn fun i : Fin lanes => w[lanes - 1 - i.val]?.getD 0

/-- Every lane takes the value of lane `j`. -/
def broadcast (j : Nat) (w : Word lanes) : Word lanes :=
  Vector.replicate lanes (w[j]?.getD 0)

/-- Lane `i` takes the value of lane `table[i]`. A lane with no entry in the
table, or an entry that names no lane, becomes zero. -/
def permute (table : List Nat) (w : Word lanes) : Word lanes :=
  Vector.ofFn fun i : Fin lanes =>
    match table[i.val]? with
    | some k => w[k]?.getD 0
    | none => 0

/-- The dot product of two words: the sum, over the lanes, of the lane of `w`
times the lane of `x`, each read as a signed integer and the sum taken in 32
bits. -/
def dot (w x : Word lanes) : Elem :=
  (List.finRange lanes).foldl (fun acc j => acc + w[j].signExtend 32 * x[j].signExtend 32) 0

end Word

end Tau
