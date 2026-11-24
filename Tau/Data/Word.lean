/-!
# Lanes and words

A *lane* carries one 32-bit signed integer. A *word* is a fixed number of lanes
side by side. A word is what one stream slot holds, and what one memory address
holds.

Arithmetic wraps around on overflow, as it does in hardware.

Terms to look up: *two's complement*, *SIMD*, *saturating arithmetic*,
*arithmetic shift*.
-/

namespace Tau

/-- One lane: a 32-bit value, read as a signed integer. -/
abbrev Lane := BitVec 32

/-- A word: `lanes` lanes side by side. -/
abbrev Word (lanes : Nat) := Vector Lane lanes

namespace Lane

/-- Negative values become zero. -/
def relu (a : Lane) : Lane := if a.slt 0 then 0 else a

/-- The larger of two signed values. -/
def max (a b : Lane) : Lane := if a.slt b then b else a

/-- The smaller of two signed values. -/
def min (a b : Lane) : Lane := if a.slt b then a else b

/-- Scale a wide value back to 8 bits: divide by `2 ^ k`, rounding down, then
clamp to the range -128 to 127. -/
def requant (k : Nat) (a : Lane) : Lane :=
  let s := a.sshiftRight k
  if s.slt (-128) then -128 else if (127 : Lane).slt s then 127 else s

end Lane

namespace Word

variable {lanes : Nat}

/-- The word with every lane zero. -/
def zero : Word lanes := Vector.replicate lanes 0

/-- Build a word from signed integers. Missing lanes are zero. -/
def ofInts (xs : List Int) : Word lanes :=
  Vector.ofFn fun i : Fin lanes => BitVec.ofInt 32 (xs[i.val]?.getD 0)

/-- The lanes of a word as signed integers. -/
def toInts (w : Word lanes) : List Int := w.toList.map BitVec.toInt

/-- Move every lane up by `k` places. The lowest `k` lanes become zero. -/
def shift (k : Nat) (w : Word lanes) : Word lanes :=
  Vector.ofFn fun i : Fin lanes => if k ≤ i.val then w[i.val - k]?.getD 0 else 0

/-- Rotate the lanes by `k` places: lane `i` takes the value of lane `i + k`,
wrapping around. -/
def rotate (k : Nat) (w : Word lanes) : Word lanes :=
  Vector.ofFn fun i : Fin lanes => w[(i.val + k) % lanes]?.getD 0

/-- One step of a matrix-vector product: add lane `j` of `x`, times `w`, to
`acc`. With `w` a column of a matrix, doing this for every column gives the
product of the matrix with `x`. -/
def mac (j : Nat) (acc x w : Word lanes) : Word lanes :=
  Vector.zipWith (fun a c => a + x[j]?.getD 0 * c) acc w

end Word

end Tau
