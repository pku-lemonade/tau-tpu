import Tau.Isa.Value

/-!
# Elements, bytes and values

A slice computes with elements of 32 bits, and a value holds each element as
bytes, one in each of its words (`Tau.Isa.Value`). The facts here say that
nothing is lost between the two: an element made of up to four bytes has
those bytes, and a value of up to four words is the value with its own
elements. The proofs about operations on values rest on them
(`Tau.Proofs.Check.Simplify`).

The facts about bytes are proved bit by bit: two bit vectors are equal if
every bit is (`BitVec.eq_of_getLsbD_eq`).

Terms to look up: *little-endian*, *sign extension*.
-/

namespace Tau.Elem

/-! ## Elements and their bytes -/

theorem byte_signExtend (b : Lane) : byte (b.signExtend 32) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h32 : i < 32 := by omega
  simp [byte, hi, h32, BitVec.getElem_signExtend, BitVec.getLsbD_eq_getElem]

theorem byte_zero_cons (r : Elem) (b : Lane) : byte ((r <<< 8) ||| b.setWidth 32) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [byte]

theorem byte_succ_cons (r : Elem) (b : Lane) (k : Nat) (hk : k < 3) :
    byte ((r <<< 8) ||| b.setWidth 32) (k + 1) = byte r k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : 8 * (k + 1) + i < 32 := by omega
  have h2 : ¬ 8 * (k + 1) + i < 8 := by omega
  have h3 : 8 * (k + 1) + i - 8 = 8 * k + i := by omega
  have h4 : b.getLsbD (8 * (k + 1) + i) = false := BitVec.getLsbD_of_ge b _ (by omega)
  have h5 : 8 * k + i < 32 := by omega
  simp [byte, h1, h2, h3, h4, h5, BitVec.getLsbD_eq_getElem]

/-- Byte `k` of the element whose bytes are `bs` is `bs[k]`, for up to four
bytes. -/
theorem byte_ofBytes (bs : List Lane) (k : Nat) (hlen : bs.length ≤ 4) (hk : k < bs.length) :
    byte (ofBytes bs) k = bs[k] := by
  -- Induction on the list. The last byte is extended with its sign
  -- (`byte_signExtend`). Any other is put below the rest shifted up by one
  -- byte (`byte_zero_cons`, `byte_succ_cons`).
  induction bs generalizing k with
  | nil => simp at hk
  | cons b rest ih =>
    cases rest with
    | nil =>
      have : k = 0 := by simp at hk; omega
      subst this
      simp [ofBytes, byte_signExtend]
    | cons c rest =>
      cases k with
      | zero => simp [ofBytes, byte_zero_cons]
      | succ k =>
        simp only [ofBytes, List.length_cons] at hlen hk ⊢
        rw [byte_succ_cons _ _ _ (by omega)]
        simpa using ih k (by simp; omega) (by simp; omega)

/-- An element made of `n` bytes is put together again from those bytes. -/
theorem refit_ofBytes (bs : List Lane) (hlen : bs.length ≤ 4) :
    refit bs.length (ofBytes bs) = ofBytes bs := by
  unfold refit
  congr 1
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [byte_ofBytes bs k hlen h1]

theorem ofBytes_zeros (n : Nat) : ofBytes (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => simp [ofBytes]
    | succ m =>
      rw [List.replicate_succ] at ih ⊢
      rw [List.replicate_succ, ofBytes, ih]
      · simp
      · simp

theorem refit_zero (n : Nat) : refit n 0 = 0 := by
  have hb : (List.range n).map (byte 0) = List.replicate n 0 := by
    apply List.ext_getElem <;> simp [byte]
  rw [refit, hb, ofBytes_zeros]

end Tau.Elem

namespace Tau

theorem DType.bytes_le (ty : DType) : ty.bytes ≤ 4 := by
  cases ty <;> simp [DType.bytes]

namespace Value

variable {lanes : Nat}

/-! ## Values and their elements -/

theorem length_fit (n : Nat) (v : Value lanes) : (fit n v).length = n := by
  simp [fit]

theorem length_ofElems (n : Nat) (f : Fin lanes → Elem) : (ofElems n f).length = n := by
  simp [ofElems]

/-- A value of `n` words is its own first `n` words. -/
theorem fit_of_length (n : Nat) (v : Value lanes) (h : v.length = n) : fit n v = v := by
  apply List.ext_getElem
  · simp [fit, h]
  · intro k h1 h2
    simp [fit, List.getElem?_eq_getElem h2]

/-- Element `i` of the value with the elements `f` is `f i`, put together
from its first `n` bytes. -/
theorem elem_ofElems (n : Nat) (f : Fin lanes → Elem) (i : Fin lanes) :
    (ofElems n f).elem i = Elem.refit n (f i) := by
  simp [elem, ofElems, Elem.refit, List.map_map, Function.comp_def]

/-- An element of a value of up to four words is put together again from its
own bytes. -/
theorem refit_elem (v : Value lanes) (i : Fin lanes) (h : v.length ≤ 4) :
    Elem.refit v.length (v.elem i) = v.elem i := by
  have := Elem.refit_ofBytes (v.map (·[i])) (by simpa using h)
  simpa [elem] using this

/-- A value of up to four words is the value with its own elements. -/
theorem ofElems_elem (v : Value lanes) (h : v.length ≤ 4) : ofElems v.length v.elem = v := by
  apply List.ext_getElem
  · simp [ofElems]
  · intro k h1 h2
    apply Vector.ext
    intro i hi
    simp only [ofElems, List.getElem_map, List.getElem_range, Vector.getElem_ofFn, elem]
    rw [Elem.byte_ofBytes _ k (by simpa using h) (by simpa using h2)]
    simp

end Value

end Tau
