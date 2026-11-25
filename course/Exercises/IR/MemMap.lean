/-
Exercise file. Generated from Tau/Proofs/IR/MemMap.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/IR/MemMap.lean.
Build this file alone with:

    lake build Exercises.IR.MemMap
-/

import Tau.IR.MemMap

/-!
# The memory map does not look at its values

`image` and `extract` only move values around. So applying a function `f` to
every value commutes with both: `image_map` and `extract_map`.

The soundness proofs in `Tau/Proofs/Check/` use these to carry a statement
about memory contents over to a statement about buffers.
-/

namespace Tau

variable {V W : Type}

theorem image_map (f : V → W) (map : MemMap) (memSizes : List Nat) (word : Nat → Nat → V)
    (fill : V) :
    (image map memSizes word fill).map (List.map f) =
      image map memSizes (fun b k => f (word b k)) (f fill) := by
  -- Outline of one proof:
  -- Both sides are a map over positions of a map over addresses. Fuse the
  -- maps (`List.map_map`) and compare the functions (`List.map_congr_left`).
  sorry

theorem extract_map (f : V → W) (map : MemMap) (mem : List (List V)) (fill : V) :
    extract map (mem.map (List.map f)) (f fill) = (extract map mem fill).map (List.map f) := by
  sorry

end Tau
