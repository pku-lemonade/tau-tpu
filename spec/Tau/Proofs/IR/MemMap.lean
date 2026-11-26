import Tau.IR.MemMap
import Tau.Proofs.Isa.Event

/-!
# The memory map does not look at its values

`image` and `extract` only move values around. So applying a function `f` to
every value commutes with both: `image_map` and `extract_map`. The same holds
for turning issues into events: `Issue.event_map`.

The soundness proofs in `spec/Tau/Proofs/Check/` use these to carry a statement
about memory contents over to a statement about buffers.
-/

namespace Tau

variable {V W : Type}

theorem image_map (f : V → W) (map : MemMap) (memSizes : List Nat) (word : Nat → Nat → V)
    (fill : V) :
    (image map memSizes word fill).map (List.map f) =
      image map memSizes (fun b k => f (word b k)) (f fill) := by
  -- Both sides are a map over positions of a map over addresses. Fuse the
  -- maps (`List.map_map`) and compare the functions (`List.map_congr_left`).
  unfold image
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp, List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp]
  cases MemMap.findFrom p a 0 map with
  | none => rfl
  | some bk => rfl

theorem extract_map (f : V → W) (map : MemMap) (mem : List (List V)) (fill : V) :
    extract map (mem.map (List.map f)) (f fill) = (extract map mem fill).map (List.map f) := by
  unfold extract
  simp only [List.map_map]
  apply List.map_congr_left
  intro pl _
  simp only [Function.comp, List.map_map]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp, List.getElem?_map]
  cases mem[pl.slice]? with
  | none => rfl
  | some l =>
    simp only [Option.map_some, Option.getD_some, List.getElem?_map]
    cases l[pl.base + k]? <;> rfl

theorem Issue.event_map (f : V → W) (map : MemMap) (x : Issue V) :
    (x.map f).event map = (x.event map).map (Event.map f) := by
  unfold Issue.event Issue.map
  cases x.addr with
  | none => rfl
  | some a =>
    simp only
    cases MemMap.findFrom x.slice a 0 map <;> rfl

/-- Turning mapped issues into events gives the mapped events. -/
theorem filterMap_event_map (f : V → W) (map : MemMap) (l : List (Issue V)) :
    (l.map (Issue.map f)).filterMap (Issue.event map) =
      (l.filterMap (Issue.event map)).map (Event.map f) := by
  rw [List.filterMap_map, List.map_filterMap]
  apply filterMap_congr
  intro x _
  exact Issue.event_map f map x

end Tau
