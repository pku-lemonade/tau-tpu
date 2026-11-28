import Tau.Isa.Op

/-!
# Facts about lists

The words a slice issues and the events of a compiled program are both picked
out of a list with `List.filterMap` (`Tau.Machine.Issues`, `Tau.IR.Compiled`).
This file has the one lemma about it that the proofs about them need and the
standard library does not have under a stable name. It also has the two facts
about rows of words that the machine and the kernels share: taking words out
of a row and putting words into one commute with applying a function to
every word.
-/

namespace Tau

/-- `filterMap` with two functions that agree on the list gives one result. -/
theorem filterMap_congr {α β : Type} {f g : α → Option β} {l : List α}
    (h : ∀ x, x ∈ l → f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    have ha : f a = g a := h a (List.mem_cons_self ..)
    have hr : rest.filterMap f = rest.filterMap g :=
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.filterMap_cons, ha, hr]

theorem putAt_map {V W : Type} (f : V → W) (ws : List V) (j : Nat) (vs : List V) :
    putAt (ws.map f) j (vs.map f) = (putAt ws j vs).map f := by
  induction vs generalizing ws j with
  | nil => rfl
  | cons v vs ih => simp only [List.map_cons, putAt, ← List.map_set, ih]

theorem wordsAt_map {V W : Type} (f : V → W) (ws : List V) (k n : Nat) :
    wordsAt (ws.map f) k n = (wordsAt ws k n).map (List.map f) := by
  simp only [wordsAt, List.length_map]
  split <;> simp [List.map_take, List.map_drop]

end Tau
