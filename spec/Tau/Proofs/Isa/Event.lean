/-!
# Events: a fact about lists

The words a slice issues and the events of a compiled program are both picked
out of a list with `List.filterMap` (`Tau.Machine.Issues`, `Tau.IR.Compiled`).
This file has the one lemma about it that the proofs about them need and the
standard library does not have under a stable name.
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

end Tau
