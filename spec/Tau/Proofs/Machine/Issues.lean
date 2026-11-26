import Tau.Machine.Issues
import Tau.Proofs.Machine.SliceLevel
import Tau.Proofs.Isa.Event

/-!
# When the machine issues a word does not depend on its values

`Tau.Proofs.Machine.SliceLevel` shows that a function `f` that respects the
operations commutes with a run. This file shows the same for what the run
issues: the cycles, slices and addresses are the same, and the words are the
words of the other run with `f` applied.

The main result is `issues_map`. The checks use it to turn the timeline of
one run on expressions into the timeline of every run on real words.
-/

namespace Tau

variable {V W : Type}

theorem issued_map (f : V → W) (rd : Stream → Option V) (rd' : Stream → Option W)
    (hrd : ∀ tr, rd' tr = (rd tr).map f) (i : Instr) (r : Option (Stream × V)) :
    issued rd' i (r.map (Prod.map id f)) = (issued rd i r).map (Prod.map id f) := by
  cases r with
  | some tv => rfl
  | none =>
    cases i <;> simp only [issued, Option.map_none]
    case write src addr =>
      rw [hrd]
      cases rd src <;> rfl

theorem State.issue_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (s : State V) (p : Nat) :
    (s.map f).issue T cfg prog p = (s.issue S cfg prog p).map (Issue.map f) := by
  -- The same instruction is due in both states. Its result in the mapped
  -- state is the mapped result (`exec_map`), and so is the word it issues
  -- (`issued_map`).
  unfold State.issue
  have ht : (s.map f).time = s.time := rfl
  have hs : (s.map f).slices = s.slices.map (Slice.map f) := rfl
  rw [ht, hs, List.getElem?_map]
  cases prog.dueAt p s.time with
  | nil => rfl
  | cons i rest =>
    cases rest with
    | cons j rest => rfl
    | nil =>
      cases cfg.kindAt p with
      | none => rfl
      | some kind =>
        cases s.slices[p]? with
        | none => rfl
        | some sl =>
          simp only [Option.map_some]
          rw [exec_map S T f h cfg kind (s.sample p) ((s.map f).sample p)
            (State.sample_map f s p) sl i]
          cases exec S cfg kind (s.sample p) sl i with
          | error k => rfl
          | ok r =>
            obtain ⟨sl', r⟩ := r
            simp only [Except.map, mapResult]
            rw [issued_map f (s.sample p) ((s.map f).sample p) (State.sample_map f s p)]
            cases issued (s.sample p) i r <;> rfl

theorem State.issues_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (s : State V) :
    (s.map f).issues T cfg prog = (s.issues S cfg prog).map (Issue.map f) := by
  unfold State.issues
  have hs : (s.map f).slices.length = s.slices.length := by simp [State.map]
  rw [hs, List.map_filterMap]
  apply filterMap_congr
  intro p _
  exact State.issue_map S T f h cfg prog s p

theorem issuesFrom_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (n : Nat) (s : State V) :
    issuesFrom T cfg prog n (s.map f) = (issuesFrom S cfg prog n s).map (Issue.map f) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [issuesFrom, State.issues_map S T f h, step_map S T f h, List.map_append]
    cases step S cfg prog s with
    | error e => rfl
    | ok s' => simp only [Except.map, ih]

/-- What a run on a mapped memory image issues is what the run on the image
issues, with the words mapped. -/
theorem issues_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (n : Nat) (image : List (List V)) :
    issues T cfg prog n (image.map (List.map f)) =
      (issues S cfg prog n image).map (Issue.map f) := by
  unfold issues
  rw [State.init_map S T f h, issuesFrom_map S T f h]

end Tau
