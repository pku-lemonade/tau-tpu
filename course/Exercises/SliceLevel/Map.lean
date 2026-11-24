/-
Exercise file. Generated from Tau/Proofs/SliceLevel/Map.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/SliceLevel/Map.lean.
Build this file alone with:

    lake build Exercises.SliceLevel.Map
-/

import Tau.SliceLevel.Machine

/-!
# The machine does not look at its values

The machine moves words around and hands them to the operations in `Sem`. It
never inspects a word to decide what to do next: which slots are read, which
are written, and whether it traps depend only on the program.

This file states that precisely. Take two kinds of value, `V` and `W`, and a
function `f : V → W` that respects the operations (`Sem.Hom`). Then running the
machine on `V`-values and applying `f` to the final state gives the same result
as applying `f` to the starting state and running the machine on `W`-values.
That is `run_map`, and `execute_map` is the same fact for memory contents.

The checker's proof uses this with `V` the expressions, `W` the real words and
`f` the function that evaluates an expression.
-/

namespace Tau

variable {V W : Type}

/-- Apply `f` to every value in a slice. -/
def Slice.map (f : V → W) (sl : Slice V) : Slice W where
  words := sl.words.map f
  x := sl.x.map f
  acc := f sl.acc
  pipe := sl.pipe.map (Option.map (Prod.map id f))

/-- Apply `f` to every value in a machine state. -/
def State.map (f : V → W) (s : State V) : State W where
  time := s.time
  east := s.east.map (List.map (Option.map f))
  west := s.west.map (List.map (Option.map f))
  slices := s.slices.map (Slice.map f)

/-- Apply `f` to what a slice step returns. -/
def mapResult (f : V → W) (r : Slice V × Option (Track × V)) :
    Slice W × Option (Track × W) :=
  (r.1.map f, r.2.map (Prod.map id f))

theorem State.sample_map (f : V → W) (s : State V) (p : Nat) (tr : Track) :
    (s.map f).sample p tr = (s.sample p tr).map f := by
  sorry

theorem exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (kind : Kind) (rd : Track → Option V) (rd' : Track → Option W)
    (hrd : ∀ tr, rd' tr = (rd tr).map f) (sl : Slice V) (i : Instr) :
    exec T cfg kind rd' (sl.map f) i = (exec S cfg kind rd sl i).map (mapResult f) := by
  sorry

theorem shiftPipe_map (f : V → W) (sl : Slice V) (r : Option (Track × V)) :
    shiftPipe (sl.map f) (r.map (Prod.map id f)) = mapResult f (shiftPipe sl r) := by
  sorry

theorem stepSlice_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (s : State V) (p : Nat) (sl : Slice V) :
    stepSlice T cfg prog (s.map f) p (sl.map f) =
      (stepSlice S cfg prog s p sl).map (mapResult f) := by
  sorry

theorem stepSlices_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (s : State V) (p : Nat) (sls : List (Slice V)) :
    stepSlices T cfg prog (s.map f) p (sls.map (Slice.map f)) =
      (stepSlices S cfg prog s p sls).map (List.map (mapResult f)) := by
  sorry

theorem inject_map (f : V → W) (outs : List (Option (Track × V))) (d : Dir) (k p : Nat) :
    inject (outs.map (Option.map (Prod.map id f))) d k p = (inject outs d k p).map f := by
  sorry

theorem advanceRow_map (f : V → W) (outs : List (Option (Track × V))) (d : Dir) (k : Nat)
    (row : List (Option V)) :
    advanceRow (outs.map (Option.map (Prod.map id f))) d k (row.map (Option.map f)) =
      (advanceRow outs d k row).map (Option.map f) := by
  sorry

theorem advance_map (f : V → W) (outs : List (Option (Track × V))) (d : Dir) (k : Nat)
    (rows : List (List (Option V))) :
    advance (outs.map (Option.map (Prod.map id f))) d k (rows.map (List.map (Option.map f))) =
      (advance outs d k rows).map (List.map (Option.map f)) := by
  sorry

/-- One cycle commutes with applying `f`. -/
theorem step_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (s : State V) :
    step T cfg prog (s.map f) = (step S cfg prog s).map (State.map f) := by
  sorry

/-- Any number of cycles commutes with applying `f`. -/
theorem run_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (n : Nat) (s : State V) :
    run T cfg prog n (s.map f) = (run S cfg prog n s).map (State.map f) := by
  sorry

theorem State.init_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (image : List (List V)) :
    State.init T cfg (image.map (List.map f)) = (State.init S cfg image).map f := by
  sorry

theorem State.memory_map (f : V → W) (s : State V) :
    (s.map f).memory = s.memory.map (List.map f) := by
  sorry

/-- Running a program on a mapped memory image gives the mapped result, and
traps in exactly the same cases. -/
theorem execute_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (prog : Program) (n : Nat) (image : List (List V)) :
    execute T cfg prog n (image.map (List.map f)) =
      (execute S cfg prog n image).map (List.map (List.map f)) := by
  sorry

end Tau
