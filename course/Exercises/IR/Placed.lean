/-
Exercise file. Generated from Tau/Proofs/IR/Placed.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/IR/Placed.lean.
Build this file alone with:

    lake build Exercises.IR.Placed
-/

import Tau.IR.Placed
import Tau.Proofs.SliceLevel.Map
import Tau.Proofs.IR.Map

/-!
# A placed program does not look at its values

The same fact as `Tau/Proofs/SliceLevel/Map.lean` and `Tau/Proofs/IR/Map.lean`,
for the placed form: a function `f` that respects the operations commutes
with carrying out a placed program. Whether the program fails depends only on
the program and the memory sizes, never on the values.

The main result is `Placed.execute_map`. `checkPlaced_sound`
(`Tau/Proofs/Check/Stages.lean`) uses it.
-/

namespace Tau

variable {V W : Type}

/-- Apply `f` to every value in a placed state. -/
def PState.map (f : V → W) (st : PState V) : PState W where
  vars := st.vars.map (Prod.map id f)
  slices := st.slices.map (Slice.map f)

theorem PInstr.exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (kind : Kind)
    (vars : List (Var × V)) (sl : Slice V) (i : PInstr) :
    i.exec T kind (vars.map (Prod.map id f)) (sl.map f) =
      (i.exec S kind vars sl).map fun r => (r.1.map (Prod.map id f), r.2.map f) := by
  -- Outline of one proof:
  -- One case per instruction, as in `exec_map` for the machine: unfold, move
  -- the map out of each lookup (`lookup_map`), split on each check and on
  -- what each lookup found.
  sorry

theorem PState.step_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (st : PState V) (p : Nat) (i : PInstr) :
    (st.map f).step T cfg p i = (st.step S cfg p i).map (PState.map f) := by
  sorry

theorem PState.run_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (cfg : Config)
    (st : PState V) (instrs : List (Nat × PInstr)) :
    PState.run T cfg (st.map f) instrs = (PState.run S cfg st instrs).map (PState.map f) := by
  sorry

/-- Running a placed program on a mapped memory image gives the mapped
result, and fails in exactly the same cases. -/
theorem Placed.execute_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (pl : Placed)
    (image : List (List V)) :
    pl.execute T (image.map (List.map f)) =
      (pl.execute S image).map (List.map (List.map f)) := by
  sorry

end Tau
