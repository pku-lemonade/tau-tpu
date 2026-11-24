/-
Exercise file. Generated from Tau/Proofs/Check/Stages.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/Check/Stages.lean.
Build this file alone with:

    lake build Exercises.Check.Stages
-/

import Tau.Check.Stages
import Tau.Proofs.Check.Sound

/-!
# The per-pass checks are sound

Two results, one for each new check in `Tau/Check/Stages.lean`.

* `checkKernels_sound`: two kernels the check accepts compute the same
  buffers, on every input.
* `checkPlaced_sound`: a placed program the check accepts, run from any
  buffer contents, ends with the buffers the kernel computes.

The proofs follow `check_sound`. The new ingredient is `Placed.execute_map`:
like the machine and like a kernel, a placed program does not look at its
values.
-/

namespace Tau

variable {V W : Type}

/-! ## Kernel against kernel -/

/-- **Soundness of `checkKernels`.** Two kernels it accepts compute the same
buffers on every input, and neither fails. -/
theorem checkKernels_sound (S : Sem V) (hS : S.Lawful) (k k' : Kernel)
    (bufs : List (List V)) (fill : V)
    (h : checkKernels k k' (bufs.map List.length) = true) :
    ∃ out, k.run S bufs = some out ∧ k'.run S bufs = some out := by
  sorry

/-! ## A placed program does not look at its values -/

/-- Apply `f` to every value in a placed state. -/
def PState.map (f : V → W) (st : PState V) : PState W where
  vars := st.vars.map (Prod.map id f)
  slices := st.slices.map (Slice.map f)

theorem PInstr.exec_map (S : Sem V) (T : Sem W) (f : V → W) (h : S.Hom T f) (kind : Kind)
    (vars : List (Var × V)) (sl : Slice V) (i : PInstr) :
    i.exec T kind (vars.map (Prod.map id f)) (sl.map f) =
      (i.exec S kind vars sl).map fun r => (r.1.map (Prod.map id f), r.2.map f) := by
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

/-! ## Placed program against kernel -/

/-- **Soundness of `checkPlaced`.** If it accepts the placed program `pl` for
the kernel `k`, then on any buffer contents the instructions of `pl`, carried
out in order, end with the buffers that `k` computes. -/
theorem checkPlaced_sound (S : Sem V) (hS : S.Lawful) (k : Kernel) (pl : Placed)
    (bufs : List (List V)) (fill : V)
    (h : checkPlaced k (bufs.map List.length) pl = true) :
    ∃ mem out,
      pl.execute S (pl.image bufs fill) = some mem ∧
      k.run S bufs = some out ∧
      extract pl.map mem fill = out := by
  sorry

end Tau
