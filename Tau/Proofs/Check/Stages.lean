import Tau.Check.Stages
import Tau.Proofs.Check.Sound
import Tau.Proofs.IR.Placed

/-!
# The per-pass checks are sound

Two results, one for each new check in `Tau/Check/Stages.lean`.

* `checkKernels_sound`: two kernels the check accepts compute the same
  buffers, on every input.
* `checkPlaced_sound`: a placed program the check accepts, run from any
  buffer contents, ends with the buffers the kernel computes.

The proofs follow `check_sound`. The new ingredient is `Placed.execute_map`
(`Tau/Proofs/IR/Placed.lean`): like the machine and like a kernel, a placed
program does not look at its values.
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
  -- Split on the two symbolic runs. Each kernel on real buffers is its
  -- symbolic run evaluated (`Kernel.run_of_exprs`), and the two evaluated
  -- results agree (`denote_of_simp_eq`).
  unfold checkKernels at h
  cases ha : kernelExprs k (bufs.map List.length) with
  | none => simp [ha] at h
  | some a =>
    cases hb : kernelExprs k' (bufs.map List.length) with
    | none => simp [ha, hb] at h
    | some b =>
      simp only [ha, hb, beq_iff_eq] at h
      refine ⟨_, Kernel.run_of_exprs S k bufs fill a ha, ?_⟩
      rw [Kernel.run_of_exprs S k' bufs fill b hb, denote_of_simp_eq S hS bufs fill a b h]

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
  -- The proof of `check_sound` again, with `Placed.execute_map` in place of
  -- `execute_map`.
  let f := Expr.denote S bufs fill
  have hf : exprSem.Hom S f := denote_hom S bufs fill
  unfold checkPlaced at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  unfold placedExprs at h
  cases hx : pl.execute exprSem (image pl.map pl.memSizes Expr.init .fill) with
  | none => simp [hx] at h
  | some memE =>
    cases hk : kernelExprs k (bufs.map List.length) with
    | none => simp [hx, hk] at h
    | some outE =>
      simp only [hx, hk, beq_iff_eq] at h
      have himg : pl.image bufs fill =
          (image pl.map pl.memSizes Expr.init .fill).map (List.map f) := by
        rw [image_map]
        rfl
      have hrun : pl.execute S (pl.image bufs fill) = some (memE.map (List.map f)) := by
        rw [himg, Placed.execute_map exprSem S f hf, hx]
        rfl
      refine ⟨_, _, hrun, Kernel.run_of_exprs S k bufs fill outE hk, ?_⟩
      have hfill : f .fill = fill := rfl
      rw [← hfill, extract_map f pl.map memE .fill]
      exact denote_of_simp_eq S hS bufs fill _ _ h

end Tau
