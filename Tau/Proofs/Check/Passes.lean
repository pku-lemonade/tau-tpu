import Tau.Check.Passes
import Tau.Proofs.Check.Sound
import Tau.Proofs.IR.Placed

/-!
# The per-pass checks are sound

One theorem for each check in `Tau/Check/Passes.lean`. Each says: if the
check accepts, the output of the pass computes what its input computes, on
every buffer contents.

| Pass | Theorem |
|---|---|
| `tau-simplify`, `tau-unroll` | `checkKernels_sound` |
| `tau-place` | `checkPlaced_sound` |
| `tau-schedule` | `checkScheduled_sound` |
| `tau-route` | `checkRouted_sound` |

`passes_sound` chains the five: if every pass is accepted, the compiled
program computes the kernel. That is the conclusion of `check_sound`, reached
one pass at a time.

The proofs follow `check_sound`. Each side of a check is a run on
expressions, and a run on real buffers is that run evaluated:
`Kernel.run_of_exprs` for a kernel, `execute_of_exprs` for a compiled program,
and `Placed.execute_of_exprs`, proved here, for a placed program.
-/

namespace Tau

variable {V W : Type}

/-- If a placed program run on expressions ends with the table `m`, then run
on real buffers it can be carried out, and the buffers it ends with are `m`
evaluated. -/
theorem Placed.execute_of_exprs (S : Sem V) (pl : Placed) (bufs : List (List V)) (fill : V)
    (m : List (List Expr)) (h : placedExprs pl = some m) :
    ∃ mem,
      pl.execute S (pl.image bufs fill) = some mem ∧
      extract pl.map mem fill = m.map (List.map (Expr.denote S bufs fill)) := by
  -- The proof of `execute_of_exprs` again, with `Placed.execute_map` in place
  -- of `execute_map`.
  let f := Expr.denote S bufs fill
  have hf : exprSem.Hom S f := denote_hom S bufs fill
  unfold placedExprs at h
  cases hx : pl.execute exprSem (Tau.image pl.map pl.memSizes Expr.init .fill) with
  | none => simp [hx] at h
  | some memE =>
    simp only [hx, Option.some.injEq] at h
    have himg : pl.image bufs fill =
        (Tau.image pl.map pl.memSizes Expr.init .fill).map (List.map f) := by
      rw [image_map]
      rfl
    refine ⟨memE.map (List.map f), ?_, ?_⟩
    · rw [himg, Placed.execute_map exprSem S f hf, hx]
      rfl
    · have hext := extract_map f pl.map memE .fill
      rw [h] at hext
      exact hext

/-! ## `tau-simplify` and `tau-unroll`: kernel to kernel -/

/-- **Soundness of `checkKernels`.** Two kernels it accepts compute the same
buffers on every input, and neither fails. -/
theorem checkKernels_sound (S : Sem V) (hS : S.Lawful) (k k' : Kernel)
    (bufs : List (List V)) (fill : V)
    (h : checkKernels k k' (bufs.map List.length) = true) :
    ∃ out, k.run S bufs = some out ∧ k'.run S bufs = some out := by
  -- Split on the two symbolic runs. Each kernel on real buffers is its
  -- symbolic run evaluated (`Kernel.run_of_exprs`), and the two evaluated
  -- results agree (`denote_of_sameExprs`).
  unfold checkKernels at h
  cases ha : kernelExprs k (bufs.map List.length) with
  | none => simp [ha] at h
  | some a =>
    cases hb : kernelExprs k' (bufs.map List.length) with
    | none => simp [ha, hb] at h
    | some b =>
      simp only [ha, hb] at h
      refine ⟨_, Kernel.run_of_exprs S k bufs fill a ha, ?_⟩
      rw [Kernel.run_of_exprs S k' bufs fill b hb, denote_of_sameExprs S hS bufs fill a b h]

/-! ## `tau-place`: kernel to placed program -/

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
  -- The proof of `check_sound` again, with `Placed.execute_of_exprs` in
  -- place of `execute_of_exprs`.
  unfold checkPlaced at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  cases hk : kernelExprs k (bufs.map List.length) with
  | none => simp [hk] at h
  | some a =>
    cases hp : placedExprs pl with
    | none => simp [hk, hp] at h
    | some b =>
      simp only [hk, hp] at h
      obtain ⟨mem, hrun, hx⟩ := Placed.execute_of_exprs S pl bufs fill b hp
      refine ⟨mem, _, hrun, Kernel.run_of_exprs S k bufs fill a hk, ?_⟩
      rw [hx]
      exact (denote_of_sameExprs S hS bufs fill a b h).symm

/-! ## `tau-schedule`: placed program to compiled program -/

/-- **Soundness of `checkScheduled`.** If it accepts the compiled program `c`
for the placed program `pl`, then on any buffer contents the machine runs `c`
without a trap and ends with the buffers that the instructions of `pl`,
carried out in order, end with. -/
theorem checkScheduled_sound (S : Sem V) (hS : S.Lawful) (pl : Placed) (c : Compiled)
    (bufs : List (List V)) (fill : V)
    (h : checkScheduled pl c = true) :
    ∃ mem mem',
      pl.execute S (pl.image bufs fill) = some mem ∧
      execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem' ∧
      extract c.map mem' fill = extract pl.map mem fill := by
  -- Split on the two symbolic runs. Each side on real buffers is its
  -- symbolic run evaluated (`Placed.execute_of_exprs`, `execute_of_exprs`),
  -- and the two evaluated tables agree (`denote_of_sameExprs`).
  unfold checkScheduled at h
  cases hp : placedExprs pl with
  | none => simp [hp] at h
  | some a =>
    cases hm : machineExprs c with
    | none => simp [hp, hm] at h
    | some b =>
      simp only [hp, hm] at h
      obtain ⟨mem, hrun, hx⟩ := Placed.execute_of_exprs S pl bufs fill a hp
      obtain ⟨mem', hrun', hx'⟩ := execute_of_exprs S c bufs fill b hm
      refine ⟨mem, mem', hrun, hrun', ?_⟩
      rw [hx, hx']
      exact (denote_of_sameExprs S hS bufs fill a b h).symm

/-! ## `tau-route`: compiled program to compiled program -/

/-- **Soundness of `checkRouted`.** If it accepts the compiled program `c'`
for the compiled program `c`, then on any buffer contents the machine runs
both without a trap and they end with the same buffers. -/
theorem checkRouted_sound (S : Sem V) (hS : S.Lawful) (c c' : Compiled)
    (bufs : List (List V)) (fill : V)
    (h : checkRouted c c' = true) :
    ∃ mem mem',
      execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem ∧
      execute S c'.cfg c'.prog c'.cycles (c'.image bufs fill) = .ok mem' ∧
      extract c'.map mem' fill = extract c.map mem fill := by
  -- The proof of `checkScheduled_sound` again, with `execute_of_exprs` on
  -- both sides.
  unfold checkRouted at h
  cases ha : machineExprs c with
  | none => simp [ha] at h
  | some a =>
    cases hb : machineExprs c' with
    | none => simp [ha, hb] at h
    | some b =>
      simp only [ha, hb] at h
      obtain ⟨mem, hrun, hx⟩ := execute_of_exprs S c bufs fill a ha
      obtain ⟨mem', hrun', hx'⟩ := execute_of_exprs S c' bufs fill b hb
      refine ⟨mem, mem', hrun, hrun', ?_⟩
      rw [hx, hx']
      exact (denote_of_sameExprs S hS bufs fill a b h).symm

/-! ## All five passes -/

/-- **The passes together.** Let `k₁` be the output of `tau-simplify` on the
kernel `k`, `k₂` the output of `tau-unroll`, `pl` the output of `tau-place`,
`c₁` the output of `tau-schedule` and `c` the output of `tau-route`. If every
pass's check accepts, then on any buffer contents the machine runs `c`
without a trap and ends with the buffers that `k` computes. -/
theorem passes_sound (S : Sem V) (hS : S.Lawful) (k k₁ k₂ : Kernel) (pl : Placed)
    (c₁ c : Compiled) (bufs : List (List V)) (fill : V)
    (hsimplify : checkKernels k k₁ (bufs.map List.length) = true)
    (hunroll : checkKernels k₁ k₂ (bufs.map List.length) = true)
    (hplace : checkPlaced k₂ (bufs.map List.length) pl = true)
    (hschedule : checkScheduled pl c₁ = true)
    (hroute : checkRouted c₁ c = true) :
    ∃ mem out,
      execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem ∧
      k.run S bufs = some out ∧
      extract c.map mem fill = out := by
  -- Take the conclusion of each soundness theorem. Two neighbouring
  -- theorems speak about the same run in the middle, so their results are
  -- the same (`Option.some.inj`, `Except.ok.inj`). Then chain the equations.
  obtain ⟨o, hk, hk₁⟩ := checkKernels_sound S hS k k₁ bufs fill hsimplify
  obtain ⟨o', hk₁', hk₂⟩ := checkKernels_sound S hS k₁ k₂ bufs fill hunroll
  obtain ⟨m, o'', hpl, hk₂', hxp⟩ := checkPlaced_sound S hS k₂ pl bufs fill hplace
  obtain ⟨m', n, hpl', hc₁, hxs⟩ := checkScheduled_sound S hS pl c₁ bufs fill hschedule
  obtain ⟨n', mem, hc₁', hc, hxr⟩ := checkRouted_sound S hS c₁ c bufs fill hroute
  have e₁ : o = o' := Option.some.inj (hk₁.symm.trans hk₁')
  have e₂ : o' = o'' := Option.some.inj (hk₂.symm.trans hk₂')
  have e₃ : m = m' := Option.some.inj (hpl.symm.trans hpl')
  have e₄ : n = n' := Except.ok.inj (hc₁.symm.trans hc₁')
  refine ⟨mem, o, hc, hk, ?_⟩
  rw [hxr, ← e₄, hxs, ← e₃, hxp, ← e₂, ← e₁]

end Tau
