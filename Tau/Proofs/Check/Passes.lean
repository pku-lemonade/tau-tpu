import Tau.Check.Passes
import Tau.Proofs.Check.Sound
import Tau.Proofs.IR.Placed

/-!
# The per-pass checks are sound

Two theorems for each check in `Tau/Check/Passes.lean`. The first says: if
the check accepts, the output of the pass computes what its input computes,
on every buffer contents. The second says: every word the input pins to a
cycle, the output issues on that cycle.

| Pass | Buffers | Time |
|---|---|---|
| `tau-inline` | `checkInlined_sound` | `checkInlined_pins` |
| `tau-simplify`, `tau-unroll` | `checkKernels_sound` | `checkKernels_pins` |
| `tau-place` | `checkPlaced_sound` | `checkPlaced_pins` |
| `tau-schedule` | `checkScheduled_sound` | `checkScheduled_pins` |
| `tau-route`, `tau-slice`, `tau-fold` | `checkRouted_sound` | `checkRouted_pins` |

`passes_sound` and `passes_pins` chain them: if every pass is accepted, the
compiled program computes the source program and keeps its pins. That is the
conclusion of `check_sound` and `check_pins`, reached one pass at a time.

The proofs follow `check_sound`. Each side of a check is a run on
expressions, and a run on real buffers is that run evaluated:
`Source.run_of_exprs` for a source program, `Kernel.run_of_exprs` for a
kernel, `execute_of_exprs` for a compiled program, and
`Placed.execute_of_exprs`, proved here, for a placed program. The timelines
have the same four lemmas, ending in `_of_events`.
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

/-- The timeline of a placed program on real buffers is its timeline on
expressions, evaluated. -/
theorem Placed.timeline_of_events (S : Sem V) (pl : Placed) (bufs : List (List V)) (fill : V) :
    pl.timeline S bufs fill =
      (placedEvents pl).map (Event.map (Expr.denote S bufs fill)) := by
  unfold Placed.timeline placedEvents Placed.image
  rw [image_denote S, Placed.timelineFrom_map exprSem S _ (denote_hom S bufs fill)]

/-! ## `tau-inline`: source program to kernel -/

/-- **Soundness of `checkInlined`.** A source program and a kernel it accepts
compute the same buffers on every input, and neither fails. -/
theorem checkInlined_sound (S : Sem V) (hS : S.Lawful) (s : Source) (k : Kernel)
    (bufs : List (List V)) (fill : V)
    (h : checkInlined s k (bufs.map List.length) = true) :
    ∃ out, s.run S bufs = some out ∧ k.run S bufs = some out := by
  -- Both symbolic runs finished with tables that are the same after
  -- simplifying (`agree_exprs`). Each side on real buffers is its symbolic
  -- run evaluated, and the two evaluated results agree
  -- (`denote_of_sameExprs`).
  obtain ⟨a, b, ha, hb, hab⟩ := agree_exprs h
  refine ⟨_, Source.run_of_exprs S s bufs fill a ha, ?_⟩
  rw [Kernel.run_of_exprs S k bufs fill b hb, denote_of_sameExprs S hS bufs fill a b hab]

/-- **`checkInlined` and time.** Every word the source program pins to a
cycle, the kernel pins to the same cycle. -/
theorem checkInlined_pins (S : Sem V) (hS : S.Lawful) (s : Source) (k : Kernel)
    (bufs : List (List V)) (fill : V)
    (h : checkInlined s k (bufs.map List.length) = true) :
    s.timeline S bufs ⊆ k.timeline S bufs := by
  rw [Source.timeline_of_events S s bufs fill, Kernel.timeline_of_events S k bufs fill]
  exact covers_denote S hS bufs fill _ _ (agree_events h)

/-! ## `tau-simplify` and `tau-unroll`: kernel to kernel -/

/-- **Soundness of `checkKernels`.** Two kernels it accepts compute the same
buffers on every input, and neither fails. -/
theorem checkKernels_sound (S : Sem V) (hS : S.Lawful) (k k' : Kernel)
    (bufs : List (List V)) (fill : V)
    (h : checkKernels k k' (bufs.map List.length) = true) :
    ∃ out, k.run S bufs = some out ∧ k'.run S bufs = some out := by
  -- The proof of `checkInlined_sound` again, with `Kernel.run_of_exprs` on
  -- both sides.
  obtain ⟨a, b, ha, hb, hab⟩ := agree_exprs h
  refine ⟨_, Kernel.run_of_exprs S k bufs fill a ha, ?_⟩
  rw [Kernel.run_of_exprs S k' bufs fill b hb, denote_of_sameExprs S hS bufs fill a b hab]

/-- **`checkKernels` and time.** Every word the first kernel pins to a cycle,
the second pins to the same cycle. -/
theorem checkKernels_pins (S : Sem V) (hS : S.Lawful) (k k' : Kernel)
    (bufs : List (List V)) (fill : V)
    (h : checkKernels k k' (bufs.map List.length) = true) :
    k.timeline S bufs ⊆ k'.timeline S bufs := by
  rw [Kernel.timeline_of_events S k bufs fill, Kernel.timeline_of_events S k' bufs fill]
  exact covers_denote S hS bufs fill _ _ (agree_events h)

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
  obtain ⟨a, b, hk, hp, hab⟩ := agree_exprs h.2
  obtain ⟨mem, hrun, hx⟩ := Placed.execute_of_exprs S pl bufs fill b hp
  refine ⟨mem, _, hrun, Kernel.run_of_exprs S k bufs fill a hk, ?_⟩
  rw [hx]
  exact (denote_of_sameExprs S hS bufs fill a b hab).symm

/-- **`checkPlaced` and time.** Every word the kernel pins to a cycle is the
word of an instruction pinned to that cycle. -/
theorem checkPlaced_pins (S : Sem V) (hS : S.Lawful) (k : Kernel) (pl : Placed)
    (bufs : List (List V)) (fill : V)
    (h : checkPlaced k (bufs.map List.length) pl = true) :
    k.timeline S bufs ⊆ pl.timeline S bufs fill := by
  unfold checkPlaced at h
  simp only [Bool.and_eq_true] at h
  rw [Kernel.timeline_of_events S k bufs fill, Placed.timeline_of_events S pl bufs fill]
  exact covers_denote S hS bufs fill _ _ (agree_events h.2)

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
  -- Both symbolic runs finished with tables that are the same after
  -- simplifying (`agree_exprs`). Each side on real buffers is its symbolic
  -- run evaluated (`Placed.execute_of_exprs`, `execute_of_exprs`), and the
  -- two evaluated tables agree (`denote_of_sameExprs`).
  obtain ⟨a, b, hp, hm, hab⟩ := agree_exprs h
  obtain ⟨mem, hrun, hx⟩ := Placed.execute_of_exprs S pl bufs fill a hp
  obtain ⟨mem', hrun', hx'⟩ := execute_of_exprs S c bufs fill b hm
  refine ⟨mem, mem', hrun, hrun', ?_⟩
  rw [hx, hx']
  exact (denote_of_sameExprs S hS bufs fill a b hab).symm

/-- **`checkScheduled` and time.** Every pinned instruction of the placed
program is issued by the machine on the cycle it is pinned to. -/
theorem checkScheduled_pins (S : Sem V) (hS : S.Lawful) (pl : Placed) (c : Compiled)
    (bufs : List (List V)) (fill : V)
    (h : checkScheduled pl c = true) :
    pl.timeline S bufs fill ⊆ c.timeline S bufs fill := by
  rw [Placed.timeline_of_events S pl bufs fill, timeline_of_events S c bufs fill]
  exact covers_denote S hS bufs fill _ _ (agree_events h)

/-! ## `tau-route`, `tau-slice`, `tau-fold`: compiled program to compiled program -/

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
  obtain ⟨a, b, ha, hb, hab⟩ := agree_exprs h
  obtain ⟨mem, hrun, hx⟩ := execute_of_exprs S c bufs fill a ha
  obtain ⟨mem', hrun', hx'⟩ := execute_of_exprs S c' bufs fill b hb
  refine ⟨mem, mem', hrun, hrun', ?_⟩
  rw [hx, hx']
  exact (denote_of_sameExprs S hS bufs fill a b hab).symm

/-- **`checkRouted` and time.** Every word the first program issues, the
second issues on the same cycle. -/
theorem checkRouted_pins (S : Sem V) (hS : S.Lawful) (c c' : Compiled)
    (bufs : List (List V)) (fill : V)
    (h : checkRouted c c' = true) :
    c.timeline S bufs fill ⊆ c'.timeline S bufs fill := by
  rw [timeline_of_events S c bufs fill, timeline_of_events S c' bufs fill]
  exact covers_denote S hS bufs fill _ _ (agree_events h)

/-! ## All the passes -/

/-- **The passes together.** Let `k` be the output of `tau-inline` on the
source program `s`, `k₁` the output of `tau-simplify`, `k₂` of `tau-unroll`,
`pl` of `tau-place`, `c₁` of `tau-schedule`, `c₂` of `tau-route`, `c₃` of
`tau-slice` and `c` of `tau-fold`. If every pass's check accepts, then on any
buffer contents the machine runs `c` without a trap and ends with the buffers
that `s` computes. -/
theorem passes_sound (S : Sem V) (hS : S.Lawful) (s : Source) (k k₁ k₂ : Kernel) (pl : Placed)
    (c₁ c₂ c₃ c : Compiled) (bufs : List (List V)) (fill : V)
    (hinline : checkInlined s k (bufs.map List.length) = true)
    (hsimplify : checkKernels k k₁ (bufs.map List.length) = true)
    (hunroll : checkKernels k₁ k₂ (bufs.map List.length) = true)
    (hplace : checkPlaced k₂ (bufs.map List.length) pl = true)
    (hschedule : checkScheduled pl c₁ = true)
    (hroute : checkRouted c₁ c₂ = true)
    (hslice : checkRouted c₂ c₃ = true)
    (hfold : checkRouted c₃ c = true) :
    ∃ mem out,
      execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem ∧
      s.run S bufs = some out ∧
      extract c.map mem fill = out := by
  -- Take the conclusion of each soundness theorem. Two neighbouring
  -- theorems speak about the same run in the middle, so their results are
  -- the same (`Option.some.inj`, `Except.ok.inj`). Then chain the equations.
  obtain ⟨o₀, hs, hk⟩ := checkInlined_sound S hS s k bufs fill hinline
  obtain ⟨o, hk', hk₁⟩ := checkKernels_sound S hS k k₁ bufs fill hsimplify
  obtain ⟨o', hk₁', hk₂⟩ := checkKernels_sound S hS k₁ k₂ bufs fill hunroll
  obtain ⟨m, o'', hpl, hk₂', hxp⟩ := checkPlaced_sound S hS k₂ pl bufs fill hplace
  obtain ⟨m', n, hpl', hc₁, hxs⟩ := checkScheduled_sound S hS pl c₁ bufs fill hschedule
  obtain ⟨n', r, hc₁', hc₂, hxr⟩ := checkRouted_sound S hS c₁ c₂ bufs fill hroute
  obtain ⟨r', q, hc₂', hc₃, hxq⟩ := checkRouted_sound S hS c₂ c₃ bufs fill hslice
  obtain ⟨q', mem, hc₃', hc, hxf⟩ := checkRouted_sound S hS c₃ c bufs fill hfold
  have e₀ : o₀ = o := Option.some.inj (hk.symm.trans hk')
  have e₁ : o = o' := Option.some.inj (hk₁.symm.trans hk₁')
  have e₂ : o' = o'' := Option.some.inj (hk₂.symm.trans hk₂')
  have e₃ : m = m' := Option.some.inj (hpl.symm.trans hpl')
  have e₄ : n = n' := Except.ok.inj (hc₁.symm.trans hc₁')
  have e₅ : r = r' := Except.ok.inj (hc₂.symm.trans hc₂')
  have e₆ : q = q' := Except.ok.inj (hc₃.symm.trans hc₃')
  refine ⟨mem, o₀, hc, hs, ?_⟩
  rw [hxf, ← e₆, hxq, ← e₅, hxr, ← e₄, hxs, ← e₃, hxp, ← e₂, ← e₁, ← e₀]

/-- **The passes and time.** With the same eight checks accepted, every word
that `s` pins to a cycle is issued by the machine, running `c`, on that
cycle. -/
theorem passes_pins (S : Sem V) (hS : S.Lawful) (s : Source) (k k₁ k₂ : Kernel) (pl : Placed)
    (c₁ c₂ c₃ c : Compiled) (bufs : List (List V)) (fill : V)
    (hinline : checkInlined s k (bufs.map List.length) = true)
    (hsimplify : checkKernels k k₁ (bufs.map List.length) = true)
    (hunroll : checkKernels k₁ k₂ (bufs.map List.length) = true)
    (hplace : checkPlaced k₂ (bufs.map List.length) pl = true)
    (hschedule : checkScheduled pl c₁ = true)
    (hroute : checkRouted c₁ c₂ = true)
    (hslice : checkRouted c₂ c₃ = true)
    (hfold : checkRouted c₃ c = true) :
    s.timeline S bufs ⊆ c.timeline S bufs fill := by
  -- Each check puts one timeline inside the next. Follow an event through
  -- all eight.
  intro e he
  have h₁ := checkInlined_pins S hS s k bufs fill hinline he
  have h₂ := checkKernels_pins S hS k k₁ bufs fill hsimplify h₁
  have h₃ := checkKernels_pins S hS k₁ k₂ bufs fill hunroll h₂
  have h₄ := checkPlaced_pins S hS k₂ pl bufs fill hplace h₃
  have h₅ := checkScheduled_pins S hS pl c₁ bufs fill hschedule h₄
  have h₆ := checkRouted_pins S hS c₁ c₂ bufs fill hroute h₅
  have h₇ := checkRouted_pins S hS c₂ c₃ bufs fill hslice h₆
  exact checkRouted_pins S hS c₃ c bufs fill hfold h₇

end Tau
