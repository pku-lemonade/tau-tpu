import Tau.Proofs.Check.Passes
import Tau.Proofs.CellLevel.Refine
import Tau.Proofs.Passes.Unroll

/-!
# End to end

One statement that ties the whole development together.

Take a source program and a compiled program that the checker accepts. Load
any buffer contents into the machine's memories and run the program on the
cell-level machine, the one built from shift registers, memories, sequencers
and multiply-accumulate cells. Then:

* the machine does not trap,
* the buffers read back from its memories are exactly what the source program
  computes, and
* every word the source program pins to a cycle is issued on that cycle.

The proof is short, because each layer has already done its part:

* `check_sound`, `check_pins`: an accepted program is correct and on time
  on the slice-level machine,
* `cellExecute_eq`: the cell-level machine equals the slice-level machine,
* `wordSem_lawful`: real words obey the laws the simplifier uses.

## What this does not say

* It says nothing about the C++ compiler or the Python frontend. A wrong
  compiler produces programs the checker rejects; the theorem covers only the
  programs it accepts.
* It trusts the JSON readers in `Tau/Sim/Json.lean`: the source program and
  the compiled program that were checked must be the ones that were meant.
* The third point is about the slice-level machine. The cell-level machine
  is proved to end with the same memory; that it issues the same words on
  the same cycles is not stated.
* It is about this Lean model of the machine. There is no silicon here.
-/

namespace Tau

/-- **End to end.** A program accepted by the checker, run on the cell-level
machine from any buffer contents, finishes without a trap and leaves in memory
exactly the buffers the source program computes; and the machine
specification issues every pinned word on its cycle. -/
theorem end_to_end (lanes : Nat) (s : Source) (c : Compiled)
    (bufs : List (List (Word lanes)))
    (h : check s (bufs.map List.length) c = true) :
    ∃ mem out,
      cellExecute c.cfg c.prog c.cycles (c.image bufs Word.zero) = .ok mem ∧
      s.run (wordSem lanes) bufs = some out ∧
      extract c.map mem Word.zero = out ∧
      s.timeline (wordSem lanes) bufs ⊆ c.timeline (wordSem lanes) bufs Word.zero := by
  obtain ⟨mem, out, hrun, hk, hx⟩ :=
    check_sound (wordSem lanes) (wordSem_lawful lanes) s c bufs Word.zero h
  exact ⟨mem, out, by rw [cellExecute_eq]; exact hrun, hk, hx,
    check_pins (wordSem lanes) (wordSem_lawful lanes) s c bufs Word.zero h⟩

/-- The same for a kernel with no calls, when the checker was given the
unrolled kernel: the conclusion is still about the kernel as written, loops
and all. -/
theorem end_to_end_unrolled (lanes : Nat) (k : Kernel) (c : Compiled)
    (bufs : List (List (Word lanes)))
    (h : check (Source.ofKernel (k.unroll.map Item.stmt)) (bufs.map List.length) c = true) :
    ∃ mem out,
      cellExecute c.cfg c.prog c.cycles (c.image bufs Word.zero) = .ok mem ∧
      k.run (wordSem lanes) bufs = some out ∧
      extract c.map mem Word.zero = out ∧
      k.timeline (wordSem lanes) bufs ⊆ c.timeline (wordSem lanes) bufs Word.zero := by
  obtain ⟨mem, out, hrun, hk, hx, ht⟩ := end_to_end lanes _ c bufs h
  rw [Source.run_ofKernel, Kernel.run_unroll] at hk
  rw [Source.timeline_ofKernel, Kernel.timeline_unroll] at ht
  exact ⟨mem, out, hrun, hk, hx, ht⟩

/-- The same, when each of the eight passes was checked on its own instead of
the compiler as a whole. `k`, `k₁`, `k₂`, `pl`, `c₁`, `c₂` and `c₃` are the
outputs of `tau-inline`, `tau-simplify`, `tau-unroll`, `tau-place`,
`tau-schedule`, `tau-route` and `tau-slice`, and `c` is the output of
`tau-fold`. -/
theorem end_to_end_passes (lanes : Nat) (s : Source) (k k₁ k₂ : Kernel) (pl : Placed)
    (c₁ c₂ c₃ c : Compiled) (bufs : List (List (Word lanes)))
    (hinline : checkInlined s k (bufs.map List.length) = true)
    (hsimplify : checkKernels k k₁ (bufs.map List.length) = true)
    (hunroll : checkKernels k₁ k₂ (bufs.map List.length) = true)
    (hplace : checkPlaced k₂ (bufs.map List.length) pl = true)
    (hschedule : checkScheduled pl c₁ = true)
    (hroute : checkRouted c₁ c₂ = true)
    (hslice : checkRouted c₂ c₃ = true)
    (hfold : checkRouted c₃ c = true) :
    ∃ mem out,
      cellExecute c.cfg c.prog c.cycles (c.image bufs Word.zero) = .ok mem ∧
      s.run (wordSem lanes) bufs = some out ∧
      extract c.map mem Word.zero = out ∧
      s.timeline (wordSem lanes) bufs ⊆ c.timeline (wordSem lanes) bufs Word.zero := by
  obtain ⟨mem, out, hrun, hk, hx⟩ :=
    passes_sound (wordSem lanes) (wordSem_lawful lanes) s k k₁ k₂ pl c₁ c₂ c₃ c bufs Word.zero
      hinline hsimplify hunroll hplace hschedule hroute hslice hfold
  exact ⟨mem, out, by rw [cellExecute_eq]; exact hrun, hk, hx,
    passes_pins (wordSem lanes) (wordSem_lawful lanes) s k k₁ k₂ pl c₁ c₂ c₃ c bufs Word.zero
      hinline hsimplify hunroll hplace hschedule hroute hslice hfold⟩

end Tau
