import Tau.Proofs.Check.Sound
import Tau.Proofs.CellLevel.Refine
import Tau.Proofs.Passes.Unroll

/-!
# End to end

One statement that ties the whole development together.

Take a kernel and a compiled program that the checker accepts. Load any
buffer contents into the chip's memories and run the program on the
cell-level machine, the one built from shift registers, memories, sequencers
and multiply-accumulate cells. Then:

* the machine does not trap, and
* the buffers read back from its memories are exactly what the kernel
  computes.

The proof is three lines, because each layer has already done its part:

* `check_sound`: an accepted program is correct on the slice-level machine,
* `cellExecute_eq`: the cell-level machine equals the slice-level machine,
* `wordSem_lawful`: real words obey the laws the simplifier uses.

## What this does not say

* It says nothing about the C++ compiler. A wrong compiler produces programs
  the checker rejects; the theorem covers only the programs it accepts.
* It trusts the JSON readers in `Tau/Sim/Json.lean`: the kernel and program
  that were checked must be the ones that were meant.
* It is about this Lean model of the chip. There is no silicon here.
-/

namespace Tau

/-- **End to end.** A program accepted by the checker, run on the cell-level
machine from any buffer contents, finishes without a trap and leaves in memory
exactly the buffers the kernel computes. -/
theorem end_to_end (lanes : Nat) (k : Kernel) (c : Compiled)
    (bufs : List (List (Word lanes)))
    (h : check k (bufs.map List.length) c = true) :
    ∃ mem out,
      cellExecute c.cfg c.prog c.cycles (c.image bufs Word.zero) = .ok mem ∧
      k.run (wordSem lanes) bufs = some out ∧
      extract c.map mem Word.zero = out := by
  obtain ⟨mem, out, hrun, hk, hx⟩ :=
    check_sound (wordSem lanes) (wordSem_lawful lanes) k c bufs Word.zero h
  exact ⟨mem, out, by rw [cellExecute_eq]; exact hrun, hk, hx⟩

/-- The same, when the checker was given the unrolled kernel: the conclusion
is still about the kernel as written, loops and all. -/
theorem end_to_end_unrolled (lanes : Nat) (k : Kernel) (c : Compiled)
    (bufs : List (List (Word lanes)))
    (h : check (k.unroll.map Item.stmt) (bufs.map List.length) c = true) :
    ∃ mem out,
      cellExecute c.cfg c.prog c.cycles (c.image bufs Word.zero) = .ok mem ∧
      k.run (wordSem lanes) bufs = some out ∧
      extract c.map mem Word.zero = out := by
  obtain ⟨mem, out, hrun, hk, hx⟩ := end_to_end lanes _ c bufs h
  exact ⟨mem, out, hrun, by rw [← Kernel.run_unroll]; exact hk, hx⟩

end Tau
