/-
Exercise file. Generated from Tau/Proofs/Blocks/Memory.lean by scripts/make-exercises.py.

Replace each `sorry` with a proof. The finished proofs are in Tau/Proofs/Blocks/Memory.lean.
Build this file alone with:

    lake build Exercises.Blocks.Memory
-/

import Tau.Blocks.Memory
import Tau.Proofs.Blocks.Basic

/-!
# Memory: proofs

The main results are `memory_stateAt` and `memory_outAt_read`: a word holds the
value most recently written to its address, or its starting value if it has
never been written, and a read returns exactly that.
-/

namespace Tau

variable {α : Type}

theorem memory_step (n : Nat) (init : Vector α n) (s : Vector α n) (c : MemIn α) :
    (memory n init).step s c =
      match c with
      | .idle => (s, none)
      | .read a => (s, s[a]?)
      | .write a x => (s.setIfInBounds a x, none) := rfl

/-- At the start of cycle `t`, address `a` holds the last value written to it,
or its starting value if nothing was written. -/
theorem memory_stateAt (n : Nat) (init : Vector α n) (inp : Signal (MemIn α))
    (t a : Nat) (ha : a < n) :
    ((memory n init).stateAt inp t)[a] = (lastWrite inp a t).getD init[a] := by
  sorry

/-- A read of a valid address returns the last value written to it, or its
starting value if nothing was written. -/
theorem memory_outAt_read (n : Nat) (init : Vector α n) (inp : Signal (MemIn α))
    (t a : Nat) (ha : a < n) (hr : inp t = .read a) :
    (memory n init).outAt inp t = some ((lastWrite inp a t).getD init[a]) := by
  sorry

end Tau
