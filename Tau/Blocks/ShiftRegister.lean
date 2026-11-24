import Tau.Blocks.Basic

/-!
# Shift register

A shift register of depth `n` is a row of `n` slots. On every cycle each value
moves one slot along: the input enters slot 0, slot `i` moves to slot `i + 1`,
and the value in the last slot leaves as the output.

In tau-tpu a stream is a shift register: a value written at one slice reaches a
slice `n` hops away exactly `n` cycles later. That fact is
`shiftRegister_outAt` in `Tau/Proofs/Blocks/ShiftRegister.lean`.

Terms to look up: *flip-flop*, *register*, *shift register*.
-/

namespace Tau

variable {α : Type}

/-- A shift register of depth `n`. Every slot holds `reset` at cycle 0.
A depth of 0 is a plain wire: the output is the input of the same cycle. -/
def shiftRegister (n : Nat) (reset : α) : Block (Vector α n) α α where
  init := Vector.replicate n reset
  step s x :=
    (Vector.ofFn fun i : Fin n =>
        if i.val = 0 then x
        else s[i.val - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt),
     if h : 0 < n then s[n - 1]'(Nat.sub_lt h Nat.zero_lt_one) else x)

/-- Example: a depth-2 register fed 10, 11, 12, ... and reset to 0. -/
example : (shiftRegister 2 0).trace (fun t => 10 + t) 5 = [0, 0, 10, 11, 12] := by
  decide

end Tau
