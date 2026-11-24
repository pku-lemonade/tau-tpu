import Tau.Blocks.Accumulator

/-!
# Multiply-accumulate (MAC)

A MAC cell takes a pair `(a, b)` on each cycle and adds the product `a * b` to
a running total. Fed the entries of two vectors one pair per cycle, it computes
their dot product.

It is built from an accumulator by putting a multiplier in front of the input.

In tau-tpu each lane of the matrix slice is one MAC cell.

Terms to look up: *multiply-accumulate*, *dot product*.
-/

namespace Tau

variable {α : Type}

/-- A multiply-accumulate cell that starts at `zero`. -/
def mac [Add α] [Mul α] (zero : α) : Block α (AccIn (α × α)) α :=
  (accumulator zero).mapIn (AccIn.map fun p => p.1 * p.2)

/-- The dot product of (1, 2, 3) and (4, 5, 6) is 32, reached after three cycles. -/
example :
    (mac (0 : Nat)).trace (fun t => .add (t + 1, t + 4)) 4 = [0, 4, 14, 32] := by
  decide

end Tau
