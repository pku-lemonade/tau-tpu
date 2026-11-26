import Tau.Blocks.Basic

/-!
# Systolic array

A systolic array is a row of identical cells in which data moves one cell per
cycle and every cell does a small piece of work as the data passes.

This one multiplies a matrix by a vector. Cell `j` holds the vector entry
`x[j]`. A partial sum starts at zero, enters cell 0, and moves one cell to the
right on every cycle. As it passes cell `j`, the cell adds `c * x[j]`, where
`c` is the coefficient fed to that cell on that cycle. After the last cell the
partial sum is a finished entry of the result.

For this to compute row `i` of the matrix `A`, the coefficient `A i j` has to
reach cell `j` at cycle `i + j`: the same cycle as the partial sum for row `i`.
Nothing in the array checks this. The coefficients simply have to be fed on the
right cycles. This is static scheduling in its smallest form.

In tau-tpu the matrix slice has the same shape of timing problem.

Terms to look up: *systolic array*, *matrix-vector product*.

Docs: Machine 2.8 (`Tau/Docs/`).
-/

namespace Tau

variable {α : Type}

/-- A systolic array of `n` cells holding the vector `x`. On each cycle the
input gives one coefficient per cell. The state is the partial sum stored after
each cell. The output is the partial sum after the last cell. -/
def systolicArray [Add α] [Mul α] (zero : α) {n : Nat} (x : Vector α n) :
    Block (Vector α n) (Vector α n) α where
  init := Vector.replicate n zero
  step s c :=
    (Vector.ofFn fun j : Fin n =>
        (if j.val = 0 then zero
         else s[j.val - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt))
          + c[j] * x[j],
     if h : 0 < n then s[n - 1]'(Nat.sub_lt h Nat.zero_lt_one) else zero)

/-- The matrix `[[1, 2], [3, 4]]` times the vector `(10, 100)` is `(210, 430)`.
Row `i` is fed to cell `j` at cycle `i + j`, so cell 0 sees 1, 3 and cell 1
sees 2, 4 one cycle later. The results appear at cycles 2 and 3. -/
example :
    (systolicArray (0 : Nat) #v[10, 100]).trace
      (fun t => #v[if t = 0 then 1 else if t = 1 then 3 else 0,
                   if t = 1 then 2 else if t = 2 then 4 else 0]) 4
      = [0, 0, 210, 430] := by
  decide

end Tau
