import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The systolic array" =>
*Terms to look up:* systolic array, matrix-vector product, pipelining.

*Files:* `Tau/Blocks/SystolicArray.lean`, `Tau/Proofs/Blocks/SystolicArray.lean`.

# The idea

A systolic array is a row of identical cells. Data moves one cell per cycle,
and each cell does a small piece of work as the data passes.

{docstring Tau.systolicArray}

This one multiplies a matrix by a vector. Cell `j` holds entry `j` of the
vector. A partial sum enters at the left and moves right. As it passes cell
`j`, the cell adds its entry times a coefficient that arrives from outside on
that cycle.

For the array to compute row `i` of a matrix `A`, the coefficient `A i j`
must reach cell `j` on cycle `i + j`, which is the cycle on which the partial
sum for row `i` is there. Nothing in the array checks this. The coefficients
have to be fed on the right cycles, and if they are fed one cycle off the
array computes something else without complaint.

This is the whole idea of tau-tpu at small scale. Read the example in
`Tau/Blocks/SystolicArray.lean` and work out by hand why cell 1 is fed the
coefficients one cycle later than cell 0.

# What to prove

There are two theorems.

`systolicArray_stateAt` says what is stored after each cell on each cycle,
for any coefficients at all. It is an induction on the cell index, and it is
the hardest proof so far, because the cycle number has to be generalized and
the index arithmetic is fiddly.

`systolicArray_matvec` says that if the coefficients are fed on the right
cycles, the output is the matrix-vector product. It follows from the first
theorem by substituting the feeding rule.

Notice the division of labour. The first theorem describes the hardware. The
second adds an assumption about how the hardware is driven. The assumption
`hc` in `systolicArray_matvec` is a timetable.

# Lean you will need

* `induction j generalizing t`.
* `obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1`, to replace a positive number by a
  successor.
* `congr 1` and a congruence lemma (`sumTo_congr`) to show two sums are equal
  by showing their terms are equal.
* Patience with `omega`. When it fails, state the arithmetic fact you need
  with `have` and prove that separately.

# Exercises

*Guided.* `Exercises/Blocks/SystolicArray.lean`. Budget three days.

*Open.* The theorem starts counting rows at cycle 0. State and prove a version
for a matrix whose first row starts at an arbitrary cycle `t0`. Decide first
whether you need a new induction or can reuse the existing theorem with a
shifted signal.

*Challenge.* A two-dimensional systolic array multiplies two matrices. Each
cell holds a running total, passes its left input to the right and its top
input downward, and adds their product. Define it as a block whose state is a
grid, work out on which cycle each entry of each matrix must enter, and prove
that the totals are the matrix product.

# Checkpoint

You have proved that a piece of hardware is correct under a stated timing
assumption. Everything after this chapter is that idea at a larger scale.
