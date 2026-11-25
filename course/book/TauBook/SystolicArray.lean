import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The systolic array" =>
*Terms to look up:* systolic array, matrix-vector product.

*Source:* `course/architecture-manual.md`, section 2.8.

*Specify:* `course/Specs/SystolicArray.lean`.

*Read, after you have specified it:* `Tau/Blocks/SystolicArray.lean`.

*Proofs:* `Tau/Proofs/Blocks/SystolicArray.lean`. One is an exercise.

*Time:* two days.

# Specify it first

Stop reading here. Open section 2.8 of the manual and
`course/Specs/SystolicArray.lean`, and follow the steps at the top of the
file. Come back when the report says that all rows agree.

The statement is the hard part of this one. The array computes a product
only if its inputs arrive on the right cycles. Your statement has to say
which cycles, as a hypothesis about the input signal.

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
sum for row `i` is there. Nothing in the array checks this. If the
coefficients are fed one cycle off, the array computes something else and
does not complain.

This is the whole idea of tau-tpu at small scale.

# Try it, slowly

Multiply the matrix with rows (1, 2) and (3, 4) by the vector (10, 100). The
answers are 1·10 + 2·100 = 210 and 3·10 + 4·100 = 430.

Cell 0 must see the first column, 1 then 3, on cycles 0 and 1. Cell 1 must
see the second column, 2 then 4, one cycle later, on cycles 1 and 2.

```lean
def feed : Signal (Vector Nat 2) := fun t =>
  #v[if t = 0 then 1 else if t = 1 then 3 else 0,
     if t = 1 then 2 else if t = 2 then 4 else 0]
```

Here is what is stored after each cell at the start of each cycle.

```lean
example :
    (List.range 5).map (fun t => ((systolicArray 0 #v[10, 100]).stateAt feed t).toList)
      = [[0, 0], [10, 0], [30, 210], [0, 430], [0, 0]] := by
  decide
```

Follow row 0 through. On cycle 0 cell 0 computes 0 + 1·10 = 10, stored at the
start of cycle 1. On cycle 1 cell 1 takes that 10 and adds 2·100, giving 210,
stored at the start of cycle 2. The output on cycle 2 is 210.

Now follow row 1 yourself, and say where the 30 comes from.

Then shift the second column one cycle later in your scratch file, evaluate
again, and see the wrong answers come out with no error.

# The statement

There are two theorems.

`systolicArray_stateAt` says what is stored after each cell on each cycle,
for any coefficients at all:

```lean
example (x : Vector Nat 3) (c : Signal (Vector Nat 3)) (j : Nat) (hj : j < 3)
    (t : Nat) (ht : j + 1 ≤ t) :
    ((systolicArray 0 x).stateAt c t)[j] =
      sumTo 0 (fun k => (c (t - 1 - j + k))[k]?.getD 0 * x[k]?.getD 0) (j + 1) :=
  systolicArray_stateAt 0 x c j hj t ht
```

In words: the partial sum after cell `j` at cycle `t` has one term from each
of cells 0 to `j`, and the term from cell `k` used the coefficient fed to
that cell at cycle `t - 1 - j + k`. Check that against the 210 above, with
`t = 2` and `j = 1`: cell 0 used the coefficient of cycle 0, and cell 1 the
coefficient of cycle 1.

The sum ranges over `k`, which is a plain number with no evidence attached
that it is less than the number of cells. So the statement reads lane `k`
with `v[k]?.getD 0`, which needs no evidence: it is `v[k]` when `k` is in
range. Inside the proofs, whenever you know `k < n`, `simp [hk]` turns
`v[k]?.getD 0` back into `v[k]`.

The hypothesis `ht : j + 1 ≤ t` says the array has run long enough for a sum
to have reached cell `j`.

`systolicArray_matvec` says that if the coefficients are fed on the right
cycles, the output is the matrix-vector product:

```lean
example (x : Vector Nat 3) (A : Nat → Nat → Nat) (c : Signal (Vector Nat 3))
    (hc : ∀ i j (hj : j < 3), (c (i + j))[j] = A i j) (i : Nat) :
    (systolicArray 0 x).outAt c (i + 3) = sumTo 0 (fun k => A i k * x[k]?.getD 0) 3 :=
  systolicArray_matvec 0 (by omega) x A c hc i
```

Notice the division of labour. The first theorem describes the hardware,
whatever it is fed. The second adds an assumption, `hc`, about how it is fed.
The assumption `hc` is a timetable.

# How to work through it

1. Specify the array from the manual, as above.
2. Read the definition and redo the table above for a 3 by 3 matrix of your
   choice.
3. Compare your statement with `systolicArray_matvec`. Its hypothesis `hc`
   is the timing assumption. Is yours the same assumption?
4. Read the statement of `systolicArray_stateAt` until you can explain every
   index in it. It is given in the exercise file. Its proof is nearly all
   index arithmetic; read the outline only.
5. Prove `systolicArray_matvec` from it, or give it to an agent and review
   what comes back. No induction.

# Lean you will need

* `apply sumTo_congr`, to show two sums are equal by showing their terms are.
* `have h : (some index fact) := by omega` followed by `rw [h]`. When `omega`
  or `simp` will not see that two index expressions are equal, state the
  equation yourself.

# Exercises

*Specify.* `course/Specs/SystolicArray.lean`.

*State.* `ComputesMatVec` in that file.

*State.* The theorem counts rows from cycle 0. State a version for a matrix
whose first row starts at an arbitrary cycle `t0`. Before asking for a
proof, decide whether it needs a new induction or follows from
`systolicArray_matvec` applied to the signal `fun t => c (t + t0)`. If the
second, it needs a lemma relating a block's behaviour on a shifted signal to
its behaviour on the original, and you should ask whether that lemma is
true.

*Prove.* `systolicArray_matvec` in `Exercises/Blocks/SystolicArray.lean`.

*Questions.* Section 2.8 leaves at least two things open.

*Claims.* Add to `course/Work/Claims.md` a row for each thing you wrote in this
chapter: what it is, and how it stands.

*Challenge.* A two-dimensional systolic array multiplies two matrices. Each
cell holds a running total, passes its left input to the right and its top
input downward, and adds their product. Write its page of the manual first:
a paragraph and a table. Then define it as a block whose state is a grid,
work out on which cycle each entry of each matrix must enter, and state that
the totals are the matrix product.

# Hints

For `systolicArray_matvec`: unfold `Block.outAt`, take a step, use
`systolicArray_stateAt` at `j = n - 1` and `t = i + n`. Rewrite `n - 1 + 1`
to `n`. Then `sumTo_congr` and the hypothesis `hc`.

# Checkpoint

The report says that all rows agree. Your statement has a hypothesis about
when the inputs arrive. You have specified a piece of hardware that is
correct only under a stated timing assumption. Everything after this chapter
is that idea at a larger scale.
