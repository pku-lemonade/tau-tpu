import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The systolic array" =>
*Terms to look up:* systolic array, matrix-vector product.

*Read:* `Tau/Blocks/SystolicArray.lean`.

*Solutions, not to be opened yet:* `Tau/Proofs/Blocks/SystolicArray.lean`.

*Time:* three days.

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

# What to prove

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

1. Read the definition and redo the table above for a 3 by 3 matrix of your
   choice.
2. Read the statement of `systolicArray_stateAt` until you can explain every
   index in it. Do not start the proof before that.
3. Prove `systolicArray_stateAt` in `Exercises/Blocks/SystolicArray.lean`.
   The induction is on the cell index `j`, with the cycle `t` generalized,
   because the sum after cell `j + 1` at cycle `t + 1` is built from the sum
   after cell `j` at cycle `t`.
4. Prove `systolicArray_matvec` from it. No induction.

Expect step 3 to take most of the time. Nearly all of the difficulty is index
arithmetic.

# Lean you will need

* `induction j generalizing t`.
* `obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩`. When you know
  `t` is positive, this replaces `t` by `t + 1` everywhere, so that
  `Block.stateAt_succ` applies.
* `congr 1`, to split an equation `a + b = a' + b'` into `a = a'` and
  `b = b'`.
* `apply sumTo_congr`, to show two sums are equal by showing their terms are.
* `have h : (some index fact) := by omega` followed by `rw [h]`. When `omega`
  or `simp` will not see that two index expressions are equal, state the
  equation yourself.

# Exercises

*Guided.* `Exercises/Blocks/SystolicArray.lean`.

*Open.* The theorem counts rows from cycle 0. State and prove a version for a
matrix whose first row starts at an arbitrary cycle `t0`. Before proving
anything, decide whether you need a new induction or can apply
`systolicArray_matvec` to the signal `fun t => c (t + t0)`. If the second,
you need a lemma relating a block's behaviour on a shifted signal to its
behaviour on the original, and you should ask whether that lemma is true.

*Challenge.* A two-dimensional systolic array multiplies two matrices. Each
cell holds a running total, passes its left input to the right and its top
input downward, and adds their product. Define it as a block whose state is a
grid, work out on which cycle each entry of each matrix must enter, and prove
that the totals are the matrix product.

# Hints

For `systolicArray_stateAt`, case `j = 0`: after `obtain` and one step, the
goal is about a sum with one term. `simp [sumTo, hj]` finishes.

Case `j + 1`, in order:

1. After one step and `simp only [Vector.getElem_ofFn]`, unfold one layer of
   `sumTo` on the right with `rw [sumTo]`.
2. The last term on the right now mentions the cycle
   `t + 1 - 1 - (j + 1) + (j + 1)`. State with `have` that this equals `t`,
   prove it by `omega`, and rewrite with it.
3. The left side still says `if j + 1 = 0 then zero else ...[j + 1 - 1]`.
   Clean it up with
   `simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]`. Until
   you do, the induction hypothesis will not match.
4. Rewrite with the induction hypothesis at cycle `t`. The goal is now of
   the form `a + b = a' + b'`; use `congr 1`.
5. The first goal is two sums whose terms differ only in how the cycle index
   is written: `apply sumTo_congr`, then state the index equation with
   `have` and prove it by `omega`.
6. The second goal differs only by `[j + 1]?.getD` against `[j + 1]`:
   `simp [hj]`.

For `systolicArray_matvec`: unfold `Block.outAt`, take a step, use
`systolicArray_stateAt` at `j = n - 1` and `t = i + n`. Rewrite `n - 1 + 1`
to `n`. Then `sumTo_congr` and the hypothesis `hc`.

# Checkpoint

`lake build Exercises.Blocks.SystolicArray` prints no `sorry` warning. You
have proved that a piece of hardware is correct under a stated timing
assumption. Everything after this chapter is that idea at a larger scale.
