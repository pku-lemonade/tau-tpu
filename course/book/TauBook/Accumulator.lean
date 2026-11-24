import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The accumulator" =>
*Terms to look up:* accumulator, register with enable.

*Read:* `Tau/Blocks/Accumulator.lean`.

*Solutions, not to be opened yet:* `Tau/Proofs/Blocks/Accumulator.lean`.

*Time:* one day.

# The idea

An accumulator keeps a running total. Its input is a command.

{docstring Tau.AccIn}

`AccIn` is an _inductive type_ with four constructors. A value of it is one
of `.hold`, `.add x`, `.clear` or `.load x`. A function on it is written with
`match`, one line per constructor.

{docstring Tau.accumulator}

The accumulator works for any type that has an addition. Lean expresses "has
an addition" with a _type class_: the `[Add α]` in the definition. Nothing is
assumed about the addition. It need not be associative or commutative.

# Try it

Adding 1, 2, 3, 4 gives the running totals 0, 1, 3, 6, 10. The output on each
cycle is the total before that cycle's command takes effect.

```lean
example : (accumulator (0 : Nat)).trace (fun t => .add (t + 1)) 5 = [0, 1, 3, 6, 10] := by
  decide
```

A `clear` in the middle:

```lean
example :
    (accumulator (0 : Nat)).trace
      (fun t => if t = 2 then .clear else .add 5) 5 = [0, 5, 10, 0, 5] := by
  decide
```

# What to prove

If the accumulator is told to add on every cycle, its output at cycle `t` is
the sum of the first `t` inputs. The sum is a definition of ours:

{docstring Tau.sumTo}

```lean
example : sumTo 0 (fun k => k + 1) 4 = 10 := by decide
```

The theorem:

```lean
example (x : Signal Nat) (t : Nat) :
    (accumulator 0).outAt (fun k => .add (x k)) t = sumTo 0 x t :=
  accumulator_outAt_add 0 x t
```

The accumulator adds left to right, starting from zero, and so does `sumTo`.
That is why the proof needs no law about addition: the two sides are built in
the same order. Had `sumTo` been defined right to left, the theorem would be
false for an addition that is not associative.

When a proof is harder than you expected, check whether the definitions on
the two sides recurse the same way. Often the fix is to change the
specification, not the proof.

# How to work through it

1. Read `Tau/Blocks/Accumulator.lean`.
2. In your scratch file, run the accumulator on a signal of your own with a
   `hold` in it.
3. Do `Exercises/Blocks/Accumulator.lean`, in the order of the file.

# Lean you will need

* `match c with` and the three constructors.
* `split`, which turns a goal containing a `match` into one goal per branch.
  Use it for `accumulator_outAt`, where every branch is then `rfl`.
* `rw [ih]` followed by `rfl`. After rewriting with the induction hypothesis,
  the step case of `accumulator_stateAt_add` is true by computing.

# Exercises

*Guided.* `Exercises/Blocks/Accumulator.lean`.

*Open.* The theorem covers only the case where every command is `add`. State
what the total is when the commands are arbitrary. One way is to define the
total as a function `total zero cmds t` by recursion on `t`, and prove the
accumulator's state equals it:

```
def total [Add α] (zero : α) (cmds : Signal (AccIn α)) : Nat → α
  | 0 => zero
  | t + 1 => sorry
```

Prove it. Then answer in a comment: does this theorem tell a reader anything
that the definition of `accumulator` did not? Compare with
`accumulator_stateAt_add`, which does. Not every true statement is a useful
specification.

*Challenge.* State and prove: if the command at cycle `t0` is `clear` and all
later commands are `add`, the total at cycle `t0 + 1 + k` is the sum of the
`k` values after the clear.

# Hints

For `accumulator_outAt`: unfold `Block.outAt`, rewrite with
`accumulator_step`, then `split <;> rfl`.

For `accumulator_stateAt_add`: induction on `t`. The zero case is `rfl`. In
the step case, `rw [Block.stateAt_succ, ih]` and then `rfl`.

For `accumulator_outAt_add`: no induction. Rewrite with the two theorems
before it.

# Checkpoint

`lake build Exercises.Blocks.Accumulator` prints no `sorry` warning. You can
say why the proof needs no law about addition.
