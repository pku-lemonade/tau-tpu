import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Multiply-accumulate" =>
*Terms to look up:* multiply-accumulate, dot product, two's complement,
overflow, SAT solver.

*Read:* `Tau/Blocks/Mac.lean`, `Tau/Data/Word.lean`.

*In the doc:* `Tau/Docs/Machine.md`, sections 1 and 2.3.

*Solutions, not to be opened yet:* `Tau/Proofs/Blocks/Mac.lean`,
`Tau/Proofs/Data/Lane.lean`.

*Time:* one day.

# The idea

A multiply-accumulate cell, or MAC, adds a product to a running total on each
cycle. Fed the entries of two vectors, one pair per cycle, it computes their
dot product. It is the cell that matrix hardware is made of.

The definition does not start from scratch. A MAC is an accumulator with a
multiplier in front of its input:

{docstring Tau.mac}

{docstring Tau.Block.mapIn}

# Try it

The dot product of (1, 2, 3) and (4, 5, 6) is 4 + 10 + 18 = 32:

```lean
example : (mac (0 : Nat)).trace (fun t => .add (t + 1, t + 4)) 4 = [0, 4, 14, 32] := by
  decide
```

# What to prove

```lean
example (a b : Signal Nat) (t : Nat) :
    (mac 0).outAt (fun k => .add (a k, b k)) t = sumTo 0 (fun k => a k * b k) t :=
  mac_outAt_add 0 a b t
```

The proof does not start from scratch either. `Block.stateAt_mapIn`, which
you proved in the chapter on the shift register, says that running `b.mapIn f` on a signal
is running `b` on the signal with `f` applied. So the MAC theorem is the
accumulator theorem applied to a different signal. No new induction is
needed.

Building a component from smaller ones pays twice: once in the definition and
once in the proof.

# Fixed-width numbers

So far the examples used `Nat`. Real hardware uses a fixed number of bits. A
_lane_ in tau-tpu is a 32-bit value, the Lean type `BitVec 32`, and arithmetic
wraps around on overflow. Read `Tau/Data/Word.lean` now. A _word_ is a fixed
number of lanes.

The MAC theorem holds for lanes too, because it assumes nothing about
addition. What changes is the meaning of the sum: it is the true dot product
only if nothing overflowed.

`Tau/Proofs/Data/Lane.lean` proves facts about single lanes in two ways.

The first way is by cases. `Lane.relu a` is `if a.slt 0 then 0 else a`, where
`slt` is signed less-than. To prove something about it, split on the
comparison:

```lean
example (a : Lane) : Lane.relu (Lane.relu a) = Lane.relu a := by
  unfold Lane.relu
  by_cases h : a.slt 0 = true <;> simp_all
```

The second way is `bv_decide`. It turns the statement into a question about
individual bits, hands it to a SAT solver, and checks the solver's answer:

```lean
example (a b : Lane) : Lane.max a b = Lane.max b a := by
  unfold Lane.max
  bv_decide
```

`bv_decide` needs no insight. When the statement is false it gives a
counterexample: try it on `Lane.max a b = a` and read the message. Its cost is
trust. In your scratch file run these two commands and compare:

```
#print axioms Tau.Lane.max_comm
#print axioms Tau.Lane.max_self
```

The first lists an extra axiom. A `bv_decide` proof relies on Lean's compiler
being correct. The main theorems of this course avoid it for that reason.

# How to work through it

1. Read `Tau/Blocks/Mac.lean` and find where `mapIn` is defined.
2. Do `Exercises/Blocks/Mac.lean`. Two short proofs.
3. Read `Tau/Data/Word.lean`.
4. Do `Exercises/Data/Lane.lean`. For each statement, decide first whether
   you would split into cases or use `bv_decide`.

# Lean you will need

* `unfold mac`, so that `mapIn` is visible and `Block.stateAt_mapIn` can
  rewrite.
* `exact lemma args`, to close a goal with an existing theorem. Lean checks
  that the theorem's statement matches the goal, unfolding definitions as
  needed.
* `simp_all`, which simplifies the goal and all hypotheses together.

# Exercises

*Prove.* `Exercises/Blocks/Mac.lean`, then `Exercises/Data/Lane.lean`.

*State.* State and prove a fact about `Lane.requant` that a user of it would
want to know, other than its range. For example: with `k = 0`, an input that
is already between -128 and 127 comes out unchanged. Write the bounds with
`slt`, as `Lane.requant_range` does. Try `bv_decide` first. If it fails, read
the counterexample before deciding the tactic is at fault: your statement may
be false at one of the bounds.

*Challenge.* Give a condition on two signals of lanes under which the MAC's
total, read as a signed integer with `BitVec.toInt`, equals the dot product
computed over the integers. Prove it. You will need facts about
`BitVec.toInt` from Lean's library. Finding them, with `exact?` and by
reading the library, is part of the exercise.

# Hints

For `mac_stateAt_add`: `unfold mac`, then `rw [Block.stateAt_mapIn]`, then
`exact accumulator_stateAt_add zero (fun k => a k * b k) t`. The `exact`
works because applying `AccIn.map` to `.add (a k, b k)` computes to
`.add (a k * b k)`.

For the lane facts proved by cases: `unfold` the operation, then
`split <;> rfl` or `by_cases h : ... <;> simp_all`.

# Checkpoint

`lake build Exercises.Blocks.Mac Exercises.Data.Lane` prints no `sorry`
warning. You can name two ways to prove a fact about 32-bit values and say
what each costs.
