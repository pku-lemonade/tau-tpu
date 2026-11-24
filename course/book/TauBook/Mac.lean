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

*Files:* `Tau/Blocks/Mac.lean`, `Tau/Proofs/Blocks/Mac.lean`,
`Tau/Data/Word.lean`, `Tau/Proofs/Data/Lane.lean`.

# The idea

A multiply-accumulate cell, or MAC, adds a product to a running total on each
cycle. Fed the entries of two vectors, one pair per cycle, it computes their
dot product. It is the cell that matrix hardware is made of.

The definition does not start from scratch. A MAC is an accumulator with a
multiplier in front of its input:

{docstring Tau.mac}

{docstring Tau.Block.mapIn}

```lean
example : (mac (0 : Nat)).trace (fun t => .add (t + 1, t + 4)) 4 = [0, 4, 14, 32] := by
  decide
```

# What to prove

The proof does not start from scratch either. One lemma says what `mapIn`
does to a block's behaviour: `Block.stateAt_mapIn`. With it, the MAC theorem
is the accumulator theorem applied to a different signal. No new induction is
needed. Building a component from smaller ones pays off twice: once in the
definition and once in the proof.

# Fixed-width numbers

So far the examples used `Nat`. Real hardware uses a fixed number of bits. A
_lane_ in tau-tpu is a 32-bit value, the Lean type `BitVec 32`, and addition
wraps around on overflow. The MAC theorem still holds for lanes, because it
assumes nothing about addition. What changes is the meaning of the sum: it is
the true dot product only if nothing overflowed.

`Tau/Data/Word.lean` defines the operations on lanes, such as `Lane.relu` and
`Lane.requant`. `Tau/Proofs/Data/Lane.lean` proves facts about them in two
ways. Some are proved by splitting into cases. Others are proved by
`bv_decide`, which turns the statement into a question about individual bits
and hands it to a SAT solver:

```lean
example (a b : Lane) : Lane.max a b = Lane.max b a := Lane.max_comm a b
```

`bv_decide` needs no insight, and when the statement is false it gives a
counterexample. Its cost is trust. Run `#print axioms Tau.Lane.max_comm` and
compare with `#print axioms Tau.Lane.max_self`.

# Exercises

*Guided.* `Exercises/Blocks/Mac.lean`, then `Exercises/Data/Lane.lean`.

*Open.* State and prove a fact about `Lane.requant` that a user of it would
want to know, other than the range. For example: if the input is already
between -128 and 127 and `k` is 0, the output is the input. Try `bv_decide`
first. If it fails, read the counterexample before deciding the tactic is at
fault.

*Challenge.* Give a condition on two signals of lanes under which the MAC's
total, read as a signed integer, equals the dot product computed over the
integers. Prove it. You will need facts about `BitVec.toInt` from Lean's
library; finding them is part of the exercise.

# Checkpoint

You can build one block from another and reuse its theorem, and you know two
ways to prove a fact about fixed-width numbers and what each one costs.
