import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The accumulator" =>
*Terms to look up:* accumulator, register with enable.

*Files:* `Tau/Blocks/Accumulator.lean`, `Tau/Proofs/Blocks/Accumulator.lean`.

# The idea

An accumulator keeps a running total. Its input is a command.

{docstring Tau.AccIn}

{docstring Tau.accumulator}

The accumulator works for any type that has an addition. Lean expresses "has
an addition" with a _type class_: the `[Add α]` in the definition. Nothing is
assumed about the addition. It need not be associative or commutative.

```lean
example : (accumulator (0 : Nat)).trace (fun t => .add (t + 1)) 5 = [0, 1, 3, 6, 10] := by
  decide
```

# What to prove

If the accumulator is told to add on every cycle, its output at cycle `t` is
the sum of the first `t` inputs. The sum is defined by recursion:

{docstring Tau.sumTo}

The accumulator adds left to right, starting from zero, and so does `sumTo`.
That is why the proof needs no law about addition: the two sides are built in
the same order. If `sumTo` had been defined right to left, the theorem would
be false for an addition that is not associative. When a proof is harder than
you expected, check whether the definitions on the two sides line up.

# Lean you will need

* `inductive` types with several constructors, and `match`.
* Type classes: `[Add α]`.
* `rfl`, which proves an equation when both sides compute to the same thing.
  After `rw [ih]` the induction step here is closed by `rfl`.

# Exercises

*Guided.* `Exercises/Blocks/Accumulator.lean`.

*Open.* The theorem covers only the case where every command is `add`. State
and prove what the total is when the commands are arbitrary. One way: define
the total as a fold over the commands so far, and prove the accumulator's
state equals it. Then decide whether that theorem tells a reader anything the
definition did not. Not every true statement is a useful specification.

*Challenge.* State and prove: if the command at cycle `t0` is `clear` and all
later commands are `add`, the total at cycle `t0 + 1 + k` is the sum of the
`k` values after the clear.

# Checkpoint

You can write a component that is generic in its data type, and you have seen
a proof go through because two definitions recurse the same way.
