import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The shift register" =>
*Terms to look up:* flip-flop, register, shift register, clock cycle.

*Files:* `Tau/Blocks/Basic.lean`, `Tau/Blocks/ShiftRegister.lean`,
`Tau/Proofs/Blocks/Basic.lean`, `Tau/Proofs/Blocks/ShiftRegister.lean`.

# The idea

Every piece of hardware in this course is a _block_: something that holds a
state, and on each clock cycle reads an input, writes an output and moves to a
new state. In Lean a block is a starting state and a function.

{docstring Tau.Block}

Two functions say what a block does over time. Both take a _signal_, which is
a function from cycle numbers to values.

{docstring Tau.Block.stateAt}

{docstring Tau.Block.outAt}

The first block is the shift register: a row of slots through which values
move one slot per cycle.

{docstring Tau.shiftRegister}

You can run it. A depth-2 register fed 10, 11, 12 and so on outputs its reset
value twice and then the inputs, two cycles late:

```lean
example : (shiftRegister 2 0).trace (fun t => 10 + t) 5 = [0, 0, 10, 11, 12] := by
  decide
```

# What to prove

That example checks one depth, one input and five cycles. The theorem says
the same thing for every depth, every input and every cycle:

```lean
example (n : Nat) (reset : Nat) (inp : Signal Nat) (t : Nat) :
    (shiftRegister n reset).outAt inp t = if n ≤ t then inp (t - n) else reset :=
  shiftRegister_outAt n reset inp t
```

Every theorem about a block in this course has this shape: the output at
cycle `t`, written as a function of the inputs at earlier cycles.

To prove it you first need to know what is in every slot, not only the last
one. That is `shiftRegister_stateAt`, and it is proved by induction on the
cycle. The statement about the output then follows from the statement about
the state. This pattern, a stronger statement about the whole state proved by
induction and then a corollary about the output, returns in every chapter.

# Lean you will need

* `structure`, `def`, pattern matching on `Nat`.
* `Vector α n`: an array whose length is part of its type.
* The tactics `induction ... generalizing`, `rw`, `simp`, `by_cases`, `omega`.
  `omega` proves facts about natural numbers and integers that involve only
  addition, subtraction, comparison and constants. You will use it constantly
  for index arithmetic.

# Exercises

*Guided.* `Exercises/Blocks/Basic.lean`, then
`Exercises/Blocks/ShiftRegister.lean`.

*Open.* Define a register with an enable input: it takes a pair of a Boolean
and a value, and keeps its old contents on cycles where the Boolean is false.
State what its output is at cycle `t`. You will find you need a helper
function that walks back to the most recent enabled cycle. Writing that
helper is the exercise.

*Challenge.* Define the composition of two blocks, where the output of the
first feeds the input of the second, and prove that two shift registers of
depths `m` and `n` in a row behave as one of depth `m + n`.

# Checkpoint

You can define a clocked component as a step function, run it, state what it
outputs at every cycle, and prove the statement by induction on time.
