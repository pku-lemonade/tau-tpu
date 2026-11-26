import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The shift register" =>
*Terms to look up:* flip-flop, register, shift register, clock cycle.

*Read:* `Tau/Blocks/Basic.lean`, `Tau/Blocks/ShiftRegister.lean`.

*In the doc:* `Tau/Docs/Machine.md`, section 2.1. Read it after the definition,
and see how much less it says.

*Solutions, not to be opened yet:* `Tau/Proofs/Blocks/Basic.lean`,
`Tau/Proofs/Blocks/ShiftRegister.lean`.

*Time:* two days.

# The idea

Every piece of hardware in this course is a _block_: something that holds a
state, and on each clock cycle reads an input, writes an output and moves to a
new state. In Lean a block is a starting state and a function.

{docstring Tau.Block}

`Block σ ι ο` has three type arguments: the type of the state, of the input
and of the output. The `register` and `counter` of the previous chapter were
blocks.

Two functions say what a block does over time. Both take a _signal_, which is
a function from cycle numbers to values. `Signal α` is just another name for
`Nat → α`.

{docstring Tau.Block.stateAt}

{docstring Tau.Block.outAt}

Read their definitions in `Tau/Blocks/Basic.lean`. `stateAt` is by recursion
on the cycle: the state at cycle 0 is `init`, and the state at `t + 1` is one
step from the state at `t`. That recursion is why proofs about blocks are by
induction on the cycle.

The first block is the shift register: a row of slots through which values
move one slot per cycle.

{docstring Tau.shiftRegister}

# Reading the definition

The definition uses four things you have not seen.

* `Vector α n` is an array of exactly `n` values. The length is part of the
  type, so the state of a depth-3 register and a depth-4 register have
  different types.
* `Vector.ofFn f` builds a vector from a function that gives each slot's
  value. Its argument `i` has type `Fin n`: a number known to be less than
  `n`. `i.val` is that number as a plain `Nat`.
* `s[k]'proof` is slot `k` of `s`. Lean will not let you index a vector
  without evidence that the index is in range, and the part after the `'` is
  that evidence. You can ignore what the evidence says. Read `s[i.val - 1]'(...)`
  as "slot `i - 1` of `s`".

* `if h : 0 < n then ... else ...` is an `if` that gives its condition a name.
  Inside the `then` branch, `h` is evidence that `0 < n`, which is what makes
  `s[n - 1]` a legal index there.

So the step function reads: the new slot 0 is the input, the new slot `i` is
the old slot `i - 1`, and the output is the old last slot. If the depth is 0
there are no slots and the output is the input.

# Try it

A depth-2 register fed 10, 11, 12 and so on outputs its reset value twice and
then the inputs, two cycles late:

```lean
example : (shiftRegister 2 0).trace (fun t => 10 + t) 5 = [0, 0, 10, 11, 12] := by
  decide
```

You can look inside. At the start of cycle 3 the inputs of cycles 2 and 1 are
in slots 0 and 1:

```lean
example : ((shiftRegister 2 0).stateAt (fun t => 10 + t) 3).toList = [12, 11] := by
  decide
```

In your scratch file, change the depth to 0 and to 4 and predict the output
before you evaluate it.

# What to prove

The examples check one depth, one input and a few cycles. The theorem says
the same thing for every depth, every input and every cycle:

```lean
example (n : Nat) (reset : Nat) (inp : Signal Nat) (t : Nat) :
    (shiftRegister n reset).outAt inp t = if n ≤ t then inp (t - n) else reset :=
  shiftRegister_outAt n reset inp t
```

Every theorem about a block in this course has this shape: the output at
cycle `t`, written as a function of the inputs at earlier cycles.

You cannot prove it directly by induction on `t`. The output at cycle `t + 1`
is the last slot, and the last slot at `t + 1` came from the slot before it at
`t`, which the statement says nothing about. The statement has to be made
stronger: say what is in every slot.

```lean
example (n : Nat) (reset : Nat) (inp : Signal Nat) (t i : Nat) (hi : i < n) :
    ((shiftRegister n reset).stateAt inp t)[i] = if i < t then inp (t - 1 - i) else reset :=
  shiftRegister_stateAt n reset inp t i hi
```

Check this against the second example above: with `t = 3`, slot 0 holds
`inp 2` and slot 1 holds `inp 1`.

Strengthening the statement until the induction goes through is the central
move of this course. When an induction fails, ask what else you would need to
know about the state at cycle `t`, and add it to the statement.

# How to work through it

1. Read `Tau/Blocks/Basic.lean` and `Tau/Blocks/ShiftRegister.lean`.
2. In your scratch file, evaluate `stateAt` for depth 3 at cycles 0 to 4.
3. Do `Exercises/Blocks/Basic.lean`. It has three proofs of a few lines each,
   about two small definitions from `Tau/Blocks/Basic.lean` that later
   chapters use. `b.mapIn f` is the block `b` with the function `f` applied
   to each input first. `sumTo zero x n` is `zero + x 0 + ... + x (n - 1)`.
   The first two proofs say what `mapIn` does to `stateAt` and `outAt`. The
   third says two sums are equal if their terms are.
4. Read the statement of `shiftRegister_stateAt` and convince yourself it is
   true, using step 2.
5. Do `Exercises/Blocks/ShiftRegister.lean`. Prove `shiftRegister_stateAt`
   first, then `shiftRegister_outAt` from it.

# Lean you will need

* `induction t generalizing i`. The slot index changes between cycles: slot
  `i` at cycle `t + 1` came from slot `i - 1` at cycle `t`. A plain induction
  gives you the hypothesis for the same `i`, which is the wrong one.
  `generalizing i` gives you the hypothesis for every `i`.
* `rw [Block.stateAt_succ, shiftRegister_step]` to take one step. These two
  lemmas are true by `rfl`; they exist so that you can rewrite with them.
* `simp only [Vector.getElem_ofFn]` to read a slot of a vector built by
  `Vector.ofFn`.
* `simp only [h, ↓reduceIte]`. The odd-looking `↓reduceIte` tells `simp` to
  decide an `if` whose condition it can now settle. `↓reduceDIte` does the
  same for an `if h : ...`. Plain `simp [h]` does this without being told.
* `omega`, for facts like `i - 1 < n` when `i < n`, and
  `t - 1 - (i - 1) = t + 1 - 1 - i` when `i` is not 0 and `i < t + 1`.
  Subtraction on natural numbers stops at zero, so `omega` needs to know the
  inequalities. Give them to it as hypotheses.

# Exercises

*Prove.* `Exercises/Blocks/Basic.lean`, then
`Exercises/Blocks/ShiftRegister.lean`.

*Specify.* Define a register with an enable input. Its input is a pair of a
Boolean and a value, and it keeps its old contents on cycles where the
Boolean is `false`. Start from this and fill in the step:

```
def enRegister {α : Type} (reset : α) : Block α (Bool × α) α where
  init := reset
  step s x := sorry
```

Test it with `trace`. Then define, by recursion on the cycle, the function
`held inp t` that it should be holding at cycle `t`, test that, and prove
`(enRegister reset).stateAt inp t = held reset inp t`. Writing `held` is the
exercise. If the proof is `rfl` in both cases, look again: you may have
copied the block into the specification.

*Challenge.* Define the composition of two blocks, in which the output of the
first feeds the input of the second. Its state is a pair of states. Prove
that two shift registers of depths `m` and `n` in a row have the same output
as one of depth `m + n`. You will need a lemma that says what the composed
block's output is in terms of the two blocks' `outAt`.

# Hints

For `Block.stateAt_mapIn`: induction on `t`. In the step case rewrite both
sides with `stateAt_succ`, rewrite with the induction hypothesis, and finish
with `rfl`.

For `sumTo_congr`: induction on `n`. Unfold `sumTo`. You need the hypothesis
`h` twice: once for the terms below `n`, to use the induction hypothesis, and
once for the term `n` itself.

For `shiftRegister_stateAt`: induction on `t` generalizing `i`. The zero case
is `simp` with the two lemmas about `init`. In the step case, after taking a
step, split on whether `i = 0`. If it is, `simp` finishes. If not, use the
induction hypothesis at `i - 1`, then split on whether `i < t + 1`.

For `shiftRegister_outAt`: split on whether `0 < n`. If so the output is slot
`n - 1`, and `shiftRegister_stateAt` says what is there. If not, `n` is 0;
`subst` it and `simp`.

# Checkpoint

`lake build Exercises.Blocks.Basic Exercises.Blocks.ShiftRegister` prints no
`sorry` warning. You can explain, without looking, why the induction needs
the statement about every slot.
