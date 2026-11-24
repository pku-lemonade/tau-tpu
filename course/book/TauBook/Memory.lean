import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Memory" =>
*Terms to look up:* random-access memory, address, read port, write port.

*Read:* `Tau/Blocks/Memory.lean`.

*Solutions, not to be opened yet:* `Tau/Proofs/Blocks/Memory.lean`.

*Time:* two days.

# The idea

A memory is a row of words. On each cycle it reads one word, writes one word,
or does nothing.

{docstring Tau.MemIn}

{docstring Tau.memory}

Two library functions appear in the definition. `s[a]?` is slot `a` of `s` as
an `Option`: `some x` if `a` is in range and `none` if not. No evidence is
needed, because the answer covers both cases. `s.setIfInBounds a x` is `s`
with slot `a` replaced by `x`, or `s` unchanged if `a` is out of range.

# Try it

Write 7 to address 1 on cycle 0, then read address 1, then read address 0.
`#v[10, 11]` is a vector literal.

```lean
example :
    (memory 2 #v[10, 11]).trace
      (fun t => if t = 0 then .write 1 7 else if t = 1 then .read 1 else .read 0) 3
      = [none, some 7, some 10] := by
  decide
```

# What to prove

What does a read return? The value most recently written to that address, or
the starting value if the address has never been written. To state this you
need a function that finds the most recent write:

{docstring Tau.lastWrite}

Two writes to address 1, then nothing. The last write before cycle 3 is the
9:

```lean
example :
    lastWrite
      (fun t => if t = 0 then MemIn.write 1 7 else if t = 1 then .write 1 9 else .idle)
      1 3 = some 9 := by
  decide
```

The theorem about the contents:

```lean
example (init : Vector Nat 4) (inp : Signal (MemIn Nat)) (t a : Nat) (ha : a < 4) :
    ((memory 4 init).stateAt inp t)[a] = (lastWrite inp a t).getD init[a] :=
  memory_stateAt 4 init inp t a ha
```

`o.getD d` is the value inside the option `o`, or `d` if `o` is `none`.

`lastWrite` is part of the specification. It is not a helper for the proof.
It lives in the definitions tree, and a reader has to check that it means
what its name says. Whenever a theorem mentions a function you defined, the
theorem is only as good as that definition. That is why the example above is
there.

# How to work through it

1. Read `Tau/Blocks/Memory.lean`. Evaluate `lastWrite` on a signal of your
   own, including one with no write to the address.
2. Do `memory_stateAt` in `Exercises/Blocks/Memory.lean`. It is an induction
   on the cycle with a case split on the command. Two of the three cases are
   one line.
3. The write case splits again: was the write to the address `a` or to
   another address? You will need a library fact about reading a vector after
   `setIfInBounds`. Do not guess its name. Type `exact?` or `simp?` at the
   point where you need it and read what Lean suggests.
4. Do `memory_outAt_read`.

# Lean you will need

* `split` on a goal with a `match`, then `rename_i a x h` to give names to
  the variables and the hypothesis that `split` introduced without names. The
  names are assigned in order to the nameless items in the context, oldest
  first.
* `subst h`, when `h : a' = a`, replaces one variable by the other
  everywhere.
* `unfold lastWrite` to expose its `match`.

# Exercises

*Guided.* `Exercises/Blocks/Memory.lean`.

*Open.* This memory answers a read in the same cycle. Define a memory whose
reads come back one cycle later, by putting a pipeline of depth one behind
this one. You will need a way to chain two blocks; write it for this one
case if you did not do the challenge in the shift register chapter. State its
read theorem. Then say, in a comment, what a read returns if the same address
is written on the cycle in between, and check your claim by running your
definition.

*Challenge.* A memory with two ports can take two commands per cycle. Define
it, decide what happens when both ports write the same address on the same
cycle, and prove a read theorem. There is more than one defensible answer for
the conflict. tau-tpu avoids the question by giving each memory slice one
instruction per cycle.

# Hints

For `memory_stateAt`, the step case: `rw [Block.stateAt_succ, memory_step]`,
then `unfold lastWrite`, then `split`. In the idle and read cases the state
is unchanged: `simp` with the hypothesis from `split` and the induction
hypothesis.

In the write case, use `by_cases haa : a' = a`. If equal, `subst` and `simp`.
If not, the fact you need says that reading slot `a` after setting a
different slot gives the old value.

For `memory_outAt_read`: unfold `Block.outAt`, rewrite with `memory_step` and
the hypothesis that the command is a read, then `simp` with `ha` and
`memory_stateAt`.

# Checkpoint

`lake build Exercises.Blocks.Memory` prints no `sorry` warning. You found a
library lemma by asking Lean for it.
