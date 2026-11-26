import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Memory" =>
*Terms to look up:* random-access memory, address, read port, write port.

*Source:* `docs/Machine.md`, section 2.5.

*Specify:* `course/Specify/Memory.lean`.

*Read, after you have specified it:* `spec/Tau/Blocks/Memory.lean`.

*Proofs:* `spec/Tau/Proofs/Blocks/Memory.lean`. One of them is an exercise.

*Time:* one day.

# Specify it first

Stop reading here. Open section 2.5 of `Machine.md` and
`course/Specify/Memory.lean`, and follow the steps at the top of the file.
Come back when the report says that all rows agree.

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

# The statement

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

1. Specify the memory from the doc, as above.
2. Read `spec/Tau/Blocks/Memory.lean`. Evaluate `lastWrite` on a signal of your
   own, including one with no write to the address.
3. Compare your statement with `memory_outAt_read`. Did you need a function
   like `lastWrite`? Does your statement have the hypothesis that the
   address is valid? Without it the statement is false: this is the third
   statement of `course/Specify/Repair.lean`.
4. In `Prove/Blocks/Memory.lean`, read the statement and the outline of
   `memory_stateAt`, which is given. Then prove `memory_outAt_read` from it.

# Exercises

*Specify.* `course/Specify/Memory.lean`.

*State.* `ReadsLastWrite` in that file.

*Specify.* This memory answers a read in the same cycle. Define a memory whose
reads come back one cycle later, by putting a pipeline of depth one behind
this one. You will need a way to chain two blocks; write it for this one
case. State its read theorem. Then say, in a comment, what a read returns if
the same address is written on the cycle in between, and check your claim by
running your definition. The doc would have to say this too.

*Prove.* `memory_outAt_read` in `Prove/Blocks/Memory.lean`.

*Questions.* Section 2.5 leaves at least three things open.

*Claims.* Add to `course/Work/Claims.md` a row for each thing you wrote in this
chapter: what it is, and how it stands.

*Challenge.* A memory with two ports can take two commands per cycle. Define
it, decide what happens when both ports write the same address on the same
cycle, and state a read theorem. There is more than one defensible answer for
the conflict, which makes it a question for the architect. tau-tpu avoids it
by giving each memory slice one instruction per cycle.

# Hints

For `memory_outAt_read`: unfold `Block.outAt`, rewrite with `memory_step` and
the hypothesis that the command is a read, then `simp` with `ha` and
`memory_stateAt`.

# Checkpoint

The report says that all rows agree. `lake build Prove.Blocks.Memory`
prints no `sorry` warning. You can say why `lastWrite` belongs to the
specification and is not a helper for the proof.
