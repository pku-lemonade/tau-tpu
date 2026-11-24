import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Memory" =>
*Terms to look up:* random-access memory, address, read port, write port.

*Files:* `Tau/Blocks/Memory.lean`, `Tau/Proofs/Blocks/Memory.lean`.

# The idea

A memory is a row of words. On each cycle it reads one word, writes one word,
or does nothing.

{docstring Tau.MemIn}

{docstring Tau.memory}

# What to prove

What does a read return? The value most recently written to that address, or
the starting value if the address has never been written. To state this you
need a function that finds the most recent write:

{docstring Tau.lastWrite}

`lastWrite` is part of the specification. It is not a helper for the proof.
It lives in the definitions tree, and a reader has to check that it means
what its name says. Whenever a theorem mentions a function you defined, the
theorem is only as good as that definition.

The proof is an induction on the cycle with a case split on the command. The
only real case is a write, which splits again on whether the write was to the
address in question.

# Lean you will need

* `split`, which breaks a goal containing a `match` or an `if` into cases.
* `rename_i`, which names the hypotheses that `split` introduces.
* Searching the library. The proof needs a fact about reading a vector after
  writing to it. You will not guess its name. Type `exact?` where the fact is
  needed, or search with a pattern in `#loogle`.

# Exercises

*Guided.* `Exercises/Blocks/Memory.lean`.

*Open.* This memory reads and writes in the same cycle it is asked to. Define
a memory whose reads take one cycle to come back, by putting a pipeline of
depth one behind this one, and state its read theorem. Then say, in a comment,
what a read returns if the same address is written on the cycle in between.
Check your claim against your definition by running it.

*Challenge.* A memory with two ports can take two commands per cycle. Define
it, decide what happens when both ports write the same address on the same
cycle, and prove a read theorem. There is more than one defensible answer for
the conflict. tau-tpu avoids the question by giving each memory slice one
instruction per cycle.

# Checkpoint

You can specify a component with internal state that is addressed, and you
know that helper functions in a statement are part of what must be trusted.
