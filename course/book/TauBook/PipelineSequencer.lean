import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Pipeline and sequencer" =>
*Terms to look up:* pipelining, latency, program counter, static scheduling.

*Read:* `Tau/Blocks/Pipeline.lean`, `Tau/Blocks/Sequencer.lean`.

*Solutions, not to be opened yet:* `Tau/Proofs/Blocks/Pipeline.lean`,
`Tau/Proofs/Blocks/Sequencer.lean`.

*Time:* one day.

# The pipeline

A pipeline computes a function and delivers the result a fixed number of
cycles later.

{docstring Tau.pipeline}

```lean
example : (pipeline 2 (· * 2) 0).trace (fun t => t + 1) 5 = [0, 0, 2, 4, 6] := by
  decide
```

`(· * 2)` is short for `fun x => x * 2`.

Like the MAC, a pipeline is an existing block with a function in front, so
its theorem is built from `Block.outAt_mapIn` and the shift register theorem
with no new induction:

```lean
example (d : Nat) (f : Nat → Nat) (inp : Signal Nat) (t : Nat) :
    (pipeline d f 0).outAt inp t = if d ≤ t then f (inp (t - d)) else 0 :=
  pipeline_outAt d f 0 inp t
```

This theorem is the timing contract of every slice in tau-tpu. A slice is a
pipeline: an instruction issued on cycle `t` has its result ready on cycle
`t + d`, where `d` depends on the kind of slice and on nothing else.

# The sequencer

A sequencer holds a program, a list of items each with a cycle, and on each
cycle outputs the items due.

{docstring Tau.sequencer}

{docstring Tau.dueAt}

```lean
example :
    (sequencer [(1, "read"), (3, "add"), (3, "write")]).trace (fun _ => ()) 4
      = [[], ["read"], [], ["add", "write"]] := by
  decide
```

The input type is `Unit`, the type with one value `()`. A sequencer takes no
information from outside. Its state is the cycle count.

The sequencer is where static scheduling lives. Nothing that happens while
the chip runs can change when an instruction is issued.

This sequencer needs no real state: it compares a cycle count with the times
in the program. The chapter after next builds one that has state, and that is
the one tau-tpu uses.

# How to work through it

1. Read both definition files.
2. Do `Exercises/Blocks/Pipeline.lean`. One proof of two lines.
3. Do `Exercises/Blocks/Sequencer.lean` without looking at any hint. The
   state theorem is about as small as an induction can be. If you can do it
   alone, the first week has worked.

# Exercises

*Guided.* `Exercises/Blocks/Pipeline.lean`, `Exercises/Blocks/Sequencer.lean`.

*Open.* A sequencer can be asked to issue two items on the same cycle, as in
the example above. Write a function that decides whether a program ever does
that:

```
def noClash {α : Type} (prog : List (Nat × α)) : Bool := sorry
```

Then state the theorem that connects your function to the sequencer: if
`noClash prog = true`, then for every cycle `t` the list `dueAt prog t` has
at most one element. Prove it if you can. You have just written a small
checker and its soundness statement. The chapter on the checker does this for
the whole machine.

*Challenge.* Define `mapOut` for blocks, the counterpart of `mapIn`, and
prove its two lemmas. Then define a pipeline whose function is applied after
the delay instead of before, and prove it has the same output as `pipeline`.

# Hints

For `pipeline_outAt`: `unfold pipeline`, then rewrite with
`Block.outAt_mapIn` and `shiftRegister_outAt`.

For `sequencer_stateAt`: induction on `t`; `rw [Block.stateAt_succ, ih]`;
`rfl`.

For `sequencer_outAt`: unfold `Block.outAt`, rewrite with
`sequencer_stateAt`, `rfl`.

# Checkpoint

`lake build Exercises.Blocks.Pipeline Exercises.Blocks.Sequencer` prints no
`sorry` warning, and you did the sequencer proofs without help.
