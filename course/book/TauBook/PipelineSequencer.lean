import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Pipeline and sequencer" =>
*Terms to look up:* pipelining, latency, program counter, static scheduling.

*Files:* `Tau/Blocks/Pipeline.lean`, `Tau/Blocks/Sequencer.lean`, and their
proof files.

# The pipeline

A pipeline computes a function and delivers the result a fixed number of
cycles later.

{docstring Tau.pipeline}

Like the MAC, it is an existing block with a function in front, so its
theorem is one line built from `Block.outAt_mapIn` and the shift register
theorem:

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

Its state is just the cycle count. The proof that the state at cycle `t` is
`t` is about as small as an induction can be. Do it without looking.

The sequencer is where static scheduling lives. Nothing that happens while
the chip runs can change when an instruction is issued.

# Exercises

*Guided.* `Exercises/Blocks/Pipeline.lean`, `Exercises/Blocks/Sequencer.lean`.

*Open.* A sequencer can be asked to issue two items on the same cycle. Write
a function that decides whether a program ever does that, and state the
theorem that connects your function to the sequencer's output. You have just
written a small checker and its soundness statement. Chapter 11 does this for
the whole machine.

*Challenge.* Define a `mapOut` for blocks, the counterpart of `mapIn`, and
prove its two lemmas. Then define a pipeline whose function is applied after
the delay instead of before, and prove it has the same output.

# Checkpoint

You have seen a timing contract stated as a theorem, and you can prove small
facts by induction without help.
