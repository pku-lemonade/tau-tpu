import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Pipeline and sequencer" =>
*Terms to look up:* pipelining, latency, program counter, static scheduling.

*Source:* `course/architecture-manual.md`, sections 2.4 and 2.6.

*Specify:* `course/Specs/Pipeline.lean`, `course/Specs/Sequencer.lean`.

*Read, after you have specified them:* `Tau/Blocks/Pipeline.lean`,
`Tau/Blocks/Sequencer.lean`.

*Proofs:* `Tau/Proofs/Blocks/Pipeline.lean`,
`Tau/Proofs/Blocks/Sequencer.lean`. All of them are exercises.

*Time:* one day.

# Specify them first

These are your first two specifications. Stop reading here.

Open sections 2.4 and 2.6 of the manual, and the two files under
`course/Specs/`. Follow the steps at the top of each file: choose the state,
write the block, read the report, list what the manual does not say. Come
back when both reports say that all rows agree.

The rest of this chapter shows the definitions in the repository. They are
one way to say what the manual says. Yours is another.

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

1. Specify the pipeline and the sequencer from the manual, as above.
2. Read both definition files in `Tau/Blocks/`. Compare the states. The
   repository builds the pipeline out of the shift register and `mapIn`, so
   its state is the shift register's. The state of its sequencer is the
   cycle count. Were yours the same? If not, are both right?
3. Compare your two statements with `pipeline_outAt` and `sequencer_outAt`.
4. Do `Exercises/Blocks/Pipeline.lean`. One proof of two lines.
5. Do `Exercises/Blocks/Sequencer.lean` without looking at any hint. The
   state theorem is about as small as an induction can be. If you can do it
   alone, the first week has worked.

# Exercises

*Specify.* `course/Specs/Pipeline.lean` and `course/Specs/Sequencer.lean`.

*State.* `OutputIsDelayed` and `IssuesWhatIsDue` in those two files.

*Specify and state.* A sequencer can be asked to issue two items on the same
cycle, as in the example above. Write a function that decides whether a
program ever does that:

```
def noClash {α : Type} (prog : List (Nat × α)) : Bool := sorry
```

Then state the theorem that connects your function to the sequencer: if
`noClash prog = true`, then for every cycle `t` the list `dueAt prog t` has
at most one element. Give the proof to an agent, or prove it yourself. You
have just written a small check and the statement that it can be trusted.
The chapter on the checker does this for the whole compiler.

*Prove.* `Exercises/Blocks/Pipeline.lean`, `Exercises/Blocks/Sequencer.lean`.

*Questions.* Sections 2.4 and 2.6 leave at least four things open. Find them
before you look at the `Decisions` tables.

*Claims.* Add to `course/Work/Claims.md` a row for each thing you wrote in this
chapter: what it is, and how it stands.

*Challenge.* Define `mapOut` for blocks, the counterpart of `mapIn`, and
state its two lemmas. Then define a pipeline whose function is applied after
the delay instead of before, and state that it has the same output as
`pipeline`.

# Hints

For `pipeline_outAt`: `unfold pipeline`, then rewrite with
`Block.outAt_mapIn` and `shiftRegister_outAt`.

For `sequencer_stateAt`: induction on `t`; `rw [Block.stateAt_succ, ih]`;
`rfl`.

For `sequencer_outAt`: unfold `Block.outAt`, rewrite with
`sequencer_stateAt`, `rfl`.

# Checkpoint

Both reports say that all rows agree. `lake build Exercises.Blocks.Pipeline
Exercises.Blocks.Sequencer` prints no `sorry` warning, and you did the
sequencer proofs without help. `course/Work/Questions.md` has four more
entries, and `course/Work/Claims.md` has a row for each thing you wrote.
