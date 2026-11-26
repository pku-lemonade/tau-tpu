import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The repeater" =>
*Terms to look up:* down counter, loop counter.

*Source:* `docs/Machine.md`, section 2.7.

*Specify:* `course/Specify/Blocks/Repeater.lean`.

*Read, after you have specified it:* `spec/Tau/Blocks/Repeater.lean`.

*Proofs:* `spec/Tau/Proofs/Blocks/Repeater.lean`. Two short ones are exercises.
The invariant is for reading.

*Time:* two days.

# Specify it first

Stop reading here. Open section 2.7 of `Machine.md` and
`course/Specify/Blocks/Repeater.lean`, and follow the steps at the top of the file.

This one is harder than the memory, because the doc describes the
repeater twice: by what it issues on each cycle, and by the registers it is
built from. You may write either. The "State" step asks for the other one,
and for the statement that the two agree. Come back when the report says
that all rows agree.

# The idea

The sequencer of the last chapter but one could issue each item once. Real
programs repeat: read eight consecutive addresses on eight consecutive
cycles. A _repeater_ is a sequencer whose entries can do that.

{docstring Tau.Entry}

This entry issues the items 5, 6, 7 on cycles 2, 4, 6:

```lean
def readThree : Entry Nat :=
  { time := 2, repeats := 2, gap := 1, first := 5, next := (· + 1) }
```

There are two ways to say what a repeater does, and this chapter is about
the difference between them.

# What: a specification with no state

Issue number `i` happens at cycle `timeAt i` and carries `itemAt i`. Both are
defined by recursion on `i`. Read them in the file.

```lean
example : (List.range 3).map readThree.timeAt = [2, 4, 6] := by decide
example : (List.range 3).map readThree.itemAt = [5, 6, 7] := by decide
```

{docstring Tau.Entry.dueAt}

```lean
example : readThree.dueAt 4 = some 6 := by decide
example : readThree.dueAt 5 = none := by decide
```

Nothing here says how hardware would do it. To evaluate `dueAt` at cycle `t`
you compare `t` with the time of every issue. A circuit that did that would
need a comparator for every issue of every entry.

# How: three registers per entry

Real hardware counts down.

{docstring Tau.Slot}

{docstring Tau.Slot.step}

The registers never see the cycle number. Each cycle they look only at
themselves. Here they are for `readThree` at the start of cycle 3, one cycle
after the first issue: two issues left, one cycle to wait, and the next item
is 6.

```lean
example :
    ((readThree.slotAt 3).left, (readThree.slotAt 3).wait, (readThree.slotAt 3).cur)
      = (2, 1, 6) := by
  decide
```

{docstring Tau.repeater}

```lean
example :
    (repeater [readThree]).trace (fun _ => ()) 8
      = [[], [], [5], [], [6], [], [7], []] := by
  decide
```

# The statement

That the counting registers issue exactly what the specification says, at
every cycle, for every program:

```lean
example (prog : List (Entry Nat)) (inp : Signal Unit) (t : Nat) :
    (repeater prog).outAt inp t = prog.filterMap fun e => e.dueAt t :=
  repeater_outAt prog inp t
```

This is a small refinement proof, the first in the course: a description
with state against a description without. The chapter on the cell-level
machine does the same for the whole machine, and uses this theorem to do it.

The work is in one lemma about one entry, `Entry.slotAt_spec`. It says what
the registers hold at every cycle. In words: at the start of cycle `t` some
number `k` of issues have been made, and

* `left` is the number of issues remaining,
* `cur` is the item of issue `k`,
* every issue before `k` had its time before `t`,
* if issue `k` is still to come, `wait` is the number of cycles until its
  time.

A statement like this is called an _invariant_. It is proved by induction on
the cycle, and the step case has three branches, one for each branch of
`Slot.step`: nothing left, wait over, still waiting.

Notice that the invariant talks about `k`, which is not stored anywhere. The
registers hold `left`, and `k` is the total minus `left`. Proofs about state
often need a quantity that the state does not hold directly. Here the
statement says "there is a `k`", and the proof supplies it.

# How to work through it

1. Specify the repeater from the doc, as above.
2. Read `spec/Tau/Blocks/Repeater.lean`. In your scratch file define an entry of
   your own and evaluate `timeAt`, `dueAt` and `slotAt` at several cycles.
3. Which of the two descriptions did you write, the one with registers or the
   one without? The repository has both, and the theorem says they agree.
4. On paper, write the registers of `readThree` at cycles 0 to 7 and, next
   to each, the `k` of the invariant. This is how you read an invariant
   somebody else proved: check it on one run.
5. Read the statement and the outline of `Entry.slotAt_spec` in
   `spec/Tau/Proofs/Blocks/Repeater.lean`. Do not work through its steps.
6. In `Prove/Blocks/Repeater.lean`, prove `repeater_stateAt` and
   `repeater_outAt`. Everything above them is given.

# Exercises

*Specify.* `course/Specify/Blocks/Repeater.lean`.

*State.* `IssuesWhatIsDue` in that file: the description without registers,
and the statement that the block agrees with it.

*State.* The specification defines the time of issue `i` by recursion. State
the closed form:

```
theorem Entry.timeAt_eq {α : Type} (e : Entry α) (i : Nat) :
    e.timeAt i = e.time + i * (e.gap + 1) := by
  sorry
```

Give the proof to an agent, or do it: `omega` does not multiply two
variables, so the step case needs a rewrite with a lemma about `(i + 1) * n`
first. Then say, in a comment, which of the two definitions of `timeAt` you
would rather have in the specification, and why the file uses the recursive
one.

*Specify.* Define an entry that repeats for ever: no `repeats` field, and a
slot with no `left` register. Write the description without registers, the
step function, and the invariant that connects them. It is simpler than the
one in this chapter.

*Prove.* `repeater_stateAt` and `repeater_outAt` in
`Prove/Blocks/Repeater.lean`.

*Questions.* Section 2.7 leaves at least three things open.

*Claims.* Add to `course/Work/Claims.md` a row for each thing you wrote in this
chapter: what it is, and how it stands.

*Challenge.* Define a repeater whose entries can nest: repeat a group of
items. Decide what the registers are before writing any Lean.

# Hints

For `repeater_stateAt`: induction on `t`. In the step case, rewrite with
`Block.stateAt_succ`, the induction hypothesis and `repeater_step`.

For `repeater_outAt`: unfold `Block.outAt`, then rewrite with
`repeater_stateAt` and `repeater_step`.

# Checkpoint

The report says that all rows agree. `lake build Prove.Blocks.Repeater`
prints no `sorry` warning. You can say what an invariant is, and why this one
mentions a number the registers do not hold.
