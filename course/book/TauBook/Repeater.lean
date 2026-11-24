import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The repeater" =>
*Terms to look up:* down counter, loop counter.

*Read:* `Tau/Blocks/Repeater.lean`.

*Solutions, not to be opened yet:* `Tau/Proofs/Blocks/Repeater.lean`.

*Time:* two days.

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

# What to prove

That the counting registers issue exactly what the specification says, at
every cycle, for every program:

```lean
example (prog : List (Entry Nat)) (inp : Signal Unit) (t : Nat) :
    (repeater prog).outAt inp t = prog.filterMap fun e => e.dueAt t :=
  repeater_outAt prog inp t
```

This is a small refinement proof, the first in the course: a description
with state against a description without. The chapter on the cell-level
machine does the same for the whole chip, and uses this theorem to do it.

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

1. Read `Tau/Blocks/Repeater.lean`. In your scratch file define an entry of
   your own and evaluate `timeAt`, `dueAt` and `slotAt` at several cycles.
2. On paper, write the registers of `readThree` at cycles 0 to 7 and, next
   to each, the `k` of the invariant.
3. In `Exercises/Blocks/Repeater.lean` do `Entry.timeAt_lt`, then
   `Entry.dueUpTo_none` and `Entry.dueUpTo_some`. Each is a short induction.
4. Do `Entry.slotAt_spec`. Use your table from step 2 to see what `k` and the
   wait should be in each branch.
5. Do `Entry.step_slotAt`, which reads the output off the invariant.
6. Do the three theorems about the whole repeater. They are short.

# Lean you will need

* A statement that starts `∃ k w, ...` is proved by giving the `k` and the
  `w`: `refine ⟨k + 1, e.gap, ?_, ?_, ?_, ?_⟩` gives them and leaves the four
  facts as goals. A hypothesis of that form is taken apart with
  `obtain ⟨k, w, hk, hs, hlt, heq⟩ := ih`.
* `by_cases hdone : e.repeats + 1 - k = 0`, then inside it
  `by_cases hw : w = 0`, to follow the branches of `Slot.step`.
* `omega`, given the right hypotheses. Before calling it, bring the facts it
  needs into the context with `have := hlt i hi`.

# Exercises

*Guided.* `Exercises/Blocks/Repeater.lean`.

*Open.* The specification defines the time of issue `i` by recursion. State
and prove the closed form:

```
theorem Entry.timeAt_eq {α : Type} (e : Entry α) (i : Nat) :
    e.timeAt i = e.time + i * (e.gap + 1) := by
  sorry
```

`omega` does not multiply two variables, so the step case needs a rewrite
with a lemma about `(i + 1) * n` first. Find it with `exact?` or `rw?`. Then
say, in a comment, which of the two definitions of `timeAt` you would rather
have in the specification, and why the file uses the recursive one.

*Open.* Define an entry that repeats for ever: no `repeats` field, and a slot
with no `left` register. Write its specification and its step function, and
state the invariant. It is simpler than the one in this chapter. Prove it.

*Challenge.* Define a repeater whose entries can nest: repeat a group of
items. Decide what the registers are before writing any Lean.

# Hints

For `Entry.timeAt_lt`: induction on `j`. In the step case either `i = j` or
`i < j`; in the second, use the induction hypothesis.

For `Entry.dueUpTo_some`: induction on `n`. If `k = n + 1` the first `if` is
taken. Otherwise the time of issue `n + 1` is later than the time of issue
`k`, by `Entry.timeAt_lt`, so it is not `t`, and the induction hypothesis
applies.

For `Entry.slotAt_spec`, the three branches:

* nothing left: give the same `k` and `w`;
* wait over: give `k + 1` and `e.gap`. The fact about earlier issues needs a
  case split on whether the issue is `k` itself;
* still waiting: give `k` and `w - 1`.

For `repeater_step`: `stepSlots_map` turns stepping a mapped list into a map.
The outputs are then a `filterMap` of a function that `Entry.step_slotAt`
says is `dueAt`.

# Checkpoint

`lake build Exercises.Blocks.Repeater` prints no `sorry` warning. You can say
what an invariant is, and why this one mentions a number the registers do not
hold.
