import VersoManual
import Tau
import TauBook.SliceLevel
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The cell-level machine" =>
*Terms to look up:* refinement, simulation relation, abstraction function.

*Read:* `Tau/CellLevel/Machine.lean`.

*Solutions, not to be opened yet:* `Tau/Proofs/CellLevel/Refine.lean`.

*Time:* five days.

# The idea

The slice-level machine treats each slice as one box. The cell-level machine
opens the box. A slice is now made of the blocks from the first half of the
course:

{docstring Tau.Cell}

The step function calls the step functions of those blocks. Open
`Tau/CellLevel/Machine.lean` and `Tau/SliceLevel/Machine.lean` side by side
and compare `cellExec` with `exec`, and `cellStep` with `stepSlice`. They
have the same shape. The differences are these.

* Instructions are issued by a `repeater`, which counts down to each one in
  its own registers. No cycle count is shared by the whole chip.
* Memory is a `memory` block holding a vector, not a list.
* Results wait in a `shiftRegister`.
* The matrix slice has one `mac` cell per lane, and a second small `memory`
  for the columns it stores.

# Try it

On the small copy program the two machines give the same answer:

```lean
example :
    cellExecute tinyChip copyProgram 5 [[Word.ofInts [7, -3]], [], [Word.zero]]
      = execute (wordSem 2) tinyChip copyProgram 5
          [[Word.ofInts [7, -3]], [], [Word.zero]] := by
  rfl
```

# What to prove

That the two machines cannot be told apart, on any chip, program, number of
cycles and starting memory:

```lean
example (cfg : Tau.Config) (prog : Program) (n : Nat) (image : List (List (Word 4))) :
    cellExecute cfg prog n image = execute (wordSem 4) cfg prog n image :=
  cellExecute_eq cfg prog n image
```

This kind of theorem is called a _refinement_. The detailed machine refines
the simple one: whatever the simple one promises, the detailed one delivers.

The proof uses an _abstraction function_, which maps a state of the detailed
machine to the state of the simple machine it represents, by forgetting how a
slice is built.

{docstring Tau.Cell.abs}

The central lemma, `CellState.step_abs`, says that stepping and then
abstracting gives the same result as abstracting and then stepping. Draw it
as a square: the detailed step along the top, the simple step along the
bottom, and the abstraction function down both sides. The lemma says the two
ways round the square agree. Everything else is induction on the number of
cycles.

One thing the abstraction cannot forget for free is time. The simple machine
has one cycle count, and looks up what is due by that count. The detailed
machine has a repeater in every slice, each with its own registers. So the
proof carries an _invariant_: every slice's registers are the ones its
entries should have at the current cycle.

{docstring Tau.Cell.InSync}

{docstring Tau.Synced}

Find where the hypothesis `Synced prog t 0 s.cells` is used, in
`cellSteps_abs`, and where it is re-established for the next cycle, in
`cellSteps_synced`. An invariant always needs both: a place where it is
assumed and a place where it is shown to hold again.

# Where the blocks come back

The lemmas `toList_shift` and `last_shift` say that one step of a shift
register, seen as a list, is the list operation the slice-level machine
uses. `macLanes_add`, `macLanes_clear` and `macLanes_load` say that stepping
every MAC cell computes the word-level operation. `cellRepeater_step` says
that a repeater in step issues what the slice-level machine looks up; it is
`repeater_step` from the chapter on the repeater, applied.

These are small facts, and they are the only places where the insides of the
blocks matter. The rest of the proof would not change if a block were
replaced by a different implementation with the same step behaviour.

# How to work through it

1. Read `Tau/CellLevel/Machine.lean` beside the slice-level machine.
2. In `Exercises/CellLevel/Refine.lean`, do the five small facts about blocks
   first: `macLanes_add`, `macLanes_clear`, `macLanes_load`, `toList_shift`
   and `last_shift`.
3. Then `cellShift_abs` and `cellExec_abs`, which use them.
4. Then `cellRepeater_step`, `cellStep_abs` and `cellStep_sync`, about one
   slice.
5. Then `cellSteps_abs` and `cellSteps_synced`, about all slices, and the
   lemmas about one cycle and many cycles, in the order of the file.
6. Last, `cellExecute_eq`.

# Lean you will need

* `Vector.ext`, to prove two vectors equal by proving every slot equal:
  `apply Vector.ext; intro k hk`.
* `List.ext_getElem`, the same for lists.
* Carrying a hypothesis through an induction. `Synced` is defined by
  recursion on the list of slices, so for a list `c :: rest` the hypothesis
  is a pair: `obtain ⟨hc, hrest⟩ := h` gives the fact about `c` and the fact
  about `rest`, which is what the induction hypothesis wants.
* `exact congrArg Except.ok (lemma ...)`, to turn an equation `a = b` into
  `.ok a = .ok b`.

# Exercises

*Guided.* `Exercises/CellLevel/Refine.lean`.

*Open.* The cell-level machine does not use the systolic array. Design a
matrix slice that does, for products with a stored matrix. Do it for the
slice alone, as a block, so that nothing else has to be defined:

```
/-- What the slice is told on one cycle: nothing, or one coefficient per
cell. -/
abbrev MatIn (n : Nat) := Option (Vector Lane n)

def matSlice {n : Nat} (x : Vector Lane n) : Block (Vector Lane n) (MatIn n) Lane :=
  sorry

theorem matSlice_refines {n : Nat} (hn : 0 < n) (x : Vector Lane n)
    (A : Nat → Nat → Lane) (inp : Signal (MatIn n))
    (hfeed : sorry) (i : Nat) :
    (matSlice x).outAt inp (i + n) = sumTo 0 (fun k => A i k * x[k]?.getD 0) n := by
  sorry
```

Build `matSlice` from `systolicArray`. The exercise is `hfeed`: write the
condition on the input signal under which the conclusion holds. You are done
when the statement type-checks and you can argue, in a comment, that it is
neither false nor impossible to satisfy. Proving it is a challenge exercise.

*Challenge.* Open the streams. Replace each stream by a row of depth-one
shift registers with a way for a slice to overwrite a slot, define the
abstraction to lists, and extend the refinement proof.

# Hints

Every long proof has an outline in the exercise file, above its `sorry`.

For `macLanes_add`, `macLanes_clear` and `macLanes_load`: `apply Vector.ext`,
`intro k hk`, then `simp` with the definitions of `macLanes`, `Word.mac` or
`Word.zero`, `mac`, `Block.mapIn`, `accumulator` and `AccIn.map`.

For `toList_shift`: `apply List.ext_getElem`. The first goal is about
lengths. In the second, simplify both sides to an `if` on whether the index
is 0.

For `cellExec_abs`: `cases i`. Do `read` first. Each case is
`simp only [cellExec, exec, ...]`, then `split` once per `if`, then `cases`
on each read. The memory cases add `memory_step`, `Cell.abs` and the lemmas
that turn a vector operation into a list operation (`Vector.getElem?_toList`,
`Vector.length_toList`); `simp?` will name them. The matrix cases end with a
`macLanes` lemma.

For `cellRepeater_step`: rewrite the slots with the second half of the
hypothesis, then `repeater_step`.

For `cellStep_abs`: follow the outline. After `simp only` with
`cellRepeater_step`, split on the due instructions as in `stepSlice_map`.
`exact congrArg Except.ok (cellShift_abs c none)` closes the first case.

For `cellStep_sync`: unfold `cellStep` in the hypothesis and `split` it. In
the branches where the step succeeded, `cases h` identifies the result, and
the two halves of `InSync` are a fact about `c.clock + 1` and the first
component of `cellRepeater_step`.

For `cellSteps_abs` and `cellSteps_synced`: induction on the list of slices,
generalizing the position. Take the hypothesis apart with `obtain`.

For `CellState.run_abs`: induction on `n`, generalizing both the state and
the time. After a successful step, `CellState.step_synced` gives the
invariant for the next state.

For `synced_map_range'`: induction on the length; `List.range'_succ` unfolds
one element.

# Checkpoint

`lake build Exercises.CellLevel.Refine` prints no `sorry` warning. You can
draw the square for `CellState.step_abs` and say what the invariant is, where
it is used and where it is restored.
