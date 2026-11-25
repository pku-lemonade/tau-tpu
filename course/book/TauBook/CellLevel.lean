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

*Source:* `course/architecture-manual.md`, section 4.

*Read:* `Tau/CellLevel/Machine.lean`.

*Proofs:* `Tau/Proofs/CellLevel/Refine.lean`. For reading. It is the largest
proof of the development.

*Time:* one day.

# State it first

Section 4 of the manual ends with the sentence "A chip built this way
behaves exactly as section 3 says."

Before you read on, write that sentence as a Lean proposition, in
`course/Work/`. `cellExecute` in `Tau/CellLevel/Machine.lean` runs the
machine built from blocks, and `execute` runs the one you know. Decide what
"exactly" means: for which chips, which programs, how many cycles, which
starting memory? And what should hold when the simple machine traps?

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

# The statement

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

1. Read section 4 of the manual and state its last sentence, as above.
2. Read `Tau/CellLevel/Machine.lean` beside the slice-level machine. Every
   field of `Cell` is the state of a block you specified.
3. Compare your statement with `cellExecute_eq`.
4. In `Tau/Proofs/CellLevel/Refine.lean`, read `Cell.abs`, `Cell.InSync` and
   `Synced`, then the statements of `CellState.step_abs` and
   `CellState.run_abs`, then the outline of `cellExecute_eq`. Draw the
   square.
5. Read the statements of `toList_shift`, `last_shift`, `macLanes_add` and
   `cellRepeater_step`. Each says that a block you specified does what the
   simple machine does in one line. They are where your earlier chapters are
   used.

# Exercises

*State.* The last sentence of section 4, as above.

*State.* The cell-level machine does not use the systolic array. Design a
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
neither false nor impossible to satisfy. Then give the proof to an agent.

*Read a proof.* Answer from `Refine.lean`, without running anything. What
does the abstraction function forget? What is the invariant, in one
sentence? In which lemma is the invariant used, and in which is it shown to
hold again? Which lemmas would have to change if the pipe were built from
something other than a shift register?

*Questions.* Section 4 is four lines of a table. List what somebody building
the chip from it would have to ask. One to start you off: the simple machine
has one cycle count, and section 4 gives each slice a repeater of its own.
What keeps them in step?

*Claims.* Add to `course/Work/Claims.md` a row for each thing you wrote in this
chapter: what it is, and how it stands.

*Challenge.* Open the streams. Replace each stream by a row of depth-one
shift registers with a way for a slice to overwrite a slot, define the
abstraction to lists, and state the refinement.

# Checkpoint

Your statement of refinement has the same content as `cellExecute_eq`, or
you can say where it differs and which is better. You can draw the square
for `CellState.step_abs` and say what the invariant is, where it is used and
where it is restored.
