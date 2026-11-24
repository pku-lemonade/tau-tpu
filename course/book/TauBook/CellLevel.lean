import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The cell-level machine" =>
*Terms to look up:* refinement, simulation relation, abstraction function.

*Files:* `Tau/CellLevel/Machine.lean`, `Tau/Proofs/CellLevel/Refine.lean`.

# The idea

The slice-level machine treats each slice as one box. The cell-level machine
opens the box. A slice is now made of the blocks from chapters 2 to 7:

{docstring Tau.Cell}

The step function calls the step functions of those blocks. Read `cellExec`
and `cellStep` in `Tau/CellLevel/Machine.lean` next to `exec` and `stepSlice`
in `Tau/SliceLevel/Machine.lean`. They have the same shape. The differences
are these.

* The slice has its own clock, kept by a sequencer. There is no clock shared
  by the whole chip.
* Memory is a `memory` block holding a vector, not a list.
* Results wait in a `shiftRegister`.
* The matrix slice has one `mac` cell per lane.

# What to prove

That the two machines cannot be told apart:

```lean
example (cfg : Tau.Config) (prog : Program) (n : Nat) (image : List (List (Word 4))) :
    cellExecute cfg prog n image = execute (wordSem 4) cfg prog n image :=
  cellExecute_eq cfg prog n image
```

This kind of theorem is called a _refinement_. The detailed machine refines
the simple one: whatever the simple one promises, the detailed one delivers.

The proof uses an _abstraction function_, which maps a state of the detailed
machine to the state of the simple machine it represents by forgetting how a
slice is built.

{docstring Tau.Cell.abs}

The central lemma says that stepping and then abstracting gives the same
result as abstracting and then stepping. Draw it as a square with the two
machines' steps on the top and bottom and the abstraction function on the
sides. Everything else is induction on the number of cycles.

One thing the abstraction cannot forget for free is time. The simple machine
has one clock and the detailed one has a clock per slice. So the proof carries
an _invariant_: all the clocks are equal. Look for the hypothesis
`∀ c ∈ s.cells, c.clock = t` and see where it is used and where it is
re-established.

# Where the blocks come back

The lemmas `toList_shift` and `last_shift` say that one step of a shift
register, seen as a list, is the list operation the slice-level machine uses.
`macLanes_add` says that stepping every MAC cell computes `Word.mac`. These
are small facts, and they are the only places where the insides of the blocks
matter. The rest of the proof would not change if a block were replaced by a
different implementation with the same step behaviour.

# Exercises

*Guided.* `Exercises/CellLevel/Refine.lean`. Budget four days.

*Open.* The cell-level machine does not use the systolic array. Design a
matrix slice that does: decide what its instructions are, on which cycles the
columns must arrive, and what its delay is. Write down, as a Lean statement,
the refinement theorem your design would have to satisfy. You need not prove
it.

*Challenge.* Open the streams. Replace each stream by a row of depth-one
shift registers with a way for a slice to overwrite a slot, define the
abstraction to lists, and extend the refinement proof.

# Checkpoint

You can relate two models of one system at different levels of detail with an
abstraction function, and carry an invariant through an induction.
