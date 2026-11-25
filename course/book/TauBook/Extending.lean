import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Extending the machine" =>
*Time:* as much as you like. Each exercise is from an hour to a few days.

The best test of whether you understand a system is to change it. This
chapter is homework: add something to tau-tpu, and keep every theorem true.

# Why this works as homework

Every feature takes the same path through the repository, and Lean tells you
when you have left a step out. Add a constructor to a type and build: every
function that matches on that type stops compiling, with a message that
names the missing case. Fix those and build again: every proof by cases on
that type stops, naming the missing case. When the build is quiet, the
feature is in and the end-to-end theorem covers it.

Three messages do most of the guiding.

* `Missing cases: ...` in a definition: a `match` needs a new line.
* `Alternative 'foo' has not been provided` in a proof: a `cases ... with`
  needs a new case.
* `Fields missing: 'foo'`: a structure got a new field and a value of it is
  built here.

# The path of a feature

In dependency order. A small feature touches only the first few.

1. `Tau/Data/Word.lean`: what it does to a lane or a word.
2. `Tau/Isa/Op.lean`: its name as an operation, and its meaning in `wordSem`.
3. `Tau/Isa/Instr.lean` and `Tau/SliceLevel/Machine.lean`: its instruction,
   and what `exec` does with it.
4. `Tau/Proofs/SliceLevel/Map.lean`: the machine still does not look at its
   values.
5. `Tau/IR/Kernel.lean`, `Tau/IR/Expr.lean` and their proofs, if kernels can
   say it.
6. `Tau/IR/Placed.lean` and its proof: the placed form.
7. `Tau/CellLevel/Machine.lean` and `Tau/Proofs/CellLevel/Refine.lean`: how
   the slice does it with blocks, and that this is the same thing.
8. `Tau/Sim/Json.lean`: reading it from a file.
9. `compiler/`: the dialect and the passes. Optional: without it, write your
   test programs by hand as Lean values, as `tests/TauTest/Features.lean`
   does.
10. A test in `tests/TauTest/`, and an example under `examples/`.

Work on a branch: `git switch -c my-feature`. While you are half way,
`lake build` fails; that is the method working.

# Four sizes, with a worked example of each

The repository already contains one feature of each size. Read how each was
done before doing your own. `git log` and `git show` on the files above show
the changes.

*An operation.* `neg` negates every lane. It is a constructor of `UnOp`, a
line in `UnOp.kind`, and a line in `wordSem`. Nothing else in Lean changed:
no instruction, no proof. The machine, the kernels and the checker were
written for any set of operations, so they already handle it. That is what
writing against `Sem` bought.

*An instruction.* `seed` replaces the matrix slice's accumulator by a word
from a stream. It is a constructor of `Instr`, a case in `exec`, and one new
case in each of `exec_map`, `PInstr.exec_map` and `cellExec_abs`. At the cell
level it needed the accumulator block to accept a new command, `AccIn.load`,
and one small lemma, `macLanes_load`.

*State.* Stored columns gave the matrix slice a memory of its own: a new
field in `Slice`, a new field in `Cell`, two instructions (`install`,
`macw`), and a new line in the abstraction function `Cell.abs`. The compiler
uses it without any kernel asking: when a matrix is multiplied twice,
`tau-place` installs it once. The checker accepted that optimization without
being told about it, because it is the machine run on names.

*A block.* Repeats needed a new block with a real invariant, the repeater,
and changed the invariant of the refinement proof from "all clocks are
equal" to "all repeaters are in step".

# Homework

Do them in order of size. Each has a test for being done.

## An operation

Pick one.

* `not`: the bitwise complement of every lane.
* `sar k`: divide every lane by `2 ^ k`, rounding down, with no clamping.
* `ge`: lane by lane, 1 where the first is at least the second.
* `swapHalves`: on the rearrangement slice, exchange the lower and upper
  half of the lanes.

Steps: `Tau/Data/Word.lean` if it needs a helper, then `Tau/Isa/Op.lean`,
then `Tau/Sim/Json.lean`. Add `#guard` lines to `tests/TauTest/Features.lean`
with inputs for which you worked the answer out by hand, including a
negative lane.

You are done when `lake build Tau TauTest` succeeds. Notice that you did not
touch a proof, and say why.

Then state one fact about your operation on a single lane and prove it with
`bv_decide`, in the style of `Tau/Proofs/Data/Lane.lean`.

With the compiler: add the operation to
`compiler/include/tau/Dialect/TauOps.td` and to `isUnaryKernelOp` or
`isBinaryKernelOp` in `compiler/lib/Target/Chip.cpp`, write an example
kernel with its buffers, and run `scripts/check-examples.sh`.

## An instruction

Pick one.

* `clear`: the matrix slice sets its accumulator to zero and outputs
  nothing.
* `peek dst`: the matrix slice puts its accumulator on a stream without
  clearing it.
* `forward src dst`: the vector slice passes a word from one stream to
  another unchanged. This lets a word turn round.

Steps 3, 4, 6, 7 and 8 of the path. For each proof, find the existing case
that is most like yours and copy its shape.

You are done when `lake build Tau TauTest` succeeds, with a hand-written
program in `tests/TauTest/Features.lean` that uses your instruction, run on
both machines as `run` does there. `#print axioms Tau.end_to_end` must still
list three axioms.

For `forward`: before you start, decide whether it needs a new instruction
at all. An operation that returns its operand unchanged would do the same
job with less work. What would be lost?

## State

* A second accumulator in the matrix slice. `mac` and `emit` take a number,
  0 or 1, saying which one. Two products can then be in progress at once.
* A held operand in the vector slice: `hold src` keeps a word, and a new
  two-word instruction uses the held word as its second operand. A constant
  can then be used many times without being sent many times.

Here the abstraction function changes, and so does `State.init_map` and
`CellState.init_abs`. Decide first what the cell level builds the new state
from. For the second accumulator, the answer is a second row of `mac` cells.

You are done as for an instruction, with a test that would fail if the two
accumulators, or the held word and the stream, were confused.

## Timing

One project, for after everything else.

Today every instruction of a slice spends the same number of cycles in it.
Give each operation its own delay. Two results can then leave a slice on the
same cycle, which the machine has no rule for.

* Decide the rule. A trap is the simplest.
* At the slice level the pipe becomes a row of slots that a result can enter
  part way along.
* At the cell level you need a new block: a shift register with several
  inputs. Write it, and its theorem, in the style of the block chapters
  before using it.
* The scheduler in `compiler/lib/Target/Schedule.cpp` needs the new delays,
  and `tau-place` needs to avoid the new conflict.

The chapters on the shift register, the slice-level machine and the
cell-level machine each come back once in this project. If you finish it you
have done, alone, what the course did with you.

# Checkpoint

One feature of each of the first three sizes, built, tested, and covered by
the end-to-end theorem.
