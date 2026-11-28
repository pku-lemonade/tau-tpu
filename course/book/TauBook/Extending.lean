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

It is also the whole method of the course in one piece of work. For each
feature:

1. *Write its section of the docs first.* A paragraph, and a table if it has
   timing. Add it to `docs/Machine.md`, or to `docs/Programs.md` if
   it is something a program says.
2. *Specify it.* The definitions on the path below.
3. *Test it* against your table.
4. *List what your paragraph left open,* and what you decided.
5. *State* what should be true of it, or say which existing statement
   already covers it.
6. *Have the proofs repaired* by an agent, and review the change as the
   chapter "Writing a specification" shows. A feature of the first size
   should touch no proof at all. If the agent's change does, find out why.

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

1. `spec/Tau/Isa/Word.lean`: what it does to an element or a word.
   `spec/Tau/Isa/Value.lean` if it handles the words of a value in a way of
   its own.
2. `spec/Tau/Isa/Op.lean`: its name as an operation, and its meaning: what it
   does to one element (`UnOp.elem`, `BinOp.elem`) or, on the rearrangement
   slice, to one word (`UnOp.move`).
   `spec/Tau/Isa/Encode.lean`: its number in the image, both ways.
3. `spec/Tau/Isa/Instr.lean` and `spec/Tau/Machine/SliceLevel.lean`: its instruction,
   and what `exec` does with it. `spec/Tau/Machine/Issues.lean` if it issues a
   word in a new way. `spec/Tau/Isa/Encode.lean` again, for the instruction.
4. `spec/Tau/Proofs/Machine/SliceLevel.lean`: the machine still does not look at its
   values.
5. `spec/Tau/IR/Kernel.lean`, `spec/Tau/Check/Expr.lean` and their proofs, if kernels can
   say it.
6. `spec/Tau/IR/Placed.lean` and its proof: the placed IR.
   `spec/Tau/Check/Decides.lean`: the shape of a new instruction.
7. `spec/Tau/Machine/CellLevel.lean` and `spec/Tau/Proofs/Machine/CellLevel.lean`: how
   the slice does it with blocks, and that this is the same thing.
8. `spec/Tau/Tools/Json.lean`: reading it from a file.
9. `compiler/`: the dialect, the passes, and `encodeEntry` in
   `compiler/lib/Passes/Encode.cpp`. `compiler/python/tau/__init__.py`: a function for
   it that traces and one that computes. Optional: without them, write your
   test programs by hand as Lean values, as `spec/tests/TauTest/Features.lean`
   does.
10. A test in `spec/tests/TauTest/`, and an example under `examples/`.

Work on a branch: `git switch -c my-feature`. While you are half way,
`lake build` fails; that is the method working.

# Four sizes, with a worked example of each

The repository already contains one feature of each size. Read how each was
done before doing your own. `git log` and `git show` on the files above show
the changes.

*An operation.* `neg` negates every element. It is a constructor of `UnOp`,
a line in `UnOp.kind`, a line in `UnOp.elem`, and a number in
`spec/Tau/Isa/Encode.lean`. Nothing else in Lean changed: no instruction, no
proof. The machine, the kernels and the checker were written for any set of
operations, so they already handle it. That is what writing against `Sem`
bought. It works at every type for the same reason: `wordSem` puts the bytes
of an element together, applies `UnOp.elem`, and takes the result apart
again, whatever the operation. Only an operation whose result has another
type than its operand, as `requant` and `widen` have, needs a line more, in
`UnOp.out`.

*An instruction.* `product` puts the product of a matrix slice's installed
words with a word on a stream. It is a constructor of `Instr`, a case in
`exec`, and one new case in each of `exec_map`, `PInstr.exec_map` and
`cellExec_abs`. Its meaning is one operation of `Sem`, `matvec`, with one
law in `Sem.Hom`. At the cell level it is a row of multiply-accumulate cells
for each element of the product, and one small lemma, `macRow_eq`.

*State.* The installed words are a state of the matrix slice: a field in
`Slice`, a field in `Cell`, an instruction that changes it (`install`), and
a line in the abstraction function `Cell.abs`. The compiler uses the state
without any kernel asking: when a matrix is multiplied twice, `tau-place`
installs it once. The checker accepts that without being told about it,
because it is the machine run on names.

*A block.* Repeats needed a new block with a real invariant, the repeater,
and changed the invariant of the refinement proof from "all clocks are
equal" to "all repeaters are in step".

# Homework

Do them in order of size. Each has a test for being done.

## An operation

Pick one.

* `not`: the bitwise complement of every element.
* `sar k`: divide every element by `2 ^ k`, rounding down, with no clamping.
* `ge`: element by element, 1 where the first is at least the second.
* `swapHalves`: on the rearrangement slice, exchange the lower and upper
  half of the elements.

Steps: `spec/Tau/Isa/Word.lean` if it needs a helper, then `spec/Tau/Isa/Op.lean`,
then `spec/Tau/Isa/Encode.lean`, where it needs a number that no other operation
has, in `encode` and in `decode`, then `spec/Tau/Tools/Json.lean`. Add `#guard` lines to `spec/tests/TauTest/Features.lean`
with inputs for which you worked the answer out by hand, including a
negative element, and at a type of more than 8 bits.

You are done when `lake build` succeeds. Notice that you did not
touch a proof, and say why. For the proof in `spec/Tau/Proofs/Isa/Encode.lean`,
say what would have happened had you given your operation a number that is
already taken.

Then state one fact about your operation on a single element and prove it with
`bv_decide`, in the style of `spec/Tau/Proofs/Isa/Word.lean`.

With the compiler: add the operation to
`compiler/include/tau/Dialect/TauOps.td` and to `isUnaryKernelOp` or
`isBinaryKernelOp` in `compiler/lib/Support/OpUtils.cpp`, give it its number in
`encodeEntry` in `compiler/lib/Passes/Encode.cpp`, add a function for it to
`compiler/python/tau/__init__.py`, write an example in Python with its buffers, and
run `scripts/check-examples.sh`. If the number in the C++ is not the number
in Lean, say which line of the script's output tells you.

## An instruction

Pick one.

* `clear j g`: the matrix slice sets `g` of its installed words to zero,
  from word `j` on, and outputs nothing.
* `peek j dst`: the matrix slice puts installed word `j` on a stream.
* `forward src dst`: the vector slice passes a word from one stream to
  another unchanged. This lets a word turn round.

Steps 3, 4, 6, 7 and 8 of the path. For each proof, find the existing case
that is most like yours and copy its shape. Decide whether your instruction
issues a word, in the sense of Machine 3.9, and check that
`issued` in `spec/Tau/Machine/Issues.lean` agrees.

You are done when `lake build` succeeds, with a hand-written
program in `spec/tests/TauTest/Features.lean` that uses your instruction, run on
both machines as `run` does there. `#print axioms Tau.end_to_end` must still
list three axioms.

For `forward`: before you start, decide whether it needs a new instruction
at all. An operation that returns its operand unchanged would do the same
job with less work. What would be lost?

## State

* An accumulator in the matrix slice. `accumulate n src` adds a product to
  it and outputs nothing, and `emit dst` puts it on a stream and clears it.
  A matrix that takes a word longer than the machine's can then be
  multiplied in parts, and the parts summed.
* A held operand in the vector slice: `hold src` keeps a word, and a new
  two-value instruction uses the held word as its second operand. A constant
  can then be used many times without being sent many times.

Here the abstraction function changes, and so does `State.init_map` and
`CellState.init_abs`. Decide first what the cell level builds the new state
from. For the accumulator, the answer is the block of the chapter "The
accumulator", one for each lane.

You are done as for an instruction, with a test that would fail if the
accumulator and the product, or the held word and the stream, were
confused.

## Timing

One project, for after everything else.

Give each operation its own delay. Two results can then leave a slice on the
same cycle, which a machine with one delay per slice never had to decide.

The repository has done this once (Machine 3.4, `Config.delayOf`), so this
project has a solution, as the Specify exercises do. Start from the commit
before it (`git log -S delayOf`), and read the solution only once your build
is quiet.

* Decide the rule. A trap is the simplest.
* At the slice level the pipe becomes a row of slots that a result can enter
  part way along.
* At the cell level you need a new block, a shift register with several
  inputs, or a way to write one slot of the shift register you have. Say
  which you chose and what the other would have cost.
* The scheduler in `compiler/lib/Passes/Schedule.cpp` needs the new delays.
  Decide whether a program without pins can make two results leave one slice
  on one cycle, and so whether `tau-place` or `tau-schedule` has anything to
  avoid.

The chapters on the shift register, the slice-level machine and the
cell-level machine each come back once in this project. If you finish it you
have done, alone, what the course did with you.

# Checkpoint

One feature of each of the first three sizes, built, tested, and covered by
the end-to-end theorem.
