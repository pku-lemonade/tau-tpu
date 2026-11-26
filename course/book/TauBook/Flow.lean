import VersoManual
import Tau
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "From Python to an image" =>
*Terms to look up:* embedded domain-specific language, tracing,
metaprogramming, function inlining, assembler, instruction encoding.

*Sources:* the opening comment of `frontend/tau/__init__.py`; the description
of `tau.call` in `compiler/include/tau/Dialect/TauOps.td`; the opening
comments of `compiler/lib/Transforms/Inline.cpp`, `compiler/lib/Target/Slice.cpp`
and `Fold.cpp`; `Tau/Docs/Programs.md`, sections 4 and 7;
`Tau/Docs/Compiler.md`; `Tau/Docs/Machine.md`, section 3.10.

*Specify:* `course/Specs/Encode.lean`.

*Read:* `Tau/IR/Source.lean`, `Tau/Isa/Encode.lean`.

*Proofs:* none are exercises. `Tau/Proofs/IR/Source.lean` and
`Tau/Proofs/Isa/Encode.lean` are for reading.

*Time:* two days.

# The two ends

So far a program began as MLIR text that somebody typed and ended as a list
of instructions in a JSON file. Neither end is where a real flow begins or
ends. People write programs in a language made for writing them, and a machine
is loaded with numbers.

This chapter adds both ends: a frontend in Python before the compiler, and
after it the three steps that turn the scheduled program into the numbers
each slice is loaded with. For each step the question is the one of the
chapter on the checker: what is the specification, and which of the three
ways is used.

```
kernel.py -> kernel.mlir -> source -> kernel -> ... -> routed -> sliced -> compiled -> image
```

# The front end records

Read the comment at the top of `frontend/tau/__init__.py`, then
`examples/conv-taps/kernel.py`, and run:

```
PYTHONPATH=frontend python3 -m tau examples/conv-taps/kernel.py -o out
```

Open `out/kernel.mlir`. The Python has a loop over three taps inside a
`tau.loop`. The MLIR has one `tau.for` with three loads, three
multiplications and two additions in it. The Python `for` over the taps is
gone, and so is `enumerate`, the tuple of taps and the test `if total is
None`.

The frontend did not translate the function. It ran it. Every operation the
function called wrote one line into a record, and the record is the program.
Whatever else the function did while running, it did in Python, and none of
it is in the record. This is called _tracing_.

Two things make this sound for a machine like tau-tpu.

* A word is a handle with no operators. Python cannot add two words, compare
  them, or use one in an `if`. So what a function records cannot depend on
  the data, and one run stands for all. This is the property of the machine
  that the checker rests on, met again at the other end of the flow.
* A `tau.loop` is the one loop that is not Python's. Its body is run once,
  with an index that stands for every iteration and supports only `+`, `-`
  and `*` with integers. That is exactly what `Idx` can hold: a base and a
  stride.

`tau.dense` in the same file shows the third thing a traced language gives
for free. It is not an operation of the machine. It is a Python function
that calls three of them. An operation made of others needs nothing in the
compiler and nothing in Lean.

# What is specified, and what is not

There are two languages here, and only one has a specification.

The record is a _source program_. `Source` in `Tau/IR/Source.lean` says what
it is, `Source.run` what it computes and `Source.timeline` when. Every
theorem of the last two chapters starts from it.

The Python around the calls has none. Nothing in Lean says what a Python file
means, and nothing could without a specification of Python. What can be said
is narrower, and each part is a test:

* The frontend writes the record twice: as MLIR for the compiler, and
  directly as a source file, `traced.json`. The compiler writes its own
  source file from the MLIR. The two must be equal.
* The same Python function can be run on real numbers, with the operations
  computing instead of recording. Its buffers and its events must be the ones
  `tau-sim` gives for the record.

Both are in `scripts/check-examples.sh`. Run by hand:

```
compiler/build/bin/tauc out/kernel.mlir -o out
PYTHONPATH=frontend python3 -m tau examples/conv-taps/kernel.py --run examples/conv-taps/buffers.json
lake exe tau-sim out/source.json examples/conv-taps/buffers.json
```

# Calls

A kernel may call another. `examples/two-layer/kernel.py` calls one layer
twice. In the record a call is one item.

{docstring Tau.Source}

A call names the caller's buffers that the called kernel's buffers stand
for, and an _origin_: the cycle the called kernel's pins count from.

{docstring Tau.Source.exec}

Read the `call` case. The called kernel starts with no variables, and with
only the buffers it was given. When it is done, what it left in its buffers
is written back, and its events are added to the caller's, moved by the
origin.

A kernel that applies relu, pinned to its cycle 3, called twice:

```lean
def reluCallee : Source :=
  Source.ofKernel
    [ .stmt (.load 0 0 ⟨0, 0⟩),
      .stmt (.pin ⟨3, 0⟩ (.un 1 .relu 0)),
      .stmt (.store 1 1 ⟨0, 0⟩) ]

def reluTwice : Source :=
  .call reluCallee [0, 2] 0 (.call reluCallee [2, 1] 10 .done)
```

The first call reads buffer 0 and writes buffer 2. The second reads buffer 2
and writes buffer 1, and counts from cycle 10. So the program has two events,
on cycles 3 and 13. The list holds the most recent first.

```lean
example : (sourceEvents reluTwice [1, 1, 1]).map (·.time) = [13, 3] := by
  rfl
```

A call may not pass the same buffer twice. The called kernel would then see,
through one buffer, what it stored to the other, and a kernel copied in and a
kernel called would no longer do the same thing.

```lean
example : sourceExprs (.call reluCallee [0, 0] 0 .done) [1, 1] = none := by
  rfl
```

`tau-inline` replaces each call by a copy of the called kernel. It is checked
like every other pass: `checkInlined` runs the source program and the kernel
on names and compares buffers and timelines.

# The back end: slices

After `tau-route` every instruction has a slice, a cycle and a stream. But
the compiler still holds them as one function, in which an instruction is
joined to the instructions it feeds by the words it passes on. Run:

```
compiler/build/bin/tauc examples/linear/kernel.mlir -o out --print-mlir
```

and compare what is printed after `tau-route` with what is printed after
`tau-slice`. Before, `%8 = tau.i.bin %6, %7` says that the add takes the
results of two other instructions. After, an entry says
`a = "e0", b = "e1"`: it reads two streams. The first is how a compiler
thinks. The second is all the machine has: a slice is told which streams to
read on which cycle, and whose word is on them is the scheduler's business.

`tau-slice` makes that step, and sorts the entries into one list per slice.
In Lean this was never a step: `Program.entriesOf` picks a slice's entries
out of the one list, and `step` asks each slice for what is due.

# The back end: folds

A slice's repeater can issue one entry many times. `tau-fold` finds entries
of a slice that are the same but for their cycle and their address, and
whose cycles and addresses go up in equal steps, and merges them into one
repeating entry. After `tau-fold` in the output above, the two `mac` entries
of slice 0 are one.

A fold is a rewrite, and a rewrite can be wrong. tau-tpu once did this
merging inside the function that writes the JSON file. Every check still
covered it, because the checks read the file. But a wrong fold would have
been reported as a wrong schedule or a wrong routing, the pass before. A
rewrite belongs in a pass, with a file before it and a file after.

# The image

The last step writes the entries of each slice as numbers. Read section 3.10
of `Machine.md` and do `course/Specs/Encode.lean` now.

{docstring Tau.Timed.encode}

{docstring Tau.Image.decode}

```lean
def imageProgram : Program :=
  [ .once 2 6 (.write ⟨.east, 0⟩ 0),
    { slice := 0, time := 0, instr := .read 0 ⟨.east, 0⟩,
      repeats := 3, gap := 1, stride := 1 } ]

example :
    imageProgram.encode 3
      = [[1, 0, 3, 1, 1, 0, 0, 0], [0], [1, 6, 0, 0, 0, 1, 0, 0]] := by
  rfl
```

Slice 0 has one entry, slice 1 none, slice 2 one. The theorem about the
encoding mentions both directions, because it has to:

```lean
example (prog : Program) (slices : Nat) :
    Image.decode (prog.encode slices) =
      some ((List.range slices).flatMap fun p => prog.entriesOf p) :=
  Image.decode_encode prog slices
```

In words: the image of a program, read back, is the program's entries,
slice by slice. An encoder alone has nothing to be right about. What the
numbers mean is said by the decoder, and the decoder is the specification.

That theorem is about `Program.encode`, a Lean function. The compiler has its
own encoder in C++, and the two are compared on every example:

```
lake exe tau-check --encode out/compiled.json out/image.json
lake exe tau-check out/source.json out/image.json
```

The second line is the check of the whole flow. To `tau-check` an image is
the compiled program that `Image.decode` reads out of it.

# Three steps, three kinds of evidence

| Step | Specified by | Evidence |
|---|---|---|
| recording a Python function | nothing; the record is the program | two writers agree; a run in Python agrees with the Lean tools |
| `tau-inline` | `Source.run`, `Source.timeline` | a check, proved sound |
| `tau-slice`, `tau-fold` | the machine | a check, proved sound |
| writing the image | `Image.decode` | a copy, proved to be undone by `decode`; and a check on the decoded image |

# How to work through it

1. Read the top of `frontend/tau/__init__.py` and the four examples written
   in Python. Record each and read its MLIR.
2. Read `Tau/IR/Source.lean`. Redo the example of the two calls in your
   scratch file, with a third call.
3. Run `tauc` with `--print-mlir` on `examples/paced/kernel.py` after
   recording it, and follow one instruction from `tau-route` through
   `tau-slice` and `tau-fold` into `out/image.json`.
4. Do `course/Specs/Encode.lean`, with its questions.
5. Read `Tau/Isa/Encode.lean` and the statements in
   `Tau/Proofs/Isa/Encode.lean`. Each layer has the same statement; say what
   it is.

# Exercises

*Specify.* `course/Specs/Encode.lean`.

*State.* In the same file: the two directions, and which one the compiler
relies on.

*By hand.* Write a program in Python that uses a helper function, a Python
loop and a `tau.loop`. Before you record it, write down the MLIR you expect.
Then make the helper take a Python `bool` that decides whether it applies a
relu, and say what is in the record.

*By hand.* Try to make what a kernel does depend on its data: use a word in
an `if`, compare two words, add an integer to a word. Read each error. Then
find one thing a function can do that makes two runs record different
programs, without touching a word. What does that say about the sentence "the
record is the program"?

*By hand.* Break one thing at each end, and say first which line of
`scripts/check-examples.sh` you expect to fail. One of the four is not caught
by anything. Say why, and write the example that would catch it.

1. In `frontend/tau/__init__.py`, in the table `_BIN`, make `sub` compute
   `b - a`.
2. In the same file, in `_Tracer.stmt`, record a pin one cycle late.
3. In `compiler/lib/Target/Emit.cpp`, in `encodeEntry`, write `gap` before
   `repeats`.
4. In `compiler/lib/Target/Fold.cpp`, set `gap` to `period` and not
   `period - 1`.

*Claims.* Add to `course/Work/Claims.md` a row for each line of the table
above, and one for what a Python file means.

*Challenge.* The frontend could have been written the other way: read the
Python file as text and translate its `for` and `if` into the program. Write
half a page: what would have to be specified in Lean for that, which
programs in `examples/` could still be written, and which property of the
machine makes recording enough.

# Checkpoint

You can say what the frontend records and what it leaves out, what a call
means and why it may not pass a buffer twice, why slicing is a step for the
compiler and not for the machine, and why a statement about an encoder is a
statement about a decoder too.
