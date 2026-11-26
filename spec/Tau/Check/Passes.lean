import Tau.Check.Checker
import Tau.IR.Placed

/-!
# Checking each compiler pass on its own

`check` (`spec/Tau/Check/Checker.lean`) compares the compiled program with the
source program. That covers the whole compiler at once. This file has one
check for each pass. Each compares the output of the pass with its input, so
a rejection names the pass that went wrong.

| Pass | Input | Output | Check |
|---|---|---|---|
| `tau-inline` | a source program | a kernel | `checkInlined` |
| `tau-simplify` | a kernel | a kernel | `checkKernels` |
| `tau-unroll` | a kernel | a kernel | `checkKernels` |
| `tau-place` | a kernel | a placed program | `checkPlaced` |
| `tau-schedule` | a placed program | a compiled program | `checkScheduled` |
| `tau-route` | a compiled program | a compiled program | `checkRouted` |
| `tau-slice` | a compiled program | a compiled program | `checkRouted` |
| `tau-fold` | a compiled program | a compiled program | `checkRouted` |

The image, the program as numbers, is decoded (`spec/Tau/Isa/Encode.lean`) and
then checked as a compiled program, again by `checkRouted`.

Every check works the same way. It runs both sides on expressions. That
gives an expression for every word of every buffer, and a timeline
(`spec/Tau/Isa/Event.lean`). The check accepts if the two tables of expressions
are the same after simplifying, and the timeline of the output has every
event of the timeline of the input (`agree`).

Each check asks whether the output computes what the input computes, and
issues the pinned words on their cycles. It does not ask how the pass got
there: `checkScheduled` accepts any timed program that ends with the buffers
of the placed program and keeps its pins, including one whose instructions
are different.

In a compiled program every instruction has a cycle, so every word it issues
is an event. `checkRouted` therefore asks that the second program issue every
word of the first on the same cycle: the passes after `tau-schedule` may not
move anything in time.

`tau-schedule` writes its output with a stream for every word, on a machine with
as many streams as that takes, so that the schedule can be checked before
any stream is shared. `tau-route` then fits the words onto the streams the
machine has.

The forms are in `spec/Tau/IR/`. The soundness theorems, two for each check, are
in `spec/Tau/Proofs/Check/Passes.lean`.

Terms to look up: *translation validation*.

Docs: Compiler 4 and 5 (`docs/`).
-/

namespace Tau

/-- The expressions a placed program ends with, for every word of every
buffer. `none` if an instruction cannot be carried out. -/
def placedExprs (pl : Placed) : Option (List (List Expr)) :=
  match pl.execute exprSem (image pl.map pl.memSizes Expr.init .fill) with
  | some mem => some (extract pl.map mem .fill)
  | none => none

/-- The events of a placed program: the word of every pinned instruction, as
an expression, with its cycle. -/
def placedEvents (pl : Placed) : List (Event Expr) :=
  pl.timelineFrom exprSem (image pl.map pl.memSizes Expr.init .fill)

/-- `tau-inline`: accept or reject the kernel `k` as the source program `s`
with its calls copied in. -/
def checkInlined (s : Source) (k : Kernel) (sizes : List Nat) : Bool :=
  agree (sourceExprs s sizes) (kernelExprs k sizes) (sourceEvents s sizes) (kernelEvents k sizes)

/-- `tau-simplify` and `tau-unroll`: accept or reject the kernel `k'` as a
rewriting of the kernel `k`. -/
def checkKernels (k k' : Kernel) (sizes : List Nat) : Bool :=
  agree (kernelExprs k sizes) (kernelExprs k' sizes) (kernelEvents k sizes) (kernelEvents k' sizes)

/-- `tau-place`: accept or reject the placed program `pl` for the kernel
`k`. -/
def checkPlaced (k : Kernel) (sizes : List Nat) (pl : Placed) : Bool :=
  pl.map.map (·.size) == sizes &&
  agree (kernelExprs k sizes) (placedExprs pl) (kernelEvents k sizes) (placedEvents pl)

/-- `tau-schedule`: accept or reject the compiled program `c` as a schedule
of the placed program `pl`. -/
def checkScheduled (pl : Placed) (c : Compiled) : Bool :=
  agree (placedExprs pl) (machineExprs c) (placedEvents pl) (machineEvents c)

/-- `tau-route`, `tau-slice`, `tau-fold` and the encoding: accept or reject
the compiled program `c'` as another form of the compiled program `c`. -/
def checkRouted (c c' : Compiled) : Bool :=
  agree (machineExprs c) (machineExprs c') (machineEvents c) (machineEvents c')

end Tau
