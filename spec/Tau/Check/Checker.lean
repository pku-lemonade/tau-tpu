import Tau.Machine.SliceLevel
import Tau.IR.Source
import Tau.IR.Compiled
import Tau.Check.Simplify

/-!
# The checker

The compiler turns a source program into a program for the machine: it
decides which memory holds each buffer, which slice runs each operation, on
which cycle, and on which streams the words travel. Any of those decisions
can be wrong.

The checker decides whether a compiled program is right, without looking at
how the compiler made its decisions. It runs the machine on the compiled
program and it runs the source program, both over expressions instead of real
words (`Tau.Check.Expr`). Each run gives two things.

* An expression for every word of every buffer at the end. If the two runs
  end with the same expressions, the compiled program computes what the
  source program computes, whatever the buffers hold (`sameExprs`).
* A timeline: the words issued and their cycles (`Tau.Isa.Event`). If
  the machine's timeline has every event of the source program's, the
  compiled program keeps every pin (`covers`).

The checker is the machine itself, run on names instead of numbers. That is why
it needs no separate rules about timing, stream reuse or hazards.

The proof that an accepted program is correct is in `spec/Tau/Proofs/Check/`.

Terms to look up: *translation validation*.

Docs: Compiler 1, 5 and 7 (`docs/`).
-/

namespace Tau

/-- Buffers of the given sizes whose words are the expressions `init b k`. -/
def symBufs (sizes : List Nat) : List (List Expr) :=
  (List.range sizes.length).map fun b =>
    (List.range (sizes[b]?.getD 0)).map fun k => Expr.init b k

/-- The expressions the machine ends with, for every word of every buffer.
`none` if the machine traps. -/
def machineExprs (c : Compiled) : Option (List (List Expr)) :=
  match execute exprSem c.cfg c.prog c.cycles (image c.map c.memSizes Expr.init .fill) with
  | .ok mem => some (extract c.map mem .fill)
  | .error _ => none

/-- The events of the machine: every word it issues, as an expression, with
its cycle. -/
def machineEvents (c : Compiled) : List (Event Expr) :=
  c.timelineFrom exprSem (image c.map c.memSizes Expr.init .fill)

/-- The expressions the kernel ends with, for every word of every buffer. -/
def kernelExprs (k : Kernel) (sizes : List Nat) : Option (List (List Expr)) :=
  k.run exprSem (symBufs sizes)

/-- The events of the kernel: the word of every pinned statement, as an
expression, with its cycle. -/
def kernelEvents (k : Kernel) (sizes : List Nat) : List (Event Expr) :=
  k.timeline exprSem (symBufs sizes)

/-- The expressions the source program ends with, for every word of every
buffer. -/
def sourceExprs (s : Source) (sizes : List Nat) : Option (List (List Expr)) :=
  s.run exprSem (symBufs sizes)

/-- The events of the source program. -/
def sourceEvents (s : Source) (sizes : List Nat) : List (Event Expr) :=
  s.timeline exprSem (symBufs sizes)

/-- Whether two tables of expressions are the same after simplifying. -/
def sameExprs (a b : List (List Expr)) : Bool :=
  a.map (·.map Expr.simp) == b.map (·.map Expr.simp)

/-- Whether every event of `a` is an event of `b`, after simplifying the
words. -/
def covers (a b : List (Event Expr)) : Bool :=
  (a.map (Event.map Expr.simp)).all fun e => (b.map (Event.map Expr.simp)).contains e

/-- Whether the second of two runs ends with the buffers of the first and
has its events. `a` and `b` are the final expressions of the two runs, or
`none` for a run that failed; `ea` and `eb` are their events. -/
def agree (a b : Option (List (List Expr))) (ea eb : List (Event Expr)) : Bool :=
  (match a, b with
   | some a, some b => sameExprs a b
   | _, _ => false) &&
  covers ea eb

/-- Accept or reject a compiled program for the source program `s`, whose
buffers have the given sizes. -/
def check (s : Source) (sizes : List Nat) (c : Compiled) : Bool :=
  c.map.map (·.size) == sizes &&
  agree (sourceExprs s sizes) (machineExprs c) (sourceEvents s sizes) (machineEvents c)

end Tau
