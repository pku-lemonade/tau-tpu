import Specs.Tables

set_option linter.unusedVariables false

/-!
# Specify: what a pin claims

Sources: `Tau/Docs/Programs.md`, section 5; `Tau/Docs/Machine.md`,
section 3.9.

The types are in `Tau/Isa/Event.lean`: read the structure `Event` and stop
there. `Stmt` and `Env` you know from `course/Specs/Kernel.lean`; a pinned
statement is `Stmt.pin t s`.

The steps are the ones in `course/Specs/Kernel.lean`.
-/

namespace Specs.Pins

open Tau Specs

variable {V : Type}

/-- The event that the statement `s`, pinned to `t`, makes on loop iteration
`i`. `env` is the environment after `s` has run: the word of `s` is in it.
`none` if there is no word to issue. -/
def eventOf (i : Nat) (t : Idx) (s : Stmt) (env : Env V) : Option (Event V) := todo

#eval report "pins" (Tables.pin eventOf)

-- #eval report "pins, what the doc leaves open" (Tables.pinDecisions eventOf)

/-! ## State

A source program and a compiled program each have a timeline: the events of
one run. For a source program they are the events of its pinned statements
(`Source.timeline`). For a compiled program they are everything the machine
issues (`Compiled.timeline`). -/

/-- What it means for the compiled program `c` to keep the pins of the source
program `s`, on the buffer contents `bufs`. Say it with the two timelines. -/
def KeepsPins (S : Sem V) (s : Source) (c : Compiled) (bufs : List (List V)) (fill : V) :
    Prop := todo

/-! ## Judge

Before you compare, answer in `course/Work/Questions.md`. Each is a question
about your `KeepsPins`, of the kind the chapter "Writing a specification"
asks of every statement.

1. A program computes the pinned relu on cycle 3 at the vector slice, as
   asked. A second program computes it on cycle 1, parks it in memory, and
   reads it back out on cycle 3. Does the second keep the pin? Should it?
2. Two operations of one program compute the same word. One is pinned to
   cycle 5. The compiler issues the other one on cycle 5 and the pinned one
   on cycle 9. Does `KeepsPins` hold?
3. A program has no pins. What does `KeepsPins` say about it?
4. Is there a compiled program that satisfies `KeepsPins` for every source
   program?

## Compare

The definitions are `Stmt.target` and `Env.issue` in `Tau/IR/Kernel.lean`,
used by the `pin` case of `Stmt.exec`. The statement is the conclusion of
`check_pins` in `Tau/Proofs/Check/Sound.lean`, and `CheckKeepsPins` in
`Tau/Claims.lean`.

The answers to 1 and 2 are both yes, and `Tau/Isa/Event.lean` says so in its
opening comment. An event is a word and a cycle; it does not name a slice or
an instruction. That is a decision, and the README lists it under what is
not claimed. A stronger statement would need a way to say which instruction
of the compiled program stands for which operation of the source, and no
check in tau-tpu has one.
-/

end Specs.Pins
