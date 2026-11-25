import Specs.Tables

set_option linter.unusedVariables false

/-!
# Specify: a rule for schedules

Source: `course/architecture-manual.md`, section 3.4, and
`compiler/lib/Target/Schedule.cpp`.

The checks of the course ask whether a compiled program computes its kernel.
They do not say what a correct schedule is. Here you say one part of it, as
a rule on the program text: every operand arrives on the cycle it is read.

Nothing proves your rule. It is tested against the machine: a program your
rule accepts should not make the machine read an empty stream slot, and a
program your rule rejects should.

Three functions are given in `Specs/Tables.lean`:

* `Tables.issues c`: every instruction the program issues, as
  `(slice, cycle, instruction)`, with repeats written out;
* `Tables.operands i`: the streams the instruction `i` reads;
* `Tables.result i`: the stream `i` places its result on, if any.

1. Read the sources.
2. Write the rule in place of `todo`.
3. Put the cursor on the `#eval` lines. The first uses small programs. The
   second takes the scheduled and the finished program of one example, and
   every copy of them with one instruction issued a cycle late.
4. Your rule is not all of "a correct schedule". Write down a program that
   passes your rule and is still wrong. What second rule would catch it?
5. A solution, with no proof, is in `tests/TauTest/SpecSolutions.lean`.
-/

namespace Specs.OnTime

open Tau Specs

/-- Every operand of every instruction arrives on the cycle it is read. -/
def onTime (c : Compiled) : Bool := todo

#eval report "on time" (Tables.onTime onTime)
#eval reportIO "on time, against the machine"
  (Tables.onTimeOnExample onTime "examples/linear/stages")

end Specs.OnTime
