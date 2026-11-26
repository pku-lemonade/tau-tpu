import Specify.Support.Tables

/-!
# Three rules for a specification, and what happens without them

Sources: `course/Specify/Support/Tables.lean`, the section "What makes a specification
provable", and the files in `spec/Tau/` named in each task.

The chapter "Writing a specification" gives five rules that tau-tpu follows.
Each of the three tasks here takes one rule, shows a definition that breaks
it, and asks you for the input on which that goes wrong. The definitions are
in `course/Specify/Support/Tables.lean`; read them there.

Put the cursor on the `#eval` line at the end. It has one row for a fact
about the definitions and the others for your answers.
-/

namespace Specify.Provable

open Tau Specify Specify.Tables

/-! ## 1. Never decide anything from what a value holds

`plain S x` computes `relu` of `x`. `peeking S x` does the same, except that
it first compares `x` with zero. Run on a name, both give "relu of the
input", so a check that runs on names cannot tell them apart:

    #eval peeking exprSem (.init 0 0)

On real words they are not the same. Give a word of two lanes on which they
differ. -/

/-- The lanes of a word on which `peeking` and `plain` differ. -/
def giveaway : List Int := todo

/-! This is why the machine and the kernel are written for an arbitrary
`Sem` (`spec/Tau/Isa/Op.lean`), which has no way to compare two values. Look at
the type of `exec` in `spec/Tau/Machine/SliceLevel.lean`: nothing in it lets
`exec` test a word. If one instruction did, `execute_map` could not be
proved, and every check in `spec/Tau/Check/` would accept programs that are
wrong on some input. -/

/-! ## 2. Make sizes parameters

`shiftRegisterButOne n reset` behaves as a shift register of depth `n` at
every depth but one. The doc's table, at depths 1 and 2, will not find
it. Give the depth at which it is wrong. -/

/-- The depth at which `shiftRegisterButOne` is not a shift register. -/
def badDepth : Nat := todo

/-! `shiftRegister_outAt` in `spec/Tau/Proofs/Blocks/ShiftRegister.lean` is stated
for every `n`. A theorem for every size has to meet every size, including
the one nobody tested. A table has the sizes somebody thought of. That is why
every size in `spec/Tau/` is a parameter: the depth of a shift register, the
number of lanes in a word, the number of slices on a machine. -/

/-! ## 3. Make failure a result

`memory0` answers 0 where `Tau.memory` answers "nothing": for an idle cycle,
and for a read outside the memory. Then a read outside the memory can look
exactly like a read inside it. Give the two words of a memory, and an
address inside it, such that reading that address and reading address 5 give
the same output. -/

/-- The two words of a memory, and an address below 2. -/
def lookalike : List Int × Nat := todo

/-! With `memory0`, "this program never reads outside the memory" cannot be
told from the outputs, so no theorem about outputs can say it. With
`Tau.memory` it is "the output is never `none` on a read". The machine does
the same on a larger scale: `execute` returns a trap, and "does not trap" is
half of the conclusion of `check_sound`. -/

#eval report "provable" (provable giveaway badDepth lookalike)

/-! ## The other two rules

*Define one step, derive many.* You have seen this in every block: `step`
says one cycle, and `outAt` at cycle `t` is a theorem. The timing rule is the
same at the scale of the machine.

*Keep definitions and proofs apart.* Count the lines under `spec/Tau/` that are
outside `spec/Tau/Proofs/`. That is all a person has to read to know what tau-tpu
claims. `spec/Tau/Claims.lean` lists the claims themselves.
-/

end Specify.Provable
