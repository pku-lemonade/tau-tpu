import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The slice-level machine" =>
*Terms to look up:* instruction set architecture, SIMD, saturating arithmetic.

*Files:* `Tau/Isa/Op.lean`, `Tau/Isa/Instr.lean`, `Tau/SliceLevel/Machine.lean`,
`tests/TauTest/Linear.lean`.

# The idea

This chapter has no proofs. You read a specification of a whole machine, and
then you program the machine by hand.

Start with the instruction set.

{docstring Tau.Kind}

{docstring Tau.Instr}

{docstring Tau.Timed}

Then the machine. Its state is the contents of every stream slot and of every
slice:

{docstring Tau.State}

One cycle is the function `step`. Read it in `Tau/SliceLevel/Machine.lean`
together with the comment at the top of the file. The rule to take away is
this. A result computed at slice `p` on cycle `t` can be read at slice `q` on
cycle `t + delay + 1 + |q - p|`, and on no other cycle.

Things that can go wrong are traps:

{docstring Tau.TrapKind}

A trap is not an error message added for convenience. It is part of the
specification: it says which programs the hardware gives no meaning to.

# Values the machine never looks at

The machine is written for an arbitrary type of values, with the operations
supplied from outside:

{docstring Tau.Sem}

The machine moves values and hands them to these operations. It never
inspects one to decide what to do. Which slots are read, and whether a trap
happens, depend only on the program. Chapter 11 turns this observation into
the key lemma of the course.

# Programming by hand

`tests/TauTest/Linear.lean` contains a quantized linear layer scheduled by
hand, with a comment on each instruction. Follow one value through it: the
word `x` leaves slice 2 on cycle 0 and is used by slice 0 on cycle 4. Check
that against the rule above, with a memory delay of 1 and a distance of 2.

The file also runs the checker on the same schedule. Ignore that part for
now.

# Exercises

There is no guided file for this chapter.

*Open.* Write a schedule, as a Lean `Program`, that adds two words held in
slice 2 and slice 3 and stores the result in slice 5. Run it with `execute`
and a `#guard`, as the test file does. Then make it one cycle shorter, or
convince yourself that it cannot be done.

*Open.* Write a schedule that traps with each of the seven kinds of trap, one
program per kind. This is a good way to find out whether you have understood
`step`.

*Challenge.* State and prove the transit lemma for one stream: if a value is
placed on an east-going stream at position `p` on cycle `t`, and no slice
between `p` and `q` places anything on that stream in the meantime, the value
is at position `q` on cycle `t + (q - p)`. Stating it precisely is most of the
work. Compare your statement with `shiftRegister_outAt`.

# Checkpoint

You can read an executable specification of a machine, predict what a program
does on it, and write a program that meets its timing rule.
