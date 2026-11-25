import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Writing a specification" =>
*Read:* `course/architecture-manual.md`, sections 1 and 2.1 to 2.3; `docs/overview.md`, "The
words".

*Work in:* `course/Specs/Candidates.lean`, `course/Specs/Review.lean`,
`course/Specs/Repair.lean`, `course/Specs/Provable.lean`.

*Time:* one day.

# What the rest of the course asks of you

So far you were given a definition and a statement, and you wrote the proof.
From here on it is the other way round. You are given a _source_ that is not
Lean, and you write the definition and the statement. The proof is mostly
somebody else's work: an AI agent's, checked by Lean.

This is the order in which the work is done on a real chip and a real
compiler. Somebody hands you an architecture manual and a few thousand lines
of C++. Nothing in them is precise enough to prove anything about. Your job
is to say, in Lean, what the manual and the C++ mean. Once that is said,
proving things about it is work that can be handed over. Saying it cannot be
handed over, because only a person who knows what the hardware is for can
judge whether a definition says the right thing.

# The loop

Every chapter from here on goes through the same seven steps.

1. *Read the source.* For hardware it is a section of the manual,
   `course/architecture-manual.md`. For a compiler pass it is a C++ file.
2. *Write the definition.* In a file under `course/Specs/`, in place of a
   `todo`.
3. *Run the tests.* Each file has `#eval report` lines that compare your
   definition with the table in the source.
4. *List what the source does not say.* Your definition had to decide things
   the source left open. Write them down as questions for the architect.
5. *State the property.* Write, as a proposition, what a user of the
   component relies on.
6. *Compare.* Only now open the definition and the theorem in `Tau/`.
7. *Hand the proof over, and review what comes back.*

Steps 2, 4 and 5 are the ones that need you.

# The source

`course/architecture-manual.md` describes the chip the way an architect would: a paragraph
per component, and a table of what goes in and what comes out on each cycle.
Read section 2.2 now. It is the accumulator you already know.

Notice what kind of document it is. It is short. It is written for a reader
who knows what an accumulator is for. And it does not answer every question:
it gives a table for a starting value of 0 and says nothing of what `load`
does to the output in the cycle it arrives.

# The definition, and choosing the state

A block is a state, a starting value for it, and a step. The manual tells
you the inputs and the outputs. It does not tell you the state. That is
yours to choose.

The files under `course/Specs/` leave it open on purpose:

```
abbrev State : Type := Unit

def memory (words : List Int) : Block State (MemIn Int) (Option Int) := todo
```

`todo` stands for a definition you have not written. It has a value, so the
file compiles and the tests run and disagree. Replace `Unit` by what your
block has to remember, and `todo` by the block.

Two people will choose different states for the same component, and both can
be right. The tests cannot tell, because they look only at outputs. Keep
this in mind: the chapter on the cell-level machine is about two machines
with different state and the same behaviour.

# The tests, and what they cannot tell you

A test compares your outputs with the rows of the manual's table.

```
#eval report "the memory" (Tables.memory memory)
```

Put the cursor on the line. It prints how many rows agree and lists the rows
that do not.

A table is a handful of inputs. A definition can give every row and still be
wrong. `course/Specs/Candidates.lean` shows this on the three components you
know. For each it has three definitions. All three give every row of the
manual's table, and two of them are wrong.

# What the source does not say

Take the memory of section 2.5. It says a read gives "the word at address
`a`". What if the memory has two words and `a` is 5? The manual does not say.
A definition must say something: Lean will not accept a function that has no
answer.

So every definition settles questions the source left open. Each one is a
decision that nobody may have made yet, and on a real project a decision that
the architect has to hear about. Write each as a question:

* What does a read of an address outside the memory return?
* What does a write to an address outside the memory do?

Keep the list in `course/Work/Questions.md`. Each file under `course/Specs/`
has a second `#eval` line, commented out, for the cases the source leaves
open. Remove the `--` after you have your own list. It shows what the
specification in `Tau/` decided. Where it differs from your definition,
neither is wrong: the source did not say.

Finding these is the part of the job that most often changes a design.

# The statement

A table says what happens on five inputs. A statement says what happens on
all of them.

```lean
example (zero : Nat) (x : Signal Nat) (t : Nat) :
    (accumulator zero).outAt (fun k => .add (x k)) t = sumTo zero x t :=
  accumulator_outAt_add zero x t
```

Three things make a statement good.

* *It says what a user relies on.* The user of an accumulator wants a sum.
  The statement is about a sum. It does not mention the state.
* *Its hypotheses can be met.* This one holds for a signal in which every
  command is `add`. Such signals exist. A statement whose hypotheses nothing
  satisfies is true and says nothing.
* *The wrong candidates fail it.* A statement that the two wrong
  accumulators in `Candidates.lean` also satisfy has not said enough.

In this course you write a statement as a named proposition next to the
definition:

```
def SumsItsInputs : Prop :=
  ∀ (zero : Nat) (x : Signal Nat) (t : Nat),
    (accumulator zero).outAt (fun k => .add (x k)) t = sumTo zero x t
```

The name is what you hand to an agent: "prove `SumsItsInputs`". The agent
cannot then prove something slightly different without Lean noticing.

# Handing the proof over

Give the agent the file with the definition, the name of the proposition,
and the instruction to prove it without changing either. `AGENTS.md` in this
repository tells an agent the rules of the course.

Then one of three things happens.

* *A proof comes back.* Review it, as below.
* *The agent says the statement is false.* It will usually show an input.
  Check the input with `#eval`. Then the statement is wrong, or the
  definition is.
* *The agent is stuck.* Ask for the goal it is stuck on. A goal that cannot
  be proved tells you which case you forgot. `course/Specs/Repair.lean` has
  three statements that sound right and are false, each with the goal an
  agent got stuck on.

A stuck proof is the most useful message you will get about a
specification. Tests showed you the cases you thought of. A proof finds the
ones you did not.

# Reviewing what comes back

Lean checks that a proof proves its statement. It does not check that the
statement is the one you asked for. That is the review, and it takes five
looks.

1. *Is it the statement you asked for?* Compare it with yours. A changed `≤`
   or one more hypothesis is easy to miss. If you asked for a proof of a
   named proposition and got `theorem ... : ThatName`, Lean has done this
   look for you.
2. *Can the hypotheses be met?* For each hypothesis, give one example that
   satisfies it. A hypothesis that the proof never uses is a warning sign.
3. *Is it about your definition?* Put the cursor on each name in the
   statement and see where it is defined. A definition of the same name
   closer by wins.
4. *Does it rest on anything unproved?* `#print axioms name` lists what a
   theorem rests on. `sorryAx` in the list means some proof on the way is
   missing.
5. *Was the definition changed?* Look at the difference in the definition
   file, not only at the proof.

`course/Specs/Review.lean` has five theorems that came back. Four should not
be accepted.

# What makes a specification provable

Some definitions are easy to prove things about and some are not, and the
difference is decided when the definition is written. tau-tpu follows a few
rules. Each is visible in the code.

* *Never decide anything from what a value holds.* The machine and the
  kernel take the operations as a parameter (`Sem` in `Tau/Isa/Op.lean`) and
  never look inside a word. This is what lets one run on names stand for
  every run on numbers. The chapter on the checker depends on it.
* *Make sizes parameters.* A shift register has depth `n`, not depth 4. A
  theorem then holds for every size, and a test at one size is only a test.
* *Make failure a result.* A machine that reads an empty stream slot returns
  a trap. It does not raise an error and it does not return garbage. Then
  "does not trap" is something a theorem can say.
* *Define one step. Derive many.* `step` says what one cycle does. What
  happens over many cycles is a theorem, such as the timing rule.
* *Keep definitions and proofs apart.* Everything a person has to read and
  judge is under `Tau/`, outside `Tau/Proofs/`. The main statements are
  there too, as named propositions in `Tau/Claims.lean`.

A rule is easier to believe after seeing what happens without it.
`course/Specs/Provable.lean` takes the first three rules. For each it gives a
definition that breaks the rule and asks you for the input on which that
goes wrong.

# Your claims table

For everything you write from here on, record how it stands. Keep the table
in `course/Work/Claims.md`.

```
| What                                   | How it stands                                    |
| my memory                              | a definition. Tested on 4 rows. Nothing proves   |
|                                        | it right.                                        |
| ReadsLastWrite                         | a statement. Proved by an agent, reviewed by me. |
| read outside the memory gives nothing  | my decision. Not in the manual.                  |
```

The last chapter compares your table with the one in the repository's
`README.md`.

# How to work through it

1. Read `docs/overview.md`, "The words", and sections 1 and 2.1 to 2.3 of
   the manual.
2. Do `course/Specs/Candidates.lean`.
3. Do `course/Specs/Review.lean`. Then read
   `course/Specs/ReviewAnswers.md`.
4. Do `course/Specs/Repair.lean`.
5. Do `course/Specs/Provable.lean`.
6. Read `Tau/Claims.lean` from top to the end of "The components". These are
   the statements about the three components you know, written the way the
   course asks you to write yours.
7. Start `course/Work/Questions.md` and `course/Work/Claims.md`. Both have a
   first line to copy.

# Exercises

*Specify.* `course/Specs/Candidates.lean`. For each of the three components,
find the right candidate and an input that gives each wrong one away. For
each wrong candidate, say whether it contradicts a sentence of the manual or
settles something the manual does not say. Those are different kinds of
mistake: the first is a bug, the second is a question nobody asked.

*State.* For one component in `Candidates.lean`, write a statement that the
right candidate satisfies and one wrong candidate does not. Show that the
wrong one fails by giving the input.

*Review.* `course/Specs/Review.lean`. Decide for each of the five whether to
accept it, and which of the five looks told you.

*Repair.* `course/Specs/Repair.lean`. For each of the three statements, find
an input that makes it false, then change it so that it is true and still
useful.

*Break a rule.* `course/Specs/Provable.lean`. Three definitions, each of which
breaks one rule of "What makes a specification provable". For each, give the
input on which it goes wrong, and find the place in `Tau/` that the task
names.

*Questions.* Read sections 2.1 to 2.3 of the manual once more and write down
everything they leave open. There are at least six such things across the
three sections. The rows of the three `Decisions` tables in
`course/Specs/Tables.lean` are some of them.

# Checkpoint

You can say what a table of outputs cannot show and a statement can. You
rejected four of the five returned proofs, each for a different reason. The
report of `Provable.lean` says that all rows agree. You have a list of
questions for the architect with at least six entries.
