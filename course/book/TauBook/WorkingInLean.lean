import VersoManual
import Tau

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Tau

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Working in Lean" =>
This chapter is Day 0: a few hours to a day of practice before Day 1. It
shows the Lean you need to write and read definitions, takes you through two
complete proofs one step at a time, and ends with what to do when you are
stuck. Type everything in. Do not paste.

If you have not used Lean before, play the Tutorial, Addition and
Multiplication worlds of the Natural Number Game (about two hours; linked in
the reading list) before Day 1.

# Your working setup

Open the repository folder in VS Code. Open the whole folder, not a single
file, or `import Tau` will not be found. The folder `course/Work/` is for
your own files. It already has `Scratch.lean`, which sets up `import Tau`
and `open Tau` after a short header comment:

```
import Tau
...
open Tau
```

`import Tau` makes the whole library available. `open Tau` lets you write
`Block` instead of `Tau.Block`. While Lean is checking a file, an orange bar
runs down the margin; wait for it to go away.

Files in `course/Work/` are yours. VS Code checks them as you type. To check
one from a terminal, run `lake build Work.Scratch`. A file
`course/Work/Foo.lean` is the module `Work.Foo`, so a later file can start
with `import Work.Foo` and use what you defined there.

If you played the Natural Number Game: its Lean is slightly different. It
writes `induction n with d hd`. Here that is written with one line per case,
as you will see below.

On the right is the _infoview_. It shows what Lean knows at the position of
your cursor. Keep it open at all times. If it is not there, press
`Ctrl+Shift+Enter` (`Cmd+Shift+Enter` on macOS).

A file is correct when it has no red underlines. A yellow underline is a
warning. The warning you will see most is `declaration uses 'sorry'`, which
means a proof is unfinished.

Lean code uses symbols such as `→`, `∀`, `⟨`, `⟩` and `·`. Type them with a
backslash and a name: `\to` gives `→`, `\forall` gives `∀`, `\<` and `\>`
give `⟨` and `⟩`, `\.` gives `·`, `\le` gives `≤`, `\ne` gives `≠`. The
symbol appears when you type a space or the next character. To learn how to
type a symbol you see, hover the mouse over it.

When you change a file that another open file imports, the importing file
does not see the change at once. It shows a message that its imports are out
of date, with a button to restart the file. Click it.

If nothing works at all (no infoview messages, `import Tau` underlined, or
an error that `lake` cannot be found), check in this order: the folder open
in VS Code is the repository folder; `lake build Tau` succeeds in a terminal
in that folder; VS Code was started after elan was installed.

# Programs

A definition has a name, arguments with types, a result type, and a body.

```lean
def double (n : Nat) : Nat := n + n
```

Put the cursor on a line starting with `#eval` and the infoview shows the
value.

```lean
#eval double 21
```

A structure groups values. A function on a structure is usually put in the
structure's namespace, so it can be called with a dot. Adding `deriving Repr`
tells Lean how to print values for `#eval`.

```lean
structure Point where
  x : Nat
  y : Nat
  deriving Repr

def Point.swap (p : Point) : Point := { x := p.y, y := p.x }

#eval (Point.mk 1 2).swap
```

A function on a list or on a natural number is usually written by cases. The
case for `t + 1` may call the function on `t`. This is _recursion_, and it is
how every "for all cycles" definition in this course is written.

```lean
def sumList : List Nat → Nat
  | [] => 0
  | x :: rest => x + sumList rest

#eval sumList [1, 2, 3]
```

`{ p with y := 5 }` is a copy of the structure `p` in which the field `y` has
been replaced.

```lean
#eval ({ (Point.mk 1 2) with y := 5 }).x
```

Hardware commands and instructions are written as _inductive types_, listing
each case with `|`, and handled with `match`.

```lean
inductive Cmd where
  | hold
  | add (x : Nat)
  | clear
  deriving Repr

def applyCmd (s : Nat) (c : Cmd) : Nat :=
  match c with
  | .hold => s
  | .add x => s + x
  | .clear => 0

#eval applyCmd 10 (.add 5)
```

A dot in front of a name, as in `.add 5`, means "the constructor of that name
of whatever type is expected here". `abbrev` gives an existing type a shorter
name:

```lean
abbrev Words := List Nat
```

`if c then a else b` chooses `a` when the Boolean `c` is `true` and `b`
otherwise. `a == b` compares values and returns a `Bool` (`true` or
`false`), whereas `a = b` is a mathematical equation you can state and prove.
`fun x => ...` is a function without a name. `Option α` is either `none` or
`some x`. `(a, b)` is a pair, and `.1` and `.2` take it apart.

# Statements and proofs

`example` states something and proves it, without giving it a name. `theorem`
does the same and gives it a name, so that it can be used later.

The simplest proof is `rfl` (for _reflexivity_). It asks Lean to unfold
definitions and compute both sides; if they reduce to the exact same value,
`rfl` closes the equation.

```lean
example : double 2 = 4 := rfl
example : sumList [1, 2, 3] = 6 := rfl
example : (Point.mk 1 2).swap = { x := 2, y := 1 } := rfl
```

Most proofs are written after the word `by`, as a list of _tactics_. Each
tactic changes the _goal_: what remains to be proved. Put the cursor at the
end of any line of a proof and the infoview shows the goal at that point.
Reading a proof means moving the cursor down it and watching the goal. Do
this for every proof you read in this course.

# A first block, and a proof by computing

Every hardware component in this course is a `Block`: a starting state and a
`step` function that takes the current state and input and returns the next
state and output. A `Signal` gives one input per cycle (`Nat → α`).

{docstring Tau.Signal}

{docstring Tau.Block}

{docstring Tau.Block.stateAt}

{docstring Tau.Block.outAt}

In `spec/Tau/Blocks/Basic.lean` (read in full in the next chapter), `stateAt`
starts at `b.init` at cycle `0` and steps with `(b.step (b.stateAt inp t)
(inp t)).1` at `t + 1`; `outAt` at cycle `t` is `(b.step (b.stateAt inp t)
(inp t)).2`.

This block outputs whatever it was given on the previous cycle.

```lean
def register {α : Type} (reset : α) : Block α α α where
  init := reset
  step s x := (x, s)
```

The curly braces around `α : Type` make it an argument Lean fills in by
itself. `Block α α α` says the state, the input and the output all have type
`α`.

Run it for four cycles on the inputs 10, 11, 12, 13:

```lean
example : (register 0).trace (fun t => 10 + t) 4 = [0, 10, 11, 12] := by
  decide
```

`decide` asks Lean to evaluate both sides and compare. It works for one
concrete case. Now the statement for every cycle and every input:

```lean
theorem register_outAt_succ {α : Type} (reset : α) (inp : Signal α) (t : Nat) :
    (register reset).outAt inp (t + 1) = inp t := by
  -- ⊢ (register reset).outAt inp (t + 1) = inp t
  rfl
```

The comment shows the goal, as the infoview would. The symbol `⊢` separates
what is known from what is to be proved. Unfolding `outAt` at `t + 1` gives
the state of `register` at `t + 1` (because `step s x` returns `s` as `.2`),
and unfolding `stateAt` at `t + 1` gives `inp t` (because `step s x` returns
`x` as `.1`). Both sides compute to `inp t`, so `rfl` closes the goal.

When `rfl` works, the theorem is true by definition. That is the best kind of
proof and you should always try it first.

# A second block, and a proof by induction

This block counts the cycles on which its input was `true`. Its output is the
count so far.

```lean
def counter : Block Nat Bool Nat where
  init := 0
  step n en := (if en then n + 1 else n, n)

example : counter.trace (fun t => t % 2 == 0) 6 = [0, 1, 1, 2, 2, 3] := by
  decide
```

To say what it outputs at every cycle, we need to say "the number of `true`
inputs before cycle `t`" in Lean. That is a definition of our own, by
recursion on `t`:

```lean
def countTrue (inp : Signal Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => countTrue inp t + (if inp t then 1 else 0)
```

Now the theorem about the state. `rfl` will not do: the statement is about
every `t`, and no amount of computing reaches every `t`. The proof is by
induction, which follows the recursion in the two definitions.

```lean
theorem counter_stateAt (inp : Signal Bool) (t : Nat) :
    counter.stateAt inp t = countTrue inp t := by
  induction t with
  | zero =>
    -- ⊢ counter.stateAt inp 0 = countTrue inp 0
    rfl
  | succ t ih =>
    -- ih : counter.stateAt inp t = countTrue inp t
    -- ⊢ counter.stateAt inp (t + 1) = countTrue inp (t + 1)
    rw [Block.stateAt_succ, ih]
    -- ⊢ (counter.step (countTrue inp t) (inp t)).fst = countTrue inp (t + 1)
    by_cases h : inp t
    · -- h : inp t = true
      simp [counter, countTrue, h]
    · -- h : ¬inp t = true
      simp [counter, countTrue, h]
```

Read it with the goal in view.

* `induction t with` splits the proof into the case `t = 0` and the case
  `t + 1`. In the second case you are given `ih`, the statement for `t`.
* The zero case is true by definition, so `rfl`.
* `rw [Block.stateAt_succ, ih]` rewrites the goal twice. The lemma
  `Block.stateAt_succ` says what the state at `t + 1` is in terms of the
  state at `t`. Then `ih` replaces the state at `t` by `countTrue inp t`.
  After a `rw`, look at the goal. It has changed exactly as the lemma says.
* The goal now depends on whether the input at cycle `t` is `true`.
  `by_cases h : inp t` splits into the two cases and names the fact `h`
  (`inp t = true` in the first branch, `¬inp t = true` in the second).
* Each `·` focuses on one branch at a time. `simp [counter, countTrue, h]`
  simplifies the goal using the definitions of `counter` and `countTrue` and
  the fact `h`. In each case that is enough.

The theorem about the output follows from the one about the state. No second
induction is needed.

```lean
theorem counter_outAt (inp : Signal Bool) (t : Nat) :
    counter.outAt inp t = countTrue inp t := by
  unfold Block.outAt
  -- ⊢ (counter.step (counter.stateAt inp t) (inp t)).snd = countTrue inp t
  rw [counter_stateAt]
  rfl
```

This is the shape of every proof about a block in the block chapters.

1. Define, by recursion, the function the block is supposed to compute.
2. Prove by induction on the cycle that the state is that function.
3. Derive the statement about the output.

Step 1 is the reference function you want to prove the block matches. If
`countTrue` is wrong, the theorem is proved and useless. Check it the way
you check a program: evaluate it on an input for which you know the answer.

```lean
example : countTrue (fun t => t % 2 == 0) 5 = 3 := by decide
```

# Doing an exercise

The first exercise file comes in the next chapter. Whichever file it is, the
method is the same. Open it and find the first `sorry`.

1. Put the cursor just before `sorry` and read the goal in the infoview. Read
   the hypotheses above the `⊢` as well.
2. Delete `sorry` and try `rfl`.
3. If the statement is about every cycle or every length, start with
   `induction` on that variable.
4. After every tactic, look at the goal again before typing the next one.
5. The file is finished when it has no `sorry` and no red underline. Check
   from a terminal, for example:

```
lake build Prove.Blocks.Basic
```

A finished file prints no warning about `sorry`.

The chapter "Tactic reference" near the end of the book has one worked
example of every tactic the course uses. Keep it open in a second window.

# When you are stuck

Work down this list. Do not skip to the last item.

1. *Read the goal aloud.* Say what each side means. Many stuck proofs are
   attempts to prove something other than what the goal says.
2. *Unfold.* If the goal mentions a definition and nothing happens, the
   tactics may not be looking inside it. Try `unfold name`, or
   `simp only [name]`, and look at the goal again.
3. *Split.* If the goal contains `if` or `match`, use `split`. If it depends
   on a fact that may or may not hold, use `by_cases h : fact`.
4. *Ask Lean.* `simp?` reports which lemmas `simp` used. `exact?` searches
   the library for a lemma that closes the goal. `rw?` searches for a
   rewrite.
5. *State the missing fact.* If you know why the goal is true, write that
   reason as `have h : ... := by sorry`, finish the proof using `h`, and then
   come back and prove `h`.
6. *Test the statement.* If nothing works, the statement may be false. Put
   concrete numbers in and evaluate both sides with `#eval`.
7. *Look at one line.* Open the solution under `spec/Tau/Proofs/`, read the first
   tactic of the proof, and close the file. Repeat only if you are stuck
   again after a quarter of an hour.

# Messages you will see

* `unsolved goals`: the proof ended while something was still to be proved.
  The message shows what.
* `type mismatch`: you gave a term of one type where another was expected.
  Compare the two types in the message character by character.
* `omega could not prove the goal` (`omega` is introduced in the next chapter
  for natural-number arithmetic): the arithmetic fact is false, or it
  involves multiplication of variables, or the hypothesis it needs is not in
  the context. Check the fact by hand first.
* `simp made no progress`: none of the lemmas applied. Unfold a definition,
  or name the lemma you meant.
* `The rfl tactic failed`: the two sides do not compute to the same thing.
  You need a real proof.

# Exercises

*Prove and state.* In `course/Work/Scratch.lean`, define a block that remembers
the largest input it has seen so far:

```
def runMax : Block Nat Nat Nat where
  init := 0
  step m x := sorry
```

Check it with `trace` and `decide`. Then write, by recursion on the cycle,
the function `maxTo inp t` that its state should equal, test that function
on an input for which you know the answer, and prove
`runMax.stateAt inp t = maxTo inp t`. Follow the proof of `counter_stateAt`.
If you defined things the natural way, the step case needs only
`rw [Block.stateAt_succ, ih]` and `rfl`.

*Specify from prose.* A saturating down-counter holds a `Nat` starting from
`start`. On each cycle it takes a command: either tick down by 1 (stopping at
0) or reload with a new value `n`. Its output is the current count. In
`course/Work/Scratch.lean`, write an `inductive` command type and a `Block`
from this description, run `#eval` on two input signals with `.trace`, and
write in a comment one detail the description left open (for example, what a
`reload` outputs in the cycle it arrives).

# Checkpoint

You can define functions, structures, inductive types and blocks, run them
with `#eval` and `decide`, state a theorem about every cycle, and prove it
by `rfl` or by induction while watching the goal.
