import Specify.Support.Tables

/-!
# Three candidates, one right

For each of the first three components there are three definitions here. One
of them is what the doc describes. The other two are wrong, and all three
give every row of the doc's table.

For each component:

1. Put the cursor on the three `#eval report` lines. All agree with the
   table.
2. Read section 2.1, 2.2 or 2.3 of `docs/Machine.md` again, the words this
   time. Find an input on which the candidates differ, with
   `#eval (candidateA ...).trace ... n`. Decide which one the words describe.
3. For each wrong candidate, say whether it contradicts a sentence of the
   doc or settles something the doc does not say.
4. Write a statement, as in the chapter, that the right candidate satisfies
   and a wrong one does not. A table could not tell them apart. A statement
   about every input can.

The answers are the `#guard` lines under "Candidates" in
`course/tests/CourseTest/SpecSolutions.lean`.
-/

namespace Specify.Candidates

open Tau Specify

/-! ## Shift register (section 2.1) -/

namespace ShiftRegister

/-- Candidate A. -/
def candidateA (n : Nat) (reset : Int) : Block (List Int) Int Int where
  init := List.replicate (max n 1) reset
  step s x := ((x :: s).dropLast, (x :: s).getLast?.getD x)

/-- Candidate B. -/
def candidateB (n : Nat) (reset : Int) : Block (List Int) Int Int where
  init := List.replicate n reset
  step s x := ((x :: s).dropLast, (x :: s).getLast?.getD x)

/-- Candidate C. -/
def candidateC (n : Nat) (_reset : Int) : Block (List Int) Int Int where
  init := List.replicate n 0
  step s x := ((x :: s).dropLast, (x :: s).getLast?.getD x)

#eval report "shift register, candidate A" (Tables.shiftRegister candidateA)
#eval report "shift register, candidate B" (Tables.shiftRegister candidateB)
#eval report "shift register, candidate C" (Tables.shiftRegister candidateC)

end ShiftRegister

/-! ## Accumulator (section 2.2) -/

namespace Accumulator

/-- Candidate A. -/
def candidateA (zero : Int) : Block Int (AccIn Int) Int where
  init := zero
  step s c :=
    match c with
    | .hold => (s, s)
    | .add x => (s + x, s)
    | .clear => (0, s)
    | .load x => (x, s)

/-- Candidate B. -/
def candidateB (zero : Int) : Block Int (AccIn Int) Int where
  init := zero
  step s c :=
    match c with
    | .hold => (s, s)
    | .add x => (s + x, s)
    | .clear => (zero, s)
    | .load x => (x, x)

/-- Candidate C. -/
def candidateC (zero : Int) : Block Int (AccIn Int) Int where
  init := zero
  step s c :=
    (match c with
     | .hold => s
     | .add x => s + x
     | .clear => zero
     | .load x => x,
     s)

#eval report "accumulator, candidate A" (Tables.accumulator candidateA)
#eval report "accumulator, candidate B" (Tables.accumulator candidateB)
#eval report "accumulator, candidate C" (Tables.accumulator candidateC)

end Accumulator

/-! ## Multiply-accumulate cell (section 2.3) -/

namespace Mac

/-- Candidate A. -/
def candidateA (zero : Int) : Block Int (AccIn (Int × Int)) Int where
  init := zero
  step s c :=
    match c with
    | .hold => (s, s)
    | .add (a, b) => (s + a * b, s)
    | .clear => (zero, s)
    | .load (a, b) => (a * b, s)

/-- Candidate B. -/
def candidateB (zero : Int) : Block Int (AccIn (Int × Int)) Int where
  init := zero
  step s c :=
    match c with
    | .hold => (s, s)
    | .add (a, b) => (s + (a * b).natAbs, s)
    | .clear => (zero, s)
    | .load (a, b) => (a * b, s)

/-- Candidate C. -/
def candidateC (zero : Int) : Block Int (AccIn (Int × Int)) Int where
  init := zero
  step s c :=
    match c with
    | .hold => (s, s)
    | .add (a, b) => (s + a * b, s)
    | .clear => (zero, s)
    | .load (a, _) => (a, s)

#eval report "MAC, candidate A" (Tables.mac candidateA)
#eval report "MAC, candidate B" (Tables.mac candidateB)
#eval report "MAC, candidate C" (Tables.mac candidateC)

end Mac

end Specify.Candidates
