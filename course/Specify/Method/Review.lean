import Specify.Support.Harness

/-!
# Review: what came back from the agent

In each section a person asked for a proof of a statement, written as a
named proposition (`Asked`), and an agent sent back a theorem (`returned`).
Every file compiles. Four of the five should not be accepted as they are.

For each section decide: accept or not, and why. The chapter "Writing a
specification" gives the list of things to look at. The answers are in
`course/Specify/Answers/Review.md`.
-/

namespace Specify.Review

open Tau

/-! ## 1. The shift register delays its input -/

namespace One

/-- "From cycle `n` on, a shift register of depth `n` outputs the input of
`n` cycles earlier." -/
def Asked : Prop :=
  ∀ (n : Nat) (reset : Int) (inp : Signal Int) (t : Nat),
    n ≤ t → (shiftRegister n reset).outAt inp t = inp (t - n)

theorem returned (n : Nat) (reset : Int) (inp : Signal Int) (t : Nat) (h : n < t) :
    (shiftRegister n reset).outAt inp t = inp (t - n) := by
  simp only [shiftRegister_outAt, Nat.le_of_lt h, ↓reduceIte]

end One

/-! ## 2. The accumulator sums its inputs -/

namespace Two

/-- "An accumulator told to add on every cycle outputs, at cycle `t`, the sum
of the first `t` inputs." -/
def Asked : Prop :=
  ∀ (x : Signal Nat) (t : Nat),
    (accumulator 0).outAt (fun k => .add (x k)) t = sumTo 0 x t

theorem returned (x : Signal Nat) (hx : ∀ k, x (k + 1) < x k) (t : Nat) :
    (accumulator 0).outAt (fun k => .add (x k)) t = sumTo 0 x t :=
  accumulator_outAt_add 0 x t

end Two

/-! ## 3. The multiply-accumulate cell computes a dot product -/

namespace Three

/-- "A MAC cell fed one pair per cycle outputs, at cycle `t`, the dot product
of the first `t` pairs." -/
def Asked : Prop :=
  ∀ (a b : Signal Int) (t : Nat),
    (mac 0).outAt (fun k => .add (a k, b k)) t = sumTo 0 (fun k => a k * b k) t

theorem state_is_sum (a b : Signal Int) (t : Nat) :
    (mac 0).stateAt (fun k => .add (a k, b k)) t = sumTo 0 (fun k => a k * b k) t := by
  sorry

theorem output_is_state (a b : Signal Int) (t : Nat) :
    (mac (0 : Int)).outAt (fun k => .add (a k, b k)) t =
      (mac 0).stateAt (fun k => .add (a k, b k)) t := by
  simp [Block.outAt, mac, Block.mapIn, accumulator, AccIn.map]

theorem returned : Asked := by
  intro a b t
  rw [output_is_state, state_is_sum]

end Three

/-! ## 4. A clear takes effect on the next cycle -/

namespace Four

/-- An accumulator that starts at `zero`. -/
def accumulator (zero : Int) : Block Int (AccIn Int) Int where
  init := zero
  step s c :=
    match c with
    | .hold => (s, s)
    | .add x => (s + x, s)
    | .clear => (zero, zero)
    | .load x => (x, s)

/-- "If the command at cycle `t` is `clear`, the output at cycle `t + 1` is
the starting value." -/
def Asked : Prop :=
  ∀ (zero : Int) (inp : Signal (AccIn Int)) (t : Nat),
    inp t = .clear → inp (t + 1) = .hold → (accumulator zero).outAt inp (t + 1) = zero

theorem returned : Asked := by
  intro zero inp t h h'
  simp [Block.outAt, Block.stateAt, accumulator, h, h']

end Four

/-! ## 5. The sequencer issues what is due -/

namespace Five

/-- "At cycle `t` a sequencer outputs the items of its program that are due
at `t`." -/
def Asked : Prop :=
  ∀ (prog : List (Nat × String)) (inp : Signal Unit) (t : Nat),
    (sequencer prog).outAt inp t = (prog.filter fun e => e.1 == t).map fun e => e.2

theorem returned : Asked := by
  intro prog inp t
  exact sequencer_outAt prog inp t

end Five

end Specify.Review
