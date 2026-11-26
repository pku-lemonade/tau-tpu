import Specify.Support.Harness

/-!
# Repair: statements that are false as written

Each statement below sounds right and is false. An agent asked to prove it
gets stuck, and where it gets stuck tells you what is missing.

For each one:

1. Find an input that makes it false. Use `#eval` on the two sides.
2. Read the goal the agent got stuck on, quoted in the comment.
3. Change the statement so that it is true and still says something useful.
   Usually that means adding a hypothesis.
4. Ask an agent for the proof, or find the theorem in `spec/Tau/Proofs/Blocks/`
   that already says it.

Repaired statements, with proofs, are under "Repairs" in
`spec/tests/TauTest/SpecSolutions.lean`.
-/

namespace Specify.Repair

open Tau

/-- "The output of a shift register is the input of `n` cycles earlier."

The agent got stuck on `reset = inp 0`, in the case `t < n`. -/
def ShiftDelays : Prop :=
  ∀ (n : Nat) (reset : Int) (inp : Signal Int) (t : Nat),
    (shiftRegister n reset).outAt inp t = inp (t - n)

/-- The value a command adds, and 0 for a command that adds nothing. -/
def added : AccIn Int → Int
  | .add x => x
  | _ => 0

/-- "The output of an accumulator is the sum of everything added so far."

The agent got stuck on a goal with `inp t = AccIn.clear` among its
hypotheses. -/
def AccumulatorSums : Prop :=
  ∀ (inp : Signal (AccIn Int)) (t : Nat),
    (accumulator 0).outAt inp t = sumTo 0 (fun k => added (inp k)) t

/-- "A read just after a write to the same address returns the value written."

The agent got stuck on `none = some x`. -/
def ReadsBack : Prop :=
  ∀ (n : Nat) (init : Vector Int n) (inp : Signal (MemIn Int)) (t a : Nat) (x : Int),
    inp t = .write a x → inp (t + 1) = .read a →
      (memory n init).outAt inp (t + 1) = some x

end Specify.Repair
