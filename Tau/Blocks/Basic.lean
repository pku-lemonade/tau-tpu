/-!
# Blocks

A *block* is a clocked component. It holds some state. On every cycle it reads
one input, produces one output, and moves to a new state.

Every hardware component in tau-tpu is a block, from a shift register up to a
whole slice. They all share the three definitions in this file, so one way of
running a block and one way of stating a theorem about it works for all of them.

Cycle numbering: cycles are numbered from 0. During cycle `t` a block

* starts in the state `stateAt inp t`,
* reads the input `inp t`,
* produces the output `outAt inp t`, and
* ends in the state `stateAt inp (t + 1)`.

Docs: Machine 1 (`Tau/Docs/`).
-/

namespace Tau

/-- A signal: the value present on a wire during each cycle. -/
abbrev Signal (α : Type) : Type := Nat → α

/-- A clocked component with state `σ`, input `ι` and output `ο`. -/
structure Block (σ ι ο : Type) where
  /-- The state at the start of cycle 0. -/
  init : σ
  /-- One cycle. Given the current state and this cycle's input, returns the
  next state and this cycle's output. -/
  step : σ → ι → σ × ο

namespace Block

variable {σ ι ο : Type}

/-- The state at the start of cycle `t`, when the block is fed the signal `inp`. -/
def stateAt (b : Block σ ι ο) (inp : Signal ι) : Nat → σ
  | 0 => b.init
  | t + 1 => (b.step (b.stateAt inp t) (inp t)).1

/-- The output during cycle `t`, when the block is fed the signal `inp`. -/
def outAt (b : Block σ ι ο) (inp : Signal ι) (t : Nat) : ο :=
  (b.step (b.stateAt inp t) (inp t)).2

/-- The outputs of cycles `0` to `n - 1`. Use it with `#eval` to run a block. -/
def trace (b : Block σ ι ο) (inp : Signal ι) (n : Nat) : List ο :=
  (List.range n).map (b.outAt inp)

/-- Put a function in front of a block's input. The block `b.mapIn f` behaves
like `b`, but each input `x` is first turned into `f x`. -/
def mapIn {ι' : Type} (b : Block σ ι ο) (f : ι' → ι) : Block σ ι' ο where
  init := b.init
  step s x := b.step s (f x)

end Block

/-- `sumTo zero x n` is `zero + x 0 + x 1 + ... + x (n - 1)`, added left to right. -/
def sumTo {α : Type} [Add α] (zero : α) (x : Nat → α) : Nat → α
  | 0 => zero
  | n + 1 => sumTo zero x n + x n

end Tau
