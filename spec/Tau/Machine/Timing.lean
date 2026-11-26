import Tau.Machine.Arch

/-!
# What the timing rule is stated with

`spec/Tau/Machine/Arch.lean` defines one cycle of the machine. The timing
rule is about many cycles: a result computed at slice `p` on cycle `t` is at
slice `q` on cycle `t + delay + 1 + |q - p|`. To state it one needs names for
"the states of a run", "the result a slice computes in a cycle" and "what a
slice places on a stream in a cycle". They are defined here.

Nothing here changes what the machine does. The rule itself is stated in
`spec/Tau/Claims.lean` and proved in `spec/Tau/Proofs/Machine/Timing.lean`.

Docs: Machine 3.4 (`docs/`).
-/

namespace Tau

variable {V : Type}

/-- The states of a run of `n` cycles that does not trap: `st u` is the state
at the start of cycle `u`. -/
def IsRun (S : Sem V) (cfg : Config) (prog : Program) (st : Nat → State V) (n : Nat) : Prop :=
  ∀ u, u < n → step S cfg prog (st u) = .ok (st (u + 1))

/-- A state has the shape of the machine: the right number of streams, every
stream as long as the row of slices, one slice state per position, and in
every slice a pipe as long as the delay of its kind. -/
structure State.Shaped (cfg : Config) (s : State V) : Prop where
  /-- There are `cfg.streams` streams going east. -/
  east : s.east.length = cfg.streams
  /-- There are `cfg.streams` streams going west. -/
  west : s.west.length = cfg.streams
  /-- Every stream going east has one slot per slice. -/
  eastRow : ∀ (id : Nat) (row : List (Option V)),
    s.east[id]? = some row → row.length = cfg.kinds.length
  /-- Every stream going west has one slot per slice. -/
  westRow : ∀ (id : Nat) (row : List (Option V)),
    s.west[id]? = some row → row.length = cfg.kinds.length
  /-- There is one slice state per position. -/
  slices : s.slices.length = cfg.kinds.length
  /-- The pipe of every slice is as long as the delay of its kind. -/
  pipe : ∀ (p : Nat) (sl : Slice V) (kind : Kind),
    s.slices[p]? = some sl → cfg.kindAt p = some kind → sl.pipe.length = cfg.delay kind

/-- The result that the slice at `p` computes in the cycle that starts in
`s`, with the stream it is meant for. This is what `exec` returns, before the
result enters the pipe. `none` if no instruction is due or the instruction
has no result. -/
def State.result (S : Sem V) (cfg : Config) (prog : Program) (s : State V) (p : Nat) :
    Option (Track × V) :=
  match prog.dueAt p s.time, cfg.kindAt p, s.slices[p]? with
  | [i], some kind, some sl =>
    match exec S cfg kind (s.sample p) sl i with
    | .ok (_, r) => r
    | .error _ => none
  | _, _, _ => none

/-- What comes out of the pipe of the slice at `p` in the cycle that starts in
`s`. This is the result that the machine places on a stream at position `p`. -/
def State.out (S : Sem V) (cfg : Config) (prog : Program) (s : State V) (p : Nat) :
    Option (Track × V) :=
  match s.slices[p]? with
  | some sl =>
    match stepSlice S cfg prog s p sl with
    | .ok (_, o) => o
    | .error _ => none
  | none => none

/-- What stream `tr` holds one position upstream of `p`. This is the word
that reaches `p` on the next cycle, if no slice places a result there. -/
def State.upstream (s : State V) (p : Nat) (tr : Track) : Option V :=
  match tr.dir with
  | .east => if p = 0 then none else s.sample (p - 1) tr
  | .west => s.sample (p + 1) tr

end Tau
