import Tau.Machine.Arch
import Tau.Isa.Event

/-!
# What the machine issues, and when

`Tau.Machine.Arch` says what the memories hold after a run. This
file says what happened on the way: on which cycle each slice issued which
word. A slice *issues* a word when it runs an instruction that has a result,
or one that writes a word to memory.

`issues` is the list for a whole run. `Compiled.timeline`
(`Tau.IR.Compiled`) turns it into the events that pins are checked
against.

Nothing here changes what the machine does.

Docs: Machine 3.9 (`docs/`).
-/

namespace Tau

variable {V : Type}

/-- The word an instruction issues, given what the instruction read and what
`exec` returned for it: the result, or for a write the word written. With the
address, for a write. -/
def issued (rd : Track → Option V) (i : Instr) (r : Option (Track × V)) :
    Option (Option Nat × V) :=
  match r, i with
  | some (_, v), _ => some (none, v)
  | none, .write src addr => (rd src).map fun v => (some addr, v)
  | none, _ => none

/-- What the slice at `p` issues in the cycle that starts in `s`. -/
def State.issue (S : Sem V) (cfg : Config) (prog : Program) (s : State V) (p : Nat) :
    Option (Issue V) :=
  match prog.dueAt p s.time, cfg.kindAt p, s.slices[p]? with
  | [i], some kind, some sl =>
    match exec S cfg kind (s.sample p) sl i with
    | .ok (_, r) => (issued (s.sample p) i r).map fun aw => ⟨s.time, p, aw.1, aw.2⟩
    | .error _ => none
  | _, _, _ => none

/-- What every slice issues in the cycle that starts in `s`. -/
def State.issues (S : Sem V) (cfg : Config) (prog : Program) (s : State V) : List (Issue V) :=
  (List.range s.slices.length).filterMap (s.issue S cfg prog)

/-- What is issued in `n` cycles from the state `s`, up to a trap if there is
one. -/
def issuesFrom (S : Sem V) (cfg : Config) (prog : Program) : Nat → State V → List (Issue V)
  | 0, _ => []
  | n + 1, s =>
    s.issues S cfg prog ++
      match step S cfg prog s with
      | .ok s' => issuesFrom S cfg prog n s'
      | .error _ => []

/-- What is issued when a program is run for `n` cycles from a memory image. -/
def issues (S : Sem V) (cfg : Config) (prog : Program) (n : Nat) (image : List (List V)) :
    List (Issue V) :=
  issuesFrom S cfg prog n (State.init S cfg image)

end Tau
