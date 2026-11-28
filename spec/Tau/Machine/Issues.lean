import Tau.Machine.SliceLevel
import Tau.Isa.Event

/-!
# What the machine issues, and when

`Tau.Machine.SliceLevel` says what the memories hold after a run. This
file says what happened on the way: on which cycle each slice issued which
word. A slice *issues* a word when it runs an instruction that has a result,
or one that writes a word to memory. A result of several words is as many
issued words.

`issues` is the list for a whole run. `Compiled.timeline`
(`Tau.IR.Compiled`) turns it into the events that pins are checked
against.

Nothing here changes what the machine does.

Docs: Machine 3.9 (`docs/`).
-/

namespace Tau

variable {V : Type}

/-- The words an instruction issues, given what the instruction read and what
`exec` returned for it: the words of the result, or for a write the word
written, with its address. -/
def issued (rd : Stream → Option V) (i : Instr) (r : Option (Stream × List V)) :
    List (Option Nat × V) :=
  match r, i with
  | some (_, vs), _ => vs.map fun v => (none, v)
  | none, .write src addr => ((rd src).map fun v => (some addr, v)).toList
  | none, _ => []

/-- What one instruction issues at the slice at `p` in the cycle that starts
in `s`, with the slice in the state `sl`. -/
def State.issueOf (S : Sem V) (cfg : Config) (s : State V) (p : Nat) (kind : Kind)
    (sl : Slice V) (i : Instr) : List (Issue V) :=
  match exec S cfg kind (s.sample p) sl i with
  | .ok (_, r) => (issued (s.sample p) i r).map fun aw => ⟨s.time, p, aw.1, aw.2⟩
  | .error _ => []

/-- What the slice at `p` issues in the cycle that starts in `s`: the words of
the instruction it runs, or the word read and the word written when it runs a
read and a write. -/
def State.issue (S : Sem V) (cfg : Config) (prog : Program) (s : State V) (p : Nat) :
    List (Issue V) :=
  match prog.dueAt p s.time, cfg.kindAt p, s.slices[p]? with
  | [i], some kind, some sl => s.issueOf S cfg p kind sl i
  | [i, j], some kind, some sl =>
    match Instr.readWrite i j with
    | some (r, w) => s.issueOf S cfg p kind sl r ++ s.issueOf S cfg p kind sl w
    | none => []
  | _, _, _ => []

/-- What every slice issues in the cycle that starts in `s`. -/
def State.issues (S : Sem V) (cfg : Config) (prog : Program) (s : State V) : List (Issue V) :=
  (List.range s.slices.length).flatMap (s.issue S cfg prog)

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
