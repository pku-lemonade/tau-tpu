import Tau.IR.Kernel

/-!
# Source programs

The first form a program takes: what the user wrote. A source program is a
kernel that may also *call* other kernels. It is what the Python frontend
records (`frontend/`), and the Lean model of a module of the compiler's `tau`
dialect with `tau.call` in it.

A call names the kernel to run, the caller's buffers that the kernel's own
buffers stand for, and an *origin*: the cycle that the kernel's pins count
from. The called kernel has its own variables. It sees only the buffers it is
given, and it cannot be given the same buffer twice.

What a source program computes (`Source.run`) and when (`Source.timeline`) are
the standard for everything below: a compiled program is right if the
machine, running it, ends with the buffers that `Source.run` gives and issues
the words of `Source.timeline` on their cycles.

`tau-inline` turns a source program into a kernel with no calls
(`Tau/IR/Kernel.lean`), by copying each called kernel in. `checkInlined`
(`Tau/Check/Passes.lean`) checks its output.

The forms, in order: this file, `Tau/IR/Kernel.lean`, `Tau/IR/Placed.lean`,
`Tau/IR/Compiled.lean`.

Terms to look up: *function inlining*, *call by reference*.

Docs: Programs 4 and 6 (`Tau/Docs/`).
-/

namespace Tau

/-- A source program: items and calls, in order. -/
inductive Source where
  /-- Nothing more to do. -/
  | done
  /-- A statement or a loop, then `rest`. -/
  | item (it : Item) (rest : Source)
  /-- Run `callee` with its buffer `j` standing for the caller's buffer
  `args[j]` and its pins counted from cycle `origin`, then `rest`. -/
  | call (callee : Source) (args : List Nat) (origin : Nat) (rest : Source)
  deriving DecidableEq, Repr

/-- A kernel as a source program with no calls. -/
def Source.ofKernel : Kernel → Source
  | [] => .done
  | it :: rest => .item it (Source.ofKernel rest)

variable {V : Type}

/-- An event of a called kernel as an event of its caller: the cycle counts
from `origin`, and a store goes to the caller's buffer. -/
def Event.rebase (args : List Nat) (origin : Nat) (e : Event V) : Event V :=
  ⟨origin + e.time, e.store.map fun bk => (args[bk.1]?.getD bk.1, bk.2), e.word⟩

/-- The caller's buffers after a call: buffer `args[j]` now holds what the
called kernel left in its buffer `j`. -/
def writeBack (bufs : List (List V)) : List Nat → List (List V) → List (List V)
  | b :: args, x :: inner => writeBack (bufs.set b x) args inner
  | _, _ => bufs

/-- The caller's environment after a call that ended in `inner`. The caller
keeps its variables. -/
def Env.returnFrom (env : Env V) (args : List Nat) (origin : Nat) (inner : Env V) : Env V :=
  { env with
    bufs := writeBack env.bufs args inner.bufs
    events := inner.events.map (Event.rebase args origin) ++ env.events }

/-- Whether a call may be made: every buffer it passes exists, and none is
passed twice. -/
def callable (args : List Nat) (buffers : Nat) : Bool :=
  args.all (· < buffers) && args.Nodup

/-- Run a source program from an environment. `none` if a statement fails or
a call is not `callable`. -/
def Source.exec (S : Sem V) : Source → Env V → Option (Env V)
  | .done, env => some env
  | .item it rest, env =>
    match it.exec S env with
    | some env' => rest.exec S env'
    | none => none
  | .call callee args origin rest, env =>
    if callable args env.bufs.length then
      match callee.exec S ⟨[], args.map fun b => env.bufs[b]?.getD [], []⟩ with
      | some inner => rest.exec S (env.returnFrom args origin inner)
      | none => none
    else none

/-- Run a source program on the given buffer contents and return the final
contents. -/
def Source.run (S : Sem V) (s : Source) (bufs : List (List V)) : Option (List (List V)) :=
  match s.exec S ⟨[], bufs, []⟩ with
  | some env => some env.bufs
  | none => none

/-- The events of a source program run on the given buffer contents: for
every pinned statement, its word and its cycle. Empty if the run fails. -/
def Source.timeline (S : Sem V) (s : Source) (bufs : List (List V)) : List (Event V) :=
  match s.exec S ⟨[], bufs, []⟩ with
  | some env => env.events
  | none => []

end Tau
