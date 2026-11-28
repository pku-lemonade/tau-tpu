import Tau.Isa.Op
import Tau.Isa.Event

/-!
# Kernels

A *kernel* is a program with no machine in it: load values from buffers,
compute, and store values back. A buffer is a row of words, and a value of a
type (`Tau.Isa.Word`) is as many words of it as the type has bytes: the value
at position `k` of a buffer of values of 4 bytes is its words `4 * k` to
`4 * k + 3`. It says nothing about slices or streams, and about
cycles only where a statement is pinned. It is the Lean model of one function
of the compiler's `tau` dialect (see `compiler/`), and the second IR a
program takes: a source program (`Tau.IR.Source`) is a kernel that may
also call other kernels, and `tau-inline` turns it into one that does not.

What a kernel computes (`Kernel.run`) and what a source program computes are
defined by the same statements, in this file. Together they are the
definition of correctness for everything below: a compiled program is right
if the machine, running it, ends with the buffer contents that the source
gives.

A statement may carry a *pin*: the cycle on which its word must be issued
(`Tau.Isa.Event`). A pin does not change what the kernel computes. Running
a kernel also gives its *timeline* (`Kernel.timeline`): for every pinned
statement, the word and the cycle. A compiled program keeps the pins if the
machine issues those words on those cycles.

Like the machine, kernels are given meaning over an arbitrary `Sem`.

Terms to look up: *intermediate representation*, *SSA form*, *loop unrolling*.

Docs: Programs 1 to 3 and 5 (`docs/`).
-/

namespace Tau

/-- A named value inside a kernel. -/
abbrev Var := Nat

/-- A position in a buffer: `base + stride * i`, where `i` is the index of the
enclosing loop, or 0 outside a loop. -/
structure Idx where
  /-- The position on iteration 0. -/
  base : Nat
  /-- How far the position moves on each iteration. -/
  stride : Nat
  deriving DecidableEq, Repr

/-- The position an index refers to on iteration `i`. -/
def Idx.eval (ix : Idx) (i : Nat) : Nat := ix.base + ix.stride * i

/-- One statement of a kernel. A statement that takes or gives a value says
the type of the value. -/
inductive Stmt where
  /-- `dst = buf[ix]`, a value of type `ty`. -/
  | load (dst : Var) (ty : DType) (buf : Nat) (ix : Idx)
  /-- `buf[ix] = src`, a value of type `ty`. -/
  | store (src : Var) (ty : DType) (buf : Nat) (ix : Idx)
  /-- `dst = op a`, with `a` of type `ty`. -/
  | un (dst : Var) (ty : DType) (op : UnOp) (a : Var)
  /-- `dst = op a b`, all of type `ty`. -/
  | bin (dst : Var) (ty : DType) (op : BinOp) (a b : Var)
  /-- `dst = M * x`, where the matrix `M` is the `n` words `buf[ix]`,
  `buf[ix + 1]`, ...: word `i` holds the weights of element `i` of the
  product. `x` is a value of 8 bits and the product one of 32. -/
  | matvec (dst : Var) (x : Var) (buf : Nat) (ix : Idx) (n : Nat)
  /-- `dst` is the constant of type `ty` with elements `xs`. -/
  | const (dst : Var) (ty : DType) (xs : List Int)
  /-- `dst = sel m a b`: element by element, `a` where `m` is not zero, else
  `b`. All are of type `ty`. -/
  | sel (dst : Var) (ty : DType) (m a b : Var)
  /-- The statement `s`, with its value issued on cycle `t`. Inside a loop the
  cycle moves with the iteration, as a position does. -/
  | pin (t : Idx) (s : Stmt)
  deriving DecidableEq, Repr

/-- The value a statement issues: the variable that holds it, and for a store
the buffer and the word of it that the value's first word goes to, on loop
iteration `i`. -/
def Stmt.target (i : Nat) : Stmt → Var × Option (Nat × Nat)
  | .load dst _ _ _ => (dst, none)
  | .store src ty buf ix => (src, some (buf, ty.bytes * ix.eval i))
  | .un dst _ _ _ => (dst, none)
  | .bin dst _ _ _ _ => (dst, none)
  | .matvec dst _ _ _ _ => (dst, none)
  | .const dst _ _ => (dst, none)
  | .sel dst _ _ _ _ => (dst, none)
  | .pin _ s => s.target i

/-- A statement, or a loop that runs its body `n` times. Loops do not nest. -/
inductive Item where
  /-- One statement, run once. -/
  | stmt (s : Stmt)
  /-- `body` run `n` times, with the loop index going from `0` to `n - 1`. -/
  | loop (n : Nat) (body : List Stmt)
  deriving DecidableEq, Repr

/-- A kernel: a list of statements and loops. -/
abbrev Kernel := List Item

variable {V : Type}

/-- The values of a kernel's variables, the contents of its buffers, and the
events of its pinned statements so far. -/
structure Env (V : Type) where
  /-- Variable bindings, most recent first. A value is a list of words. -/
  vars : List (Var × List V)
  /-- The words of each buffer. -/
  bufs : List (List V)
  /-- The events so far, most recent first. -/
  events : List (Event V)

/-- Give variable `v` the value `x`. -/
def Env.bind (env : Env V) (v : Var) (x : List V) : Env V :=
  { env with vars := (v, x) :: env.vars }

/-- The value of variable `v`, if it has one of type `ty`. -/
def Env.get (env : Env V) (ty : DType) (v : Var) : Option (List V) :=
  match env.vars.lookup v with
  | some x => if x.length = ty.bytes then some x else none
  | none => none

/-- The one word of variable `v`, if its value is one word. -/
def Env.word (env : Env V) (v : Var) : Option V :=
  match env.vars.lookup v with
  | some [w] => some w
  | _ => none

/-- The events of a value issued on cycle `t`: one for each of its words. The
words of a store go to the words of the buffer from `store` on. -/
def eventsOf (t : Nat) (store : Option (Nat × Nat)) (x : List V) : List (Event V) :=
  (List.range x.length).zipWith (fun k w => ⟨t, store.map fun bk => (bk.1, bk.2 + k), w⟩) x

/-- Record that the value of variable `v` is issued on cycle `t`. -/
def Env.issue (env : Env V) (t : Nat) (target : Var × Option (Nat × Nat)) : Env V :=
  match env.vars.lookup target.1 with
  | some x => { env with events := eventsOf t target.2 x ++ env.events }
  | none => env

/-- Run one statement on loop iteration `i`. The result is `none` if the
statement uses a variable that has no value of the type it needs, or a
position outside a buffer. -/
def Stmt.exec (S : Sem V) (i : Nat) (env : Env V) : Stmt → Option (Env V)
  | .load dst ty buf ix =>
    match wordsAt (env.bufs[buf]?.getD []) (ty.bytes * ix.eval i) ty.bytes with
    | some x => some (env.bind dst x)
    | none => none
  | .store src ty buf ix =>
    match env.get ty src, env.bufs[buf]? with
    | some x, some b =>
      if ty.bytes * ix.eval i + ty.bytes ≤ b.length then
        some { env with bufs := env.bufs.set buf (putAt b (ty.bytes * ix.eval i) x) }
      else none
    | _, _ => none
  | .un dst ty op a =>
    match env.get ty a with
    | some x => some (env.bind dst (S.un ty op x))
    | none => none
  | .bin dst ty op a b =>
    match env.get ty a, env.get ty b with
    | some x, some y => some (env.bind dst (S.bin ty op x y))
    | _, _ => none
  | .matvec dst x buf ix n =>
    match env.word x, wordsAt (env.bufs[buf]?.getD []) (ix.eval i) n with
    | some w, some rows => some (env.bind dst (S.matvec rows w))
    | _, _ => none
  | .const dst ty xs => some (env.bind dst (S.const ty xs))
  | .sel dst ty m a b =>
    match env.get ty m, env.get ty a, env.get ty b with
    | some vm, some va, some vb => some (env.bind dst (S.sel ty vm va vb))
    | _, _, _ => none
  | .pin t s =>
    match s.exec S i env with
    | some env' => some (env'.issue (t.eval i) (s.target i))
    | none => none

/-- Run a list of statements in order, on loop iteration `i`. -/
def execStmts (S : Sem V) (i : Nat) : Env V → List Stmt → Option (Env V)
  | env, [] => some env
  | env, s :: rest =>
    match s.exec S i env with
    | some env' => execStmts S i env' rest
    | none => none

/-- Run iterations `0` to `n - 1` of a loop body. -/
def execLoop (S : Sem V) (body : List Stmt) : Nat → Env V → Option (Env V)
  | 0, env => some env
  | n + 1, env =>
    match execLoop S body n env with
    | some env' => execStmts S n env' body
    | none => none

/-- Run one item. -/
def Item.exec (S : Sem V) (env : Env V) : Item → Option (Env V)
  | .stmt s => s.exec S 0 env
  | .loop n body => execLoop S body n env

/-- Run a kernel from an environment. -/
def Kernel.exec (S : Sem V) : Env V → Kernel → Option (Env V)
  | env, [] => some env
  | env, it :: rest =>
    match it.exec S env with
    | some env' => Kernel.exec S env' rest
    | none => none

/-- Run a kernel on the given buffer contents and return the final contents. -/
def Kernel.run (S : Sem V) (k : Kernel) (bufs : List (List V)) : Option (List (List V)) :=
  match Kernel.exec S ⟨[], bufs, []⟩ k with
  | some env => some env.bufs
  | none => none

/-- The events of a kernel run on the given buffer contents: for every pinned
statement, its word and its cycle. Empty if the run fails. -/
def Kernel.timeline (S : Sem V) (k : Kernel) (bufs : List (List V)) : List (Event V) :=
  match Kernel.exec S ⟨[], bufs, []⟩ k with
  | some env => env.events
  | none => []

end Tau
