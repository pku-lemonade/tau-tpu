import Tau.Isa.Op

/-!
# Kernels

A *kernel* is the program a user writes: load words from buffers, compute, and
store words back. It says nothing about slices, streams or cycles. It is the
Lean model of the compiler's `tau` dialect (see `compiler/`).

What a kernel computes (`Kernel.run`) is the definition of correctness for
everything below it: a compiled program is right if the machine, running it,
ends with the buffer contents that `Kernel.run` gives.

Like the machine, kernels are given meaning over an arbitrary `Sem`.

Terms to look up: *intermediate representation*, *SSA form*, *loop unrolling*.
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

/-- One statement of a kernel. -/
inductive Stmt where
  /-- `dst = buf[ix]` -/
  | load (dst : Var) (buf : Nat) (ix : Idx)
  /-- `buf[ix] = src` -/
  | store (src : Var) (buf : Nat) (ix : Idx)
  /-- `dst = op a` -/
  | un (dst : Var) (op : UnOp) (a : Var)
  /-- `dst = op a b` -/
  | bin (dst : Var) (op : BinOp) (a b : Var)
  /-- `dst = M * x`, where the columns of the matrix `M` are the `n` words
  `buf[ix]`, `buf[ix + 1]`, ... -/
  | matvec (dst : Var) (x : Var) (buf : Nat) (ix : Idx) (n : Nat)
  /-- `dst = M * x + bias`, with `M` as in `matvec`. -/
  | affine (dst : Var) (x bias : Var) (buf : Nat) (ix : Idx) (n : Nat)
  /-- `dst` is the constant word with lanes `xs`. -/
  | const (dst : Var) (xs : List Int)
  /-- `dst = sel m a b`: lane by lane, `a` where `m` is not zero, else `b`. -/
  | sel (dst : Var) (m a b : Var)
  deriving DecidableEq, Repr

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

/-- The values of a kernel's variables and the contents of its buffers. -/
structure Env (V : Type) where
  /-- Variable bindings, most recent first. -/
  vars : List (Var × V)
  /-- The contents of each buffer. -/
  bufs : List (List V)

/-- Give variable `v` the value `x`. -/
def Env.bind (env : Env V) (v : Var) (x : V) : Env V :=
  { env with vars := (v, x) :: env.vars }

/-- `init` plus the product of a matrix with `x`, built up one column at a
time. `cols j` is column `j`; the result is `none` if a column is missing. -/
def matvecFrom (S : Sem V) (x : V) (cols : Nat → Option V) (init : V) : Nat → Option V
  | 0 => some init
  | j + 1 =>
    match matvecFrom S x cols init j, cols j with
    | some acc, some w => some (S.mac j acc x w)
    | _, _ => none

/-- Run one statement on loop iteration `i`. The result is `none` if the
statement uses a variable that has no value or a position outside a buffer. -/
def Stmt.exec (S : Sem V) (i : Nat) (env : Env V) : Stmt → Option (Env V)
  | .load dst buf ix =>
    match (env.bufs[buf]?.getD [])[ix.eval i]? with
    | some v => some (env.bind dst v)
    | none => none
  | .store src buf ix =>
    match env.vars.lookup src, env.bufs[buf]? with
    | some v, some b =>
      if ix.eval i < b.length then
        some { env with bufs := env.bufs.set buf (b.set (ix.eval i) v) }
      else none
    | _, _ => none
  | .un dst op a =>
    match env.vars.lookup a with
    | some v => some (env.bind dst (S.un op v))
    | none => none
  | .bin dst op a b =>
    match env.vars.lookup a, env.vars.lookup b with
    | some va, some vb => some (env.bind dst (S.bin op va vb))
    | _, _ => none
  | .matvec dst x buf ix n =>
    match env.vars.lookup x with
    | some xv =>
      match matvecFrom S xv (fun j => (env.bufs[buf]?.getD [])[ix.eval i + j]?) S.zero n with
      | some r => some (env.bind dst r)
      | none => none
    | none => none
  | .affine dst x bias buf ix n =>
    match env.vars.lookup x, env.vars.lookup bias with
    | some xv, some bv =>
      match matvecFrom S xv (fun j => (env.bufs[buf]?.getD [])[ix.eval i + j]?) bv n with
      | some r => some (env.bind dst r)
      | none => none
    | _, _ => none
  | .const dst xs => some (env.bind dst (S.const xs))
  | .sel dst m a b =>
    match env.vars.lookup m, env.vars.lookup a, env.vars.lookup b with
    | some vm, some va, some vb => some (env.bind dst (S.sel vm va vb))
    | _, _, _ => none

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
  match Kernel.exec S ⟨[], bufs⟩ k with
  | some env => some env.bufs
  | none => none

end Tau
