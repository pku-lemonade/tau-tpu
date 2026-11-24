import Tau.Check.Checker

/-!
# Checking each compiler pass on its own

`check` (`Tau/Check/Checker.lean`) decides whether the finished program is
right. When it says no, it does not say which pass went wrong. This file adds
a check for the output of each earlier pass, so that the first rejected stage
names the faulty pass.

Every check compares against the kernel as the user wrote it, in the same
way: run both sides on expressions and compare the results.

| Pass | Its output | Checked by |
|---|---|---|
| `tau-simplify` | a kernel | `checkKernels` |
| `tau-unroll` | a kernel | `checkKernels` |
| `tau-place` | instructions in order, no cycles (`Placed`) | `checkPlaced` |
| `tau-schedule` | a program in which every word has its own stream | `check` |
| `tau-route` | the finished program | `check` |

The schedule can be checked before routing because a routing in which no two
words share a stream cannot be wrong. The compiler writes the scheduled
program with such a routing, on a chip with as many streams as that takes.

## The placed level

After `tau-place` the kernel has become machine instructions. Every buffer
has a home in some memory, every operation has a slice, and the compiler has
decided which values travel directly and which wait in memory. What is still
missing is time. A placed program is a list of instructions to be carried out
one after another, as if each took effect at once.

`Placed.execute` gives that meaning. It reuses the slice state of the
slice-level machine, and ignores streams and pipes.

The soundness proofs are in `Tau/Proofs/Check/Stages.lean`.
-/

namespace Tau

variable {V : Type}

/-- An instruction before it has a cycle or streams. A word in transit is
named by a variable, as in a kernel. -/
inductive PInstr where
  /-- Memory: `dst` is the word at `addr`. -/
  | read (dst : Var) (addr : Nat)
  /-- Memory: store `src` at `addr`. -/
  | write (src : Var) (addr : Nat)
  /-- Vector or rearrangement: `dst = op src`. -/
  | un (dst : Var) (op : UnOp) (src : Var)
  /-- Vector: `dst = op a b`. -/
  | bin (dst : Var) (op : BinOp) (a b : Var)
  /-- Matrix: keep `src` as the vector operand. -/
  | load (src : Var)
  /-- Matrix: add lane `j` of the vector operand, times `src`, to the
  accumulator. -/
  | mac (j : Nat) (src : Var)
  /-- Matrix: `dst` is the accumulator, which is then cleared. -/
  | emit (dst : Var)
  /-- Vector: `dst` is the constant word with lanes `xs`. -/
  | const (dst : Var) (xs : List Int)
  /-- Vector: `dst = sel m a b`. -/
  | sel (dst : Var) (m a b : Var)
  /-- Matrix: replace the accumulator by `src`. -/
  | seed (src : Var)
  /-- Matrix: keep `src` as stored column `j`. -/
  | install (j : Nat) (src : Var)
  /-- Matrix: add lane `j` of the vector operand, times stored column `j`, to
  the accumulator. -/
  | macw (j : Nat)
  deriving DecidableEq, Repr

/-- The output of `tau-place`. -/
structure Placed where
  /-- The chip the program is for. -/
  cfg : Config
  /-- The number of words in the memory at each position. -/
  memSizes : List Nat
  /-- Where each buffer lives. -/
  map : MemMap
  /-- The instructions in order, each with the position of its slice. -/
  instrs : List (Nat × PInstr)
  deriving Repr

/-- The words in transit and the state of every slice. -/
structure PState (V : Type) where
  /-- Words in transit, most recent first. -/
  vars : List (Var × V)
  /-- The state of the slice at each position. -/
  slices : List (Slice V)

/-- Carry out one instruction at a slice of the given kind. `none` if the
slice is of the wrong kind, an address is out of range, or a word is used
before it exists. -/
def PInstr.exec (S : Sem V) (kind : Kind) (vars : List (Var × V)) (sl : Slice V) :
    PInstr → Option (List (Var × V) × Slice V)
  | .read dst addr =>
    if kind ≠ .mem then none
    else
      match sl.words[addr]? with
      | some v => some ((dst, v) :: vars, sl)
      | none => none
  | .write src addr =>
    if kind ≠ .mem then none
    else if sl.words.length ≤ addr then none
    else
      match vars.lookup src with
      | some v => some (vars, { sl with words := sl.words.set addr v })
      | none => none
  | .un dst op src =>
    if op.kind ≠ kind then none
    else
      match vars.lookup src with
      | some v => some ((dst, S.un op v) :: vars, sl)
      | none => none
  | .bin dst op a b =>
    if kind ≠ .vxm then none
    else
      match vars.lookup a, vars.lookup b with
      | some va, some vb => some ((dst, S.bin op va vb) :: vars, sl)
      | _, _ => none
  | .load src =>
    if kind ≠ .mxm then none
    else
      match vars.lookup src with
      | some v => some (vars, { sl with x := some v })
      | none => none
  | .mac j src =>
    if kind ≠ .mxm then none
    else
      match sl.x, vars.lookup src with
      | some x, some w => some (vars, { sl with acc := S.mac j sl.acc x w })
      | _, _ => none
  | .emit dst =>
    if kind ≠ .mxm then none
    else some ((dst, sl.acc) :: vars, { sl with acc := S.zero })
  | .const dst xs =>
    if kind ≠ .vxm then none
    else some ((dst, S.const xs) :: vars, sl)
  | .sel dst m a b =>
    if kind ≠ .vxm then none
    else
      match vars.lookup m, vars.lookup a, vars.lookup b with
      | some vm, some va, some vb => some ((dst, S.sel vm va vb) :: vars, sl)
      | _, _, _ => none
  | .seed src =>
    if kind ≠ .mxm then none
    else
      match vars.lookup src with
      | some v => some (vars, { sl with acc := v })
      | none => none
  | .install j src =>
    if kind ≠ .mxm then none
    else if sl.weights.length ≤ j then none
    else
      match vars.lookup src with
      | some v => some (vars, { sl with weights := sl.weights.set j v })
      | none => none
  | .macw j =>
    if kind ≠ .mxm then none
    else
      match sl.x, sl.weights[j]? with
      | some x, some w => some (vars, { sl with acc := S.mac j sl.acc x w })
      | _, _ => none

/-- Carry out one instruction at the slice at position `p`. -/
def PState.step (S : Sem V) (cfg : Config) (st : PState V) (p : Nat) (i : PInstr) :
    Option (PState V) :=
  match cfg.kindAt p, st.slices[p]? with
  | some kind, some sl =>
    match i.exec S kind st.vars sl with
    | some (vars, sl') => some ⟨vars, st.slices.set p sl'⟩
    | none => none
  | _, _ => none

/-- Carry out a list of instructions in order. -/
def PState.run (S : Sem V) (cfg : Config) : PState V → List (Nat × PInstr) → Option (PState V)
  | st, [] => some st
  | st, (p, i) :: rest =>
    match st.step S cfg p i with
    | some st' => PState.run S cfg st' rest
    | none => none

/-- Run a placed program from a memory image and return the final memory
contents. -/
def Placed.execute (S : Sem V) (pl : Placed) (image : List (List V)) :
    Option (List (List V)) :=
  match PState.run S pl.cfg ⟨[], (State.init S pl.cfg image).slices⟩ pl.instrs with
  | some st => some (st.slices.map (·.words))
  | none => none

/-- The starting memory contents for the given buffer contents. -/
def Placed.image (pl : Placed) (bufs : List (List V)) (fill : V) : List (List V) :=
  Tau.image pl.map pl.memSizes (bufWord bufs fill) fill

/-- The expressions a placed program ends with, for every word of every
buffer. -/
def placedExprs (pl : Placed) : Option (List (List Expr)) :=
  match pl.execute exprSem (image pl.map pl.memSizes Expr.init .fill) with
  | some mem => some (extract pl.map mem .fill)
  | none => none

/-- Accept or reject the output of `tau-place` for the kernel `k`. -/
def checkPlaced (k : Kernel) (sizes : List Nat) (pl : Placed) : Bool :=
  pl.map.map (·.size) == sizes &&
  match placedExprs pl, kernelExprs k sizes with
  | some m, some e => m.map (·.map Expr.simp) == e.map (·.map Expr.simp)
  | _, _ => false

/-- Accept or reject a kernel `k'` produced from the kernel `k` by a pass
that should not change what it computes. -/
def checkKernels (k k' : Kernel) (sizes : List Nat) : Bool :=
  match kernelExprs k sizes, kernelExprs k' sizes with
  | some a, some b => a.map (·.map Expr.simp) == b.map (·.map Expr.simp)
  | _, _ => false

end Tau
