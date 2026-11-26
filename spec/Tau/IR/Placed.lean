import Tau.Machine.Arch
import Tau.IR.Kernel
import Tau.IR.MemMap
import Tau.Check.Expr

/-!
# Placed programs

The middle form a program takes in the compiler, and the output of
`tau-place`. The kernel has become machine instructions. Every buffer has a
home in some memory, every operation has a slice, and the compiler has decided
which values travel directly and which wait in memory. What is still missing
is time: no instruction has a cycle, unless it is pinned, and no word has a
stream.

A placed program is a list of instructions to be carried out one after
another, as if each took effect at once. `Placed.execute` gives that meaning.
It reuses the slice state of the slice-level machine and ignores streams and
pipes. A word in transit is named by a variable, as in a kernel.

An instruction may carry a pin, the cycle it must be issued on
(`spec/Tau/Isa/Event.lean`). The pins of the kernel are now on the instructions
that issue the pinned words. Running a placed program gives the events of its
pinned instructions (`Placed.timeline`), although it has no cycles of its
own yet.

The four forms, in order: `spec/Tau/IR/Source.lean`, `spec/Tau/IR/Kernel.lean`, this
file, `spec/Tau/IR/Compiled.lean`. The theorems about this one are in
`spec/Tau/Proofs/IR/Placed.lean`.

Docs: Compiler 2 (`docs/`).
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
  /-- The instruction `i`, to be issued on cycle `t`. -/
  | pin (t : Nat) (i : PInstr)
  deriving DecidableEq, Repr

/-- The word an instruction issues, if it issues one: the variable that holds
it, and for a write the address. -/
def PInstr.target : PInstr → Option (Var × Option Nat)
  | .read dst _ => some (dst, none)
  | .write src addr => some (src, some addr)
  | .un dst _ _ => some (dst, none)
  | .bin dst _ _ _ => some (dst, none)
  | .emit dst => some (dst, none)
  | .const dst _ => some (dst, none)
  | .sel dst _ _ _ => some (dst, none)
  | .pin _ i => i.target
  | _ => none

/-- The cycles an instruction is pinned to. -/
def PInstr.pins : PInstr → List Nat
  | .pin t i => t :: i.pins
  | _ => []

/-- What a pinned instruction at the slice at `p` issues, once it has run and
the words in transit are `vars`: its word, on each cycle it is pinned to. -/
def PInstr.issues (p : Nat) (i : PInstr) (vars : List (Var × V)) : List (Issue V) :=
  match i.target with
  | some (v, addr) =>
    match vars.lookup v with
    | some w => i.pins.map fun t => ⟨t, p, addr, w⟩
    | none => []
  | none => []

/-- The output of `tau-place`. -/
structure Placed where
  /-- The machine the program is for. -/
  cfg : Config
  /-- The number of words in the memory at each position. -/
  memSizes : List Nat
  /-- Where each buffer lives. -/
  map : MemMap
  /-- The instructions in order, each with the position of its slice. -/
  instrs : List (Nat × PInstr)
  deriving Repr

/-- The words in transit, the state of every slice, and what the pinned
instructions have issued so far. -/
structure PState (V : Type) where
  /-- Words in transit, most recent first. -/
  vars : List (Var × V)
  /-- The state of the slice at each position. -/
  slices : List (Slice V)
  /-- What the pinned instructions have issued, most recent first. -/
  issues : List (Issue V)

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
  | .pin _ i => i.exec S kind vars sl

/-- Carry out one instruction at the slice at position `p`. -/
def PState.step (S : Sem V) (cfg : Config) (st : PState V) (p : Nat) (i : PInstr) :
    Option (PState V) :=
  match cfg.kindAt p, st.slices[p]? with
  | some kind, some sl =>
    match i.exec S kind st.vars sl with
    | some (vars, sl') => some ⟨vars, st.slices.set p sl', i.issues p vars ++ st.issues⟩
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
  match PState.run S pl.cfg ⟨[], (State.init S pl.cfg image).slices, []⟩ pl.instrs with
  | some st => some (st.slices.map (·.words))
  | none => none

/-- The events of a placed program run from a memory image: the word of every
pinned instruction, with its cycle. Empty if the run fails. -/
def Placed.timelineFrom (S : Sem V) (pl : Placed) (image : List (List V)) : List (Event V) :=
  match PState.run S pl.cfg ⟨[], (State.init S pl.cfg image).slices, []⟩ pl.instrs with
  | some st => st.issues.filterMap (Issue.event pl.map)
  | none => []

/-- The starting memory contents for the given buffer contents. -/
def Placed.image (pl : Placed) (bufs : List (List V)) (fill : V) : List (List V) :=
  Tau.image pl.map pl.memSizes (bufWord bufs fill) fill

/-- The events of a placed program run on the given buffer contents. -/
def Placed.timeline (S : Sem V) (pl : Placed) (bufs : List (List V)) (fill : V) :
    List (Event V) :=
  pl.timelineFrom S (pl.image bufs fill)

end Tau
