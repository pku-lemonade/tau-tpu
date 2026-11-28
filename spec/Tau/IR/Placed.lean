import Tau.Machine.SliceLevel
import Tau.IR.Kernel
import Tau.IR.MemMap

/-!
# Placed programs

The third IR a program takes in the compiler, and the output of
`tau-place`. The kernel has become machine instructions. Every buffer has a
home in some memory and every operation has a slice. That is all that has
been decided: where. What is still missing is time. No instruction has a
cycle, unless it is pinned, and no word has a stream. No word waits in
memory either: whether one has to is known only when both its ends have a
cycle, so `tau-schedule` decides it, and a placed program has no scratch
space.

A placed program is a list of instructions to be carried out one after
another, as if each took effect at once. `Placed.execute` gives that meaning.
It reuses the slice state of the slice-level machine and ignores streams and
pipes. A word in transit is named by a variable, as in a kernel, and as in a
kernel any number of later instructions may use it.

An instruction may carry a pin, the cycle it must be issued on
(`Tau.Isa.Event`). The pins of the kernel are now on the instructions
that issue the pinned words. Running a placed program gives the events of its
pinned instructions (`Placed.timeline`), although it has no cycles of its
own yet.

The four IRs, in order: `Tau.IR.Source`, `Tau.IR.Kernel`, this
file, `Tau.IR.Compiled`. The theorems about this one are in
`Tau.Proofs.IR.Placed`.

Docs: Compiler 2 (`docs/`).
-/

namespace Tau

variable {V : Type}

/-- An instruction before it has a cycle or streams. A word in transit is
named by a variable, as in a kernel, and a value of several words by a list
of them, the low word first. -/
inductive PInstr where
  /-- Memory: `dst` is the word at `addr`. -/
  | read (dst : Var) (addr : Nat)
  /-- Memory: store `src` at `addr`. -/
  | write (src : Var) (addr : Nat)
  /-- Vector or rearrangement: `dst = op src`, with `src` of type `ty`. -/
  | un (dst : List Var) (ty : DType) (op : UnOp) (src : List Var)
  /-- Vector: `dst = op a b`, all of type `ty`. -/
  | bin (dst : List Var) (ty : DType) (op : BinOp) (a b : List Var)
  /-- Vector: `dst` is the constant of type `ty` with elements `xs`. -/
  | const (dst : List Var) (ty : DType) (xs : List Int)
  /-- Vector: `dst = sel m a b`, all of type `ty`. -/
  | sel (dst : List Var) (ty : DType) (m a b : List Var)
  /-- Matrix: keep the words `srcs` as installed words `j`, `j + 1`, ... -/
  | install (j : Nat) (srcs : List Var)
  /-- Matrix: `dst` is the product of the first `n` installed words with
  `src`, a value of 32 bits. -/
  | product (dst : List Var) (n : Nat) (src : Var)
  /-- The instruction `i`, to be issued on cycle `t`. -/
  | pin (t : Nat) (i : PInstr)
  deriving DecidableEq, Repr

/-- The words an instruction issues: the variable that holds each, and for a
write the address. -/
def PInstr.targets : PInstr → List (Var × Option Nat)
  | .read dst _ => [(dst, none)]
  | .write src addr => [(src, some addr)]
  | .un dst _ _ _ => dst.map (·, none)
  | .bin dst _ _ _ _ => dst.map (·, none)
  | .product dst _ _ => dst.map (·, none)
  | .const dst _ _ => dst.map (·, none)
  | .sel dst _ _ _ _ => dst.map (·, none)
  | .pin _ i => i.targets
  | _ => []

/-- The cycles an instruction is pinned to. -/
def PInstr.pins : PInstr → List Nat
  | .pin t i => t :: i.pins
  | _ => []

/-- What a pinned instruction at the slice at `p` issues, once it has run and
the words in transit are `vars`: each of its words, on each cycle it is
pinned to. -/
def PInstr.issues (p : Nat) (i : PInstr) (vars : List (Var × V)) : List (Issue V) :=
  i.targets.flatMap fun (v, addr) =>
    match vars.lookup v with
    | some w => i.pins.map fun t => ⟨t, p, addr, w⟩
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

/-- The words in transit that `srcs` name. `none` if one of them has no word
yet. -/
def lookupAll (vars : List (Var × V)) : List Var → Option (List V)
  | [] => some []
  | src :: rest =>
    match vars.lookup src, lookupAll vars rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- The words in transit that `srcs` name, if they are a value of type `ty`. -/
def lookupValue (vars : List (Var × V)) (ty : DType) (srcs : List Var) : Option (List V) :=
  if srcs.length = ty.bytes then lookupAll vars srcs else none

/-- Name the words of the value `x` by the variables `dst`. -/
def bindAll (vars : List (Var × V)) (dst : List Var) (x : List V) : List (Var × V) :=
  dst.zip x ++ vars

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
  | .un dst ty op src =>
    if op.kind ≠ kind then none
    else
      match lookupValue vars ty src with
      | some v => some (bindAll vars dst (S.un ty op v), sl)
      | none => none
  | .bin dst ty op a b =>
    if kind ≠ .vxm then none
    else
      match lookupValue vars ty a, lookupValue vars ty b with
      | some va, some vb => some (bindAll vars dst (S.bin ty op va vb), sl)
      | _, _ => none
  | .const dst ty xs =>
    if kind ≠ .vxm then none
    else some (bindAll vars dst (S.const ty xs), sl)
  | .sel dst ty m a b =>
    if kind ≠ .vxm then none
    else
      match lookupValue vars ty m, lookupValue vars ty a, lookupValue vars ty b with
      | some vm, some va, some vb => some (bindAll vars dst (S.sel ty vm va vb), sl)
      | _, _, _ => none
  | .install j srcs =>
    if kind ≠ .mxm then none
    else if sl.weights.length < j + srcs.length then none
    else
      match lookupAll vars srcs with
      | some vs => some (vars, { sl with weights := putAt sl.weights j vs })
      | none => none
  | .product dst n src =>
    if kind ≠ .mxm then none
    else if sl.weights.length < n then none
    else
      match vars.lookup src with
      | some x => some (bindAll vars dst (S.matvec (sl.weights.take n) x), sl)
      | none => none
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
