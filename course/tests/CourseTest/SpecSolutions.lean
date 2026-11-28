import Tau
import Specify.Support.Tables
import Specify.Method.Candidates
import Specify.Method.Review
import Specify.Method.Repair

/-!
# Test: the specification exercises can be solved

The exercises in `course/Specify/` that take the compiler as their source are
tested by tables in `Specify.Support.Tables`. This file runs those tables
on a solution, so that a table which no definition could satisfy fails the
build.

For the kernel and for `tau-unroll` the solution is the definition in `spec/Tau/`.
For `tau-simplify` and for the timing rule there is none in `spec/Tau/`, so one is
written here. These two are solutions to exercises and nothing more: no
theorem is proved about them.
-/

namespace CourseTest.SpecSolutions

open Tau Specify

#guard passes (Tables.stmt Stmt.exec)
#guard passes (Tables.stmtDecisions Stmt.exec)
#guard passes (Tables.unroll Kernel.unroll)
#guard passes (Tables.unrollDecisions Kernel.unroll)

/-! ## Pins and the image -/

/-- A solution to `Specify.IR.Pins`. -/
def eventOf {V : Type} (i : Nat) (t : Idx) (s : Stmt) (env : Env V) : List (Event V) :=
  let target := s.target i
  match env.vars.lookup target.1 with
  | some x =>
    (List.range x.length).zipWith
      (fun k w => ⟨t.eval i, target.2.map fun bk => (bk.1, bk.2 + k), w⟩) x
  | none => []

#guard passes (Tables.pin eventOf)
#guard passes (Tables.pinDecisions eventOf)

/-- A solution to `Specify.Isa.Encode`. -/
def encodeEntry (e : TimedEntry) : List Nat :=
  match e.instr with
  | .read addr dst => [e.time, e.repeats, e.gap, e.stride, 0, addr, dst.encode]
  | .write src addr => [e.time, e.repeats, e.gap, e.stride, 1, src.encode, addr]
  | i => e.time :: e.repeats :: e.gap :: e.stride :: i.encode

#guard passes (Tables.numbers Stream.encode encodeInt)
#guard passes (Tables.numbersBack Stream.decode decodeInt)
#guard passes (Tables.entries encodeEntry)

-- The two statements of `Specify.Isa.Encode`, for streams.
example (tr : Stream) : Stream.decode tr.encode = tr := Stream.decode_encode tr
example (n : Nat) : (Stream.decode n).encode = n := by
  simp only [Stream.decode, Stream.encode]
  split <;> simp_all <;> omega

/-! ## A copy of `tau-simplify` -/

/-- What the pass knows while it walks a kernel: which values are now other
names for an earlier value, and which values are the result of a relu. -/
structure Known where
  /-- `(v, w)`: every use of `v` is to be replaced by `w`. -/
  alias : List (Var × Var)
  /-- The values defined by a relu. -/
  relus : List Var

/-- The value to use in place of `v`. -/
def Known.use (k : Known) (v : Var) : Var := (k.alias.lookup v).getD v

/-- A statement with every value it uses replaced by the value to use in its
place. -/
def Known.rename (k : Known) : Stmt → Stmt
  | .load dst ty buf ix => .load dst ty buf ix
  | .store src ty buf ix => .store (k.use src) ty buf ix
  | .un dst ty op a => .un dst ty op (k.use a)
  | .bin dst ty op a b => .bin dst ty op (k.use a) (k.use b)
  | .matvec dst x buf ix n => .matvec dst (k.use x) buf ix n
  | .const dst ty xs => .const dst ty xs
  | .sel dst ty m a b => .sel dst ty (k.use m) (k.use a) (k.use b)
  | .pin t s => .pin t (k.rename s)

/-- Simplify one statement. Returns what is known afterwards and the
statement to keep, if any. A pinned statement is always kept. -/
def simplifyStmt (k : Known) : Stmt → Known × Option Stmt
  | .load dst ty buf ix => (k, some (.load dst ty buf ix))
  | .store src ty buf ix => (k, some (.store (k.use src) ty buf ix))
  | .un dst ty .relu a =>
    let a := k.use a
    if k.relus.contains a then ({ k with alias := (dst, a) :: k.alias }, none)
    else ({ k with relus := dst :: k.relus }, some (.un dst ty .relu a))
  | .un dst ty op a => (k, some (.un dst ty op (k.use a)))
  | .bin dst ty op a b =>
    let a := k.use a
    let b := k.use b
    if (op == .max || op == .min) && a == b then ({ k with alias := (dst, a) :: k.alias }, none)
    else (k, some (.bin dst ty op a b))
  | .matvec dst x buf ix n => (k, some (.matvec dst (k.use x) buf ix n))
  | .const dst ty xs => (k, some (.const dst ty xs))
  | .sel dst ty m a b => (k, some (.sel dst ty (k.use m) (k.use a) (k.use b)))
  | .pin t s =>
    let k' := match s with
      | .un dst _ .relu _ => { k with relus := dst :: k.relus }
      | _ => k
    (k', some (.pin t (k.rename s)))

/-- Simplify a list of statements. -/
def simplifyStmts (k : Known) : List Stmt → Known × List Stmt
  | [] => (k, [])
  | s :: rest =>
    let (k, s') := simplifyStmt k s
    let (k, rest') := simplifyStmts k rest
    (k, match s' with | some s' => s' :: rest' | none => rest')

/-- Simplify a kernel, starting from what is known so far. -/
def simplifyFrom (k : Known) : Kernel → Kernel
  | [] => []
  | .stmt s :: rest =>
    let (k, s') := simplifyStmt k s
    match s' with
    | some s' => .stmt s' :: simplifyFrom k rest
    | none => simplifyFrom k rest
  | .loop n body :: rest =>
    let (k, body') := simplifyStmts k body
    .loop n body' :: simplifyFrom k rest

/-- A copy of `tau-simplify`. -/
def simplify (k : Kernel) : Kernel := simplifyFrom ⟨[], []⟩ k

#guard passes (Tables.simplify simplify)
#guard passes (Tables.simplifyDecisions simplify)

/-! ## The timing rule on programs -/

/-- Whether the word that `(p, t, i)` computes is at the slice at `q` on cycle
`u`, on the stream `tr`: Machine 3.4. -/
def arrives (cfg : Config) (tr : Stream) (q u : Nat) : Nat × Nat × Instr → Bool
  | (p, t, i) =>
    (Tables.results i).contains tr &&
    match cfg.kindAt p with
    | none => false
    | some kind =>
      match tr.dir with
      | .east => p ≤ q && u == t + cfg.delayOf kind i + 1 + (q - p)
      | .west => q ≤ p && u == t + cfg.delayOf kind i + 1 + (p - q)

/-- Every operand of every instruction arrives on the cycle it is read. -/
def onTime (c : Compiled) : Bool :=
  let all := Tables.issues c
  all.all fun (q, u, i) =>
    (Tables.operands i).all fun tr => all.any (arrives c.cfg tr q u)

#guard passes (Tables.onTime onTime)

/-- Fail the build unless every row agrees. -/
def expect (rows : IO (List Row)) : IO Unit := do
  let rows ← rows
  unless passes rows do throw (IO.userError (summary "table" rows))

#eval expect (Tables.unrollOnExample Kernel.unroll "examples/ops/elementwise/stages")
#eval expect (Tables.simplifyOnExample simplify "examples/nn/linear/stages")
#eval expect (Tables.onTimeOnExample onTime "examples/nn/linear/stages")
#eval expect (Tables.onTimeOnExample onTime "examples/nn/residual/stages")
#eval expect (Tables.onTimeOnExample onTime "examples/ops/elementwise/stages")


/-! ## Candidates

`Specify.Method.Candidates` gives three definitions of each of three
components. All pass the doc's table. The lines below say which one is
right and show an input that gives the other two away. -/

section Candidates

open Specify.Candidates

/-- Whether two blocks give the same outputs on the inputs `inp`. -/
def agree {σ τ ι ο : Type} [BEq ο] (a : Block σ ι ο) (b : Block τ ι ο) (inp : List ι)
    (pad : ι) : Bool :=
  Tables.run a inp pad == Tables.run b inp pad

-- All nine pass the table.
#guard passes (Tables.shiftRegister ShiftRegister.candidateA)
#guard passes (Tables.shiftRegister ShiftRegister.candidateB)
#guard passes (Tables.shiftRegister ShiftRegister.candidateC)
#guard passes (Tables.accumulator Accumulator.candidateA)
#guard passes (Tables.accumulator Accumulator.candidateB)
#guard passes (Tables.accumulator Accumulator.candidateC)
#guard passes (Tables.mac Mac.candidateA)
#guard passes (Tables.mac Mac.candidateB)
#guard passes (Tables.mac Mac.candidateC)

-- Shift register: B is right.
-- A treats depth 0 as depth 1; the doc does not say what depth 0 is.
-- C starts its slots at 0 whatever the reset value; the doc says they
-- hold the reset value.
#guard passes (Tables.shiftRegisterDecisions ShiftRegister.candidateB)
#guard !agree (ShiftRegister.candidateA 0 9) (shiftRegister 0 9) [5, 6, 7] 0
#guard !agree (ShiftRegister.candidateC 2 9) (shiftRegister 2 9) [5, 6, 7] 0

-- Accumulator: C is right.
-- A clears to 0, not to the starting value; the doc says the starting
-- value.
-- B shows a loaded value in the cycle of the load; the doc says the
-- output is the total before the command takes effect.
#guard passes (Tables.accumulatorDecisions Accumulator.candidateC)
#guard !agree (Accumulator.candidateA 100) (accumulator 100) [.add 1, .clear, .hold] .hold
#guard !agree (Accumulator.candidateB 0) (accumulator 0) [.add 4, .load 7, .hold] .hold

-- MAC: A is right.
-- B adds the size of the product and loses its sign; the doc says it
-- adds the product.
-- C loads the first value of a pair, not the product; the doc says the
-- commands carry a pair and is silent on what load does with it.
#guard passes (Tables.macDecisions Mac.candidateA)
#guard !agree (Mac.candidateB 0) (mac 0) [.add (2, -3), .hold] .hold
#guard !agree (Mac.candidateC 0) (mac 0) [.load (2, 5), .hold] .hold

end Candidates


/-! ## Review

The planted problems of `Specify.Method.Review` are what the answers say
they are. -/

/-- info: 'Specify.Review.Three.returned' depends on axioms: [propext, sorryAx] -/
#guard_msgs in
#print axioms Specify.Review.Three.returned

/-- info: 'Specify.Review.Five.returned' does not depend on any axioms -/
#guard_msgs in
#print axioms Specify.Review.Five.returned

-- Section 4 is about another accumulator: the two differ on a clear.
#guard Tables.run (Specify.Review.Four.accumulator 5) [.add 1, .clear] .hold !=
  Tables.run (accumulator (5 : Int)) [.add 1, .clear] .hold

/-! ## Repairs

Each statement of `Specify.Method.Repair` is false as written, and true
with one more hypothesis. -/

section Repairs

open Specify.Repair

example : ¬ ShiftDelays := by
  intro h
  have := h 1 7 (fun _ => 0) 0
  revert this
  decide

theorem shiftDelays_repaired (n : Nat) (reset : Int) (inp : Signal Int) (t : Nat)
    (h : n ≤ t) : (shiftRegister n reset).outAt inp t = inp (t - n) := by
  simp only [shiftRegister_outAt, h, ↓reduceIte]

example : ¬ AccumulatorSums := by
  intro h
  have := h (fun k => if k = 0 then .add 3 else .clear) 2
  revert this
  decide

theorem accumulatorSums_repaired (x : Signal Int) (t : Nat) :
    (accumulator 0).outAt (fun k => .add (x k)) t = sumTo 0 x t :=
  accumulator_outAt_add 0 x t

example : ¬ ReadsBack := by
  intro h
  have := h 1 #v[0] (fun k => if k = 0 then .write 5 9 else .read 5) 0 5 9 rfl rfl
  revert this
  decide

theorem readsBack_repaired (n : Nat) (init : Vector Int n) (inp : Signal (MemIn Int))
    (t a : Nat) (x : Int) (ha : a < n) (hw : inp t = .write a x)
    (hr : inp (t + 1) = .read a) :
    (memory n init).outAt inp (t + 1) = some x := by
  rw [memory_outAt_read n init inp (t + 1) a ha hr]
  simp [lastWrite, hw]

end Repairs


/-! ## Reading the C++, and the three rules

The answers to `Specify.IR.ReadCpp` and `Specify.Method.Provable`. -/

section Reading

open Specify.Tables

#guard passes (readUnroll ⟨.mlir, ""⟩ ⟨.kernel, "Idx.inst"⟩ ⟨.kernel, "Stmt.inst"⟩ ⟨.mlir, ""⟩
  ⟨.limit, "Item"⟩ ⟨.kernel, "unrollLoop"⟩ ⟨.mlir, ""⟩ ⟨.kernel, "Item.unroll"⟩ ⟨.mlir, ""⟩)
#guard passes (readDifferences (some true) (some false) (some true) 354)

-- The names the answers give exist.
#check @Idx.inst
#check @Stmt.inst
#check @unrollLoop
#check @Item.unroll

-- The lines the exercise quotes are where it says they are.
#eval expect quotedLinesHold

-- 1. A zero word. 2. Depth 3. 3. A word that is 0, read at its own address.
#guard passes (provable [0, 0] 3 ([0, 7], 0))
-- Before any answer is given, the reports do not agree.
#guard !passes (provable [] 0 ([], 0))

end Reading

end CourseTest.SpecSolutions
