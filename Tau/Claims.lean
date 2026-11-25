import Tau.Blocks.ShiftRegister
import Tau.Blocks.Accumulator
import Tau.Blocks.Mac
import Tau.Blocks.Pipeline
import Tau.Blocks.Memory
import Tau.Blocks.Sequencer
import Tau.Blocks.Repeater
import Tau.Blocks.SystolicArray
import Tau.SliceLevel.Timing
import Tau.CellLevel.Machine
import Tau.Passes.Unroll
import Tau.Check.Passes

/-!
# What tau-tpu claims

Every main statement of the development, as a named proposition. Each is
proved in `Tau/Proofs/Claims.lean`, by the theorem named in its comment.

This file is for reading. It imports definitions only, so everything in a
statement here is something defined outside `Tau/Proofs/`. A person who has
read the definitions and this file knows what is claimed, without opening a
proof. A proof can be long and written by anyone, or anything; a statement
has to be read by a person.

`docs/overview.md` says the same in words, and the table under "What is
proved" in `README.md` says what is not claimed.
-/

namespace Tau.Claims

/-! ## The components -/

/-- A shift register of depth `n` outputs the input of `n` cycles earlier,
and the reset value before that. (`shiftRegister_outAt`) -/
def ShiftRegisterDelays : Prop :=
  ∀ (α : Type) (n : Nat) (reset : α) (inp : Signal α) (t : Nat),
    (shiftRegister n reset).outAt inp t = if n ≤ t then inp (t - n) else reset

/-- An accumulator told to add on every cycle outputs, at cycle `t`, the sum
of the first `t` inputs. (`accumulator_outAt_add`) -/
def AccumulatorSums : Prop :=
  ∀ (α : Type) [Add α] (zero : α) (x : Signal α) (t : Nat),
    (accumulator zero).outAt (fun k => .add (x k)) t = sumTo zero x t

/-- A multiply-accumulate cell fed one pair per cycle outputs, at cycle `t`,
the dot product of the first `t` pairs. (`mac_outAt_add`) -/
def MacComputesDotProduct : Prop :=
  ∀ (α : Type) [Add α] [Mul α] (zero : α) (a b : Signal α) (t : Nat),
    (mac zero).outAt (fun k => .add (a k, b k)) t = sumTo zero (fun k => a k * b k) t

/-- A pipeline of depth `d` outputs the function of the input of `d` cycles
earlier, and the reset value before that. (`pipeline_outAt`) -/
def PipelineDelays : Prop :=
  ∀ (α β : Type) (d : Nat) (f : α → β) (reset : β) (inp : Signal α) (t : Nat),
    (pipeline d f reset).outAt inp t = if d ≤ t then f (inp (t - d)) else reset

/-- A read of a valid address returns the value most recently written to it,
or its starting value. (`memory_outAt_read`) -/
def MemoryReadsLastWrite : Prop :=
  ∀ (α : Type) (n : Nat) (init : Vector α n) (inp : Signal (MemIn α)) (t a : Nat)
    (ha : a < n), inp t = .read a →
      (memory n init).outAt inp t = some ((lastWrite inp a t).getD init[a])

/-- A sequencer outputs, at cycle `t`, the items due at `t`.
(`sequencer_outAt`) -/
def SequencerIssuesWhatIsDue : Prop :=
  ∀ (α : Type) (prog : List (Nat × α)) (inp : Signal Unit) (t : Nat),
    (sequencer prog).outAt inp t = dueAt prog t

/-- A repeater, which counts with registers, issues at cycle `t` what the
description without registers says is due at `t`. (`repeater_outAt`) -/
def RepeaterIssuesWhatIsDue : Prop :=
  ∀ (α : Type) (prog : List (Entry α)) (inp : Signal Unit) (t : Nat),
    (repeater prog).outAt inp t = prog.filterMap fun e => e.dueAt t

/-- If the coefficient `A i j` is fed to cell `j` at cycle `i + j`, a systolic
array holding `x` outputs the product of row `i` with `x` at cycle `i + n`.
(`systolicArray_matvec`) -/
def SystolicArrayComputesMatVec : Prop :=
  ∀ (α : Type) [Add α] [Mul α] (zero : α) (n : Nat), 0 < n → ∀ (x : Vector α n)
    (A : Nat → Nat → α) (c : Signal (Vector α n)),
    (∀ i j (hj : j < n), (c (i + j))[j] = A i j) → ∀ (i : Nat),
      (systolicArray zero x).outAt c (i + n) =
        sumTo zero (fun k => A i k * x[k]?.getD zero) n

/-! ## The machine -/

/-- **The timing rule, going east.** In a run that does not trap, if the slice
at `p` computes `v` on cycle `t` for the stream `id` going east, and no slice
on the way places a word of its own on that stream just as `v` arrives, then
on cycle `t + delay + 1 + k` the stream holds `v` at position `p + k`.
(`arrives_east`) -/
def TimingRuleEast : Prop :=
  ∀ (V : Type) (S : Sem V) (cfg : Config) (prog : Program) (st : Nat → State V) (n : Nat),
    IsRun S cfg prog st n → (st 0).Shaped cfg →
    ∀ (p t id : Nat) (kind : Kind) (v : V), cfg.kindAt p = some kind →
    (st t).result S cfg prog p = some (⟨.east, id⟩, v) →
    ∀ (k : Nat), p + k < cfg.kinds.length → t + cfg.delay kind + 1 + k ≤ n →
    (∀ i, 1 ≤ i → i ≤ k → ∀ w,
      (st (t + cfg.delay kind + i)).out S cfg prog (p + i) ≠ some (⟨.east, id⟩, w)) →
    (st (t + cfg.delay kind + 1 + k)).sample (p + k) ⟨.east, id⟩ = some v

/-- **The timing rule, going west.** The mirror image. (`arrives_west`) -/
def TimingRuleWest : Prop :=
  ∀ (V : Type) (S : Sem V) (cfg : Config) (prog : Program) (st : Nat → State V) (n : Nat),
    IsRun S cfg prog st n → (st 0).Shaped cfg →
    ∀ (p t id : Nat) (kind : Kind) (v : V), cfg.kindAt p = some kind →
    (st t).result S cfg prog p = some (⟨.west, id⟩, v) →
    ∀ (k : Nat), k ≤ p → t + cfg.delay kind + 1 + k ≤ n →
    (∀ i, 1 ≤ i → i ≤ k → ∀ w,
      (st (t + cfg.delay kind + i)).out S cfg prog (p - i) ≠ some (⟨.west, id⟩, w)) →
    (st (t + cfg.delay kind + 1 + k)).sample (p - k) ⟨.west, id⟩ = some v

/-- **The machine does not look at its values.** Running a program and then
applying a function that respects the operations gives what applying the
function first and then running gives, traps included. (`execute_map`) -/
def MachineIgnoresValues : Prop :=
  ∀ (V W : Type) (S : Sem V) (T : Sem W) (f : V → W), S.Hom T f →
    ∀ (cfg : Config) (prog : Program) (n : Nat) (image : List (List V)),
      execute T cfg prog n (image.map (List.map f)) =
        (execute S cfg prog n image).map (List.map (List.map f))

/-- **Refinement.** The machine built from blocks and the machine
specification give the same result on every chip and program: the same
trap, or the same final memory. (`cellExecute_eq`) -/
def CellLevelRefinesSliceLevel : Prop :=
  ∀ (lanes : Nat) (cfg : Config) (prog : Program) (n : Nat)
    (image : List (List (Word lanes))),
    cellExecute cfg prog n image = execute (wordSem lanes) cfg prog n image

/-! ## The compiler -/

/-- The Lean copy of `tau-unroll` keeps what a kernel computes.
(`Kernel.run_unroll`) -/
def UnrollKeepsWhatIsComputed : Prop :=
  ∀ (V : Type) (S : Sem V) (k : Kernel) (bufs : List (List V)),
    Kernel.run S (k.unroll.map Item.stmt) bufs = k.run S bufs

/-- Simplifying an expression keeps its value, for operations that obey the
laws. (`Expr.denote_simp`) -/
def SimplifyKeepsValues : Prop :=
  ∀ (V : Type) (S : Sem V), S.Lawful → ∀ (bufs : List (List V)) (fill : V) (e : Expr),
    e.simp.denote S bufs fill = e.denote S bufs fill

/-- Real words obey the laws. (`wordSem_lawful`) -/
def WordsObeyTheLaws : Prop := ∀ (lanes : Nat), (wordSem lanes).Lawful

/-- **`tau-simplify`, `tau-unroll`.** Two kernels the check accepts compute
the same buffers. The value `fill` is not used in the statement; it is there
because the type of values must have at least one. (`checkKernels_sound`) -/
def CheckKernelsIsSound : Prop :=
  ∀ (V : Type) (S : Sem V), S.Lawful → ∀ (k k' : Kernel) (bufs : List (List V)) (_fill : V),
    checkKernels k k' (bufs.map List.length) = true →
      ∃ out, k.run S bufs = some out ∧ k'.run S bufs = some out

/-- **`tau-place`.** A placed program the check accepts ends with the buffers
the kernel computes. (`checkPlaced_sound`) -/
def CheckPlacedIsSound : Prop :=
  ∀ (V : Type) (S : Sem V), S.Lawful → ∀ (k : Kernel) (pl : Placed)
    (bufs : List (List V)) (fill : V),
    checkPlaced k (bufs.map List.length) pl = true →
      ∃ mem out,
        pl.execute S (pl.image bufs fill) = some mem ∧
        k.run S bufs = some out ∧
        extract pl.map mem fill = out

/-- **`tau-schedule`.** A compiled program the check accepts for a placed
program runs without a trap and ends with the same buffers.
(`checkScheduled_sound`) -/
def CheckScheduledIsSound : Prop :=
  ∀ (V : Type) (S : Sem V), S.Lawful → ∀ (pl : Placed) (c : Compiled)
    (bufs : List (List V)) (fill : V),
    checkScheduled pl c = true →
      ∃ mem mem',
        pl.execute S (pl.image bufs fill) = some mem ∧
        execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem' ∧
        extract c.map mem' fill = extract pl.map mem fill

/-- **`tau-route`.** Two compiled programs the check accepts both run without
a trap and end with the same buffers. (`checkRouted_sound`) -/
def CheckRoutedIsSound : Prop :=
  ∀ (V : Type) (S : Sem V), S.Lawful → ∀ (c c' : Compiled)
    (bufs : List (List V)) (fill : V),
    checkRouted c c' = true →
      ∃ mem mem',
        execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem ∧
        execute S c'.cfg c'.prog c'.cycles (c'.image bufs fill) = .ok mem' ∧
        extract c'.map mem' fill = extract c.map mem fill

/-- **The whole compiler, by one check.** A compiled program the check accepts
for a kernel runs on the machine specification without a trap and ends with
the buffers the kernel computes. (`check_sound`) -/
def CheckIsSound : Prop :=
  ∀ (V : Type) (S : Sem V), S.Lawful → ∀ (k : Kernel) (c : Compiled)
    (bufs : List (List V)) (fill : V),
    check k (bufs.map List.length) c = true →
      ∃ mem out,
        execute S c.cfg c.prog c.cycles (c.image bufs fill) = .ok mem ∧
        k.run S bufs = some out ∧
        extract c.map mem fill = out

/-! ## End to end -/

/-- **End to end.** A compiled program the check accepts for a kernel, run on
the machine built from blocks from any buffer contents, finishes without a
trap and leaves in memory the buffers the kernel computes. (`end_to_end`) -/
def EndToEnd : Prop :=
  ∀ (lanes : Nat) (k : Kernel) (c : Compiled) (bufs : List (List (Word lanes))),
    check k (bufs.map List.length) c = true →
      ∃ mem out,
        cellExecute c.cfg c.prog c.cycles (c.image bufs Word.zero) = .ok mem ∧
        k.run (wordSem lanes) bufs = some out ∧
        extract c.map mem Word.zero = out

/-- **End to end, pass by pass.** The same, when each of the five passes was
checked against its own input. `k₁`, `k₂`, `pl` and `c₁` are the outputs of
`tau-simplify`, `tau-unroll`, `tau-place` and `tau-schedule`.
(`end_to_end_passes`) -/
def EndToEndByPasses : Prop :=
  ∀ (lanes : Nat) (k k₁ k₂ : Kernel) (pl : Placed) (c₁ c : Compiled)
    (bufs : List (List (Word lanes))),
    checkKernels k k₁ (bufs.map List.length) = true →
    checkKernels k₁ k₂ (bufs.map List.length) = true →
    checkPlaced k₂ (bufs.map List.length) pl = true →
    checkScheduled pl c₁ = true →
    checkRouted c₁ c = true →
      ∃ mem out,
        cellExecute c.cfg c.prog c.cycles (c.image bufs Word.zero) = .ok mem ∧
        k.run (wordSem lanes) bufs = some out ∧
        extract c.map mem Word.zero = out

end Tau.Claims
