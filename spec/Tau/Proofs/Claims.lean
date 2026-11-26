import Tau.Claims
import Tau.Proofs.Blocks.ShiftRegister
import Tau.Proofs.Blocks.Accumulator
import Tau.Proofs.Blocks.Mac
import Tau.Proofs.Blocks.Pipeline
import Tau.Proofs.Blocks.Memory
import Tau.Proofs.Blocks.Sequencer
import Tau.Proofs.Blocks.Repeater
import Tau.Proofs.Blocks.SystolicArray
import Tau.Proofs.Machine.Timing
import Tau.Proofs.EndToEnd
import Tau.Proofs.Isa.Encode

/-!
# Every claim is proved

One line for each proposition of `spec/Tau/Claims.lean`: the theorem that says it.
If a statement in `spec/Tau/Claims.lean` and the theorem named beside it ever say
different things, this file stops compiling.
-/

namespace Tau.Claims

theorem shiftRegisterDelays : ShiftRegisterDelays :=
  fun _ n reset inp t => shiftRegister_outAt n reset inp t

theorem accumulatorSums : AccumulatorSums :=
  fun _ _ zero x t => accumulator_outAt_add zero x t

theorem macComputesDotProduct : MacComputesDotProduct :=
  fun _ _ _ zero a b t => mac_outAt_add zero a b t

theorem pipelineDelays : PipelineDelays :=
  fun _ _ d f reset inp t => pipeline_outAt d f reset inp t

theorem memoryReadsLastWrite : MemoryReadsLastWrite :=
  fun _ n init inp t a ha hr => memory_outAt_read n init inp t a ha hr

theorem sequencerIssuesWhatIsDue : SequencerIssuesWhatIsDue :=
  fun _ prog inp t => sequencer_outAt prog inp t

theorem repeaterIssuesWhatIsDue : RepeaterIssuesWhatIsDue :=
  fun _ prog inp t => repeater_outAt prog inp t

theorem systolicArrayComputesMatVec : SystolicArrayComputesMatVec :=
  fun _ _ _ zero _ hn x A c hc i => systolicArray_matvec zero hn x A c hc i

theorem timingRuleEast : TimingRuleEast :=
  fun _ S cfg prog st n hrun h0 p t id kind v hk hres k hq hn hfree =>
    arrives_east S cfg prog st n hrun h0 p t id kind v hk hres k hq hn hfree

theorem timingRuleWest : TimingRuleWest :=
  fun _ S cfg prog st n hrun h0 p t id kind v hk hres k hq hn hfree =>
    arrives_west S cfg prog st n hrun h0 p t id kind v hk hres k hq hn hfree

theorem machineIgnoresValues : MachineIgnoresValues :=
  fun _ _ S T f h cfg prog n image => execute_map S T f h cfg prog n image

theorem issuesIgnoreValues : IssuesIgnoreValues :=
  fun _ _ S T f h cfg prog n image => issues_map S T f h cfg prog n image

theorem decodeInvertsEncode : DecodeInvertsEncode :=
  fun prog slices => Image.decode_encode prog slices

theorem cellLevelRefinesSliceLevel : CellLevelRefinesSliceLevel :=
  fun _ cfg prog n image => cellExecute_eq cfg prog n image

theorem unrollKeepsWhatIsComputed : UnrollKeepsWhatIsComputed :=
  fun _ S k bufs => Kernel.run_unroll S k bufs

theorem unrollKeepsPins : UnrollKeepsPins :=
  fun _ S k bufs => Kernel.timeline_unroll S k bufs

theorem simplifyKeepsValues : SimplifyKeepsValues :=
  fun _ S hS bufs fill e => Expr.denote_simp S hS bufs fill e

theorem wordsObeyTheLaws : WordsObeyTheLaws := wordSem_lawful

theorem checkInlinedIsSound : CheckInlinedIsSound :=
  fun _ S hS s k bufs fill h => checkInlined_sound S hS s k bufs fill h

theorem checkInlinedKeepsPins : CheckInlinedKeepsPins :=
  fun _ S hS s k bufs fill h => checkInlined_pins S hS s k bufs fill h

theorem checkKernelsIsSound : CheckKernelsIsSound :=
  fun _ S hS k k' bufs fill h => checkKernels_sound S hS k k' bufs fill h

theorem checkKernelsKeepsPins : CheckKernelsKeepsPins :=
  fun _ S hS k k' bufs fill h => checkKernels_pins S hS k k' bufs fill h

theorem checkPlacedIsSound : CheckPlacedIsSound :=
  fun _ S hS k pl bufs fill h => checkPlaced_sound S hS k pl bufs fill h

theorem checkPlacedKeepsPins : CheckPlacedKeepsPins :=
  fun _ S hS k pl bufs fill h => checkPlaced_pins S hS k pl bufs fill h

theorem checkScheduledIsSound : CheckScheduledIsSound :=
  fun _ S hS pl c bufs fill h => checkScheduled_sound S hS pl c bufs fill h

theorem checkScheduledKeepsPins : CheckScheduledKeepsPins :=
  fun _ S hS pl c bufs fill h => checkScheduled_pins S hS pl c bufs fill h

theorem checkRoutedIsSound : CheckRoutedIsSound :=
  fun _ S hS c c' bufs fill h => checkRouted_sound S hS c c' bufs fill h

theorem checkRoutedKeepsPins : CheckRoutedKeepsPins :=
  fun _ S hS c c' bufs fill h => checkRouted_pins S hS c c' bufs fill h

theorem checkIsSound : CheckIsSound :=
  fun _ S hS s c bufs fill h => check_sound S hS s c bufs fill h

theorem checkKeepsPins : CheckKeepsPins :=
  fun _ S hS s c bufs fill h => check_pins S hS s c bufs fill h

theorem endToEnd : EndToEnd :=
  fun lanes s c bufs h => end_to_end lanes s c bufs h

theorem endToEndByPasses : EndToEndByPasses :=
  fun lanes s k k₁ k₂ pl c₁ c₂ c₃ c bufs h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ =>
    end_to_end_passes lanes s k k₁ k₂ pl c₁ c₂ c₃ c bufs h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈

end Tau.Claims
