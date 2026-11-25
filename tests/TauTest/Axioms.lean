import Tau

/-!
# Test: no theorem depends on `sorry`

`#print axioms` lists what a theorem ultimately rests on. The `#guard_msgs`
commands below fail the build if that list ever changes, in particular if a
`sorry` creeps in.

The theorems below rest only on Lean's three standard axioms. In particular
none of them uses `bv_decide`, whose proofs add an axiom that trusts the Lean
compiler (see `Tau/Proofs/Data/Lane.lean`).
-/

/-- info: 'Tau.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Tau.check_sound

/-- info: 'Tau.checkPlaced_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Tau.checkPlaced_sound

/-- info: 'Tau.checkKernels_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Tau.checkKernels_sound

/-- info: 'Tau.checkScheduled_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Tau.checkScheduled_sound

/-- info: 'Tau.checkRouted_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Tau.checkRouted_sound

/-- info: 'Tau.passes_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Tau.passes_sound

/-- info: 'Tau.arrives_east' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Tau.arrives_east

/-- info: 'Tau.arrives_west' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Tau.arrives_west

/-- info: 'Tau.Kernel.exec_unroll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Tau.Kernel.exec_unroll

/-- info: 'Tau.systolicArray_matvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tau.systolicArray_matvec

/-- info: 'Tau.cellExecute_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tau.cellExecute_eq

/-- info: 'Tau.end_to_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tau.end_to_end

/-- info: 'Tau.Claims.endToEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tau.Claims.endToEnd

/-- info: 'Tau.repeater_outAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tau.repeater_outAt
