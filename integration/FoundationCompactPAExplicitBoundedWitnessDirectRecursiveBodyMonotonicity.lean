import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectHeadPayloadMonotonicity

/-! # Monotonicity of recursive bounded-witness body-code envelopes -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactPAExplicitBoundedWitnessDirectRecursiveBodyMonotonicity

open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectHeadPayloadMonotonicity

theorem closedShiftShortBinaryNumeralPublicCodeEnvelope_mono
    (arity : Nat) {smallBound largeBound : Nat}
    (hbound : smallBound <= largeBound) :
    closedShiftShortBinaryNumeralPublicCodeEnvelope arity smallBound <=
      closedShiftShortBinaryNumeralPublicCodeEnvelope arity largeBound := by
  induction arity with
  | zero =>
      simpa only [closedShiftShortBinaryNumeralPublicCodeEnvelope] using
        boundedWitnessNumeralTermCodeEnvelope_mono hbound
  | succ arity ih =>
      simp only [closedShiftShortBinaryNumeralPublicCodeEnvelope]
      have hnumeral := boundedWitnessNumeralTermCodeEnvelope_mono hbound
      omega

theorem explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono
    (arity : Nat)
    {smallBound largeBound smallBody largeBody : Nat}
    (hbound : smallBound <= largeBound)
    (hbody : smallBody <= largeBody) :
    explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope arity smallBound
        smallBody <=
      explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope arity largeBound
        largeBody := by
  have hclosed :=
    closedShiftShortBinaryNumeralPublicCodeEnvelope_mono arity hbound
  have hsuccessor :
      explicitBoundedWitnessRecursiveSuccessorTermPublicCodeEnvelope arity
          smallBound <=
        explicitBoundedWitnessRecursiveSuccessorTermPublicCodeEnvelope arity
          largeBound := by
    unfold explicitBoundedWitnessRecursiveSuccessorTermPublicCodeEnvelope
    omega
  have hshifted :
      explicitBoundedWitnessRecursiveShiftedSuccessorPublicCodeEnvelope arity
          smallBound <=
        explicitBoundedWitnessRecursiveShiftedSuccessorPublicCodeEnvelope arity
          largeBound := by
    unfold explicitBoundedWitnessRecursiveShiftedSuccessorPublicCodeEnvelope
    exact Nat.mul_le_mul_left 3 hsuccessor
  have hguard : explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope arity
        smallBound <=
      explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope arity
        largeBound := by
    unfold explicitBoundedWitnessRecursiveGuardPublicCodeEnvelope
    omega
  unfold explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope
  omega

#print axioms explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono

end FoundationCompactPAExplicitBoundedWitnessDirectRecursiveBodyMonotonicity
