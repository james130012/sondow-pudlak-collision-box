import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds
import integration.FoundationCompactPAContextCostPolynomialBounds
import integration.FoundationCompactPAExponentialShortNumeralCompilerBounds
import integration.FoundationCompactPAUnaryAtomicTransportPolynomialBounds

/-! # Monotonicity of one public direct bounded-witness layer -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactPAExplicitBoundedWitnessDirectHeadPayloadMonotonicity

open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAUnaryAtomicTransportPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxTransformationBounds
open FoundationCompactPABoundedWitnessGuardCompiler
open FoundationCompactPAExponentialShortNumeralCompilerBounds

theorem boundedWitnessNumeralTermCodeEnvelope_mono
    {small large : Nat} (hbound : small <= large) :
    boundedWitnessNumeralTermCodeEnvelope small <=
      boundedWitnessNumeralTermCodeEnvelope large := by
  unfold boundedWitnessNumeralTermCodeEnvelope
  exact binaryNumeralTermCodeEnvelope_mono_short (Nat.size_le_size hbound)

theorem uniformRewritingFormulaCodeEnvelope_mono
    {smallImage largeImage smallFormula largeFormula : Nat}
    (himage : smallImage <= largeImage)
    (hformula : smallFormula <= largeFormula) :
    uniformRewritingFormulaCodeEnvelope smallImage smallFormula <=
      uniformRewritingFormulaCodeEnvelope largeImage largeFormula := by
  unfold uniformRewritingFormulaCodeEnvelope
  gcongr

theorem explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono
    (contextCodeBound : Nat)
    {smallBound largeBound smallBody largeBody : Nat}
    (hbound : smallBound <= largeBound)
    (hbody : smallBody <= largeBody) :
    explicitBoundedWitnessDirectHeadPublicPayloadPolynomial contextCodeBound
        smallBound smallBody <=
      explicitBoundedWitnessDirectHeadPublicPayloadPolynomial contextCodeBound
        largeBound largeBody := by
  have hnumeral := boundedWitnessNumeralTermCodeEnvelope_mono hbound
  have hlifted : liftedRewritingImageCodeBound
      (boundedWitnessNumeralTermCodeEnvelope smallBound) <=
      liftedRewritingImageCodeBound
        (boundedWitnessNumeralTermCodeEnvelope largeBound) := by
    unfold liftedRewritingImageCodeBound
    omega
  have htail : explicitWitnessBodyAfterTailPublicCodeEnvelope smallBound
        smallBody <=
      explicitWitnessBodyAfterTailPublicCodeEnvelope largeBound
        largeBody := by
    unfold explicitWitnessBodyAfterTailPublicCodeEnvelope
    exact uniformRewritingFormulaCodeEnvelope_mono hlifted hbody
  have hinstalled : explicitWitnessInstalledPublicCodeEnvelope smallBound
        smallBody <=
      explicitWitnessInstalledPublicCodeEnvelope largeBound largeBody := by
    unfold explicitWitnessInstalledPublicCodeEnvelope
    exact uniformRewritingFormulaCodeEnvelope_mono hnumeral hbody
  have hsuccessor : boundedWitnessSuccessorTermCodeEnvelope smallBound <=
      boundedWitnessSuccessorTermCodeEnvelope largeBound := by
    unfold boundedWitnessSuccessorTermCodeEnvelope
    omega
  have hshifted : boundedWitnessShiftedSuccessorTermCodeEnvelope smallBound <=
      boundedWitnessShiftedSuccessorTermCodeEnvelope largeBound := by
    unfold boundedWitnessShiftedSuccessorTermCodeEnvelope
    exact Nat.mul_le_mul_left 3 hsuccessor
  have hguardCode : boundedWitnessGuardFormulaCodeEnvelope smallBound <=
      boundedWitnessGuardFormulaCodeEnvelope largeBound := by
    unfold boundedWitnessGuardFormulaCodeEnvelope
    omega
  have hopenGuard : boundedWitnessOpenGuardFormulaCodeEnvelope smallBound <=
      boundedWitnessOpenGuardFormulaCodeEnvelope largeBound := by
    unfold boundedWitnessOpenGuardFormulaCodeEnvelope
    omega
  have hmatrix : explicitBoundedWitnessMatrixPublicCodeEnvelope smallBound
        smallBody <=
      explicitBoundedWitnessMatrixPublicCodeEnvelope largeBound largeBody := by
    unfold explicitBoundedWitnessMatrixPublicCodeEnvelope
    omega
  have hbounded :
      explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope smallBound
          smallBody <=
        explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope largeBound
          largeBody := by
    unfold explicitBoundedWitnessBoundedMatrixPublicCodeEnvelope
    omega
  have hinstantiated :
      explicitBoundedWitnessInstantiatedPublicCodeEnvelope smallBound
          smallBody <=
        explicitBoundedWitnessInstantiatedPublicCodeEnvelope largeBound
          largeBody := by
    unfold explicitBoundedWitnessInstantiatedPublicCodeEnvelope
    exact substitutionFormulaCodeEnvelope_mono_local hbounded hnumeral
  have hexistential :
      explicitBoundedWitnessExistentialPublicCodeEnvelope smallBound
          smallBody <=
        explicitBoundedWitnessExistentialPublicCodeEnvelope largeBound
          largeBody := by
    unfold explicitBoundedWitnessExistentialPublicCodeEnvelope
    omega
  have hsyntax :
      explicitBoundedWitnessDirectHeadPublicSyntaxResource contextCodeBound
          smallBound smallBody <=
        explicitBoundedWitnessDirectHeadPublicSyntaxResource contextCodeBound
          largeBound largeBody := by
    unfold explicitBoundedWitnessDirectHeadPublicSyntaxResource
    omega
  have hsize : Nat.size smallBound <= Nat.size largeBound :=
    Nat.size_le_size hbound
  have hguardWidth : boundedWitnessGuardUniformBitWidth smallBound <=
      boundedWitnessGuardUniformBitWidth largeBound := by
    unfold boundedWitnessGuardUniformBitWidth boundedWitnessGuardBitWidth
    omega
  have hguardPayload :=
    boundedWitnessGuardPayloadPolynomial_mono_uniform hguardWidth
  have hassembly := generalContextAssemblyEnvelope_mono_uniform hsyntax
  unfold explicitBoundedWitnessDirectHeadPublicPayloadPolynomial
  omega

#print axioms explicitBoundedWitnessDirectHeadPublicPayloadPolynomial_mono

end FoundationCompactPAExplicitBoundedWitnessDirectHeadPayloadMonotonicity
