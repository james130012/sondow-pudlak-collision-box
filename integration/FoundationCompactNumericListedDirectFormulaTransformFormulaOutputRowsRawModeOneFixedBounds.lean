import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModePayloadCoreFixedBounds

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 160000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeFixedBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsMappedRowsFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeLeafFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeSyntaxFixedBounds

private abbrev rawZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate.zeroValuation

noncomputable def rawModeOneFixedCertificate
    (mode : Nat) (hmode : mode = 1) :
    CheckedHybridValuationBoundedFormulaCertificate rawZeroValuation
      (rawModeFormula (shortBinaryNumeralTerm mode)) :=
  .disjunctionRight
    (.disjunctionLeft
      (right := rawModeInnerFormula mode)
      (modeNativeEqualityCertificate mode (‘1’ : ValuationTerm) 1
        (termValue_arithmeticOne rawZeroValuation) hmode))

theorem rawModeOneFixedCertificate_structuralPayloadBound_le_fixed
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    ∀ (hmode : mode = 1),
    hybridFormulaStructuralPayloadBound
        (rawModeOneFixedCertificate mode hmode) <=
      outputRowsRawModeFixedPayloadPolynomial bitBound := by
  intro hmode
  have hzero := rawModeZeroFormula_closed_code_full mode bitBound hmodeSize
  have hone := rawModeOneFormula_closed_code_full mode bitBound hmodeSize
  have hinner := rawModeInnerFormula_closed_code mode bitBound hmodeSize
  have hmiddle := rawModeMiddleFormula_closed_code mode bitBound hmodeSize
  have hraw := rawModeFormula_closed_code mode bitBound hmodeSize
  let leafCertificate :=
    modeNativeEqualityCertificate mode (‘1’ : ValuationTerm) 1
      (termValue_arithmeticOne rawZeroValuation) hmode
  have hleaf :
      hybridFormulaStructuralPayloadBound leafCertificate <=
        outputRowsPositiveAtomicFixedPayloadPolynomial bitBound := by
    exact modeNativeEqualityCertificate_structuralPayloadBound_le_fixed mode
      (‘1’ : ValuationTerm) 1 bitBound
      (termValue_arithmeticOne rawZeroValuation) hmode hmodeSize
      (outputRowsModeLiteral_closed _ (Or.inr (Or.inl rfl)))
      (outputRowsModeLiteralCode_le _ bitBound (Or.inr (Or.inl rfl)))
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := rawModeInnerFormula mode) leafCertificate
  have hselected :=
    transparentHybridDisjunctionLeftPayloadBound_le
      (right := rawModeInnerFormula mode) leafCertificate
      (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound) hleaf
  have hmiddleAssembly :=
    transparentHybridDisjunctionLeftPayloadEnvelope_le_closedGeneral_outputRows
      rawZeroValuation (rawModeOneFormula mode) (rawModeInnerFormula mode)
      (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound)
      (outputRowsRawModeSyntaxPolynomial bitBound)
      (by unfold outputRowsRawModeSyntaxPolynomial; omega)
      hone.1 hinner.1 hone.2 hinner.2 hmiddle.2
  have hselectedFixed :
      hybridFormulaStructuralPayloadBound selectedCertificate <=
        hybridDisjunctionGeneralPayloadEnvelope
          (outputRowsRawModeSyntaxPolynomial bitBound)
          (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound) :=
    hselected.trans hmiddleAssembly
  have houterRaw :=
    transparentHybridDisjunctionRightPayloadBound_le
      (left := rawModeZeroFormula mode) selectedCertificate
      (hybridDisjunctionGeneralPayloadEnvelope
        (outputRowsRawModeSyntaxPolynomial bitBound)
        (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound))
      hselectedFixed
  have houterAssembly :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_closedGeneral_outputRows
      rawZeroValuation (rawModeZeroFormula mode) (rawModeMiddleFormula mode)
      (hybridDisjunctionGeneralPayloadEnvelope
        (outputRowsRawModeSyntaxPolynomial bitBound)
        (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound))
      (outputRowsRawModeSyntaxPolynomial bitBound)
      (by unfold outputRowsRawModeSyntaxPolynomial; omega)
      hzero.1 hmiddle.1 hzero.2 hmiddle.2 (by
        simpa only [rawModeFormula_eq_fixedShape] using hraw.2)
  change
    hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := rawModeZeroFormula mode) selectedCertificate) <= _
  exact houterRaw.trans (houterAssembly.trans (by
    simp only [outputRowsRawModeFixedPayloadPolynomial,
      hybridDisjunctionGeneralPayloadEnvelope]
    omega))

#print axioms rawModeOneFixedCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeFixedBounds
