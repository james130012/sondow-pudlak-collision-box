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

noncomputable def rawModeTwoFixedCertificate
    (mode : Nat) (hmode : mode = 2) :
    CheckedHybridValuationBoundedFormulaCertificate rawZeroValuation
      (rawModeFormula (shortBinaryNumeralTerm mode)) :=
  .disjunctionRight
    (.disjunctionRight
      (.disjunctionLeft
        (right := rawModeFiveFormula mode)
        (modeNativeEqualityCertificate mode (‘2’ : ValuationTerm) 2
          (termValue_arithmeticTwo rawZeroValuation) hmode)))

theorem rawModeTwoFixedCertificate_structuralPayloadBound_le_fixed
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    ∀ (hmode : mode = 2),
    hybridFormulaStructuralPayloadBound
        (rawModeTwoFixedCertificate mode hmode) <=
      outputRowsRawModeFixedPayloadPolynomial bitBound := by
  intro hmode
  have hzero := rawModeZeroFormula_closed_code_full mode bitBound hmodeSize
  have hone := rawModeOneFormula_closed_code_full mode bitBound hmodeSize
  have htwo := rawModeTwoFormula_closed_code_full mode bitBound hmodeSize
  have hfive := rawModeFiveFormula_closed_code_full mode bitBound hmodeSize
  have hinner := rawModeInnerFormula_closed_code mode bitBound hmodeSize
  have hmiddle := rawModeMiddleFormula_closed_code mode bitBound hmodeSize
  have hraw := rawModeFormula_closed_code mode bitBound hmodeSize
  let leafCertificate :=
    modeNativeEqualityCertificate mode (‘2’ : ValuationTerm) 2
      (termValue_arithmeticTwo rawZeroValuation) hmode
  have hleaf :
      hybridFormulaStructuralPayloadBound leafCertificate <=
        outputRowsPositiveAtomicFixedPayloadPolynomial bitBound := by
    exact modeNativeEqualityCertificate_structuralPayloadBound_le_fixed mode
      (‘2’ : ValuationTerm) 2 bitBound
      (termValue_arithmeticTwo rawZeroValuation) hmode hmodeSize
      (outputRowsModeLiteral_closed _ (Or.inr (Or.inr (Or.inl rfl))))
      (outputRowsModeLiteralCode_le _ bitBound
        (Or.inr (Or.inr (Or.inl rfl))))
  let innerCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := rawModeFiveFormula mode) leafCertificate
  have hinnerRaw :=
    transparentHybridDisjunctionLeftPayloadBound_le
      (right := rawModeFiveFormula mode) leafCertificate
      (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound) hleaf
  have hinnerAssembly :=
    transparentHybridDisjunctionLeftPayloadEnvelope_le_closedGeneral_outputRows
      rawZeroValuation (rawModeTwoFormula mode) (rawModeFiveFormula mode)
      (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound)
      (outputRowsRawModeSyntaxPolynomial bitBound)
      (by unfold outputRowsRawModeSyntaxPolynomial; omega)
      htwo.1 hfive.1 htwo.2 hfive.2 hinner.2
  have hinnerFixed :
      hybridFormulaStructuralPayloadBound innerCertificate <=
        hybridDisjunctionGeneralPayloadEnvelope
          (outputRowsRawModeSyntaxPolynomial bitBound)
          (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound) :=
    hinnerRaw.trans hinnerAssembly
  let middleCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := rawModeOneFormula mode) innerCertificate
  have hmiddleRaw :=
    transparentHybridDisjunctionRightPayloadBound_le
      (left := rawModeOneFormula mode) innerCertificate
      (hybridDisjunctionGeneralPayloadEnvelope
        (outputRowsRawModeSyntaxPolynomial bitBound)
        (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound))
      hinnerFixed
  have hmiddleAssembly :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_closedGeneral_outputRows
      rawZeroValuation (rawModeOneFormula mode) (rawModeInnerFormula mode)
      (hybridDisjunctionGeneralPayloadEnvelope
        (outputRowsRawModeSyntaxPolynomial bitBound)
        (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound))
      (outputRowsRawModeSyntaxPolynomial bitBound)
      (by unfold outputRowsRawModeSyntaxPolynomial; omega)
      hone.1 hinner.1 hone.2 hinner.2 hmiddle.2
  have hmiddleFixed :
      hybridFormulaStructuralPayloadBound middleCertificate <=
        hybridDisjunctionGeneralPayloadEnvelope
          (outputRowsRawModeSyntaxPolynomial bitBound)
          (hybridDisjunctionGeneralPayloadEnvelope
            (outputRowsRawModeSyntaxPolynomial bitBound)
            (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound)) :=
    hmiddleRaw.trans hmiddleAssembly
  have houterRaw :=
    transparentHybridDisjunctionRightPayloadBound_le
      (left := rawModeZeroFormula mode) middleCertificate
      (hybridDisjunctionGeneralPayloadEnvelope
        (outputRowsRawModeSyntaxPolynomial bitBound)
        (hybridDisjunctionGeneralPayloadEnvelope
          (outputRowsRawModeSyntaxPolynomial bitBound)
          (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound)))
      hmiddleFixed
  have houterAssembly :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_closedGeneral_outputRows
      rawZeroValuation (rawModeZeroFormula mode) (rawModeMiddleFormula mode)
      (hybridDisjunctionGeneralPayloadEnvelope
        (outputRowsRawModeSyntaxPolynomial bitBound)
        (hybridDisjunctionGeneralPayloadEnvelope
          (outputRowsRawModeSyntaxPolynomial bitBound)
          (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound)))
      (outputRowsRawModeSyntaxPolynomial bitBound)
      (by unfold outputRowsRawModeSyntaxPolynomial; omega)
      hzero.1 hmiddle.1 hzero.2 hmiddle.2 (by
        simpa only [rawModeFormula_eq_fixedShape] using hraw.2)
  change
    hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := rawModeZeroFormula mode) middleCertificate) <= _
  exact houterRaw.trans (by
    simpa only [outputRowsRawModeFixedPayloadPolynomial, rawModeMiddleFormula,
      rawModeInnerFormula, rawModeTwoFormula] using houterAssembly)

#print axioms rawModeTwoFixedCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeFixedBounds
