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

noncomputable def rawModeZeroFixedCertificate
    (mode : Nat) (hmode : mode = 0) :
    CheckedHybridValuationBoundedFormulaCertificate rawZeroValuation
      (rawModeFormula (shortBinaryNumeralTerm mode)) :=
  .disjunctionLeft
    (right := rawModeMiddleFormula mode)
    (modeNativeEqualityCertificate mode (‘0’ : ValuationTerm) 0
      (termValue_arithmeticZero rawZeroValuation) hmode)

theorem rawModeZeroFixedCertificate_structuralPayloadBound_le_fixed
    (mode bitBound : Nat) (hmodeSize : Nat.size mode <= bitBound) :
    ∀ (hmode : mode = 0),
    hybridFormulaStructuralPayloadBound
        (rawModeZeroFixedCertificate mode hmode) <=
      outputRowsRawModeFixedPayloadPolynomial bitBound := by
  intro hmode
  have hzero := rawModeZeroFormula_closed_code_full mode bitBound hmodeSize
  have hmiddle := rawModeMiddleFormula_closed_code mode bitBound hmodeSize
  have hraw := rawModeFormula_closed_code mode bitBound hmodeSize
  let leafCertificate :=
    modeNativeEqualityCertificate mode (‘0’ : ValuationTerm) 0
      (termValue_arithmeticZero rawZeroValuation) hmode
  have hleaf :
      hybridFormulaStructuralPayloadBound leafCertificate <=
        outputRowsPositiveAtomicFixedPayloadPolynomial bitBound := by
    exact modeNativeEqualityCertificate_structuralPayloadBound_le_fixed mode
      (‘0’ : ValuationTerm) 0 bitBound
      (termValue_arithmeticZero rawZeroValuation) hmode hmodeSize
      (outputRowsModeLiteral_closed _ (Or.inl rfl))
      (outputRowsModeLiteralCode_le _ bitBound (Or.inl rfl))
  have hselected :=
    transparentHybridDisjunctionLeftPayloadBound_le
      (right := rawModeMiddleFormula mode) leafCertificate
      (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound) hleaf
  have hassembly :=
    transparentHybridDisjunctionLeftPayloadEnvelope_le_closedGeneral_outputRows
      rawZeroValuation (rawModeZeroFormula mode) (rawModeMiddleFormula mode)
      (outputRowsPositiveAtomicFixedPayloadPolynomial bitBound)
      (outputRowsRawModeSyntaxPolynomial bitBound)
      (by unfold outputRowsRawModeSyntaxPolynomial; omega)
      hzero.1 hmiddle.1 hzero.2 hmiddle.2 (by
        simpa only [rawModeFormula_eq_fixedShape] using hraw.2)
  change
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := rawModeMiddleFormula mode) leafCertificate) <= _
  exact hselected.trans (hassembly.trans (by
    simp only [outputRowsRawModeFixedPayloadPolynomial,
      hybridDisjunctionGeneralPayloadEnvelope]
    omega))

#print axioms rawModeZeroFixedCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeFixedBounds
