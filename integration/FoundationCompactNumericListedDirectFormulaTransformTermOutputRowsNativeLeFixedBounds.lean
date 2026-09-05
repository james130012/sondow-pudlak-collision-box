import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsNativeLeCertificateFixedCore

/-! # Fixed positive-count certificate for term-output rows -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 120000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds

theorem consumedCountPositiveCertificate_structuralPayloadBound_le_fixed
    (consumedCount bitBound : Nat)
    (hpositive : 1 <= consumedCount)
    (hconsumedSize : Nat.size consumedCount <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (consumedCountPositiveCertificate consumedCount hpositive) <=
      termRowsNativeLeFixedPayloadPolynomial bitBound := by
  have hle : termValue
      FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation
      (‘1’ : ValuationTerm) <=
      termValue
        FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation
        (shortBinaryNumeralTerm consumedCount) := by
    simpa [termValue_arithmeticOne,
      termValue_shortBinaryNumeralTerm] using hpositive
  have hfixed :=
    termRowsNativeLeCertificate_structuralPayloadBound_le_fixed
      (‘1’ : ValuationTerm) (shortBinaryNumeralTerm consumedCount) hle bitBound
      (termRowsLiteral_closed (‘1’ : ValuationTerm) (Or.inr (Or.inl rfl)))
      (shortBinaryNumeralTerm_freeVariables_eq_empty _)
      (termRowsLiteralCode_le (‘1’ : ValuationTerm) bitBound
        (Or.inr (Or.inl rfl)))
      (termRowsShortNumeralCode_le consumedCount bitBound hconsumedSize)
  simpa only [consumedCountPositiveCertificate] using hfixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds
