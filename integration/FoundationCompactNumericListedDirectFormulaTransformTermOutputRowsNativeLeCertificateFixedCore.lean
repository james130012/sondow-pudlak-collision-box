import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsNativeLeEnvelopeFixedCore

/-! # Fixed certificate wrapper for term-output-row non-strict order -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 120000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds

private abbrev termRowsLeCertificateZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

theorem termRowsNativeLeCertificate_structuralPayloadBound_le_fixed
    (left right : ValuationTerm)
    (hle : termValue termRowsLeCertificateZeroValuation left <=
      termValue termRowsLeCertificateZeroValuation right)
    (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    hybridFormulaStructuralPayloadBound (nativeLeCertificate left right hle) <=
      termRowsNativeLeFixedPayloadPolynomial bitBound :=
  (nativeLeCertificate_structuralPayloadBound_le_transparent left right hle).trans
    (termRowsNativeLeStructuralEnvelope_le_fixed_of_closed left right bitBound
      hleftClosed hrightClosed hleftCode hrightCode)

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds
