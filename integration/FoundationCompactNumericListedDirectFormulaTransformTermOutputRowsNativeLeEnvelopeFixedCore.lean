import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedCore
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixAtomicFixedBounds

/-! # Fixed structural envelope for term-output-row non-strict order -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 120000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixAtomicFixedBounds

private abbrev termRowsLeEnvelopeZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate.zeroValuation

def termRowsNativeLeFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  appendSourcePrefixLeFixedPayloadPolynomial
    (termOutputFailureTermCodePolynomial bitBound)

theorem termRowsNativeLeStructuralEnvelope_le_fixed_of_closed
    (left right : ValuationTerm) (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    termRowsNativeLeStructuralEnvelope left right <=
      termRowsNativeLeFixedPayloadPolynomial bitBound := by
  change appendSourcePrefixValuationLeStructuralEnvelopeAt
      termRowsLeEnvelopeZeroValuation left right <=
    appendSourcePrefixLeFixedPayloadPolynomial
      (termOutputFailureTermCodePolynomial bitBound)
  exact appendSourcePrefixValuationLeStructuralEnvelopeAt_le_fixed
    termRowsLeEnvelopeZeroValuation left right
    (termOutputFailureTermCodePolynomial bitBound)
    hleftClosed hrightClosed hleftCode hrightCode

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds
