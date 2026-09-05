import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardSyntaxFixedCore

/-! # Uniform fixed leaf resource for term-output-row guards -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAtomicFixedBounds

def termRowsGuardLeafFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  termRowsPositiveAtomicFixedPayloadPolynomial bitBound +
    termRowsNativeLeFixedPayloadPolynomial bitBound

theorem termRowsNativeEqStructuralEnvelope_le_guardLeaf
    (left right : ValuationTerm) (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    termRowsNativeEqStructuralEnvelope left right <=
      termRowsGuardLeafFixedPayloadPolynomial bitBound := by
  have hfixed := termRowsNativeEqStructuralEnvelope_le_fixed_of_closed
    left right bitBound hleftClosed hrightClosed hleftCode hrightCode
  unfold termRowsGuardLeafFixedPayloadPolynomial
  omega

theorem termRowsNativeLtStructuralEnvelope_le_guardLeaf
    (left right : ValuationTerm) (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    termRowsNativeLtStructuralEnvelope left right <=
      termRowsGuardLeafFixedPayloadPolynomial bitBound := by
  have hfixed := termRowsNativeLtStructuralEnvelope_le_fixed_of_closed
    left right bitBound hleftClosed hrightClosed hleftCode hrightCode
  unfold termRowsGuardLeafFixedPayloadPolynomial
  omega

theorem termRowsNativeLeStructuralEnvelope_le_guardLeaf
    (left right : ValuationTerm) (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    termRowsNativeLeStructuralEnvelope left right <=
      termRowsGuardLeafFixedPayloadPolynomial bitBound := by
  have hfixed := termRowsNativeLeStructuralEnvelope_le_fixed_of_closed
    left right bitBound hleftClosed hrightClosed hleftCode hrightCode
  unfold termRowsGuardLeafFixedPayloadPolynomial
  omega

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardFixedBounds
