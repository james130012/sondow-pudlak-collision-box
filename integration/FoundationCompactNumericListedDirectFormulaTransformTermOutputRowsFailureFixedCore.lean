import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureTermFixedCore

/-! # Fixed negative atomic resources for term-output failure decisions -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 240000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds

theorem termRowsNativeNeStructuralEnvelope_le_fixed
    (left right : ValuationTerm) (bitBound : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hrightCode : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    termRowsNativeNeStructuralEnvelope left right <=
      termOutputFailureAtomicPayloadPolynomial bitBound := by
  unfold termRowsNativeNeStructuralEnvelope
    termOutputFailureAtomicPayloadPolynomial
  exact compileNegativeRelationPayloadResource_le_fixed_of_closed
    _ Language.Eq.eq left right 0
    (termOutputFailureTermCodePolynomial bitBound)
    hleftClosed hrightClosed hleftCode hrightCode

theorem failureNativeNeFormula_closed
    (left right : ValuationTerm)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (nativeNeFormula left right).freeVariables = ∅ := by
  unfold nativeNeFormula nativeEqFormula
  rw [LO.FirstOrder.Semiformula.freeVariables_not]
  exact outputRowsBinaryRelation_closed Language.Eq.eq left right hleft hright

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds

