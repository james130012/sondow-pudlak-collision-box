import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedCore

/-! # Fixed formula-code resource for term-output failure atoms -/

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
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAtomicFixedBounds

theorem failureNativeNeFormula_code_le
    (left right : ValuationTerm) (bitBound : Nat)
    (hleft : (binaryTermCode left).length <=
      termOutputFailureTermCodePolynomial bitBound)
    (hright : (binaryTermCode right).length <=
      termOutputFailureTermCodePolynomial bitBound) :
    (binaryFormulaCode (nativeNeFormula left right)).length <=
      termOutputFailureAtomFormulaCodePolynomial bitBound := by
  have heq' : (binaryFormulaCode (nativeEqFormula left right)).length <=
      outputRowsAtomicLeafFormulaCodePolynomial bitBound := by
    rw [show nativeEqFormula left right =
        LO.FirstOrder.Semiformula.rel Language.Eq.eq ![left, right] by
      unfold nativeEqFormula
      exact LO.FirstOrder.Semiformula.Operator.eq_def left right]
    exact outputRowsBinaryRelationCode_le Language.Eq.eq left right bitBound
      (by simpa [termOutputFailureTermCodePolynomial] using hleft)
      (by simpa [termOutputFailureTermCodePolynomial] using hright)
  have hneg := binaryFormulaCode_neg_length_le (nativeEqFormula left right)
  unfold nativeNeFormula termOutputFailureAtomFormulaCodePolynomial
  omega

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
