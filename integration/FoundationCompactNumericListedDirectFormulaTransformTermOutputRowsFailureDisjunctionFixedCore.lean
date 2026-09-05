import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFormulaCodeFixedCore

/-! # Fixed disjunction resources for term-output failure decisions -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 240000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds

theorem failureDisjunction_closed
    (left right : ValuationFormula)
    (hleft : left.freeVariables = ∅)
    (hright : right.freeVariables = ∅) :
    (left ⋎ right).freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_or, hleft, hright]
  simp

theorem failureInnerDisjunction_code_le
    (left right : ValuationFormula) (bitBound : Nat)
    (hleft : (binaryFormulaCode left).length <=
      termOutputFailureAtomFormulaCodePolynomial bitBound)
    (hright : (binaryFormulaCode right).length <=
      termOutputFailureAtomFormulaCodePolynomial bitBound) :
    (binaryFormulaCode (left ⋎ right)).length <=
      termOutputFailureInnerFormulaCodePolynomial bitBound := by
  simp only [binaryFormulaCode, List.length_append] at hleft hright ⊢
  unfold termOutputFailureInnerFormulaCodePolynomial
  omega

theorem failureOuterDisjunction_code_le
    (left right : ValuationFormula) (bitBound : Nat)
    (hleft : (binaryFormulaCode left).length <=
      termOutputFailureAtomFormulaCodePolynomial bitBound)
    (hright : (binaryFormulaCode right).length <=
      termOutputFailureInnerFormulaCodePolynomial bitBound) :
    (binaryFormulaCode (left ⋎ right)).length <=
      termOutputFailureFormulaCodePolynomial bitBound := by
  simp only [binaryFormulaCode, List.length_append] at hleft hright ⊢
  unfold termOutputFailureFormulaCodePolynomial
  omega

theorem failureDisjunctionPathLeft_le_fixed
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (childResource bitBound : Nat)
    (hclosed : (left ⋎ right).freeVariables = ∅)
    (hleft : (binaryFormulaCode left).length <=
      termOutputFailureFormulaCodePolynomial bitBound)
    (hright : (binaryFormulaCode right).length <=
      termOutputFailureFormulaCodePolynomial bitBound)
    (hformula : (binaryFormulaCode (left ⋎ right)).length <=
      termOutputFailureFormulaCodePolynomial bitBound)
    (hchild : childResource <=
      termOutputFailureAtomicPayloadPolynomial bitBound) :
    transparentHybridDisjunctionLeftPayloadEnvelope valuation left right
        childResource <=
      termOutputFailurePathPayloadPolynomial bitBound := by
  have hcontext : formulaCodeSum
      (valuationContext (left ⋎ right).freeVariables valuation) <=
        termOutputFailureFormulaCodePolynomial bitBound := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  have hraw := transparentHybridDisjunctionLeftPayloadEnvelope_le_general
    valuation left right childResource
    (termOutputFailureFormulaCodePolynomial bitBound)
    (by unfold termOutputFailureFormulaCodePolynomial; omega)
    hcontext hleft hright hformula
  unfold termOutputFailurePathPayloadPolynomial
    hybridDisjunctionGeneralPayloadEnvelope at hraw ⊢
  omega

theorem failureDisjunctionPathRight_le_fixed
    (valuation : Nat -> Nat) (left right : ValuationFormula)
    (childResource bitBound : Nat)
    (hclosed : (left ⋎ right).freeVariables = ∅)
    (hleft : (binaryFormulaCode left).length <=
      termOutputFailureFormulaCodePolynomial bitBound)
    (hright : (binaryFormulaCode right).length <=
      termOutputFailureFormulaCodePolynomial bitBound)
    (hformula : (binaryFormulaCode (left ⋎ right)).length <=
      termOutputFailureFormulaCodePolynomial bitBound)
    (hchild : childResource <=
      termOutputFailureAtomicPayloadPolynomial bitBound) :
    transparentHybridDisjunctionRightPayloadEnvelope valuation left right
        childResource <=
      termOutputFailurePathPayloadPolynomial bitBound := by
  have hcontext : formulaCodeSum
      (valuationContext (left ⋎ right).freeVariables valuation) <=
        termOutputFailureFormulaCodePolynomial bitBound := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  have hraw := transparentHybridDisjunctionRightPayloadEnvelope_le_general
    valuation left right childResource
    (termOutputFailureFormulaCodePolynomial bitBound)
    (by unfold termOutputFailureFormulaCodePolynomial; omega)
    hcontext hleft hright hformula
  unfold termOutputFailurePathPayloadPolynomial
    hybridDisjunctionGeneralPayloadEnvelope at hraw ⊢
  omega

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsFailureFixedBounds
