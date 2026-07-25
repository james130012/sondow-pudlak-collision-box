import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds

/-!
# Closed general bounds for selected hybrid connectives

These wrappers compose the transparent certificate bound with the general
closed-formula assembly bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false

namespace FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds

theorem checkedHybridConjunctionPayloadBound_le_closedGeneral
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (leftCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation left)
    (rightCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation right)
    (leftResource rightResource syntaxResource : Nat)
    (hleftResource :
      hybridFormulaStructuralPayloadBound leftCertificate <= leftResource)
    (hrightResource :
      hybridFormulaStructuralPayloadBound rightCertificate <= rightResource)
    (hpositive : 1 <= syntaxResource)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryFormulaCode left).length <= syntaxResource)
    (hrightCode : (binaryFormulaCode right).length <= syntaxResource)
    (hfullCode :
      (binaryFormulaCode (left ⋏ right)).length <= syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          leftCertificate rightCertificate) <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
        rightResource :=
  (transparentHybridConjunctionPayloadBound_le leftCertificate
      rightCertificate leftResource rightResource hleftResource
      hrightResource).trans
    (transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      left right leftResource rightResource syntaxResource hpositive
      hleftClosed hrightClosed hleftCode hrightCode hfullCode)

theorem checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (leftCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation left)
    (childResource syntaxResource : Nat)
    (hchild :
      hybridFormulaStructuralPayloadBound leftCertificate <= childResource)
    (hpositive : 1 <= syntaxResource)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryFormulaCode left).length <= syntaxResource)
    (hrightCode : (binaryFormulaCode right).length <= syntaxResource)
    (hfullCode :
      (binaryFormulaCode (left ⋎ right)).length <= syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := right) leftCertificate) <=
      hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource := by
  have hclosed : (left ⋎ right).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hleftClosed, hrightClosed]
    simp
  have hcontext :
      formulaCodeSum
          (valuationContext (left ⋎ right).freeVariables valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  exact
    (transparentHybridDisjunctionLeftPayloadBound_le leftCertificate
      childResource hchild).trans
    (transparentHybridDisjunctionLeftPayloadEnvelope_le_general valuation left
      right childResource syntaxResource hpositive hcontext hleftCode
      hrightCode hfullCode)

theorem checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (rightCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation right)
    (childResource syntaxResource : Nat)
    (hchild :
      hybridFormulaStructuralPayloadBound rightCertificate <= childResource)
    (hpositive : 1 <= syntaxResource)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryFormulaCode left).length <= syntaxResource)
    (hrightCode : (binaryFormulaCode right).length <= syntaxResource)
    (hfullCode :
      (binaryFormulaCode (left ⋎ right)).length <= syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := left) rightCertificate) <=
      hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource := by
  have hclosed : (left ⋎ right).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_or, hleftClosed, hrightClosed]
    simp
  have hcontext :
      formulaCodeSum
          (valuationContext (left ⋎ right).freeVariables valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  exact
    (transparentHybridDisjunctionRightPayloadBound_le rightCertificate
      childResource hchild).trans
    (transparentHybridDisjunctionRightPayloadEnvelope_le_general valuation
      left right childResource syntaxResource hpositive hcontext hleftCode
      hrightCode hfullCode)

#print axioms checkedHybridConjunctionPayloadBound_le_closedGeneral
#print axioms checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
#print axioms checkedHybridDisjunctionRightPayloadBound_le_closedGeneral

end FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
