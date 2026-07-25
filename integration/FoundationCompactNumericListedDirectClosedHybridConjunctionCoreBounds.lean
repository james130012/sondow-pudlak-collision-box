import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Closed hybrid conjunction core

This composes the transparent certificate-resource bound with the closed
general syntax envelope in one compiled theorem.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectClosedHybridConjunctionCoreBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds

theorem closedHybridConjunction_structuralPayloadBound_le_general
    {valuation : Nat -> Nat} {left right : ValuationFormula}
    (leftCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation left)
    (rightCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation right)
    (leftResource rightResource syntaxResource : Nat)
    (hleft :
      hybridFormulaStructuralPayloadBound leftCertificate <= leftResource)
    (hright :
      hybridFormulaStructuralPayloadBound rightCertificate <= rightResource)
    (hpositive : 1 <= syntaxResource)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryFormulaCode left).length <= syntaxResource)
    (hrightCode : (binaryFormulaCode right).length <= syntaxResource)
    (hconjunctionCode :
      (binaryFormulaCode (left ⋏ right)).length <= syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          leftCertificate rightCertificate) <=
      hybridConjunctionGeneralPayloadEnvelope syntaxResource leftResource
        rightResource := by
  have htransparent :=
    transparentHybridConjunctionPayloadBound_le leftCertificate
      rightCertificate leftResource rightResource hleft hright
  have hgeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      left right leftResource rightResource syntaxResource hpositive
      hleftClosed hrightClosed hleftCode hrightCode hconjunctionCode
  exact htransparent.trans hgeneral

#print axioms closedHybridConjunction_structuralPayloadBound_le_general

end FoundationCompactNumericListedDirectClosedHybridConjunctionCoreBounds
