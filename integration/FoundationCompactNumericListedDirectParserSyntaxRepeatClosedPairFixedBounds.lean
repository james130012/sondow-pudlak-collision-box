import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Closed conjunction bound derived directly from two certificate resources -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactCertifiedContextProofConclusionCodeBounds

def repeatClosedPairSyntaxResource
    (leftResource rightResource : Nat) : Nat :=
  leftResource + rightResource + (binaryNatCode 4).length + 1

theorem closedPairCertificate_structuralPayloadBound_le_fixed
    (valuation : Nat -> Nat)
    (left right : ValuationFormula)
    (leftCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation left)
    (rightCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation right)
    (leftResource rightResource : Nat)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleft :
      hybridFormulaStructuralPayloadBound leftCertificate <= leftResource)
    (hright :
      hybridFormulaStructuralPayloadBound rightCertificate <= rightResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          leftCertificate rightCertificate) <=
      hybridConjunctionGeneralPayloadEnvelope
        (repeatClosedPairSyntaxResource leftResource rightResource)
        leftResource rightResource := by
  let syntaxResource :=
    repeatClosedPairSyntaxResource leftResource rightResource
  have hleftCodeResource :
      (binaryFormulaCode left).length <= leftResource :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      leftCertificate |>.trans hleft
  have hrightCodeResource :
      (binaryFormulaCode right).length <= rightResource :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      rightCertificate |>.trans hright
  have hleftCode :
      (binaryFormulaCode left).length <= syntaxResource :=
    hleftCodeResource.trans (by
      unfold syntaxResource repeatClosedPairSyntaxResource
      omega)
  have hrightCode :
      (binaryFormulaCode right).length <= syntaxResource :=
    hrightCodeResource.trans (by
      unfold syntaxResource repeatClosedPairSyntaxResource
      omega)
  have htotalCode :
      (binaryFormulaCode (left ⋏ right)).length <= syntaxResource := by
    simp only [binaryFormulaCode, List.length_append]
    unfold syntaxResource repeatClosedPairSyntaxResource
    omega
  have htransparent :=
    transparentHybridConjunctionPayloadBound_le leftCertificate
      rightCertificate leftResource rightResource hleft hright
  have hclosed :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      left right leftResource rightResource syntaxResource
      (by
        unfold syntaxResource repeatClosedPairSyntaxResource
        omega)
      hleftClosed hrightClosed hleftCode hrightCode htotalCode
  exact htransparent.trans hclosed

end FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds
