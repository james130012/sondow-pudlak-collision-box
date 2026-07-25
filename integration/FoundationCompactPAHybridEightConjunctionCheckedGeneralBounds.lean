import integration.FoundationCompactPAHybridSixConjunctionClosedGeneralBounds

/-!
# Checked general-context bound for eight conjunction leaves

The theorem composes the actual checked certificates.  The final three leaves
are first assembled as a closed tail; that tail is then the sixth input of the
existing six-leaf right-associated conjunction theorem.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactPAHybridEightConjunctionCheckedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridSixConjunctionClosedGeneralBounds

private theorem binaryFormulaCode_and_left_le_eight
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem binaryFormulaCode_and_right_le_eight
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

def hybridEightConjunctionCheckedGeneralPayloadEnvelope
    (syntaxResource resource1 resource2 resource3 resource4 resource5
      resource6 resource7 resource8 : Nat) : Nat :=
  hybridSixConjunctionGeneralPayloadEnvelope syntaxResource resource1
    resource2 resource3 resource4 resource5
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource6
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource7
        resource8))

theorem checkedHybridEightConjunctionPayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    {formula1 formula2 formula3 formula4 formula5 formula6 formula7 formula8 :
      ValuationFormula}
    (certificate1 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula1)
    (certificate2 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula2)
    (certificate3 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula3)
    (certificate4 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula4)
    (certificate5 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula5)
    (certificate6 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula6)
    (certificate7 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula7)
    (certificate8 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula8)
    (resource1 resource2 resource3 resource4 resource5 resource6 resource7
      resource8 syntaxResource : Nat)
    (hresource1 :
      hybridFormulaStructuralPayloadBound certificate1 <= resource1)
    (hresource2 :
      hybridFormulaStructuralPayloadBound certificate2 <= resource2)
    (hresource3 :
      hybridFormulaStructuralPayloadBound certificate3 <= resource3)
    (hresource4 :
      hybridFormulaStructuralPayloadBound certificate4 <= resource4)
    (hresource5 :
      hybridFormulaStructuralPayloadBound certificate5 <= resource5)
    (hresource6 :
      hybridFormulaStructuralPayloadBound certificate6 <= resource6)
    (hresource7 :
      hybridFormulaStructuralPayloadBound certificate7 <= resource7)
    (hresource8 :
      hybridFormulaStructuralPayloadBound certificate8 <= resource8)
    (hpositive : 1 <= syntaxResource)
    (hclosed1 : formula1.freeVariables = ∅)
    (hclosed2 : formula2.freeVariables = ∅)
    (hclosed3 : formula3.freeVariables = ∅)
    (hclosed4 : formula4.freeVariables = ∅)
    (hclosed5 : formula5.freeVariables = ∅)
    (hclosed6 : formula6.freeVariables = ∅)
    (hclosed7 : formula7.freeVariables = ∅)
    (hclosed8 : formula8.freeVariables = ∅)
    (hcode :
      (binaryFormulaCode
        (formula1 ⋏
          (formula2 ⋏
            (formula3 ⋏
              (formula4 ⋏
                (formula5 ⋏
                  (formula6 ⋏ (formula7 ⋏ formula8)))))))).length <=
        syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          certificate1
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            certificate2
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              certificate3
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                certificate4
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  certificate5
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    certificate6
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      certificate7 certificate8))))))) <=
      hybridEightConjunctionCheckedGeneralPayloadEnvelope syntaxResource
        resource1 resource2 resource3 resource4 resource5 resource6 resource7
        resource8 := by
  let formula78 := formula7 ⋏ formula8
  let formula678 := formula6 ⋏ formula78
  let formula5678 := formula5 ⋏ formula678
  let formula45678 := formula4 ⋏ formula5678
  let formula345678 := formula3 ⋏ formula45678
  let formula2345678 := formula2 ⋏ formula345678
  let total := formula1 ⋏ formula2345678
  have h2345678Code :
      (binaryFormulaCode formula2345678).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_eight formula1 formula2345678).trans (by
      simpa only [total, formula2345678, formula345678, formula45678,
        formula5678, formula678, formula78] using hcode)
  have h345678Code :
      (binaryFormulaCode formula345678).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_eight formula2 formula345678).trans
      h2345678Code
  have h45678Code :
      (binaryFormulaCode formula45678).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_eight formula3 formula45678).trans
      h345678Code
  have h5678Code :
      (binaryFormulaCode formula5678).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_eight formula4 formula5678).trans
      h45678Code
  have h678Code :
      (binaryFormulaCode formula678).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_eight formula5 formula678).trans
      h5678Code
  have h78Code :
      (binaryFormulaCode formula78).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_eight formula6 formula78).trans h678Code
  have h6Code :
      (binaryFormulaCode formula6).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_eight formula6 formula78).trans h678Code
  have h7Code :
      (binaryFormulaCode formula7).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_eight formula7 formula8).trans h78Code
  have h8Code :
      (binaryFormulaCode formula8).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_eight formula7 formula8).trans h78Code
  have h78Closed : formula78.freeVariables = ∅ := by
    dsimp only [formula78]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hclosed7, hclosed8]
    simp
  have h678Closed : formula678.freeVariables = ∅ := by
    dsimp only [formula678]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hclosed6, h78Closed]
    simp
  let certificate78 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate7
      certificate8
  have hcertificate78Transparent :=
    transparentHybridConjunctionPayloadBound_le certificate7 certificate8
      resource7 resource8 hresource7 hresource8
  have hcertificate78General :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula7 formula8 resource7 resource8 syntaxResource hpositive hclosed7
      hclosed8 h7Code h8Code h78Code
  have hcertificate78 :
      hybridFormulaStructuralPayloadBound certificate78 <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource resource7
          resource8 := by
    exact hcertificate78Transparent.trans hcertificate78General
  let tailResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource resource7 resource8
  let certificate678 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate6
      certificate78
  have hcertificate678Transparent :=
    transparentHybridConjunctionPayloadBound_le certificate6 certificate78
      resource6 tailResource hresource6 hcertificate78
  have hcertificate678General :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula6 formula78 resource6 tailResource syntaxResource hpositive
      hclosed6 h78Closed h6Code h78Code h678Code
  have hcertificate678 :
      hybridFormulaStructuralPayloadBound certificate678 <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource resource6
          tailResource := by
    exact hcertificate678Transparent.trans hcertificate678General
  let innerResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource resource6
      tailResource
  let certificate5678 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate5
      certificate678
  have hcertificate5678 :=
    transparentHybridConjunctionPayloadBound_le certificate5 certificate678
      resource5 innerResource hresource5 hcertificate678
  let certificate45678 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate4
      certificate5678
  have hcertificate45678 :=
    transparentHybridConjunctionPayloadBound_le certificate4 certificate5678
      resource4 _ hresource4 hcertificate5678
  let certificate345678 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate3
      certificate45678
  have hcertificate345678 :=
    transparentHybridConjunctionPayloadBound_le certificate3 certificate45678
      resource3 _ hresource3 hcertificate45678
  let certificate2345678 :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate2
      certificate345678
  have hcertificate2345678 :=
    transparentHybridConjunctionPayloadBound_le certificate2 certificate345678
      resource2 _ hresource2 hcertificate345678
  have htotalTransparent :=
    transparentHybridConjunctionPayloadBound_le certificate1
      certificate2345678 resource1 _ hresource1 hcertificate2345678
  have hsix :=
    transparentHybridSixConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula1 formula2 formula3 formula4 formula5 formula678 resource1
      resource2 resource3 resource4 resource5 innerResource syntaxResource
      hpositive hclosed1 hclosed2 hclosed3 hclosed4 hclosed5 h678Closed (by
        simpa only [total, formula2345678, formula345678, formula45678,
          formula5678, formula678, formula78] using hcode)
  unfold hybridEightConjunctionCheckedGeneralPayloadEnvelope
  simpa only [certificate78, certificate678, certificate5678,
    certificate45678, certificate345678, certificate2345678, formula78,
    formula678, formula5678, formula45678, formula345678, formula2345678,
    tailResource, innerResource] using htotalTransparent.trans hsix

#print axioms checkedHybridEightConjunctionPayloadBound_le_closedGeneral

end FoundationCompactPAHybridEightConjunctionCheckedGeneralBounds
