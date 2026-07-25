import integration.FoundationCompactPAHybridEightConjunctionCheckedGeneralBounds

/-! # Checked general-context bound for nine right-associated conjunction leaves -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactPAHybridNineConjunctionCheckedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridEightConjunctionCheckedGeneralBounds

def hybridNineConjunctionCheckedGeneralPayloadEnvelope
    (syntaxResource resource1 resource2 resource3 resource4 resource5
      resource6 resource7 resource8 resource9 : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope syntaxResource resource1
    (hybridEightConjunctionCheckedGeneralPayloadEnvelope syntaxResource
      resource2 resource3 resource4 resource5 resource6 resource7 resource8
      resource9)

theorem checkedHybridNineConjunctionPayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    {formula1 formula2 formula3 formula4 formula5 formula6 formula7 formula8
      formula9 : ValuationFormula}
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
    (certificate9 :
      CheckedHybridValuationBoundedFormulaCertificate valuation formula9)
    (resource1 resource2 resource3 resource4 resource5 resource6 resource7
      resource8 resource9 syntaxResource : Nat)
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
    (hresource9 :
      hybridFormulaStructuralPayloadBound certificate9 <= resource9)
    (hpositive : 1 <= syntaxResource)
    (hclosed1 : formula1.freeVariables = ∅)
    (hclosed2 : formula2.freeVariables = ∅)
    (hclosed3 : formula3.freeVariables = ∅)
    (hclosed4 : formula4.freeVariables = ∅)
    (hclosed5 : formula5.freeVariables = ∅)
    (hclosed6 : formula6.freeVariables = ∅)
    (hclosed7 : formula7.freeVariables = ∅)
    (hclosed8 : formula8.freeVariables = ∅)
    (hclosed9 : formula9.freeVariables = ∅)
    (hcode :
      (binaryFormulaCode
        (formula1 ⋏
          (formula2 ⋏
            (formula3 ⋏
              (formula4 ⋏
                (formula5 ⋏
                  (formula6 ⋏
                    (formula7 ⋏ (formula8 ⋏ formula9))))))))).length <=
        syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (.conjunction certificate1
          (.conjunction certificate2
            (.conjunction certificate3
              (.conjunction certificate4
                (.conjunction certificate5
                  (.conjunction certificate6
                    (.conjunction certificate7
                      (.conjunction certificate8 certificate9)))))))) <=
      hybridNineConjunctionCheckedGeneralPayloadEnvelope syntaxResource
        resource1 resource2 resource3 resource4 resource5 resource6 resource7
        resource8 resource9 := by
  let tailFormula :=
    formula2 ⋏
      (formula3 ⋏
        (formula4 ⋏
          (formula5 ⋏
            (formula6 ⋏ (formula7 ⋏ (formula8 ⋏ formula9))))))
  let tailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction certificate2
      (.conjunction certificate3
        (.conjunction certificate4
          (.conjunction certificate5
            (.conjunction certificate6
              (.conjunction certificate7
                (.conjunction certificate8 certificate9))))))
  let tailResource :=
    hybridEightConjunctionCheckedGeneralPayloadEnvelope syntaxResource
      resource2 resource3 resource4 resource5 resource6 resource7 resource8
      resource9
  have htailClosed : tailFormula.freeVariables = ∅ := by
    simp only [tailFormula, LO.FirstOrder.Semiformula.freeVariables_and,
      hclosed2, hclosed3, hclosed4, hclosed5, hclosed6, hclosed7, hclosed8,
      hclosed9]
    simp
  have htailCode :
      (binaryFormulaCode tailFormula).length <= syntaxResource := by
    dsimp only [tailFormula]
    have hraw := hcode
    simp only [binaryFormulaCode, List.length_append] at hraw ⊢
    omega
  have htail :
      hybridFormulaStructuralPayloadBound tailCertificate <= tailResource := by
    dsimp only [tailCertificate, tailResource, tailFormula]
    exact checkedHybridEightConjunctionPayloadBound_le_closedGeneral
      certificate2 certificate3 certificate4 certificate5 certificate6
      certificate7 certificate8 certificate9 resource2 resource3 resource4
      resource5 resource6 resource7 resource8 resource9 syntaxResource
      hresource2 hresource3 hresource4 hresource5 hresource6 hresource7
      hresource8 hresource9 hpositive hclosed2 hclosed3 hclosed4 hclosed5
      hclosed6 hclosed7 hclosed8 hclosed9 (by
        simpa only [tailFormula] using htailCode)
  have htransparent :=
    transparentHybridConjunctionPayloadBound_le certificate1 tailCertificate
      resource1 tailResource hresource1 htail
  have hformula1Code :
      (binaryFormulaCode formula1).length <= syntaxResource := by
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hassembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula1 tailFormula resource1 tailResource syntaxResource hpositive
      hclosed1 htailClosed hformula1Code htailCode (by
        simpa only [tailFormula] using hcode)
  unfold hybridNineConjunctionCheckedGeneralPayloadEnvelope
  exact htransparent.trans hassembly

#print axioms checkedHybridNineConjunctionPayloadBound_le_closedGeneral

end FoundationCompactPAHybridNineConjunctionCheckedGeneralBounds
