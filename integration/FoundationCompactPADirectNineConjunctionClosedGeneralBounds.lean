import integration.FoundationCompactPADirectNineConjunctionCompiler
import integration.FoundationCompactPAHybridNineConjunctionCheckedGeneralBounds

/-! # Closed general-context bound for direct nine-leaf conjunctions -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactPADirectNineConjunctionClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridEightConjunctionCheckedGeneralBounds
open FoundationCompactPAHybridNineConjunctionCheckedGeneralBounds
open FoundationCompactPADirectNineConjunctionCompiler

def directNineConjunctionGeneralPayloadEnvelope
    (syntaxResource resource1 resource2 resource3 resource4 resource5
      resource6 resource7 resource8 resource9 : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope syntaxResource resource1
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource4
          (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource5
            (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource6
              (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource7
                (hybridConjunctionGeneralPayloadEnvelope syntaxResource
                  resource8 resource9)))))))

theorem compileDirectNineConjunction_payloadLength_le_closedGeneral
    {valuation : Nat -> Nat}
    {formula1 formula2 formula3 formula4 formula5 formula6 formula7 formula8
      formula9 : ValuationFormula}
    (proof1 : CertifiedPAContextProof
      (valuationContext formula1.freeVariables valuation) formula1)
    (proof2 : CertifiedPAContextProof
      (valuationContext formula2.freeVariables valuation) formula2)
    (proof3 : CertifiedPAContextProof
      (valuationContext formula3.freeVariables valuation) formula3)
    (proof4 : CertifiedPAContextProof
      (valuationContext formula4.freeVariables valuation) formula4)
    (proof5 : CertifiedPAContextProof
      (valuationContext formula5.freeVariables valuation) formula5)
    (proof6 : CertifiedPAContextProof
      (valuationContext formula6.freeVariables valuation) formula6)
    (proof7 : CertifiedPAContextProof
      (valuationContext formula7.freeVariables valuation) formula7)
    (proof8 : CertifiedPAContextProof
      (valuationContext formula8.freeVariables valuation) formula8)
    (proof9 : CertifiedPAContextProof
      (valuationContext formula9.freeVariables valuation) formula9)
    (resource1 resource2 resource3 resource4 resource5 resource6 resource7
      resource8 resource9 syntaxResource : Nat)
    (hresource1 : proof1.payloadLength <= resource1)
    (hresource2 : proof2.payloadLength <= resource2)
    (hresource3 : proof3.payloadLength <= resource3)
    (hresource4 : proof4.payloadLength <= resource4)
    (hresource5 : proof5.payloadLength <= resource5)
    (hresource6 : proof6.payloadLength <= resource6)
    (hresource7 : proof7.payloadLength <= resource7)
    (hresource8 : proof8.payloadLength <= resource8)
    (hresource9 : proof9.payloadLength <= resource9)
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
    (compileDirectNineConjunction proof1 proof2 proof3 proof4 proof5 proof6
      proof7 proof8 proof9).payloadLength <=
      directNineConjunctionGeneralPayloadEnvelope syntaxResource resource1
        resource2 resource3 resource4 resource5 resource6 resource7 resource8
        resource9 := by
  let formula89 := formula8 ⋏ formula9
  let formula789 := formula7 ⋏ formula89
  let formula6789 := formula6 ⋏ formula789
  let formula56789 := formula5 ⋏ formula6789
  let formula456789 := formula4 ⋏ formula56789
  let formula3456789 := formula3 ⋏ formula456789
  let formula23456789 := formula2 ⋏ formula3456789
  let resource89 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    resource8 resource9
  let resource789 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    resource7 resource89
  let resource6789 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    resource6 resource789
  let resource56789 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    resource5 resource6789
  let resource456789 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    resource4 resource56789
  let resource3456789 := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    resource3 resource456789
  let resource23456789 := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource resource2 resource3456789
  have hclosed89 : formula89.freeVariables = ∅ := by
    simp [formula89, hclosed8, hclosed9]
  have hclosed789 : formula789.freeVariables = ∅ := by
    simp [formula789, hclosed7, hclosed89]
  have hclosed6789 : formula6789.freeVariables = ∅ := by
    simp [formula6789, hclosed6, hclosed789]
  have hclosed56789 : formula56789.freeVariables = ∅ := by
    simp [formula56789, hclosed5, hclosed6789]
  have hclosed456789 : formula456789.freeVariables = ∅ := by
    simp [formula456789, hclosed4, hclosed56789]
  have hclosed3456789 : formula3456789.freeVariables = ∅ := by
    simp [formula3456789, hclosed3, hclosed456789]
  have hclosed23456789 : formula23456789.freeVariables = ∅ := by
    simp [formula23456789, hclosed2, hclosed3456789]
  have hcode1 : (binaryFormulaCode formula1).length <= syntaxResource := by
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode2 : (binaryFormulaCode formula2).length <= syntaxResource := by
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode3 : (binaryFormulaCode formula3).length <= syntaxResource := by
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode4 : (binaryFormulaCode formula4).length <= syntaxResource := by
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode5 : (binaryFormulaCode formula5).length <= syntaxResource := by
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode6 : (binaryFormulaCode formula6).length <= syntaxResource := by
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode7 : (binaryFormulaCode formula7).length <= syntaxResource := by
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode8 : (binaryFormulaCode formula8).length <= syntaxResource := by
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode9 : (binaryFormulaCode formula9).length <= syntaxResource := by
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode89 : (binaryFormulaCode formula89).length <= syntaxResource := by
    dsimp only [formula89]
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode789 : (binaryFormulaCode formula789).length <= syntaxResource := by
    dsimp only [formula789, formula89]
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode6789 :
      (binaryFormulaCode formula6789).length <= syntaxResource := by
    dsimp only [formula6789, formula789, formula89]
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode56789 :
      (binaryFormulaCode formula56789).length <= syntaxResource := by
    dsimp only [formula56789, formula6789, formula789, formula89]
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode456789 :
      (binaryFormulaCode formula456789).length <= syntaxResource := by
    dsimp only [formula456789, formula56789, formula6789, formula789,
      formula89]
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode3456789 :
      (binaryFormulaCode formula3456789).length <= syntaxResource := by
    dsimp only [formula3456789, formula456789, formula56789, formula6789,
      formula789, formula89]
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have hcode23456789 :
      (binaryFormulaCode formula23456789).length <= syntaxResource := by
    dsimp only [formula23456789, formula3456789, formula456789, formula56789,
      formula6789, formula789, formula89]
    simp only [binaryFormulaCode, List.length_append] at hcode ⊢
    omega
  have htransparent :=
    compileDirectNineConjunction_payloadLength_le_transparent proof1 proof2
      proof3 proof4 proof5 proof6 proof7 proof8 proof9 resource1 resource2
      resource3 resource4 resource5 resource6 resource7 resource8 resource9
      hresource1 hresource2 hresource3 hresource4 hresource5 hresource6
      hresource7 hresource8 hresource9
  have h89 :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula8 formula9 resource8 resource9 syntaxResource hpositive hclosed8
      hclosed9 hcode8 hcode9 hcode89
  have h789Mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula7 formula89 (leftSmall := resource7) (leftLarge := resource7)
    le_rfl h89
  have h789General :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula7 formula89 resource7 resource89 syntaxResource hpositive
      hclosed7 hclosed89 hcode7 hcode89 hcode789
  have h789 := h789Mono.trans h789General
  have h6789Mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula6 formula789 (leftSmall := resource6) (leftLarge := resource6)
    le_rfl h789
  have h6789General :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula6 formula789 resource6 resource789 syntaxResource hpositive
      hclosed6 hclosed789 hcode6 hcode789 hcode6789
  have h6789 := h6789Mono.trans h6789General
  have h56789Mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula5 formula6789 (leftSmall := resource5) (leftLarge := resource5)
    le_rfl h6789
  have h56789General :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula5 formula6789 resource5 resource6789 syntaxResource hpositive
      hclosed5 hclosed6789 hcode5 hcode6789 hcode56789
  have h56789 := h56789Mono.trans h56789General
  have h456789Mono :=
    transparentHybridConjunctionPayloadEnvelope_mono valuation formula4
      formula56789 (leftSmall := resource4) (leftLarge := resource4)
      le_rfl h56789
  have h456789General :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula4 formula56789 resource4 resource56789 syntaxResource hpositive
      hclosed4 hclosed56789 hcode4 hcode56789 hcode456789
  have h456789 := h456789Mono.trans h456789General
  have h3456789Mono :=
    transparentHybridConjunctionPayloadEnvelope_mono valuation formula3
      formula456789 (leftSmall := resource3) (leftLarge := resource3)
      le_rfl h456789
  have h3456789General :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula3 formula456789 resource3 resource456789 syntaxResource hpositive
      hclosed3 hclosed456789 hcode3 hcode456789 hcode3456789
  have h3456789 := h3456789Mono.trans h3456789General
  have h23456789Mono :=
    transparentHybridConjunctionPayloadEnvelope_mono valuation formula2
      formula3456789 (leftSmall := resource2) (leftLarge := resource2)
      le_rfl h3456789
  have h23456789General :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula2 formula3456789 resource2 resource3456789 syntaxResource
      hpositive hclosed2 hclosed3456789 hcode2 hcode3456789 hcode23456789
  have h23456789 := h23456789Mono.trans h23456789General
  have htotalMono :=
    transparentHybridConjunctionPayloadEnvelope_mono valuation formula1
      formula23456789 (leftSmall := resource1) (leftLarge := resource1)
      le_rfl h23456789
  have htotalGeneral :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula1 formula23456789 resource1 resource23456789 syntaxResource
      hpositive hclosed1 hclosed23456789 hcode1 hcode23456789 hcode
  have htotal := htotalMono.trans htotalGeneral
  exact htransparent.trans (by
    simpa only [directNineConjunctionTransparentPayloadEnvelope,
      directNineConjunctionGeneralPayloadEnvelope, formula89, formula789,
      formula6789, formula56789, formula456789, formula3456789,
      formula23456789, resource89, resource789, resource6789, resource56789,
      resource456789, resource3456789, resource23456789] using htotal)

#print axioms compileDirectNineConjunction_payloadLength_le_closedGeneral

end FoundationCompactPADirectNineConjunctionClosedGeneralBounds
