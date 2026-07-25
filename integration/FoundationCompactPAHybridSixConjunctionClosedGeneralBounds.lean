import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Closed general-context bound for six right-associated conjunction leaves

This packages five applications of the checked binary conjunction assembly
bound.  Formula-code bounds for every leaf and tail are derived from the code
of the actual right-associated conjunction.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactPAHybridSixConjunctionClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds

private theorem binaryFormulaCode_and_left_le_six
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem binaryFormulaCode_and_right_le_six
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

def hybridSixConjunctionGeneralPayloadEnvelope
    (syntaxResource resource1 resource2 resource3 resource4 resource5
      resource6 : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope syntaxResource resource1
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource4
          (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource5
            resource6))))

theorem transparentHybridSixConjunctionPayloadEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (formula1 formula2 formula3 formula4 formula5 formula6 :
      ValuationFormula)
    (resource1 resource2 resource3 resource4 resource5 resource6
      syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed1 : formula1.freeVariables = ∅)
    (hclosed2 : formula2.freeVariables = ∅)
    (hclosed3 : formula3.freeVariables = ∅)
    (hclosed4 : formula4.freeVariables = ∅)
    (hclosed5 : formula5.freeVariables = ∅)
    (hclosed6 : formula6.freeVariables = ∅)
    (hcode :
      (binaryFormulaCode
        (formula1 ⋏
          (formula2 ⋏
            (formula3 ⋏ (formula4 ⋏ (formula5 ⋏ formula6)))))).length <=
        syntaxResource) :
    transparentHybridConjunctionPayloadEnvelope valuation formula1
        (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ (formula5 ⋏ formula6))))
        resource1
        (transparentHybridConjunctionPayloadEnvelope valuation formula2
          (formula3 ⋏ (formula4 ⋏ (formula5 ⋏ formula6))) resource2
          (transparentHybridConjunctionPayloadEnvelope valuation formula3
            (formula4 ⋏ (formula5 ⋏ formula6)) resource3
            (transparentHybridConjunctionPayloadEnvelope valuation formula4
              (formula5 ⋏ formula6) resource4
              (transparentHybridConjunctionPayloadEnvelope valuation formula5
                formula6 resource5 resource6)))) <=
      hybridSixConjunctionGeneralPayloadEnvelope syntaxResource resource1
        resource2 resource3 resource4 resource5 resource6 := by
  let tail5 := formula5 ⋏ formula6
  let tail4 := formula4 ⋏ tail5
  let tail3 := formula3 ⋏ tail4
  let tail2 := formula2 ⋏ tail3
  let total := formula1 ⋏ tail2
  have htail2Code :
      (binaryFormulaCode tail2).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_six formula1 tail2).trans (by
      simpa only [total, tail2, tail3, tail4, tail5] using hcode)
  have htail3Code :
      (binaryFormulaCode tail3).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_six formula2 tail3).trans htail2Code
  have htail4Code :
      (binaryFormulaCode tail4).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_six formula3 tail4).trans htail3Code
  have htail5Code :
      (binaryFormulaCode tail5).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_six formula4 tail5).trans htail4Code
  have hformula1Code :
      (binaryFormulaCode formula1).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_six formula1 tail2).trans (by
      simpa only [total, tail2, tail3, tail4, tail5] using hcode)
  have hformula2Code :
      (binaryFormulaCode formula2).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_six formula2 tail3).trans htail2Code
  have hformula3Code :
      (binaryFormulaCode formula3).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_six formula3 tail4).trans htail3Code
  have hformula4Code :
      (binaryFormulaCode formula4).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_six formula4 tail5).trans htail4Code
  have hformula5Code :
      (binaryFormulaCode formula5).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_six formula5 formula6).trans htail5Code
  have hformula6Code :
      (binaryFormulaCode formula6).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_six formula5 formula6).trans htail5Code
  have htail5Closed : tail5.freeVariables = ∅ := by
    dsimp only [tail5]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hclosed5, hclosed6]
    simp
  have htail4Closed : tail4.freeVariables = ∅ := by
    dsimp only [tail4]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hclosed4, htail5Closed]
    simp
  have htail3Closed : tail3.freeVariables = ∅ := by
    dsimp only [tail3]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hclosed3, htail4Closed]
    simp
  have htail2Closed : tail2.freeVariables = ∅ := by
    dsimp only [tail2]
    rw [LO.FirstOrder.Semiformula.freeVariables_and, hclosed2, htail3Closed]
    simp
  have h5 := transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    valuation formula5 formula6 resource5 resource6 syntaxResource hpositive
    hclosed5 hclosed6 hformula5Code hformula6Code htail5Code
  have h4 := transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    valuation formula4 tail5 resource4
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource5
        resource6)
      syntaxResource hpositive hclosed4 htail5Closed hformula4Code htail5Code
      htail4Code
  have h4mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula4 tail5 (leftSmall := resource4) (leftLarge := resource4)
    le_rfl h5
  have h3 := transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    valuation formula3 tail4 resource3
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource4
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource5
          resource6))
      syntaxResource hpositive hclosed3 htail4Closed hformula3Code htail4Code
      htail3Code
  have h3mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula3 tail4 (leftSmall := resource3) (leftLarge := resource3)
    le_rfl (h4mono.trans h4)
  have h2 := transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    valuation formula2 tail3 resource2
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource4
          (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource5
            resource6)))
      syntaxResource hpositive hclosed2 htail3Closed hformula2Code htail3Code
      htail2Code
  have h2mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula2 tail3 (leftSmall := resource2) (leftLarge := resource2)
    le_rfl (h3mono.trans h3)
  have h1 := transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    valuation formula1 tail2 resource1
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3
          (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource4
            (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource5
              resource6))))
      syntaxResource hpositive hclosed1 htail2Closed hformula1Code htail2Code
      (by simpa only [total, tail2, tail3, tail4, tail5] using hcode)
  have h1mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula1 tail2 (leftSmall := resource1) (leftLarge := resource1)
    le_rfl (h2mono.trans h2)
  unfold hybridSixConjunctionGeneralPayloadEnvelope
  simpa only [tail2, tail3, tail4, tail5] using h1mono.trans h1

#print axioms
  transparentHybridSixConjunctionPayloadEnvelope_le_closedGeneral

end FoundationCompactPAHybridSixConjunctionClosedGeneralBounds
