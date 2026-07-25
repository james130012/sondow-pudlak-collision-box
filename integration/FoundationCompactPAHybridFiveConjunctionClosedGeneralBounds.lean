import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Closed general-context bound for five right-associated conjunction leaves

The code and closedness obligations for every leaf and tail are recovered from
the actual full conjunction.  Four checked conjunction assemblies are then
bounded without introducing a context-cardinality parameter.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds

private theorem binaryFormulaCode_and_left_le_five
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem binaryFormulaCode_and_right_le_five
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem conjunction_left_closed_of_closed_five
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    left.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).1

private theorem conjunction_right_closed_of_closed_five
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    right.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).2

def hybridFiveConjunctionGeneralPayloadEnvelope
    (syntaxResource resource1 resource2 resource3 resource4 resource5 : Nat) :
    Nat :=
  hybridConjunctionGeneralPayloadEnvelope syntaxResource resource1
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource4
          resource5)))

theorem transparentHybridFiveConjunctionPayloadEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (formula1 formula2 formula3 formula4 formula5 : ValuationFormula)
    (resource1 resource2 resource3 resource4 resource5 syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed :
      (formula1 ⋏
        (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5)))).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode
        (formula1 ⋏
          (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5))))).length <=
        syntaxResource) :
    transparentHybridConjunctionPayloadEnvelope valuation formula1
        (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5))) resource1
        (transparentHybridConjunctionPayloadEnvelope valuation formula2
          (formula3 ⋏ (formula4 ⋏ formula5)) resource2
          (transparentHybridConjunctionPayloadEnvelope valuation formula3
            (formula4 ⋏ formula5) resource3
            (transparentHybridConjunctionPayloadEnvelope valuation formula4
              formula5 resource4 resource5))) <=
      hybridFiveConjunctionGeneralPayloadEnvelope syntaxResource resource1
        resource2 resource3 resource4 resource5 := by
  let tail4 := formula4 ⋏ formula5
  let tail3 := formula3 ⋏ tail4
  let tail2 := formula2 ⋏ tail3
  let total := formula1 ⋏ tail2
  have htotalClosed : total.freeVariables = ∅ := by
    simpa only [total, tail2, tail3, tail4] using hclosed
  have hformula1Closed : formula1.freeVariables = ∅ :=
    conjunction_left_closed_of_closed_five formula1 tail2 htotalClosed
  have htail2Closed : tail2.freeVariables = ∅ :=
    conjunction_right_closed_of_closed_five formula1 tail2 htotalClosed
  have hformula2Closed : formula2.freeVariables = ∅ :=
    conjunction_left_closed_of_closed_five formula2 tail3 htail2Closed
  have htail3Closed : tail3.freeVariables = ∅ :=
    conjunction_right_closed_of_closed_five formula2 tail3 htail2Closed
  have hformula3Closed : formula3.freeVariables = ∅ :=
    conjunction_left_closed_of_closed_five formula3 tail4 htail3Closed
  have htail4Closed : tail4.freeVariables = ∅ :=
    conjunction_right_closed_of_closed_five formula3 tail4 htail3Closed
  have hformula4Closed : formula4.freeVariables = ∅ :=
    conjunction_left_closed_of_closed_five formula4 formula5 htail4Closed
  have hformula5Closed : formula5.freeVariables = ∅ :=
    conjunction_right_closed_of_closed_five formula4 formula5 htail4Closed
  have htotalCode : (binaryFormulaCode total).length <= syntaxResource := by
    simpa only [total, tail2, tail3, tail4] using hcode
  have htail2Code : (binaryFormulaCode tail2).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_five formula1 tail2).trans htotalCode
  have htail3Code : (binaryFormulaCode tail3).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_five formula2 tail3).trans htail2Code
  have htail4Code : (binaryFormulaCode tail4).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_five formula3 tail4).trans htail3Code
  have hformula1Code :
      (binaryFormulaCode formula1).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_five formula1 tail2).trans htotalCode
  have hformula2Code :
      (binaryFormulaCode formula2).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_five formula2 tail3).trans htail2Code
  have hformula3Code :
      (binaryFormulaCode formula3).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_five formula3 tail4).trans htail3Code
  have hformula4Code :
      (binaryFormulaCode formula4).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_five formula4 formula5).trans htail4Code
  have hformula5Code :
      (binaryFormulaCode formula5).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_five formula4 formula5).trans htail4Code
  have h4 := transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    valuation formula4 formula5 resource4 resource5 syntaxResource hpositive
    hformula4Closed hformula5Closed hformula4Code hformula5Code htail4Code
  have h3 := transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    valuation formula3 tail4 resource3
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource4
        resource5)
      syntaxResource hpositive hformula3Closed htail4Closed hformula3Code
      htail4Code htail3Code
  have h3mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula3 tail4 (leftSmall := resource3) (leftLarge := resource3) le_rfl h4
  have h2 := transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    valuation formula2 tail3 resource2
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource4
          resource5))
      syntaxResource hpositive hformula2Closed htail3Closed hformula2Code
      htail3Code htail2Code
  have h2mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula2 tail3 (leftSmall := resource2) (leftLarge := resource2) le_rfl
    (h3mono.trans h3)
  have h1 := transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    valuation formula1 tail2 resource1
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3
          (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource4
            resource5)))
      syntaxResource hpositive hformula1Closed htail2Closed hformula1Code
      htail2Code htotalCode
  have h1mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula1 tail2 (leftSmall := resource1) (leftLarge := resource1) le_rfl
    (h2mono.trans h2)
  unfold hybridFiveConjunctionGeneralPayloadEnvelope
  simpa only [tail2, tail3, tail4] using h1mono.trans h1

#print axioms transparentHybridFiveConjunctionPayloadEnvelope_le_closedGeneral

end FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds
