import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Closed general-context bound for four right-associated conjunction leaves

One code bound for the complete closed conjunction controls every leaf and
tail.  Three transparent conjunction assemblies are then charged to a fixed
general-context envelope.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactPAHybridFourConjunctionClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds

private theorem binaryFormulaCode_and_left_le_four
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem binaryFormulaCode_and_right_le_four
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem conjunction_left_closed_of_closed_four
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    left.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).1

private theorem conjunction_right_closed_of_closed_four
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    right.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).2

def hybridFourConjunctionGeneralPayloadEnvelope
    (syntaxResource resource1 resource2 resource3 resource4 : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope syntaxResource resource1
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3
        resource4))

theorem transparentHybridFourConjunctionPayloadEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (formula1 formula2 formula3 formula4 : ValuationFormula)
    (resource1 resource2 resource3 resource4 syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed :
      (formula1 ⋏ (formula2 ⋏ (formula3 ⋏ formula4))).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode
        (formula1 ⋏ (formula2 ⋏ (formula3 ⋏ formula4)))).length <=
        syntaxResource) :
    transparentHybridConjunctionPayloadEnvelope valuation formula1
        (formula2 ⋏ (formula3 ⋏ formula4)) resource1
        (transparentHybridConjunctionPayloadEnvelope valuation formula2
          (formula3 ⋏ formula4) resource2
          (transparentHybridConjunctionPayloadEnvelope valuation formula3
            formula4 resource3 resource4)) <=
      hybridFourConjunctionGeneralPayloadEnvelope syntaxResource resource1
        resource2 resource3 resource4 := by
  let tail3 := formula3 ⋏ formula4
  let tail2 := formula2 ⋏ tail3
  let total := formula1 ⋏ tail2
  have htotalClosed : total.freeVariables = ∅ := by
    simpa only [total, tail2, tail3] using hclosed
  have hformula1Closed : formula1.freeVariables = ∅ :=
    conjunction_left_closed_of_closed_four formula1 tail2 htotalClosed
  have htail2Closed : tail2.freeVariables = ∅ :=
    conjunction_right_closed_of_closed_four formula1 tail2 htotalClosed
  have hformula2Closed : formula2.freeVariables = ∅ :=
    conjunction_left_closed_of_closed_four formula2 tail3 htail2Closed
  have htail3Closed : tail3.freeVariables = ∅ :=
    conjunction_right_closed_of_closed_four formula2 tail3 htail2Closed
  have hformula3Closed : formula3.freeVariables = ∅ :=
    conjunction_left_closed_of_closed_four formula3 formula4 htail3Closed
  have hformula4Closed : formula4.freeVariables = ∅ :=
    conjunction_right_closed_of_closed_four formula3 formula4 htail3Closed
  have htotalCode : (binaryFormulaCode total).length <= syntaxResource := by
    simpa only [total, tail2, tail3] using hcode
  have htail2Code : (binaryFormulaCode tail2).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_four formula1 tail2).trans htotalCode
  have htail3Code : (binaryFormulaCode tail3).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_four formula2 tail3).trans htail2Code
  have hformula1Code :
      (binaryFormulaCode formula1).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_four formula1 tail2).trans htotalCode
  have hformula2Code :
      (binaryFormulaCode formula2).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_four formula2 tail3).trans htail2Code
  have hformula3Code :
      (binaryFormulaCode formula3).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_four formula3 formula4).trans htail3Code
  have hformula4Code :
      (binaryFormulaCode formula4).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_four formula3 formula4).trans htail3Code
  have h3 := transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    valuation formula3 formula4 resource3 resource4 syntaxResource hpositive
    hformula3Closed hformula4Closed hformula3Code hformula4Code htail3Code
  have h2 := transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    valuation formula2 tail3 resource2
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3
        resource4)
      syntaxResource hpositive hformula2Closed htail3Closed hformula2Code
      htail3Code htail2Code
  have h2mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula2 tail3 (leftSmall := resource2) (leftLarge := resource2) le_rfl h3
  have h1 := transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
    valuation formula1 tail2 resource1
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3
          resource4))
      syntaxResource hpositive hformula1Closed htail2Closed hformula1Code
      htail2Code htotalCode
  have h1mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula1 tail2 (leftSmall := resource1) (leftLarge := resource1) le_rfl
    (h2mono.trans h2)
  unfold hybridFourConjunctionGeneralPayloadEnvelope
  simpa only [tail2, tail3] using h1mono.trans h1

#print axioms transparentHybridFourConjunctionPayloadEnvelope_le_closedGeneral

end FoundationCompactPAHybridFourConjunctionClosedGeneralBounds
