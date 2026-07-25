import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-!
# Closed general-context bound for three right-associated conjunction leaves

One code bound for the complete closed conjunction controls both leaves and
the inner tail.  The theorem then pays exactly two checked conjunction
assemblies.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds

private theorem binaryFormulaCode_and_left_le_three
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem binaryFormulaCode_and_right_le_three
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem conjunction_left_closed_of_closed_three
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    left.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).1

private theorem conjunction_right_closed_of_closed_three
    (left right : ValuationFormula)
    (hclosed : (left ⋏ right).freeVariables = ∅) :
    right.freeVariables = ∅ := by
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
  exact (Finset.union_eq_empty.mp hclosed).2

def hybridThreeConjunctionGeneralPayloadEnvelope
    (syntaxResource resource1 resource2 resource3 : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope syntaxResource resource1
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2
      resource3)

theorem transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (formula1 formula2 formula3 : ValuationFormula)
    (resource1 resource2 resource3 syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (formula1 ⋏ (formula2 ⋏ formula3)).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
        syntaxResource) :
    transparentHybridConjunctionPayloadEnvelope valuation formula1
        (formula2 ⋏ formula3) resource1
        (transparentHybridConjunctionPayloadEnvelope valuation formula2
          formula3 resource2 resource3) <=
      hybridThreeConjunctionGeneralPayloadEnvelope syntaxResource resource1
        resource2 resource3 := by
  let tail := formula2 ⋏ formula3
  let total := formula1 ⋏ tail
  have htotalClosed : total.freeVariables = ∅ := by
    simpa only [total, tail] using hclosed
  have hformula1Closed : formula1.freeVariables = ∅ :=
    conjunction_left_closed_of_closed_three formula1 tail htotalClosed
  have htailClosed : tail.freeVariables = ∅ :=
    conjunction_right_closed_of_closed_three formula1 tail htotalClosed
  have hformula2Closed : formula2.freeVariables = ∅ :=
    conjunction_left_closed_of_closed_three formula2 formula3 htailClosed
  have hformula3Closed : formula3.freeVariables = ∅ :=
    conjunction_right_closed_of_closed_three formula2 formula3 htailClosed
  have htotalCode : (binaryFormulaCode total).length <= syntaxResource := by
    simpa only [total, tail] using hcode
  have htailCode : (binaryFormulaCode tail).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_three formula1 tail).trans htotalCode
  have hformula1Code :
      (binaryFormulaCode formula1).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_three formula1 tail).trans htotalCode
  have hformula2Code :
      (binaryFormulaCode formula2).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_three formula2 formula3).trans htailCode
  have hformula3Code :
      (binaryFormulaCode formula3).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_three formula2 formula3).trans htailCode
  have hinner :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula2 formula3 resource2 resource3 syntaxResource hpositive
      hformula2Closed hformula3Closed hformula2Code hformula3Code htailCode
  have houter :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula1 tail resource1
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2
        resource3)
      syntaxResource hpositive hformula1Closed htailClosed hformula1Code
      htailCode htotalCode
  have hmono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula1 tail (leftSmall := resource1) (leftLarge := resource1) le_rfl
    hinner
  unfold hybridThreeConjunctionGeneralPayloadEnvelope
  exact hmono.trans houter

#print axioms transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral

end FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
