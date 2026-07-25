import integration.FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds
import integration.FoundationCompactPAValuationTermCompilerPublicBounds

/-!
# Five-leaf hybrid conjunctions over one valuation variable

This is the open-index counterpart of the closed five-leaf assembly theorem.
All formulas may use variable `0`; no caller-provided context resource remains
once its value is bounded by the shared numeric coordinate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactPAHybridFiveConjunctionSingletonGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds

private theorem and_left_variables_subset_singleton
    (left right : ValuationFormula)
    (hvariables : (left ⋏ right).freeVariables ⊆ {0}) :
    left.freeVariables ⊆ {0} := by
  intro candidate hcandidate
  apply hvariables
  rw [LO.FirstOrder.Semiformula.freeVariables_and]
  exact Finset.mem_union_left _ hcandidate

private theorem and_right_variables_subset_singleton
    (left right : ValuationFormula)
    (hvariables : (left ⋏ right).freeVariables ⊆ {0}) :
    right.freeVariables ⊆ {0} := by
  intro candidate hcandidate
  apply hvariables
  rw [LO.FirstOrder.Semiformula.freeVariables_and]
  exact Finset.mem_union_right _ hcandidate

private theorem binaryFormulaCode_and_left_le_singletonFive
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem binaryFormulaCode_and_right_le_singletonFive
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem valuationContextFormulaCodeSum_le_singletonFive
    (valuation : Nat -> Nat) (formula : ValuationFormula)
    (numericBound : Nat)
    (hvariables : formula.freeVariables ⊆ {0})
    (hvaluation : valuation 0 <= numericBound) :
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
        (valuationContext formula.freeVariables valuation) <=
      valuationContextFormulaCodeSumEnvelope 1 numericBound
        (binaryTermCode (&0 : ValuationTerm)).length := by
  have hcard : formula.freeVariables.card <= 1 :=
    (Finset.card_le_card hvariables).trans (by simp)
  have hvalues : forall index, index ∈ formula.freeVariables ->
      valuation index <= numericBound := by
    intro index hindex
    have hsingleton := hvariables hindex
    simp only [Finset.mem_singleton] at hsingleton
    subst index
    exact hvaluation
  have htermCodes : forall index, index ∈ formula.freeVariables ->
      (binaryTermCode (&index : ValuationTerm)).length <=
        (binaryTermCode (&0 : ValuationTerm)).length := by
    intro index hindex
    have hsingleton := hvariables hindex
    simp only [Finset.mem_singleton] at hsingleton
    subst index
    exact le_rfl
  have hraw := valuationContext_formulaCodeSum_le_uniform
    formula.freeVariables valuation 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length hcard hvalues htermCodes
  simpa only [
    FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum,
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum] using
      hraw

theorem transparentHybridFiveConjunctionPayloadEnvelope_le_singletonGeneral
    (valuation : Nat -> Nat)
    (formula1 formula2 formula3 formula4 formula5 : ValuationFormula)
    (resource1 resource2 resource3 resource4 resource5 syntaxResource
      numericBound : Nat)
    (hpositive : 1 <= syntaxResource)
    (hvaluation : valuation 0 <= numericBound)
    (hvariables :
      (formula1 ⋏
        (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5)))).freeVariables ⊆
          {0})
    (hcode :
      (binaryFormulaCode
        (formula1 ⋏
          (formula2 ⋏ (formula3 ⋏ (formula4 ⋏ formula5))))).length <=
        syntaxResource)
    (hcontext :
      valuationContextFormulaCodeSumEnvelope 1 numericBound
          (binaryTermCode (&0 : ValuationTerm)).length <= syntaxResource) :
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
  have htotalVariables : total.freeVariables ⊆ {0} := by
    simpa only [total, tail2, tail3, tail4] using hvariables
  have hformula1Variables : formula1.freeVariables ⊆ {0} :=
    and_left_variables_subset_singleton formula1 tail2 htotalVariables
  have htail2Variables : tail2.freeVariables ⊆ {0} :=
    and_right_variables_subset_singleton formula1 tail2 htotalVariables
  have hformula2Variables : formula2.freeVariables ⊆ {0} :=
    and_left_variables_subset_singleton formula2 tail3 htail2Variables
  have htail3Variables : tail3.freeVariables ⊆ {0} :=
    and_right_variables_subset_singleton formula2 tail3 htail2Variables
  have hformula3Variables : formula3.freeVariables ⊆ {0} :=
    and_left_variables_subset_singleton formula3 tail4 htail3Variables
  have htail4Variables : tail4.freeVariables ⊆ {0} :=
    and_right_variables_subset_singleton formula3 tail4 htail3Variables
  have hformula4Variables : formula4.freeVariables ⊆ {0} :=
    and_left_variables_subset_singleton formula4 formula5 htail4Variables
  have hformula5Variables : formula5.freeVariables ⊆ {0} :=
    and_right_variables_subset_singleton formula4 formula5 htail4Variables
  have htotalCode : (binaryFormulaCode total).length <= syntaxResource := by
    simpa only [total, tail2, tail3, tail4] using hcode
  have htail2Code : (binaryFormulaCode tail2).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_singletonFive formula1 tail2).trans
      htotalCode
  have htail3Code : (binaryFormulaCode tail3).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_singletonFive formula2 tail3).trans
      htail2Code
  have htail4Code : (binaryFormulaCode tail4).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_singletonFive formula3 tail4).trans
      htail3Code
  have hformula1Code :
      (binaryFormulaCode formula1).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_singletonFive formula1 tail2).trans
      htotalCode
  have hformula2Code :
      (binaryFormulaCode formula2).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_singletonFive formula2 tail3).trans
      htail2Code
  have hformula3Code :
      (binaryFormulaCode formula3).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_singletonFive formula3 tail4).trans
      htail3Code
  have hformula4Code :
      (binaryFormulaCode formula4).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_singletonFive formula4 formula5).trans
      htail4Code
  have hformula5Code :
      (binaryFormulaCode formula5).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_singletonFive formula4 formula5).trans
      htail4Code
  have contextBound : forall formula : ValuationFormula,
      formula.freeVariables ⊆ {0} ->
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext formula.freeVariables valuation) <=
        syntaxResource := by
    intro formula hformula
    exact (valuationContextFormulaCodeSum_le_singletonFive valuation formula
      numericBound hformula hvaluation).trans hcontext
  have h4 := hybridConjunctionStructuralPayloadEnvelope_le_general valuation
    formula4 formula5 resource4 resource5 syntaxResource hpositive
    (contextBound tail4 htail4Variables) hformula4Code hformula5Code
    htail4Code
  have h3 := hybridConjunctionStructuralPayloadEnvelope_le_general valuation
    formula3 tail4 resource3
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource4
        resource5)
      syntaxResource hpositive (contextBound tail3 htail3Variables)
      hformula3Code htail4Code htail3Code
  have h3mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula3 tail4 (leftSmall := resource3) (leftLarge := resource3) le_rfl
    (by
      simpa only [transparentHybridConjunctionPayloadEnvelope,
        hybridConjunctionStructuralPayloadEnvelope] using h4)
  have h2 := hybridConjunctionStructuralPayloadEnvelope_le_general valuation
    formula2 tail3 resource2
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource4
          resource5))
      syntaxResource hpositive (contextBound tail2 htail2Variables)
      hformula2Code htail3Code htail2Code
  have h2mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula2 tail3 (leftSmall := resource2) (leftLarge := resource2) le_rfl
    (h3mono.trans (by
      simpa only [transparentHybridConjunctionPayloadEnvelope,
        hybridConjunctionStructuralPayloadEnvelope] using h3))
  have h1 := hybridConjunctionStructuralPayloadEnvelope_le_general valuation
    formula1 tail2 resource1
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource2
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource3
          (hybridConjunctionGeneralPayloadEnvelope syntaxResource resource4
            resource5)))
      syntaxResource hpositive (contextBound total htotalVariables)
      hformula1Code htail2Code htotalCode
  have h1mono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula1 tail2 (leftSmall := resource1) (leftLarge := resource1) le_rfl
    (h2mono.trans (by
      simpa only [transparentHybridConjunctionPayloadEnvelope,
        hybridConjunctionStructuralPayloadEnvelope] using h2))
  unfold hybridFiveConjunctionGeneralPayloadEnvelope
  simpa only [tail2, tail3, tail4, transparentHybridConjunctionPayloadEnvelope,
    hybridConjunctionStructuralPayloadEnvelope] using h1mono.trans h1

#print axioms
  transparentHybridFiveConjunctionPayloadEnvelope_le_singletonGeneral

end FoundationCompactPAHybridFiveConjunctionSingletonGeneralBounds
