import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Closedness of the raw thirty-one-variable endpoint matrix -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectFreeVariables

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectSyntax

private theorem compactFormulaTransformInitialFinalBoundedDirectPublicTerms_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat)
    (coordinate : Fin 13) :
    (compactFormulaTransformInitialFinalBoundedDirectPublicTerms tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity coordinate).freeVariables = ∅ := by
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem compactFormulaTransformInitialFinalBoundedDirectRawTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity : Nat) :
    (compactFormulaTransformInitialFinalBoundedDirectRawTerminal tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity).freeVariables = ∅ := by
  unfold compactFormulaTransformInitialFinalBoundedDirectRawTerminal
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  unfold compactFormulaTransformInitialFinalBoundedDirectRawTerms
  simp only [Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · let publicCoordinate : Fin 13 := ⟨coordinate, hcoordinate⟩
    change (sourceSubstitutionLift 31
      (compactFormulaTransformInitialFinalBoundedDirectPublicTerms tokenTable
        width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
        expectedSuffixCount binderArity publicCoordinate)).freeVariables = ∅
    rw [sourceSubstitutionLift_freeVariables_eq]
    exact
      compactFormulaTransformInitialFinalBoundedDirectPublicTerms_freeVariables_eq_empty
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity
        publicCoordinate
  · simp [compactFormulaTransformInitialFinalBoundedDirectRawWitnessTerms]

#print axioms
  compactFormulaTransformInitialFinalBoundedDirectRawTerminal_freeVariables_eq_empty

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectFreeVariables
