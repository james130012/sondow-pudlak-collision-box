import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexFixedCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Free variables of one open-index bounded sequent row -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexFreeVariables

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax

private theorem
    compactSequentFormulaStepRowBoundedAtValuationIndexCorePublicTerms_freeVariables_subset_singleton
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat)
    (coordinate : Fin 8) :
    (compactSequentFormulaStepRowBoundedAtValuationIndexCorePublicTerms
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount (&0 : ValuationTerm) coordinate).freeVariables ⊆ {0} := by
  fin_cases coordinate <;>
    simp [
      compactSequentFormulaStepRowBoundedAtValuationIndexCorePublicTerms,
      shortBinaryNumeralTerm_freeVariables_eq_empty]

theorem
    compactSequentFormulaStepRowBoundedAtValuationIndexRawBody_freeVariables_subset_singleton
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat) :
    (compactSequentFormulaStepRowBoundedAtOpenIndexRawBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary
      valueCount).freeVariables ⊆ {0} := by
  unfold compactSequentFormulaStepRowBoundedAtOpenIndexRawBody
  unfold compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal
  apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
  intro coordinate
  unfold compactSequentFormulaStepRowBoundedAtValuationIndexRawTerms
  simp only [Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · unfold
      compactSequentFormulaStepRowBoundedAtValuationIndexRawPublicTerms
    rw [sourceSubstitutionLift_freeVariables_eq]
    exact
      compactSequentFormulaStepRowBoundedAtValuationIndexCorePublicTerms_freeVariables_subset_singleton
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount ⟨coordinate, hcoordinate⟩
  · unfold compactSequentFormulaStepRowBoundedDirectRawWitnessTerms
    simp

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexRawBody_freeVariables_subset_singleton

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexFreeVariables
