import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData

/-! # Closedness of the bounded sequent-step row syntax -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectFreeVariables

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax

private theorem
    compactSequentFormulaStepRowBoundedDirectCorePublicTerms_freeVariables_eq_empty
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (coordinate : Fin 8) :
    (compactSequentFormulaStepRowBoundedDirectCorePublicTerms tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      coordinate).freeVariables = ∅ := by
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem
    compactSequentFormulaStepRowBoundedDirectRawTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat) :
    (compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      rowIndex).freeVariables = ∅ := by
  unfold compactSequentFormulaStepRowBoundedDirectRawTerminal
  apply
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  unfold compactSequentFormulaStepRowBoundedDirectRawTerms
  simp only [Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · unfold compactSequentFormulaStepRowBoundedDirectRawPublicTerms
    rw [sourceSubstitutionLift_freeVariables_eq]
    exact
      compactSequentFormulaStepRowBoundedDirectCorePublicTerms_freeVariables_eq_empty
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex ⟨coordinate, hcoordinate⟩
  · unfold compactSequentFormulaStepRowBoundedDirectRawWitnessTerms
    simp

theorem compactSequentFormulaStepDirectClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : FoundationCompactNumericListedDirectSequentFormulaStepFormula.CompactSequentFormulaStepCoordinates) :
    (compactSequentFormulaStepDirectClosedFormula tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex
      row).freeVariables = ∅ := by
  unfold compactSequentFormulaStepDirectClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem
    compactSequentFormulaStepRowBoundedDirectInstalledTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : FoundationCompactNumericListedDirectSequentFormulaStepFormula.CompactSequentFormulaStepCoordinates) :
    (compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowIndex ⇜
      (fun index => shortBinaryNumeralTerm
        (compactSequentFormulaStepRowBoundedDirectWitnessValues row
          index))).freeVariables = ∅ := by
  rw [
    compactSequentFormulaStepRowBoundedDirectRawTerminal_alignment]
  exact
    compactSequentFormulaStepDirectClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex row

theorem
    compactSequentFormulaStepRowBoundedDirectClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat) :
    (compactSequentFormulaStepRowBoundedDirectClosedFormula tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound).freeVariables = ∅ := by
  unfold compactSequentFormulaStepRowBoundedDirectClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

#print axioms
  compactSequentFormulaStepRowBoundedDirectRawTerminal_freeVariables_eq_empty
#print axioms
  compactSequentFormulaStepDirectClosedFormula_freeVariables_eq_empty
#print axioms
  compactSequentFormulaStepRowBoundedDirectInstalledTerminal_freeVariables_eq_empty
#print axioms
  compactSequentFormulaStepRowBoundedDirectClosedFormula_freeVariables_eq_empty

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectFreeVariables
