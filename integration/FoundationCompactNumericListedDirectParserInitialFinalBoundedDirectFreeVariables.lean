import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectCheckedData
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectTerminalAlignment
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Closedness of the bounded parser endpoint syntax -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectFreeVariables

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalSourceAlignment
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectClosedTermsAlignment
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectTerminalAlignment

private theorem
    compactParserInitialFinalBoundedDirectPublicTerms_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (coordinate : Fin 13) :
    (compactParserInitialFinalBoundedDirectPublicTerms tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount coordinate).freeVariables = ∅ := by
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem compactParserInitialFinalBoundedDirectRawTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat) :
    (compactParserInitialFinalBoundedDirectRawTerminal tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount).freeVariables = ∅ := by
  unfold compactParserInitialFinalBoundedDirectRawTerminal
  apply
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  unfold compactParserInitialFinalBoundedDirectRawTerms
  simp only [Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · let publicCoordinate : Fin 13 := ⟨coordinate, hcoordinate⟩
    change (sourceSubstitutionLift 23
      (compactParserInitialFinalBoundedDirectPublicTerms tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount publicCoordinate)).freeVariables = ∅
    rw [sourceSubstitutionLift_freeVariables_eq]
    exact
      compactParserInitialFinalBoundedDirectPublicTerms_freeVariables_eq_empty
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount publicCoordinate
  · simp [compactParserInitialFinalBoundedDirectRawWitnessTerms]

theorem compactParserInitialFinalBoundedDirectClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) :
    (compactParserInitialFinalBoundedDirectClosedFormula tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound).freeVariables = ∅ := by
  rw [compactParserInitialFinalBoundedDirectClosedFormula_eq_original]
  apply
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  unfold compactParserInitialFinalBoundedDirectSourceTerms
  simp only [Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · let publicCoordinate : Fin 13 := ⟨coordinate, hcoordinate⟩
    change
      (compactParserInitialFinalBoundedDirectPublicTerms tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount publicCoordinate).freeVariables = ∅
    exact
      compactParserInitialFinalBoundedDirectPublicTerms_freeVariables_eq_empty
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount publicCoordinate
  · let boundCoordinate : Fin 1 := ⟨coordinate - 13, by omega⟩
    change
      (![shortBinaryNumeralTerm valueBound] boundCoordinate).freeVariables = ∅
    simpa using shortBinaryNumeralTerm_freeVariables_eq_empty valueBound

theorem compactUnifiedParserInitialFinalRowsClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    (compactUnifiedParserInitialFinalRowsClosedFormula tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount witness).freeVariables = ∅ := by
  rw [compactUnifiedParserInitialFinalRowsClosedFormula_eq_directClosedTerms]
  apply
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  unfold compactParserInitialFinalBoundedDirectClosedTerms
  simp only [Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · let publicCoordinate : Fin 13 := ⟨coordinate, hcoordinate⟩
    change
      (compactParserInitialFinalBoundedDirectPublicTerms tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount publicCoordinate).freeVariables = ∅
    exact
      compactParserInitialFinalBoundedDirectPublicTerms_freeVariables_eq_empty
        tokenTable width tokenCount stateBoundary stateCount fuel
        inputBoundary inputCount expectedBoundary expectedCount taskKind
        taskBinderArity taskRepeatCount publicCoordinate
  · simp [compactParserInitialFinalBoundedDirectClosedWitnessTerms,
      shortBinaryNumeralTerm_freeVariables_eq_empty]

theorem
    compactParserInitialFinalBoundedDirectInstalledTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    (compactParserInitialFinalBoundedDirectRawTerminal tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount ⇜
        (fun coordinate => shortBinaryNumeralTerm
          (compactParserInitialFinalBoundedDirectWitnessValues witness
            coordinate))).freeVariables = ∅ := by
  rw [compactParserInitialFinalBoundedDirectRawTerminal_alignment]
  exact
    compactUnifiedParserInitialFinalRowsClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount witness

#print axioms
  compactParserInitialFinalBoundedDirectRawTerminal_freeVariables_eq_empty
#print axioms
  compactParserInitialFinalBoundedDirectClosedFormula_freeVariables_eq_empty
#print axioms
  compactUnifiedParserInitialFinalRowsClosedFormula_freeVariables_eq_empty
#print axioms
  compactParserInitialFinalBoundedDirectInstalledTerminal_freeVariables_eq_empty

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectFreeVariables
