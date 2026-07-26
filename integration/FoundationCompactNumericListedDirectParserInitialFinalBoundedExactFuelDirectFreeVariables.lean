import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectTerminalAlignment
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Closedness of exact-fuel bounded parser endpoint syntax -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectFreeVariables

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSourceAlignment
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectTerminalAlignment

private theorem
    compactParserInitialFinalBoundedExactFuelDirectPublicTerms_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (coordinate : Fin 13) :
    (compactParserInitialFinalBoundedExactFuelDirectPublicTerms tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount coordinate).freeVariables = ∅ := by
  fin_cases coordinate <;>
    first
    | exact compactParserSyntaxExactFuelTerm_freeVariables_eq_empty inputCount
    | exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem
    compactParserInitialFinalBoundedExactFuelDirectRawTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat) :
    (compactParserInitialFinalBoundedExactFuelDirectRawTerminal tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount).freeVariables = ∅ := by
  unfold compactParserInitialFinalBoundedExactFuelDirectRawTerminal
  apply
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  unfold compactParserInitialFinalBoundedExactFuelDirectRawTerms
  simp only [Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · let publicCoordinate : Fin 13 := ⟨coordinate, hcoordinate⟩
    change (sourceSubstitutionLift 23
      (compactParserInitialFinalBoundedExactFuelDirectPublicTerms tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount publicCoordinate)).freeVariables = ∅
    rw [sourceSubstitutionLift_freeVariables_eq]
    exact
      compactParserInitialFinalBoundedExactFuelDirectPublicTerms_freeVariables_eq_empty
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount publicCoordinate
  · simp [compactParserInitialFinalBoundedDirectRawWitnessTerms]

theorem
    compactParserInitialFinalBoundedExactFuelDirectClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound : Nat) :
    (compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound).freeVariables = ∅ := by
  rw [
    compactParserInitialFinalBoundedExactFuelDirectClosedFormula_eq_original]
  apply
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  unfold compactParserInitialFinalBoundedExactFuelDirectSourceTerms
  simp only [Matrix.vecAppend_eq_ite]
  split_ifs with hcoordinate
  · let publicCoordinate : Fin 13 := ⟨coordinate, hcoordinate⟩
    change
      (compactParserInitialFinalBoundedExactFuelDirectPublicTerms tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount publicCoordinate).freeVariables = ∅
    exact
      compactParserInitialFinalBoundedExactFuelDirectPublicTerms_freeVariables_eq_empty
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount publicCoordinate
  · let boundCoordinate : Fin 1 := ⟨coordinate - 13, by omega⟩
    change
      (![shortBinaryNumeralTerm valueBound] boundCoordinate).freeVariables = ∅
    simpa using shortBinaryNumeralTerm_freeVariables_eq_empty valueBound

#print axioms
  compactParserInitialFinalBoundedExactFuelDirectRawTerminal_freeVariables_eq_empty
#print axioms
  compactParserInitialFinalBoundedExactFuelDirectClosedFormula_freeVariables_eq_empty

end FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectFreeVariables
