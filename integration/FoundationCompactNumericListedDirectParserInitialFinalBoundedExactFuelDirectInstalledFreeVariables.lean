import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectFreeVariables

/-! # Closedness after installing the exact-fuel endpoint witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectInstalledFreeVariables

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectTerminalAlignment

theorem
    compactUnifiedParserInitialFinalRowsExactFuelClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    (compactUnifiedParserInitialFinalRowsExactFuelClosedFormula tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount witness).freeVariables = ∅ := by
  unfold compactUnifiedParserInitialFinalRowsExactFuelClosedFormula
  apply
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    first
    | exact compactParserSyntaxExactFuelTerm_freeVariables_eq_empty inputCount
    | exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem
    compactParserInitialFinalBoundedExactFuelDirectInstalledTerminal_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    (compactParserInitialFinalBoundedExactFuelDirectRawTerminal tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount ⇜
        (fun coordinate => shortBinaryNumeralTerm
          (compactParserInitialFinalBoundedDirectWitnessValues witness
            coordinate))).freeVariables = ∅ := by
  rw [
    compactParserInitialFinalBoundedExactFuelDirectRawTerminal_alignment]
  exact
    compactUnifiedParserInitialFinalRowsExactFuelClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount witness

#print axioms
  compactUnifiedParserInitialFinalRowsExactFuelClosedFormula_freeVariables_eq_empty
#print axioms
  compactParserInitialFinalBoundedExactFuelDirectInstalledTerminal_freeVariables_eq_empty

end FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectInstalledFreeVariables
