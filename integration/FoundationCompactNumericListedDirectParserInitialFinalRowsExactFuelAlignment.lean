import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelInitialAtAlignment
import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelInitialAlignment
import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFinalAtAlignment
import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFinalAlignment

/-! # Alignment of the exact-fuel combined parser endpoints -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelAlignment

open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelInitialAtAlignment
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelInitialAlignment
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFinalAtAlignment
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFinalAlignment

theorem compactUnifiedParserInitialFinalRowsExactFuel_alignment
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    compactUnifiedParserInitialFinalRowsExactFuelClosedFormula tokenTable width
        tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness =
      compactUnifiedParserInitialFinalRowsExactFuelExplicitFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness := by
  unfold compactUnifiedParserInitialFinalRowsExactFuelClosedFormula
  unfold compactUnifiedParserInitialFinalRowsExactFuelExplicitFormula
  unfold compactParserInitialFinalExactFuelCountFormula
  unfold compactUnifiedParserInitialFinalRowsDef
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  · rfl
  · rfl
  · rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    simpa only [compactParserInitialFinalInitialAtClosedSourceTerms] using
      compactUnifiedParserInitialFinalRowsExactFuel_initialAt_embedded_alignment
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness
  · rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    simpa only [compactParserInitialFinalInitialClosedSourceTerms] using
      compactUnifiedParserInitialFinalRowsExactFuel_initial_embedded_alignment
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness
  · rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    simpa only [compactParserInitialFinalFinalAtClosedSourceTerms] using
      compactUnifiedParserInitialFinalRowsExactFuel_finalAt_embedded_alignment
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness
  · rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    simpa only [compactParserInitialFinalFinalClosedSourceTerms] using
      compactUnifiedParserInitialFinalRowsExactFuel_final_embedded_alignment
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount witness

#print axioms compactUnifiedParserInitialFinalRowsExactFuel_alignment

end FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelAlignment
