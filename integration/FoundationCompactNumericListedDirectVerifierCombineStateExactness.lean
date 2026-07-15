import integration.FoundationCompactNumericListedDirectVerifierCombineStateFrameRows

/-!
# Exact semantic endpoints for verifier combine states

The common bounded frame already identifies the real task, removes exactly
that task from the stack, and preserves both input streams.  This module adds
the two possible public combine outcomes and proves that the realized target
state is exactly one executable verifier step.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineStateFrameRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierPayloadEquality

theorem CompactNumericVerifierCombineStateFrameRealization.realizeExactSuccess
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    (frame : CompactNumericVerifierCombineStateFrameRealization
      tokenTable width tokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates)
    {combined : CompactNumericChildResult ×
      List CompactNumericChildResult}
    (hcombine : compactNumericCombineTransition
      frame.task frame.currentValues = some combined)
    (hvalues : frame.nextValues = combined.1 :: combined.2)
    (hnextStatusTag : nextCoordinates.statusTag = 0) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  have hnextStatusNone : frame.nextStatus = none := by
    rcases frame.nextStatusCase with hnone | hsome
    · exact hnone.1
    · rcases hsome with ⟨result, _hstatus, htag, _hbool⟩
      omega
  let currentState : CompactNumericVerifierState :=
    (((frame.proofTokens, frame.certificateTokens),
      (frame.currentTasks, frame.currentValues)), none)
  let nextState : CompactNumericVerifierState :=
    (((frame.proofTokens, frame.certificateTokens),
      (frame.nextTasks, frame.nextValues)), none)
  have hnextLayout : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount nextCoordinates.start
        nextCoordinates.finish nextState := by
    simpa [nextState, hnextStatusNone] using frame.nextLayout
  refine ⟨currentState, nextState, ?_, hnextLayout, ?_⟩
  · simpa [currentState] using frame.currentLayout
  · dsimp only [currentState, nextState]
    rw [frame.taskStack_eq]
    simp [compactNumericVerifierStep, compactNumericRunningStep,
      frame.taskTag_ne_ten, compactNumericCombineState,
      hcombine, hvalues]

theorem CompactNumericVerifierCombineStateFrameRealization.realizeExactFailure
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    (frame : CompactNumericVerifierCombineStateFrameRealization
      tokenTable width tokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates)
    (hcombine : compactNumericCombineTransition
      frame.task frame.currentValues = none)
    (hvalues : frame.nextValues = frame.currentValues)
    (hnextStatusTag : nextCoordinates.statusTag = 1)
    (hnextStatusBool : nextCoordinates.statusBool =
      compactAdditiveBoolTag false) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  have hnextStatusFalse : frame.nextStatus = some false := by
    rcases frame.nextStatusCase with hnone | hsome
    · omega
    · rcases hsome with ⟨result, hstatus, _htag, hbool⟩
      have hresult : result = false :=
        compactAdditiveBoolTag_injective
          (hbool.trans hnextStatusBool)
      simpa [hresult] using hstatus
  let currentState : CompactNumericVerifierState :=
    (((frame.proofTokens, frame.certificateTokens),
      (frame.currentTasks, frame.currentValues)), none)
  let nextState : CompactNumericVerifierState :=
    (((frame.proofTokens, frame.certificateTokens),
      (frame.nextTasks, frame.nextValues)), some false)
  have hnextLayout : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount nextCoordinates.start
        nextCoordinates.finish nextState := by
    simpa [nextState, hnextStatusFalse] using frame.nextLayout
  refine ⟨currentState, nextState, ?_, hnextLayout, ?_⟩
  · simpa [currentState] using frame.currentLayout
  · dsimp only [currentState, nextState]
    rw [frame.taskStack_eq]
    simp [compactNumericVerifierStep, compactNumericRunningStep,
      frame.taskTag_ne_ten, compactNumericCombineState,
      hcombine, hvalues]

#print axioms
  CompactNumericVerifierCombineStateFrameRealization.realizeExactSuccess
#print axioms
  CompactNumericVerifierCombineStateFrameRealization.realizeExactFailure

end FoundationCompactNumericListedDirectVerifierCombineStateFrameRows
