import integration.FoundationCompactNumericListedDirectVerifierHaltedFormula
import integration.FoundationCompactNumericListedDirectVerifierPayloadEquality
import integration.FoundationCompactNumericListedDirectVerifierStateRealization

/-!
# Exact semantic realization of the halted verifier branch

An arithmetic halted row copies the complete encoded state.  Determinacy of
the state decoder turns that byte-level equality into equality of typed states.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierHaltedExactness

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierHaltedFormula
open FoundationCompactNumericListedDirectVerifierStateRealization
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTokenSliceEquality

theorem CompactNumericVerifierHaltedRows.realizeExactStep
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    (hcurrent : CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount currentCoordinates currentSizeWitness)
    (hnext : CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount nextCoordinates nextSizeWitness)
    (hhalted : CompactNumericVerifierHaltedRows
      tokenTable width tokenCount
      currentCoordinates.start currentCoordinates.finish
      currentCoordinates.statusTag
      nextCoordinates.start nextCoordinates.finish) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  rcases hhalted with ⟨hcurrentTag, heq⟩
  rcases CompactNumericVerifierStateCoreGraph.realizeDirectLayout hcurrent with
    ⟨currentProofTokens, currentCertificateTokens, currentTasks,
      currentValues, currentStatus,
      _hcurrentProofLength, _hcurrentCertificateLength,
      _hcurrentTasksLength, _hcurrentValuesLength,
      hcurrentLayout,
      _hcurrentProof, _hcurrentCertificate,
      _hcurrentTaskLayout, _hcurrentTaskRows,
      _hcurrentValueLayout, _hcurrentValueRows,
      hcurrentStatus⟩
  rcases CompactNumericVerifierStateCoreGraph.realizeDirectLayout hnext with
    ⟨nextProofTokens, nextCertificateTokens, nextTasks,
      nextValues, nextStatus,
      _hnextProofLength, _hnextCertificateLength,
      _hnextTasksLength, _hnextValuesLength,
      hnextLayout,
      _hnextProof, _hnextCertificate,
      _hnextTaskLayout, _hnextTaskRows,
      _hnextValueLayout, _hnextValueRows,
      _hnextStatus⟩
  obtain ⟨currentResult, hcurrentStatusSome⟩ :
      ∃ result : Bool, currentStatus = some result := by
    rcases hcurrentStatus with hnone | hsome
    · omega
    · rcases hsome with ⟨result, hstatus, _htag, _hresult⟩
      exact ⟨result, hstatus⟩
  let currentState : CompactNumericVerifierState :=
    (((currentProofTokens, currentCertificateTokens),
      (currentTasks, currentValues)), currentStatus)
  let nextState : CompactNumericVerifierState :=
    (((nextProofTokens, nextCertificateTokens),
      (nextTasks, nextValues)), nextStatus)
  have hstateEq : nextState = currentState := by
    exact CompactFixedWidthTokenSlicesEq.verifierStateValue_eq
      heq hcurrentLayout hnextLayout
  have hcurrentFixed :
      compactNumericVerifierStep currentState = currentState := by
    simp [currentState, compactNumericVerifierStep, hcurrentStatusSome]
  refine ⟨currentState, nextState, ?_, ?_, ?_⟩
  · exact hcurrentLayout
  · exact hnextLayout
  · exact hstateEq.trans hcurrentFixed.symm

#print axioms CompactNumericVerifierHaltedRows.realizeExactStep

end FoundationCompactNumericListedDirectVerifierHaltedExactness
