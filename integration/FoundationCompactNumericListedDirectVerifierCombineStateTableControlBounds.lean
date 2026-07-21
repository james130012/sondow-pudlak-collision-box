import integration.FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds
import integration.FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsPublicBounds

/-!
# Numeric state-table controls for canonical combine rows

Combine rows use the two state encodings followed by the explicit rule-checking
suffix.  The public combine budget controls that whole canonical table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineStateTableControlBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierCombinePublicBounds
open FoundationCompactNumericListedDirectVerifierNonParseCheckedRowsPublicBounds
open FoundationCompactNumericListedDirectVerifierAcceptedStateTableControlBounds

set_option maxRecDepth 4000 in
set_option maxHeartbeats 9000000 in
theorem
    exists_compactNumericVerifierPublicCombineCheckedStepRow_with_controlBounds_of_transition
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (htaskNe : task.1 ≠ 10)
    (htransition : compactNumericCombineState task
      ((proofTokens, certificateTokens), (tasks, source)) =
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus))
    {rowWeight : Nat}
    (hcurrent : compactNumericVerifierStateWeight
      ((((proofTokens, certificateTokens), (task :: tasks, source)), none)) <=
        rowWeight)
    (hnext : compactNumericVerifierStateWeight
      ((((proofTokens, certificateTokens), (tasks, target)), nextStatus)) <=
        rowWeight) :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (task :: tasks, source)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
    let coordinateBound :=
      compactNumericVerifierPublicCombineStepCoordinateSizeBound
        (compactNumericVerifierPublicCombineTokenWeightBound
          (compactAdditiveValueWeight currentState)
          (compactAdditiveValueWeight nextState))
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState /\
        row.nextState = nextState /\
        CompactNumericVerifierAcceptedStateTableControlBounds row rowWeight /\
        forall coordinate : Fin 429,
          Nat.size (row.environment coordinate) <= coordinateBound := by
  dsimp only
  rcases
      exists_compactNumericVerifierPublicCombineStepFormulaWitness_with_fixed_sizeBound
        proofTokens certificateTokens task tasks source htaskNe with
    ⟨actualTarget, actualStatus, hactualTransition, witness, hwitness⟩
  have hstateEquality :
      (((proofTokens, certificateTokens), (tasks, actualTarget)),
          actualStatus) =
        (((proofTokens, certificateTokens), (tasks, target)), nextStatus) :=
    hactualTransition.symm.trans htransition
  have htargetStatus :
      actualTarget = target /\ actualStatus = nextStatus := by
    simpa only [Prod.mk.injEq, true_and, and_true] using hstateEquality
  rcases htargetStatus with ⟨rfl, rfl⟩
  exact
    exists_checkedStepRow_of_canonicalCombineFormulaWitness_with_controls
      proofTokens certificateTokens task tasks source actualTarget actualStatus
        rowWeight _
        (by simpa only [compactNumericVerifierStateWeight] using hcurrent)
        (by simpa only [compactNumericVerifierStateWeight] using hnext)
        witness hwitness

#print axioms
  exists_compactNumericVerifierPublicCombineCheckedStepRow_with_controlBounds_of_transition

end FoundationCompactNumericListedDirectVerifierCombineStateTableControlBounds
