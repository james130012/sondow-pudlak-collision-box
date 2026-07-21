import integration.FoundationCompactNumericListedDirectVerifierCombineBranchRows
import integration.FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds

/-!
# Converse packing for verifier-combine branches

Each local successful or failed rule row is packed into the common fixed
combine witness.  Coordinates unused by the selected disjunct are set to zero.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineBranchRowsCompleteness

open FoundationCompactNumericListedDirectSimpleCombineTransitionRows
open FoundationCompactNumericListedDirectAllShiftCombineRuleRows
open FoundationCompactNumericListedDirectExsCutCombineRuleRows
open FoundationCompactNumericListedDirectVerifierCombineFailureRows
open FoundationCompactNumericListedDirectVerifierCombineSuccessRows
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds

theorem CompactNumericVerifierCombineBranchRows.of_simple_rows
    {tokenTable width tokenCount taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue nextStatusBool : Nat}
    (hrows : CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue) :
    CompactNumericVerifierCombineBranchRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound 0 nextStatusBool
      (compactNumericVerifierSimpleCombineRuleWitness
        rightGammaCount rightGammaBoundary rightBoolValue
        leftGammaCount leftGammaBoundary leftBoolValue resultBoolValue) := by
  exact Or.inl ⟨hrows, rfl⟩

theorem CompactNumericVerifierCombineBranchRows.exists_of_simple_rows
    {tokenTable width tokenCount taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue nextStatusBool : Nat}
    (hrows : CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue) :
    ∃ witness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineBranchRows
        tokenTable width tokenCount
        taskTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        witnessFinish witnessCount
        sourceBoundary sourceCount targetBoundary targetCount
        tableWidth valueBound 0 nextStatusBool witness := by
  exact ⟨compactNumericVerifierSimpleCombineRuleWitness
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue resultBoolValue,
    CompactNumericVerifierCombineBranchRows.of_simple_rows hrows⟩

theorem CompactNumericVerifierCombineBranchRows.exists_of_all_shift_rows
    {tokenTable width tokenCount taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount premiseGammaCount premiseGammaBoundary
      premiseBoolValue sourceBoundary sourceCount targetBoundary targetCount
      secondFinish secondCount witnessFinish witnessCount
      formulaBoundary formulaBoundarySize freedStart freedFinish freedBoundary
      freedCount freedBoundarySize freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize shiftWitnessBound
      freeTableWidth freeValueBound tableWidth valueBound resultBoolValue
      nextStatusBool : Nat}
    (hrows : CompactNumericAllShiftCombineRuleRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue) :
    ∃ witness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineBranchRows
        tokenTable width tokenCount
        taskTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        witnessFinish witnessCount
        sourceBoundary sourceCount targetBoundary targetCount
        tableWidth valueBound 0 nextStatusBool witness := by
  let witness : CompactNumericVerifierCombineRuleWitness :=
    compactNumericVerifierAllShiftCombineRuleWitness
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound resultBoolValue
  refine ⟨witness, ?_⟩
  exact Or.inr <| Or.inl ⟨hrows, rfl⟩

theorem CompactNumericVerifierCombineBranchRows.exists_of_exs_cut_rows
    {tokenTable width tokenCount taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize transformedStart transformedFinish
      transformedBoundary transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount emptyStart emptyFinish
      emptyBoundary emptyBoundarySize transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue nextStatusBool : Nat}
    (hrows : CompactNumericExsCutCombineRuleRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish witnessFinish witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary transformedCount
        transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue) :
    ∃ witness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineBranchRows
        tokenTable width tokenCount
        taskTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        witnessFinish witnessCount
        sourceBoundary sourceCount targetBoundary targetCount
        tableWidth valueBound 0 nextStatusBool witness := by
  let witness : CompactNumericVerifierCombineRuleWitness :=
    compactNumericVerifierExsCutCombineRuleWitness
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound resultBoolValue
  refine ⟨witness, ?_⟩
  exact Or.inr <| Or.inr <| Or.inl ⟨hrows, rfl⟩

theorem CompactNumericVerifierCombineBranchRows.of_failure_rows
    {tokenTable width tokenCount taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount tableWidth valueBound
      nextStatusBool : Nat}
    (hrows : CompactNumericVerifierCombineFailureRows
      tokenTable width tokenCount taskTag
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound 1 nextStatusBool) :
    CompactNumericVerifierCombineBranchRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound 1 nextStatusBool
      compactNumericVerifierFailureCombineRuleWitness := by
  exact Or.inr <| Or.inr <| Or.inr hrows

theorem CompactNumericVerifierCombineBranchRows.exists_of_failure_rows
    {tokenTable width tokenCount taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount tableWidth valueBound
      nextStatusBool : Nat}
    (hrows : CompactNumericVerifierCombineFailureRows
      tokenTable width tokenCount taskTag
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound 1 nextStatusBool) :
    ∃ witness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineBranchRows
        tokenTable width tokenCount
        taskTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        witnessFinish witnessCount
        sourceBoundary sourceCount targetBoundary targetCount
        tableWidth valueBound 1 nextStatusBool witness := by
  exact ⟨compactNumericVerifierFailureCombineRuleWitness,
    CompactNumericVerifierCombineBranchRows.of_failure_rows hrows⟩

#print axioms CompactNumericVerifierCombineBranchRows.of_simple_rows
#print axioms CompactNumericVerifierCombineBranchRows.of_failure_rows
#print axioms CompactNumericVerifierCombineBranchRows.exists_of_simple_rows
#print axioms CompactNumericVerifierCombineBranchRows.exists_of_all_shift_rows
#print axioms CompactNumericVerifierCombineBranchRows.exists_of_exs_cut_rows
#print axioms CompactNumericVerifierCombineBranchRows.exists_of_failure_rows

end FoundationCompactNumericListedDirectVerifierCombineBranchRowsCompleteness
