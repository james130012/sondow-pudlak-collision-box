import integration.FoundationCompactNumericListedDirectVerifierCombineBranchRows

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
  let witness : CompactNumericVerifierCombineRuleWitness :=
    { rightGammaCount := rightGammaCount
      rightGammaBoundary := rightGammaBoundary
      rightBoolValue := rightBoolValue
      leftGammaCount := leftGammaCount
      leftGammaBoundary := leftGammaBoundary
      leftBoolValue := leftBoolValue
      formulaBoundary := 0
      formulaBoundarySize := 0
      transformedStart := 0
      transformedFinish := 0
      transformedBoundary := 0
      transformedCount := 0
      transformedBoundarySize := 0
      transformStateBoundary := 0
      transformStateCount := 0
      freedStart := 0
      freedFinish := 0
      freedBoundary := 0
      freedCount := 0
      freedBoundarySize := 0
      freeStateBoundary := 0
      freeStateCount := 0
      shiftCandidateBoundary := 0
      shiftSuccessTable := 0
      shiftedBoundary := 0
      shiftedCount := 0
      emptyStart := 0
      emptyFinish := 0
      emptyBoundary := 0
      emptyBoundarySize := 0
      shiftWitnessBound := 0
      freeTableWidth := 0
      freeValueBound := 0
      resultBoolValue := resultBoolValue }
  refine ⟨witness, ?_⟩
  exact Or.inl ⟨hrows, rfl⟩

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
    { rightGammaCount := premiseGammaCount
      rightGammaBoundary := premiseGammaBoundary
      rightBoolValue := premiseBoolValue
      leftGammaCount := 0
      leftGammaBoundary := 0
      leftBoolValue := 0
      formulaBoundary := formulaBoundary
      formulaBoundarySize := formulaBoundarySize
      transformedStart := 0
      transformedFinish := 0
      transformedBoundary := 0
      transformedCount := 0
      transformedBoundarySize := 0
      transformStateBoundary := 0
      transformStateCount := 0
      freedStart := freedStart
      freedFinish := freedFinish
      freedBoundary := freedBoundary
      freedCount := freedCount
      freedBoundarySize := freedBoundarySize
      freeStateBoundary := freeStateBoundary
      freeStateCount := freeStateCount
      shiftCandidateBoundary := shiftCandidateBoundary
      shiftSuccessTable := shiftSuccessTable
      shiftedBoundary := shiftedBoundary
      shiftedCount := shiftedCount
      emptyStart := emptyStart
      emptyFinish := emptyFinish
      emptyBoundary := emptyBoundary
      emptyBoundarySize := emptyBoundarySize
      shiftWitnessBound := shiftWitnessBound
      freeTableWidth := freeTableWidth
      freeValueBound := freeValueBound
      resultBoolValue := resultBoolValue }
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
    { rightGammaCount := rightGammaCount
      rightGammaBoundary := rightGammaBoundary
      rightBoolValue := rightBoolValue
      leftGammaCount := leftGammaCount
      leftGammaBoundary := leftGammaBoundary
      leftBoolValue := leftBoolValue
      formulaBoundary := formulaBoundary
      formulaBoundarySize := formulaBoundarySize
      transformedStart := transformedStart
      transformedFinish := transformedFinish
      transformedBoundary := transformedBoundary
      transformedCount := transformedCount
      transformedBoundarySize := transformedBoundarySize
      transformStateBoundary := transformStateBoundary
      transformStateCount := transformStateCount
      freedStart := 0
      freedFinish := 0
      freedBoundary := 0
      freedCount := 0
      freedBoundarySize := 0
      freeStateBoundary := 0
      freeStateCount := 0
      shiftCandidateBoundary := 0
      shiftSuccessTable := 0
      shiftedBoundary := 0
      shiftedCount := 0
      emptyStart := emptyStart
      emptyFinish := emptyFinish
      emptyBoundary := emptyBoundary
      emptyBoundarySize := emptyBoundarySize
      shiftWitnessBound := 0
      freeTableWidth := transformTableWidth
      freeValueBound := transformValueBound
      resultBoolValue := resultBoolValue }
  refine ⟨witness, ?_⟩
  exact Or.inr <| Or.inr <| Or.inl ⟨hrows, rfl⟩

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
  let witness : CompactNumericVerifierCombineRuleWitness :=
    { rightGammaCount := 0
      rightGammaBoundary := 0
      rightBoolValue := 0
      leftGammaCount := 0
      leftGammaBoundary := 0
      leftBoolValue := 0
      formulaBoundary := 0
      formulaBoundarySize := 0
      transformedStart := 0
      transformedFinish := 0
      transformedBoundary := 0
      transformedCount := 0
      transformedBoundarySize := 0
      transformStateBoundary := 0
      transformStateCount := 0
      freedStart := 0
      freedFinish := 0
      freedBoundary := 0
      freedCount := 0
      freedBoundarySize := 0
      freeStateBoundary := 0
      freeStateCount := 0
      shiftCandidateBoundary := 0
      shiftSuccessTable := 0
      shiftedBoundary := 0
      shiftedCount := 0
      emptyStart := 0
      emptyFinish := 0
      emptyBoundary := 0
      emptyBoundarySize := 0
      shiftWitnessBound := 0
      freeTableWidth := 0
      freeValueBound := 0
      resultBoolValue := 0 }
  refine ⟨witness, ?_⟩
  exact Or.inr <| Or.inr <| Or.inr hrows

#print axioms CompactNumericVerifierCombineBranchRows.exists_of_simple_rows
#print axioms CompactNumericVerifierCombineBranchRows.exists_of_all_shift_rows
#print axioms CompactNumericVerifierCombineBranchRows.exists_of_exs_cut_rows
#print axioms CompactNumericVerifierCombineBranchRows.exists_of_failure_rows

end FoundationCompactNumericListedDirectVerifierCombineBranchRowsCompleteness
