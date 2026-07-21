import integration.FoundationCompactNumericListedDirectVerifierCheckedStepRow
import integration.FoundationCompactNumericListedDirectTrace

/-!
# Splicing bounded checked rows along unary and binary executions

These lemmas contain only scheduler arithmetic.  They transport exact checked
rows for a root parse, its child executions, and the final combine step to the
corresponding offsets of the enclosing verifier execution.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCheckedRowExecutionSplicing

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectVerifierCheckedStepRow

theorem compactNumericVerifierStateAt_add_of_iterate
    {start middle : CompactNumericVerifierState}
    {prefixSteps : Nat}
    (hprefix : (compactNumericVerifierStep^[prefixSteps]) start = middle)
    (suffix : Nat) :
    compactNumericVerifierStateAt start (prefixSteps + suffix) =
      compactNumericVerifierStateAt middle suffix := by
  unfold compactNumericVerifierStateAt
  exact compactNumericVerifier_iterate_trans hprefix rfl

theorem compactNumericVerifierStateAt_weight_le_of_prefix
    {start childStart : CompactNumericVerifierState}
    {prefixSteps totalSteps rowWeight childOffset : Nat}
    (hprefix :
      (compactNumericVerifierStep^[prefixSteps]) start = childStart)
    (hparent : forall parentOffset,
      parentOffset <= totalSteps ->
        compactNumericVerifierStateWeight
          (compactNumericVerifierStateAt start parentOffset) <= rowWeight)
    (hindex : prefixSteps + childOffset <= totalSteps) :
    compactNumericVerifierStateWeight
        (compactNumericVerifierStateAt childStart childOffset) <= rowWeight := by
  have hmap := compactNumericVerifierStateAt_add_of_iterate
    hprefix childOffset
  rw [← hmap]
  exact hparent (prefixSteps + childOffset) hindex

theorem exists_checkedStepRow_at_unary_execution_offset
    {start childStart beforeCombine finish : CompactNumericVerifierState}
    {childSteps : Nat}
    (rowProperty : CompactNumericVerifierCheckedStepRow -> Prop)
    (hrootStep : compactNumericVerifierStep start = childStart)
    (hchildExecute :
      (compactNumericVerifierStep^[childSteps]) childStart = beforeCombine)
    (hcombineStep : compactNumericVerifierStep beforeCombine = finish)
    (hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = childStart /\
        rowProperty row)
    (hchildRows : ∀ childOffset, childOffset < childSteps →
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt childStart childOffset /\
          row.nextState =
            compactNumericVerifierStateAt childStart (childOffset + 1) /\
          rowProperty row)
    (hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        rowProperty row)
    {offset : Nat}
    (hoffset : offset < 1 + childSteps + 1) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt start offset /\
        row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
        rowProperty row := by
  have hrootIterate :
      (compactNumericVerifierStep^[1]) start = childStart := by
    simpa only [Function.iterate_one] using hrootStep
  cases offset with
  | zero =>
      rcases hrootRow with ⟨row, hcurrent, hnext, hproperty⟩
      refine ⟨row, ?_, ?_, hproperty⟩
      · simpa [compactNumericVerifierStateAt] using hcurrent
      · exact hnext.trans (by
          simpa [compactNumericVerifierStateAt, Function.iterate_one] using
            hrootStep.symm)
  | succ childOffset =>
      by_cases hinside : childOffset < childSteps
      · rcases hchildRows childOffset hinside with
          ⟨row, hcurrent, hnext, hproperty⟩
        have hcurrentMap :
            compactNumericVerifierStateAt start (Nat.succ childOffset) =
              compactNumericVerifierStateAt childStart childOffset := by
          have hmap := compactNumericVerifierStateAt_add_of_iterate
            hrootIterate childOffset
          have hindex : Nat.succ childOffset = 1 + childOffset := by omega
          rw [hindex]
          exact hmap
        have hnextMap :
            compactNumericVerifierStateAt start
                (Nat.succ childOffset + 1) =
              compactNumericVerifierStateAt childStart (childOffset + 1) := by
          have hmap := compactNumericVerifierStateAt_add_of_iterate
            hrootIterate (childOffset + 1)
          have hindex :
              Nat.succ childOffset + 1 = 1 + (childOffset + 1) := by omega
          rw [hindex]
          exact hmap
        exact ⟨row, hcurrent.trans hcurrentMap.symm,
          hnext.trans hnextMap.symm, hproperty⟩
      · have hoffsetEq : childOffset = childSteps := by omega
        subst childOffset
        rcases hcombineRow with ⟨row, hcurrent, hnext, hproperty⟩
        have hprefix := compactNumericVerifier_iterate_trans
          hrootIterate hchildExecute
        have hcurrentMap :
            compactNumericVerifierStateAt start (Nat.succ childSteps) =
              beforeCombine := by
          unfold compactNumericVerifierStateAt
          have hindex : Nat.succ childSteps = 1 + childSteps := by omega
          rw [hindex]
          exact hprefix
        have hfinishIterate :
            (compactNumericVerifierStep^[1]) beforeCombine = finish := by
          simpa only [Function.iterate_one] using hcombineStep
        have hall := compactNumericVerifier_iterate_trans
          hprefix hfinishIterate
        have hnextMap :
            compactNumericVerifierStateAt start
                (Nat.succ childSteps + 1) = finish := by
          unfold compactNumericVerifierStateAt
          have hindex :
              Nat.succ childSteps + 1 = (1 + childSteps) + 1 := by omega
          rw [hindex]
          exact hall
        exact ⟨row, hcurrent.trans hcurrentMap.symm,
          hnext.trans hnextMap.symm, hproperty⟩

theorem exists_checkedStepRow_at_binary_execution_offset
    {start leftStart rightStart beforeCombine finish :
      CompactNumericVerifierState}
    {leftSteps rightSteps : Nat}
    (rowProperty : CompactNumericVerifierCheckedStepRow -> Prop)
    (hrootStep : compactNumericVerifierStep start = leftStart)
    (hleftExecute :
      (compactNumericVerifierStep^[leftSteps]) leftStart = rightStart)
    (hrightExecute :
      (compactNumericVerifierStep^[rightSteps]) rightStart = beforeCombine)
    (hcombineStep : compactNumericVerifierStep beforeCombine = finish)
    (hrootRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = start /\ row.nextState = leftStart /\
        rowProperty row)
    (hleftRows : ∀ leftOffset, leftOffset < leftSteps →
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt leftStart leftOffset /\
          row.nextState =
            compactNumericVerifierStateAt leftStart (leftOffset + 1) /\
          rowProperty row)
    (hrightRows : ∀ rightOffset, rightOffset < rightSteps →
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState =
            compactNumericVerifierStateAt rightStart rightOffset /\
          row.nextState =
            compactNumericVerifierStateAt rightStart (rightOffset + 1) /\
          rowProperty row)
    (hcombineRow : exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = beforeCombine /\ row.nextState = finish /\
        rowProperty row)
    {offset : Nat}
    (hoffset : offset < 1 + leftSteps + rightSteps + 1) :
    exists row : CompactNumericVerifierCheckedStepRow,
      row.currentState = compactNumericVerifierStateAt start offset /\
        row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
        rowProperty row := by
  have hrootIterate :
      (compactNumericVerifierStep^[1]) start = leftStart := by
    simpa only [Function.iterate_one] using hrootStep
  have hthroughLeft := compactNumericVerifier_iterate_trans
    hrootIterate hleftExecute
  have hthroughRight := compactNumericVerifier_iterate_trans
    hthroughLeft hrightExecute
  cases offset with
  | zero =>
      rcases hrootRow with ⟨row, hcurrent, hnext, hproperty⟩
      refine ⟨row, ?_, ?_, hproperty⟩
      · simpa [compactNumericVerifierStateAt] using hcurrent
      · exact hnext.trans (by
          simpa [compactNumericVerifierStateAt, Function.iterate_one] using
            hrootStep.symm)
  | succ insideOffset =>
      by_cases hleft : insideOffset < leftSteps
      · rcases hleftRows insideOffset hleft with
          ⟨row, hcurrent, hnext, hproperty⟩
        have hcurrentMap :
            compactNumericVerifierStateAt start (Nat.succ insideOffset) =
              compactNumericVerifierStateAt leftStart insideOffset := by
          have hmap := compactNumericVerifierStateAt_add_of_iterate
            hrootIterate insideOffset
          have hindex : Nat.succ insideOffset = 1 + insideOffset := by omega
          rw [hindex]
          exact hmap
        have hnextMap :
            compactNumericVerifierStateAt start
                (Nat.succ insideOffset + 1) =
              compactNumericVerifierStateAt leftStart (insideOffset + 1) := by
          have hmap := compactNumericVerifierStateAt_add_of_iterate
            hrootIterate (insideOffset + 1)
          have hindex :
              Nat.succ insideOffset + 1 = 1 + (insideOffset + 1) := by omega
          rw [hindex]
          exact hmap
        exact ⟨row, hcurrent.trans hcurrentMap.symm,
          hnext.trans hnextMap.symm, hproperty⟩
      · by_cases hright : insideOffset < leftSteps + rightSteps
        · let rightOffset := insideOffset - leftSteps
          have hrightOffset : rightOffset < rightSteps := by
            dsimp only [rightOffset]
            omega
          have hoffsetSplit : insideOffset = leftSteps + rightOffset := by
            dsimp only [rightOffset]
            omega
          rcases hrightRows rightOffset hrightOffset with
            ⟨row, hcurrent, hnext, hproperty⟩
          have hcurrentMap :
              compactNumericVerifierStateAt start (Nat.succ insideOffset) =
                compactNumericVerifierStateAt rightStart rightOffset := by
            have hmap := compactNumericVerifierStateAt_add_of_iterate
              hthroughLeft rightOffset
            have hindex :
                Nat.succ insideOffset =
                  (1 + leftSteps) + rightOffset := by omega
            rw [hindex]
            exact hmap
          have hnextMap :
              compactNumericVerifierStateAt start
                  (Nat.succ insideOffset + 1) =
                compactNumericVerifierStateAt rightStart
                  (rightOffset + 1) := by
            have hmap := compactNumericVerifierStateAt_add_of_iterate
              hthroughLeft (rightOffset + 1)
            have hindex :
                Nat.succ insideOffset + 1 =
                  (1 + leftSteps) + (rightOffset + 1) := by omega
            rw [hindex]
            exact hmap
          exact ⟨row, hcurrent.trans hcurrentMap.symm,
            hnext.trans hnextMap.symm, hproperty⟩
        · have hoffsetEq : insideOffset = leftSteps + rightSteps := by
            omega
          subst insideOffset
          rcases hcombineRow with ⟨row, hcurrent, hnext, hproperty⟩
          have hcurrentMap :
              compactNumericVerifierStateAt start
                  (Nat.succ (leftSteps + rightSteps)) = beforeCombine := by
            unfold compactNumericVerifierStateAt
            have hindex :
                Nat.succ (leftSteps + rightSteps) =
                  (1 + leftSteps) + rightSteps := by omega
            rw [hindex]
            exact hthroughRight
          have hfinishIterate :
              (compactNumericVerifierStep^[1]) beforeCombine = finish := by
            simpa only [Function.iterate_one] using hcombineStep
          have hall := compactNumericVerifier_iterate_trans
            hthroughRight hfinishIterate
          have hnextMap :
              compactNumericVerifierStateAt start
                  (Nat.succ (leftSteps + rightSteps) + 1) = finish := by
            unfold compactNumericVerifierStateAt
            have hindex :
                Nat.succ (leftSteps + rightSteps) + 1 =
                  ((1 + leftSteps) + rightSteps) + 1 := by omega
            rw [hindex]
            exact hall
          exact ⟨row, hcurrent.trans hcurrentMap.symm,
            hnext.trans hnextMap.symm, hproperty⟩

#print axioms compactNumericVerifierStateAt_add_of_iterate
#print axioms compactNumericVerifierStateAt_weight_le_of_prefix
#print axioms exists_checkedStepRow_at_unary_execution_offset
#print axioms exists_checkedStepRow_at_binary_execution_offset

end FoundationCompactNumericListedDirectVerifierCheckedRowExecutionSplicing
