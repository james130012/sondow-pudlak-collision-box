import integration.FoundationCompactNumericListedDirectParserStepCases
import integration.FoundationCompactNumericListedDirectParserStateFormula
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRows
import integration.FoundationCompactNumericListedDirectNatListSameRows
import integration.FoundationCompactNumericListedDirectCompletedStatusSameRows

/-!
# Exact direct rows for an already finished parser state

The remaining-token list and task stack are compared row by row.  The nested
status is either failed on both sides or completed with the same output list.
Under fixed parser-state layouts this direct relation is exactly the outer
parser case saying that the current status is finished and `next = current`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserDoneRows

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectParserStateFormula

def CompactUnifiedParserStepDoneCase
    (current next : CompactUnifiedParserState) : Prop :=
  ∃ result, current.2.2 = some result ∧ next = current

def CompactUnifiedParserCompletedStatusSameRowsExists
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish : Nat) : Prop :=
  ∃ sourceOutputStart sourceOutputBoundary
      targetOutputStart targetOutputBoundary outputCount,
    CompactBinaryNatCompletedStatusSameRows
      tokenTable width tokenCount
        sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish
        sourceOutputStart sourceOutputBoundary
        targetOutputStart targetOutputBoundary outputCount

def CompactUnifiedParserDoneRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates) : Prop :=
  CompactAdditiveNatListSameRows
      tokenTable width tokenCount
        current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount ∧
    CompactAdditiveSyntaxTaskListSameRows
      tokenTable width tokenCount
        current.tasksBoundary current.tasksCount
        next.tasksBoundary next.tasksCount ∧
    ((CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount current.tasksFinish current.finish ∧
      CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount next.tasksFinish next.finish) ∨
      CompactUnifiedParserCompletedStatusSameRowsExists
        tokenTable width tokenCount
          current.tasksFinish current.finish
          next.tasksFinish next.finish)

theorem compactUnifiedParserStepDoneCase_iff_outer_done
    (current next : CompactUnifiedParserState) :
    CompactUnifiedParserStepDoneCase current next ↔
      current.2.2.isSome = true ∧ next = current := by
  rcases current with ⟨tokens, tasks, status⟩
  cases status <;> simp [CompactUnifiedParserStepDoneCase]

theorem compactUnifiedParserDoneRows_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    CompactUnifiedParserDoneRows
        tokenTable width tokenCount currentCoordinates nextCoordinates ↔
      CompactUnifiedParserStepDoneCase current next := by
  constructor
  · rintro ⟨htokensRows, htasksRows, hstatusRows⟩
    have htokensRows' : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary next.1.length := by
      simpa only [hcurrent.tokensCount_eq,
        hnext.tokensCount_eq] using htokensRows
    have htokens : next.1 = current.1 :=
      CompactAdditiveNatListSameRows.eq_of_rows
        htokensRows' hcurrent.tokensRows hnext.tokensRows
    have htasksRows' : CompactAdditiveSyntaxTaskListSameRows
        tokenTable width tokenCount
          currentCoordinates.tasksBoundary current.2.1.length
          nextCoordinates.tasksBoundary next.2.1.length := by
      simpa only [hcurrent.tasksCount_eq,
        hnext.tasksCount_eq] using htasksRows
    have htasks : next.2.1 = current.2.1 :=
      CompactAdditiveSyntaxTaskListSameRows.eq_of_rows
        htasksRows' hcurrent.tasksRows hnext.tasksRows
    rcases hstatusRows with hfailed | hcompleted
    · have hcurrentStatus : current.2.2 = some none :=
        (CompactBinaryNatStreamStatusDirectLayout.failed_iff
          hcurrent.statusLayout).mp hfailed.1
      have hnextStatus : next.2.2 = some none :=
        (CompactBinaryNatStreamStatusDirectLayout.failed_iff
          hnext.statusLayout).mp hfailed.2
      have hstate : next = current := by
        rcases current with
          ⟨currentTokens, currentTasks, currentStatus⟩
        rcases next with ⟨nextTokens, nextTasks, nextStatus⟩
        simp only at htokens htasks hcurrentStatus hnextStatus ⊢
        simp [htokens, htasks, hcurrentStatus, hnextStatus]
      exact ⟨none, hcurrentStatus, hstate⟩
    · rcases
          (completedStatusSameRows_iff
            hcurrent.statusLayout hnext.statusLayout).mp hcompleted with
        ⟨output, hcurrentStatus, hnextStatus⟩
      have hstate : next = current := by
        rcases current with
          ⟨currentTokens, currentTasks, currentStatus⟩
        rcases next with ⟨nextTokens, nextTasks, nextStatus⟩
        simp only at htokens htasks hcurrentStatus hnextStatus ⊢
        simp [htokens, htasks, hcurrentStatus, hnextStatus]
      exact ⟨some output, hcurrentStatus, hstate⟩
  · rintro ⟨result, hcurrentStatus, hstate⟩
    subst next
    have htokensRows : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary current.1.length :=
      CompactAdditiveStructuredListElementRowLayouts.natSameRows
        hcurrent.tokensRows hnext.tokensRows rfl
    have htasksRows : CompactAdditiveSyntaxTaskListSameRows
        tokenTable width tokenCount
          currentCoordinates.tasksBoundary current.2.1.length
          nextCoordinates.tasksBoundary current.2.1.length :=
      CompactAdditiveStructuredListElementRowLayouts.taskSameRows
        hcurrent.tasksRows hnext.tasksRows rfl
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hcurrent.tokensCount_eq,
        hnext.tokensCount_eq] using htokensRows
    · simpa only [hcurrent.tasksCount_eq,
        hnext.tasksCount_eq] using htasksRows
    · cases result with
      | none =>
          left
          exact
            ⟨(CompactBinaryNatStreamStatusDirectLayout.failed_iff
                hcurrent.statusLayout).mpr hcurrentStatus,
              (CompactBinaryNatStreamStatusDirectLayout.failed_iff
                hnext.statusLayout).mpr hcurrentStatus⟩
      | some output =>
          right
          exact (completedStatusSameRows_iff
            hcurrent.statusLayout hnext.statusLayout).mpr
              ⟨output, hcurrentStatus, hcurrentStatus⟩

#print axioms compactUnifiedParserStepDoneCase_iff_outer_done
#print axioms compactUnifiedParserDoneRows_iff

end FoundationCompactNumericListedDirectParserDoneRows
