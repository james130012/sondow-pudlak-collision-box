import integration.FoundationCompactNumericListedDirectParserStepCases
import integration.FoundationCompactNumericListedDirectParserStateFormula
import integration.FoundationCompactNumericListedDirectNatListSameRows
import integration.FoundationCompactNumericListedDirectCompletedOutputSameRows

/-!
# Exact direct rows for parser completion with an empty task stack

A running parser with no remaining task completes by returning its remaining
token list.  The current and next token rows are compared directly, both task
counts are forced to zero, and the next completed status output is tied to the
current token rows through the rigid completed-output equality relation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserEmptyRows

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectCompletedOutputSameRows
open FoundationCompactNumericListedDirectParserStateFormula

def CompactUnifiedParserStepEmptyCase
    (current next : CompactUnifiedParserState) : Prop :=
  current.2.2 = none ∧
    current.2.1 = [] ∧
    next = (current.1, [], some (some current.1))

def CompactUnifiedParserCompletedOutputSameRowsExists
    (tokenTable width tokenCount statusStart statusFinish
      sourceBoundary sourceCount : Nat) : Prop :=
  ∃ outputStart outputBoundary,
    CompactBinaryNatCompletedOutputSameRows
      tokenTable width tokenCount statusStart statusFinish
        sourceBoundary sourceCount outputStart outputBoundary

def CompactUnifiedParserEmptyRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates) : Prop :=
  current.tasksCount = 0 ∧
    next.tasksCount = 0 ∧
    CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount current.tasksFinish current.finish ∧
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount
        current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount ∧
    CompactUnifiedParserCompletedOutputSameRowsExists
      tokenTable width tokenCount next.tasksFinish next.finish
        current.tokensBoundary current.tokensCount

theorem compactUnifiedParserEmptyRows_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    CompactUnifiedParserEmptyRows
        tokenTable width tokenCount currentCoordinates nextCoordinates ↔
      CompactUnifiedParserStepEmptyCase current next := by
  constructor
  · rintro ⟨hcurrentTaskCount, hnextTaskCount, hcurrentRunning,
      htokenRows, hcompleted⟩
    have hcurrentTasks : current.2.1 = [] :=
      List.eq_nil_of_length_eq_zero
        (hcurrent.tasksCount_eq.symm.trans hcurrentTaskCount)
    have hnextTasks : next.2.1 = [] :=
      List.eq_nil_of_length_eq_zero
        (hnext.tasksCount_eq.symm.trans hnextTaskCount)
    have hcurrentStatus : current.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mp hcurrentRunning
    have htokenRows' : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary next.1.length := by
      simpa only [hcurrent.tokensCount_eq,
        hnext.tokensCount_eq] using htokenRows
    have htokens : next.1 = current.1 :=
      CompactAdditiveNatListSameRows.eq_of_rows
        htokenRows' hcurrent.tokensRows hnext.tokensRows
    have hnextStatus : next.2.2 = some (some current.1) :=
      (completedOutputSameRows_iff
        hcurrent.tokensRows hnext.statusLayout).mp (by
          simpa only [CompactUnifiedParserCompletedOutputSameRowsExists,
            hcurrent.tokensCount_eq] using hcompleted)
    refine ⟨hcurrentStatus, hcurrentTasks, ?_⟩
    rcases current with
      ⟨currentTokens, currentTasks, currentStatus⟩
    rcases next with ⟨nextTokens, nextTasks, nextStatus⟩
    simp only at hcurrentTasks hnextTasks htokens hnextStatus ⊢
    simp [hnextTasks, htokens, hnextStatus]
  · rintro ⟨hcurrentStatus, hcurrentTasks, hstate⟩
    subst next
    have hcurrentTaskCount : currentCoordinates.tasksCount = 0 := by
      simpa [hcurrentTasks] using hcurrent.tasksCount_eq
    have hnextTaskCount : nextCoordinates.tasksCount = 0 := by
      simpa using hnext.tasksCount_eq
    have hcurrentRunning : CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount
          currentCoordinates.tasksFinish currentCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mpr hcurrentStatus
    have htokenRows : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary current.1.length :=
      CompactAdditiveStructuredListElementRowLayouts.natSameRows
        hcurrent.tokensRows hnext.tokensRows rfl
    have hcompleted : CompactUnifiedParserCompletedOutputSameRowsExists
        tokenTable width tokenCount
          nextCoordinates.tasksFinish nextCoordinates.finish
          currentCoordinates.tokensBoundary current.1.length :=
      (completedOutputSameRows_iff
        hcurrent.tokensRows hnext.statusLayout).mpr rfl
    refine ⟨hcurrentTaskCount, hnextTaskCount,
      hcurrentRunning, ?_, ?_⟩
    · simpa only [hcurrent.tokensCount_eq,
        hnext.tokensCount_eq] using htokenRows
    · simpa only [hcurrent.tokensCount_eq] using hcompleted

#print axioms compactUnifiedParserEmptyRows_iff

end FoundationCompactNumericListedDirectParserEmptyRows
