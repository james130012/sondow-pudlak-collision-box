import integration.FoundationCompactNumericListedDirectParserStateFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusCases
import integration.FoundationCompactNumericListedDirectNatListSameRows
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRows

/-!
# Exact direct rows for the repeated-term syntax task

A running parser whose head task is `(2, binderArity, repeatCount)` preserves
its remaining token list.  At count zero it exposes the certified tail stack;
at positive count it pushes one term task and the decremented repeat task in
front of that same tail.  Both outcomes remain running.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatRows

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectParserStateFormula

structure CompactSyntaxRepeatTaskWitnessCoordinates where
  tailBoundary : Nat
  tailCount : Nat
  tailBoundarySize : Nat
  decrementedCount : Nat

private theorem list_eq_two_cons_of_getI_drop
    {α : Type*} [Inhabited α]
    {values : List α} {first second : α} {tail : List α}
    (hzero : 0 < values.length)
    (hone : 1 < values.length)
    (hfirst : values.getI 0 = first)
    (hsecond : values.getI 1 = second)
    (htail : tail = values.drop 2) :
    values = first :: second :: tail := by
  cases values with
  | nil => simp at hzero
  | cons actualFirst rest =>
      cases rest with
      | nil => simp at hone
      | cons actualSecond rest =>
          simp only [List.getI_cons_zero] at hfirst
          simp only [List.getI_cons_succ, List.getI_cons_zero] at hsecond
          simp only [List.drop_succ_cons, List.drop_zero] at htail
          subst actualFirst
          subst actualSecond
          subst tail
          rfl

def CompactSyntaxParserRepeatTaskCase
    (binderArity repeatCount : Nat)
    (current next : CompactUnifiedParserState) : Prop :=
  current.2.2 = none ∧
    ∃ tail,
      current.2.1 = (2, binderArity, repeatCount) :: tail ∧
      next = compactRepeatTermTokenStep
        ((2, binderArity, repeatCount), current.1, tail)

def CompactUnifiedParserSyntaxRepeatRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity repeatCount : Nat)
    (witness : CompactSyntaxRepeatTaskWitnessCoordinates) : Prop :=
  CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount current.tasksFinish current.finish ∧
    CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount next.tasksFinish next.finish ∧
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount
        current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount ∧
    CompactAdditiveSyntaxTaskListUnconsRowsWithSize
      tokenTable width tokenCount
        current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize
        2 binderArity repeatCount ∧
    ((repeatCount = 0 ∧
      CompactAdditiveSyntaxTaskListSameRows
        tokenTable width tokenCount
          witness.tailBoundary witness.tailCount
          next.tasksBoundary next.tasksCount) ∨
      (repeatCount = witness.decrementedCount + 1 ∧
        CompactAdditiveSyntaxTaskListDropRows
          tokenTable width tokenCount
            next.tasksBoundary next.tasksCount
            witness.tailBoundary witness.tailCount 2 ∧
        CompactAdditiveSyntaxTaskListAtRows
          tokenTable width tokenCount
            next.tasksBoundary next.tasksCount 0
            0 binderArity 0 ∧
        CompactAdditiveSyntaxTaskListAtRows
          tokenTable width tokenCount
            next.tasksBoundary next.tasksCount 1
            2 binderArity witness.decrementedCount))

theorem compactUnifiedParserSyntaxRepeatRows_iff
    {tokenTable width tokenCount binderArity repeatCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    (∃ witness,
        CompactUnifiedParserSyntaxRepeatRows
          tokenTable width tokenCount currentCoordinates nextCoordinates
            binderArity repeatCount witness) ↔
      CompactSyntaxParserRepeatTaskCase
        binderArity repeatCount current next := by
  constructor
  · rintro ⟨witness, hcurrentRunning, hnextRunning,
      htokenRows, huncons, hbranch⟩
    have hcurrentStatus : current.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mp hcurrentRunning
    have hnextStatus : next.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hnext.statusLayout).mp hnextRunning
    have htokenRows' : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary next.1.length := by
      simpa only [hcurrent.tokensCount_eq,
        hnext.tokensCount_eq] using htokenRows
    have htokens : next.1 = current.1 :=
      CompactAdditiveNatListSameRows.eq_of_rows
        htokenRows' hcurrent.tokensRows hnext.tokensRows
    rcases huncons.realizes hcurrent.tasksCount_eq hcurrent.tasksRows with
      ⟨tail, htailRows, htailCount, hcurrentTasks⟩
    refine ⟨hcurrentStatus, tail, hcurrentTasks, ?_⟩
    rcases hbranch with hzero | hpositive
    · rcases hzero with ⟨hrepeatZero, hsameRows⟩
      have hsameRows' : CompactAdditiveSyntaxTaskListSameRows
          tokenTable width tokenCount
            witness.tailBoundary tail.length
            nextCoordinates.tasksBoundary next.2.1.length := by
        simpa only [htailCount, hnext.tasksCount_eq] using hsameRows
      have hnextTasks : next.2.1 = tail :=
        CompactAdditiveSyntaxTaskListSameRows.eq_of_rows
          hsameRows' htailRows hnext.tasksRows
      have hnextState : next = (current.1, tail, none) := by
        rcases current with
          ⟨currentTokens, currentTasks, currentStatus⟩
        rcases next with ⟨nextTokens, nextTasks, nextStatus⟩
        simp only at htokens hnextTasks hnextStatus ⊢
        simp [htokens, hnextTasks, hnextStatus]
      rw [hnextState]
      simp [compactRepeatTermTokenStep, hrepeatZero,
        compactSyntaxContinue]
    · rcases hpositive with
        ⟨hrepeatSuccessor, hdropRows, htaskZero, htaskOne⟩
      have hdecremented : witness.decrementedCount = repeatCount - 1 := by
        omega
      have hdropRows' : CompactAdditiveSyntaxTaskListDropRows
          tokenTable width tokenCount
            nextCoordinates.tasksBoundary next.2.1.length
            witness.tailBoundary tail.length 2 := by
        simpa only [hnext.tasksCount_eq, htailCount] using hdropRows
      have htailEq : tail = next.2.1.drop 2 :=
        hdropRows'.eq_drop_of_rows hnext.tasksRows htailRows
      have htaskZero' :=
        (compactAdditiveSyntaxTaskListAtRows_iff_getI
          hnext.tasksRows 0 0 binderArity 0).mp (by
            simpa only [hnext.tasksCount_eq] using htaskZero)
      have htaskOneRaw :=
        (compactAdditiveSyntaxTaskListAtRows_iff_getI
          hnext.tasksRows 1 2 binderArity witness.decrementedCount).mp (by
            simpa only [hnext.tasksCount_eq] using htaskOne)
      have htaskOne' : 1 < next.2.1.length ∧
          next.2.1.getI 1 = (2, binderArity, repeatCount - 1) := by
        simpa only [hdecremented] using htaskOneRaw
      have hnextTasks : next.2.1 =
          (0, binderArity, 0) ::
            (2, binderArity, repeatCount - 1) :: tail := by
        exact list_eq_two_cons_of_getI_drop
          htaskZero'.1 htaskOne'.1
          htaskZero'.2 htaskOne'.2 htailEq
      have hnextState : next =
          (current.1,
            (0, binderArity, 0) ::
              (2, binderArity, repeatCount - 1) :: tail,
            none) := by
        rcases current with
          ⟨currentTokens, currentTasks, currentStatus⟩
        rcases next with ⟨nextTokens, nextTasks, nextStatus⟩
        simp only at htokens hnextTasks hnextStatus ⊢
        simp [htokens, hnextTasks, hnextStatus]
      have hrepeatNonzero : repeatCount ≠ 0 := by omega
      rw [hnextState]
      simp [compactRepeatTermTokenStep, hrepeatNonzero,
        compactSyntaxContinue, compactTermTask, compactRepeatTermTask]
  · rintro ⟨hcurrentStatus, tail, hcurrentTasks, hnextStep⟩
    rcases
        (exists_compactAdditiveSyntaxTaskListUnconsRowsWithSize_iff
          hcurrent.tasksRows 2 binderArity repeatCount).mpr
            ⟨tail, hcurrentTasks⟩ with
      ⟨tailBoundary, tailCount, tailBoundarySize, hunconsTyped⟩
    have huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize
        tokenTable width tokenCount
          currentCoordinates.tasksBoundary currentCoordinates.tasksCount
          tailBoundary tailCount tailBoundarySize
          2 binderArity repeatCount := by
      simpa only [hcurrent.tasksCount_eq] using hunconsTyped
    rcases huncons.realizes hcurrent.tasksCount_eq hcurrent.tasksRows with
      ⟨realizedTail, hrealizedTailRows,
        hrealizedTailCount, hrealizedCurrentTasks⟩
    have hrealizedTailEq : realizedTail = tail :=
      (List.cons.inj (hrealizedCurrentTasks.symm.trans hcurrentTasks)).2
    have htailRows : CompactAdditiveStructuredListElementRowLayouts
        CompactSyntaxTaskDirectLayout tokenTable width tokenCount
          tailBoundary tail := by
      simpa only [hrealizedTailEq] using hrealizedTailRows
    have htailCount : tail.length = tailCount := by
      simpa only [hrealizedTailEq] using hrealizedTailCount
    let witness : CompactSyntaxRepeatTaskWitnessCoordinates :=
      { tailBoundary := tailBoundary
        tailCount := tailCount
        tailBoundarySize := tailBoundarySize
        decrementedCount := repeatCount - 1 }
    by_cases hrepeatZero : repeatCount = 0
    · have hnextState : next = (current.1, tail, none) := by
        simpa [compactRepeatTermTokenStep, hrepeatZero,
          compactSyntaxContinue] using hnextStep
      have hnextLayout : CompactUnifiedParserStateFixedLayout
          tokenTable width tokenCount nextCoordinates
            (current.1, tail, none) := by
        simpa only [hnextState] using hnext
      have hcurrentRunning : CompactBinaryNatRunningStatusSlice
          tokenTable width tokenCount
            currentCoordinates.tasksFinish currentCoordinates.finish :=
        (CompactBinaryNatStreamStatusDirectLayout.running_iff
          hcurrent.statusLayout).mpr hcurrentStatus
      have hnextRunning : CompactBinaryNatRunningStatusSlice
          tokenTable width tokenCount
            nextCoordinates.tasksFinish nextCoordinates.finish :=
        (CompactBinaryNatStreamStatusDirectLayout.running_iff
          hnextLayout.statusLayout).mpr rfl
      have htokenRows : CompactAdditiveNatListSameRows
          tokenTable width tokenCount
            currentCoordinates.tokensBoundary current.1.length
            nextCoordinates.tokensBoundary current.1.length :=
        CompactAdditiveStructuredListElementRowLayouts.natSameRows
          hcurrent.tokensRows hnextLayout.tokensRows rfl
      have htaskRows : CompactAdditiveSyntaxTaskListSameRows
          tokenTable width tokenCount
            tailBoundary tail.length
            nextCoordinates.tasksBoundary tail.length :=
        CompactAdditiveStructuredListElementRowLayouts.taskSameRows
          htailRows hnextLayout.tasksRows rfl
      refine ⟨witness, hcurrentRunning, hnextRunning, ?_, huncons,
        Or.inl ⟨hrepeatZero, ?_⟩⟩
      · simpa only [hcurrent.tokensCount_eq,
          hnextLayout.tokensCount_eq] using htokenRows
      · simpa only [htailCount,
          hnextLayout.tasksCount_eq] using htaskRows
    · have hnextState : next =
          (current.1,
            (0, binderArity, 0) ::
              (2, binderArity, repeatCount - 1) :: tail,
            none) := by
        simpa [compactRepeatTermTokenStep, hrepeatZero,
          compactSyntaxContinue, compactTermTask,
          compactRepeatTermTask] using hnextStep
      have hnextLayout : CompactUnifiedParserStateFixedLayout
          tokenTable width tokenCount nextCoordinates
            (current.1,
              (0, binderArity, 0) ::
                (2, binderArity, repeatCount - 1) :: tail,
              none) := by
        simpa only [hnextState] using hnext
      have hcurrentRunning : CompactBinaryNatRunningStatusSlice
          tokenTable width tokenCount
            currentCoordinates.tasksFinish currentCoordinates.finish :=
        (CompactBinaryNatStreamStatusDirectLayout.running_iff
          hcurrent.statusLayout).mpr hcurrentStatus
      have hnextRunning : CompactBinaryNatRunningStatusSlice
          tokenTable width tokenCount
            nextCoordinates.tasksFinish nextCoordinates.finish :=
        (CompactBinaryNatStreamStatusDirectLayout.running_iff
          hnextLayout.statusLayout).mpr rfl
      have htokenRows : CompactAdditiveNatListSameRows
          tokenTable width tokenCount
            currentCoordinates.tokensBoundary current.1.length
            nextCoordinates.tokensBoundary current.1.length :=
        CompactAdditiveStructuredListElementRowLayouts.natSameRows
          hcurrent.tokensRows hnextLayout.tokensRows rfl
      have hdropRows : CompactAdditiveSyntaxTaskListDropRows
          tokenTable width tokenCount
            nextCoordinates.tasksBoundary
              ((0, binderArity, 0) ::
                (2, binderArity, repeatCount - 1) :: tail).length
            tailBoundary tail.length 2 :=
        CompactAdditiveStructuredListElementRowLayouts.taskDropRows
          hnextLayout.tasksRows htailRows (by simp)
          (by simp)
      have htaskZero : CompactAdditiveSyntaxTaskListAtRows
          tokenTable width tokenCount
            nextCoordinates.tasksBoundary
              ((0, binderArity, 0) ::
                (2, binderArity, repeatCount - 1) :: tail).length 0
            0 binderArity 0 :=
        (compactAdditiveSyntaxTaskListAtRows_iff_getI
          hnextLayout.tasksRows 0 0 binderArity 0).mpr (by simp)
      have htaskOne : CompactAdditiveSyntaxTaskListAtRows
          tokenTable width tokenCount
            nextCoordinates.tasksBoundary
              ((0, binderArity, 0) ::
                (2, binderArity, repeatCount - 1) :: tail).length 1
            2 binderArity (repeatCount - 1) :=
        (compactAdditiveSyntaxTaskListAtRows_iff_getI
          hnextLayout.tasksRows 1 2 binderArity
            (repeatCount - 1)).mpr (by simp)
      refine ⟨witness, hcurrentRunning, hnextRunning, ?_, huncons,
        Or.inr ⟨by dsimp [witness]; omega, ?_, ?_, ?_⟩⟩
      · simpa only [hcurrent.tokensCount_eq,
          hnextLayout.tokensCount_eq] using htokenRows
      · simpa only [hnextLayout.tasksCount_eq,
          htailCount] using hdropRows
      · simpa only [hnextLayout.tasksCount_eq] using htaskZero
      · simpa only [hnextLayout.tasksCount_eq, witness] using htaskOne

#print axioms compactUnifiedParserSyntaxRepeatRows_iff

end FoundationCompactNumericListedDirectParserSyntaxRepeatRows
