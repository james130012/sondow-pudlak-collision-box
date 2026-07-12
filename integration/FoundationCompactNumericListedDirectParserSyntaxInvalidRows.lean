import integration.FoundationCompactNumericListedDirectParserSyntaxTermRows

/-!
# Exact direct rows for an invalid syntax-task kind

The current task head is read by the canonical bounded uncons relation.  A kind
outside `0`, `1`, and `2` must leave the token stream untouched, pop exactly
that head, preserve the resulting tail, and enter the failed status.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxInvalidRows

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows

structure CompactSyntaxInvalidTaskWitnessCoordinates where
  tailBoundary : Nat
  tailCount : Nat
  tailBoundarySize : Nat
  kind : Nat
  binderArity : Nat
  repeatCount : Nat

def CompactSyntaxParserInvalidTaskCase
    (current next : CompactUnifiedParserState) : Prop :=
  current.2.2 = none ∧
    ∃ kind binderArity repeatCount tail,
      current.2.1 = (kind, binderArity, repeatCount) :: tail ∧
      kind ≠ 0 ∧ kind ≠ 1 ∧ kind ≠ 2 ∧
      next = compactSyntaxFailure current.1 tail

def CompactUnifiedParserSyntaxInvalidRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates) : Prop :=
  CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount current.tasksFinish current.finish ∧
    CompactAdditiveSyntaxTaskListUnconsRowsWithSize
      tokenTable width tokenCount
        current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize
        witness.kind witness.binderArity witness.repeatCount ∧
    witness.kind ≠ 0 ∧ witness.kind ≠ 1 ∧ witness.kind ≠ 2 ∧
    CompactUnifiedParserSyntaxTermFailureRows
      tokenTable width tokenCount current next
        witness.tailBoundary witness.tailCount

theorem compactUnifiedParserSyntaxInvalidRows_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    (∃ witness,
        CompactUnifiedParserSyntaxInvalidRows
          tokenTable width tokenCount currentCoordinates nextCoordinates
            witness) ↔
      CompactSyntaxParserInvalidTaskCase current next := by
  constructor
  · rintro ⟨witness, hcurrentRunning, huncons,
      hkindZero, hkindOne, hkindTwo, hfailureRows⟩
    have hcurrentStatus : current.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mp hcurrentRunning
    rcases huncons.realizes hcurrent.tasksCount_eq hcurrent.tasksRows with
      ⟨tail, htailRows, htailCount, hcurrentTasks⟩
    have hfailure :=
      (compactUnifiedParserSyntaxTermFailureRows_iff
        hcurrent hnext htailRows htailCount).mp hfailureRows
    exact ⟨hcurrentStatus, witness.kind, witness.binderArity,
      witness.repeatCount, tail, hcurrentTasks,
      hkindZero, hkindOne, hkindTwo, hfailure⟩
  · rintro ⟨hcurrentStatus, kind, binderArity, repeatCount, tail,
      hcurrentTasks, hkindZero, hkindOne, hkindTwo, hnextState⟩
    rcases
        (exists_compactAdditiveSyntaxTaskListUnconsRowsWithSize_iff
          hcurrent.tasksRows kind binderArity repeatCount).mpr
            ⟨tail, hcurrentTasks⟩ with
      ⟨tailBoundary, tailCount, tailBoundarySize, hunconsTyped⟩
    have huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize
        tokenTable width tokenCount
          currentCoordinates.tasksBoundary currentCoordinates.tasksCount
          tailBoundary tailCount tailBoundarySize
          kind binderArity repeatCount := by
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
    have hcurrentRunning : CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount
          currentCoordinates.tasksFinish currentCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mpr hcurrentStatus
    have hfailureRows :=
      (compactUnifiedParserSyntaxTermFailureRows_iff
        hcurrent hnext htailRows htailCount).mpr hnextState
    let witness : CompactSyntaxInvalidTaskWitnessCoordinates :=
      { tailBoundary := tailBoundary
        tailCount := tailCount
        tailBoundarySize := tailBoundarySize
        kind := kind
        binderArity := binderArity
        repeatCount := repeatCount }
    exact ⟨witness, hcurrentRunning, huncons,
      hkindZero, hkindOne, hkindTwo, hfailureRows⟩

#print axioms compactUnifiedParserSyntaxInvalidRows_iff

end FoundationCompactNumericListedDirectParserSyntaxInvalidRows
