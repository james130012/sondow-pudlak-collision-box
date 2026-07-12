import integration.FoundationCompactNumericListedDirectParserStateFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusCases
import integration.FoundationCompactNumericListedDirectNatListSameRows
import integration.FoundationCompactNumericListedDirectNatListDropRows
import integration.FoundationCompactNumericListedDirectNatListAtRows
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows

/-!
# Exact direct rows for the syntax term task

The relation below expands every branch of `compactTermTokenStep`: short input,
bound and free variables, valid function symbols, and all rejection cases.  It
uses only exact token-row lookup, exact suffix rows, and exact task-stack row
operations on the public parser-state coordinates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxTermRows

open FoundationCompactArithmeticSymbolCode
open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectParserStateFormula

structure CompactSyntaxTermTaskWitnessCoordinates where
  tailBoundary : Nat
  tailCount : Nat
  tailBoundarySize : Nat
  tag : Nat
  argument : Nat
  functionCode : Nat

theorem compactTokenAt_eq_getI
    (index : Nat) (tokens : List Nat) :
    compactTokenAt index tokens = tokens.getI index := by
  simpa [compactTokenAt] using
    (List.getI_eq_getElem?_getD (l := tokens) index).symm

def CompactSyntaxParserTermTaskCase
    (binderArity : Nat)
    (current next : CompactUnifiedParserState) : Prop :=
  current.2.2 = none ∧
    ∃ tail,
      current.2.1 = (0, binderArity, 0) :: tail ∧
      next = compactTermTokenStep (binderArity, current.1, tail)

def CompactUnifiedParserSyntaxTermFailureRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat) : Prop :=
  CompactBinaryNatFailedStatusSlice
      tokenTable width tokenCount next.tasksFinish next.finish ∧
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount
        current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount ∧
    CompactAdditiveSyntaxTaskListSameRows
      tokenTable width tokenCount
        tailBoundary tailCount next.tasksBoundary next.tasksCount

def CompactUnifiedParserSyntaxTermContinueRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount consumed : Nat) : Prop :=
  CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount next.tasksFinish next.finish ∧
    CompactAdditiveNatListDropRows
      tokenTable width tokenCount
        current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount consumed ∧
    CompactAdditiveSyntaxTaskListSameRows
      tokenTable width tokenCount
        tailBoundary tailCount next.tasksBoundary next.tasksCount

def CompactUnifiedParserSyntaxTermFunctionRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity : Nat) : Prop :=
  CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount next.tasksFinish next.finish ∧
    CompactAdditiveNatListDropRows
      tokenTable width tokenCount
        current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount 3 ∧
    CompactAdditiveSyntaxTaskListConsRows
      tokenTable width tokenCount
        tailBoundary tailCount next.tasksBoundary next.tasksCount
        2 binderArity functionArity

theorem compactUnifiedParserSyntaxTermFailureRows_iff
    {tokenTable width tokenCount tailBoundary tailCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    {tail : List CompactSyntaxTask}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (htailRows : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        tailBoundary tail)
    (htailCount : tail.length = tailCount) :
    CompactUnifiedParserSyntaxTermFailureRows
        tokenTable width tokenCount currentCoordinates nextCoordinates
          tailBoundary tailCount ↔
      next = compactSyntaxFailure current.1 tail := by
  constructor
  · rintro ⟨hfailed, htokenRows, htaskRows⟩
    have hnextStatus : next.2.2 = some none :=
      (CompactBinaryNatStreamStatusDirectLayout.failed_iff
        hnext.statusLayout).mp hfailed
    have htokenRows' : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary next.1.length := by
      simpa only [hcurrent.tokensCount_eq,
        hnext.tokensCount_eq] using htokenRows
    have htokens : next.1 = current.1 :=
      CompactAdditiveNatListSameRows.eq_of_rows
        htokenRows' hcurrent.tokensRows hnext.tokensRows
    have htaskRows' : CompactAdditiveSyntaxTaskListSameRows
        tokenTable width tokenCount
          tailBoundary tail.length
          nextCoordinates.tasksBoundary next.2.1.length := by
      simpa only [htailCount, hnext.tasksCount_eq] using htaskRows
    have htasks : next.2.1 = tail :=
      CompactAdditiveSyntaxTaskListSameRows.eq_of_rows
        htaskRows' htailRows hnext.tasksRows
    rcases current with ⟨currentTokens, currentTasks, currentStatus⟩
    rcases next with ⟨nextTokens, nextTasks, nextStatus⟩
    simp only at hnextStatus htokens htasks ⊢
    simp [compactSyntaxFailure, hnextStatus, htokens, htasks]
  · intro hnextState
    have hnextLayout : CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount nextCoordinates
          (current.1, tail, some none) := by
      simpa [compactSyntaxFailure, hnextState] using hnext
    have hfailed : CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount
          nextCoordinates.tasksFinish nextCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.failed_iff
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
    refine ⟨hfailed, ?_, ?_⟩
    · simpa only [hcurrent.tokensCount_eq,
        hnextLayout.tokensCount_eq] using htokenRows
    · simpa only [htailCount,
        hnextLayout.tasksCount_eq] using htaskRows

theorem compactUnifiedParserSyntaxTermContinueRows_iff
    {tokenTable width tokenCount tailBoundary tailCount consumed : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    {tail : List CompactSyntaxTask}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (htailRows : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        tailBoundary tail)
    (htailCount : tail.length = tailCount) :
    CompactUnifiedParserSyntaxTermContinueRows
        tokenTable width tokenCount currentCoordinates nextCoordinates
          tailBoundary tailCount consumed ↔
      consumed ≤ current.1.length ∧
        next = compactSyntaxContinue (current.1.drop consumed) tail := by
  constructor
  · rintro ⟨hrunning, htokenRows, htaskRows⟩
    have hnextStatus : next.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hnext.statusLayout).mp hrunning
    have htokenRows' : CompactAdditiveNatListDropRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary next.1.length consumed := by
      simpa only [hcurrent.tokensCount_eq,
        hnext.tokensCount_eq] using htokenRows
    have htokens : next.1 = current.1.drop consumed :=
      htokenRows'.eq_drop_of_rows hcurrent.tokensRows hnext.tokensRows
    have htaskRows' : CompactAdditiveSyntaxTaskListSameRows
        tokenTable width tokenCount
          tailBoundary tail.length
          nextCoordinates.tasksBoundary next.2.1.length := by
      simpa only [htailCount, hnext.tasksCount_eq] using htaskRows
    have htasks : next.2.1 = tail :=
      CompactAdditiveSyntaxTaskListSameRows.eq_of_rows
        htaskRows' htailRows hnext.tasksRows
    refine ⟨htokenRows'.1, ?_⟩
    rcases current with ⟨currentTokens, currentTasks, currentStatus⟩
    rcases next with ⟨nextTokens, nextTasks, nextStatus⟩
    simp only at hnextStatus htokens htasks ⊢
    simp [compactSyntaxContinue, hnextStatus, htokens, htasks]
  · rintro ⟨hconsumed, hnextState⟩
    have hnextLayout : CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount nextCoordinates
          (current.1.drop consumed, tail, none) := by
      simpa [compactSyntaxContinue, hnextState] using hnext
    have hrunning : CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount
          nextCoordinates.tasksFinish nextCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hnextLayout.statusLayout).mpr rfl
    have htokenRows : CompactAdditiveNatListDropRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary (current.1.drop consumed).length
          consumed :=
      CompactAdditiveStructuredListElementRowLayouts.natDropRows
        hcurrent.tokensRows hnextLayout.tokensRows hconsumed rfl
    have htaskRows : CompactAdditiveSyntaxTaskListSameRows
        tokenTable width tokenCount
          tailBoundary tail.length
          nextCoordinates.tasksBoundary tail.length :=
      CompactAdditiveStructuredListElementRowLayouts.taskSameRows
        htailRows hnextLayout.tasksRows rfl
    refine ⟨hrunning, ?_, ?_⟩
    · simpa only [hcurrent.tokensCount_eq,
        hnextLayout.tokensCount_eq] using htokenRows
    · simpa only [htailCount,
        hnextLayout.tasksCount_eq] using htaskRows

theorem compactUnifiedParserSyntaxTermFunctionRows_iff
    {tokenTable width tokenCount tailBoundary tailCount
      binderArity functionArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    {tail : List CompactSyntaxTask}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (htailRows : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        tailBoundary tail)
    (htailCount : tail.length = tailCount) :
    CompactUnifiedParserSyntaxTermFunctionRows
        tokenTable width tokenCount currentCoordinates nextCoordinates
          tailBoundary tailCount binderArity functionArity ↔
      3 ≤ current.1.length ∧
        next = compactSyntaxContinue (current.1.drop 3)
          ((2, binderArity, functionArity) :: tail) := by
  constructor
  · rintro ⟨hrunning, htokenRows, htaskRows⟩
    have hnextStatus : next.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hnext.statusLayout).mp hrunning
    have htokenRows' : CompactAdditiveNatListDropRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary next.1.length 3 := by
      simpa only [hcurrent.tokensCount_eq,
        hnext.tokensCount_eq] using htokenRows
    have htokens : next.1 = current.1.drop 3 :=
      htokenRows'.eq_drop_of_rows hcurrent.tokensRows hnext.tokensRows
    have htaskRows' : CompactAdditiveSyntaxTaskListConsRows
        tokenTable width tokenCount
          tailBoundary tail.length
          nextCoordinates.tasksBoundary next.2.1.length
          2 binderArity functionArity := by
      simpa only [htailCount, hnext.tasksCount_eq] using htaskRows
    have htasks : next.2.1 = (2, binderArity, functionArity) :: tail :=
      htaskRows'.eq_cons_of_rows htailRows hnext.tasksRows
    refine ⟨htokenRows'.1, ?_⟩
    rcases current with ⟨currentTokens, currentTasks, currentStatus⟩
    rcases next with ⟨nextTokens, nextTasks, nextStatus⟩
    simp only at hnextStatus htokens htasks ⊢
    simp [compactSyntaxContinue, hnextStatus, htokens, htasks]
  · rintro ⟨hconsumed, hnextState⟩
    have hnextLayout : CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount nextCoordinates
          (current.1.drop 3,
            (2, binderArity, functionArity) :: tail, none) := by
      simpa [compactSyntaxContinue, hnextState] using hnext
    have hrunning : CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount
          nextCoordinates.tasksFinish nextCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hnextLayout.statusLayout).mpr rfl
    have htokenRows : CompactAdditiveNatListDropRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary (current.1.drop 3).length 3 :=
      CompactAdditiveStructuredListElementRowLayouts.natDropRows
        hcurrent.tokensRows hnextLayout.tokensRows hconsumed rfl
    have htaskRows : CompactAdditiveSyntaxTaskListConsRows
        tokenTable width tokenCount
          tailBoundary tail.length
          nextCoordinates.tasksBoundary
            ((2, binderArity, functionArity) :: tail).length
          2 binderArity functionArity :=
      CompactAdditiveStructuredListElementRowLayouts.taskConsRows
        htailRows hnextLayout.tasksRows rfl
    refine ⟨hrunning, ?_, ?_⟩
    · simpa only [hcurrent.tokensCount_eq,
        hnextLayout.tokensCount_eq] using htokenRows
    · simpa only [htailCount,
        hnextLayout.tasksCount_eq] using htaskRows

def CompactUnifiedParserSyntaxTermRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : Prop :=
  CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount current.tasksFinish current.finish ∧
    CompactAdditiveSyntaxTaskListUnconsRowsWithSize
      tokenTable width tokenCount
        current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize
        0 binderArity 0 ∧
    ((current.tokensCount ≤ 1 ∧
      CompactUnifiedParserSyntaxTermFailureRows
        tokenTable width tokenCount current next
          witness.tailBoundary witness.tailCount) ∨
     (2 ≤ current.tokensCount ∧
      CompactAdditiveNatListAtRows
        tokenTable width tokenCount
          current.tokensBoundary current.tokensCount 0 witness.tag ∧
      CompactAdditiveNatListAtRows
        tokenTable width tokenCount
          current.tokensBoundary current.tokensCount 1 witness.argument ∧
      (((witness.tag = 0 ∧ witness.argument < binderArity ∧
          CompactUnifiedParserSyntaxTermContinueRows
            tokenTable width tokenCount current next
              witness.tailBoundary witness.tailCount 2) ∨
        (witness.tag = 0 ∧ binderArity ≤ witness.argument ∧
          CompactUnifiedParserSyntaxTermFailureRows
            tokenTable width tokenCount current next
              witness.tailBoundary witness.tailCount)) ∨
       (witness.tag = 1 ∧
          CompactUnifiedParserSyntaxTermContinueRows
            tokenTable width tokenCount current next
              witness.tailBoundary witness.tailCount 2) ∨
       (witness.tag = 2 ∧
          ((current.tokensCount ≤ 2 ∧
            CompactUnifiedParserSyntaxTermFailureRows
              tokenTable width tokenCount current next
                witness.tailBoundary witness.tailCount) ∨
           (3 ≤ current.tokensCount ∧
            CompactAdditiveNatListAtRows
              tokenTable width tokenCount
                current.tokensBoundary current.tokensCount
                2 witness.functionCode ∧
            ((ArithmeticFuncCodeValid
                witness.argument witness.functionCode ∧
              CompactUnifiedParserSyntaxTermFunctionRows
                tokenTable width tokenCount current next
                  witness.tailBoundary witness.tailCount
                  binderArity witness.argument) ∨
             (¬ ArithmeticFuncCodeValid
                witness.argument witness.functionCode ∧
              CompactUnifiedParserSyntaxTermFailureRows
                tokenTable width tokenCount current next
                  witness.tailBoundary witness.tailCount))))) ∨
       (witness.tag ≠ 0 ∧ witness.tag ≠ 1 ∧ witness.tag ≠ 2 ∧
          CompactUnifiedParserSyntaxTermFailureRows
            tokenTable width tokenCount current next
              witness.tailBoundary witness.tailCount))))

theorem compactUnifiedParserSyntaxTermRows_iff
    {tokenTable width tokenCount binderArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    (∃ witness,
        CompactUnifiedParserSyntaxTermRows
          tokenTable width tokenCount currentCoordinates nextCoordinates
            binderArity witness) ↔
      CompactSyntaxParserTermTaskCase binderArity current next := by
  constructor
  · rintro ⟨witness, hcurrentRunning, huncons, hbranch⟩
    have hcurrentStatus : current.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mp hcurrentRunning
    rcases huncons.realizes hcurrent.tasksCount_eq hcurrent.tasksRows with
      ⟨tail, htailRows, htailCount, hcurrentTasks⟩
    refine ⟨hcurrentStatus, tail, hcurrentTasks, ?_⟩
    rcases hbranch with hshort | henough
    · have hlength : ¬ 2 ≤ current.1.length := by
        have hshortCount : current.1.length ≤ 1 := by
          simpa only [hcurrent.tokensCount_eq] using hshort.1
        omega
      have hfailure :=
        (compactUnifiedParserSyntaxTermFailureRows_iff
          hcurrent hnext htailRows htailCount).mp hshort.2
      simpa [compactTermTokenStep, hlength] using hfailure
    · rcases henough with
        ⟨hlengthCoordinates, htagRows, hargumentRows, hcontrol⟩
      have hlength : 2 ≤ current.1.length := by
        simpa only [hcurrent.tokensCount_eq] using hlengthCoordinates
      have htag :=
        (compactAdditiveNatListAtRows_iff_getI
          hcurrent.tokensRows 0 witness.tag).mp (by
            simpa only [hcurrent.tokensCount_eq] using htagRows)
      have hargument :=
        (compactAdditiveNatListAtRows_iff_getI
          hcurrent.tokensRows 1 witness.argument).mp (by
            simpa only [hcurrent.tokensCount_eq] using hargumentRows)
      have htagToken : compactTokenAt 0 current.1 = witness.tag :=
        (compactTokenAt_eq_getI 0 current.1).trans htag.2
      have hargumentToken :
          compactTokenAt 1 current.1 = witness.argument :=
        (compactTokenAt_eq_getI 1 current.1).trans hargument.2
      rcases hcontrol with htagZero | htagOne | htagTwo | htagInvalid
      · rcases htagZero with hsuccess | hfailure
        · rcases hsuccess with ⟨htagValue, hargumentBound, hcontinueRows⟩
          have hcontinue :=
            (compactUnifiedParserSyntaxTermContinueRows_iff
              hcurrent hnext htailRows htailCount).mp hcontinueRows
          simpa [compactTermTokenStep, hlength, htagToken,
            hargumentToken, htagValue, hargumentBound] using hcontinue.2
        · rcases hfailure with ⟨htagValue, hargumentBound, hfailureRows⟩
          have hnotBound : ¬ witness.argument < binderArity := by omega
          have hfailed :=
            (compactUnifiedParserSyntaxTermFailureRows_iff
              hcurrent hnext htailRows htailCount).mp hfailureRows
          simpa [compactTermTokenStep, hlength, htagToken,
            hargumentToken, htagValue, hnotBound] using hfailed
      · rcases htagOne with ⟨htagValue, hcontinueRows⟩
        have hcontinue :=
          (compactUnifiedParserSyntaxTermContinueRows_iff
            hcurrent hnext htailRows htailCount).mp hcontinueRows
        simpa [compactTermTokenStep, hlength, htagToken,
          htagValue] using hcontinue.2
      · rcases htagTwo with ⟨htagValue, hfunctionBranch⟩
        rcases hfunctionBranch with hshortFunction | henoughFunction
        · have hlengthThree : ¬ 3 ≤ current.1.length := by
            have hshortCount : current.1.length ≤ 2 := by
              simpa only [hcurrent.tokensCount_eq] using hshortFunction.1
            omega
          have hfailed :=
            (compactUnifiedParserSyntaxTermFailureRows_iff
              hcurrent hnext htailRows htailCount).mp hshortFunction.2
          simpa [compactTermTokenStep, hlength, htagToken,
            htagValue, hlengthThree] using hfailed
        · rcases henoughFunction with
            ⟨hlengthThreeCoordinates, hfunctionCodeRows,
              hvalidBranch⟩
          have hlengthThree : 3 ≤ current.1.length := by
            simpa only [hcurrent.tokensCount_eq] using
              hlengthThreeCoordinates
          have hfunctionCode :=
            (compactAdditiveNatListAtRows_iff_getI
              hcurrent.tokensRows 2 witness.functionCode).mp (by
                simpa only [hcurrent.tokensCount_eq] using
                  hfunctionCodeRows)
          have hfunctionCodeToken :
              compactTokenAt 2 current.1 = witness.functionCode :=
            (compactTokenAt_eq_getI 2 current.1).trans hfunctionCode.2
          rcases hvalidBranch with hvalid | hinvalid
          · have hfunction :=
              (compactUnifiedParserSyntaxTermFunctionRows_iff
                hcurrent hnext htailRows htailCount).mp hvalid.2
            simpa [compactTermTokenStep, hlength, htagToken,
              hargumentToken, hfunctionCodeToken, htagValue,
              hlengthThree, hvalid.1,
              compactRepeatTermTask] using hfunction.2
          · have hfailed :=
              (compactUnifiedParserSyntaxTermFailureRows_iff
                hcurrent hnext htailRows htailCount).mp hinvalid.2
            simpa [compactTermTokenStep, hlength, htagToken,
              hargumentToken, hfunctionCodeToken, htagValue,
              hlengthThree, hinvalid.1] using hfailed
      · rcases htagInvalid with ⟨htagZero, htagOne, htagTwo, hfailureRows⟩
        have hfailed :=
          (compactUnifiedParserSyntaxTermFailureRows_iff
            hcurrent hnext htailRows htailCount).mp hfailureRows
        simpa [compactTermTokenStep, hlength, htagToken,
          htagZero, htagOne, htagTwo] using hfailed
  · rintro ⟨hcurrentStatus, tail, hcurrentTasks, hnextStep⟩
    rcases
        (exists_compactAdditiveSyntaxTaskListUnconsRowsWithSize_iff
          hcurrent.tasksRows 0 binderArity 0).mpr
            ⟨tail, hcurrentTasks⟩ with
      ⟨tailBoundary, tailCount, tailBoundarySize, hunconsTyped⟩
    have huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize
        tokenTable width tokenCount
          currentCoordinates.tasksBoundary currentCoordinates.tasksCount
          tailBoundary tailCount tailBoundarySize
          0 binderArity 0 := by
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
    let witness : CompactSyntaxTermTaskWitnessCoordinates :=
      { tailBoundary := tailBoundary
        tailCount := tailCount
        tailBoundarySize := tailBoundarySize
        tag := compactTokenAt 0 current.1
        argument := compactTokenAt 1 current.1
        functionCode := compactTokenAt 2 current.1 }
    have hcurrentRunning : CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount
          currentCoordinates.tasksFinish currentCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mpr hcurrentStatus
    by_cases hlength : 2 ≤ current.1.length
    · have htagRows : CompactAdditiveNatListAtRows
          tokenTable width tokenCount
            currentCoordinates.tokensBoundary current.1.length 0
            witness.tag :=
        (compactAdditiveNatListAtRows_iff_getI
          hcurrent.tokensRows 0 witness.tag).mpr (by
            refine ⟨by omega, ?_⟩
            exact (compactTokenAt_eq_getI 0 current.1).symm)
      have hargumentRows : CompactAdditiveNatListAtRows
          tokenTable width tokenCount
            currentCoordinates.tokensBoundary current.1.length 1
            witness.argument :=
        (compactAdditiveNatListAtRows_iff_getI
          hcurrent.tokensRows 1 witness.argument).mpr (by
            refine ⟨by omega, ?_⟩
            exact (compactTokenAt_eq_getI 1 current.1).symm)
      by_cases htagZero : witness.tag = 0
      · change compactTokenAt 0 current.1 = 0 at htagZero
        by_cases hargumentBound : witness.argument < binderArity
        · change compactTokenAt 1 current.1 < binderArity at hargumentBound
          have hnextState : next =
              compactSyntaxContinue (current.1.drop 2) tail := by
            simpa [compactTermTokenStep, hlength, witness,
              htagZero, hargumentBound] using hnextStep
          have hcontinue :=
            (compactUnifiedParserSyntaxTermContinueRows_iff
              hcurrent hnext htailRows htailCount).mpr
                ⟨hlength, hnextState⟩
          refine ⟨witness, hcurrentRunning, huncons, Or.inr
            ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
              ?_, ?_, Or.inl (Or.inl ⟨htagZero,
                hargumentBound, hcontinue⟩)⟩⟩
          · simpa only [hcurrent.tokensCount_eq] using htagRows
          · simpa only [hcurrent.tokensCount_eq] using hargumentRows
        · change ¬ compactTokenAt 1 current.1 < binderArity at hargumentBound
          have hnextState : next = compactSyntaxFailure current.1 tail := by
            simpa [compactTermTokenStep, hlength, witness,
              htagZero, hargumentBound] using hnextStep
          have hfailure :=
            (compactUnifiedParserSyntaxTermFailureRows_iff
              hcurrent hnext htailRows htailCount).mpr hnextState
          refine ⟨witness, hcurrentRunning, huncons, Or.inr
            ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
              ?_, ?_, Or.inl (Or.inr ⟨htagZero,
                by
                  have hle := Nat.le_of_not_gt hargumentBound
                  simpa [witness] using hle,
                hfailure⟩)⟩⟩
          · simpa only [hcurrent.tokensCount_eq] using htagRows
          · simpa only [hcurrent.tokensCount_eq] using hargumentRows
      · change compactTokenAt 0 current.1 ≠ 0 at htagZero
        by_cases htagOne : witness.tag = 1
        · change compactTokenAt 0 current.1 = 1 at htagOne
          have hnextState : next =
              compactSyntaxContinue (current.1.drop 2) tail := by
            simpa [compactTermTokenStep, hlength, witness,
              htagZero, htagOne] using hnextStep
          have hcontinue :=
            (compactUnifiedParserSyntaxTermContinueRows_iff
              hcurrent hnext htailRows htailCount).mpr
                ⟨hlength, hnextState⟩
          refine ⟨witness, hcurrentRunning, huncons, Or.inr
            ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
              ?_, ?_, Or.inr (Or.inl ⟨htagOne, hcontinue⟩)⟩⟩
          · simpa only [hcurrent.tokensCount_eq] using htagRows
          · simpa only [hcurrent.tokensCount_eq] using hargumentRows
        · change compactTokenAt 0 current.1 ≠ 1 at htagOne
          by_cases htagTwo : witness.tag = 2
          · change compactTokenAt 0 current.1 = 2 at htagTwo
            by_cases hlengthThree : 3 ≤ current.1.length
            · have hfunctionCodeRows : CompactAdditiveNatListAtRows
                  tokenTable width tokenCount
                    currentCoordinates.tokensBoundary current.1.length 2
                    witness.functionCode :=
                (compactAdditiveNatListAtRows_iff_getI
                  hcurrent.tokensRows 2 witness.functionCode).mpr (by
                    refine ⟨by omega, ?_⟩
                    exact (compactTokenAt_eq_getI 2 current.1).symm)
              by_cases hvalid : ArithmeticFuncCodeValid
                  witness.argument witness.functionCode
              · change ArithmeticFuncCodeValid
                  (compactTokenAt 1 current.1)
                  (compactTokenAt 2 current.1) at hvalid
                have hnextState : next =
                    compactSyntaxContinue (current.1.drop 3)
                      ((2, binderArity, witness.argument) :: tail) := by
                  simpa [compactTermTokenStep, hlength, witness,
                    htagZero, htagOne, htagTwo,
                    hlengthThree, hvalid,
                    compactRepeatTermTask] using hnextStep
                have hfunction :=
                  (compactUnifiedParserSyntaxTermFunctionRows_iff
                    hcurrent hnext htailRows htailCount).mpr
                      ⟨hlengthThree, hnextState⟩
                refine ⟨witness, hcurrentRunning, huncons, Or.inr
                  ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
                    ?_, ?_, Or.inr (Or.inr (Or.inl
                      ⟨htagTwo, Or.inr
                        ⟨by simpa only [hcurrent.tokensCount_eq] using
                            hlengthThree,
                          ?_, Or.inl ⟨hvalid, hfunction⟩⟩⟩))⟩⟩
                · simpa only [hcurrent.tokensCount_eq] using htagRows
                · simpa only [hcurrent.tokensCount_eq] using hargumentRows
                · simpa only [hcurrent.tokensCount_eq] using
                    hfunctionCodeRows
              · change ¬ ArithmeticFuncCodeValid
                  (compactTokenAt 1 current.1)
                  (compactTokenAt 2 current.1) at hvalid
                have hnextState : next = compactSyntaxFailure current.1 tail := by
                  simpa [compactTermTokenStep, hlength, witness,
                    htagZero, htagOne, htagTwo,
                    hlengthThree, hvalid] using hnextStep
                have hfailure :=
                  (compactUnifiedParserSyntaxTermFailureRows_iff
                    hcurrent hnext htailRows htailCount).mpr hnextState
                refine ⟨witness, hcurrentRunning, huncons, Or.inr
                  ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
                    ?_, ?_, Or.inr (Or.inr (Or.inl
                      ⟨htagTwo, Or.inr
                        ⟨by simpa only [hcurrent.tokensCount_eq] using
                            hlengthThree,
                          ?_, Or.inr ⟨hvalid, hfailure⟩⟩⟩))⟩⟩
                · simpa only [hcurrent.tokensCount_eq] using htagRows
                · simpa only [hcurrent.tokensCount_eq] using hargumentRows
                · simpa only [hcurrent.tokensCount_eq] using
                    hfunctionCodeRows
            · have hnextState : next = compactSyntaxFailure current.1 tail := by
                simpa [compactTermTokenStep, hlength, witness,
                  htagZero, htagOne, htagTwo,
                  hlengthThree] using hnextStep
              have hfailure :=
                (compactUnifiedParserSyntaxTermFailureRows_iff
                  hcurrent hnext htailRows htailCount).mpr hnextState
              refine ⟨witness, hcurrentRunning, huncons, Or.inr
                ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
                  ?_, ?_, Or.inr (Or.inr (Or.inl
                    ⟨htagTwo, Or.inl
                      ⟨by simpa only [hcurrent.tokensCount_eq] using
                          (show current.1.length ≤ 2 by omega),
                        hfailure⟩⟩))⟩⟩
              · simpa only [hcurrent.tokensCount_eq] using htagRows
              · simpa only [hcurrent.tokensCount_eq] using hargumentRows
          · change compactTokenAt 0 current.1 ≠ 2 at htagTwo
            have hnextState : next = compactSyntaxFailure current.1 tail := by
              simpa [compactTermTokenStep, hlength, witness,
                htagZero, htagOne, htagTwo] using hnextStep
            have hfailure :=
              (compactUnifiedParserSyntaxTermFailureRows_iff
                hcurrent hnext htailRows htailCount).mpr hnextState
            refine ⟨witness, hcurrentRunning, huncons, Or.inr
              ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
                ?_, ?_, Or.inr (Or.inr (Or.inr
                  ⟨htagZero, htagOne, htagTwo, hfailure⟩))⟩⟩
            · simpa only [hcurrent.tokensCount_eq] using htagRows
            · simpa only [hcurrent.tokensCount_eq] using hargumentRows
    · have hnextState : next = compactSyntaxFailure current.1 tail := by
        simpa [compactTermTokenStep, hlength] using hnextStep
      have hfailure :=
        (compactUnifiedParserSyntaxTermFailureRows_iff
          hcurrent hnext htailRows htailCount).mpr hnextState
      refine ⟨witness, hcurrentRunning, huncons, Or.inl ⟨?_, hfailure⟩⟩
      simpa only [hcurrent.tokensCount_eq] using
        (show current.1.length ≤ 1 by omega)

#print axioms compactTokenAt_eq_getI
#print axioms compactUnifiedParserSyntaxTermFailureRows_iff
#print axioms compactUnifiedParserSyntaxTermContinueRows_iff
#print axioms compactUnifiedParserSyntaxTermFunctionRows_iff
#print axioms compactUnifiedParserSyntaxTermRows_iff

end FoundationCompactNumericListedDirectParserSyntaxTermRows
