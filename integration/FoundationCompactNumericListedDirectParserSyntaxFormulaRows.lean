import integration.FoundationCompactNumericListedDirectParserSyntaxTermRows
import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRows

/-!
# Exact direct rows for the syntax formula task

This module expands all eight formula tags and every rejection branch of
`compactFormulaTokenStep`.  Relation atoms push a repeated-term task, binary
connectives push two formula tasks, and quantifiers push one task at successor
binder arity; all token suffixes and task prefixes are checked directly.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaRows

open FoundationCompactArithmeticSymbolCode
open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows

structure CompactSyntaxFormulaTaskWitnessCoordinates where
  tailBoundary : Nat
  tailCount : Nat
  tailBoundarySize : Nat
  tag : Nat
  relationArity : Nat
  relationCode : Nat

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

def CompactSyntaxParserFormulaTaskCase
    (binderArity : Nat)
    (current next : CompactUnifiedParserState) : Prop :=
  current.2.2 = none ∧
    ∃ tail,
      current.2.1 = (1, binderArity, 0) :: tail ∧
      next = compactFormulaTokenStep (binderArity, current.1, tail)

def CompactUnifiedParserSyntaxFormulaBinaryRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) : Prop :=
  CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount next.tasksFinish next.finish ∧
    CompactAdditiveNatListDropRows
      tokenTable width tokenCount
        current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount 1 ∧
    CompactAdditiveSyntaxTaskListDropRows
      tokenTable width tokenCount
        next.tasksBoundary next.tasksCount tailBoundary tailCount 2 ∧
    CompactAdditiveSyntaxTaskListAtRows
      tokenTable width tokenCount
        next.tasksBoundary next.tasksCount 0 1 binderArity 0 ∧
    CompactAdditiveSyntaxTaskListAtRows
      tokenTable width tokenCount
        next.tasksBoundary next.tasksCount 1 1 binderArity 0

def CompactUnifiedParserSyntaxFormulaQuantifierRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity : Nat) : Prop :=
  CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount next.tasksFinish next.finish ∧
    CompactAdditiveNatListDropRows
      tokenTable width tokenCount
        current.tokensBoundary current.tokensCount
        next.tokensBoundary next.tokensCount 1 ∧
    CompactAdditiveSyntaxTaskListConsRows
      tokenTable width tokenCount
        tailBoundary tailCount next.tasksBoundary next.tasksCount
        1 (binderArity + 1) 0

theorem compactUnifiedParserSyntaxFormulaBinaryRows_iff
    {tokenTable width tokenCount tailBoundary tailCount binderArity : Nat}
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
    CompactUnifiedParserSyntaxFormulaBinaryRows
        tokenTable width tokenCount currentCoordinates nextCoordinates
          tailBoundary tailCount binderArity ↔
      1 ≤ current.1.length ∧
        next = compactSyntaxContinue (current.1.drop 1)
          ((1, binderArity, 0) :: (1, binderArity, 0) :: tail) := by
  constructor
  · rintro ⟨hrunning, htokenRows, hdropRows, htaskZero, htaskOne⟩
    have hnextStatus : next.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hnext.statusLayout).mp hrunning
    have htokenRows' : CompactAdditiveNatListDropRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary next.1.length 1 := by
      simpa only [hcurrent.tokensCount_eq,
        hnext.tokensCount_eq] using htokenRows
    have htokens : next.1 = current.1.drop 1 :=
      htokenRows'.eq_drop_of_rows hcurrent.tokensRows hnext.tokensRows
    have hdropRows' : CompactAdditiveSyntaxTaskListDropRows
        tokenTable width tokenCount
          nextCoordinates.tasksBoundary next.2.1.length
          tailBoundary tail.length 2 := by
      simpa only [hnext.tasksCount_eq, htailCount] using hdropRows
    have htailEq : tail = next.2.1.drop 2 :=
      hdropRows'.eq_drop_of_rows hnext.tasksRows htailRows
    have htaskZero' :=
      (compactAdditiveSyntaxTaskListAtRows_iff_getI
        hnext.tasksRows 0 1 binderArity 0).mp (by
          simpa only [hnext.tasksCount_eq] using htaskZero)
    have htaskOne' :=
      (compactAdditiveSyntaxTaskListAtRows_iff_getI
        hnext.tasksRows 1 1 binderArity 0).mp (by
          simpa only [hnext.tasksCount_eq] using htaskOne)
    have htasks : next.2.1 =
        (1, binderArity, 0) :: (1, binderArity, 0) :: tail :=
      list_eq_two_cons_of_getI_drop
        htaskZero'.1 htaskOne'.1 htaskZero'.2 htaskOne'.2 htailEq
    refine ⟨htokenRows'.1, ?_⟩
    rcases current with ⟨currentTokens, currentTasks, currentStatus⟩
    rcases next with ⟨nextTokens, nextTasks, nextStatus⟩
    simp only at hnextStatus htokens htasks ⊢
    simp [compactSyntaxContinue, hnextStatus, htokens, htasks]
  · rintro ⟨hlength, hnextState⟩
    have hnextLayout : CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount nextCoordinates
          (current.1.drop 1,
            (1, binderArity, 0) :: (1, binderArity, 0) :: tail,
            none) := by
      simpa [compactSyntaxContinue, hnextState] using hnext
    have hrunning : CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount
          nextCoordinates.tasksFinish nextCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hnextLayout.statusLayout).mpr rfl
    have htokenRows : CompactAdditiveNatListDropRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary (current.1.drop 1).length 1 :=
      CompactAdditiveStructuredListElementRowLayouts.natDropRows
        hcurrent.tokensRows hnextLayout.tokensRows hlength rfl
    have hdropRows : CompactAdditiveSyntaxTaskListDropRows
        tokenTable width tokenCount
          nextCoordinates.tasksBoundary
            ((1, binderArity, 0) :: (1, binderArity, 0) :: tail).length
          tailBoundary tail.length 2 :=
      CompactAdditiveStructuredListElementRowLayouts.taskDropRows
        hnextLayout.tasksRows htailRows (by simp) (by simp)
    have htaskZero : CompactAdditiveSyntaxTaskListAtRows
        tokenTable width tokenCount
          nextCoordinates.tasksBoundary
            ((1, binderArity, 0) :: (1, binderArity, 0) :: tail).length
          0 1 binderArity 0 :=
      (compactAdditiveSyntaxTaskListAtRows_iff_getI
        hnextLayout.tasksRows 0 1 binderArity 0).mpr (by simp)
    have htaskOne : CompactAdditiveSyntaxTaskListAtRows
        tokenTable width tokenCount
          nextCoordinates.tasksBoundary
            ((1, binderArity, 0) :: (1, binderArity, 0) :: tail).length
          1 1 binderArity 0 :=
      (compactAdditiveSyntaxTaskListAtRows_iff_getI
        hnextLayout.tasksRows 1 1 binderArity 0).mpr (by simp)
    refine ⟨hrunning, ?_, ?_, ?_, ?_⟩
    · simpa only [hcurrent.tokensCount_eq,
        hnextLayout.tokensCount_eq] using htokenRows
    · simpa only [hnextLayout.tasksCount_eq, htailCount] using hdropRows
    · simpa only [hnextLayout.tasksCount_eq] using htaskZero
    · simpa only [hnextLayout.tasksCount_eq] using htaskOne

theorem compactUnifiedParserSyntaxFormulaQuantifierRows_iff
    {tokenTable width tokenCount tailBoundary tailCount binderArity : Nat}
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
    CompactUnifiedParserSyntaxFormulaQuantifierRows
        tokenTable width tokenCount currentCoordinates nextCoordinates
          tailBoundary tailCount binderArity ↔
      1 ≤ current.1.length ∧
        next = compactSyntaxContinue (current.1.drop 1)
          ((1, binderArity + 1, 0) :: tail) := by
  constructor
  · rintro ⟨hrunning, htokenRows, htaskRows⟩
    have hnextStatus : next.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hnext.statusLayout).mp hrunning
    have htokenRows' : CompactAdditiveNatListDropRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary next.1.length 1 := by
      simpa only [hcurrent.tokensCount_eq,
        hnext.tokensCount_eq] using htokenRows
    have htokens : next.1 = current.1.drop 1 :=
      htokenRows'.eq_drop_of_rows hcurrent.tokensRows hnext.tokensRows
    have htaskRows' : CompactAdditiveSyntaxTaskListConsRows
        tokenTable width tokenCount
          tailBoundary tail.length
          nextCoordinates.tasksBoundary next.2.1.length
          1 (binderArity + 1) 0 := by
      simpa only [htailCount, hnext.tasksCount_eq] using htaskRows
    have htasks : next.2.1 = (1, binderArity + 1, 0) :: tail :=
      htaskRows'.eq_cons_of_rows htailRows hnext.tasksRows
    refine ⟨htokenRows'.1, ?_⟩
    rcases current with ⟨currentTokens, currentTasks, currentStatus⟩
    rcases next with ⟨nextTokens, nextTasks, nextStatus⟩
    simp only at hnextStatus htokens htasks ⊢
    simp [compactSyntaxContinue, hnextStatus, htokens, htasks]
  · rintro ⟨hlength, hnextState⟩
    have hnextLayout : CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount nextCoordinates
          (current.1.drop 1, (1, binderArity + 1, 0) :: tail, none) := by
      simpa [compactSyntaxContinue, hnextState] using hnext
    have hrunning : CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount
          nextCoordinates.tasksFinish nextCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hnextLayout.statusLayout).mpr rfl
    have htokenRows : CompactAdditiveNatListDropRows
        tokenTable width tokenCount
          currentCoordinates.tokensBoundary current.1.length
          nextCoordinates.tokensBoundary (current.1.drop 1).length 1 :=
      CompactAdditiveStructuredListElementRowLayouts.natDropRows
        hcurrent.tokensRows hnextLayout.tokensRows hlength rfl
    have htaskRows : CompactAdditiveSyntaxTaskListConsRows
        tokenTable width tokenCount
          tailBoundary tail.length
          nextCoordinates.tasksBoundary
            ((1, binderArity + 1, 0) :: tail).length
          1 (binderArity + 1) 0 :=
      CompactAdditiveStructuredListElementRowLayouts.taskConsRows
        htailRows hnextLayout.tasksRows rfl
    refine ⟨hrunning, ?_, ?_⟩
    · simpa only [hcurrent.tokensCount_eq,
        hnextLayout.tokensCount_eq] using htokenRows
    · simpa only [htailCount,
        hnextLayout.tasksCount_eq] using htaskRows

def CompactUnifiedParserSyntaxFormulaRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : Prop :=
  CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount current.tasksFinish current.finish ∧
    CompactAdditiveSyntaxTaskListUnconsRowsWithSize
      tokenTable width tokenCount
        current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize
        1 binderArity 0 ∧
    ((current.tokensCount = 0 ∧
      CompactUnifiedParserSyntaxTermFailureRows
        tokenTable width tokenCount current next
          witness.tailBoundary witness.tailCount) ∨
     (1 ≤ current.tokensCount ∧
      CompactAdditiveNatListAtRows
        tokenTable width tokenCount
          current.tokensBoundary current.tokensCount 0 witness.tag ∧
      ((((witness.tag = 0 ∨ witness.tag = 1) ∧
          ((current.tokensCount ≤ 2 ∧
            CompactUnifiedParserSyntaxTermFailureRows
              tokenTable width tokenCount current next
                witness.tailBoundary witness.tailCount) ∨
           (3 ≤ current.tokensCount ∧
            CompactAdditiveNatListAtRows
              tokenTable width tokenCount
                current.tokensBoundary current.tokensCount
                1 witness.relationArity ∧
            CompactAdditiveNatListAtRows
              tokenTable width tokenCount
                current.tokensBoundary current.tokensCount
                2 witness.relationCode ∧
            ((ArithmeticRelCodeValid
                witness.relationArity witness.relationCode ∧
              CompactUnifiedParserSyntaxTermFunctionRows
                tokenTable width tokenCount current next
                  witness.tailBoundary witness.tailCount
                  binderArity witness.relationArity) ∨
             (¬ ArithmeticRelCodeValid
                witness.relationArity witness.relationCode ∧
              CompactUnifiedParserSyntaxTermFailureRows
                tokenTable width tokenCount current next
                  witness.tailBoundary witness.tailCount))))) ∨
        ((witness.tag = 2 ∨ witness.tag = 3) ∧
          CompactUnifiedParserSyntaxTermContinueRows
            tokenTable width tokenCount current next
              witness.tailBoundary witness.tailCount 1) ∨
        ((witness.tag = 4 ∨ witness.tag = 5) ∧
          CompactUnifiedParserSyntaxFormulaBinaryRows
            tokenTable width tokenCount current next
              witness.tailBoundary witness.tailCount binderArity) ∨
        ((witness.tag = 6 ∨ witness.tag = 7) ∧
          CompactUnifiedParserSyntaxFormulaQuantifierRows
            tokenTable width tokenCount current next
              witness.tailBoundary witness.tailCount binderArity) ∨
        (witness.tag ≠ 0 ∧ witness.tag ≠ 1 ∧
          witness.tag ≠ 2 ∧ witness.tag ≠ 3 ∧
          witness.tag ≠ 4 ∧ witness.tag ≠ 5 ∧
          witness.tag ≠ 6 ∧ witness.tag ≠ 7 ∧
          CompactUnifiedParserSyntaxTermFailureRows
            tokenTable width tokenCount current next
              witness.tailBoundary witness.tailCount)))))

theorem compactUnifiedParserSyntaxFormulaRows_iff
    {tokenTable width tokenCount binderArity : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    (∃ witness,
        CompactUnifiedParserSyntaxFormulaRows
          tokenTable width tokenCount currentCoordinates nextCoordinates
            binderArity witness) ↔
      CompactSyntaxParserFormulaTaskCase binderArity current next := by
  constructor
  · rintro ⟨witness, hcurrentRunning, huncons, hbranch⟩
    have hcurrentStatus : current.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mp hcurrentRunning
    rcases huncons.realizes hcurrent.tasksCount_eq hcurrent.tasksRows with
      ⟨tail, htailRows, htailCount, hcurrentTasks⟩
    refine ⟨hcurrentStatus, tail, hcurrentTasks, ?_⟩
    rcases hbranch with hshort | henough
    · have hlength : ¬ 1 ≤ current.1.length := by
        have hzero : current.1.length = 0 := by
          simpa only [hcurrent.tokensCount_eq] using hshort.1
        omega
      have hfailed :=
        (compactUnifiedParserSyntaxTermFailureRows_iff
          hcurrent hnext htailRows htailCount).mp hshort.2
      simpa [compactFormulaTokenStep, hlength] using hfailed
    · rcases henough with ⟨hlengthCoordinates, htagRows, hcontrol⟩
      have hlength : 1 ≤ current.1.length := by
        simpa only [hcurrent.tokensCount_eq] using hlengthCoordinates
      have htag :=
        (compactAdditiveNatListAtRows_iff_getI
          hcurrent.tokensRows 0 witness.tag).mp (by
            simpa only [hcurrent.tokensCount_eq] using htagRows)
      have htagToken : compactTokenAt 0 current.1 = witness.tag :=
        (compactTokenAt_eq_getI 0 current.1).trans htag.2
      rcases hcontrol with
        hrelation | hatomic | hbinary | hquantifier | hinvalid
      · rcases hrelation with ⟨htagClass, hrelationBranch⟩
        rcases hrelationBranch with hshortRelation | henoughRelation
        · have hlengthThree : ¬ 3 ≤ current.1.length := by
            have hshortCount : current.1.length ≤ 2 := by
              simpa only [hcurrent.tokensCount_eq] using hshortRelation.1
            omega
          have hfailed :=
            (compactUnifiedParserSyntaxTermFailureRows_iff
              hcurrent hnext htailRows htailCount).mp hshortRelation.2
          rcases htagClass with htagZero | htagOne
          · simpa [compactFormulaTokenStep, hlength,
              htagToken, htagZero, hlengthThree] using hfailed
          · simpa [compactFormulaTokenStep, hlength,
              htagToken, htagOne, hlengthThree] using hfailed
        · rcases henoughRelation with
            ⟨hlengthThreeCoordinates, harityRows, hcodeRows, hvalidBranch⟩
          have hlengthThree : 3 ≤ current.1.length := by
            simpa only [hcurrent.tokensCount_eq] using
              hlengthThreeCoordinates
          have harity :=
            (compactAdditiveNatListAtRows_iff_getI
              hcurrent.tokensRows 1 witness.relationArity).mp (by
                simpa only [hcurrent.tokensCount_eq] using harityRows)
          have hcode :=
            (compactAdditiveNatListAtRows_iff_getI
              hcurrent.tokensRows 2 witness.relationCode).mp (by
                simpa only [hcurrent.tokensCount_eq] using hcodeRows)
          have harityToken :
              compactTokenAt 1 current.1 = witness.relationArity :=
            (compactTokenAt_eq_getI 1 current.1).trans harity.2
          have hcodeToken :
              compactTokenAt 2 current.1 = witness.relationCode :=
            (compactTokenAt_eq_getI 2 current.1).trans hcode.2
          rcases hvalidBranch with hvalid | hinvalidCode
          · have hrelationRows :=
              (compactUnifiedParserSyntaxTermFunctionRows_iff
                hcurrent hnext htailRows htailCount).mp hvalid.2
            rcases htagClass with htagZero | htagOne
            · simpa [compactFormulaTokenStep, hlength, htagToken,
                harityToken, hcodeToken, htagZero, hlengthThree,
                hvalid.1, compactRepeatTermTask] using hrelationRows.2
            · simpa [compactFormulaTokenStep, hlength, htagToken,
                harityToken, hcodeToken, htagOne, hlengthThree,
                hvalid.1, compactRepeatTermTask] using hrelationRows.2
          · have hfailed :=
              (compactUnifiedParserSyntaxTermFailureRows_iff
                hcurrent hnext htailRows htailCount).mp hinvalidCode.2
            rcases htagClass with htagZero | htagOne
            · simpa [compactFormulaTokenStep, hlength, htagToken,
                harityToken, hcodeToken, htagZero, hlengthThree,
                hinvalidCode.1] using hfailed
            · simpa [compactFormulaTokenStep, hlength, htagToken,
                harityToken, hcodeToken, htagOne, hlengthThree,
                hinvalidCode.1] using hfailed
      · rcases hatomic with ⟨htagClass, hcontinueRows⟩
        have hcontinue :=
          (compactUnifiedParserSyntaxTermContinueRows_iff
            hcurrent hnext htailRows htailCount).mp hcontinueRows
        rcases htagClass with htagTwo | htagThree
        · simpa [compactFormulaTokenStep, hlength,
            htagToken, htagTwo] using hcontinue.2
        · simpa [compactFormulaTokenStep, hlength,
            htagToken, htagThree] using hcontinue.2
      · rcases hbinary with ⟨htagClass, hbinaryRows⟩
        have hbinaryStep :=
          (compactUnifiedParserSyntaxFormulaBinaryRows_iff
            hcurrent hnext htailRows htailCount).mp hbinaryRows
        rcases htagClass with htagFour | htagFive
        · simpa [compactFormulaTokenStep, hlength, htagToken,
            htagFour, compactFormulaTask] using hbinaryStep.2
        · simpa [compactFormulaTokenStep, hlength, htagToken,
            htagFive, compactFormulaTask] using hbinaryStep.2
      · rcases hquantifier with ⟨htagClass, hquantifierRows⟩
        have hquantifierStep :=
          (compactUnifiedParserSyntaxFormulaQuantifierRows_iff
            hcurrent hnext htailRows htailCount).mp hquantifierRows
        rcases htagClass with htagSix | htagSeven
        · simpa [compactFormulaTokenStep, hlength, htagToken,
            htagSix, compactFormulaTask] using hquantifierStep.2
        · simpa [compactFormulaTokenStep, hlength, htagToken,
            htagSeven, compactFormulaTask] using hquantifierStep.2
      · rcases hinvalid with
          ⟨hzero, hone, htwo, hthree, hfour, hfive, hsix, hseven,
            hfailureRows⟩
        have hfailed :=
          (compactUnifiedParserSyntaxTermFailureRows_iff
            hcurrent hnext htailRows htailCount).mp hfailureRows
        simpa [compactFormulaTokenStep, hlength, htagToken,
          hzero, hone, htwo, hthree, hfour, hfive, hsix, hseven] using hfailed
  · rintro ⟨hcurrentStatus, tail, hcurrentTasks, hnextStep⟩
    rcases
        (exists_compactAdditiveSyntaxTaskListUnconsRowsWithSize_iff
          hcurrent.tasksRows 1 binderArity 0).mpr
            ⟨tail, hcurrentTasks⟩ with
      ⟨tailBoundary, tailCount, tailBoundarySize, hunconsTyped⟩
    have huncons : CompactAdditiveSyntaxTaskListUnconsRowsWithSize
        tokenTable width tokenCount
          currentCoordinates.tasksBoundary currentCoordinates.tasksCount
          tailBoundary tailCount tailBoundarySize
          1 binderArity 0 := by
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
    let witness : CompactSyntaxFormulaTaskWitnessCoordinates :=
      { tailBoundary := tailBoundary
        tailCount := tailCount
        tailBoundarySize := tailBoundarySize
        tag := compactTokenAt 0 current.1
        relationArity := compactTokenAt 1 current.1
        relationCode := compactTokenAt 2 current.1 }
    have hcurrentRunning : CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount
          currentCoordinates.tasksFinish currentCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mpr hcurrentStatus
    by_cases hlength : 1 ≤ current.1.length
    · have htagRows : CompactAdditiveNatListAtRows
          tokenTable width tokenCount
            currentCoordinates.tokensBoundary current.1.length 0 witness.tag :=
        (compactAdditiveNatListAtRows_iff_getI
          hcurrent.tokensRows 0 witness.tag).mpr (by
            refine ⟨by omega, ?_⟩
            exact (compactTokenAt_eq_getI 0 current.1).symm)
      by_cases hrelationTag : witness.tag = 0 ∨ witness.tag = 1
      · by_cases hlengthThree : 3 ≤ current.1.length
        · have harityRows : CompactAdditiveNatListAtRows
              tokenTable width tokenCount
                currentCoordinates.tokensBoundary current.1.length
                1 witness.relationArity :=
            (compactAdditiveNatListAtRows_iff_getI
              hcurrent.tokensRows 1 witness.relationArity).mpr (by
                refine ⟨by omega, ?_⟩
                exact (compactTokenAt_eq_getI 1 current.1).symm)
          have hcodeRows : CompactAdditiveNatListAtRows
              tokenTable width tokenCount
                currentCoordinates.tokensBoundary current.1.length
                2 witness.relationCode :=
            (compactAdditiveNatListAtRows_iff_getI
              hcurrent.tokensRows 2 witness.relationCode).mpr (by
                refine ⟨by omega, ?_⟩
                exact (compactTokenAt_eq_getI 2 current.1).symm)
          by_cases hvalid : ArithmeticRelCodeValid
              witness.relationArity witness.relationCode
          · change ArithmeticRelCodeValid
              (compactTokenAt 1 current.1)
              (compactTokenAt 2 current.1) at hvalid
            have hnextState : next =
                compactSyntaxContinue (current.1.drop 3)
                  ((2, binderArity, witness.relationArity) :: tail) := by
              rcases hrelationTag with htagZero | htagOne
              · have htagZeroToken : compactTokenAt 0 current.1 = 0 := by
                  simpa [witness] using htagZero
                simpa [compactFormulaTokenStep, hlength, witness,
                  htagZeroToken, hlengthThree, hvalid,
                  compactRepeatTermTask] using hnextStep
              · have htagOneToken : compactTokenAt 0 current.1 = 1 := by
                  simpa [witness] using htagOne
                simpa [compactFormulaTokenStep, hlength, witness,
                  htagOneToken, hlengthThree, hvalid,
                  compactRepeatTermTask] using hnextStep
            have hrelationRows :=
              (compactUnifiedParserSyntaxTermFunctionRows_iff
                hcurrent hnext htailRows htailCount).mpr
                  ⟨hlengthThree, hnextState⟩
            refine ⟨witness, hcurrentRunning, huncons, Or.inr
              ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
                ?_, Or.inl ⟨?_, Or.inr
                  ⟨by simpa only [hcurrent.tokensCount_eq] using hlengthThree,
                    ?_, ?_, Or.inl ⟨hvalid, hrelationRows⟩⟩⟩⟩⟩
            · simpa only [hcurrent.tokensCount_eq] using htagRows
            · exact hrelationTag
            · simpa only [hcurrent.tokensCount_eq] using harityRows
            · simpa only [hcurrent.tokensCount_eq] using hcodeRows
          · change ¬ ArithmeticRelCodeValid
              (compactTokenAt 1 current.1)
              (compactTokenAt 2 current.1) at hvalid
            have hnextState : next = compactSyntaxFailure current.1 tail := by
              rcases hrelationTag with htagZero | htagOne
              · have htagZeroToken : compactTokenAt 0 current.1 = 0 := by
                  simpa [witness] using htagZero
                simpa [compactFormulaTokenStep, hlength, witness,
                  htagZeroToken, hlengthThree, hvalid] using hnextStep
              · have htagOneToken : compactTokenAt 0 current.1 = 1 := by
                  simpa [witness] using htagOne
                simpa [compactFormulaTokenStep, hlength, witness,
                  htagOneToken, hlengthThree, hvalid] using hnextStep
            have hfailure :=
              (compactUnifiedParserSyntaxTermFailureRows_iff
                hcurrent hnext htailRows htailCount).mpr hnextState
            refine ⟨witness, hcurrentRunning, huncons, Or.inr
              ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
                ?_, Or.inl ⟨?_, Or.inr
                  ⟨by simpa only [hcurrent.tokensCount_eq] using hlengthThree,
                    ?_, ?_, Or.inr ⟨hvalid, hfailure⟩⟩⟩⟩⟩
            · simpa only [hcurrent.tokensCount_eq] using htagRows
            · exact hrelationTag
            · simpa only [hcurrent.tokensCount_eq] using harityRows
            · simpa only [hcurrent.tokensCount_eq] using hcodeRows
        · have hnextState : next = compactSyntaxFailure current.1 tail := by
            rcases hrelationTag with htagZero | htagOne
            · have htagZeroToken : compactTokenAt 0 current.1 = 0 := by
                simpa [witness] using htagZero
              simpa [compactFormulaTokenStep, hlength, witness,
                htagZeroToken, hlengthThree] using hnextStep
            · have htagOneToken : compactTokenAt 0 current.1 = 1 := by
                simpa [witness] using htagOne
              simpa [compactFormulaTokenStep, hlength, witness,
                htagOneToken, hlengthThree] using hnextStep
          have hfailure :=
            (compactUnifiedParserSyntaxTermFailureRows_iff
              hcurrent hnext htailRows htailCount).mpr hnextState
          refine ⟨witness, hcurrentRunning, huncons, Or.inr
            ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
              ?_, Or.inl ⟨hrelationTag, Or.inl ⟨?_, hfailure⟩⟩⟩⟩
          · simpa only [hcurrent.tokensCount_eq] using htagRows
          · simpa only [hcurrent.tokensCount_eq] using
              (show current.1.length ≤ 2 by omega)
      · by_cases hatomicTag : witness.tag = 2 ∨ witness.tag = 3
        · have hnextState : next =
              compactSyntaxContinue (current.1.drop 1) tail := by
            rcases hatomicTag with htagTwo | htagThree
            · have htagTwoToken : compactTokenAt 0 current.1 = 2 := by
                simpa [witness] using htagTwo
              simpa [compactFormulaTokenStep, hlength,
                witness, htagTwoToken] using hnextStep
            · have htagThreeToken : compactTokenAt 0 current.1 = 3 := by
                simpa [witness] using htagThree
              simpa [compactFormulaTokenStep, hlength,
                witness, htagThreeToken] using hnextStep
          have hcontinue :=
            (compactUnifiedParserSyntaxTermContinueRows_iff
              hcurrent hnext htailRows htailCount).mpr
                ⟨hlength, hnextState⟩
          refine ⟨witness, hcurrentRunning, huncons, Or.inr
            ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
              ?_, Or.inr (Or.inl ⟨hatomicTag, hcontinue⟩)⟩⟩
          simpa only [hcurrent.tokensCount_eq] using htagRows
        · by_cases hbinaryTag : witness.tag = 4 ∨ witness.tag = 5
          · have hnextState : next =
                compactSyntaxContinue (current.1.drop 1)
                  ((1, binderArity, 0) ::
                    (1, binderArity, 0) :: tail) := by
              rcases hbinaryTag with htagFour | htagFive
              · have htagFourToken : compactTokenAt 0 current.1 = 4 := by
                  simpa [witness] using htagFour
                simpa [compactFormulaTokenStep, hlength, witness,
                  htagFourToken, compactFormulaTask] using hnextStep
              · have htagFiveToken : compactTokenAt 0 current.1 = 5 := by
                  simpa [witness] using htagFive
                simpa [compactFormulaTokenStep, hlength, witness,
                  htagFiveToken, compactFormulaTask] using hnextStep
            have hbinaryRows :=
              (compactUnifiedParserSyntaxFormulaBinaryRows_iff
                hcurrent hnext htailRows htailCount).mpr
                  ⟨hlength, hnextState⟩
            refine ⟨witness, hcurrentRunning, huncons, Or.inr
              ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
                ?_, Or.inr (Or.inr (Or.inl
                  ⟨hbinaryTag, hbinaryRows⟩))⟩⟩
            simpa only [hcurrent.tokensCount_eq] using htagRows
          · by_cases hquantifierTag : witness.tag = 6 ∨ witness.tag = 7
            · have hnextState : next =
                  compactSyntaxContinue (current.1.drop 1)
                    ((1, binderArity + 1, 0) :: tail) := by
                rcases hquantifierTag with htagSix | htagSeven
                · have htagSixToken : compactTokenAt 0 current.1 = 6 := by
                    simpa [witness] using htagSix
                  simpa [compactFormulaTokenStep, hlength, witness,
                    htagSixToken, compactFormulaTask] using hnextStep
                · have htagSevenToken : compactTokenAt 0 current.1 = 7 := by
                    simpa [witness] using htagSeven
                  simpa [compactFormulaTokenStep, hlength, witness,
                    htagSevenToken, compactFormulaTask] using hnextStep
              have hquantifierRows :=
                (compactUnifiedParserSyntaxFormulaQuantifierRows_iff
                  hcurrent hnext htailRows htailCount).mpr
                    ⟨hlength, hnextState⟩
              refine ⟨witness, hcurrentRunning, huncons, Or.inr
                ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
                  ?_, Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨hquantifierTag, hquantifierRows⟩)))⟩⟩
              simpa only [hcurrent.tokensCount_eq] using htagRows
            · have hzero : witness.tag ≠ 0 := by
                intro h
                exact hrelationTag (Or.inl h)
              have hone : witness.tag ≠ 1 := by
                intro h
                exact hrelationTag (Or.inr h)
              have htwo : witness.tag ≠ 2 := by
                intro h
                exact hatomicTag (Or.inl h)
              have hthree : witness.tag ≠ 3 := by
                intro h
                exact hatomicTag (Or.inr h)
              have hfour : witness.tag ≠ 4 := by
                intro h
                exact hbinaryTag (Or.inl h)
              have hfive : witness.tag ≠ 5 := by
                intro h
                exact hbinaryTag (Or.inr h)
              have hsix : witness.tag ≠ 6 := by
                intro h
                exact hquantifierTag (Or.inl h)
              have hseven : witness.tag ≠ 7 := by
                intro h
                exact hquantifierTag (Or.inr h)
              have hnextState : next = compactSyntaxFailure current.1 tail := by
                simpa [compactFormulaTokenStep, hlength, witness,
                  hzero, hone, htwo, hthree, hfour, hfive, hsix, hseven]
                  using hnextStep
              have hfailure :=
                (compactUnifiedParserSyntaxTermFailureRows_iff
                  hcurrent hnext htailRows htailCount).mpr hnextState
              refine ⟨witness, hcurrentRunning, huncons, Or.inr
                ⟨by simpa only [hcurrent.tokensCount_eq] using hlength,
                  ?_, Or.inr (Or.inr (Or.inr (Or.inr
                    ⟨hzero, hone, htwo, hthree, hfour, hfive,
                      hsix, hseven, hfailure⟩)))⟩⟩
              simpa only [hcurrent.tokensCount_eq] using htagRows
    · have hnextState : next = compactSyntaxFailure current.1 tail := by
        simpa [compactFormulaTokenStep, hlength] using hnextStep
      have hfailure :=
        (compactUnifiedParserSyntaxTermFailureRows_iff
          hcurrent hnext htailRows htailCount).mpr hnextState
      refine ⟨witness, hcurrentRunning, huncons, Or.inl ⟨?_, hfailure⟩⟩
      simpa only [hcurrent.tokensCount_eq] using
        (show current.1.length = 0 by omega)

#print axioms compactUnifiedParserSyntaxFormulaBinaryRows_iff
#print axioms compactUnifiedParserSyntaxFormulaQuantifierRows_iff
#print axioms compactUnifiedParserSyntaxFormulaRows_iff

end FoundationCompactNumericListedDirectParserSyntaxFormulaRows
