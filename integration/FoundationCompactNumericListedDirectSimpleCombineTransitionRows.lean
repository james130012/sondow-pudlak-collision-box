import integration.FoundationCompactNumericListedDirectSimpleCombineRuleRows
import integration.FoundationCompactNumericListedDirectNatListListRowsRealization

/-!
# Source-linked direct rows for simple combine rules

The earlier local rule graph computes the correct Boolean and target push but
does not itself identify the supplied child conclusions with the actual source
stack.  This strengthening adds that missing link and proves soundness against
the public combine transition for And, Or, and weakening.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSimpleCombineTransitionRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectNatListListRowsRealization
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectChildResultBoundedHeadEquality
open FoundationCompactNumericListedDirectChildResultListPushDropRows
open FoundationCompactNumericListedDirectSimpleCombineRuleRows
open FoundationCompactNumericListedDirectAndRuleCheck
open FoundationCompactNumericListedDirectOrRuleCheck
open FoundationCompactNumericListedDirectWkRuleCheck
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization

def CompactNumericSimpleCombineTransitionRows
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue : Nat) : Prop :=
  CompactNumericSimpleCombineRuleRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue ∧
    CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount rightGammaBoundary rightGammaCount ∧
    CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount sourceBoundary
        rightGammaBoundary rightGammaCount valueBound 0 rightBoolValue ∧
    (taskTag = 3 →
      CompactAdditiveNatListListRowsWellFormed
        tokenTable width tokenCount leftGammaBoundary leftGammaCount ∧
      CompactNumericChildResultBoundedHeadEq
        tokenTable width tokenCount sourceBoundary
          leftGammaBoundary leftGammaCount valueBound 1 leftBoolValue)

def compactNumericSimpleCombineTransitionRowsDef :
    𝚺₀.Semisentence 24 := .mkSigma
  “tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue.
    !(compactNumericSimpleCombineRuleRowsDef)
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue ∧
    !(compactAdditiveNatListListRowsWellFormedDef)
      tokenTable width tokenCount rightGammaBoundary rightGammaCount ∧
    !(compactNumericChildResultBoundedHeadEqDef)
      tokenTable width tokenCount sourceBoundary
        rightGammaBoundary rightGammaCount valueBound 0 rightBoolValue ∧
    (taskTag = 3 →
      !(compactAdditiveNatListListRowsWellFormedDef)
        tokenTable width tokenCount leftGammaBoundary leftGammaCount ∧
      !(compactNumericChildResultBoundedHeadEqDef)
        tokenTable width tokenCount sourceBoundary
          leftGammaBoundary leftGammaCount valueBound 1 leftBoolValue)”

@[simp] theorem compactNumericSimpleCombineTransitionRowsDef_spec
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue : Nat) :
    compactNumericSimpleCombineTransitionRowsDef.val.Evalb
        (compactNumericSimpleCombineRuleRowsEnvironment
          tokenTable width tokenCount
          taskTag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          rightGammaCount rightGammaBoundary rightBoolValue
          leftGammaCount leftGammaBoundary leftBoolValue
          sourceBoundary sourceCount targetBoundary targetCount
          tableWidth valueBound resultBoolValue) ↔
      CompactNumericSimpleCombineTransitionRows
        tokenTable width tokenCount
        taskTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        rightGammaCount rightGammaBoundary rightBoolValue
        leftGammaCount leftGammaBoundary leftBoolValue
        sourceBoundary sourceCount targetBoundary targetCount
        tableWidth valueBound resultBoolValue := by
  let env := compactNumericSimpleCombineRuleRowsEnvironment
    tokenTable width tokenCount
    taskTag gammaFinish gammaCount gammaBoundary
    firstFinish firstCount secondFinish secondCount
    rightGammaCount rightGammaBoundary rightBoolValue
    leftGammaCount leftGammaBoundary leftBoolValue
    sourceBoundary sourceCount targetBoundary targetCount
    tableWidth valueBound resultBoolValue
  change compactNumericSimpleCombineTransitionRowsDef.val.Evalb env ↔ _
  have hbaseEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #11, #12, #13, #14, #15, #16,
          #17, #18, #19, #20, #21, #22, #23]) = env := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hbaseSpec :
      compactNumericSimpleCombineRuleRowsDef.val.Evalb env ↔
        CompactNumericSimpleCombineRuleRows
          tokenTable width tokenCount
          taskTag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          rightGammaCount rightGammaBoundary rightBoolValue
          leftGammaCount leftGammaBoundary leftBoolValue
          sourceBoundary sourceCount targetBoundary targetCount
          tableWidth valueBound resultBoolValue := by
    simpa [env] using compactNumericSimpleCombineRuleRowsDef_spec
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue
  have hrightRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #12, #11]) =
        ![tokenTable, width, tokenCount,
          rightGammaBoundary, rightGammaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hrightHeadEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #17,
          #12, #11, #22, (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 24), #13]) =
        ![tokenTable, width, tokenCount, sourceBoundary,
          rightGammaBoundary, rightGammaCount, valueBound,
          0, rightBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hleftRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #15, #14]) =
        ![tokenTable, width, tokenCount,
          leftGammaBoundary, leftGammaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hleftHeadEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2, #17,
          #15, #14, #22, (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 24), #16]) =
        ![tokenTable, width, tokenCount, sourceBoundary,
          leftGammaBoundary, leftGammaCount, valueBound,
          1, leftBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htagValue : env 3 = taskTag := rfl
  simp [compactNumericSimpleCombineTransitionRowsDef,
    CompactNumericSimpleCombineTransitionRows,
    hbaseEnv, hbaseSpec, hrightRowsEnv, hrightHeadEnv,
    hleftRowsEnv, hleftHeadEnv, htagValue]
  tauto

theorem compactNumericSimpleCombineTransitionRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericSimpleCombineTransitionRowsDef.val := by
  simp [compactNumericSimpleCombineTransitionRowsDef]

theorem CompactNumericSimpleCombineTransitionRows.sound
    {tokenTable width tokenCount taskTag
      gammaFinish gammaBoundary firstFinish secondFinish
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary targetBoundary tableWidth valueBound
      resultBoolValue : Nat}
    {Gamma : List (List Nat)} {firstFormula secondFormula : List Nat}
    {source target : List CompactNumericChildResult}
    (hrows : CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      taskTag gammaFinish Gamma.length gammaBoundary
      firstFinish firstFormula.length secondFinish secondFormula.length
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary source.length targetBoundary target.length
      tableWidth valueBound resultBoolValue)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hfirst : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount gammaFinish firstFinish firstFormula)
    (hsecond : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount firstFinish secondFinish secondFormula)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound) :
    (taskTag = 3 ∧
      2 ≤ source.length ∧
      resultBoolValue = compactAdditiveBoolTag
        (compactAndRuleCheck
          (Gamma, (firstFormula, (secondFormula,
            (source.getI 1, source.getI 0))))) ∧
      target =
        (Gamma, compactAndRuleCheck
          (Gamma, (firstFormula, (secondFormula,
            (source.getI 1, source.getI 0))))) :: source.drop 2) ∨
    (taskTag = 4 ∧
      1 ≤ source.length ∧
      resultBoolValue = compactAdditiveBoolTag
        (compactOrRuleCheck
          (Gamma, (firstFormula, (secondFormula, source.getI 0)))) ∧
      target =
        (Gamma, compactOrRuleCheck
          (Gamma, (firstFormula, (secondFormula, source.getI 0)))) ::
            source.drop 1) ∨
    (taskTag = 7 ∧
      1 ≤ source.length ∧
      resultBoolValue = compactAdditiveBoolTag
        (compactWkRuleCheck (Gamma, source.getI 0)) ∧
      target =
        (Gamma, compactWkRuleCheck (Gamma, source.getI 0)) ::
          source.drop 1) := by
  rcases hrows with ⟨hbase, hrightWellFormed, hrightHead, hleftLink⟩
  rcases CompactAdditiveNatListListRowsWellFormed.realizeRows
      hrightWellFormed with
    ⟨rightConclusion, hrightLength, hrightRows⟩
  subst rightGammaCount
  rcases hrightHead.exists_boolTag with ⟨rightValid, hrightBool⟩
  have hrightHead' : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount sourceBoundary
        rightGammaBoundary rightConclusion.length valueBound 0
        (compactAdditiveBoolTag rightValid) := by
    simpa only [hrightBool] using hrightHead
  have hrightValue := hrightHead'.value_eq
    (target := source) (by
      simp only [CompactNumericSimpleCombineRuleRows] at hbase
      rcases hbase with hAnd | hOr | hWk <;> omega)
    hrightRows hsourceRows
  simp only [CompactNumericSimpleCombineRuleRows] at hbase
  rcases hbase with hAnd | hOr | hWk
  · rcases hAnd with ⟨htag, hcount, hcheck, hpush⟩
    rcases hleftLink htag with ⟨hleftWellFormed, hleftHead⟩
    rcases CompactAdditiveNatListListRowsWellFormed.realizeRows
        hleftWellFormed with
      ⟨leftConclusion, hleftLength, hleftRows⟩
    subst leftGammaCount
    rcases hleftHead.exists_boolTag with ⟨leftValid, hleftBool⟩
    have hleftHead' : CompactNumericChildResultBoundedHeadEq
        tokenTable width tokenCount sourceBoundary
          leftGammaBoundary leftConclusion.length valueBound 1
          (compactAdditiveBoolTag leftValid) := by
      simpa only [hleftBool] using hleftHead
    have hleftValue := hleftHead'.value_eq
      (target := source) (by omega) hleftRows hsourceRows
    have hresult :=
      (compactAdditiveAndRuleCheck_iff
        hGamma hfirst hsecond hleftRows hrightRows
          hleftBool hrightBool).mp hcheck
    rw [hresult] at hpush
    have htarget :=
      ((compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
        (consumed := 2)
        (expectedResult := compactAndRuleCheck
          (Gamma, firstFormula, secondFormula,
            (leftConclusion, leftValid), rightConclusion, rightValid))
        hsourceRows htargetRows hGamma hsourceGraph htargetGraph).mp
          hpush).2
    left
    refine ⟨htag, hcount, ?_, ?_⟩
    · simpa only [hrightValue, hleftValue] using hresult
    · simpa only [hrightValue, hleftValue] using htarget
  · rcases hOr with ⟨htag, hcount, hcheck, hpush⟩
    have hresult :=
      (compactAdditiveOrRuleCheck_iff
        hGamma hfirst hsecond hrightRows hrightBool).mp hcheck
    rw [hresult] at hpush
    have htarget :=
      ((compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
        (consumed := 1)
        (expectedResult := compactOrRuleCheck
          (Gamma, firstFormula, secondFormula,
            rightConclusion, rightValid))
        hsourceRows htargetRows hGamma hsourceGraph htargetGraph).mp
          hpush).2
    right
    left
    refine ⟨htag, hcount, ?_, ?_⟩
    · simpa only [hrightValue] using hresult
    · simpa only [hrightValue] using htarget
  · rcases hWk with ⟨htag, hcount, hcheck, hpush⟩
    have hresult :=
      (compactAdditiveWkRuleCheck_iff
        hGamma hrightRows hrightBool).mp hcheck
    rw [hresult] at hpush
    have htarget :=
      ((compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
        (consumed := 1)
        (expectedResult := compactWkRuleCheck
          (Gamma, rightConclusion, rightValid))
        hsourceRows htargetRows hGamma hsourceGraph htargetGraph).mp
          hpush).2
    right
    right
    refine ⟨htag, hcount, ?_, ?_⟩
    · simpa only [hrightValue] using hresult
    · simpa only [hrightValue] using htarget

theorem CompactNumericSimpleCombineTransitionRows.sound_combineTransition
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    {task : CompactNumericVerifierTask}
    {source target : List CompactNumericChildResult}
    {rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary targetBoundary tableWidth valueBound
      resultBoolValue : Nat}
    (hcore : CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (htask : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount coordinates.start coordinates.finish task)
    (hrows : CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      coordinates.tag coordinates.gammaFinish coordinates.gammaCount
        coordinates.gammaBoundary
      coordinates.firstFinish coordinates.firstCount
        coordinates.secondFinish coordinates.secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary source.length targetBoundary target.length
      tableWidth valueBound resultBoolValue)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound) :
    ∃ combined,
      compactNumericCombineTransition task source = some combined ∧
      target = combined.1 :: combined.2 := by
  rcases CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
      hcore with
    ⟨realizedTask, hrealizedTask, htag,
      hGamma, hGammaLength,
      hfirst, hfirstLength,
      hsecond, hsecondLength,
      _hwitness, _hwitnessLength,
      _hsuffix, _hsuffixLength⟩
  have hrealizedTaskEq : realizedTask = task :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hcore htask hrealizedTask
  subst task
  have hrows' : CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      coordinates.tag coordinates.gammaFinish realizedTask.2.1.length
        coordinates.gammaBoundary
      coordinates.firstFinish realizedTask.2.2.1.length
        coordinates.secondFinish realizedTask.2.2.2.1.length
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary source.length targetBoundary target.length
      tableWidth valueBound resultBoolValue := by
    simpa only [hGammaLength, hfirstLength, hsecondLength] using hrows
  have hsound := CompactNumericSimpleCombineTransitionRows.sound
    hrows' hGamma hfirst hsecond hsourceRows htargetRows
      hsourceGraph htargetGraph
  rcases hsound with hAnd | hOr | hWk
  · rcases hAnd with ⟨htagThree, hcount, _hresult, htarget⟩
    have htaskTag : realizedTask.1 = 3 := htag.trans htagThree
    have hhead : source.head?.getD compactNumericDefaultChildResult =
        source.getI 0 := by
      cases source with
      | nil => simp at hcount
      | cons head tail => simp
    have hsecondValue : source[1]?.getD
        compactNumericDefaultChildResult = source.getI 1 := by
      cases source with
      | nil => simp at hcount
      | cons first rest =>
          cases rest with
          | nil => simp at hcount
          | cons second tail => simp
    let result := compactAndRuleCheck
      (realizedTask.2.1,
        (realizedTask.2.2.1,
          (realizedTask.2.2.2.1, (source.getI 1, source.getI 0))))
    refine ⟨((realizedTask.2.1, result), source.drop 2), ?_, ?_⟩
    · simp [compactNumericCombineTransition, htaskTag, hcount,
        hhead, hsecondValue, result]
    · simpa [result] using htarget
  · rcases hOr with ⟨htagFour, hcount, _hresult, htarget⟩
    have htaskTag : realizedTask.1 = 4 := htag.trans htagFour
    have hhead : source.head?.getD compactNumericDefaultChildResult =
        source.getI 0 := by
      cases source with
      | nil => simp at hcount
      | cons head tail => simp
    let result := compactOrRuleCheck
      (realizedTask.2.1,
        (realizedTask.2.2.1,
          (realizedTask.2.2.2.1, source.getI 0)))
    refine ⟨((realizedTask.2.1, result), source.tail), ?_, ?_⟩
    · simp [compactNumericCombineTransition, htaskTag, hcount,
        hhead, result]
    · simpa [result] using htarget
  · rcases hWk with ⟨htagSeven, hcount, _hresult, htarget⟩
    have htaskTag : realizedTask.1 = 7 := htag.trans htagSeven
    have hhead : source.head?.getD compactNumericDefaultChildResult =
        source.getI 0 := by
      cases source with
      | nil => simp at hcount
      | cons head tail => simp
    let result := compactWkRuleCheck
      (realizedTask.2.1, source.getI 0)
    refine ⟨((realizedTask.2.1, result), source.tail), ?_, ?_⟩
    · simp [compactNumericCombineTransition, htaskTag, hcount,
        hhead, result]
    · simpa [result] using htarget

#print axioms compactNumericSimpleCombineTransitionRowsDef_spec
#print axioms compactNumericSimpleCombineTransitionRowsDef_sigmaZero
#print axioms CompactNumericSimpleCombineTransitionRows.sound
#print axioms CompactNumericSimpleCombineTransitionRows.sound_combineTransition

end FoundationCompactNumericListedDirectSimpleCombineTransitionRows
