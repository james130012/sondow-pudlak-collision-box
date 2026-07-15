import integration.FoundationCompactNumericListedDirectVerifierTaskFieldRealization
import integration.FoundationCompactNumericListedDirectOrRuleCheck
import integration.FoundationCompactNumericListedDirectWkRuleCheck

/-!
# Direct rows for conjunction, disjunction, and weakening combines

These are the three combine rules that require no recursive formula
transformation.  Each branch computes the exact rule Boolean and couples it
to the checked push-after-drop relation for the result stack.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSimpleCombineRuleRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectAndRuleCheck
open FoundationCompactNumericListedDirectOrRuleCheck
open FoundationCompactNumericListedDirectWkRuleCheck
open FoundationCompactNumericListedDirectChildResultListPushDropRows

def CompactNumericSimpleCombineRuleRows
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue : Nat) : Prop :=
  (taskTag = 3 ∧
    2 ≤ sourceCount ∧
    CompactAdditiveAndRuleCheck tokenTable width tokenCount
      gammaBoundary gammaCount
      gammaFinish firstFinish firstCount
      firstFinish secondFinish secondCount
      leftGammaBoundary leftGammaCount leftBoolValue
      rightGammaBoundary rightGammaCount rightBoolValue
      resultBoolValue ∧
    CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        gammaBoundary gammaCount tableWidth valueBound 2 resultBoolValue) ∨
  (taskTag = 4 ∧
    1 ≤ sourceCount ∧
    CompactAdditiveOrRuleCheck tokenTable width tokenCount
      gammaBoundary gammaCount
      gammaFinish firstFinish firstCount
      firstFinish secondFinish secondCount
      rightGammaBoundary rightGammaCount rightBoolValue
      resultBoolValue ∧
    CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        gammaBoundary gammaCount tableWidth valueBound 1 resultBoolValue) ∨
  (taskTag = 7 ∧
    1 ≤ sourceCount ∧
    CompactAdditiveWkRuleCheck tokenTable width tokenCount
      gammaBoundary gammaCount
      rightGammaBoundary rightGammaCount rightBoolValue resultBoolValue ∧
    CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        gammaBoundary gammaCount tableWidth valueBound 1 resultBoolValue)

def compactNumericSimpleCombineRuleRowsDef :
    𝚺₀.Semisentence 24 := .mkSigma
  “tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue.
    (taskTag = 3 ∧
      2 ≤ sourceCount ∧
      !(compactAdditiveAndRuleCheckDef)
        tokenTable width tokenCount
        gammaBoundary gammaCount
        gammaFinish firstFinish firstCount
        firstFinish secondFinish secondCount
        leftGammaBoundary leftGammaCount leftBoolValue
        rightGammaBoundary rightGammaCount rightBoolValue
        resultBoolValue ∧
      !(compactNumericChildResultListPushDropRowsDef)
        tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        gammaBoundary gammaCount tableWidth valueBound 2 resultBoolValue) ∨
    (taskTag = 4 ∧
      1 ≤ sourceCount ∧
      !(compactAdditiveOrRuleCheckDef)
        tokenTable width tokenCount
        gammaBoundary gammaCount
        gammaFinish firstFinish firstCount
        firstFinish secondFinish secondCount
        rightGammaBoundary rightGammaCount rightBoolValue
        resultBoolValue ∧
      !(compactNumericChildResultListPushDropRowsDef)
        tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        gammaBoundary gammaCount tableWidth valueBound 1 resultBoolValue) ∨
    (taskTag = 7 ∧
      1 ≤ sourceCount ∧
      !(compactAdditiveWkRuleCheckDef)
        tokenTable width tokenCount
        gammaBoundary gammaCount
        rightGammaBoundary rightGammaCount rightBoolValue resultBoolValue ∧
      !(compactNumericChildResultListPushDropRowsDef)
        tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        gammaBoundary gammaCount tableWidth valueBound 1 resultBoolValue)”

def compactNumericSimpleCombineRuleRowsEnvironment
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue : Nat) : Fin 24 → Nat :=
  ![tokenTable, width, tokenCount,
    taskTag, gammaFinish, gammaCount, gammaBoundary,
    firstFinish, firstCount, secondFinish, secondCount,
    rightGammaCount, rightGammaBoundary, rightBoolValue,
    leftGammaCount, leftGammaBoundary, leftBoolValue,
    sourceBoundary, sourceCount, targetBoundary, targetCount,
    tableWidth, valueBound, resultBoolValue]

@[simp] theorem compactNumericSimpleCombineRuleRowsDef_spec
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue : Nat) :
    compactNumericSimpleCombineRuleRowsDef.val.Evalb
        (compactNumericSimpleCombineRuleRowsEnvironment
          tokenTable width tokenCount
          taskTag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          rightGammaCount rightGammaBoundary rightBoolValue
          leftGammaCount leftGammaBoundary leftBoolValue
          sourceBoundary sourceCount targetBoundary targetCount
          tableWidth valueBound resultBoolValue) ↔
      CompactNumericSimpleCombineRuleRows
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
  change compactNumericSimpleCombineRuleRowsDef.val.Evalb env ↔ _
  have handEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2,
          #6, #5, #4, #7, #8, #7, #9, #10,
          #15, #14, #16, #12, #11, #13, #23]) =
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          gammaFinish, firstFinish, firstCount,
          firstFinish, secondFinish, secondCount,
          leftGammaBoundary, leftGammaCount, leftBoolValue,
          rightGammaBoundary, rightGammaCount, rightBoolValue,
          resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have horEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2,
          #6, #5, #4, #7, #8, #7, #9, #10,
          #12, #11, #13, #23]) =
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          gammaFinish, firstFinish, firstCount,
          firstFinish, secondFinish, secondCount,
          rightGammaBoundary, rightGammaCount, rightBoolValue,
          resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hwkEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2,
          #6, #5, #12, #11, #13, #23]) =
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          rightGammaBoundary, rightGammaCount, rightBoolValue,
          resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hpushTwoEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2,
          #17, #18, #19, #20, #6, #5, #21, #22,
          (↑(2 : Nat) : Semiterm ℒₒᵣ Empty 24), #23]) =
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          gammaBoundary, gammaCount, tableWidth, valueBound,
          2, resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hpushOneEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 24), #1, #2,
          #17, #18, #19, #20, #6, #5, #21, #22,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 24), #23]) =
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          gammaBoundary, gammaCount, tableWidth, valueBound,
          1, resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htagValue : env 3 = taskTag := rfl
  have hsourceCountValue : env 18 = sourceCount := rfl
  simp [compactNumericSimpleCombineRuleRowsDef,
    CompactNumericSimpleCombineRuleRows,
    handEnv, horEnv, hwkEnv, hpushTwoEnv, hpushOneEnv,
    htagValue, hsourceCountValue]
  rfl

theorem compactNumericSimpleCombineRuleRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericSimpleCombineRuleRowsDef.val := by
  simp [compactNumericSimpleCombineRuleRowsDef]

theorem compactNumericSimpleCombineRuleRows_iff
    {tokenTable width tokenCount taskTag
      gammaFinish gammaBoundary firstFinish secondFinish
      rightGammaBoundary rightBoolValue
      leftGammaBoundary leftBoolValue
      sourceBoundary targetBoundary tableWidth valueBound resultBoolValue : Nat}
    {Gamma : List (List Nat)} {firstFormula secondFormula : List Nat}
    {rightConclusion leftConclusion : List (List Nat)}
    {rightValid leftValid : Bool}
    {source target : List CompactNumericChildResult}
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hfirst : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount gammaFinish firstFinish firstFormula)
    (hsecond : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount firstFinish secondFinish secondFormula)
    (hright : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        rightGammaBoundary rightConclusion)
    (hleft : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        leftGammaBoundary leftConclusion)
    (hrightBool : rightBoolValue = compactAdditiveBoolTag rightValid)
    (hleftBool : leftBoolValue = compactAdditiveBoolTag leftValid)
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
    CompactNumericSimpleCombineRuleRows
        tokenTable width tokenCount
        taskTag gammaFinish Gamma.length gammaBoundary
        firstFinish firstFormula.length secondFinish secondFormula.length
        rightConclusion.length rightGammaBoundary rightBoolValue
        leftConclusion.length leftGammaBoundary leftBoolValue
        sourceBoundary source.length targetBoundary target.length
        tableWidth valueBound resultBoolValue ↔
      (taskTag = 3 ∧
        2 ≤ source.length ∧
        resultBoolValue = compactAdditiveBoolTag
          (compactAndRuleCheck
            (Gamma, (firstFormula, (secondFormula,
              ((leftConclusion, leftValid),
                (rightConclusion, rightValid)))))) ∧
        target =
          (Gamma, compactAndRuleCheck
            (Gamma, (firstFormula, (secondFormula,
              ((leftConclusion, leftValid),
                (rightConclusion, rightValid)))))) :: source.drop 2) ∨
      (taskTag = 4 ∧
        1 ≤ source.length ∧
        resultBoolValue = compactAdditiveBoolTag
          (compactOrRuleCheck
            (Gamma, (firstFormula, (secondFormula,
              (rightConclusion, rightValid))))) ∧
        target =
          (Gamma, compactOrRuleCheck
            (Gamma, (firstFormula, (secondFormula,
              (rightConclusion, rightValid))))) :: source.drop 1) ∨
      (taskTag = 7 ∧
        1 ≤ source.length ∧
        resultBoolValue = compactAdditiveBoolTag
          (compactWkRuleCheck (Gamma, (rightConclusion, rightValid))) ∧
        target =
          (Gamma, compactWkRuleCheck
            (Gamma, (rightConclusion, rightValid))) :: source.drop 1) := by
  simp only [CompactNumericSimpleCombineRuleRows]
  rw [compactAdditiveAndRuleCheck_iff
      hGamma hfirst hsecond hleft hright hleftBool hrightBool,
    compactAdditiveOrRuleCheck_iff
      hGamma hfirst hsecond hright hrightBool,
    compactAdditiveWkRuleCheck_iff hGamma hright hrightBool]
  set andResult : Bool := compactAndRuleCheck
    (Gamma, firstFormula, secondFormula,
      (leftConclusion, leftValid), rightConclusion, rightValid)
  set orResult : Bool := compactOrRuleCheck
    (Gamma, firstFormula, secondFormula, rightConclusion, rightValid)
  set wkResult : Bool := compactWkRuleCheck
    (Gamma, rightConclusion, rightValid)
  constructor
  · intro h
    rcases h with hAnd | hOr | hWk
    · rcases hAnd with ⟨htag, hcount, hresult, hpush⟩
      left
      refine ⟨htag, hcount, hresult, ?_⟩
      rw [hresult] at hpush
      have hpushExact :=
        (compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
        (consumed := 2)
        (expectedResult := andResult)
        hsourceRows htargetRows hGamma hsourceGraph htargetGraph).mp hpush
      exact hpushExact.2
    · rcases hOr with ⟨htag, hcount, hresult, hpush⟩
      right
      left
      refine ⟨htag, hcount, hresult, ?_⟩
      rw [hresult] at hpush
      have hpushExact :=
        (compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
        (consumed := 1)
        (expectedResult := orResult)
        hsourceRows htargetRows hGamma hsourceGraph htargetGraph).mp hpush
      exact hpushExact.2
    · rcases hWk with ⟨htag, hcount, hresult, hpush⟩
      right
      right
      refine ⟨htag, hcount, hresult, ?_⟩
      rw [hresult] at hpush
      have hpushExact :=
        (compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
        (consumed := 1)
        (expectedResult := wkResult)
        hsourceRows htargetRows hGamma hsourceGraph htargetGraph).mp hpush
      exact hpushExact.2
  · intro h
    rcases h with hAnd | hOr | hWk
    · rcases hAnd with ⟨htag, hcount, hresult, htarget⟩
      left
      refine ⟨htag, hcount, hresult, ?_⟩
      have hpush :=
        (compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
          (consumed := 2)
          (expectedResult := andResult)
          hsourceRows htargetRows hGamma hsourceGraph htargetGraph).mpr
            ⟨hcount, htarget⟩
      rw [← hresult] at hpush
      exact hpush
    · rcases hOr with ⟨htag, hcount, hresult, htarget⟩
      right
      left
      refine ⟨htag, hcount, hresult, ?_⟩
      have hpush :=
        (compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
          (consumed := 1)
          (expectedResult := orResult)
          hsourceRows htargetRows hGamma hsourceGraph htargetGraph).mpr
            ⟨hcount, htarget⟩
      rw [← hresult] at hpush
      exact hpush
    · rcases hWk with ⟨htag, hcount, hresult, htarget⟩
      right
      right
      refine ⟨htag, hcount, hresult, ?_⟩
      have hpush :=
        (compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
          (consumed := 1)
          (expectedResult := wkResult)
          hsourceRows htargetRows hGamma hsourceGraph htargetGraph).mpr
            ⟨hcount, htarget⟩
      rw [← hresult] at hpush
      exact hpush

#print axioms compactNumericSimpleCombineRuleRowsDef_spec
#print axioms compactNumericSimpleCombineRuleRowsDef_sigmaZero
#print axioms compactNumericSimpleCombineRuleRows_iff

end FoundationCompactNumericListedDirectSimpleCombineRuleRows
