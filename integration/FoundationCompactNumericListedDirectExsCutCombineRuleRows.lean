import integration.FoundationCompactNumericListedDirectNatListWitnessRows
import integration.FoundationCompactNumericListedDirectNatListListRowsRealization
import integration.FoundationCompactNumericListedDirectExsRuleCheck
import integration.FoundationCompactNumericListedDirectCutRuleCheck
import integration.FoundationCompactNumericListedDirectChildResultListPushDropRows
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
import integration.FoundationCompactNumericListedDirectVerifierTaskFieldRealization

/-!
# Direct combine rows for existential introduction and cut

Both branches carry an unconditional exact formula-transform trace.  Flat
formula, transformed-output, and empty-list witnesses are self-contained
bounded row graphs, while the result stack is the checked push-after-drop
relation used by the public combine transition.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectExsCutCombineRuleRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectNatListListRowsRealization
open FoundationCompactNumericListedDirectExsRuleCheck
open FoundationCompactNumericListedDirectCutRuleCheck
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectChildResultBoundedHeadEquality
open FoundationCompactNumericListedDirectChildResultListPushDropRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization

def CompactNumericExsCutCombineRuleRows
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish witnessFinish witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue : Nat) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount gammaFinish firstCount firstFinish
        formulaBoundary formulaBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount transformedStart transformedCount
        transformedFinish transformedBoundary transformedBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount emptyStart 0 emptyFinish
        emptyBoundary emptyBoundarySize ∧
    ((taskTag = 6 ∧
      1 ≤ sourceCount ∧
      CompactAdditiveNatListListRowsWellFormed
        tokenTable width tokenCount rightGammaBoundary rightGammaCount ∧
      CompactNumericChildResultBoundedHeadEq
        tokenTable width tokenCount sourceBoundary
        rightGammaBoundary rightGammaCount valueBound 0 rightBoolValue ∧
      CompactAdditiveExsRuleCheck
        tokenTable width tokenCount
        gammaBoundary gammaCount
        gammaFinish firstFinish formulaBoundary firstCount
        secondFinish witnessFinish witnessCount
        rightGammaBoundary rightGammaCount rightBoolValue
        transformedStart transformedFinish transformedBoundary
          transformedCount
        transformStateBoundary transformStateCount emptyBoundary
        transformTableWidth transformValueBound resultBoolValue ∧
      CompactNumericChildResultListPushDropRows
        tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        gammaBoundary gammaCount tableWidth valueBound 1 resultBoolValue) ∨
     (taskTag = 9 ∧
      2 ≤ sourceCount ∧
      CompactAdditiveNatListListRowsWellFormed
        tokenTable width tokenCount rightGammaBoundary rightGammaCount ∧
      CompactAdditiveNatListListRowsWellFormed
        tokenTable width tokenCount leftGammaBoundary leftGammaCount ∧
      CompactNumericChildResultBoundedHeadEq
        tokenTable width tokenCount sourceBoundary
        rightGammaBoundary rightGammaCount valueBound 0 rightBoolValue ∧
      CompactNumericChildResultBoundedHeadEq
        tokenTable width tokenCount sourceBoundary
        leftGammaBoundary leftGammaCount valueBound 1 leftBoolValue ∧
      CompactAdditiveCutRuleCheck
        tokenTable width tokenCount
        gammaBoundary gammaCount
        gammaFinish firstFinish formulaBoundary firstCount
        leftGammaBoundary leftGammaCount leftBoolValue
        rightGammaBoundary rightGammaCount rightBoolValue
        transformedStart transformedFinish transformedBoundary
          transformedCount
        transformStateBoundary transformStateCount
        emptyStart emptyFinish emptyBoundary
        transformTableWidth transformValueBound resultBoolValue ∧
      CompactNumericChildResultListPushDropRows
        tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        gammaBoundary gammaCount tableWidth valueBound 2 resultBoolValue))

def compactNumericExsCutCombineRuleRowsDef :
    𝚺₀.Semisentence 40 := .mkSigma
  “tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish witnessFinish witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount gammaFinish firstCount firstFinish
        formulaBoundary formulaBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount transformedStart transformedCount
        transformedFinish transformedBoundary transformedBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount emptyStart 0 emptyFinish
        emptyBoundary emptyBoundarySize ∧
    ((taskTag = 6 ∧
      1 ≤ sourceCount ∧
      !(compactAdditiveNatListListRowsWellFormedDef)
        tokenTable width tokenCount rightGammaBoundary rightGammaCount ∧
      !(compactNumericChildResultBoundedHeadEqDef)
        tokenTable width tokenCount sourceBoundary
        rightGammaBoundary rightGammaCount valueBound 0 rightBoolValue ∧
      !(compactAdditiveExsRuleCheckDef)
        tokenTable width tokenCount
        gammaBoundary gammaCount
        gammaFinish firstFinish formulaBoundary firstCount
        secondFinish witnessFinish witnessCount
        rightGammaBoundary rightGammaCount rightBoolValue
        transformedStart transformedFinish transformedBoundary
          transformedCount
        transformStateBoundary transformStateCount emptyBoundary
        transformTableWidth transformValueBound resultBoolValue ∧
      !(compactNumericChildResultListPushDropRowsDef)
        tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        gammaBoundary gammaCount tableWidth valueBound 1 resultBoolValue) ∨
     (taskTag = 9 ∧
      2 ≤ sourceCount ∧
      !(compactAdditiveNatListListRowsWellFormedDef)
        tokenTable width tokenCount rightGammaBoundary rightGammaCount ∧
      !(compactAdditiveNatListListRowsWellFormedDef)
        tokenTable width tokenCount leftGammaBoundary leftGammaCount ∧
      !(compactNumericChildResultBoundedHeadEqDef)
        tokenTable width tokenCount sourceBoundary
        rightGammaBoundary rightGammaCount valueBound 0 rightBoolValue ∧
      !(compactNumericChildResultBoundedHeadEqDef)
        tokenTable width tokenCount sourceBoundary
        leftGammaBoundary leftGammaCount valueBound 1 leftBoolValue ∧
      !(compactAdditiveCutRuleCheckDef)
        tokenTable width tokenCount
        gammaBoundary gammaCount
        gammaFinish firstFinish formulaBoundary firstCount
        leftGammaBoundary leftGammaCount leftBoolValue
        rightGammaBoundary rightGammaCount rightBoolValue
        transformedStart transformedFinish transformedBoundary
          transformedCount
        transformStateBoundary transformStateCount
        emptyStart emptyFinish emptyBoundary
        transformTableWidth transformValueBound resultBoolValue ∧
      !(compactNumericChildResultListPushDropRowsDef)
        tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        gammaBoundary gammaCount tableWidth valueBound 2 resultBoolValue))”

def compactNumericExsCutCombineRuleRowsEnvironment
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish witnessFinish witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue : Nat) : Fin 40 → Nat :=
  ![tokenTable, width, tokenCount,
    taskTag, gammaFinish, gammaCount, gammaBoundary,
    firstFinish, firstCount, secondFinish, witnessFinish, witnessCount,
    rightGammaCount, rightGammaBoundary, rightBoolValue,
    leftGammaCount, leftGammaBoundary, leftBoolValue,
    sourceBoundary, sourceCount, targetBoundary, targetCount,
    formulaBoundary, formulaBoundarySize,
    transformedStart, transformedFinish, transformedBoundary,
    transformedCount, transformedBoundarySize,
    transformStateBoundary, transformStateCount,
    emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
    transformTableWidth, transformValueBound,
    tableWidth, valueBound, resultBoolValue]

@[simp] theorem compactNumericExsCutCombineRuleRowsDef_spec
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish witnessFinish witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue : Nat) :
    compactNumericExsCutCombineRuleRowsDef.val.Evalb
      (compactNumericExsCutCombineRuleRowsEnvironment
        tokenTable width tokenCount
        taskTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish witnessFinish witnessCount
        rightGammaCount rightGammaBoundary rightBoolValue
        leftGammaCount leftGammaBoundary leftBoolValue
        sourceBoundary sourceCount targetBoundary targetCount
        formulaBoundary formulaBoundarySize
        transformedStart transformedFinish transformedBoundary
        transformedCount transformedBoundarySize
        transformStateBoundary transformStateCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        transformTableWidth transformValueBound
        tableWidth valueBound resultBoolValue) ↔
      CompactNumericExsCutCombineRuleRows
        tokenTable width tokenCount
        taskTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish witnessFinish witnessCount
        rightGammaCount rightGammaBoundary rightBoolValue
        leftGammaCount leftGammaBoundary leftBoolValue
        sourceBoundary sourceCount targetBoundary targetCount
        formulaBoundary formulaBoundarySize
        transformedStart transformedFinish transformedBoundary
        transformedCount transformedBoundarySize
        transformStateBoundary transformStateCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        transformTableWidth transformValueBound
        tableWidth valueBound resultBoolValue := by
  let env := compactNumericExsCutCombineRuleRowsEnvironment
    tokenTable width tokenCount
    taskTag gammaFinish gammaCount gammaBoundary
    firstFinish firstCount secondFinish witnessFinish witnessCount
    rightGammaCount rightGammaBoundary rightBoolValue
    leftGammaCount leftGammaBoundary leftBoolValue
    sourceBoundary sourceCount targetBoundary targetCount
    formulaBoundary formulaBoundarySize
    transformedStart transformedFinish transformedBoundary
    transformedCount transformedBoundarySize
    transformStateBoundary transformStateCount
    emptyStart emptyFinish emptyBoundary emptyBoundarySize
    transformTableWidth transformValueBound
    tableWidth valueBound resultBoolValue
  change compactNumericExsCutCombineRuleRowsDef.val.Evalb env ↔ _
  have hformulaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2, #4, #8, #7,
          #22, #23]) =
        ![tokenTable, width, tokenCount, gammaFinish, firstCount,
          firstFinish, formulaBoundary, formulaBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htransformedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2, #24, #27, #25,
          #26, #28]) =
        ![tokenTable, width, tokenCount, transformedStart,
          transformedCount, transformedFinish, transformedBoundary,
          transformedBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hemptyEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2, #31,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 40), #32, #33, #34]) =
        ![tokenTable, width, tokenCount, emptyStart, 0,
          emptyFinish, emptyBoundary, emptyBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hrightHeadEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2, #18,
          #13, #12, #38, (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 40),
          #14]) =
        ![tokenTable, width, tokenCount, sourceBoundary,
          rightGammaBoundary, rightGammaCount, valueBound,
          0, rightBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hrightRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2, #13, #12]) =
        ![tokenTable, width, tokenCount,
          rightGammaBoundary, rightGammaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hleftRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2, #16, #15]) =
        ![tokenTable, width, tokenCount,
          leftGammaBoundary, leftGammaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hleftHeadEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2, #18,
          #16, #15, #38, (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 40),
          #17]) =
        ![tokenTable, width, tokenCount, sourceBoundary,
          leftGammaBoundary, leftGammaCount, valueBound,
          1, leftBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hexsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2, #6, #5,
          #4, #7, #22, #8, #9, #10, #11,
          #13, #12, #14, #24, #25, #26, #27,
          #29, #30, #33, #35, #36, #39]) =
        ![tokenTable, width, tokenCount, gammaBoundary, gammaCount,
          gammaFinish, firstFinish, formulaBoundary, firstCount,
          secondFinish, witnessFinish, witnessCount,
          rightGammaBoundary, rightGammaCount, rightBoolValue,
          transformedStart, transformedFinish, transformedBoundary,
          transformedCount, transformStateBoundary, transformStateCount,
          emptyBoundary, transformTableWidth, transformValueBound,
          resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2, #6, #5,
          #4, #7, #22, #8, #16, #15, #17, #13, #12, #14,
          #24, #25, #26, #27, #29, #30, #31, #32, #33,
          #35, #36, #39]) =
        ![tokenTable, width, tokenCount, gammaBoundary, gammaCount,
          gammaFinish, firstFinish, formulaBoundary, firstCount,
          leftGammaBoundary, leftGammaCount, leftBoolValue,
          rightGammaBoundary, rightGammaCount, rightBoolValue,
          transformedStart, transformedFinish, transformedBoundary,
          transformedCount, transformStateBoundary, transformStateCount,
          emptyStart, emptyFinish, emptyBoundary,
          transformTableWidth, transformValueBound, resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hpushOneEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2,
          #18, #19, #20, #21, #6, #5, #37, #38,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 40), #39]) =
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          gammaBoundary, gammaCount, tableWidth, valueBound,
          1, resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hpushTwoEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 40), #1, #2,
          #18, #19, #20, #21, #6, #5, #37, #38,
          (↑(2 : Nat) : Semiterm ℒₒᵣ Empty 40), #39]) =
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          gammaBoundary, gammaCount, tableWidth, valueBound,
          2, resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htagValue : env 3 = taskTag := rfl
  have hsourceCountValue : env 19 = sourceCount := rfl
  simp [compactNumericExsCutCombineRuleRowsDef,
    CompactNumericExsCutCombineRuleRows,
    hformulaEnv, htransformedEnv, hemptyEnv,
    hrightRowsEnv, hleftRowsEnv, hrightHeadEnv, hleftHeadEnv,
    hexsEnv, hcutEnv, hpushOneEnv, hpushTwoEnv,
    htagValue, hsourceCountValue]
  intro _hformula _htransformed _hempty
  rfl

theorem compactNumericExsCutCombineRuleRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericExsCutCombineRuleRowsDef.val := by
  simp [compactNumericExsCutCombineRuleRowsDef]

private theorem CompactNumericChildResultBoundedHeadEq.exists_result
    {tokenTable width tokenCount targetBoundary
      expectedGammaBoundary expectedGammaCount valueBound
      targetIndex expectedBool : Nat}
    (hhead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount targetBoundary
        expectedGammaBoundary expectedGammaCount valueBound
        targetIndex expectedBool) :
    ∃ result : Bool, expectedBool = compactAdditiveBoolTag result := by
  rcases hhead with
    ⟨_targetStart, _htargetStart,
      _targetFinish, _htargetFinish,
      _targetGammaFinish, _htargetGammaFinish,
      _targetGammaCount, _htargetGammaCount,
      _targetGammaBoundary, _htargetGammaBoundary,
      targetBoolValue, _htargetBoolValue,
      _targetGammaBoundarySize, _htargetGammaBoundarySize,
      _hstartEntry, _hfinishEntry, hcore, _hgammaRows, hbool⟩
  rcases hcore.2.2.2.2.exists_bool with ⟨result, hresult⟩
  refine ⟨result, hbool.symm.trans ?_⟩
  simpa [compactNumericChildResultRowCoordinatesOf,
    compactAdditiveBoolTag] using hresult

theorem CompactNumericExsCutCombineRuleRows.sound
    {tokenTable width tokenCount taskTag gammaFinish gammaBoundary
      firstFinish secondFinish witnessFinish
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary targetBoundary
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary transformedCount
      transformedBoundarySize transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue : Nat}
    {Gamma : List (List Nat)} {formula witness : List Nat}
    {source target : List CompactNumericChildResult}
    (hrows : CompactNumericExsCutCombineRuleRows
      tokenTable width tokenCount
      taskTag gammaFinish Gamma.length gammaBoundary
      firstFinish formula.length secondFinish witnessFinish witness.length
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary source.length targetBoundary target.length
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hformula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount gammaFinish firstFinish formula)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount secondFinish witnessFinish witness)
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
    (taskTag = 6 ∧
      1 ≤ source.length ∧
      resultBoolValue = compactAdditiveBoolTag
        (compactExsRuleCheck
          (Gamma, (formula, (witness, source.getI 0)))) ∧
      target =
        (Gamma, compactExsRuleCheck
          (Gamma, (formula, (witness, source.getI 0)))) :: source.drop 1) ∨
    (taskTag = 9 ∧
      2 ≤ source.length ∧
      resultBoolValue = compactAdditiveBoolTag
        (compactCutRuleCheck
          (Gamma, (formula,
            (source.getI 1, source.getI 0)))) ∧
      target =
        (Gamma, compactCutRuleCheck
          (Gamma, (formula,
            (source.getI 1, source.getI 0)))) :: source.drop 2) := by
  rcases hrows with
    ⟨hformulaWitness, htransformedWitness, hemptyWitness, hbranch⟩
  rcases hformulaWitness.realize with
    ⟨decodedFormula, _hdecodedFormulaLength,
      hdecodedFormula, hdecodedFormulaRows⟩
  have hdecodedFormulaEq : decodedFormula = formula :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hformula hdecodedFormula).1
  subst decodedFormula
  rcases htransformedWitness.realize with
    ⟨transformed, htransformedLength,
      htransformed, htransformedRows⟩
  subst transformedCount
  rcases hemptyWitness.realize with
    ⟨decodedEmpty, hdecodedEmptyLength,
      hdecodedEmpty, hdecodedEmptyRows⟩
  have hdecodedEmptyEq : decodedEmpty = [] :=
    List.eq_nil_of_length_eq_zero hdecodedEmptyLength
  subst decodedEmpty
  rcases hbranch with hExs | hCut
  · rcases hExs with
      ⟨htag, hcount, hrightWellFormed, hrightHead, hcheck, hpush⟩
    rcases CompactAdditiveNatListListRowsWellFormed.realizeRows
        hrightWellFormed with
      ⟨rightConclusion, hrightLength, hright⟩
    subst rightGammaCount
    rcases CompactNumericChildResultBoundedHeadEq.exists_result
        hrightHead with ⟨rightValid, hrightBool⟩
    have hrightHead' : CompactNumericChildResultBoundedHeadEq
        tokenTable width tokenCount sourceBoundary
          rightGammaBoundary rightConclusion.length valueBound 0
          (compactAdditiveBoolTag rightValid) := by
      simpa only [hrightBool] using hrightHead
    have hrightValue := hrightHead'.value_eq
      (target := source) (by omega) hright hsourceRows
    have hresult :=
      (compactAdditiveExsRuleCheck_iff
        hcheck.1 hGamma hformula hdecodedFormulaRows hwitness
        hright htransformed htransformedRows hdecodedEmptyRows
        hrightBool).mp hcheck
    rw [hresult] at hpush
    have htarget :=
      ((compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
        (consumed := 1)
        (expectedResult := compactExsRuleCheck
          (Gamma, formula, witness, rightConclusion, rightValid))
        hsourceRows htargetRows hGamma hsourceGraph htargetGraph).mp
          hpush).2
    left
    refine ⟨htag, hcount, ?_, ?_⟩
    · simpa only [hrightValue] using hresult
    · simpa only [hrightValue] using htarget
  · rcases hCut with
      ⟨htag, hcount, hrightWellFormed, hleftWellFormed,
        hrightHead, hleftHead, hcheck, hpush⟩
    rcases CompactAdditiveNatListListRowsWellFormed.realizeRows
        hrightWellFormed with
      ⟨rightConclusion, hrightLength, hright⟩
    subst rightGammaCount
    rcases CompactAdditiveNatListListRowsWellFormed.realizeRows
        hleftWellFormed with
      ⟨leftConclusion, hleftLength, hleft⟩
    subst leftGammaCount
    rcases CompactNumericChildResultBoundedHeadEq.exists_result
        hrightHead with ⟨rightValid, hrightBool⟩
    rcases CompactNumericChildResultBoundedHeadEq.exists_result
        hleftHead with ⟨leftValid, hleftBool⟩
    have hrightHead' : CompactNumericChildResultBoundedHeadEq
        tokenTable width tokenCount sourceBoundary
          rightGammaBoundary rightConclusion.length valueBound 0
          (compactAdditiveBoolTag rightValid) := by
      simpa only [hrightBool] using hrightHead
    have hleftHead' : CompactNumericChildResultBoundedHeadEq
        tokenTable width tokenCount sourceBoundary
          leftGammaBoundary leftConclusion.length valueBound 1
          (compactAdditiveBoolTag leftValid) := by
      simpa only [hleftBool] using hleftHead
    have hrightValue := hrightHead'.value_eq
      (target := source) (by omega) hright hsourceRows
    have hleftValue := hleftHead'.value_eq
      (target := source) (by omega) hleft hsourceRows
    have hresult :=
      (compactAdditiveCutRuleCheck_iff
        hcheck.1 hGamma hformula hdecodedFormulaRows
        hleft hright htransformed htransformedRows
        hdecodedEmpty hdecodedEmptyRows hleftBool hrightBool).mp hcheck
    rw [hresult] at hpush
    have htarget :=
      ((compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
        (consumed := 2)
        (expectedResult := compactCutRuleCheck
          (Gamma, formula,
            (leftConclusion, leftValid), rightConclusion, rightValid))
        hsourceRows htargetRows hGamma hsourceGraph htargetGraph).mp
          hpush).2
    right
    refine ⟨htag, hcount, ?_, ?_⟩
    · simpa only [hrightValue, hleftValue] using hresult
    · simpa only [hrightValue, hleftValue] using htarget

theorem CompactNumericExsCutCombineRuleRows.sound_combineTransition
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    {task : CompactNumericVerifierTask}
    {source target : List CompactNumericChildResult}
    {rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary targetBoundary
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue : Nat}
    (hcore : CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (htask : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount coordinates.start coordinates.finish task)
    (hrows : CompactNumericExsCutCombineRuleRows
      tokenTable width tokenCount
      coordinates.tag coordinates.gammaFinish coordinates.gammaCount
        coordinates.gammaBoundary
      coordinates.firstFinish coordinates.firstCount
        coordinates.secondFinish coordinates.witnessFinish
        coordinates.witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary source.length targetBoundary target.length
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
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
      _hsecond, _hsecondLength,
      hwitness, hwitnessLength,
      _hsuffix, _hsuffixLength⟩
  have hrealizedTaskEq : realizedTask = task :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hcore htask hrealizedTask
  subst task
  have hrows' : CompactNumericExsCutCombineRuleRows
      tokenTable width tokenCount
      coordinates.tag coordinates.gammaFinish realizedTask.2.1.length
        coordinates.gammaBoundary
      coordinates.firstFinish realizedTask.2.2.1.length
        coordinates.secondFinish coordinates.witnessFinish
        realizedTask.2.2.2.2.1.length
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary source.length targetBoundary target.length
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      tableWidth valueBound resultBoolValue := by
    simpa only [hGammaLength, hfirstLength, hwitnessLength] using hrows
  have hsound := CompactNumericExsCutCombineRuleRows.sound
    hrows' hGamma hfirst hwitness hsourceRows htargetRows
      hsourceGraph htargetGraph
  rcases hsound with hExs | hCut
  · rcases hExs with ⟨htagSix, hcount, _hresult, htarget⟩
    have htaskTag : realizedTask.1 = 6 := htag.trans htagSix
    have hhead : source.head?.getD compactNumericDefaultChildResult =
        source.getI 0 := by
      cases source with
      | nil => simp at hcount
      | cons head tail => simp
    let result := compactExsRuleCheck
      (realizedTask.2.1,
        (realizedTask.2.2.1,
          (realizedTask.2.2.2.2.1, source.getI 0)))
    refine ⟨((realizedTask.2.1, result), source.tail), ?_, ?_⟩
    · simp [compactNumericCombineTransition, htaskTag, hcount,
        hhead, result]
    · simpa [result] using htarget
  · rcases hCut with ⟨htagNine, hcount, _hresult, htarget⟩
    have htaskTag : realizedTask.1 = 9 := htag.trans htagNine
    have hhead : source.head?.getD compactNumericDefaultChildResult =
        source.getI 0 := by
      cases source with
      | nil => simp at hcount
      | cons head tail => simp
    have hsecond : source[1]?.getD
        compactNumericDefaultChildResult = source.getI 1 := by
      cases source with
      | nil => simp at hcount
      | cons first rest =>
          cases rest with
          | nil => simp at hcount
          | cons second tail => simp
    let result := compactCutRuleCheck
      (realizedTask.2.1,
        (realizedTask.2.2.1, (source.getI 1, source.getI 0)))
    refine ⟨((realizedTask.2.1, result), source.drop 2), ?_, ?_⟩
    · simp [compactNumericCombineTransition, htaskTag, hcount,
        hhead, hsecond, result]
    · simpa [result] using htarget

#print axioms compactNumericExsCutCombineRuleRowsDef_spec
#print axioms compactNumericExsCutCombineRuleRowsDef_sigmaZero
#print axioms CompactNumericExsCutCombineRuleRows.sound
#print axioms CompactNumericExsCutCombineRuleRows.sound_combineTransition

end FoundationCompactNumericListedDirectExsCutCombineRuleRows
