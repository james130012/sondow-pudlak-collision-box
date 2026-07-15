import integration.FoundationCompactNumericListedDirectAllShiftRuleCheck
import integration.FoundationCompactNumericListedDirectChildResultListPushDropRows
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
import integration.FoundationCompactNumericListedDirectVerifierTaskFieldRealization

/-!
# Direct combine rows for universal introduction and shift

Both branches read their premise from the actual child-result stack, run the
checked public rule graph, and push the computed result after consuming one
child.  Universal introduction additionally carries self-contained rows for
the principal formula and its exact free-transform output.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAllShiftCombineRuleRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectNatListListRowsRealization
open FoundationCompactNumericListedDirectAllShiftRuleCheck
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectChildResultBoundedHeadEquality
open FoundationCompactNumericListedDirectChildResultListPushDropRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization

def CompactNumericAllShiftCombineRuleRows
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue : Nat) : Prop :=
  (taskTag = 5 ∧
    1 ≤ sourceCount ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount gammaFinish firstCount firstFinish
        formulaBoundary formulaBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount freedStart freedCount freedFinish
        freedBoundary freedBoundarySize ∧
    CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount premiseGammaBoundary premiseGammaCount ∧
    CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount sourceBoundary
        premiseGammaBoundary premiseGammaCount valueBound 0 premiseBoolValue ∧
    CompactAdditiveAllRuleCheck
      tokenTable width tokenCount
      gammaBoundary gammaCount
      gammaFinish firstFinish formulaBoundary firstCount
      premiseGammaBoundary premiseGammaCount premiseBoolValue
      freedStart freedFinish freedBoundary freedCount
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound resultBoolValue ∧
    CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      gammaBoundary gammaCount tableWidth valueBound 1 resultBoolValue) ∨
  (taskTag = 8 ∧
    1 ≤ sourceCount ∧
    CompactAdditiveNatListListRowsWellFormed
      tokenTable width tokenCount premiseGammaBoundary premiseGammaCount ∧
    CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount sourceBoundary
        premiseGammaBoundary premiseGammaCount valueBound 0 premiseBoolValue ∧
    CompactAdditiveShiftRuleCheck
      tokenTable width tokenCount
      gammaBoundary gammaCount
      premiseGammaBoundary premiseGammaCount premiseBoolValue
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound resultBoolValue ∧
    CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      gammaBoundary gammaCount tableWidth valueBound 1 resultBoolValue)

def compactNumericAllShiftCombineRuleRowsDef :
    𝚺₀.Semisentence 39 := .mkSigma
  “tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue.
    (taskTag = 5 ∧
      1 ≤ sourceCount ∧
      !(compactAdditiveNatListWitnessRowsDef)
        tokenTable width tokenCount gammaFinish firstCount firstFinish
          formulaBoundary formulaBoundarySize ∧
      !(compactAdditiveNatListWitnessRowsDef)
        tokenTable width tokenCount freedStart freedCount freedFinish
          freedBoundary freedBoundarySize ∧
      !(compactAdditiveNatListListRowsWellFormedDef)
        tokenTable width tokenCount premiseGammaBoundary premiseGammaCount ∧
      !(compactNumericChildResultBoundedHeadEqDef)
        tokenTable width tokenCount sourceBoundary
          premiseGammaBoundary premiseGammaCount valueBound 0 premiseBoolValue ∧
      !(compactAdditiveAllRuleCheckDef)
        tokenTable width tokenCount
        gammaBoundary gammaCount
        gammaFinish firstFinish formulaBoundary firstCount
        premiseGammaBoundary premiseGammaCount premiseBoolValue
        freedStart freedFinish freedBoundary freedCount
        freeStateBoundary freeStateCount
        shiftCandidateBoundary shiftSuccessTable
        shiftedBoundary shiftedCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        shiftWitnessBound freeTableWidth freeValueBound resultBoolValue ∧
      !(compactNumericChildResultListPushDropRowsDef)
        tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        gammaBoundary gammaCount tableWidth valueBound 1 resultBoolValue) ∨
    (taskTag = 8 ∧
      1 ≤ sourceCount ∧
      !(compactAdditiveNatListListRowsWellFormedDef)
        tokenTable width tokenCount premiseGammaBoundary premiseGammaCount ∧
      !(compactNumericChildResultBoundedHeadEqDef)
        tokenTable width tokenCount sourceBoundary
          premiseGammaBoundary premiseGammaCount valueBound 0 premiseBoolValue ∧
      !(compactAdditiveShiftRuleCheckDef)
        tokenTable width tokenCount
        gammaBoundary gammaCount
        premiseGammaBoundary premiseGammaCount premiseBoolValue
        shiftCandidateBoundary shiftSuccessTable
        shiftedBoundary shiftedCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        shiftWitnessBound resultBoolValue ∧
      !(compactNumericChildResultListPushDropRowsDef)
        tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        gammaBoundary gammaCount tableWidth valueBound 1 resultBoolValue)”

def compactNumericAllShiftCombineRuleRowsEnvironment
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue : Nat) : Fin 39 → Nat :=
  ![tokenTable, width, tokenCount,
    taskTag, gammaFinish, gammaCount, gammaBoundary,
    firstFinish, firstCount,
    premiseGammaCount, premiseGammaBoundary, premiseBoolValue,
    sourceBoundary, sourceCount, targetBoundary, targetCount,
    formulaBoundary, formulaBoundarySize,
    freedStart, freedFinish, freedBoundary, freedCount, freedBoundarySize,
    freeStateBoundary, freeStateCount,
    shiftCandidateBoundary, shiftSuccessTable,
    shiftedBoundary, shiftedCount,
    emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
    shiftWitnessBound, freeTableWidth, freeValueBound,
    tableWidth, valueBound, resultBoolValue]

set_option maxRecDepth 4096 in
@[simp] theorem compactNumericAllShiftCombineRuleRowsDef_spec
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue : Nat) :
    compactNumericAllShiftCombineRuleRowsDef.val.Evalb
        (compactNumericAllShiftCombineRuleRowsEnvironment
          tokenTable width tokenCount
          taskTag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount
          premiseGammaCount premiseGammaBoundary premiseBoolValue
          sourceBoundary sourceCount targetBoundary targetCount
          formulaBoundary formulaBoundarySize
          freedStart freedFinish freedBoundary freedCount freedBoundarySize
          freeStateBoundary freeStateCount
          shiftCandidateBoundary shiftSuccessTable
          shiftedBoundary shiftedCount
          emptyStart emptyFinish emptyBoundary emptyBoundarySize
          shiftWitnessBound freeTableWidth freeValueBound
          tableWidth valueBound resultBoolValue) ↔
      CompactNumericAllShiftCombineRuleRows
        tokenTable width tokenCount
        taskTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount
        premiseGammaCount premiseGammaBoundary premiseBoolValue
        sourceBoundary sourceCount targetBoundary targetCount
        formulaBoundary formulaBoundarySize
        freedStart freedFinish freedBoundary freedCount freedBoundarySize
        freeStateBoundary freeStateCount
        shiftCandidateBoundary shiftSuccessTable
        shiftedBoundary shiftedCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        shiftWitnessBound freeTableWidth freeValueBound
        tableWidth valueBound resultBoolValue := by
  let env := compactNumericAllShiftCombineRuleRowsEnvironment
    tokenTable width tokenCount
    taskTag gammaFinish gammaCount gammaBoundary
    firstFinish firstCount
    premiseGammaCount premiseGammaBoundary premiseBoolValue
    sourceBoundary sourceCount targetBoundary targetCount
    formulaBoundary formulaBoundarySize
    freedStart freedFinish freedBoundary freedCount freedBoundarySize
    freeStateBoundary freeStateCount
    shiftCandidateBoundary shiftSuccessTable
    shiftedBoundary shiftedCount
    emptyStart emptyFinish emptyBoundary emptyBoundarySize
    shiftWitnessBound freeTableWidth freeValueBound
    tableWidth valueBound resultBoolValue
  change compactNumericAllShiftCombineRuleRowsDef.val.Evalb env ↔ _
  have hformulaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2, #4, #8, #7,
          #16, #17]) =
        ![tokenTable, width, tokenCount, gammaFinish, firstCount,
          firstFinish, formulaBoundary, formulaBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hfreedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2, #18, #21, #19,
          #20, #22]) =
        ![tokenTable, width, tokenCount, freedStart, freedCount,
          freedFinish, freedBoundary, freedBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hpremiseRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2, #10, #9]) =
        ![tokenTable, width, tokenCount,
          premiseGammaBoundary, premiseGammaCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hpremiseHeadEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2, #12,
          #10, #9, #37, (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 39), #11]) =
        ![tokenTable, width, tokenCount, sourceBoundary,
          premiseGammaBoundary, premiseGammaCount, valueBound,
          0, premiseBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hallEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2,
          #6, #5, #4, #7, #16, #8,
          #10, #9, #11, #18, #19, #20, #21,
          #23, #24, #25, #26, #27, #28,
          #29, #30, #31, #32, #33, #34, #35, #38]) =
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          gammaFinish, firstFinish, formulaBoundary, firstCount,
          premiseGammaBoundary, premiseGammaCount, premiseBoolValue,
          freedStart, freedFinish, freedBoundary, freedCount,
          freeStateBoundary, freeStateCount,
          shiftCandidateBoundary, shiftSuccessTable,
          shiftedBoundary, shiftedCount,
          emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
          shiftWitnessBound, freeTableWidth, freeValueBound,
          resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hshiftEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2,
          #6, #5, #10, #9, #11, #25, #26, #27, #28,
          #29, #30, #31, #32, #33, #38]) =
        ![tokenTable, width, tokenCount,
          gammaBoundary, gammaCount,
          premiseGammaBoundary, premiseGammaCount, premiseBoolValue,
          shiftCandidateBoundary, shiftSuccessTable,
          shiftedBoundary, shiftedCount,
          emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
          shiftWitnessBound, resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hpushEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 39), #1, #2,
          #12, #13, #14, #15, #6, #5, #36, #37,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 39), #38]) =
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          gammaBoundary, gammaCount, tableWidth, valueBound,
          1, resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htagValue : env 3 = taskTag := rfl
  have hsourceCountValue : env 13 = sourceCount := rfl
  simp [compactNumericAllShiftCombineRuleRowsDef,
    CompactNumericAllShiftCombineRuleRows,
    hformulaEnv, hfreedEnv, hpremiseRowsEnv, hpremiseHeadEnv,
    hallEnv, hshiftEnv, hpushEnv, htagValue, hsourceCountValue]

theorem compactNumericAllShiftCombineRuleRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericAllShiftCombineRuleRowsDef.val := by
  simp [compactNumericAllShiftCombineRuleRowsDef]

theorem CompactNumericAllShiftCombineRuleRows.sound
    {tokenTable width tokenCount taskTag gammaFinish gammaBoundary
      firstFinish
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary targetBoundary
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue : Nat}
    {Gamma : List (List Nat)} {formula : List Nat}
    {source target : List CompactNumericChildResult}
    (hrows : CompactNumericAllShiftCombineRuleRows
      tokenTable width tokenCount
      taskTag gammaFinish Gamma.length gammaBoundary
      firstFinish formula.length
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary source.length targetBoundary target.length
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hformula : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount gammaFinish firstFinish formula)
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
    (taskTag = 5 ∧
      1 ≤ source.length ∧
      resultBoolValue = compactAdditiveBoolTag
        (compactAllRuleCheck (Gamma, (formula, source.getI 0))) ∧
      target =
        (Gamma, compactAllRuleCheck
          (Gamma, (formula, source.getI 0))) :: source.drop 1) ∨
    (taskTag = 8 ∧
      1 ≤ source.length ∧
      resultBoolValue = compactAdditiveBoolTag
        (compactShiftRuleCheck (Gamma, source.getI 0)) ∧
      target =
        (Gamma, compactShiftRuleCheck
          (Gamma, source.getI 0)) :: source.drop 1) := by
  rcases hrows with hAll | hShift
  · rcases hAll with
      ⟨htag, hcount, hformulaWitness, hfreedWitness,
        hpremiseWellFormed, hpremiseHead, hcheck, hpush⟩
    rcases hformulaWitness.realize with
      ⟨decodedFormula, _hdecodedFormulaLength,
        hdecodedFormula, hdecodedFormulaRows⟩
    have hdecodedFormulaEq : decodedFormula = formula :=
      (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
        hformula hdecodedFormula).1
    subst decodedFormula
    rcases hfreedWitness.realize with
      ⟨freed, hfreedLength, hfreed, hfreedRows⟩
    subst freedCount
    rcases CompactAdditiveNatListListRowsWellFormed.realizeRows
        hpremiseWellFormed with
      ⟨premiseConclusion, hpremiseLength, hpremiseRows⟩
    subst premiseGammaCount
    rcases hpremiseHead.exists_boolTag with
      ⟨premiseValid, hpremiseBool⟩
    have hpremiseHead' : CompactNumericChildResultBoundedHeadEq
        tokenTable width tokenCount sourceBoundary
          premiseGammaBoundary premiseConclusion.length valueBound 0
          (compactAdditiveBoolTag premiseValid) := by
      simpa only [hpremiseBool] using hpremiseHead
    have hpremiseValue := hpremiseHead'.value_eq
      (target := source) (by omega) hpremiseRows hsourceRows
    have hresult := compactAdditiveAllRuleCheck_iff
      hcheck hGamma hformula hdecodedFormulaRows hpremiseRows
        hfreed hfreedRows hpremiseBool
    rw [hresult] at hpush
    have htarget :=
      ((compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
        (consumed := 1)
        (expectedResult := compactAllRuleCheck
          (Gamma, formula, premiseConclusion, premiseValid))
        hsourceRows htargetRows hGamma hsourceGraph htargetGraph).mp
          hpush).2
    left
    refine ⟨htag, hcount, ?_, ?_⟩
    · simpa only [hpremiseValue] using hresult
    · simpa only [hpremiseValue] using htarget
  · rcases hShift with
      ⟨htag, hcount, hpremiseWellFormed,
        hpremiseHead, hcheck, hpush⟩
    rcases CompactAdditiveNatListListRowsWellFormed.realizeRows
        hpremiseWellFormed with
      ⟨premiseConclusion, hpremiseLength, hpremiseRows⟩
    subst premiseGammaCount
    rcases hpremiseHead.exists_boolTag with
      ⟨premiseValid, hpremiseBool⟩
    have hpremiseHead' : CompactNumericChildResultBoundedHeadEq
        tokenTable width tokenCount sourceBoundary
          premiseGammaBoundary premiseConclusion.length valueBound 0
          (compactAdditiveBoolTag premiseValid) := by
      simpa only [hpremiseBool] using hpremiseHead
    have hpremiseValue := hpremiseHead'.value_eq
      (target := source) (by omega) hpremiseRows hsourceRows
    have hresult := compactAdditiveShiftRuleCheck_iff
      hcheck hGamma hpremiseRows hpremiseBool
    rw [hresult] at hpush
    have htarget :=
      ((compactNumericChildResultListPushDropRows_iff_push_drop_of_rows
        (consumed := 1)
        (expectedResult := compactShiftRuleCheck
          (Gamma, premiseConclusion, premiseValid))
        hsourceRows htargetRows hGamma hsourceGraph htargetGraph).mp
          hpush).2
    right
    refine ⟨htag, hcount, ?_, ?_⟩
    · simpa only [hpremiseValue] using hresult
    · simpa only [hpremiseValue] using htarget

theorem CompactNumericAllShiftCombineRuleRows.sound_combineTransition
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericVerifierTaskRowCoordinates}
    {sizeWitness : CompactNumericVerifierTaskSizeWitness}
    {task : CompactNumericVerifierTask}
    {source target : List CompactNumericChildResult}
    {premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary targetBoundary
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue : Nat}
    (hcore : CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (htask : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount coordinates.start coordinates.finish task)
    (hrows : CompactNumericAllShiftCombineRuleRows
      tokenTable width tokenCount
      coordinates.tag coordinates.gammaFinish coordinates.gammaCount
        coordinates.gammaBoundary
      coordinates.firstFinish coordinates.firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary source.length targetBoundary target.length
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
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
      _hwitness, _hwitnessLength,
      _hsuffix, _hsuffixLength⟩
  have hrealizedTaskEq : realizedTask = task :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hcore htask hrealizedTask
  subst task
  have hrows' : CompactNumericAllShiftCombineRuleRows
      tokenTable width tokenCount
      coordinates.tag coordinates.gammaFinish realizedTask.2.1.length
        coordinates.gammaBoundary
      coordinates.firstFinish realizedTask.2.2.1.length
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      sourceBoundary source.length targetBoundary target.length
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue := by
    simpa only [hGammaLength, hfirstLength] using hrows
  have hsound := CompactNumericAllShiftCombineRuleRows.sound
    hrows' hGamma hfirst hsourceRows htargetRows hsourceGraph htargetGraph
  rcases hsound with hAll | hShift
  · rcases hAll with ⟨htagFive, hcount, _hresult, htarget⟩
    have htaskTag : realizedTask.1 = 5 := htag.trans htagFive
    have hhead : source.head?.getD compactNumericDefaultChildResult =
        source.getI 0 := by
      cases source with
      | nil => simp at hcount
      | cons head tail => simp
    let result := compactAllRuleCheck
      (realizedTask.2.1, (realizedTask.2.2.1, source.getI 0))
    refine ⟨((realizedTask.2.1, result), source.tail), ?_, ?_⟩
    · simp [compactNumericCombineTransition, htaskTag, hcount,
        hhead, result]
    · simpa [result] using htarget
  · rcases hShift with ⟨htagEight, hcount, _hresult, htarget⟩
    have htaskTag : realizedTask.1 = 8 := htag.trans htagEight
    have hhead : source.head?.getD compactNumericDefaultChildResult =
        source.getI 0 := by
      cases source with
      | nil => simp at hcount
      | cons head tail => simp
    let result := compactShiftRuleCheck
      (realizedTask.2.1, source.getI 0)
    refine ⟨((realizedTask.2.1, result), source.tail), ?_, ?_⟩
    · simp [compactNumericCombineTransition, htaskTag, hcount,
        hhead, result]
    · simpa [result] using htarget

#print axioms compactNumericAllShiftCombineRuleRowsDef_spec
#print axioms compactNumericAllShiftCombineRuleRowsDef_sigmaZero
#print axioms CompactNumericAllShiftCombineRuleRows.sound
#print axioms CompactNumericAllShiftCombineRuleRows.sound_combineTransition

end FoundationCompactNumericListedDirectAllShiftCombineRuleRows
