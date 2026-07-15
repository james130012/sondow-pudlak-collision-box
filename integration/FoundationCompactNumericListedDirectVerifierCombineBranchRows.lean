import integration.FoundationCompactNumericListedDirectVerifierCombineStateRows

/-!
# One bounded row schema for every verifier combine branch

The trace table needs one fixed column schema.  Irrelevant witness columns are
ignored by each disjunct, while the selected branch uses the same task and
state coordinates as the common combine frame.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineBranchRows

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRows
open FoundationCompactNumericListedDirectVerifierCombineSuccessRows
open FoundationCompactNumericListedDirectVerifierCombineFailureRows
open FoundationCompactNumericListedDirectVerifierCombineStateRows

structure CompactNumericVerifierCombineRuleWitness where
  rightGammaCount : Nat
  rightGammaBoundary : Nat
  rightBoolValue : Nat
  leftGammaCount : Nat
  leftGammaBoundary : Nat
  leftBoolValue : Nat
  formulaBoundary : Nat
  formulaBoundarySize : Nat
  transformedStart : Nat
  transformedFinish : Nat
  transformedBoundary : Nat
  transformedCount : Nat
  transformedBoundarySize : Nat
  transformStateBoundary : Nat
  transformStateCount : Nat
  freedStart : Nat
  freedFinish : Nat
  freedBoundary : Nat
  freedCount : Nat
  freedBoundarySize : Nat
  freeStateBoundary : Nat
  freeStateCount : Nat
  shiftCandidateBoundary : Nat
  shiftSuccessTable : Nat
  shiftedBoundary : Nat
  shiftedCount : Nat
  emptyStart : Nat
  emptyFinish : Nat
  emptyBoundary : Nat
  emptyBoundarySize : Nat
  shiftWitnessBound : Nat
  freeTableWidth : Nat
  freeValueBound : Nat
  resultBoolValue : Nat

def compactNumericVerifierCombineRuleWitnessOf
    (rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      resultBoolValue : Nat) :
    CompactNumericVerifierCombineRuleWitness where
  rightGammaCount := rightGammaCount
  rightGammaBoundary := rightGammaBoundary
  rightBoolValue := rightBoolValue
  leftGammaCount := leftGammaCount
  leftGammaBoundary := leftGammaBoundary
  leftBoolValue := leftBoolValue
  formulaBoundary := formulaBoundary
  formulaBoundarySize := formulaBoundarySize
  transformedStart := transformedStart
  transformedFinish := transformedFinish
  transformedBoundary := transformedBoundary
  transformedCount := transformedCount
  transformedBoundarySize := transformedBoundarySize
  transformStateBoundary := transformStateBoundary
  transformStateCount := transformStateCount
  freedStart := freedStart
  freedFinish := freedFinish
  freedBoundary := freedBoundary
  freedCount := freedCount
  freedBoundarySize := freedBoundarySize
  freeStateBoundary := freeStateBoundary
  freeStateCount := freeStateCount
  shiftCandidateBoundary := shiftCandidateBoundary
  shiftSuccessTable := shiftSuccessTable
  shiftedBoundary := shiftedBoundary
  shiftedCount := shiftedCount
  emptyStart := emptyStart
  emptyFinish := emptyFinish
  emptyBoundary := emptyBoundary
  emptyBoundarySize := emptyBoundarySize
  shiftWitnessBound := shiftWitnessBound
  freeTableWidth := freeTableWidth
  freeValueBound := freeValueBound
  resultBoolValue := resultBoolValue

def CompactNumericVerifierCombineBranchRows
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound nextStatusTag nextStatusBool : Nat)
    (witness : CompactNumericVerifierCombineRuleWitness) : Prop :=
  CompactNumericSimpleCombineSuccessRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witness.rightGammaCount witness.rightGammaBoundary
        witness.rightBoolValue
      witness.leftGammaCount witness.leftGammaBoundary
        witness.leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound witness.resultBoolValue nextStatusTag ∨
    CompactNumericAllShiftCombineSuccessRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount
      witness.rightGammaCount witness.rightGammaBoundary
        witness.rightBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      witness.formulaBoundary witness.formulaBoundarySize
      witness.freedStart witness.freedFinish witness.freedBoundary
        witness.freedCount witness.freedBoundarySize
      witness.freeStateBoundary witness.freeStateCount
      witness.shiftCandidateBoundary witness.shiftSuccessTable
      witness.shiftedBoundary witness.shiftedCount
      witness.emptyStart witness.emptyFinish witness.emptyBoundary
        witness.emptyBoundarySize
      witness.shiftWitnessBound witness.freeTableWidth witness.freeValueBound
      tableWidth valueBound witness.resultBoolValue nextStatusTag ∨
    CompactNumericExsCutCombineSuccessRows
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish witnessFinish witnessCount
      witness.rightGammaCount witness.rightGammaBoundary
        witness.rightBoolValue
      witness.leftGammaCount witness.leftGammaBoundary
        witness.leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      witness.formulaBoundary witness.formulaBoundarySize
      witness.transformedStart witness.transformedFinish
        witness.transformedBoundary witness.transformedCount
        witness.transformedBoundarySize
      witness.transformStateBoundary witness.transformStateCount
      witness.emptyStart witness.emptyFinish witness.emptyBoundary
        witness.emptyBoundarySize
      witness.freeTableWidth witness.freeValueBound
      tableWidth valueBound witness.resultBoolValue nextStatusTag ∨
    CompactNumericVerifierCombineFailureRows
      tokenTable width tokenCount taskTag
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound nextStatusTag nextStatusBool

def compactNumericVerifierCombineBranchRowsDef :
    𝚺₀.Semisentence 55 := .mkSigma
  “tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound nextStatusTag nextStatusBool
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound resultBoolValue.
    !(compactNumericSimpleCombineSuccessRowsDef)
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound resultBoolValue nextStatusTag ∨
    !(compactNumericAllShiftCombineSuccessRowsDef)
      tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount
      rightGammaCount rightGammaBoundary rightBoolValue
      sourceBoundary sourceCount targetBoundary targetCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue nextStatusTag ∨
    !(compactNumericExsCutCombineSuccessRowsDef)
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
      freeTableWidth freeValueBound
      tableWidth valueBound resultBoolValue nextStatusTag ∨
    !(compactNumericVerifierCombineFailureRowsDef)
      tokenTable width tokenCount taskTag
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound nextStatusTag nextStatusBool”

def compactNumericVerifierCombineBranchRowsEnvironment
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound nextStatusTag nextStatusBool
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      resultBoolValue : Nat) : Fin 55 → Nat :=
  ![tokenTable, width, tokenCount,
    taskTag, gammaFinish, gammaCount, gammaBoundary,
    firstFinish, firstCount, secondFinish, secondCount,
    witnessFinish, witnessCount,
    sourceBoundary, sourceCount, targetBoundary, targetCount,
    tableWidth, valueBound, nextStatusTag, nextStatusBool,
    rightGammaCount, rightGammaBoundary, rightBoolValue,
    leftGammaCount, leftGammaBoundary, leftBoolValue,
    formulaBoundary, formulaBoundarySize,
    transformedStart, transformedFinish, transformedBoundary,
    transformedCount, transformedBoundarySize,
    transformStateBoundary, transformStateCount,
    freedStart, freedFinish, freedBoundary, freedCount, freedBoundarySize,
    freeStateBoundary, freeStateCount,
    shiftCandidateBoundary, shiftSuccessTable,
    shiftedBoundary, shiftedCount,
    emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
    shiftWitnessBound, freeTableWidth, freeValueBound, resultBoolValue]

set_option maxRecDepth 16384 in
@[simp] theorem compactNumericVerifierCombineBranchRowsDef_spec
    (tokenTable width tokenCount
      taskTag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount
      sourceBoundary sourceCount targetBoundary targetCount
      tableWidth valueBound nextStatusTag nextStatusBool
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      resultBoolValue : Nat) :
    compactNumericVerifierCombineBranchRowsDef.val.Evalb
        (compactNumericVerifierCombineBranchRowsEnvironment
          tokenTable width tokenCount
          taskTag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount
          witnessFinish witnessCount
          sourceBoundary sourceCount targetBoundary targetCount
          tableWidth valueBound nextStatusTag nextStatusBool
          rightGammaCount rightGammaBoundary rightBoolValue
          leftGammaCount leftGammaBoundary leftBoolValue
          formulaBoundary formulaBoundarySize
          transformedStart transformedFinish transformedBoundary
          transformedCount transformedBoundarySize
          transformStateBoundary transformStateCount
          freedStart freedFinish freedBoundary freedCount freedBoundarySize
          freeStateBoundary freeStateCount
          shiftCandidateBoundary shiftSuccessTable
          shiftedBoundary shiftedCount
          emptyStart emptyFinish emptyBoundary emptyBoundarySize
          shiftWitnessBound freeTableWidth freeValueBound
          resultBoolValue) ↔
      CompactNumericVerifierCombineBranchRows
        tokenTable width tokenCount
        taskTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        witnessFinish witnessCount
        sourceBoundary sourceCount targetBoundary targetCount
        tableWidth valueBound nextStatusTag nextStatusBool
        (compactNumericVerifierCombineRuleWitnessOf
          rightGammaCount rightGammaBoundary rightBoolValue
          leftGammaCount leftGammaBoundary leftBoolValue
          formulaBoundary formulaBoundarySize
          transformedStart transformedFinish transformedBoundary
          transformedCount transformedBoundarySize
          transformStateBoundary transformStateCount
          freedStart freedFinish freedBoundary freedCount freedBoundarySize
          freeStateBoundary freeStateCount
          shiftCandidateBoundary shiftSuccessTable
          shiftedBoundary shiftedCount
          emptyStart emptyFinish emptyBoundary emptyBoundarySize
          shiftWitnessBound freeTableWidth freeValueBound
          resultBoolValue) := by
  let env := compactNumericVerifierCombineBranchRowsEnvironment
    tokenTable width tokenCount
    taskTag gammaFinish gammaCount gammaBoundary
    firstFinish firstCount secondFinish secondCount
    witnessFinish witnessCount
    sourceBoundary sourceCount targetBoundary targetCount
    tableWidth valueBound nextStatusTag nextStatusBool
    rightGammaCount rightGammaBoundary rightBoolValue
    leftGammaCount leftGammaBoundary leftBoolValue
    formulaBoundary formulaBoundarySize
    transformedStart transformedFinish transformedBoundary
    transformedCount transformedBoundarySize
    transformStateBoundary transformStateCount
    freedStart freedFinish freedBoundary freedCount freedBoundarySize
    freeStateBoundary freeStateCount
    shiftCandidateBoundary shiftSuccessTable
    shiftedBoundary shiftedCount
    emptyStart emptyFinish emptyBoundary emptyBoundarySize
    shiftWitnessBound freeTableWidth freeValueBound resultBoolValue
  change compactNumericVerifierCombineBranchRowsDef.val.Evalb env ↔ _
  have hsimpleEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 55), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #21, #22, #23, #24, #25, #26,
          #13, #14, #15, #16, #17, #18, #54, #19]) =
        ![tokenTable, width, tokenCount,
          taskTag, gammaFinish, gammaCount, gammaBoundary,
          firstFinish, firstCount, secondFinish, secondCount,
          rightGammaCount, rightGammaBoundary, rightBoolValue,
          leftGammaCount, leftGammaBoundary, leftBoolValue,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          tableWidth, valueBound, resultBoolValue, nextStatusTag] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hallShiftEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 55), #1, #2, #3, #4, #5, #6,
          #7, #8, #21, #22, #23, #13, #14, #15, #16, #27, #28,
          #36, #37, #38, #39, #40, #41, #42, #43, #44, #45,
          #46, #47, #48, #49, #50, #51, #52, #53, #17, #18,
          #54, #19]) =
        ![tokenTable, width, tokenCount,
          taskTag, gammaFinish, gammaCount, gammaBoundary,
          firstFinish, firstCount,
          rightGammaCount, rightGammaBoundary, rightBoolValue,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          formulaBoundary, formulaBoundarySize,
          freedStart, freedFinish, freedBoundary, freedCount,
          freedBoundarySize, freeStateBoundary, freeStateCount,
          shiftCandidateBoundary, shiftSuccessTable,
          shiftedBoundary, shiftedCount,
          emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
          shiftWitnessBound, freeTableWidth, freeValueBound,
          tableWidth, valueBound, resultBoolValue, nextStatusTag] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hexsCutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 55), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #11, #12, #21, #22, #23, #24, #25, #26,
          #13, #14, #15, #16, #27, #28, #29, #30, #31, #32,
          #33, #34, #35, #47, #48, #49, #50, #52, #53,
          #17, #18, #54,
          #19]) =
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
          freeTableWidth, freeValueBound,
          tableWidth, valueBound, resultBoolValue, nextStatusTag] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hfailureEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 55), #1, #2, #3,
          #13, #14, #15, #16, #17, #18, #19, #20]) =
        ![tokenTable, width, tokenCount, taskTag,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          tableWidth, valueBound, nextStatusTag, nextStatusBool] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierCombineBranchRowsDef,
    CompactNumericVerifierCombineBranchRows,
    compactNumericVerifierCombineRuleWitnessOf,
    hsimpleEnv, hallShiftEnv, hexsCutEnv, hfailureEnv]

set_option maxRecDepth 16384 in
theorem compactNumericVerifierCombineBranchRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierCombineBranchRowsDef.val := by
  simp [compactNumericVerifierCombineBranchRowsDef]

theorem CompactNumericVerifierCombineBranchRows.realizeExactStep
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {witness : CompactNumericVerifierCombineRuleWitness}
    (hcurrent : CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount currentCoordinates currentSizeWitness)
    (hnext : CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount nextCoordinates nextSizeWitness)
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount currentCoordinates.taskBoundary
      currentSizeWitness.taskValueBound
      taskCoordinates taskSizeWitness)
    (hframe : CompactNumericVerifierCombineStateFrameRows
      tokenTable width tokenCount
      currentCoordinates.start currentCoordinates.certificateFinish
      currentCoordinates.taskBoundary currentCoordinates.taskCount
      currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
      currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
      currentCoordinates.statusTag taskCoordinates.tag
      nextCoordinates.start nextCoordinates.certificateFinish
      nextCoordinates.taskBoundary nextCoordinates.taskCount
      nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound)
    (hbranch : CompactNumericVerifierCombineBranchRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      taskCoordinates.witnessFinish taskCoordinates.witnessCount
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      nextCoordinates.statusTag nextCoordinates.statusBool witness) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  rcases hbranch with hsimple | hallShift | hexsCut | hfailure
  · exact CompactNumericSimpleCombineTransitionRows.realizeExactStep
      hcurrent hnext hhead hframe hsimple
  · exact CompactNumericAllShiftCombineRuleRows.realizeExactStep
      hcurrent hnext hhead hframe hallShift
  · exact CompactNumericExsCutCombineRuleRows.realizeExactStep
      hcurrent hnext hhead hframe hexsCut
  · exact CompactNumericVerifierCombineFailureRows.realizeExactStep
      hcurrent hnext hhead hframe hfailure

#print axioms compactNumericVerifierCombineBranchRowsDef_spec
#print axioms compactNumericVerifierCombineBranchRowsDef_sigmaZero
#print axioms CompactNumericVerifierCombineBranchRows.realizeExactStep

end FoundationCompactNumericListedDirectVerifierCombineBranchRows
