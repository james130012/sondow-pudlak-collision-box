import integration.FoundationCompactNumericListedDirectVerifierCombineBranchRows

/-!
# Complete bounded row graph for a verifier combine state

This is the fixed outer schema used by a trace row.  It joins both typed state
graphs, the real bounded task head, the stream/task-stack frame, and the exact
successful-or-failed combine branch.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineStateGraph

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRows
open FoundationCompactNumericListedDirectVerifierCombineBranchRows

def CompactNumericVerifierCombineStateGraph
    (tokenTable width tokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates)
    (taskSizeWitness : CompactNumericVerifierTaskSizeWitness)
    (ruleWitness : CompactNumericVerifierCombineRuleWitness) : Prop :=
  CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount currentCoordinates currentSizeWitness ∧
    CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount nextCoordinates nextSizeWitness ∧
    CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount currentCoordinates.taskBoundary
      currentSizeWitness.taskValueBound taskCoordinates taskSizeWitness ∧
    CompactNumericVerifierCombineStateFrameRows
      tokenTable width tokenCount
      currentCoordinates.start currentCoordinates.certificateFinish
      currentCoordinates.taskBoundary currentCoordinates.taskCount
      currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
      currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
      currentCoordinates.statusTag taskCoordinates.tag
      nextCoordinates.start nextCoordinates.certificateFinish
      nextCoordinates.taskBoundary nextCoordinates.taskCount
      nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound ∧
    CompactNumericVerifierCombineBranchRows
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
      nextCoordinates.statusTag nextCoordinates.statusBool ruleWitness

def compactNumericVerifierCombineStateGraphDef :
    𝚺₀.Semisentence 93 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentFinish
      currentProofFinish currentProofCount
      currentCertificateFinish currentCertificateCount
      currentTasksFinish currentTaskCount currentTaskBoundary
      currentValuesFinish currentValueCount currentValueBoundary
      currentStatusTag currentStatusPayloadStart currentStatusBool
      currentTaskBoundarySize currentValueBoundarySize
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextFinish
      nextProofFinish nextProofCount
      nextCertificateFinish nextCertificateCount
      nextTasksFinish nextTaskCount nextTaskBoundary
      nextValuesFinish nextValueCount nextValueBoundary
      nextStatusTag nextStatusPayloadStart nextStatusBool
      nextTaskBoundarySize nextValueBoundarySize
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      taskStart taskFinish taskTag
      taskGammaFinish taskGammaCount taskGammaBoundary
      taskFirstFinish taskFirstCount
      taskSecondFinish taskSecondCount
      taskWitnessFinish taskWitnessCount taskSuffixCount
      taskGammaBoundarySize
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
    !(compactNumericVerifierStateCoreGraphDef)
      tokenTable width tokenCount
      currentStart currentFinish
      currentProofFinish currentProofCount
      currentCertificateFinish currentCertificateCount
      currentTasksFinish currentTaskCount currentTaskBoundary
      currentValuesFinish currentValueCount currentValueBoundary
      currentStatusTag currentStatusPayloadStart currentStatusBool
      currentTaskBoundarySize currentValueBoundarySize
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound ∧
    !(compactNumericVerifierStateCoreGraphDef)
      tokenTable width tokenCount
      nextStart nextFinish
      nextProofFinish nextProofCount
      nextCertificateFinish nextCertificateCount
      nextTasksFinish nextTaskCount nextTaskBoundary
      nextValuesFinish nextValueCount nextValueBoundary
      nextStatusTag nextStatusPayloadStart nextStatusBool
      nextTaskBoundarySize nextValueBoundarySize
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound ∧
    !(compactNumericVerifierTaskBoundedHeadDef)
      tokenTable width tokenCount
      currentTaskBoundary currentTaskValueBound
      taskStart taskFinish taskTag
      taskGammaFinish taskGammaCount taskGammaBoundary
      taskFirstFinish taskFirstCount
      taskSecondFinish taskSecondCount
      taskWitnessFinish taskWitnessCount taskSuffixCount
      taskGammaBoundarySize ∧
    !(compactNumericVerifierCombineStateFrameRowsDef)
      tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      currentStatusTag taskTag
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueTableWidth nextValueValueBound ∧
    !(compactNumericVerifierCombineBranchRowsDef)
      tokenTable width tokenCount
      taskTag taskGammaFinish taskGammaCount taskGammaBoundary
      taskFirstFinish taskFirstCount taskSecondFinish taskSecondCount
      taskWitnessFinish taskWitnessCount
      currentValueBoundary currentValueCount
      nextValueBoundary nextValueCount
      currentValueTableWidth currentValueValueBound
      nextStatusTag nextStatusBool
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
      shiftWitnessBound freeTableWidth freeValueBound resultBoolValue”

def compactNumericVerifierCombineStateGraphEnvironment
    (tokenTable width tokenCount
      currentStart currentFinish
      currentProofFinish currentProofCount
      currentCertificateFinish currentCertificateCount
      currentTasksFinish currentTaskCount currentTaskBoundary
      currentValuesFinish currentValueCount currentValueBoundary
      currentStatusTag currentStatusPayloadStart currentStatusBool
      currentTaskBoundarySize currentValueBoundarySize
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextFinish
      nextProofFinish nextProofCount
      nextCertificateFinish nextCertificateCount
      nextTasksFinish nextTaskCount nextTaskBoundary
      nextValuesFinish nextValueCount nextValueBoundary
      nextStatusTag nextStatusPayloadStart nextStatusBool
      nextTaskBoundarySize nextValueBoundarySize
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      taskStart taskFinish taskTag
      taskGammaFinish taskGammaCount taskGammaBoundary
      taskFirstFinish taskFirstCount
      taskSecondFinish taskSecondCount
      taskWitnessFinish taskWitnessCount taskSuffixCount
      taskGammaBoundarySize
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
      shiftWitnessBound freeTableWidth freeValueBound resultBoolValue : Nat) :
    Fin 93 → Nat :=
  ![tokenTable, width, tokenCount,
    currentStart, currentFinish,
    currentProofFinish, currentProofCount,
    currentCertificateFinish, currentCertificateCount,
    currentTasksFinish, currentTaskCount, currentTaskBoundary,
    currentValuesFinish, currentValueCount, currentValueBoundary,
    currentStatusTag, currentStatusPayloadStart, currentStatusBool,
    currentTaskBoundarySize, currentValueBoundarySize,
    currentTaskTableWidth, currentTaskValueBound,
    currentValueTableWidth, currentValueValueBound,
    nextStart, nextFinish,
    nextProofFinish, nextProofCount,
    nextCertificateFinish, nextCertificateCount,
    nextTasksFinish, nextTaskCount, nextTaskBoundary,
    nextValuesFinish, nextValueCount, nextValueBoundary,
    nextStatusTag, nextStatusPayloadStart, nextStatusBool,
    nextTaskBoundarySize, nextValueBoundarySize,
    nextTaskTableWidth, nextTaskValueBound,
    nextValueTableWidth, nextValueValueBound,
    taskStart, taskFinish, taskTag,
    taskGammaFinish, taskGammaCount, taskGammaBoundary,
    taskFirstFinish, taskFirstCount,
    taskSecondFinish, taskSecondCount,
    taskWitnessFinish, taskWitnessCount, taskSuffixCount,
    taskGammaBoundarySize,
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

set_option maxRecDepth 32768 in
@[simp] theorem compactNumericVerifierCombineStateGraphDef_spec
    (tokenTable width tokenCount
      currentStart currentFinish
      currentProofFinish currentProofCount
      currentCertificateFinish currentCertificateCount
      currentTasksFinish currentTaskCount currentTaskBoundary
      currentValuesFinish currentValueCount currentValueBoundary
      currentStatusTag currentStatusPayloadStart currentStatusBool
      currentTaskBoundarySize currentValueBoundarySize
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextFinish
      nextProofFinish nextProofCount
      nextCertificateFinish nextCertificateCount
      nextTasksFinish nextTaskCount nextTaskBoundary
      nextValuesFinish nextValueCount nextValueBoundary
      nextStatusTag nextStatusPayloadStart nextStatusBool
      nextTaskBoundarySize nextValueBoundarySize
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      taskStart taskFinish taskTag
      taskGammaFinish taskGammaCount taskGammaBoundary
      taskFirstFinish taskFirstCount
      taskSecondFinish taskSecondCount
      taskWitnessFinish taskWitnessCount taskSuffixCount
      taskGammaBoundarySize
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
      shiftWitnessBound freeTableWidth freeValueBound resultBoolValue : Nat) :
    compactNumericVerifierCombineStateGraphDef.val.Evalb
        (compactNumericVerifierCombineStateGraphEnvironment
          tokenTable width tokenCount
          currentStart currentFinish
          currentProofFinish currentProofCount
          currentCertificateFinish currentCertificateCount
          currentTasksFinish currentTaskCount currentTaskBoundary
          currentValuesFinish currentValueCount currentValueBoundary
          currentStatusTag currentStatusPayloadStart currentStatusBool
          currentTaskBoundarySize currentValueBoundarySize
          currentTaskTableWidth currentTaskValueBound
          currentValueTableWidth currentValueValueBound
          nextStart nextFinish
          nextProofFinish nextProofCount
          nextCertificateFinish nextCertificateCount
          nextTasksFinish nextTaskCount nextTaskBoundary
          nextValuesFinish nextValueCount nextValueBoundary
          nextStatusTag nextStatusPayloadStart nextStatusBool
          nextTaskBoundarySize nextValueBoundarySize
          nextTaskTableWidth nextTaskValueBound
          nextValueTableWidth nextValueValueBound
          taskStart taskFinish taskTag
          taskGammaFinish taskGammaCount taskGammaBoundary
          taskFirstFinish taskFirstCount
          taskSecondFinish taskSecondCount
          taskWitnessFinish taskWitnessCount taskSuffixCount
          taskGammaBoundarySize
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
          shiftWitnessBound freeTableWidth freeValueBound resultBoolValue) ↔
      CompactNumericVerifierCombineStateGraph tokenTable width tokenCount
        (compactNumericVerifierStateRowCoordinatesOf
          currentStart currentFinish
          currentProofFinish currentProofCount
          currentCertificateFinish currentCertificateCount
          currentTasksFinish currentTaskCount currentTaskBoundary
          currentValuesFinish currentValueCount currentValueBoundary
          currentStatusTag currentStatusPayloadStart currentStatusBool)
        (compactNumericVerifierStateRowCoordinatesOf
          nextStart nextFinish
          nextProofFinish nextProofCount
          nextCertificateFinish nextCertificateCount
          nextTasksFinish nextTaskCount nextTaskBoundary
          nextValuesFinish nextValueCount nextValueBoundary
          nextStatusTag nextStatusPayloadStart nextStatusBool)
        { taskBoundarySize := currentTaskBoundarySize
          valueBoundarySize := currentValueBoundarySize
          taskTableWidth := currentTaskTableWidth
          taskValueBound := currentTaskValueBound
          valueTableWidth := currentValueTableWidth
          valueValueBound := currentValueValueBound }
        { taskBoundarySize := nextTaskBoundarySize
          valueBoundarySize := nextValueBoundarySize
          taskTableWidth := nextTaskTableWidth
          taskValueBound := nextTaskValueBound
          valueTableWidth := nextValueTableWidth
          valueValueBound := nextValueValueBound }
        (compactNumericVerifierTaskRowCoordinatesOf
          taskStart taskFinish taskTag
          taskGammaFinish taskGammaCount taskGammaBoundary
          taskFirstFinish taskFirstCount
          taskSecondFinish taskSecondCount
          taskWitnessFinish taskWitnessCount taskSuffixCount)
        { gammaBoundarySize := taskGammaBoundarySize }
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
          shiftWitnessBound freeTableWidth freeValueBound resultBoolValue) := by
  let env := compactNumericVerifierCombineStateGraphEnvironment
    tokenTable width tokenCount
    currentStart currentFinish
    currentProofFinish currentProofCount
    currentCertificateFinish currentCertificateCount
    currentTasksFinish currentTaskCount currentTaskBoundary
    currentValuesFinish currentValueCount currentValueBoundary
    currentStatusTag currentStatusPayloadStart currentStatusBool
    currentTaskBoundarySize currentValueBoundarySize
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextStart nextFinish
    nextProofFinish nextProofCount
    nextCertificateFinish nextCertificateCount
    nextTasksFinish nextTaskCount nextTaskBoundary
    nextValuesFinish nextValueCount nextValueBoundary
    nextStatusTag nextStatusPayloadStart nextStatusBool
    nextTaskBoundarySize nextValueBoundarySize
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    taskStart taskFinish taskTag
    taskGammaFinish taskGammaCount taskGammaBoundary
    taskFirstFinish taskFirstCount
    taskSecondFinish taskSecondCount
    taskWitnessFinish taskWitnessCount taskSuffixCount
    taskGammaBoundarySize
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
  change compactNumericVerifierCombineStateGraphDef.val.Evalb env ↔ _
  have hcurrentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 93), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17,
          #18, #19, #20, #21, #22, #23]) =
        compactNumericVerifierStateCoreFormulaEnvironment
          tokenTable width tokenCount
          currentStart currentFinish
          currentProofFinish currentProofCount
          currentCertificateFinish currentCertificateCount
          currentTasksFinish currentTaskCount currentTaskBoundary
          currentValuesFinish currentValueCount currentValueBoundary
          currentStatusTag currentStatusPayloadStart currentStatusBool
          currentTaskBoundarySize currentValueBoundarySize
          currentTaskTableWidth currentTaskValueBound
          currentValueTableWidth currentValueValueBound := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hnextEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 93), #1, #2, #24, #25, #26,
          #27, #28, #29, #30, #31, #32, #33, #34, #35, #36,
          #37, #38, #39, #40, #41, #42, #43, #44]) =
        compactNumericVerifierStateCoreFormulaEnvironment
          tokenTable width tokenCount
          nextStart nextFinish
          nextProofFinish nextProofCount
          nextCertificateFinish nextCertificateCount
          nextTasksFinish nextTaskCount nextTaskBoundary
          nextValuesFinish nextValueCount nextValueBoundary
          nextStatusTag nextStatusPayloadStart nextStatusBool
          nextTaskBoundarySize nextValueBoundarySize
          nextTaskTableWidth nextTaskValueBound
          nextValueTableWidth nextValueValueBound := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hheadEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 93), #1, #2, #11, #21,
          #45, #46, #47, #48, #49, #50, #51, #52, #53, #54,
          #55, #56, #57, #58]) =
        compactNumericVerifierTaskBoundedHeadEnvironment
          tokenTable width tokenCount
          currentTaskBoundary currentTaskValueBound
          taskStart taskFinish taskTag
          taskGammaFinish taskGammaCount taskGammaBoundary
          taskFirstFinish taskFirstCount
          taskSecondFinish taskSecondCount
          taskWitnessFinish taskWitnessCount taskSuffixCount
          taskGammaBoundarySize := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hframeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 93), #1, #2,
          #3, #7, #11, #10, #20, #21, #22, #23, #15, #47,
          #24, #28, #32, #31, #43, #44]) =
        ![tokenTable, width, tokenCount,
          currentStart, currentCertificateFinish,
          currentTaskBoundary, currentTaskCount,
          currentTaskTableWidth, currentTaskValueBound,
          currentValueTableWidth, currentValueValueBound,
          currentStatusTag, taskTag,
          nextStart, nextCertificateFinish,
          nextTaskBoundary, nextTaskCount,
          nextValueTableWidth, nextValueValueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hbranchEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 93), #1, #2,
          #47, #48, #49, #50, #51, #52, #53, #54, #55, #56,
          #14, #13, #35, #34, #22, #23, #36, #38,
          #59, #60, #61, #62, #63, #64, #65, #66, #67, #68,
          #69, #70, #71, #72, #73, #74, #75, #76, #77, #78,
          #79, #80, #81, #82, #83, #84, #85, #86, #87, #88,
          #89, #90, #91, #92]) =
        compactNumericVerifierCombineBranchRowsEnvironment
          tokenTable width tokenCount
          taskTag taskGammaFinish taskGammaCount taskGammaBoundary
          taskFirstFinish taskFirstCount taskSecondFinish taskSecondCount
          taskWitnessFinish taskWitnessCount
          currentValueBoundary currentValueCount
          nextValueBoundary nextValueCount
          currentValueTableWidth currentValueValueBound
          nextStatusTag nextStatusBool
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
          shiftWitnessBound freeTableWidth freeValueBound resultBoolValue := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierCombineStateGraphDef,
    CompactNumericVerifierCombineStateGraph,
    compactNumericVerifierStateRowCoordinatesOf,
    compactNumericVerifierTaskRowCoordinatesOf,
    compactNumericVerifierCombineRuleWitnessOf,
    hcurrentEnv, hnextEnv, hheadEnv, hframeEnv, hbranchEnv]

set_option maxRecDepth 32768 in
theorem compactNumericVerifierCombineStateGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierCombineStateGraphDef.val := by
  simp [compactNumericVerifierCombineStateGraphDef]

theorem CompactNumericVerifierCombineStateGraph.realizeExactStep
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {ruleWitness : CompactNumericVerifierCombineRuleWitness}
    (hgraph : CompactNumericVerifierCombineStateGraph
      tokenTable width tokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness ruleWitness) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  rcases hgraph with ⟨hcurrent, hnext, hhead, hframe, hbranch⟩
  exact hbranch.realizeExactStep hcurrent hnext hhead hframe

#print axioms compactNumericVerifierCombineStateGraphDef_spec
#print axioms compactNumericVerifierCombineStateGraphDef_sigmaZero
#print axioms CompactNumericVerifierCombineStateGraph.realizeExactStep

end FoundationCompactNumericListedDirectVerifierCombineStateGraph
