import integration.FoundationCompactNumericListedDirectVerifierParseFailureBranchRows

/-!
# Complete bounded state graph for a failed verifier parse step

The graph joins both typed state cores, the actual parse-task head, the common
parse frame, and the exact parser-failure/state-update branch.  Every component
uses the same fixed-width token table and the state core's stream endpoints.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseFailureStateGraph

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierParseStateFrameRows
open FoundationCompactNumericListedDirectVerifierParseFailureBranchRows

def CompactNumericVerifierParseFailureStateGraph
    (tokenTable width tokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates)
    (taskSizeWitness : CompactNumericVerifierTaskSizeWitness)
    (rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound : Nat) : Prop :=
  CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount currentCoordinates currentSizeWitness ∧
    CompactNumericVerifierStateCoreGraph
      tokenTable width tokenCount nextCoordinates nextSizeWitness ∧
    CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount currentCoordinates.taskBoundary
      currentSizeWitness.taskValueBound taskCoordinates taskSizeWitness ∧
    CompactNumericVerifierParseStateFrameRows
      currentCoordinates.taskCount currentCoordinates.statusTag
      taskCoordinates ∧
    CompactNumericVerifierParseFailureBranchRows
      tokenTable width tokenCount
      currentCoordinates.start currentCoordinates.proofFinish
        currentCoordinates.certificateFinish
      currentCoordinates.taskBoundary currentCoordinates.taskCount
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
      currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
      nextCoordinates.start nextCoordinates.certificateFinish
      nextCoordinates.taskBoundary nextCoordinates.taskCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
      nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
      nextCoordinates.statusTag nextCoordinates.statusBool
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound

def compactNumericVerifierParseFailureStateGraphDef :
    𝚺₀.Semisentence 71 := .mkSigma
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
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound.
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
    !(compactNumericVerifierParseStateFrameRowsDef)
      currentTaskCount currentStatusTag
      taskTag taskGammaCount taskFirstCount taskSecondCount
      taskWitnessCount taskSuffixCount ∧
    !(compactNumericVerifierParseFailureBranchRowsDef)
      tokenTable width tokenCount
      currentStart currentProofFinish currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound”

def compactNumericVerifierParseFailureStateGraphEnvironment
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
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound : Nat) : Fin 71 → Nat :=
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
    rootStart, rootFinish, proofTag,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag,
    proofEndpointBound, certificateEndpointBound]

set_option maxRecDepth 32768 in
@[simp] theorem compactNumericVerifierParseFailureStateGraphDef_spec
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
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound : Nat) :
    compactNumericVerifierParseFailureStateGraphDef.val.Evalb
        (compactNumericVerifierParseFailureStateGraphEnvironment
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
          rootStart rootFinish proofTag
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag
          proofEndpointBound certificateEndpointBound) ↔
      CompactNumericVerifierParseFailureStateGraph
        tokenTable width tokenCount
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
        rootStart rootFinish proofTag
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag
        proofEndpointBound certificateEndpointBound := by
  let env := compactNumericVerifierParseFailureStateGraphEnvironment
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
    rootStart rootFinish proofTag
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag
    proofEndpointBound certificateEndpointBound
  change compactNumericVerifierParseFailureStateGraphDef.val.Evalb env ↔ _
  have hcurrentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 71), #1, #2, #3, #4, #5, #6,
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
        ![(#0 : Semiterm ℒₒᵣ Empty 71), #1, #2, #24, #25, #26,
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
        ![(#0 : Semiterm ℒₒᵣ Empty 71), #1, #2, #11, #21,
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
        ![(#10 : Semiterm ℒₒᵣ Empty 71), #15, #47, #49,
          #52, #54, #56, #57]) =
        ![currentTaskCount, currentStatusTag,
          taskTag, taskGammaCount, taskFirstCount, taskSecondCount,
          taskWitnessCount, taskSuffixCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hbranchEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 71), #1, #2,
          #3, #5, #7, #11, #10, #14, #13, #20, #21, #22, #23,
          #24, #28, #32, #31, #35, #34, #41, #42, #43, #44,
          #36, #38, #59, #60, #61, #62, #63, #64, #65,
          #66, #67, #68, #69, #70]) =
        compactNumericVerifierParseFailureBranchRowsEnvironment
          tokenTable width tokenCount
          currentStart currentProofFinish currentCertificateFinish
          currentTaskBoundary currentTaskCount
          currentValueBoundary currentValueCount
          currentTaskTableWidth currentTaskValueBound
          currentValueTableWidth currentValueValueBound
          nextStart nextCertificateFinish
          nextTaskBoundary nextTaskCount
          nextValueBoundary nextValueCount
          nextTaskTableWidth nextTaskValueBound
          nextValueTableWidth nextValueValueBound
          nextStatusTag nextStatusBool
          rootStart rootFinish proofTag
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag
          proofEndpointBound certificateEndpointBound := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierParseFailureStateGraphDef,
    CompactNumericVerifierParseFailureStateGraph,
    CompactNumericVerifierParseStateFrameRows,
    compactNumericVerifierStateRowCoordinatesOf,
    compactNumericVerifierTaskRowCoordinatesOf,
    hcurrentEnv, hnextEnv, hheadEnv, hframeEnv, hbranchEnv]

set_option maxRecDepth 32768 in
theorem compactNumericVerifierParseFailureStateGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierParseFailureStateGraphDef.val := by
  simp [compactNumericVerifierParseFailureStateGraphDef]

theorem CompactNumericVerifierParseFailureStateGraph.realizeExactStep
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound : Nat}
    (hgraph : CompactNumericVerifierParseFailureStateGraph
      tokenTable width tokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  rcases hgraph with ⟨hcurrent, hnext, hhead, hframe, hbranch⟩
  rcases hframe.realize hcurrent hnext hhead with ⟨realization⟩
  have hbranchTyped : CompactNumericVerifierParseFailureBranchRows
      tokenTable width tokenCount
      currentCoordinates.start currentCoordinates.proofFinish
        currentCoordinates.certificateFinish
      currentCoordinates.taskBoundary realization.currentTasks.length
      currentCoordinates.valueBoundary realization.currentValues.length
      currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
      currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
      nextCoordinates.start nextCoordinates.certificateFinish
      nextCoordinates.taskBoundary realization.nextTasks.length
      nextCoordinates.valueBoundary realization.nextValues.length
      nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
      nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
      nextCoordinates.statusTag nextCoordinates.statusBool
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound := by
    simpa only [realization.currentTasks_length,
      realization.currentValues_length,
      realization.nextTasks_length,
      realization.nextValues_length] using hbranch
  rcases hbranchTyped.sound
      realization.currentProofLayout realization.currentCertificateLayout
      realization.nextProofLayout realization.nextCertificateLayout
      realization.currentTaskRows realization.nextTaskRows
      realization.currentValueRows realization.nextValueRows with
    ⟨hparse, hnextProof, hnextCertificate, hnextTasks, hnextValues,
      _hnextTaskTableWidth, _hnextTaskValueBound,
      _hnextValueTableWidth, _hnextValueValueBound,
      hnextStatusTag, hnextStatusBool⟩
  have hnextStatus : realization.nextStatus = some false := by
    rcases realization.nextStatusCase with hnone | hsome
    · omega
    · rcases hsome with ⟨result, hstatus, _htag, hbool⟩
      have hresult : result = false := by
        cases result
        · rfl
        · simp [compactAdditiveBoolTag] at hbool hnextStatusBool
          omega
      simpa [hresult] using hstatus
  let currentState : CompactNumericVerifierState :=
    (((realization.currentProofTokens,
        realization.currentCertificateTokens),
      (realization.currentTasks, realization.currentValues)), none)
  let nextState : CompactNumericVerifierState :=
    (((realization.nextProofTokens,
        realization.nextCertificateTokens),
      (realization.nextTasks, realization.nextValues)),
      realization.nextStatus)
  refine ⟨currentState, nextState,
    realization.currentLayout, realization.nextLayout, ?_⟩
  dsimp only [currentState, nextState]
  rw [hnextProof, hnextCertificate, hnextTasks, hnextValues, hnextStatus]
  have hparseRest : compactNumericParsePayload
      ((realization.currentProofTokens,
        realization.currentCertificateTokens),
        (realization.currentRestTasks, realization.currentValues)) = none := by
    rw [realization.currentRestTasks_eq]
    exact hparse
  rw [realization.currentTasks_eq]
  simp [compactNumericVerifierStep, compactNumericRunningStep,
    realization.currentTaskTag, compactNumericParseState, hparseRest]

#print axioms compactNumericVerifierParseFailureStateGraphDef_spec
#print axioms compactNumericVerifierParseFailureStateGraphDef_sigmaZero
#print axioms CompactNumericVerifierParseFailureStateGraph.realizeExactStep

end FoundationCompactNumericListedDirectVerifierParseFailureStateGraph
