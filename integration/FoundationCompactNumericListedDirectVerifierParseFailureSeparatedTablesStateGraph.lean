import integration.FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesBranchRows

/-!
# Complete bounded state graph for a failed verifier parse step with separated tables

The state-transition rows use the verifier state table.  Proof and certificate
parsing use their own independent bounded tables.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierParseStateFrameRows
open FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesBranchRows

def CompactNumericVerifierParseFailureSeparatedTablesStateGraph
    (stateTable stateWidth stateTokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates)
    (taskSizeWitness : CompactNumericVerifierTaskSizeWitness)
    (proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat) : Prop :=
  CompactNumericVerifierStateCoreGraph
      stateTable stateWidth stateTokenCount currentCoordinates currentSizeWitness ∧
    CompactNumericVerifierStateCoreGraph
      stateTable stateWidth stateTokenCount nextCoordinates nextSizeWitness ∧
    CompactNumericVerifierTaskBoundedHead
      stateTable stateWidth stateTokenCount currentCoordinates.taskBoundary
      currentSizeWitness.taskValueBound taskCoordinates taskSizeWitness ∧
    CompactNumericVerifierParseStateFrameRows
      currentCoordinates.taskCount currentCoordinates.statusTag
      taskCoordinates ∧
    CompactNumericVerifierParseFailureSeparatedTablesBranchRows
      stateTable stateWidth stateTokenCount
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
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound

def compactNumericVerifierParseFailureSeparatedTablesStateGraphDef :
    𝚺₀.Semisentence 81 := .mkSigma
  “stateTable stateWidth stateTokenCount
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
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound.
    !(compactNumericVerifierStateCoreGraphDef)
      stateTable stateWidth stateTokenCount
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
      stateTable stateWidth stateTokenCount
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
      stateTable stateWidth stateTokenCount
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
    !(compactNumericVerifierParseFailureSeparatedTablesBranchRowsDef)
      stateTable stateWidth stateTokenCount
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
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound”

def compactNumericVerifierParseFailureSeparatedTablesStateGraphEnvironment
    (stateTable stateWidth stateTokenCount
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
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat) : Fin 81 → Nat :=
  ![stateTable, stateWidth, stateTokenCount,
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
    proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound]

set_option maxRecDepth 32768 in
@[simp] theorem compactNumericVerifierParseFailureSeparatedTablesStateGraphDef_spec
    (stateTable stateWidth stateTokenCount
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
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat) :
    compactNumericVerifierParseFailureSeparatedTablesStateGraphDef.val.Evalb
        (compactNumericVerifierParseFailureSeparatedTablesStateGraphEnvironment
          stateTable stateWidth stateTokenCount
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
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound) ↔
      CompactNumericVerifierParseFailureSeparatedTablesStateGraph
        stateTable stateWidth stateTokenCount
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
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound := by
  let env := compactNumericVerifierParseFailureSeparatedTablesStateGraphEnvironment
    stateTable stateWidth stateTokenCount
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
    proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
    rootStart rootFinish proofTag proofEndpointBound
    certificateTable certificateWidth certificateTokenCount
    certificateInputStart certificateInputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag certificateEndpointBound
  change compactNumericVerifierParseFailureSeparatedTablesStateGraphDef.val.Evalb env ↔ _
  have hcurrentEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 81), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17,
          #18, #19, #20, #21, #22, #23]) =
        compactNumericVerifierStateCoreFormulaEnvironment
          stateTable stateWidth stateTokenCount
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
        ![(#0 : Semiterm ℒₒᵣ Empty 81), #1, #2, #24, #25, #26,
          #27, #28, #29, #30, #31, #32, #33, #34, #35, #36,
          #37, #38, #39, #40, #41, #42, #43, #44]) =
        compactNumericVerifierStateCoreFormulaEnvironment
          stateTable stateWidth stateTokenCount
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
        ![(#0 : Semiterm ℒₒᵣ Empty 81), #1, #2, #11, #21,
          #45, #46, #47, #48, #49, #50, #51, #52, #53, #54,
          #55, #56, #57, #58]) =
        compactNumericVerifierTaskBoundedHeadEnvironment
          stateTable stateWidth stateTokenCount
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
        ![(#10 : Semiterm ℒₒᵣ Empty 81), #15, #47, #49,
          #52, #54, #56, #57]) =
        ![currentTaskCount, currentStatusTag,
          taskTag, taskGammaCount, taskFirstCount, taskSecondCount,
          taskWitnessCount, taskSuffixCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hbranchEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 81), #1, #2,
          #3, #5, #7, #11, #10, #14, #13, #20, #21, #22, #23,
          #24, #28, #32, #31, #35, #34, #41, #42, #43, #44,
          #36, #38, #59, #60, #61, #62, #63, #64, #65, #66, #67,
          #68, #69, #70, #71, #72, #73, #74, #75, #76, #77, #78,
          #79, #80]) =
        compactNumericVerifierParseFailureSeparatedTablesBranchRowsEnvironment
          stateTable stateWidth stateTokenCount
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
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierParseFailureSeparatedTablesStateGraphDef,
    CompactNumericVerifierParseFailureSeparatedTablesStateGraph,
    CompactNumericVerifierParseStateFrameRows,
    FoundationCompactNumericListedDirectVerifierParseScheduleRows.CompactNumericParseTaskShape,
    compactNumericVerifierStateRowCoordinatesOf,
    compactNumericVerifierTaskRowCoordinatesOf,
    hcurrentEnv, hnextEnv, hheadEnv, hframeEnv, hbranchEnv]

set_option maxRecDepth 32768 in
theorem compactNumericVerifierParseFailureSeparatedTablesStateGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierParseFailureSeparatedTablesStateGraphDef.val := by
  simp [compactNumericVerifierParseFailureSeparatedTablesStateGraphDef]

theorem CompactNumericVerifierParseFailureSeparatedTablesStateGraph.realizeExactStep
    {stateTable stateWidth stateTokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat}
    (hgraph : CompactNumericVerifierParseFailureSeparatedTablesStateGraph
      stateTable stateWidth stateTokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness
      taskCoordinates taskSizeWitness
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        stateTable stateWidth stateTokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        stateTable stateWidth stateTokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  rcases hgraph with ⟨hcurrent, hnext, hhead, hframe, hbranch⟩
  rcases hframe.realize hcurrent hnext hhead with ⟨realization⟩
  have hbranchTyped : CompactNumericVerifierParseFailureSeparatedTablesBranchRows
      stateTable stateWidth stateTokenCount
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
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound := by
    simpa only [realization.currentTasks_length,
      realization.currentValues_length,
      realization.nextTasks_length,
      realization.nextValues_length] using hbranch
  rcases _root_.FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesBranchRows.CompactNumericVerifierParseFailureSeparatedTablesBranchRows.sound hbranchTyped
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
  have hparseTail : compactNumericParsePayload
      ((realization.currentProofTokens,
        realization.currentCertificateTokens),
        (realization.currentTasks.tail, realization.currentValues)) = none := by
    simpa only [List.drop_one] using hparse
  rw [realization.currentTasks_eq]
  simp [compactNumericVerifierStep, compactNumericRunningStep,
    compactNumericParseTask, compactNumericParseState, hparseTail]

#print axioms compactNumericVerifierParseFailureSeparatedTablesStateGraphDef_spec
#print axioms compactNumericVerifierParseFailureSeparatedTablesStateGraphDef_sigmaZero
#print axioms FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph.CompactNumericVerifierParseFailureSeparatedTablesStateGraph.realizeExactStep

end FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph
