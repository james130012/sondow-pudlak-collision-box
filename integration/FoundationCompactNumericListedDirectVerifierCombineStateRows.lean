import integration.FoundationCompactNumericListedDirectVerifierCombineStateExactness
import integration.FoundationCompactNumericListedDirectVerifierCombineSuccessRows
import integration.FoundationCompactNumericListedDirectSimpleCombineTransitionRows
import integration.FoundationCompactNumericListedDirectAllShiftCombineRuleRows
import integration.FoundationCompactNumericListedDirectExsCutCombineRuleRows
import integration.FoundationCompactNumericListedDirectVerifierCombineFailureRows

/-!
# Exact bounded verifier combine-state rows

Each local combine graph is connected to the common state frame here.  Thus
the child-result rows, real task head, task-stack drop, preserved streams, and
stored status all refer to one pair of typed verifier states.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineStateRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRows
open FoundationCompactNumericListedDirectVerifierCombineSuccessRows
open FoundationCompactNumericListedDirectSimpleCombineTransitionRows
open FoundationCompactNumericListedDirectAllShiftCombineRuleRows
open FoundationCompactNumericListedDirectExsCutCombineRuleRows
open FoundationCompactNumericListedDirectVerifierCombineFailureRows

theorem CompactNumericSimpleCombineTransitionRows.realizeExactStep
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      resultBoolValue : Nat}
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
    (hrows : CompactNumericSimpleCombineSuccessRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound resultBoolValue
      nextCoordinates.statusTag) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  rcases hrows with ⟨hrows, hnextStatusTag⟩
  rcases hframe.realize hcurrent hnext hhead with ⟨frame⟩
  have hrows' : CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      currentCoordinates.valueBoundary frame.currentValues.length
      nextCoordinates.valueBoundary frame.nextValues.length
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound resultBoolValue := by
    simpa only [frame.currentValues_length, frame.nextValues_length] using hrows
  rcases hrows'.sound_combineTransition
      hhead.core frame.taskLayout
      frame.currentValueRows frame.nextValueRows
      frame.currentValueGraph frame.nextValueGraph with
    ⟨combined, hcombine, hvalues⟩
  exact frame.realizeExactSuccess hcombine hvalues hnextStatusTag

theorem CompactNumericAllShiftCombineRuleRows.realizeExactStep
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {premiseGammaCount premiseGammaBoundary premiseBoolValue
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      resultBoolValue : Nat}
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
    (hrows : CompactNumericAllShiftCombineSuccessRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound resultBoolValue
      nextCoordinates.statusTag) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  rcases hrows with ⟨hrows, hnextStatusTag⟩
  rcases hframe.realize hcurrent hnext hhead with ⟨frame⟩
  have hrows' : CompactNumericAllShiftCombineRuleRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
      premiseGammaCount premiseGammaBoundary premiseBoolValue
      currentCoordinates.valueBoundary frame.currentValues.length
      nextCoordinates.valueBoundary frame.nextValues.length
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary freedCount freedBoundarySize
      freeStateBoundary freeStateCount
      shiftCandidateBoundary shiftSuccessTable
      shiftedBoundary shiftedCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth freeValueBound
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound resultBoolValue := by
    simpa only [frame.currentValues_length, frame.nextValues_length] using hrows
  rcases hrows'.sound_combineTransition
      hhead.core frame.taskLayout
      frame.currentValueRows frame.nextValueRows
      frame.currentValueGraph frame.nextValueGraph with
    ⟨combined, hcombine, hvalues⟩
  exact frame.realizeExactSuccess hcombine hvalues hnextStatusTag

theorem CompactNumericExsCutCombineRuleRows.realizeExactStep
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      resultBoolValue : Nat}
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
    (hrows : CompactNumericExsCutCombineSuccessRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.witnessFinish
        taskCoordinates.witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound resultBoolValue
      nextCoordinates.statusTag) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  rcases hrows with ⟨hrows, hnextStatusTag⟩
  rcases hframe.realize hcurrent hnext hhead with ⟨frame⟩
  have hrows' : CompactNumericExsCutCombineRuleRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.witnessFinish
        taskCoordinates.witnessCount
      rightGammaCount rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      currentCoordinates.valueBoundary frame.currentValues.length
      nextCoordinates.valueBoundary frame.nextValues.length
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
      transformedCount transformedBoundarySize
      transformStateBoundary transformStateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth transformValueBound
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound resultBoolValue := by
    simpa only [frame.currentValues_length, frame.nextValues_length] using hrows
  rcases hrows'.sound_combineTransition
      hhead.core frame.taskLayout
      frame.currentValueRows frame.nextValueRows
      frame.currentValueGraph frame.nextValueGraph with
    ⟨combined, hcombine, hvalues⟩
  exact frame.realizeExactSuccess hcombine hvalues hnextStatusTag

theorem CompactNumericVerifierCombineFailureRows.realizeExactStep
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
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
    (hrows : CompactNumericVerifierCombineFailureRows
      tokenTable width tokenCount taskCoordinates.tag
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      nextCoordinates.statusTag nextCoordinates.statusBool) :
    ∃ currentState nextState : CompactNumericVerifierState,
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount currentCoordinates.start
          currentCoordinates.finish currentState ∧
      CompactNumericVerifierStateDirectLayout
        tokenTable width tokenCount nextCoordinates.start
          nextCoordinates.finish nextState ∧
      nextState = compactNumericVerifierStep currentState := by
  rcases hframe.realize hcurrent hnext hhead with ⟨frame⟩
  have hrows' : CompactNumericVerifierCombineFailureRows
      tokenTable width tokenCount taskCoordinates.tag
      currentCoordinates.valueBoundary frame.currentValues.length
      nextCoordinates.valueBoundary frame.nextValues.length
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      nextCoordinates.statusTag nextCoordinates.statusBool := by
    simpa only [frame.currentValues_length, frame.nextValues_length] using hrows
  rcases hrows'.sound frame.taskTag_eq
      frame.currentValueRows frame.nextValueRows with
    ⟨hcombine, hvalues, hnextStatusTag, hnextStatusBool⟩
  exact frame.realizeExactFailure
    hcombine hvalues hnextStatusTag hnextStatusBool

#print axioms CompactNumericSimpleCombineTransitionRows.realizeExactStep
#print axioms CompactNumericAllShiftCombineRuleRows.realizeExactStep
#print axioms CompactNumericExsCutCombineRuleRows.realizeExactStep
#print axioms CompactNumericVerifierCombineFailureRows.realizeExactStep

end FoundationCompactNumericListedDirectVerifierCombineStateRows
