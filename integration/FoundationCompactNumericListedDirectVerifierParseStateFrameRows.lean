import integration.FoundationCompactNumericListedDirectVerifierStateRealization
import integration.FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
import integration.FoundationCompactNumericListedDirectVerifierParseScheduleRows

/-!
# Common bounded frame for verifier parse states

A parse step starts in a running state whose task-list head has public tag 10.
The executable branch ignores the other task fields, so this frame validates
their encoding without requiring them to be empty.  Generated parse tasks in
non-leaf schedules remain subject to the stricter empty-field shape.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseStateFrameRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStateRealization
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierParseScheduleRows

def CompactNumericVerifierParseStateFrameRows
    (currentTaskCount currentStatusTag : Nat)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates) : Prop :=
  currentStatusTag = 0 ∧
    1 ≤ currentTaskCount ∧
    taskCoordinates.tag = 10

def compactNumericVerifierParseStateFrameRowsDef :
    𝚺₀.Semisentence 8 := .mkSigma
  “currentTaskCount currentStatusTag
      taskTag taskGammaCount taskFirstCount taskSecondCount
      taskWitnessCount taskSuffixCount.
    currentStatusTag = 0 ∧
    1 ≤ currentTaskCount ∧
    taskTag = 10”

@[simp] theorem compactNumericVerifierParseStateFrameRowsDef_spec
    (currentTaskCount currentStatusTag
      taskTag taskGammaCount taskFirstCount taskSecondCount
      taskWitnessCount taskSuffixCount : Nat) :
    compactNumericVerifierParseStateFrameRowsDef.val.Evalb
        ![currentTaskCount, currentStatusTag,
          taskTag, taskGammaCount, taskFirstCount, taskSecondCount,
          taskWitnessCount, taskSuffixCount] ↔
      CompactNumericVerifierParseStateFrameRows
        currentTaskCount currentStatusTag
        { start := 0
          finish := 0
          tag := taskTag
          gammaFinish := 0
          gammaCount := taskGammaCount
          gammaBoundary := 0
          firstFinish := 0
          firstCount := taskFirstCount
          secondFinish := 0
          secondCount := taskSecondCount
          witnessFinish := 0
          witnessCount := taskWitnessCount
          suffixCount := taskSuffixCount } := by
  simp [compactNumericVerifierParseStateFrameRowsDef,
    CompactNumericVerifierParseStateFrameRows]

theorem compactNumericVerifierParseStateFrameRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierParseStateFrameRowsDef.val := by
  simp [compactNumericVerifierParseStateFrameRowsDef]

structure CompactNumericVerifierParseStateFrameRealization
    (tokenTable width tokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness) where
  currentProofTokens : List Nat
  currentCertificateTokens : List Nat
  currentTasks : List CompactNumericVerifierTask
  currentValues : List CompactNumericChildResult
  nextProofTokens : List Nat
  nextCertificateTokens : List Nat
  nextTasks : List CompactNumericVerifierTask
  nextValues : List CompactNumericChildResult
  nextStatus : Option Bool
  currentLayout : CompactNumericVerifierStateDirectLayout
    tokenTable width tokenCount currentCoordinates.start
      currentCoordinates.finish
      (((currentProofTokens, currentCertificateTokens),
        (currentTasks, currentValues)), none)
  nextLayout : CompactNumericVerifierStateDirectLayout
    tokenTable width tokenCount nextCoordinates.start
      nextCoordinates.finish
      (((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues)), nextStatus)
  currentProofLayout : CompactAdditiveNatListDirectLayout
    tokenTable width tokenCount currentCoordinates.start
      currentCoordinates.proofFinish currentProofTokens
  currentCertificateLayout : CompactAdditiveNatListDirectLayout
    tokenTable width tokenCount currentCoordinates.proofFinish
      currentCoordinates.certificateFinish currentCertificateTokens
  nextProofLayout : CompactAdditiveNatListDirectLayout
    tokenTable width tokenCount nextCoordinates.start
      nextCoordinates.proofFinish nextProofTokens
  nextCertificateLayout : CompactAdditiveNatListDirectLayout
    tokenTable width tokenCount nextCoordinates.proofFinish
      nextCoordinates.certificateFinish nextCertificateTokens
  currentTaskRows : CompactAdditiveStructuredListElementRowLayouts
    CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
      currentCoordinates.taskBoundary currentTasks
  nextTaskRows : CompactAdditiveStructuredListElementRowLayouts
    CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
      nextCoordinates.taskBoundary nextTasks
  currentValueRows : CompactAdditiveStructuredListElementRowLayouts
    CompactNumericChildResultDirectLayout tokenTable width tokenCount
      currentCoordinates.valueBoundary currentValues
  nextValueRows : CompactAdditiveStructuredListElementRowLayouts
    CompactNumericChildResultDirectLayout tokenTable width tokenCount
      nextCoordinates.valueBoundary nextValues
  currentTaskGraph : CompactNumericVerifierTaskListRowsGraph
    tokenTable width tokenCount currentCoordinates.taskBoundary
      currentTasks.length currentSizeWitness.taskTableWidth
      currentSizeWitness.taskValueBound
  nextTaskGraph : CompactNumericVerifierTaskListRowsGraph
    tokenTable width tokenCount nextCoordinates.taskBoundary
      nextTasks.length nextSizeWitness.taskTableWidth
      nextSizeWitness.taskValueBound
  currentValueGraph : CompactNumericChildResultListRowsGraph
    tokenTable width tokenCount currentCoordinates.valueBoundary
      currentValues.length currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
  nextValueGraph : CompactNumericChildResultListRowsGraph
    tokenTable width tokenCount nextCoordinates.valueBoundary
      nextValues.length nextSizeWitness.valueTableWidth
      nextSizeWitness.valueValueBound
  currentProofTokens_length :
    currentProofTokens.length = currentCoordinates.proofCount
  currentCertificateTokens_length :
    currentCertificateTokens.length = currentCoordinates.certificateCount
  currentTasks_length : currentTasks.length = currentCoordinates.taskCount
  currentValues_length : currentValues.length = currentCoordinates.valueCount
  nextProofTokens_length : nextProofTokens.length = nextCoordinates.proofCount
  nextCertificateTokens_length :
    nextCertificateTokens.length = nextCoordinates.certificateCount
  nextTasks_length : nextTasks.length = nextCoordinates.taskCount
  nextValues_length : nextValues.length = nextCoordinates.valueCount
  currentTask : CompactNumericVerifierTask
  currentRestTasks : List CompactNumericVerifierTask
  currentTasks_eq : currentTasks = currentTask :: currentRestTasks
  currentTaskTag : currentTask.1 = 10
  currentRestTasks_eq : currentRestTasks = currentTasks.drop 1
  nextStatusCase :
    (nextStatus = none ∧ nextCoordinates.statusTag = 0) ∨
      ∃ result : Bool,
        nextStatus = some result ∧
        nextCoordinates.statusTag = 1 ∧
        compactAdditiveBoolTag result = nextCoordinates.statusBool

theorem CompactNumericVerifierParseStateFrameRows.realize
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
      currentSizeWitness.taskValueBound taskCoordinates taskSizeWitness)
    (hframe : CompactNumericVerifierParseStateFrameRows
      currentCoordinates.taskCount currentCoordinates.statusTag
      taskCoordinates) :
    Nonempty (CompactNumericVerifierParseStateFrameRealization
      tokenTable width tokenCount currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness) := by
  rcases hframe with ⟨hcurrentStatusTag, htaskCount, hparseTag⟩
  rcases CompactNumericVerifierStateCoreGraph.realizeDirectLayout hcurrent with
    ⟨currentProofTokens, currentCertificateTokens,
      currentTasks, currentValues, currentStatus,
      hcurrentProofLength, hcurrentCertificateLength,
      hcurrentTasksLength, hcurrentValuesLength,
      hcurrentLayout,
      hcurrentProofLayout, hcurrentCertificateLayout,
      _hcurrentTaskLayout, hcurrentTaskRows,
      _hcurrentValueLayout, hcurrentValueRows,
      hcurrentStatus⟩
  rcases CompactNumericVerifierStateCoreGraph.realizeDirectLayout hnext with
    ⟨nextProofTokens, nextCertificateTokens,
      nextTasks, nextValues, nextStatus,
      hnextProofLength, hnextCertificateLength,
      hnextTasksLength, hnextValuesLength,
      hnextLayout,
      hnextProofLayout, hnextCertificateLayout,
      _hnextTaskLayout, hnextTaskRows,
      _hnextValueLayout, hnextValueRows,
      hnextStatus⟩
  have hcurrentStatusNone : currentStatus = none := by
    rcases hcurrentStatus with hnone | hsome
    · exact hnone.1
    · rcases hsome with ⟨result, _hstatus, htag, _hbool⟩
      omega
  have hcurrentTasksNonempty : 0 < currentTasks.length := by
    omega
  rcases hhead.realize_actualHeadWithFields
      hcurrentTasksNonempty hcurrentTaskRows with
    ⟨task, htaskActual, htaskTag, _htaskLayout,
      _hgammaRows, _hgammaLength,
      _hfirstLayout, _hfirstLength,
      _hsecondLayout, _hsecondLength,
      _hwitnessLayout, _hwitnessLength,
      _hsuffixLayout, _hsuffixLength⟩
  have htaskTagValue : task.1 = 10 := htaskTag.trans hparseTag
  have hcurrentTasksParts : ∃ restTasks,
      currentTasks = task :: restTasks ∧
      restTasks = currentTasks.drop 1 := by
    cases htasks : currentTasks with
    | nil => simp [htasks] at hcurrentTasksNonempty
    | cons head tail =>
        have htaskHead : task = head := by
          simpa [htasks] using htaskActual
        exact ⟨tail, by simp [htaskHead], by simp⟩
  rcases hcurrentTasksParts with
    ⟨currentRestTasks, hcurrentTasksEq, hcurrentRestTasksEq⟩
  have hcurrentTaskGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount currentCoordinates.taskBoundary
      currentTasks.length currentSizeWitness.taskTableWidth
      currentSizeWitness.taskValueBound := by
    simpa [hcurrentTasksLength] using
      hcurrent.2.2.2.1
  have hnextTaskGraph : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount nextCoordinates.taskBoundary
      nextTasks.length nextSizeWitness.taskTableWidth
      nextSizeWitness.taskValueBound := by
    simpa [hnextTasksLength] using
      hnext.2.2.2.1
  have hcurrentValueGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount currentCoordinates.valueBoundary
      currentValues.length currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa [hcurrentValuesLength] using
      hcurrent.2.2.2.2.2.2.2.1
  have hnextValueGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount nextCoordinates.valueBoundary
      nextValues.length nextSizeWitness.valueTableWidth
      nextSizeWitness.valueValueBound := by
    simpa [hnextValuesLength] using
      hnext.2.2.2.2.2.2.2.1
  have hcurrentLayout' : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount currentCoordinates.start
      currentCoordinates.finish
      (((currentProofTokens, currentCertificateTokens),
        (currentTasks, currentValues)), none) := by
    simpa [hcurrentStatusNone] using hcurrentLayout
  exact ⟨
    { currentProofTokens := currentProofTokens
      currentCertificateTokens := currentCertificateTokens
      currentTasks := currentTasks
      currentValues := currentValues
      nextProofTokens := nextProofTokens
      nextCertificateTokens := nextCertificateTokens
      nextTasks := nextTasks
      nextValues := nextValues
      nextStatus := nextStatus
      currentLayout := hcurrentLayout'
      nextLayout := hnextLayout
      currentProofLayout := hcurrentProofLayout
      currentCertificateLayout := hcurrentCertificateLayout
      nextProofLayout := hnextProofLayout
      nextCertificateLayout := hnextCertificateLayout
      currentTaskRows := hcurrentTaskRows
      nextTaskRows := hnextTaskRows
      currentValueRows := hcurrentValueRows
      nextValueRows := hnextValueRows
      currentTaskGraph := hcurrentTaskGraph
      nextTaskGraph := hnextTaskGraph
      currentValueGraph := hcurrentValueGraph
      nextValueGraph := hnextValueGraph
      currentProofTokens_length := hcurrentProofLength
      currentCertificateTokens_length := hcurrentCertificateLength
      currentTasks_length := hcurrentTasksLength
      currentValues_length := hcurrentValuesLength
      nextProofTokens_length := hnextProofLength
      nextCertificateTokens_length := hnextCertificateLength
      nextTasks_length := hnextTasksLength
      nextValues_length := hnextValuesLength
      currentTask := task
      currentRestTasks := currentRestTasks
      currentTasks_eq := hcurrentTasksEq
      currentTaskTag := htaskTagValue
      currentRestTasks_eq := hcurrentRestTasksEq
      nextStatusCase := hnextStatus }⟩

#print axioms compactNumericVerifierParseStateFrameRowsDef_spec
#print axioms compactNumericVerifierParseStateFrameRowsDef_sigmaZero
#print axioms CompactNumericVerifierParseStateFrameRows.realize

end FoundationCompactNumericListedDirectVerifierParseStateFrameRows
