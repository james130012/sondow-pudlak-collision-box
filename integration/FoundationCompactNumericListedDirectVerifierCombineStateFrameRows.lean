import integration.FoundationCompactNumericListedDirectVerifierStateRealization
import integration.FoundationCompactNumericListedDirectVerifierTaskListDropRows
import integration.FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula

/-!
# Common bounded frame for verifier combine states

A combine step preserves both input streams, removes exactly the task-list
head, and operates on one common child-result row coordinate.  This module
expresses those facts as a bounded graph and realizes them against the typed
current and next states.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineStateFrameRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierStateRealization
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierTaskListDropRows
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula

def CompactNumericVerifierCombineStateFrameRows
    (tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      currentStatusTag taskTag
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueTableWidth nextValueValueBound : Nat) : Prop :=
  currentStatusTag = 0 ∧
    1 ≤ currentTaskCount ∧
    taskTag ≠ 10 ∧
    nextValueTableWidth = currentValueTableWidth ∧
    nextValueValueBound = currentValueValueBound ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      currentStart currentCertificateFinish
      nextStart nextCertificateFinish ∧
    CompactNumericVerifierTaskListDropRows
      tokenTable width tokenCount
      currentTaskBoundary currentTaskCount
      nextTaskBoundary nextTaskCount
      currentTaskTableWidth currentTaskValueBound 1

def compactNumericVerifierCombineStateFrameRowsDef :
    𝚺₀.Semisentence 19 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      currentStatusTag taskTag
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueTableWidth nextValueValueBound.
    currentStatusTag = 0 ∧
    1 ≤ currentTaskCount ∧
    taskTag ≠ 10 ∧
    nextValueTableWidth = currentValueTableWidth ∧
    nextValueValueBound = currentValueValueBound ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
      currentStart currentCertificateFinish
      nextStart nextCertificateFinish ∧
    !(compactNumericVerifierTaskListDropRowsDef)
      tokenTable width tokenCount
      currentTaskBoundary currentTaskCount
      nextTaskBoundary nextTaskCount
      currentTaskTableWidth currentTaskValueBound 1”

@[simp] theorem compactNumericVerifierCombineStateFrameRowsDef_spec
    (tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      currentStatusTag taskTag
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueTableWidth nextValueValueBound : Nat) :
    compactNumericVerifierCombineStateFrameRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          currentStart, currentCertificateFinish,
          currentTaskBoundary, currentTaskCount,
          currentTaskTableWidth, currentTaskValueBound,
          currentValueTableWidth, currentValueValueBound,
          currentStatusTag, taskTag,
          nextStart, nextCertificateFinish,
          nextTaskBoundary, nextTaskCount,
          nextValueTableWidth, nextValueValueBound] ↔
      CompactNumericVerifierCombineStateFrameRows
        tokenTable width tokenCount
        currentStart currentCertificateFinish
        currentTaskBoundary currentTaskCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        currentStatusTag taskTag
        nextStart nextCertificateFinish
        nextTaskBoundary nextTaskCount
        nextValueTableWidth nextValueValueBound := by
  have hslicesEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount,
            currentStart, currentCertificateFinish,
            currentTaskBoundary, currentTaskCount,
            currentTaskTableWidth, currentTaskValueBound,
            currentValueTableWidth, currentValueValueBound,
            currentStatusTag, taskTag,
            nextStart, nextCertificateFinish,
            nextTaskBoundary, nextTaskCount,
            nextValueTableWidth, nextValueValueBound]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2,
          #3, #4, #13, #14]) =
        ![tokenTable, width, tokenCount,
          currentStart, currentCertificateFinish,
          nextStart, nextCertificateFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hdropEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount,
            currentStart, currentCertificateFinish,
            currentTaskBoundary, currentTaskCount,
            currentTaskTableWidth, currentTaskValueBound,
            currentValueTableWidth, currentValueValueBound,
            currentStatusTag, taskTag,
            nextStart, nextCertificateFinish,
            nextTaskBoundary, nextTaskCount,
            nextValueTableWidth, nextValueValueBound]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2,
          #5, #6, #15, #16, #7, #8,
          (‘1’ : Semiterm ℒₒᵣ Empty 19)]) =
        ![tokenTable, width, tokenCount,
          currentTaskBoundary, currentTaskCount,
          nextTaskBoundary, nextTaskCount,
          currentTaskTableWidth, currentTaskValueBound, 1] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierCombineStateFrameRowsDef,
    CompactNumericVerifierCombineStateFrameRows,
    hslicesEnv, hdropEnv]

theorem compactNumericVerifierCombineStateFrameRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierCombineStateFrameRowsDef.val := by
  simp [compactNumericVerifierCombineStateFrameRowsDef]

structure CompactNumericVerifierCombineStateFrameRealization
    (tokenTable width tokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates) where
  proofTokens : List Nat
  certificateTokens : List Nat
  currentTasks : List CompactNumericVerifierTask
  currentValues : List CompactNumericChildResult
  nextTasks : List CompactNumericVerifierTask
  nextValues : List CompactNumericChildResult
  nextStatus : Option Bool
  task : CompactNumericVerifierTask
  currentLayout : CompactNumericVerifierStateDirectLayout
    tokenTable width tokenCount currentCoordinates.start
      currentCoordinates.finish
      (((proofTokens, certificateTokens),
        (currentTasks, currentValues)), none)
  nextLayout : CompactNumericVerifierStateDirectLayout
    tokenTable width tokenCount nextCoordinates.start
      nextCoordinates.finish
      (((proofTokens, certificateTokens),
        (nextTasks, nextValues)), nextStatus)
  taskLayout : CompactNumericVerifierTaskDirectLayout
    tokenTable width tokenCount taskCoordinates.start
      taskCoordinates.finish task
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
  currentValueGraph : CompactNumericChildResultListRowsGraph
    tokenTable width tokenCount currentCoordinates.valueBoundary
      currentValues.length currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
  nextValueGraph : CompactNumericChildResultListRowsGraph
    tokenTable width tokenCount nextCoordinates.valueBoundary
      nextValues.length currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
  currentValues_length : currentValues.length = currentCoordinates.valueCount
  nextValues_length : nextValues.length = nextCoordinates.valueCount
  taskStack_eq : currentTasks = task :: nextTasks
  taskTag_eq : task.1 = taskCoordinates.tag
  taskTag_ne_ten : task.1 ≠ 10
  nextStatusCase :
    (nextStatus = none ∧ nextCoordinates.statusTag = 0) ∨
      ∃ result : Bool,
        nextStatus = some result ∧
        nextCoordinates.statusTag = 1 ∧
        compactAdditiveBoolTag result = nextCoordinates.statusBool

theorem CompactNumericVerifierCombineStateFrameRows.realize
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
      nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound) :
    Nonempty (CompactNumericVerifierCombineStateFrameRealization
      tokenTable width tokenCount
      currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates) := by
  rcases hframe with
    ⟨hcurrentTag, htaskCount, htaskTagNe,
      hvalueTableWidth, hvalueValueBound,
      hstreamSlices, htaskDrop⟩
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
  have hcurrentProofFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hcurrentProofLayout
  have hnextProofFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hnextProofLayout
  have hcurrentCertificateFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hcurrentCertificateLayout
  have hnextCertificateFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hnextCertificateLayout
  rcases CompactFixedWidthTokenSlicesEq.natListPrefix_eq
      (offset := 0) hstreamSlices rfl rfl
      (by omega) (by omega) (by omega)
      hcurrentProofLayout hnextProofLayout with
    ⟨proofOffset, hcurrentProofAt, hnextProofAt, hproofEq⟩
  rcases CompactFixedWidthTokenSlicesEq.natListPrefix_eq
      (offset := proofOffset) hstreamSlices
      hcurrentProofAt hnextProofAt
      (by omega) (le_refl currentCoordinates.certificateFinish)
      (le_refl nextCoordinates.certificateFinish)
      hcurrentCertificateLayout hnextCertificateLayout with
    ⟨_certificateOffset, _hcurrentCertificateAt,
      _hnextCertificateAt, hcertificateEq⟩
  have hcurrentTasksNonempty : 0 < currentTasks.length := by
    omega
  rcases hhead.realize_actualHeadWithFields
      hcurrentTasksNonempty hcurrentTaskRows with
    ⟨task, htaskActual, htaskTag, htaskLayout,
      _hgammaRows, _hgammaLength,
      _hfirstLayout, _hfirstLength,
      _hsecondLayout, _hsecondLength,
      _hwitnessLayout, _hwitnessLength,
      _hsuffixLayout, _hsuffixLength⟩
  have htaskDrop' : CompactNumericVerifierTaskListDropRows
      tokenTable width tokenCount
      currentCoordinates.taskBoundary currentTasks.length
      nextCoordinates.taskBoundary nextTasks.length
      currentSizeWitness.taskTableWidth
      currentSizeWitness.taskValueBound 1 := by
    simpa [hcurrentTasksLength, hnextTasksLength] using htaskDrop
  have hnextTasksDrop : nextTasks = currentTasks.drop 1 :=
    htaskDrop'.eq_drop_of_rows hcurrentTaskRows hnextTaskRows
  have htaskStack : currentTasks = task :: nextTasks := by
    cases htasks : currentTasks with
    | nil => simp [htasks] at hcurrentTasksNonempty
    | cons head tail =>
        have htaskHead : task = head := by
          simpa [htasks] using htaskActual
        have hnextTail : nextTasks = tail := by
          simpa [htasks] using hnextTasksDrop
        simp [htaskHead, hnextTail]
  have hcurrentValueGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount currentCoordinates.valueBoundary
      currentValues.length currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa [hcurrentValuesLength] using
      hcurrent.2.2.2.2.2.2.2.1
  have hnextValueGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount nextCoordinates.valueBoundary
      nextValues.length currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa [hnextValuesLength, hvalueTableWidth, hvalueValueBound] using
      hnext.2.2.2.2.2.2.2.1
  have hcurrentLayout' : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount currentCoordinates.start
      currentCoordinates.finish
      (((currentProofTokens, currentCertificateTokens),
        (currentTasks, currentValues)), none) := by
    simpa [hcurrentStatusNone] using hcurrentLayout
  have hnextLayout' : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount nextCoordinates.start
      nextCoordinates.finish
      (((currentProofTokens, currentCertificateTokens),
        (nextTasks, nextValues)), nextStatus) := by
    simpa [hproofEq, hcertificateEq] using hnextLayout
  refine ⟨
    { proofTokens := currentProofTokens
      certificateTokens := currentCertificateTokens
      currentTasks := currentTasks
      currentValues := currentValues
      nextTasks := nextTasks
      nextValues := nextValues
      nextStatus := nextStatus
      task := task
      currentLayout := hcurrentLayout'
      nextLayout := hnextLayout'
      taskLayout := htaskLayout
      currentTaskRows := hcurrentTaskRows
      nextTaskRows := hnextTaskRows
      currentValueRows := hcurrentValueRows
      nextValueRows := hnextValueRows
      currentValueGraph := hcurrentValueGraph
      nextValueGraph := hnextValueGraph
      currentValues_length := hcurrentValuesLength
      nextValues_length := hnextValuesLength
      taskStack_eq := htaskStack
      taskTag_eq := htaskTag
      taskTag_ne_ten := by simpa [htaskTag] using htaskTagNe
      nextStatusCase := hnextStatus }⟩

#print axioms compactNumericVerifierCombineStateFrameRowsDef_spec
#print axioms compactNumericVerifierCombineStateFrameRowsDef_sigmaZero
#print axioms CompactNumericVerifierCombineStateFrameRows.realize

end FoundationCompactNumericListedDirectVerifierCombineStateFrameRows
