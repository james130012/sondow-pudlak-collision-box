import integration.FoundationCompactNumericListedDirectVerifierParseStateFrameRows
import integration.FoundationCompactNumericListedDirectVerifierParseFailureRows
import integration.FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
import integration.FoundationCompactNumericListedDirectVerifierTaskSliceEquality

/-!
# Canonical converse frame for a failed parse step

Two typed states with identical proof/certificate streams, one dropped parse
task, an unchanged value stack, and failure status determine all common state
rows needed by the separated-table parse-failure graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseFailureCanonicalFrameCompleteness

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectNatListSliceEquality
open FoundationCompactNumericListedDirectNatListListSliceEquality
open FoundationCompactNumericListedDirectVerifierParseScheduleRows
open FoundationCompactNumericListedDirectVerifierParseStateFrameRows
open FoundationCompactNumericListedDirectVerifierTaskListDropRows
open FoundationCompactNumericListedDirectChildResultListDropRows
open FoundationCompactNumericListedDirectVerifierParseFailureRows
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness

def CompactNumericVerifierParseFailureCanonicalFramePackage
    (tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat)
    (proofTokens certificateTokens : List Nat)
    (currentTask : CompactNumericVerifierTask)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates)
    (taskSizeWitness : CompactNumericVerifierTaskSizeWitness) : Prop :=
  CompactNumericVerifierStateCanonicalCorePackage
      tokenTable width tokenCount currentStart currentFinish
      (((proofTokens, certificateTokens),
        (currentTask :: restTasks, values)), none)
      currentCoordinates currentSizeWitness ∧
    CompactNumericVerifierStateCanonicalCorePackage
      tokenTable width tokenCount nextStart nextFinish
      (((proofTokens, certificateTokens), (restTasks, values)), some false)
      nextCoordinates nextSizeWitness ∧
    CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount currentCoordinates.taskBoundary
      currentSizeWitness.taskValueBound taskCoordinates taskSizeWitness ∧
    CompactNumericVerifierParseStateFrameRows
      currentCoordinates.taskCount currentCoordinates.statusTag
      taskCoordinates ∧
    CompactNumericVerifierParseFailureRows
      tokenTable width tokenCount
      currentCoordinates.start currentCoordinates.certificateFinish
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

theorem CompactNumericVerifierParseFailureCanonicalFramePackage.exists_of_layouts
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {currentTask : CompactNumericVerifierTask}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hcurrent : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount currentStart currentFinish
      (((proofTokens, certificateTokens),
        (currentTask :: restTasks, values)), none))
    (hnext : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount nextStart nextFinish
      (((proofTokens, certificateTokens), (restTasks, values)), some false))
    (hcurrentTaskTag : currentTask.1 = 10) :
    ∃ currentCoordinates nextCoordinates :
          CompactNumericVerifierStateRowCoordinates,
      ∃ currentSizeWitness nextSizeWitness :
          CompactNumericVerifierStateSizeWitness,
      ∃ taskCoordinates : CompactNumericVerifierTaskRowCoordinates,
      ∃ taskSizeWitness : CompactNumericVerifierTaskSizeWitness,
      CompactNumericVerifierParseFailureCanonicalFramePackage
        tokenTable width tokenCount currentStart currentFinish
        nextStart nextFinish proofTokens certificateTokens currentTask restTasks values
        currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness := by
  rcases CompactNumericVerifierStateDirectLayout.toCanonicalCorePackage
      hcurrent with
    ⟨currentCoordinates, currentSizeWitness, hcurrentPackage⟩
  rcases CompactNumericVerifierStateDirectLayout.toCanonicalCorePackage
      hnext with
    ⟨nextCoordinates, nextSizeWitness, hnextPackage⟩
  have hcurrentPackageSaved := hcurrentPackage
  have hnextPackageSaved := hnextPackage
  rcases hcurrentPackage with
    ⟨_hcurrentStart, _hcurrentFinish,
      hcurrentProof, hcurrentCertificate,
      _hcurrentTaskLayout, hcurrentTaskRows,
      _hcurrentValueLayout, hcurrentValueRows,
      hcurrentTaskCount, hcurrentValueCount,
      hcurrentTaskTableWidth, hcurrentTaskValueBound,
      hcurrentValueTableWidth, hcurrentValueValueBound,
      hcurrentStatus, hcurrentCore⟩
  rcases hnextPackage with
    ⟨_hnextStart, _hnextFinish,
      hnextProof, hnextCertificate,
      _hnextTaskLayout, hnextTaskRows,
      _hnextValueLayout, hnextValueRows,
      hnextTaskCount, hnextValueCount,
      hnextTaskTableWidth, hnextTaskValueBound,
      hnextValueTableWidth, hnextValueValueBound,
      hnextStatus, hnextCore⟩
  have hcurrentCoreSaved := hcurrentCore
  have hnextCoreSaved := hnextCore
  rcases hcurrentCore with
    ⟨_hcurrentProofSlice, _hcurrentCertificateSlice,
      _hcurrentTaskStructure, hcurrentTaskGraph,
      _hcurrentTaskBoundarySizeEq, _hcurrentTaskBoundarySize,
      _hcurrentValueStructure, hcurrentValueGraph,
      _hcurrentValueBoundarySizeEq, _hcurrentValueBoundarySize,
      _hcurrentOption, _hcurrentCoreStatus⟩
  rcases hnextCore with
    ⟨_hnextProofSlice, _hnextCertificateSlice,
      _hnextTaskStructure, hnextTaskGraph,
      _hnextTaskBoundarySizeEq, _hnextTaskBoundarySize,
      _hnextValueStructure, hnextValueGraph,
      _hnextValueBoundarySizeEq, _hnextValueBoundarySize,
      _hnextOption, _hnextCoreStatus⟩
  have htaskNonempty : 0 < (currentTask :: restTasks).length := by
    simp
  have hcurrentTaskGraphTyped : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount currentCoordinates.taskBoundary
      (currentTask :: restTasks).length
      currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound := by
    simpa only [hcurrentTaskCount] using hcurrentTaskGraph
  have hrow : CompactNumericVerifierTaskBoundedRow
      tokenTable width tokenCount currentCoordinates.taskBoundary
      currentSizeWitness.taskValueBound 0 :=
    hcurrentTaskGraphTyped.2 0 htaskNonempty
  rcases CompactNumericVerifierTaskBoundedRow.exists_boundedHead hrow with
    ⟨taskCoordinates, taskSizeWitness, hhead⟩
  rcases hhead.realize_actualHeadWithFields htaskNonempty hcurrentTaskRows with
    ⟨actualTask, hactualTask, htaskTag, _htaskLayout,
      _hgammaRows, hgammaCount,
      _hfirstLayout, hfirstCount,
      _hsecondLayout, hsecondCount,
      _hwitnessLayout, hwitnessCount,
      _hsuffixLayout, hsuffixCount⟩
  have hactualTaskEq : actualTask = currentTask := by
    simpa using hactualTask
  rw [hactualTaskEq] at htaskTag
  have hparseTag : taskCoordinates.tag = 10 :=
    htaskTag.symm.trans hcurrentTaskTag
  have hcurrentStatusTag : currentCoordinates.statusTag = 0 :=
    hcurrentPackageSaved.statusTag_eq_zero rfl
  have hnextStatusTagBool : nextCoordinates.statusTag = 1 ∧
      nextCoordinates.statusBool = compactAdditiveBoolTag false :=
    hnextPackageSaved.statusTagBool_eq_some rfl
  have hframe : CompactNumericVerifierParseStateFrameRows
      currentCoordinates.taskCount currentCoordinates.statusTag
      taskCoordinates := by
    refine ⟨hcurrentStatusTag, ?_, hparseTag⟩
    rw [hcurrentTaskCount]
    simp
  have hproofSlices : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
      currentCoordinates.start currentCoordinates.proofFinish
      nextCoordinates.start nextCoordinates.proofFinish :=
    CompactAdditiveNatListDirectLayout.slicesEq_of_eq
      hcurrentProof hnextProof rfl
  have hcertificateSlices : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
      currentCoordinates.proofFinish currentCoordinates.certificateFinish
      nextCoordinates.proofFinish nextCoordinates.certificateFinish :=
    CompactAdditiveNatListDirectLayout.slicesEq_of_eq
      hcurrentCertificate hnextCertificate rfl
  have hstreamSlices : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
      currentCoordinates.start currentCoordinates.certificateFinish
      nextCoordinates.start nextCoordinates.certificateFinish :=
    CompactFixedWidthTokenSlicesEq.append hproofSlices hcertificateSlices
  have hnextTaskGraphTyped : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount nextCoordinates.taskBoundary
      restTasks.length currentSizeWitness.taskTableWidth
      currentSizeWitness.taskValueBound := by
    simpa only [hnextTaskCount, hcurrentTaskTableWidth,
      hcurrentTaskValueBound, hnextTaskTableWidth,
      hnextTaskValueBound] using hnextTaskGraph
  have htaskDropTyped : CompactNumericVerifierTaskListDropRows
      tokenTable width tokenCount
      currentCoordinates.taskBoundary
        (currentTask :: restTasks).length
      nextCoordinates.taskBoundary restTasks.length
      currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound 1 :=
    (compactNumericVerifierTaskListDropRows_iff_drop_of_rows
      hcurrentTaskRows hnextTaskRows hcurrentTaskGraphTyped
      hnextTaskGraphTyped).mpr ⟨by simp, by simp⟩
  have htaskDrop : CompactNumericVerifierTaskListDropRows
      tokenTable width tokenCount
      currentCoordinates.taskBoundary currentCoordinates.taskCount
      nextCoordinates.taskBoundary nextCoordinates.taskCount
      currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound 1 := by
    simpa only [hcurrentTaskCount, hnextTaskCount] using htaskDropTyped
  have hcurrentValueGraphTyped : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount currentCoordinates.valueBoundary
      values.length currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueCount] using hcurrentValueGraph
  have hnextValueGraphTyped : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount nextCoordinates.valueBoundary
      values.length currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hnextValueCount, hcurrentValueTableWidth,
      hcurrentValueValueBound, hnextValueTableWidth,
      hnextValueValueBound] using hnextValueGraph
  have hvalueDropTyped : CompactNumericChildResultListDropRows
      tokenTable width tokenCount
      currentCoordinates.valueBoundary values.length
      nextCoordinates.valueBoundary values.length
      currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound 0 :=
    (compactNumericChildResultListDropRows_iff_drop_of_rows
      hcurrentValueRows hnextValueRows hcurrentValueGraphTyped
      hnextValueGraphTyped).mpr ⟨by simp, by simp⟩
  have hvalueDrop : CompactNumericChildResultListDropRows
      tokenTable width tokenCount
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound 0 := by
    simpa only [hcurrentValueCount, hnextValueCount] using hvalueDropTyped
  have hfailureRows : CompactNumericVerifierParseFailureRows
      tokenTable width tokenCount
      currentCoordinates.start currentCoordinates.certificateFinish
      currentCoordinates.taskBoundary currentCoordinates.taskCount
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
      currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
      nextCoordinates.start nextCoordinates.certificateFinish
      nextCoordinates.taskBoundary nextCoordinates.taskCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      nextSizeWitness.taskTableWidth nextSizeWitness.taskValueBound
      nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound
      nextCoordinates.statusTag nextCoordinates.statusBool := by
    refine ⟨hnextTaskTableWidth.trans hcurrentTaskTableWidth.symm,
      hnextTaskValueBound.trans hcurrentTaskValueBound.symm,
      hnextValueTableWidth.trans hcurrentValueTableWidth.symm,
      hnextValueValueBound.trans hcurrentValueValueBound.symm,
      hstreamSlices, htaskDrop, hvalueDrop, hnextStatusTagBool.1, ?_⟩
    simpa [compactAdditiveBoolTag] using hnextStatusTagBool.2
  refine ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness, taskCoordinates, taskSizeWitness, ?_⟩
  exact ⟨hcurrentPackageSaved, hnextPackageSaved,
    hhead, hframe, hfailureRows⟩

#print axioms
  CompactNumericVerifierParseFailureCanonicalFramePackage.exists_of_layouts

end FoundationCompactNumericListedDirectVerifierParseFailureCanonicalFrameCompleteness
