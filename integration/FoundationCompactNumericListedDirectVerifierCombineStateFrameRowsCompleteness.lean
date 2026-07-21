import integration.FoundationCompactNumericListedDirectVerifierCombineStateFrameRows
import integration.FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
import integration.FoundationCompactNumericListedDirectVerifierTaskSliceEquality

/-!
# Converse construction of the common verifier-combine frame

Two typed states with the same streams, a dropped task head, and canonical
state-core bounds determine the complete common combine frame.  The actual
head task and all five task-field layouts are recovered from row zero.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
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
open FoundationCompactNumericListedDirectVerifierTaskListDropRows
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRows
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness

def CompactNumericVerifierCombineCanonicalFramePackage
    (tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat)
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates)
    (currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates)
    (taskSizeWitness : CompactNumericVerifierTaskSizeWitness) : Prop :=
  CompactNumericVerifierStateCanonicalCorePackage
      tokenTable width tokenCount currentStart currentFinish
      (((proofTokens, certificateTokens), (task :: tasks, source)), none)
      currentCoordinates currentSizeWitness ∧
    CompactNumericVerifierStateCanonicalCorePackage
      tokenTable width tokenCount nextStart nextFinish
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
      nextCoordinates nextSizeWitness ∧
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
    task.1 = taskCoordinates.tag ∧
    CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount taskCoordinates.start
        taskCoordinates.finish task ∧
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        taskCoordinates.gammaBoundary task.2.1 ∧
    task.2.1.length = taskCoordinates.gammaCount ∧
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount taskCoordinates.gammaFinish
        taskCoordinates.firstFinish task.2.2.1 ∧
    task.2.2.1.length = taskCoordinates.firstCount ∧
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount taskCoordinates.firstFinish
        taskCoordinates.secondFinish task.2.2.2.1 ∧
    task.2.2.2.1.length = taskCoordinates.secondCount ∧
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount taskCoordinates.secondFinish
        taskCoordinates.witnessFinish task.2.2.2.2.1 ∧
    task.2.2.2.2.1.length = taskCoordinates.witnessCount ∧
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount taskCoordinates.witnessFinish
        taskCoordinates.finish task.2.2.2.2.2 ∧
    task.2.2.2.2.2.length = taskCoordinates.suffixCount

theorem CompactNumericVerifierCombineCanonicalFramePackage.exists_of_layouts
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {task : CompactNumericVerifierTask}
    {tasks : List CompactNumericVerifierTask}
    {source target : List CompactNumericChildResult}
    {nextStatus : Option Bool}
    (hcurrent : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount currentStart currentFinish
      (((proofTokens, certificateTokens), (task :: tasks, source)), none))
    (hnext : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount nextStart nextFinish
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus))
    (htaskNe : task.1 ≠ 10) :
    ∃ currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness,
      CompactNumericVerifierCombineCanonicalFramePackage
        tokenTable width tokenCount currentStart currentFinish
        nextStart nextFinish proofTokens certificateTokens task tasks
        source target nextStatus currentCoordinates nextCoordinates
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
      _hcurrentValueLayout, _hcurrentValueRows,
      hcurrentTaskCount, _hcurrentValueCount,
      hcurrentTaskTableWidth, hcurrentTaskValueBound,
      hcurrentValueTableWidth, hcurrentValueValueBound,
      hcurrentStatus, hcurrentCore⟩
  rcases hnextPackage with
    ⟨_hnextStart, _hnextFinish,
      hnextProof, hnextCertificate,
      _hnextTaskLayout, hnextTaskRows,
      _hnextValueLayout, _hnextValueRows,
      hnextTaskCount, _hnextValueCount,
      hnextTaskTableWidth, hnextTaskValueBound,
      hnextValueTableWidth, hnextValueValueBound,
      _hnextStatus, hnextCore⟩
  have hcurrentCoreSaved := hcurrentCore
  have hnextCoreSaved := hnextCore
  rcases hcurrentCore with
    ⟨_hcurrentProofSlice, _hcurrentCertificateSlice,
      _hcurrentTaskStructure, hcurrentTaskGraph,
      _hcurrentTaskBoundarySizeEq, _hcurrentTaskBoundarySize,
      _hcurrentValueStructure, _hcurrentValueGraph,
      _hcurrentValueBoundarySizeEq, _hcurrentValueBoundarySize,
      _hcurrentOption, _hcurrentCoreStatus⟩
  rcases hnextCore with
    ⟨_hnextProofSlice, _hnextCertificateSlice,
      _hnextTaskStructure, hnextTaskGraph,
      _hnextTaskBoundarySizeEq, _hnextTaskBoundarySize,
      _hnextValueStructure, _hnextValueGraph,
      _hnextValueBoundarySizeEq, _hnextValueBoundarySize,
      _hnextOption, _hnextCoreStatus⟩
  have hnonempty : 0 < currentCoordinates.taskCount := by
    rw [hcurrentTaskCount]
    simp
  have hrow : CompactNumericVerifierTaskBoundedRow
      tokenTable width tokenCount currentCoordinates.taskBoundary
        currentSizeWitness.taskValueBound 0 :=
    hcurrentTaskGraph.2 0 hnonempty
  rcases CompactNumericVerifierTaskBoundedRow.exists_boundedHead hrow with
    ⟨taskCoordinates, taskSizeWitness, hhead⟩
  have hlistNonempty : 0 < (task :: tasks).length := by simp
  rcases CompactNumericVerifierTaskBoundedHead.realize_actualHeadWithFields
      hhead hlistNonempty hcurrentTaskRows with
    ⟨actualTask, hactualTask, htaskTag, htaskLayout,
      hgammaRows, hgammaCount, hfirstLayout, hfirstCount,
      hsecondLayout, hsecondCount, hwitnessLayout, hwitnessCount,
      hsuffixLayout, hsuffixCount⟩
  have hactualTaskEq : actualTask = task := by
    simpa using hactualTask
  rw [hactualTaskEq] at htaskTag htaskLayout hgammaRows hgammaCount
  rw [hactualTaskEq] at hfirstLayout hfirstCount hsecondLayout hsecondCount
  rw [hactualTaskEq] at hwitnessLayout hwitnessCount hsuffixLayout hsuffixCount
  have hcurrentStatusTag : currentCoordinates.statusTag = 0 := by
    rcases hcurrentStatus with hnone | hsome
    · exact hnone.2.1
    · rcases hsome with ⟨result, hstatus, _htag, _hbool⟩
      simp at hstatus
  have htaskCoordinatesNe : taskCoordinates.tag ≠ 10 := by
    intro hten
    apply htaskNe
    rw [htaskTag, hten]
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
    CompactFixedWidthTokenSlicesEq.append
      hproofSlices hcertificateSlices
  have hcurrentTaskGraphTyped : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount currentCoordinates.taskBoundary
      (task :: tasks).length currentSizeWitness.taskTableWidth
      currentSizeWitness.taskValueBound := by
    simpa only [hcurrentTaskCount] using hcurrentTaskGraph
  have hnextTaskGraphTyped : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount nextCoordinates.taskBoundary
      tasks.length currentSizeWitness.taskTableWidth
      currentSizeWitness.taskValueBound := by
    simpa only [hnextTaskCount, hcurrentTaskTableWidth,
      hcurrentTaskValueBound, hnextTaskTableWidth,
      hnextTaskValueBound] using hnextTaskGraph
  have hdropTyped : CompactNumericVerifierTaskListDropRows
      tokenTable width tokenCount
      currentCoordinates.taskBoundary (task :: tasks).length
      nextCoordinates.taskBoundary tasks.length
      currentSizeWitness.taskTableWidth
      currentSizeWitness.taskValueBound 1 :=
    (compactNumericVerifierTaskListDropRows_iff_drop_of_rows
      hcurrentTaskRows hnextTaskRows hcurrentTaskGraphTyped
      hnextTaskGraphTyped).mpr ⟨by simp, by simp⟩
  have hdrop : CompactNumericVerifierTaskListDropRows
      tokenTable width tokenCount
      currentCoordinates.taskBoundary currentCoordinates.taskCount
      nextCoordinates.taskBoundary nextCoordinates.taskCount
      currentSizeWitness.taskTableWidth
      currentSizeWitness.taskValueBound 1 := by
    simpa only [hcurrentTaskCount, hnextTaskCount] using hdropTyped
  have hframe : CompactNumericVerifierCombineStateFrameRows
      tokenTable width tokenCount
      currentCoordinates.start currentCoordinates.certificateFinish
      currentCoordinates.taskBoundary currentCoordinates.taskCount
      currentSizeWitness.taskTableWidth currentSizeWitness.taskValueBound
      currentSizeWitness.valueTableWidth currentSizeWitness.valueValueBound
      currentCoordinates.statusTag taskCoordinates.tag
      nextCoordinates.start nextCoordinates.certificateFinish
      nextCoordinates.taskBoundary nextCoordinates.taskCount
      nextSizeWitness.valueTableWidth nextSizeWitness.valueValueBound := by
    refine ⟨hcurrentStatusTag, Nat.succ_le_iff.mpr hnonempty,
      htaskCoordinatesNe, ?_, ?_, hstreamSlices, hdrop⟩
    · exact hnextValueTableWidth.trans hcurrentValueTableWidth.symm
    · exact hnextValueValueBound.trans hcurrentValueValueBound.symm
  refine ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness, taskCoordinates, taskSizeWitness,
    hcurrentPackageSaved, hnextPackageSaved, hhead, hframe,
    htaskTag, htaskLayout, hgammaRows, hgammaCount,
    hfirstLayout, hfirstCount, hsecondLayout, hsecondCount,
    hwitnessLayout, hwitnessCount, hsuffixLayout, hsuffixCount⟩

#print axioms
  CompactNumericVerifierCombineCanonicalFramePackage.exists_of_layouts

end FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness
