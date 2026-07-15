import integration.FoundationCompactNumericListedDirectVerifierParseStateFrameRows
import integration.FoundationCompactNumericListedDirectVerifierStateCoreCompleteness

/-!
# Canonical common frame for a successful verifier parse step

Typed current and next states with running status determine the two state cores,
the actual parse-task head, and the common parse-state frame.  Branch-specific
parser and transition graphs are deliberately left outside this package.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseSuccessCanonicalFrameCompleteness

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierParseScheduleRows
open FoundationCompactNumericListedDirectVerifierParseStateFrameRows
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness

def CompactNumericVerifierParseSuccessCanonicalFramePackage
    (tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat)
    (proofTokens certificateTokens : List Nat)
    (currentTask : CompactNumericVerifierTask)
    (restTasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (nextProofTokens nextCertificateTokens : List Nat)
    (nextTasks : List CompactNumericVerifierTask)
    (nextValues : List CompactNumericChildResult)
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
      (((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues)), none)
      nextCoordinates nextSizeWitness ∧
    CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount currentCoordinates.taskBoundary
      currentSizeWitness.taskValueBound taskCoordinates taskSizeWitness ∧
    CompactNumericVerifierParseStateFrameRows
      currentCoordinates.taskCount currentCoordinates.statusTag
      taskCoordinates

theorem CompactNumericVerifierParseSuccessCanonicalFramePackage.exists_of_layouts
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {currentTask : CompactNumericVerifierTask}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    {nextProofTokens nextCertificateTokens : List Nat}
    {nextTasks : List CompactNumericVerifierTask}
    {nextValues : List CompactNumericChildResult}
    (hcurrent : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount currentStart currentFinish
      (((proofTokens, certificateTokens),
        (currentTask :: restTasks, values)), none))
    (hnext : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount nextStart nextFinish
      (((nextProofTokens, nextCertificateTokens),
        (nextTasks, nextValues)), none)) :
    currentTask.1 = 10 →
    ∃ currentCoordinates nextCoordinates :
        CompactNumericVerifierStateRowCoordinates,
    ∃ currentSizeWitness nextSizeWitness :
        CompactNumericVerifierStateSizeWitness,
    ∃ taskCoordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ taskSizeWitness : CompactNumericVerifierTaskSizeWitness,
      CompactNumericVerifierParseSuccessCanonicalFramePackage
        tokenTable width tokenCount currentStart currentFinish
        nextStart nextFinish proofTokens certificateTokens currentTask restTasks values
        nextProofTokens nextCertificateTokens nextTasks nextValues
        currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
        taskCoordinates taskSizeWitness := by
  intro hcurrentTaskTag
  rcases CompactNumericVerifierStateDirectLayout.toCanonicalCorePackage
      hcurrent with
    ⟨currentCoordinates, currentSizeWitness, hcurrentPackage⟩
  rcases CompactNumericVerifierStateDirectLayout.toCanonicalCorePackage
      hnext with
    ⟨nextCoordinates, nextSizeWitness, hnextPackage⟩
  have hcurrentPackageSaved := hcurrentPackage
  rcases hcurrentPackage with
    ⟨_hcurrentStart, _hcurrentFinish,
      _hcurrentProof, _hcurrentCertificate,
      _hcurrentTaskLayout, hcurrentTaskRows,
      _hcurrentValueLayout, _hcurrentValueRows,
      hcurrentTaskCount, _hcurrentValueCount,
      _hcurrentTaskTableWidth, _hcurrentTaskValueBound,
      _hcurrentValueTableWidth, _hcurrentValueValueBound,
      _hcurrentStatus, hcurrentCore⟩
  rcases hcurrentCore with
    ⟨_hcurrentProofSlice, _hcurrentCertificateSlice,
      _hcurrentTaskStructure, hcurrentTaskGraph,
      _hcurrentTaskBoundarySizeEq, _hcurrentTaskBoundarySize,
      _hcurrentValueStructure, _hcurrentValueGraph,
      _hcurrentValueBoundarySizeEq, _hcurrentValueBoundarySize,
      _hcurrentOption, _hcurrentCoreStatus⟩
  have htaskNonempty :
      0 < (currentTask :: restTasks).length := by
    simp
  have hcurrentTaskGraphTyped : CompactNumericVerifierTaskListRowsGraph
      tokenTable width tokenCount currentCoordinates.taskBoundary
      (currentTask :: restTasks).length
      currentSizeWitness.taskTableWidth
      currentSizeWitness.taskValueBound := by
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
  have hframe : CompactNumericVerifierParseStateFrameRows
      currentCoordinates.taskCount currentCoordinates.statusTag
      taskCoordinates := by
    refine ⟨hcurrentStatusTag, ?_, hparseTag⟩
    rw [hcurrentTaskCount]
    simp
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness,
    taskCoordinates, taskSizeWitness,
    hcurrentPackageSaved, hnextPackage, hhead, hframe⟩

#print axioms
  CompactNumericVerifierParseSuccessCanonicalFramePackage.exists_of_layouts

end FoundationCompactNumericListedDirectVerifierParseSuccessCanonicalFrameCompleteness
