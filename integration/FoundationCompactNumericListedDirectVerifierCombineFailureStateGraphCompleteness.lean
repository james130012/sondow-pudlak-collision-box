import integration.FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness

/-!
# Full 93-column converse constructor for failed combine steps

When the public combine transition returns `none`, the running step has already
dropped the task head, preserves the complete child-result stack, and stores
`some false`.  The canonical state layouts determine every corresponding fixed
column directly.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineFailureStateGraphCompleteness

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierCombineFailureRows
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineStateGraph
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness

theorem CompactNumericVerifierCombineStateGraph.exists_of_failure_frame
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {task : CompactNumericVerifierTask}
    {tasks : List CompactNumericVerifierTask}
    {source : List CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens task tasks
      source source (some false) currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (htransition : compactNumericCombineTransition task source = none) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness := by
  have hframeSaved := hframePackage
  rcases hframePackage with
    ⟨hcurrentPackage, hnextPackage, _hhead, _hframe,
      htaskTag, _htaskLayout, _hfields⟩
  have hnextPackageSaved := hnextPackage
  rcases hcurrentPackage with
    ⟨_hcurrentStart, _hcurrentFinish,
      _hcurrentProof, _hcurrentCertificate,
      _hcurrentTaskLayout, _hcurrentTaskRows,
      _hcurrentValueLayout, hsourceRows,
      _hcurrentTaskCount, hsourceCount,
      _hcurrentTaskTableWidth, _hcurrentTaskValueBound,
      hcurrentValueTableWidth, hcurrentValueValueBound,
      _hcurrentStatus, _hcurrentCore⟩
  rcases hnextPackage with
    ⟨_hnextStart, _hnextFinish,
      _hnextProof, _hnextCertificate,
      _hnextTaskLayout, _hnextTaskRows,
      _hnextValueLayout, htargetRows,
      _hnextTaskCount, htargetCount,
      _hnextTaskTableWidth, _hnextTaskValueBound,
      _hnextValueTableWidth, _hnextValueValueBound,
      _hnextStatus, _hnextCore⟩
  have hsourceGraphCanonical :=
    CompactAdditiveStructuredListElementRowLayouts.childResultListRowsGraph
      hsourceRows
  have hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount currentCoordinates.valueBoundary source.length
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueTableWidth,
      hcurrentValueValueBound] using hsourceGraphCanonical
  have htargetGraphCanonical :=
    CompactAdditiveStructuredListElementRowLayouts.childResultListRowsGraph
      htargetRows
  have htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount nextCoordinates.valueBoundary source.length
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueTableWidth,
      hcurrentValueValueBound] using htargetGraphCanonical
  have hnextStatus :=
    CompactNumericVerifierStateCanonicalCorePackage.statusTagBool_eq_some
      hnextPackageSaved (result := false) rfl
  have hnextStatusTag : nextCoordinates.statusTag = 1 := hnextStatus.1
  have hnextStatusBool : nextCoordinates.statusBool =
      compactAdditiveBoolTag false := hnextStatus.2
  have hnextStatusBoolZero : nextCoordinates.statusBool = 0 := by
    simpa [compactAdditiveBoolTag] using hnextStatusBool
  have hlocal := CompactNumericVerifierCombineFailureRows.of_transition_none
    hsourceRows htargetRows hsourceGraph htargetGraph htaskTag
    htransition rfl hnextStatusTag hnextStatusBool
  have hlocalAligned : CompactNumericVerifierCombineFailureRows
      tokenTable width tokenCount taskCoordinates.tag
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound 1 0 := by
    simpa only [hsourceCount, htargetCount, hnextStatusTag,
      hnextStatusBoolZero] using hlocal
  exact CompactNumericVerifierCombineStateGraph.exists_of_failure_rows
    hframeSaved hlocalAligned

#print axioms CompactNumericVerifierCombineStateGraph.exists_of_failure_frame

end FoundationCompactNumericListedDirectVerifierCombineFailureStateGraphCompleteness
