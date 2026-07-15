import integration.FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness

/-!
# Full 93-column converse constructors for simple combine rules

The conjunction, disjunction, and weakening branches use only the canonical
state frame, the real task fields, and real child-result rows already present
in the two state layouts.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineSimpleStateGraphCompleteness

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness
open FoundationCompactNumericListedDirectSimpleCombineTransitionRows
open FoundationCompactNumericListedDirectSimpleCombineTransitionRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateGraph
open FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness

theorem CompactNumericVerifierCombineStateGraph.exists_of_and_frame
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {Gamma : List (List Nat)}
    {firstFormula secondFormula witness suffix : List Nat}
    {tasks : List CompactNumericVerifierTask}
    {rightConclusion leftConclusion : List (List Nat)}
    {rightValid leftValid : Bool}
    {tail : List CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens
      (3, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks
      ((rightConclusion, rightValid) ::
        (leftConclusion, leftValid) :: tail)
      ((Gamma, compactAndRuleCheck
        (Gamma, firstFormula, secondFormula,
          (leftConclusion, leftValid), rightConclusion, rightValid)) :: tail)
      none currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness := by
  have hframeSaved := hframePackage
  rcases hframePackage with
    ⟨hcurrentPackage, hnextPackage, _hhead, _hframe,
      htaskTag, _htaskLayout, hGammaRows, hGammaCount,
      hfirstLayout, hfirstCount, hsecondLayout, hsecondCount,
      _hwitnessLayout, _hwitnessCount, _hsuffixLayout, _hsuffixCount⟩
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
      tokenTable width tokenCount currentCoordinates.valueBoundary
      ((rightConclusion, rightValid) ::
        (leftConclusion, leftValid) :: tail).length
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueTableWidth,
      hcurrentValueValueBound] using hsourceGraphCanonical
  have htargetGraphCanonical :=
    CompactAdditiveStructuredListElementRowLayouts.childResultListRowsGraph
      htargetRows
  have htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount nextCoordinates.valueBoundary
      ((Gamma, compactAndRuleCheck
        (Gamma, firstFormula, secondFormula,
          (leftConclusion, leftValid), rightConclusion, rightValid)) ::
        tail).length currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueTableWidth,
      hcurrentValueValueBound] using htargetGraphCanonical
  rcases CompactAdditiveStructuredListElementRowLayouts.childResult_components_at
      hsourceRows 0 (by simp) with
    ⟨rightGammaBoundary, rightBoolValue,
      hrightRowsRaw, hrightBoolRaw⟩
  rcases CompactAdditiveStructuredListElementRowLayouts.childResult_components_at
      hsourceRows 1 (by simp) with
    ⟨leftGammaBoundary, leftBoolValue,
      hleftRowsRaw, hleftBoolRaw⟩
  have hrightRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      rightGammaBoundary rightConclusion := by
    simpa using hrightRowsRaw
  have hleftRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      leftGammaBoundary leftConclusion := by
    simpa using hleftRowsRaw
  have hrightBool : rightBoolValue = compactAdditiveBoolTag rightValid := by
    simpa using hrightBoolRaw
  have hleftBool : leftBoolValue = compactAdditiveBoolTag leftValid := by
    simpa using hleftBoolRaw
  have htag : taskCoordinates.tag = 3 := by
    simpa using htaskTag.symm
  have hlocal := CompactNumericSimpleCombineTransitionRows.of_and
    hGammaRows hfirstLayout hsecondLayout hrightRows hleftRows
    hrightBool hleftBool hsourceRows htargetRows
    hsourceGraph htargetGraph htag (by simp) (by simp) (by simp) (by simp)
  have hlocalAligned : CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      rightConclusion.length rightGammaBoundary rightBoolValue
      leftConclusion.length leftGammaBoundary leftBoolValue
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      (compactAdditiveBoolTag
        (compactAndRuleCheck
          (Gamma, firstFormula, secondFormula,
            (leftConclusion, leftValid), rightConclusion, rightValid))) := by
    simpa only [hGammaCount, hfirstCount, hsecondCount,
      hsourceCount, htargetCount] using hlocal
  exact CompactNumericVerifierCombineStateGraph.exists_of_simple_rows
    hframeSaved hlocalAligned

theorem CompactNumericVerifierCombineStateGraph.exists_of_or_frame
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {Gamma : List (List Nat)}
    {firstFormula secondFormula witness suffix : List Nat}
    {tasks : List CompactNumericVerifierTask}
    {rightConclusion : List (List Nat)}
    {rightValid : Bool}
    {tail : List CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens
      (4, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactOrRuleCheck
        (Gamma, firstFormula, secondFormula,
          rightConclusion, rightValid)) :: tail)
      none currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness := by
  have hframeSaved := hframePackage
  rcases hframePackage with
    ⟨hcurrentPackage, hnextPackage, _hhead, _hframe,
      htaskTag, _htaskLayout, hGammaRows, hGammaCount,
      hfirstLayout, hfirstCount, hsecondLayout, hsecondCount,
      _hwitnessLayout, _hwitnessCount, _hsuffixLayout, _hsuffixCount⟩
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
      tokenTable width tokenCount currentCoordinates.valueBoundary
      ((rightConclusion, rightValid) :: tail).length
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueTableWidth,
      hcurrentValueValueBound] using hsourceGraphCanonical
  have htargetGraphCanonical :=
    CompactAdditiveStructuredListElementRowLayouts.childResultListRowsGraph
      htargetRows
  have htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount nextCoordinates.valueBoundary
      ((Gamma, compactOrRuleCheck
        (Gamma, firstFormula, secondFormula,
          rightConclusion, rightValid)) :: tail).length
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueTableWidth,
      hcurrentValueValueBound] using htargetGraphCanonical
  rcases CompactAdditiveStructuredListElementRowLayouts.childResult_components_at
      hsourceRows 0 (by simp) with
    ⟨rightGammaBoundary, rightBoolValue,
      hrightRowsRaw, hrightBoolRaw⟩
  have hrightRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      rightGammaBoundary rightConclusion := by
    simpa using hrightRowsRaw
  have hrightBool : rightBoolValue = compactAdditiveBoolTag rightValid := by
    simpa using hrightBoolRaw
  have htag : taskCoordinates.tag = 4 := by
    simpa using htaskTag.symm
  have hlocal := CompactNumericSimpleCombineTransitionRows.of_or
    (leftGammaCount := 0) (leftGammaBoundary := 0) (leftBoolValue := 0)
    hGammaRows hfirstLayout hsecondLayout hrightRows hrightBool
    hsourceRows htargetRows hsourceGraph htargetGraph htag
    (by simp) (by simp) (by simp)
  have hlocalAligned : CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      rightConclusion.length rightGammaBoundary rightBoolValue
      0 0 0
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      (compactAdditiveBoolTag
        (compactOrRuleCheck
          (Gamma, firstFormula, secondFormula,
            rightConclusion, rightValid))) := by
    simpa only [hGammaCount, hfirstCount, hsecondCount,
      hsourceCount, htargetCount] using hlocal
  exact CompactNumericVerifierCombineStateGraph.exists_of_simple_rows
    hframeSaved hlocalAligned

theorem CompactNumericVerifierCombineStateGraph.exists_of_wk_frame
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {Gamma : List (List Nat)}
    {firstFormula secondFormula witness suffix : List Nat}
    {tasks : List CompactNumericVerifierTask}
    {rightConclusion : List (List Nat)}
    {rightValid : Bool}
    {tail : List CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens
      (7, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactWkRuleCheck
        (Gamma, rightConclusion, rightValid)) :: tail)
      none currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness := by
  have hframeSaved := hframePackage
  rcases hframePackage with
    ⟨hcurrentPackage, hnextPackage, _hhead, _hframe,
      htaskTag, _htaskLayout, hGammaRows, hGammaCount,
      _hfirstLayout, _hfirstCount, _hsecondLayout, _hsecondCount,
      _hwitnessLayout, _hwitnessCount, _hsuffixLayout, _hsuffixCount⟩
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
      tokenTable width tokenCount currentCoordinates.valueBoundary
      ((rightConclusion, rightValid) :: tail).length
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueTableWidth,
      hcurrentValueValueBound] using hsourceGraphCanonical
  have htargetGraphCanonical :=
    CompactAdditiveStructuredListElementRowLayouts.childResultListRowsGraph
      htargetRows
  have htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount nextCoordinates.valueBoundary
      ((Gamma, compactWkRuleCheck
        (Gamma, rightConclusion, rightValid)) :: tail).length
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueTableWidth,
      hcurrentValueValueBound] using htargetGraphCanonical
  rcases CompactAdditiveStructuredListElementRowLayouts.childResult_components_at
      hsourceRows 0 (by simp) with
    ⟨rightGammaBoundary, rightBoolValue,
      hrightRowsRaw, hrightBoolRaw⟩
  have hrightRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      rightGammaBoundary rightConclusion := by
    simpa using hrightRowsRaw
  have hrightBool : rightBoolValue = compactAdditiveBoolTag rightValid := by
    simpa using hrightBoolRaw
  have htag : taskCoordinates.tag = 7 := by
    simpa using htaskTag.symm
  have hlocal := CompactNumericSimpleCombineTransitionRows.of_wk
    (gammaFinish := taskCoordinates.gammaFinish)
    (firstFinish := taskCoordinates.firstFinish)
    (firstCount := taskCoordinates.firstCount)
    (secondFinish := taskCoordinates.secondFinish)
    (secondCount := taskCoordinates.secondCount)
    (leftGammaCount := 0) (leftGammaBoundary := 0) (leftBoolValue := 0)
    hGammaRows hrightRows hrightBool hsourceRows htargetRows
    hsourceGraph htargetGraph htag (by simp) (by simp) (by simp)
  have hlocalAligned : CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.secondCount
      rightConclusion.length rightGammaBoundary rightBoolValue
      0 0 0
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      (compactAdditiveBoolTag
        (compactWkRuleCheck (Gamma, rightConclusion, rightValid))) := by
    simpa only [hGammaCount, hsourceCount, htargetCount] using hlocal
  exact CompactNumericVerifierCombineStateGraph.exists_of_simple_rows
    hframeSaved hlocalAligned

#print axioms CompactNumericVerifierCombineStateGraph.exists_of_and_frame
#print axioms CompactNumericVerifierCombineStateGraph.exists_of_or_frame
#print axioms CompactNumericVerifierCombineStateGraph.exists_of_wk_frame

end FoundationCompactNumericListedDirectVerifierCombineSimpleStateGraphCompleteness
