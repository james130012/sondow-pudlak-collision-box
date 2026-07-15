import integration.FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness

/-!
# Full 93-column converse constructors for existential and cut combine rules

The constructors recover the real child-result rows from the current state,
construct the exact substitution or negation graph, and lift the checked local
rows through the common state frame to the fixed 93-column graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineExsCutStateGraphCompleteness

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectExsCutCombineRuleRows
open FoundationCompactNumericListedDirectExsCutCombineRuleRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineStateGraph
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness

theorem CompactNumericVerifierCombineStateGraph.exists_of_exs_frame
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {Gamma : List (List Nat)}
    {formula secondFormula witness suffix : List Nat}
    {tasks : List CompactNumericVerifierTask}
    {rightConclusion : List (List Nat)} {rightValid : Bool}
    {tail : List CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {transformedStart transformedFinish transformStateBoundary
      emptyStart emptyFinish : Nat}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens
      (6, (Gamma, (formula, (secondFormula, (witness, suffix)))))
      tasks ((rightConclusion, rightValid) :: tail)
      ((Gamma, compactExsRuleCheck
        (Gamma, formula, witness, rightConclusion, rightValid)) :: tail)
      none currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (htransformed : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount transformedStart transformedFinish
        ((compactFormulaSubstitutionExact 1 (witness, formula)).getD []))
    (hempty : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount emptyStart emptyFinish [])
    (htraceRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount transformStateBoundary
        (compactFormulaTransformStateTrace (2, witness)
          (compactSyntaxRunFuelBound formula)
          (compactFormulaTransformInitialState 1 formula))) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness := by
  have hframeSaved := hframePackage
  rcases hframePackage with
    ⟨hcurrentPackage, hnextPackage, _hhead, _hframe,
      htaskTag, _htaskLayout, hGammaRows, hGammaCount,
      hformulaLayout, hformulaCount, _hsecondLayout, _hsecondCount,
      hwitnessLayout, hwitnessCount, _hsuffixLayout, _hsuffixCount⟩
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
      ((Gamma, compactExsRuleCheck
        (Gamma, formula, witness, rightConclusion, rightValid)) :: tail).length
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
  have htag : taskCoordinates.tag = 6 := by
    simpa using htaskTag.symm
  rcases CompactNumericExsCutCombineRuleRows.exists_of_exs
      hGammaRows hformulaLayout hwitnessLayout htransformed hempty htraceRows
      hrightRows hrightBool hsourceRows htargetRows hsourceGraph htargetGraph
      htag (by simp) (by simp) (by simp) with
    ⟨formulaBoundary, formulaBoundarySize,
      transformedBoundary, transformedBoundarySize,
      emptyBoundary, emptyBoundarySize, transformTableWidth, hlocal⟩
  have hlocalAligned : CompactNumericExsCutCombineRuleRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.witnessFinish
        taskCoordinates.witnessCount
      rightConclusion.length rightGammaBoundary rightBoolValue
      0 0 0
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
        ((compactFormulaSubstitutionExact 1
          (witness, formula)).getD []).length transformedBoundarySize
      transformStateBoundary (compactSyntaxRunFuelBound formula + 1)
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth (2 ^ transformTableWidth)
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      (compactAdditiveBoolTag
        (compactExsRuleCheck
          (Gamma, formula, witness, rightConclusion, rightValid))) := by
    simpa only [hGammaCount, hformulaCount, hwitnessCount,
      hsourceCount, htargetCount] using hlocal
  exact CompactNumericVerifierCombineStateGraph.exists_of_exs_cut_rows
    hframeSaved hlocalAligned

theorem CompactNumericVerifierCombineStateGraph.exists_of_cut_frame
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {Gamma : List (List Nat)}
    {formula secondFormula witness suffix : List Nat}
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
    {transformedStart transformedFinish transformStateBoundary
      emptyStart emptyFinish : Nat}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens
      (9, (Gamma, (formula, (secondFormula, (witness, suffix)))))
      tasks
      ((rightConclusion, rightValid) :: (leftConclusion, leftValid) :: tail)
      ((Gamma, compactCutRuleCheck
        (Gamma, formula, (leftConclusion, leftValid),
          rightConclusion, rightValid)) :: tail)
      none currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (hnegated : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount transformedStart transformedFinish
        ((compactFormulaNegationExact 0 formula).getD []))
    (hempty : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount emptyStart emptyFinish [])
    (htraceRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount transformStateBoundary
        (compactFormulaTransformStateTrace (3, [])
          (compactSyntaxRunFuelBound formula)
          (compactFormulaTransformInitialState 0 formula))) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness := by
  have hframeSaved := hframePackage
  rcases hframePackage with
    ⟨hcurrentPackage, hnextPackage, _hhead, _hframe,
      htaskTag, _htaskLayout, hGammaRows, hGammaCount,
      hformulaLayout, hformulaCount, _hsecondLayout, _hsecondCount,
      _hwitnessLayout, hwitnessCount, _hsuffixLayout, _hsuffixCount⟩
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
      ((Gamma, compactCutRuleCheck
        (Gamma, formula, (leftConclusion, leftValid),
          rightConclusion, rightValid)) :: tail).length
      currentSizeWitness.valueTableWidth
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
  have htag : taskCoordinates.tag = 9 := by
    simpa using htaskTag.symm
  rcases CompactNumericExsCutCombineRuleRows.exists_of_cut
      (secondFinish := taskCoordinates.secondFinish)
      (witnessFinish := taskCoordinates.witnessFinish)
      (witness := witness)
      hGammaRows hformulaLayout hnegated hempty htraceRows
      hrightRows hleftRows hrightBool hleftBool hsourceRows htargetRows
      hsourceGraph htargetGraph htag (by simp) (by simp) (by simp) (by simp) with
    ⟨formulaBoundary, formulaBoundarySize,
      transformedBoundary, transformedBoundarySize,
      emptyBoundary, emptyBoundarySize, transformTableWidth, hlocal⟩
  have hlocalAligned : CompactNumericExsCutCombineRuleRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
        taskCoordinates.secondFinish taskCoordinates.witnessFinish
        taskCoordinates.witnessCount
      rightConclusion.length rightGammaBoundary rightBoolValue
      leftConclusion.length leftGammaBoundary leftBoolValue
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      formulaBoundary formulaBoundarySize
      transformedStart transformedFinish transformedBoundary
        ((compactFormulaNegationExact 0 formula).getD []).length
        transformedBoundarySize
      transformStateBoundary (compactSyntaxRunFuelBound formula + 1)
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      transformTableWidth (2 ^ transformTableWidth)
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      (compactAdditiveBoolTag
        (compactCutRuleCheck
          (Gamma, formula, (leftConclusion, leftValid),
            rightConclusion, rightValid))) := by
    simpa only [hGammaCount, hformulaCount, hwitnessCount,
      hsourceCount, htargetCount] using hlocal
  exact CompactNumericVerifierCombineStateGraph.exists_of_exs_cut_rows
    hframeSaved hlocalAligned

#print axioms CompactNumericVerifierCombineStateGraph.exists_of_exs_frame
#print axioms CompactNumericVerifierCombineStateGraph.exists_of_cut_frame

end FoundationCompactNumericListedDirectVerifierCombineExsCutStateGraphCompleteness
