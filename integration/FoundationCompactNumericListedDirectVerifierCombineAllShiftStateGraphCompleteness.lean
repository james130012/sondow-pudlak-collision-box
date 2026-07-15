import integration.FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness

/-!
# Full 93-column converse constructors for universal and shift combine rules

The constructors recover the real premise row from the current verifier state,
build the checked local rule rows from canonical transform layouts, and lift the
result through the common state frame to the fixed 93-column graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineAllShiftStateGraphCompleteness

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
open FoundationCompactNumericListedDirectAllShiftCombineRuleRows
open FoundationCompactNumericListedDirectAllShiftCombineRuleRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineStateGraph
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness

theorem CompactNumericVerifierCombineStateGraph.exists_of_all_frame
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {Gamma : List (List Nat)}
    {formula secondFormula witness suffix : List Nat}
    {tasks : List CompactNumericVerifierTask}
    {premise : List (List Nat)} {premiseValid : Bool}
    {tail : List CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {freedStart freedFinish freeStateBoundary
      shiftCandidateBoundary shiftedBoundary emptyStart emptyFinish : Nat}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens
      (5, (Gamma, (formula, (secondFormula, (witness, suffix)))))
      tasks ((premise, premiseValid) :: tail)
      ((Gamma, compactAllRuleCheck
        (Gamma, formula, premise, premiseValid)) :: tail)
      none currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (hfreed : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount freedStart freedFinish
        ((compactFormulaFreeExact formula).getD []))
    (hempty : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount emptyStart emptyFinish [])
    (hfreeTrace : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount freeStateBoundary
        (compactFormulaTransformStateTrace (0, [])
          (compactSyntaxRunFuelBound formula)
          (compactFormulaTransformInitialState 1 formula)))
    (hcandidate : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        shiftCandidateBoundary
        (Gamma.map fun candidateFormula =>
          (compactFormulaShiftExact 0 candidateFormula).getD []))
    (hshifted : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        shiftedBoundary ((compactFormulaShiftExactList Gamma).getD []))
    (hshiftTraces : ∀ index (_hindex : index < Gamma.length),
      ∃ stateBoundary,
        CompactFormulaTransformStateListRowLayouts
          tokenTable width tokenCount stateBoundary
          (compactFormulaTransformStateTrace (1, [])
            (compactSyntaxRunFuelBound (Gamma.getI index))
            (compactFormulaTransformInitialState 0 (Gamma.getI index))))
    (htokenCount : 1 ≤ tokenCount) :
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
      ((premise, premiseValid) :: tail).length
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueTableWidth,
      hcurrentValueValueBound] using hsourceGraphCanonical
  have htargetGraphCanonical :=
    CompactAdditiveStructuredListElementRowLayouts.childResultListRowsGraph
      htargetRows
  have htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount nextCoordinates.valueBoundary
      ((Gamma, compactAllRuleCheck
        (Gamma, formula, premise, premiseValid)) :: tail).length
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueTableWidth,
      hcurrentValueValueBound] using htargetGraphCanonical
  rcases CompactAdditiveStructuredListElementRowLayouts.childResult_components_at
      hsourceRows 0 (by simp) with
    ⟨premiseGammaBoundary, premiseBoolValue,
      hpremiseRowsRaw, hpremiseBoolRaw⟩
  have hpremiseRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      premiseGammaBoundary premise := by
    simpa using hpremiseRowsRaw
  have hpremiseBool : premiseBoolValue =
      compactAdditiveBoolTag premiseValid := by
    simpa using hpremiseBoolRaw
  have htag : taskCoordinates.tag = 5 := by
    simpa using htaskTag.symm
  rcases CompactNumericAllShiftCombineRuleRows.exists_of_all
      hGammaRows hformulaLayout hfreed hempty hfreeTrace hcandidate hshifted
      hshiftTraces hpremiseRows hpremiseBool hsourceRows htargetRows
      hsourceGraph htargetGraph htokenCount htag (by simp) (by simp) (by simp) with
    ⟨formulaBoundary, formulaBoundarySize,
      freedBoundary, freedBoundarySize,
      emptyBoundary, emptyBoundarySize,
      shiftWitnessBound, freeTableWidth, hlocal⟩
  have hlocalAligned : CompactNumericAllShiftCombineRuleRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
      premise.length premiseGammaBoundary premiseBoolValue
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      formulaBoundary formulaBoundarySize
      freedStart freedFinish freedBoundary
        ((compactFormulaFreeExact formula).getD []).length freedBoundarySize
      freeStateBoundary (compactSyntaxRunFuelBound formula + 1)
      shiftCandidateBoundary
        (compactFormulaShiftSuccessTable tokenCount Gamma)
      shiftedBoundary ((compactFormulaShiftExactList Gamma).getD []).length
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound freeTableWidth (2 ^ freeTableWidth)
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      (compactAdditiveBoolTag
        (compactAllRuleCheck (Gamma, formula, premise, premiseValid))) := by
    simpa only [hGammaCount, hformulaCount,
      hsourceCount, htargetCount] using hlocal
  exact CompactNumericVerifierCombineStateGraph.exists_of_all_shift_rows
    hframeSaved hlocalAligned

theorem CompactNumericVerifierCombineStateGraph.exists_of_shift_frame
    {tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {Gamma : List (List Nat)}
    {firstFormula secondFormula witness suffix : List Nat}
    {tasks : List CompactNumericVerifierTask}
    {premise : List (List Nat)} {premiseValid : Bool}
    {tail : List CompactNumericChildResult}
    {currentCoordinates nextCoordinates :
      CompactNumericVerifierStateRowCoordinates}
    {currentSizeWitness nextSizeWitness :
      CompactNumericVerifierStateSizeWitness}
    {taskCoordinates : CompactNumericVerifierTaskRowCoordinates}
    {taskSizeWitness : CompactNumericVerifierTaskSizeWitness}
    {shiftCandidateBoundary shiftedBoundary emptyStart emptyFinish : Nat}
    (hframePackage : CompactNumericVerifierCombineCanonicalFramePackage
      tokenTable width tokenCount currentStart currentFinish
      nextStart nextFinish proofTokens certificateTokens
      (8, (Gamma, (firstFormula, (secondFormula, (witness, suffix)))))
      tasks ((premise, premiseValid) :: tail)
      ((Gamma, compactShiftRuleCheck
        (Gamma, premise, premiseValid)) :: tail)
      none currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness)
    (hempty : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount emptyStart emptyFinish [])
    (hcandidate : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        shiftCandidateBoundary
        (premise.map fun candidateFormula =>
          (compactFormulaShiftExact 0 candidateFormula).getD []))
    (hshifted : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        shiftedBoundary ((compactFormulaShiftExactList premise).getD []))
    (hshiftTraces : ∀ index (_hindex : index < premise.length),
      ∃ stateBoundary,
        CompactFormulaTransformStateListRowLayouts
          tokenTable width tokenCount stateBoundary
          (compactFormulaTransformStateTrace (1, [])
            (compactSyntaxRunFuelBound (premise.getI index))
            (compactFormulaTransformInitialState 0 (premise.getI index))))
    (htokenCount : 1 ≤ tokenCount) :
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
      ((premise, premiseValid) :: tail).length
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueTableWidth,
      hcurrentValueValueBound] using hsourceGraphCanonical
  have htargetGraphCanonical :=
    CompactAdditiveStructuredListElementRowLayouts.childResultListRowsGraph
      htargetRows
  have htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount nextCoordinates.valueBoundary
      ((Gamma, compactShiftRuleCheck
        (Gamma, premise, premiseValid)) :: tail).length
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound := by
    simpa only [hcurrentValueTableWidth,
      hcurrentValueValueBound] using htargetGraphCanonical
  rcases CompactAdditiveStructuredListElementRowLayouts.childResult_components_at
      hsourceRows 0 (by simp) with
    ⟨premiseGammaBoundary, premiseBoolValue,
      hpremiseRowsRaw, hpremiseBoolRaw⟩
  have hpremiseRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      premiseGammaBoundary premise := by
    simpa using hpremiseRowsRaw
  have hpremiseBool : premiseBoolValue =
      compactAdditiveBoolTag premiseValid := by
    simpa using hpremiseBoolRaw
  have htag : taskCoordinates.tag = 8 := by
    simpa using htaskTag.symm
  rcases CompactNumericAllShiftCombineRuleRows.exists_of_shift
      (gammaFinish := taskCoordinates.gammaFinish)
      (firstFinish := taskCoordinates.firstFinish)
      hGammaRows hempty hcandidate hshifted hshiftTraces
      hpremiseRows hpremiseBool hsourceRows htargetRows
      hsourceGraph htargetGraph htokenCount htag (by simp) (by simp) (by simp) with
    ⟨emptyBoundary, emptyBoundarySize, shiftWitnessBound, hlocal⟩
  have hlocalAligned : CompactNumericAllShiftCombineRuleRows
      tokenTable width tokenCount
      taskCoordinates.tag taskCoordinates.gammaFinish
        taskCoordinates.gammaCount taskCoordinates.gammaBoundary
      taskCoordinates.firstFinish taskCoordinates.firstCount
      premise.length premiseGammaBoundary premiseBoolValue
      currentCoordinates.valueBoundary currentCoordinates.valueCount
      nextCoordinates.valueBoundary nextCoordinates.valueCount
      0 0 0 0 0 0 0 0 0
      shiftCandidateBoundary
        (compactFormulaShiftSuccessTable tokenCount premise)
      shiftedBoundary ((compactFormulaShiftExactList premise).getD []).length
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      shiftWitnessBound 0 0
      currentSizeWitness.valueTableWidth
      currentSizeWitness.valueValueBound
      (compactAdditiveBoolTag
        (compactShiftRuleCheck (Gamma, premise, premiseValid))) := by
    right
    rcases hlocal with hall | hshift
    · omega
    · simpa only [hGammaCount, hsourceCount, htargetCount] using hshift
  exact CompactNumericVerifierCombineStateGraph.exists_of_all_shift_rows
    hframeSaved hlocalAligned

#print axioms CompactNumericVerifierCombineStateGraph.exists_of_all_frame
#print axioms CompactNumericVerifierCombineStateGraph.exists_of_shift_frame

end FoundationCompactNumericListedDirectVerifierCombineAllShiftStateGraphCompleteness
