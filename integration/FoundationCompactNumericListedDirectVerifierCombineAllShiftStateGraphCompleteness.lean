import integration.FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness
import integration.FoundationCompactNumericListedDirectVerifierChildResultComponentBounds

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
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectFormulaShiftExactListRowsCompleteness
open FoundationCompactNumericListedDirectAllShiftCombineRuleRows
open FoundationCompactNumericListedDirectAllShiftCombineRuleRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds
open FoundationCompactNumericListedDirectVerifierCombineStateGraph
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness
open FoundationCompactNumericListedDirectVerifierChildResultComponentBounds

def compactNumericAllShiftCombineRuleCoordinateSizeBound
    (width tokenCount : Nat) : Nat :=
  compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount

structure CompactNumericAllShiftCombineRuleWitnessBounds
    (width tokenCount : Nat)
    (witness : CompactNumericVerifierCombineRuleWitness) : Prop where
  critical : CompactNumericAllShiftCriticalCoordinateBounds
    width tokenCount witness.shiftWitnessBound
      witness.freeStateBoundary witness.freeTableWidth witness.freeValueBound
  coordinate_size : ∀ coordinate : Fin 34,
    Nat.size (compactNumericVerifierCombineRuleWitnessEnvironment
      witness coordinate) ≤
        compactNumericAllShiftCombineRuleCoordinateSizeBound width tokenCount

private theorem tokenCount_le_allShiftCriticalCoordinateSizeBound
    (width tokenCount : Nat) :
    tokenCount ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount := by
  have htokenArea : tokenCount ≤ (tokenCount + 1) * tokenCount := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.le_add_left tokenCount (tokenCount * tokenCount)
  exact htokenArea.trans (by
    simp [compactNumericAllShiftCriticalCoordinateSizeBound,
      compactFormulaShiftExactListCoordinateSizeBound]
    omega)

private theorem boundaryArea_le_allShiftCriticalCoordinateSizeBound
    (width tokenCount : Nat) :
    (tokenCount + 1) * tokenCount ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount := by
  simp [compactNumericAllShiftCriticalCoordinateSizeBound,
    compactFormulaShiftExactListCoordinateSizeBound]
  omega

private theorem publicFuelSucc_le_allShiftCriticalCoordinateSizeBound
    (width tokenCount : Nat) :
    compactFormulaShiftExactListPublicFuelBound tokenCount + 1 ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount := by
  simp [compactNumericAllShiftCriticalCoordinateSizeBound,
    compactFormulaShiftExactListCoordinateSizeBound]
  omega

private theorem structuredListLayout_finish_le_tokenCount
    {tokenTable width tokenCount start count finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable) :
    finish ≤ tokenCount := by
  rcases hlayout with
    ⟨_bodyStart, _hbodyStart, _hheader, hboundary⟩
  exact hboundary.2.1

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
      shiftCandidateStart shiftCandidateFinish shiftCandidateBoundary
      shiftedStart shiftedFinish shiftedBoundary
      emptyStart emptyFinish : Nat}
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
          (compactFormulaTransformInitialState 1 formula)) ∧
      Nat.size freeStateBoundary ≤
        ((compactFormulaTransformStateTrace (0, [])
            (compactSyntaxRunFuelBound formula)
            (compactFormulaTransformInitialState 1 formula)).length + 1) *
          tokenCount)
    (hcandidate :
      CompactAdditiveStructuredListLayout tokenTable width tokenCount
          shiftCandidateStart (Gamma.map fun candidateFormula =>
            (compactFormulaShiftExact 0 candidateFormula).getD []).length
          shiftCandidateFinish shiftCandidateBoundary ∧
        CompactAdditiveStructuredListElementRowLayouts
          CompactAdditiveNatListDirectLayout tokenTable width tokenCount
            shiftCandidateBoundary
            (Gamma.map fun candidateFormula =>
              (compactFormulaShiftExact 0 candidateFormula).getD []) ∧
        Nat.size shiftCandidateBoundary ≤
          ((Gamma.map fun candidateFormula =>
              (compactFormulaShiftExact 0 candidateFormula).getD []).length + 1) *
            tokenCount)
    (hshifted :
      CompactAdditiveStructuredListLayout tokenTable width tokenCount
          shiftedStart ((compactFormulaShiftExactList Gamma).getD []).length
          shiftedFinish shiftedBoundary ∧
        CompactAdditiveStructuredListElementRowLayouts
          CompactAdditiveNatListDirectLayout tokenTable width tokenCount
            shiftedBoundary ((compactFormulaShiftExactList Gamma).getD []) ∧
        Nat.size shiftedBoundary ≤
          (((compactFormulaShiftExactList Gamma).getD []).length + 1) *
            tokenCount)
    (hshiftTraces : ∀ index (_hindex : index < Gamma.length),
      ∃ stateBoundary,
        CompactFormulaTransformStateListRowLayouts
          tokenTable width tokenCount stateBoundary
          (compactFormulaTransformStateTrace (1, [])
            (compactSyntaxRunFuelBound (Gamma.getI index))
            (compactFormulaTransformInitialState 0 (Gamma.getI index))) ∧
        Nat.size stateBoundary ≤
          ((compactFormulaTransformStateTrace (1, [])
              (compactSyntaxRunFuelBound (Gamma.getI index))
              (compactFormulaTransformInitialState 0
                (Gamma.getI index))).length + 1) * tokenCount)
    (htokenCount : 1 ≤ tokenCount) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness ∧
      CompactNumericAllShiftCombineRuleWitnessBounds
        width tokenCount ruleWitness := by
  have hframeSaved := hframePackage
  rcases hframePackage with
    ⟨hcurrentPackage, hnextPackage, _hhead, _hframe,
      htaskTag, htaskLayout, hGammaRows, hGammaCount,
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
  rcases
      CompactAdditiveStructuredListElementRowLayouts.childResult_component_size_bounds
        hsourceRows (rowIndex := 0) (by simp) with
    ⟨premiseGammaCount, premiseGammaBoundary, premiseBoolValue,
      hpremiseCount, hpremiseRowsRaw, hpremiseBoolRaw,
      hpremiseCountLe, hpremiseCountSize,
      hpremiseBoundarySize, hpremiseBoolSize⟩
  have hpremiseCountEq : premiseGammaCount = premise.length := by
    simpa using hpremiseCount
  have hpremiseLengthLe : premise.length ≤ tokenCount := by
    simpa [hpremiseCountEq] using hpremiseCountLe
  have hpremiseLengthSize : Nat.size premise.length ≤ tokenCount := by
    simpa [hpremiseCountEq] using hpremiseCountSize
  have hpremiseRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      premiseGammaBoundary premise := by
    simpa using hpremiseRowsRaw
  have hpremiseBool : premiseBoolValue =
      compactAdditiveBoolTag premiseValid := by
    simpa using hpremiseBoolRaw
  have hGammaLengthLe : Gamma.length ≤ tokenCount := by
    rcases htaskLayout with
      ⟨_fieldsStart, _htagLayout, hfieldsLayout⟩
    rcases hfieldsLayout with
      ⟨_gammaFinish, _firstFinish, _secondFinish, _witnessFinish,
        hGammaLayout, _hfirstLayout, _hsecondLayout,
        _hwitnessLayout, _hsuffixLayout⟩
    rcases hGammaLayout with
      ⟨_gammaBoundary, hGammaStructure, _hGammaRows, _hGammaSize⟩
    exact structuredListLayout_count_le_tokenCount hGammaStructure
  have hformulaLengthLe : formula.length ≤ tokenCount := by
    rcases hformulaLayout with
      ⟨_formulaBoundary, hformulaStructure,
        _hformulaRows, _hformulaSize⟩
    exact structuredListLayout_count_le_tokenCount hformulaStructure
  have htag : taskCoordinates.tag = 5 := by
    simpa using htaskTag.symm
  rcases CompactNumericAllShiftCombineRuleRows.exists_of_all
      hGammaRows hformulaLayout hfreed hempty hfreeTrace hcandidate.2.1
      hshifted.2.1
      hshiftTraces hpremiseRows hpremiseBool hsourceRows htargetRows
      hsourceGraph htargetGraph htokenCount htag (by simp) (by simp) (by simp) with
    ⟨formulaBoundary, formulaBoundarySize,
      freedBoundary, freedBoundarySize,
      emptyBoundary, emptyBoundarySize,
      shiftWitnessBound, freeTableWidth, hlocal, hcritical⟩
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
  let ruleWitness := compactNumericVerifierAllShiftCombineRuleWitness
    premise.length premiseGammaBoundary premiseBoolValue
    formulaBoundary formulaBoundarySize
    freedStart freedFinish freedBoundary
      ((compactFormulaFreeExact formula).getD []).length freedBoundarySize
    freeStateBoundary (compactSyntaxRunFuelBound formula + 1)
    shiftCandidateBoundary (compactFormulaShiftSuccessTable tokenCount Gamma)
    shiftedBoundary ((compactFormulaShiftExactList Gamma).getD []).length
    emptyStart emptyFinish emptyBoundary emptyBoundarySize
    shiftWitnessBound freeTableWidth (2 ^ freeTableWidth)
    (compactAdditiveBoolTag
      (compactAllRuleCheck (Gamma, formula, premise, premiseValid)))
  have hall := hlocalAligned.resolve_right (by
    intro hshift
    omega)
  rcases hall with
    ⟨_htagAll, _hsourceNonempty, hformulaWitness, hfreedWitness,
      _hpremiseWellFormed, _hpremiseHead, hcheck, _hpush⟩
  rcases hformulaWitness with
    ⟨_hformulaStructure, _hformulaUnitRows,
      hformulaBoundarySizeEq, hformulaBoundarySizeRaw⟩
  rcases hfreedWitness with
    ⟨hfreedStructure, _hfreedUnitRows,
      hfreedBoundarySizeEq, hfreedBoundarySizeRaw⟩
  rcases hcheck with
    ⟨_hfreeTransform, hshiftRows, _hshiftedWellFormed,
      _hresultLe, _hresultIff⟩
  rcases hshiftRows with
    ⟨hemptyWitness, _hshiftRows, _hshiftOutcome⟩
  rcases hemptyWitness with
    ⟨hemptyStructure, _hemptyUnitRows,
      hemptyBoundarySizeEq, hemptyBoundarySizeRaw⟩
  have htokenBound :=
    tokenCount_le_allShiftCriticalCoordinateSizeBound
      width tokenCount
  have hareaBound :=
    boundaryArea_le_allShiftCriticalCoordinateSizeBound width tokenCount
  have hpremiseLengthSizeBound : Nat.size premise.length ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    hpremiseLengthSize.trans htokenBound
  have hpremiseBoundarySizeBound : Nat.size premiseGammaBoundary ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    hpremiseBoundarySize.trans hareaBound
  have hpremiseBoolSizeBound : Nat.size premiseBoolValue ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    hpremiseBoolSize.trans (htokenCount.trans htokenBound)
  have hformulaArea : (formula.length + 1) * tokenCount ≤
      (tokenCount + 1) * tokenCount :=
    Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right hformulaLengthLe 1)
  have hformulaBoundarySizeRaw' : formulaBoundarySize ≤
      (formula.length + 1) * tokenCount := by
    simpa only [hformulaCount] using hformulaBoundarySizeRaw
  have hformulaBoundarySizeBound : Nat.size formulaBoundary ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount := by
    rw [← hformulaBoundarySizeEq]
    exact hformulaBoundarySizeRaw'.trans (hformulaArea.trans hareaBound)
  have hformulaBoundarySizeFieldBound : Nat.size formulaBoundarySize ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le (Nat.le_refl formulaBoundarySize)).trans
      (hformulaBoundarySizeRaw'.trans (hformulaArea.trans hareaBound))
  have hfreedCountLe :
      ((compactFormulaFreeExact formula).getD []).length ≤ tokenCount :=
    structuredListLayout_count_le_tokenCount hfreedStructure
  have hfreedArea :
      (((compactFormulaFreeExact formula).getD []).length + 1) * tokenCount ≤
        (tokenCount + 1) * tokenCount :=
    Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right hfreedCountLe 1)
  have hfreedStartSizeBound : Nat.size freedStart ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (Nat.le_of_lt (structuredListLayout_start_lt_tokenCount
        hfreedStructure))).trans htokenBound
  have hfreedFinishSizeBound : Nat.size freedFinish ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (structuredListLayout_finish_le_tokenCount hfreedStructure)).trans
        htokenBound
  have hfreedBoundarySizeBound : Nat.size freedBoundary ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount := by
    rw [← hfreedBoundarySizeEq]
    exact hfreedBoundarySizeRaw.trans (hfreedArea.trans hareaBound)
  have hfreedCountSizeBound :
      Nat.size ((compactFormulaFreeExact formula).getD []).length ≤
        compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le hfreedCountLe).trans htokenBound
  have hfreedBoundarySizeFieldBound : Nat.size freedBoundarySize ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le (Nat.le_refl freedBoundarySize)).trans
      (hfreedBoundarySizeRaw.trans (hfreedArea.trans hareaBound))
  have hfreeFuel : compactSyntaxRunFuelBound formula ≤
      compactFormulaShiftExactListPublicFuelBound tokenCount := by
    have hlength := Nat.add_le_add_right hformulaLengthLe 1
    have hsquare := Nat.mul_le_mul hlength hlength
    have hscaled := Nat.mul_le_mul_left 16 hsquare
    have htotal := Nat.add_le_add_right hscaled 8
    simpa [compactSyntaxRunFuelBound,
      compactFormulaShiftExactListPublicFuelBound, Nat.mul_assoc] using htotal
  have hfreeStateCountSizeBound :
      Nat.size (compactSyntaxRunFuelBound formula + 1) ≤
        compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le (Nat.le_refl _)).trans
      ((Nat.add_le_add_right hfreeFuel 1).trans
        (publicFuelSucc_le_allShiftCriticalCoordinateSizeBound width tokenCount))
  have hcandidateBoundarySizeBound : Nat.size shiftCandidateBoundary ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount := by
    exact hcandidate.2.2.trans ((Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right (by simpa using hGammaLengthLe) 1)).trans
        hareaBound)
  have hsuccessTableSizeRaw := compactFixedWidthTableCode_size_le
    tokenCount (compactFormulaShiftSuccessValues Gamma)
  have hsuccessTableSize :
      Nat.size (compactFormulaShiftSuccessTable tokenCount Gamma) ≤
        Gamma.length * tokenCount := by
    simpa [compactFormulaShiftSuccessTable,
      compactFormulaShiftSuccessValues] using hsuccessTableSizeRaw
  have hsuccessTableSizeBound :
      Nat.size (compactFormulaShiftSuccessTable tokenCount Gamma) ≤
        compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    hsuccessTableSize.trans ((Nat.mul_le_mul_right tokenCount
      (hGammaLengthLe.trans (Nat.le_add_right tokenCount 1))).trans hareaBound)
  have hshiftedCountLe :
      ((compactFormulaShiftExactList Gamma).getD []).length ≤ tokenCount :=
    structuredListLayout_count_le_tokenCount hshifted.1
  have hshiftedBoundarySizeBound : Nat.size shiftedBoundary ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    hshifted.2.2.trans ((Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right hshiftedCountLe 1)).trans hareaBound)
  have hshiftedCountSizeBound :
      Nat.size ((compactFormulaShiftExactList Gamma).getD []).length ≤
        compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le hshiftedCountLe).trans htokenBound
  have hemptyStartSizeBound : Nat.size emptyStart ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (Nat.le_of_lt (structuredListLayout_start_lt_tokenCount
        hemptyStructure))).trans htokenBound
  have hemptyFinishSizeBound : Nat.size emptyFinish ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (structuredListLayout_finish_le_tokenCount hemptyStructure)).trans
        htokenBound
  have hemptyBoundarySizeRaw' : emptyBoundarySize ≤ tokenCount := by
    simpa using hemptyBoundarySizeRaw
  have hemptyBoundarySizeBound : Nat.size emptyBoundary ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount := by
    rw [← hemptyBoundarySizeEq]
    exact hemptyBoundarySizeRaw'.trans htokenBound
  have hemptyBoundarySizeFieldBound : Nat.size emptyBoundarySize ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le (Nat.le_refl emptyBoundarySize)).trans
      (hemptyBoundarySizeRaw'.trans htokenBound)
  have hresultBoolSizeBound :
      Nat.size (compactAdditiveBoolTag
        (compactAllRuleCheck (Gamma, formula, premise, premiseValid))) ≤
        compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount := by
    have hbool : Nat.size (compactAdditiveBoolTag
        (compactAllRuleCheck (Gamma, formula, premise, premiseValid))) ≤ 1 := by
      cases compactAllRuleCheck (Gamma, formula, premise, premiseValid) <;>
        simp [compactAdditiveBoolTag]
    exact hbool.trans (htokenCount.trans htokenBound)
  have hfieldBounds :
      CompactNumericVerifierAllShiftCombineRuleFieldSizeBounds
        premise.length premiseGammaBoundary premiseBoolValue
        formulaBoundary formulaBoundarySize
        freedStart freedFinish freedBoundary
          ((compactFormulaFreeExact formula).getD []).length freedBoundarySize
        freeStateBoundary (compactSyntaxRunFuelBound formula + 1)
        shiftCandidateBoundary (compactFormulaShiftSuccessTable tokenCount Gamma)
        shiftedBoundary ((compactFormulaShiftExactList Gamma).getD []).length
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        shiftWitnessBound freeTableWidth (2 ^ freeTableWidth)
        (compactAdditiveBoolTag
          (compactAllRuleCheck (Gamma, formula, premise, premiseValid)))
        (compactNumericAllShiftCombineRuleCoordinateSizeBound
          width tokenCount) := by
    exact
      { premiseGammaCount := hpremiseLengthSizeBound
        premiseGammaBoundary := hpremiseBoundarySizeBound
        premiseBoolValue := hpremiseBoolSizeBound
        formulaBoundary := hformulaBoundarySizeBound
        formulaBoundarySize := hformulaBoundarySizeFieldBound
        freedStart := hfreedStartSizeBound
        freedFinish := hfreedFinishSizeBound
        freedBoundary := hfreedBoundarySizeBound
        freedCount := hfreedCountSizeBound
        freedBoundarySize := hfreedBoundarySizeFieldBound
        freeStateBoundary := hcritical.freeStateBoundary_size
        freeStateCount := hfreeStateCountSizeBound
        shiftCandidateBoundary := hcandidateBoundarySizeBound
        shiftSuccessTable := hsuccessTableSizeBound
        shiftedBoundary := hshiftedBoundarySizeBound
        shiftedCount := hshiftedCountSizeBound
        emptyStart := hemptyStartSizeBound
        emptyFinish := hemptyFinishSizeBound
        emptyBoundary := hemptyBoundarySizeBound
        emptyBoundarySize := hemptyBoundarySizeFieldBound
        shiftWitnessBound := hcritical.shiftWitnessBound_size
        freeTableWidth := hcritical.freeTableWidth_size
        freeValueBound := hcritical.freeValueBound_size
        resultBoolValue := hresultBoolSizeBound }
  refine ⟨ruleWitness, ?_, ?_⟩
  · exact CompactNumericVerifierCombineStateGraph.of_all_shift_rows
      hframeSaved hlocalAligned
  · refine
      { critical := by
          simpa [ruleWitness,
            compactNumericVerifierAllShiftCombineRuleWitness] using hcritical
        coordinate_size := ?_ }
    intro coordinate
    simpa [ruleWitness] using hfieldBounds.coordinate coordinate

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
    {shiftCandidateStart shiftCandidateFinish shiftCandidateBoundary
      shiftedStart shiftedFinish shiftedBoundary emptyStart emptyFinish : Nat}
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
    (hcandidate :
      CompactAdditiveStructuredListLayout tokenTable width tokenCount
          shiftCandidateStart (premise.map fun candidateFormula =>
            (compactFormulaShiftExact 0 candidateFormula).getD []).length
          shiftCandidateFinish shiftCandidateBoundary ∧
        CompactAdditiveStructuredListElementRowLayouts
          CompactAdditiveNatListDirectLayout tokenTable width tokenCount
            shiftCandidateBoundary
            (premise.map fun candidateFormula =>
              (compactFormulaShiftExact 0 candidateFormula).getD []) ∧
        Nat.size shiftCandidateBoundary ≤
          ((premise.map fun candidateFormula =>
              (compactFormulaShiftExact 0 candidateFormula).getD []).length + 1) *
            tokenCount)
    (hshifted :
      CompactAdditiveStructuredListLayout tokenTable width tokenCount
          shiftedStart ((compactFormulaShiftExactList premise).getD []).length
          shiftedFinish shiftedBoundary ∧
        CompactAdditiveStructuredListElementRowLayouts
          CompactAdditiveNatListDirectLayout tokenTable width tokenCount
            shiftedBoundary ((compactFormulaShiftExactList premise).getD []) ∧
        Nat.size shiftedBoundary ≤
          (((compactFormulaShiftExactList premise).getD []).length + 1) *
            tokenCount)
    (hshiftTraces : ∀ index (_hindex : index < premise.length),
      ∃ stateBoundary,
        CompactFormulaTransformStateListRowLayouts
          tokenTable width tokenCount stateBoundary
          (compactFormulaTransformStateTrace (1, [])
            (compactSyntaxRunFuelBound (premise.getI index))
            (compactFormulaTransformInitialState 0 (premise.getI index))) ∧
        Nat.size stateBoundary ≤
          ((compactFormulaTransformStateTrace (1, [])
              (compactSyntaxRunFuelBound (premise.getI index))
              (compactFormulaTransformInitialState 0
                (premise.getI index))).length + 1) * tokenCount)
    (htokenCount : 1 ≤ tokenCount) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness ∧
      CompactNumericAllShiftCombineRuleWitnessBounds
        width tokenCount ruleWitness := by
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
  rcases
      CompactAdditiveStructuredListElementRowLayouts.childResult_component_size_bounds
        hsourceRows (rowIndex := 0) (by simp) with
    ⟨premiseGammaCount, premiseGammaBoundary, premiseBoolValue,
      hpremiseCount, hpremiseRowsRaw, hpremiseBoolRaw,
      hpremiseCountLe, hpremiseCountSize,
      hpremiseBoundarySize, hpremiseBoolSize⟩
  have hpremiseCountEq : premiseGammaCount = premise.length := by
    simpa using hpremiseCount
  have hpremiseLengthLe : premise.length ≤ tokenCount := by
    simpa [hpremiseCountEq] using hpremiseCountLe
  have hpremiseLengthSize : Nat.size premise.length ≤ tokenCount := by
    simpa [hpremiseCountEq] using hpremiseCountSize
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
      hGammaRows hempty hcandidate.2.1 hshifted.2.1 hshiftTraces
      hpremiseRows hpremiseBool hsourceRows htargetRows
      hsourceGraph htargetGraph htokenCount htag (by simp) (by simp) (by simp) with
    ⟨emptyBoundary, emptyBoundarySize, shiftWitnessBound,
      hlocal, hcritical⟩
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
  let ruleWitness := compactNumericVerifierAllShiftCombineRuleWitness
    premise.length premiseGammaBoundary premiseBoolValue
    0 0 0 0 0 0 0 0 0
    shiftCandidateBoundary
      (compactFormulaShiftSuccessTable tokenCount premise)
    shiftedBoundary ((compactFormulaShiftExactList premise).getD []).length
    emptyStart emptyFinish emptyBoundary emptyBoundarySize
    shiftWitnessBound 0 0
    (compactAdditiveBoolTag
      (compactShiftRuleCheck (Gamma, premise, premiseValid)))
  have hshift := hlocalAligned.resolve_left (by
    intro hall
    omega)
  rcases hshift with
    ⟨_htagShift, _hsourceNonempty, _hpremiseWellFormed,
      _hpremiseHead, hcheck, _hpush⟩
  rcases hcheck with
    ⟨hshiftRows, _hshiftedWellFormed, _hresultLe, _hresultIff⟩
  rcases hshiftRows with
    ⟨hemptyWitness, _hshiftRows, _hshiftOutcome⟩
  rcases hemptyWitness with
    ⟨hemptyStructure, _hemptyUnitRows,
      hemptyBoundarySizeEq, hemptyBoundarySizeRaw⟩
  have htokenBound :=
    tokenCount_le_allShiftCriticalCoordinateSizeBound
      width tokenCount
  have hareaBound :=
    boundaryArea_le_allShiftCriticalCoordinateSizeBound width tokenCount
  have hpremiseLengthSizeBound : Nat.size premise.length ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    hpremiseLengthSize.trans htokenBound
  have hpremiseBoundarySizeBound : Nat.size premiseGammaBoundary ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    hpremiseBoundarySize.trans hareaBound
  have hpremiseBoolSizeBound : Nat.size premiseBoolValue ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    hpremiseBoolSize.trans (htokenCount.trans htokenBound)
  have hcandidateBoundarySizeBound : Nat.size shiftCandidateBoundary ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount := by
    exact hcandidate.2.2.trans ((Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right (by simpa using hpremiseLengthLe) 1)).trans
        hareaBound)
  have hsuccessTableSizeRaw := compactFixedWidthTableCode_size_le
    tokenCount (compactFormulaShiftSuccessValues premise)
  have hsuccessTableSize :
      Nat.size (compactFormulaShiftSuccessTable tokenCount premise) ≤
        premise.length * tokenCount := by
    simpa [compactFormulaShiftSuccessTable,
      compactFormulaShiftSuccessValues] using hsuccessTableSizeRaw
  have hsuccessTableSizeBound :
      Nat.size (compactFormulaShiftSuccessTable tokenCount premise) ≤
        compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    hsuccessTableSize.trans ((Nat.mul_le_mul_right tokenCount
      (hpremiseLengthLe.trans (Nat.le_add_right tokenCount 1))).trans hareaBound)
  have hshiftedCountLe :
      ((compactFormulaShiftExactList premise).getD []).length ≤ tokenCount :=
    structuredListLayout_count_le_tokenCount hshifted.1
  have hshiftedBoundarySizeBound : Nat.size shiftedBoundary ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    hshifted.2.2.trans ((Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right hshiftedCountLe 1)).trans hareaBound)
  have hshiftedCountSizeBound :
      Nat.size ((compactFormulaShiftExactList premise).getD []).length ≤
        compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le hshiftedCountLe).trans htokenBound
  have hemptyStartSizeBound : Nat.size emptyStart ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (Nat.le_of_lt (structuredListLayout_start_lt_tokenCount
        hemptyStructure))).trans htokenBound
  have hemptyFinishSizeBound : Nat.size emptyFinish ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (structuredListLayout_finish_le_tokenCount hemptyStructure)).trans
        htokenBound
  have hemptyBoundarySizeRaw' : emptyBoundarySize ≤ tokenCount := by
    simpa using hemptyBoundarySizeRaw
  have hemptyBoundarySizeBound : Nat.size emptyBoundary ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount := by
    rw [← hemptyBoundarySizeEq]
    exact hemptyBoundarySizeRaw'.trans htokenBound
  have hemptyBoundarySizeFieldBound : Nat.size emptyBoundarySize ≤
      compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le (Nat.le_refl emptyBoundarySize)).trans
      (hemptyBoundarySizeRaw'.trans htokenBound)
  have hresultBoolSizeBound :
      Nat.size (compactAdditiveBoolTag
        (compactShiftRuleCheck (Gamma, premise, premiseValid))) ≤
        compactNumericAllShiftCriticalCoordinateSizeBound width tokenCount := by
    have hbool : Nat.size (compactAdditiveBoolTag
        (compactShiftRuleCheck (Gamma, premise, premiseValid))) ≤ 1 := by
      cases compactShiftRuleCheck (Gamma, premise, premiseValid) <;>
        simp [compactAdditiveBoolTag]
    exact hbool.trans (htokenCount.trans htokenBound)
  have hfieldBounds :
      CompactNumericVerifierAllShiftCombineRuleFieldSizeBounds
        premise.length premiseGammaBoundary premiseBoolValue
        0 0 0 0 0 0 0 0 0
        shiftCandidateBoundary
          (compactFormulaShiftSuccessTable tokenCount premise)
        shiftedBoundary ((compactFormulaShiftExactList premise).getD []).length
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        shiftWitnessBound 0 0
        (compactAdditiveBoolTag
          (compactShiftRuleCheck (Gamma, premise, premiseValid)))
        (compactNumericAllShiftCombineRuleCoordinateSizeBound
          width tokenCount) := by
    exact
      { premiseGammaCount := hpremiseLengthSizeBound
        premiseGammaBoundary := hpremiseBoundarySizeBound
        premiseBoolValue := hpremiseBoolSizeBound
        formulaBoundary := by simp
        formulaBoundarySize := by simp
        freedStart := by simp
        freedFinish := by simp
        freedBoundary := by simp
        freedCount := by simp
        freedBoundarySize := by simp
        freeStateBoundary := hcritical.freeStateBoundary_size
        freeStateCount := by simp
        shiftCandidateBoundary := hcandidateBoundarySizeBound
        shiftSuccessTable := hsuccessTableSizeBound
        shiftedBoundary := hshiftedBoundarySizeBound
        shiftedCount := hshiftedCountSizeBound
        emptyStart := hemptyStartSizeBound
        emptyFinish := hemptyFinishSizeBound
        emptyBoundary := hemptyBoundarySizeBound
        emptyBoundarySize := hemptyBoundarySizeFieldBound
        shiftWitnessBound := hcritical.shiftWitnessBound_size
        freeTableWidth := hcritical.freeTableWidth_size
        freeValueBound := hcritical.freeValueBound_size
        resultBoolValue := hresultBoolSizeBound }
  refine ⟨ruleWitness, ?_, ?_⟩
  · exact CompactNumericVerifierCombineStateGraph.of_all_shift_rows
      hframeSaved hlocalAligned
  · refine
      { critical := by
          simpa [ruleWitness,
            compactNumericVerifierAllShiftCombineRuleWitness] using hcritical
        coordinate_size := ?_ }
    intro coordinate
    simpa [ruleWitness] using hfieldBounds.coordinate coordinate

#print axioms CompactNumericVerifierCombineStateGraph.exists_of_all_frame
#print axioms CompactNumericVerifierCombineStateGraph.exists_of_shift_frame

end FoundationCompactNumericListedDirectVerifierCombineAllShiftStateGraphCompleteness
