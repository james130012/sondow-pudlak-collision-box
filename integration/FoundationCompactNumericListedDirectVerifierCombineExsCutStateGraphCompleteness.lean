import integration.FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness
import integration.FoundationCompactNumericListedDirectVerifierChildResultComponentBounds
import integration.FoundationCompactNumericListedDirectExsCutCombineRuleRowsCompleteness
import integration.FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds

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
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectExsCutCombineRuleRows
open FoundationCompactNumericListedDirectExsCutCombineRuleRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineBranchRows
open FoundationCompactNumericListedDirectVerifierCombineRuleWitnessBounds
open FoundationCompactNumericListedDirectVerifierCombineStateGraph
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness
open FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness
open FoundationCompactNumericListedDirectVerifierChildResultComponentBounds

def compactNumericExsCutCombineRuleCoordinateSizeBound
    (width tokenCount : Nat) : Nat :=
  compactNumericExsCutCriticalCoordinateSizeBound width tokenCount

structure CompactNumericExsCutCombineRuleWitnessBounds
    (width tokenCount : Nat)
    (witness : CompactNumericVerifierCombineRuleWitness) : Prop where
  critical : CompactNumericExsCutCriticalCoordinateBounds
    width tokenCount witness.transformStateBoundary
      witness.freeTableWidth witness.freeValueBound
  coordinate_size : ∀ coordinate : Fin 34,
    Nat.size (compactNumericVerifierCombineRuleWitnessEnvironment
      witness coordinate) ≤
        compactNumericExsCutCombineRuleCoordinateSizeBound width tokenCount

private theorem tokenCount_le_exsCutCriticalCoordinateSizeBound
    (width tokenCount : Nat) :
    tokenCount ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount := by
  have htokenArea : tokenCount ≤ (tokenCount + 1) * tokenCount := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.le_add_left tokenCount (tokenCount * tokenCount)
  exact htokenArea.trans (by
    simp [compactNumericExsCutCriticalCoordinateSizeBound]
    omega)

private theorem boundaryArea_le_exsCutCriticalCoordinateSizeBound
    (width tokenCount : Nat) :
    (tokenCount + 1) * tokenCount ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount := by
  simp [compactNumericExsCutCriticalCoordinateSizeBound]
  omega

private theorem publicFuelSucc_le_exsCutCriticalCoordinateSizeBound
    (width tokenCount : Nat) :
    compactNumericExsCutFormulaTransformPublicFuelBound tokenCount + 1 ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount := by
  simp [compactNumericExsCutCriticalCoordinateSizeBound]
  omega

private theorem structuredListLayout_finish_le_tokenCount
    {tokenTable width tokenCount start count finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable) :
    finish ≤ tokenCount := by
  rcases hlayout with
    ⟨_bodyStart, _hbodyStart, _hheader, hboundary⟩
  exact hboundary.2.1

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
    (htraceRows :
      CompactFormulaTransformStateListRowLayouts
          tokenTable width tokenCount transformStateBoundary
          (compactFormulaTransformStateTrace (2, witness)
            (compactSyntaxRunFuelBound formula)
            (compactFormulaTransformInitialState 1 formula)) ∧
        Nat.size transformStateBoundary ≤
          ((compactFormulaTransformStateTrace (2, witness)
              (compactSyntaxRunFuelBound formula)
              (compactFormulaTransformInitialState 1 formula)).length + 1) *
            tokenCount) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness ∧
      CompactNumericExsCutCombineRuleWitnessBounds
        width tokenCount ruleWitness := by
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
  rcases
      CompactAdditiveStructuredListElementRowLayouts.childResult_component_size_bounds
        hsourceRows (rowIndex := 0) (by simp) with
    ⟨rightGammaCount, rightGammaBoundary, rightBoolValue,
      hrightCount, hrightRowsRaw, hrightBoolRaw,
      hrightCountLe, hrightCountSize,
      hrightBoundarySize, hrightBoolSize⟩
  have hrightCountEq : rightGammaCount = rightConclusion.length := by
    simpa using hrightCount
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
      emptyBoundary, emptyBoundarySize, transformTableWidth,
      hlocal, hcritical⟩
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
  have hlocalSaved := hlocalAligned
  rcases hlocalAligned with
    ⟨hformulaWitness, htransformedWitness, hemptyWitness, _hbranch⟩
  rcases hformulaWitness with
    ⟨hformulaStructure, _hformulaUnitRows,
      hformulaBoundarySizeEq, hformulaBoundarySizeRaw⟩
  rcases htransformedWitness with
    ⟨htransformedStructure, _htransformedUnitRows,
      htransformedBoundarySizeEq, htransformedBoundarySizeRaw⟩
  rcases hemptyWitness with
    ⟨hemptyStructure, _hemptyUnitRows,
      hemptyBoundarySizeEq, hemptyBoundarySizeRaw⟩
  have hformulaLengthLe : formula.length ≤ tokenCount := by
    have hcount :=
      structuredListLayout_count_le_tokenCount hformulaStructure
    simpa only [hformulaCount] using hcount
  have htransformedCountLe :
      ((compactFormulaSubstitutionExact 1
        (witness, formula)).getD []).length ≤ tokenCount :=
    structuredListLayout_count_le_tokenCount htransformedStructure
  have htokenCount : 1 ≤ tokenCount := by
    have hstart :=
      structuredListLayout_start_lt_tokenCount hformulaStructure
    omega
  have htokenBound :=
    tokenCount_le_exsCutCriticalCoordinateSizeBound width tokenCount
  have hareaBound :=
    boundaryArea_le_exsCutCriticalCoordinateSizeBound width tokenCount
  have hrightCountSize' : Nat.size rightConclusion.length ≤ tokenCount := by
    simpa [hrightCountEq] using hrightCountSize
  have hrightCountSizeBound : Nat.size rightConclusion.length ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    hrightCountSize'.trans htokenBound
  have hrightBoundarySizeBound : Nat.size rightGammaBoundary ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    hrightBoundarySize.trans hareaBound
  have hrightBoolSizeBound : Nat.size rightBoolValue ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    hrightBoolSize.trans (htokenCount.trans htokenBound)
  have hformulaArea : (formula.length + 1) * tokenCount ≤
      (tokenCount + 1) * tokenCount :=
    Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right hformulaLengthLe 1)
  have hformulaBoundarySizeRaw' : formulaBoundarySize ≤
      (formula.length + 1) * tokenCount := by
    simpa only [hformulaCount] using hformulaBoundarySizeRaw
  have hformulaBoundarySizeBound : Nat.size formulaBoundary ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount := by
    rw [← hformulaBoundarySizeEq]
    exact hformulaBoundarySizeRaw'.trans (hformulaArea.trans hareaBound)
  have hformulaBoundarySizeFieldBound : Nat.size formulaBoundarySize ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le (Nat.le_refl formulaBoundarySize)).trans
      (hformulaBoundarySizeRaw'.trans (hformulaArea.trans hareaBound))
  have htransformedArea :
      (((compactFormulaSubstitutionExact 1
        (witness, formula)).getD []).length + 1) * tokenCount ≤
        (tokenCount + 1) * tokenCount :=
    Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right htransformedCountLe 1)
  have htransformedStartSizeBound : Nat.size transformedStart ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (Nat.le_of_lt (structuredListLayout_start_lt_tokenCount
        htransformedStructure))).trans htokenBound
  have htransformedFinishSizeBound : Nat.size transformedFinish ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (structuredListLayout_finish_le_tokenCount
        htransformedStructure)).trans htokenBound
  have htransformedBoundarySizeBound : Nat.size transformedBoundary ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount := by
    rw [← htransformedBoundarySizeEq]
    exact htransformedBoundarySizeRaw.trans
      (htransformedArea.trans hareaBound)
  have htransformedCountSizeBound :
      Nat.size ((compactFormulaSubstitutionExact 1
        (witness, formula)).getD []).length ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le htransformedCountLe).trans htokenBound
  have htransformedBoundarySizeFieldBound :
      Nat.size transformedBoundarySize ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le (Nat.le_refl transformedBoundarySize)).trans
      (htransformedBoundarySizeRaw.trans
        (htransformedArea.trans hareaBound))
  have hfuel : compactSyntaxRunFuelBound formula ≤
      compactNumericExsCutFormulaTransformPublicFuelBound tokenCount :=
    compactSyntaxRunFuelBound_le_exsCutPublicFuelBound hformulaLengthLe
  have htransformStateCountSizeBound :
      Nat.size (compactSyntaxRunFuelBound formula + 1) ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le (Nat.le_refl _)).trans
      ((Nat.add_le_add_right hfuel 1).trans
        (publicFuelSucc_le_exsCutCriticalCoordinateSizeBound
          width tokenCount))
  have hemptyStartSizeBound : Nat.size emptyStart ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (Nat.le_of_lt (structuredListLayout_start_lt_tokenCount
        hemptyStructure))).trans htokenBound
  have hemptyFinishSizeBound : Nat.size emptyFinish ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (structuredListLayout_finish_le_tokenCount hemptyStructure)).trans
        htokenBound
  have hemptyBoundarySizeRaw' : emptyBoundarySize ≤ tokenCount := by
    simpa using hemptyBoundarySizeRaw
  have hemptyBoundarySizeBound : Nat.size emptyBoundary ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount := by
    rw [← hemptyBoundarySizeEq]
    exact hemptyBoundarySizeRaw'.trans htokenBound
  have hemptyBoundarySizeFieldBound : Nat.size emptyBoundarySize ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le (Nat.le_refl emptyBoundarySize)).trans
      (hemptyBoundarySizeRaw'.trans htokenBound)
  have hresultBoolSizeBound :
      Nat.size (compactAdditiveBoolTag
        (compactExsRuleCheck
          (Gamma, formula, witness, rightConclusion, rightValid))) ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount := by
    have hbool : Nat.size (compactAdditiveBoolTag
        (compactExsRuleCheck
          (Gamma, formula, witness, rightConclusion, rightValid))) ≤ 1 := by
      cases compactExsRuleCheck
          (Gamma, formula, witness, rightConclusion, rightValid) <;>
        simp [compactAdditiveBoolTag]
    exact hbool.trans (htokenCount.trans htokenBound)
  let ruleWitness := compactNumericVerifierExsCutCombineRuleWitness
    rightConclusion.length rightGammaBoundary rightBoolValue
    0 0 0
    formulaBoundary formulaBoundarySize
    transformedStart transformedFinish transformedBoundary
    ((compactFormulaSubstitutionExact 1
      (witness, formula)).getD []).length transformedBoundarySize
    transformStateBoundary (compactSyntaxRunFuelBound formula + 1)
    emptyStart emptyFinish emptyBoundary emptyBoundarySize
    transformTableWidth (2 ^ transformTableWidth)
    (compactAdditiveBoolTag
      (compactExsRuleCheck
        (Gamma, formula, witness, rightConclusion, rightValid)))
  have hfieldBounds :
      CompactNumericVerifierExsCutCombineRuleFieldSizeBounds
        rightConclusion.length rightGammaBoundary rightBoolValue
        0 0 0
        formulaBoundary formulaBoundarySize
        transformedStart transformedFinish transformedBoundary
        ((compactFormulaSubstitutionExact 1
          (witness, formula)).getD []).length transformedBoundarySize
        transformStateBoundary (compactSyntaxRunFuelBound formula + 1)
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        transformTableWidth (2 ^ transformTableWidth)
        (compactAdditiveBoolTag
          (compactExsRuleCheck
            (Gamma, formula, witness, rightConclusion, rightValid)))
        (compactNumericExsCutCombineRuleCoordinateSizeBound
          width tokenCount) := by
    exact
      { rightGammaCount := hrightCountSizeBound
        rightGammaBoundary := hrightBoundarySizeBound
        rightBoolValue := hrightBoolSizeBound
        leftGammaCount := by simp
        leftGammaBoundary := by simp
        leftBoolValue := by simp
        formulaBoundary := hformulaBoundarySizeBound
        formulaBoundarySize := hformulaBoundarySizeFieldBound
        transformedStart := htransformedStartSizeBound
        transformedFinish := htransformedFinishSizeBound
        transformedBoundary := htransformedBoundarySizeBound
        transformedCount := htransformedCountSizeBound
        transformedBoundarySize := htransformedBoundarySizeFieldBound
        transformStateBoundary := hcritical.transformStateBoundary_size
        transformStateCount := htransformStateCountSizeBound
        emptyStart := hemptyStartSizeBound
        emptyFinish := hemptyFinishSizeBound
        emptyBoundary := hemptyBoundarySizeBound
        emptyBoundarySize := hemptyBoundarySizeFieldBound
        transformTableWidth := hcritical.transformTableWidth_size
        transformValueBound := hcritical.transformValueBound_size
        resultBoolValue := hresultBoolSizeBound }
  refine ⟨ruleWitness, ?_, ?_⟩
  · exact CompactNumericVerifierCombineStateGraph.of_exs_cut_rows
      hframeSaved hlocalSaved
  · refine
      { critical := by
          simpa [ruleWitness,
            compactNumericVerifierExsCutCombineRuleWitness] using hcritical
        coordinate_size := ?_ }
    intro coordinate
    simpa [ruleWitness,
      compactNumericExsCutCombineRuleCoordinateSizeBound] using
        hfieldBounds.coordinate coordinate

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
    (htraceRows :
      CompactFormulaTransformStateListRowLayouts
          tokenTable width tokenCount transformStateBoundary
          (compactFormulaTransformStateTrace (3, [])
            (compactSyntaxRunFuelBound formula)
            (compactFormulaTransformInitialState 0 formula)) ∧
        Nat.size transformStateBoundary ≤
          ((compactFormulaTransformStateTrace (3, [])
              (compactSyntaxRunFuelBound formula)
              (compactFormulaTransformInitialState 0 formula)).length + 1) *
            tokenCount) :
    ∃ ruleWitness : CompactNumericVerifierCombineRuleWitness,
      CompactNumericVerifierCombineStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness
        ruleWitness ∧
      CompactNumericExsCutCombineRuleWitnessBounds
        width tokenCount ruleWitness := by
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
  rcases
      CompactAdditiveStructuredListElementRowLayouts.childResult_component_size_bounds
        hsourceRows (rowIndex := 0) (by simp) with
    ⟨rightGammaCount, rightGammaBoundary, rightBoolValue,
      hrightCount, hrightRowsRaw, hrightBoolRaw,
      hrightCountLe, hrightCountSize,
      hrightBoundarySize, hrightBoolSize⟩
  rcases
      CompactAdditiveStructuredListElementRowLayouts.childResult_component_size_bounds
        hsourceRows (rowIndex := 1) (by simp) with
    ⟨leftGammaCount, leftGammaBoundary, leftBoolValue,
      hleftCount, hleftRowsRaw, hleftBoolRaw,
      hleftCountLe, hleftCountSize,
      hleftBoundarySize, hleftBoolSize⟩
  have hrightCountEq : rightGammaCount = rightConclusion.length := by
    simpa using hrightCount
  have hleftCountEq : leftGammaCount = leftConclusion.length := by
    simpa using hleftCount
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
      emptyBoundary, emptyBoundarySize, transformTableWidth,
      hlocal, hcritical⟩
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
  have hlocalSaved := hlocalAligned
  rcases hlocalAligned with
    ⟨hformulaWitness, htransformedWitness, hemptyWitness, _hbranch⟩
  rcases hformulaWitness with
    ⟨hformulaStructure, _hformulaUnitRows,
      hformulaBoundarySizeEq, hformulaBoundarySizeRaw⟩
  rcases htransformedWitness with
    ⟨htransformedStructure, _htransformedUnitRows,
      htransformedBoundarySizeEq, htransformedBoundarySizeRaw⟩
  rcases hemptyWitness with
    ⟨hemptyStructure, _hemptyUnitRows,
      hemptyBoundarySizeEq, hemptyBoundarySizeRaw⟩
  have hformulaLengthLe : formula.length ≤ tokenCount := by
    have hcount :=
      structuredListLayout_count_le_tokenCount hformulaStructure
    simpa only [hformulaCount] using hcount
  have htransformedCountLe :
      ((compactFormulaNegationExact 0 formula).getD []).length ≤ tokenCount :=
    structuredListLayout_count_le_tokenCount htransformedStructure
  have htokenCount : 1 ≤ tokenCount := by
    have hstart :=
      structuredListLayout_start_lt_tokenCount hformulaStructure
    omega
  have htokenBound :=
    tokenCount_le_exsCutCriticalCoordinateSizeBound width tokenCount
  have hareaBound :=
    boundaryArea_le_exsCutCriticalCoordinateSizeBound width tokenCount
  have hrightCountSize' : Nat.size rightConclusion.length ≤ tokenCount := by
    simpa [hrightCountEq] using hrightCountSize
  have hrightCountSizeBound : Nat.size rightConclusion.length ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    hrightCountSize'.trans htokenBound
  have hrightBoundarySizeBound : Nat.size rightGammaBoundary ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    hrightBoundarySize.trans hareaBound
  have hrightBoolSizeBound : Nat.size rightBoolValue ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    hrightBoolSize.trans (htokenCount.trans htokenBound)
  have hleftCountSize' : Nat.size leftConclusion.length ≤ tokenCount := by
    simpa [hleftCountEq] using hleftCountSize
  have hleftCountSizeBound : Nat.size leftConclusion.length ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    hleftCountSize'.trans htokenBound
  have hleftBoundarySizeBound : Nat.size leftGammaBoundary ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    hleftBoundarySize.trans hareaBound
  have hleftBoolSizeBound : Nat.size leftBoolValue ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    hleftBoolSize.trans (htokenCount.trans htokenBound)
  have hformulaArea : (formula.length + 1) * tokenCount ≤
      (tokenCount + 1) * tokenCount :=
    Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right hformulaLengthLe 1)
  have hformulaBoundarySizeRaw' : formulaBoundarySize ≤
      (formula.length + 1) * tokenCount := by
    simpa only [hformulaCount] using hformulaBoundarySizeRaw
  have hformulaBoundarySizeBound : Nat.size formulaBoundary ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount := by
    rw [← hformulaBoundarySizeEq]
    exact hformulaBoundarySizeRaw'.trans (hformulaArea.trans hareaBound)
  have hformulaBoundarySizeFieldBound : Nat.size formulaBoundarySize ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le (Nat.le_refl formulaBoundarySize)).trans
      (hformulaBoundarySizeRaw'.trans (hformulaArea.trans hareaBound))
  have htransformedArea :
      (((compactFormulaNegationExact 0 formula).getD []).length + 1) *
          tokenCount ≤
        (tokenCount + 1) * tokenCount :=
    Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right htransformedCountLe 1)
  have htransformedStartSizeBound : Nat.size transformedStart ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (Nat.le_of_lt (structuredListLayout_start_lt_tokenCount
        htransformedStructure))).trans htokenBound
  have htransformedFinishSizeBound : Nat.size transformedFinish ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (structuredListLayout_finish_le_tokenCount
        htransformedStructure)).trans htokenBound
  have htransformedBoundarySizeBound : Nat.size transformedBoundary ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount := by
    rw [← htransformedBoundarySizeEq]
    exact htransformedBoundarySizeRaw.trans
      (htransformedArea.trans hareaBound)
  have htransformedCountSizeBound :
      Nat.size ((compactFormulaNegationExact 0 formula).getD []).length ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le htransformedCountLe).trans htokenBound
  have htransformedBoundarySizeFieldBound :
      Nat.size transformedBoundarySize ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le (Nat.le_refl transformedBoundarySize)).trans
      (htransformedBoundarySizeRaw.trans
        (htransformedArea.trans hareaBound))
  have hfuel : compactSyntaxRunFuelBound formula ≤
      compactNumericExsCutFormulaTransformPublicFuelBound tokenCount :=
    compactSyntaxRunFuelBound_le_exsCutPublicFuelBound hformulaLengthLe
  have htransformStateCountSizeBound :
      Nat.size (compactSyntaxRunFuelBound formula + 1) ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le (Nat.le_refl _)).trans
      ((Nat.add_le_add_right hfuel 1).trans
        (publicFuelSucc_le_exsCutCriticalCoordinateSizeBound
          width tokenCount))
  have hemptyStartSizeBound : Nat.size emptyStart ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (Nat.le_of_lt (structuredListLayout_start_lt_tokenCount
        hemptyStructure))).trans htokenBound
  have hemptyFinishSizeBound : Nat.size emptyFinish ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le
      (structuredListLayout_finish_le_tokenCount hemptyStructure)).trans
        htokenBound
  have hemptyBoundarySizeRaw' : emptyBoundarySize ≤ tokenCount := by
    simpa using hemptyBoundarySizeRaw
  have hemptyBoundarySizeBound : Nat.size emptyBoundary ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount := by
    rw [← hemptyBoundarySizeEq]
    exact hemptyBoundarySizeRaw'.trans htokenBound
  have hemptyBoundarySizeFieldBound : Nat.size emptyBoundarySize ≤
      compactNumericExsCutCriticalCoordinateSizeBound width tokenCount :=
    (natSize_le_of_le (Nat.le_refl emptyBoundarySize)).trans
      (hemptyBoundarySizeRaw'.trans htokenBound)
  have hresultBoolSizeBound :
      Nat.size (compactAdditiveBoolTag
        (compactCutRuleCheck
          (Gamma, formula, (leftConclusion, leftValid),
            rightConclusion, rightValid))) ≤
        compactNumericExsCutCriticalCoordinateSizeBound width tokenCount := by
    have hbool : Nat.size (compactAdditiveBoolTag
        (compactCutRuleCheck
          (Gamma, formula, (leftConclusion, leftValid),
            rightConclusion, rightValid))) ≤ 1 := by
      cases compactCutRuleCheck
          (Gamma, formula, (leftConclusion, leftValid),
            rightConclusion, rightValid) <;>
        simp [compactAdditiveBoolTag]
    exact hbool.trans (htokenCount.trans htokenBound)
  let ruleWitness := compactNumericVerifierExsCutCombineRuleWitness
    rightConclusion.length rightGammaBoundary rightBoolValue
    leftConclusion.length leftGammaBoundary leftBoolValue
    formulaBoundary formulaBoundarySize
    transformedStart transformedFinish transformedBoundary
    ((compactFormulaNegationExact 0 formula).getD []).length
      transformedBoundarySize
    transformStateBoundary (compactSyntaxRunFuelBound formula + 1)
    emptyStart emptyFinish emptyBoundary emptyBoundarySize
    transformTableWidth (2 ^ transformTableWidth)
    (compactAdditiveBoolTag
      (compactCutRuleCheck
        (Gamma, formula, (leftConclusion, leftValid),
          rightConclusion, rightValid)))
  have hfieldBounds :
      CompactNumericVerifierExsCutCombineRuleFieldSizeBounds
        rightConclusion.length rightGammaBoundary rightBoolValue
        leftConclusion.length leftGammaBoundary leftBoolValue
        formulaBoundary formulaBoundarySize
        transformedStart transformedFinish transformedBoundary
        ((compactFormulaNegationExact 0 formula).getD []).length
          transformedBoundarySize
        transformStateBoundary (compactSyntaxRunFuelBound formula + 1)
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        transformTableWidth (2 ^ transformTableWidth)
        (compactAdditiveBoolTag
          (compactCutRuleCheck
            (Gamma, formula, (leftConclusion, leftValid),
              rightConclusion, rightValid)))
        (compactNumericExsCutCombineRuleCoordinateSizeBound
          width tokenCount) := by
    exact
      { rightGammaCount := hrightCountSizeBound
        rightGammaBoundary := hrightBoundarySizeBound
        rightBoolValue := hrightBoolSizeBound
        leftGammaCount := hleftCountSizeBound
        leftGammaBoundary := hleftBoundarySizeBound
        leftBoolValue := hleftBoolSizeBound
        formulaBoundary := hformulaBoundarySizeBound
        formulaBoundarySize := hformulaBoundarySizeFieldBound
        transformedStart := htransformedStartSizeBound
        transformedFinish := htransformedFinishSizeBound
        transformedBoundary := htransformedBoundarySizeBound
        transformedCount := htransformedCountSizeBound
        transformedBoundarySize := htransformedBoundarySizeFieldBound
        transformStateBoundary := hcritical.transformStateBoundary_size
        transformStateCount := htransformStateCountSizeBound
        emptyStart := hemptyStartSizeBound
        emptyFinish := hemptyFinishSizeBound
        emptyBoundary := hemptyBoundarySizeBound
        emptyBoundarySize := hemptyBoundarySizeFieldBound
        transformTableWidth := hcritical.transformTableWidth_size
        transformValueBound := hcritical.transformValueBound_size
        resultBoolValue := hresultBoolSizeBound }
  refine ⟨ruleWitness, ?_, ?_⟩
  · exact CompactNumericVerifierCombineStateGraph.of_exs_cut_rows
      hframeSaved hlocalSaved
  · refine
      { critical := by
          simpa [ruleWitness,
            compactNumericVerifierExsCutCombineRuleWitness] using hcritical
        coordinate_size := ?_ }
    intro coordinate
    simpa [ruleWitness,
      compactNumericExsCutCombineRuleCoordinateSizeBound] using
        hfieldBounds.coordinate coordinate

#print axioms CompactNumericVerifierCombineStateGraph.exists_of_exs_frame
#print axioms CompactNumericVerifierCombineStateGraph.exists_of_cut_frame

end FoundationCompactNumericListedDirectVerifierCombineExsCutStateGraphCompleteness
