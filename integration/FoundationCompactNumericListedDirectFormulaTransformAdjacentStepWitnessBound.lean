import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessTable
import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula

/-!
# Public bounds for formula-transform adjacent-step witnesses

The public width contains the token-cell width, the largest possible boundary
table area, and a fixed allowance for tags and successor values.  The first
endpoint below proves that all fourteen coordinates of a transform state row
fit this width directly from its checked core graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectCompletedOutputSameRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxInvalidRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformTraceInstallation
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound

def compactFormulaTransformAdjacentStepPublicWidth
    (width tokenCount : Nat) : Nat :=
  width + compactBinaryNatStreamStepWitnessPublicWidth tokenCount

def compactFormulaTransformCanonicalTableWidthBound
    (width tokenCount fuel : Nat) : Nat :=
  fuel * compactFormulaTransformAdjacentStepWitnessColumnCount *
      compactFormulaTransformAdjacentStepPublicWidth width tokenCount +
    (tokenCount + 1) * tokenCount +
    31 * compactFormulaTransformAdjacentStepPublicWidth width tokenCount

theorem compactFormulaTransformCanonicalTableWidthBound_mono_fuel
    (width tokenCount : Nat) {leftFuel rightFuel : Nat}
    (hfuel : leftFuel ≤ rightFuel) :
    compactFormulaTransformCanonicalTableWidthBound
        width tokenCount leftFuel ≤
      compactFormulaTransformCanonicalTableWidthBound
        width tokenCount rightFuel := by
  have hcolumns :
      leftFuel * compactFormulaTransformAdjacentStepWitnessColumnCount ≤
        rightFuel * compactFormulaTransformAdjacentStepWitnessColumnCount :=
    Nat.mul_le_mul_right
      compactFormulaTransformAdjacentStepWitnessColumnCount hfuel
  have hrows := Nat.mul_le_mul_right
    (compactFormulaTransformAdjacentStepPublicWidth width tokenCount)
    hcolumns
  unfold compactFormulaTransformCanonicalTableWidthBound
  omega

theorem width_le_compactFormulaTransformAdjacentStepPublicWidth
    (width tokenCount : Nat) :
    width ≤ compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
  simp [compactFormulaTransformAdjacentStepPublicWidth]

theorem streamWidth_le_compactFormulaTransformAdjacentStepPublicWidth
    (width tokenCount : Nat) :
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount ≤
      compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
  simp [compactFormulaTransformAdjacentStepPublicWidth]

theorem natSize_le_transformStepWidth_of_le_tokenCount
    {value width tokenCount : Nat} (hvalue : value ≤ tokenCount) :
    Nat.size value ≤
      compactFormulaTransformAdjacentStepPublicWidth width tokenCount :=
  (natSize_le_streamStepWidth_of_le_tokenCount hvalue).trans
    (streamWidth_le_compactFormulaTransformAdjacentStepPublicWidth
      width tokenCount)

theorem natSize_le_transformStepWidth_of_le_boundaryArea
    {value width tokenCount : Nat}
    (hvalue : value ≤ (tokenCount + 1) * tokenCount) :
    Nat.size value ≤
      compactFormulaTransformAdjacentStepPublicWidth width tokenCount :=
  (natSize_le_streamStepWidth_of_le_boundaryArea hvalue).trans
    (streamWidth_le_compactFormulaTransformAdjacentStepPublicWidth
      width tokenCount)

structure CompactFormulaTransformStateCoreCoordinateFits
    (width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) : Prop where
  start : Nat.size coordinates.start ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  finish : Nat.size coordinates.finish ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  parserFinish : Nat.size coordinates.parserFinish ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  parserTokensFinish : Nat.size coordinates.parserTokensFinish ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  parserTasksFinish : Nat.size coordinates.parserTasksFinish ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  parserTokensBoundary : Nat.size coordinates.parserTokensBoundary ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  parserTokensCount : Nat.size coordinates.parserTokensCount ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  parserTasksBoundary : Nat.size coordinates.parserTasksBoundary ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  parserTasksCount : Nat.size coordinates.parserTasksCount ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  outputBoundary : Nat.size coordinates.outputBoundary ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  outputCount : Nat.size coordinates.outputCount ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  parserTokensBoundarySize : Nat.size sizeWitness.parserTokensBoundarySize ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  parserTasksBoundarySize : Nat.size sizeWitness.parserTasksBoundarySize ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  outputBoundarySize : Nat.size sizeWitness.outputBoundarySize ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  finish_le_tokenCount : coordinates.finish ≤ tokenCount
  parserTokensCount_le_tokenCount : coordinates.parserTokensCount ≤ tokenCount
  parserTasksCount_le_tokenCount : coordinates.parserTasksCount ≤ tokenCount
  outputCount_le_tokenCount : coordinates.outputCount ≤ tokenCount

theorem CompactFormulaTransformStateCoreGraph.coordinateFits
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactFormulaTransformStateRowCoordinates}
    {sizeWitness : CompactFormulaTransformStateCoreSizeWitness}
    (hgraph : CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    CompactFormulaTransformStateCoreCoordinateFits
      width tokenCount coordinates sizeWitness := by
  rcases hgraph with
    ⟨houter, hparser, houtputLayout, _houtputRows,
      houtputSizeEq, houtputSize⟩
  rcases hparser with
    ⟨hparserOuter, htokensLayout, _htokensRows,
      hparserInner, htasksLayout, _htasksRows,
      htokensSizeEq, htokensSize,
      htasksSizeEq, htasksSize⟩
  have hfinish : coordinates.finish ≤ tokenCount := houter.2.2
  have hparserFinish : coordinates.parserFinish ≤ tokenCount :=
    (Nat.le_of_lt houter.2.1).trans hfinish
  have hstart : coordinates.start ≤ tokenCount :=
    (Nat.le_of_lt houter.1).trans hparserFinish
  have htokensFinish : coordinates.parserTokensFinish ≤ tokenCount :=
    (Nat.le_of_lt hparserOuter.2.1).trans hparserFinish
  have htasksFinish : coordinates.parserTasksFinish ≤ tokenCount :=
    (Nat.le_of_lt hparserInner.2.1).trans hparserFinish
  have htokensCount : coordinates.parserTokensCount ≤ tokenCount :=
    structuredListLayout_count_le_tokenCount htokensLayout
  have htasksCount : coordinates.parserTasksCount ≤ tokenCount :=
    structuredListLayout_count_le_tokenCount htasksLayout
  have houtputCount : coordinates.outputCount ≤ tokenCount :=
    structuredListLayout_count_le_tokenCount houtputLayout
  have htokensArea : sizeWitness.parserTokensBoundarySize ≤
      (tokenCount + 1) * tokenCount :=
    htokensSize.trans (listBoundaryArea_le_publicArea htokensCount)
  have htasksArea : sizeWitness.parserTasksBoundarySize ≤
      (tokenCount + 1) * tokenCount :=
    htasksSize.trans (listBoundaryArea_le_publicArea htasksCount)
  have houtputArea : sizeWitness.outputBoundarySize ≤
      (tokenCount + 1) * tokenCount :=
    houtputSize.trans (listBoundaryArea_le_publicArea houtputCount)
  have htokensSizeEq' : sizeWitness.parserTokensBoundarySize =
      Nat.size coordinates.parserTokensBoundary := by
    simpa [CompactFormulaTransformStateRowCoordinates.parser,
      CompactFormulaTransformStateCoreSizeWitness.parser] using htokensSizeEq
  have htasksSizeEq' : sizeWitness.parserTasksBoundarySize =
      Nat.size coordinates.parserTasksBoundary := by
    simpa [CompactFormulaTransformStateRowCoordinates.parser,
      CompactFormulaTransformStateCoreSizeWitness.parser] using htasksSizeEq
  refine
    { start := natSize_le_transformStepWidth_of_le_tokenCount hstart
      finish := natSize_le_transformStepWidth_of_le_tokenCount hfinish
      parserFinish :=
        natSize_le_transformStepWidth_of_le_tokenCount hparserFinish
      parserTokensFinish :=
        natSize_le_transformStepWidth_of_le_tokenCount htokensFinish
      parserTasksFinish :=
        natSize_le_transformStepWidth_of_le_tokenCount htasksFinish
      parserTokensBoundary := ?_
      parserTokensCount :=
        natSize_le_transformStepWidth_of_le_tokenCount htokensCount
      parserTasksBoundary := ?_
      parserTasksCount :=
        natSize_le_transformStepWidth_of_le_tokenCount htasksCount
      outputBoundary := ?_
      outputCount :=
        natSize_le_transformStepWidth_of_le_tokenCount houtputCount
      parserTokensBoundarySize :=
        natSize_le_transformStepWidth_of_le_boundaryArea htokensArea
      parserTasksBoundarySize :=
        natSize_le_transformStepWidth_of_le_boundaryArea htasksArea
      outputBoundarySize :=
        natSize_le_transformStepWidth_of_le_boundaryArea houtputArea
      finish_le_tokenCount := hfinish
      parserTokensCount_le_tokenCount := htokensCount
      parserTasksCount_le_tokenCount := htasksCount
      outputCount_le_tokenCount := houtputCount }
  · rw [← htokensSizeEq']
    exact htokensArea.trans
      (boundaryArea_le_streamStepWidth tokenCount |>.trans
        (streamWidth_le_compactFormulaTransformAdjacentStepPublicWidth
          width tokenCount))
  · rw [← htasksSizeEq']
    exact htasksArea.trans
      (boundaryArea_le_streamStepWidth tokenCount |>.trans
        (streamWidth_le_compactFormulaTransformAdjacentStepPublicWidth
          width tokenCount))
  · rw [← houtputSizeEq]
    exact houtputArea.trans
      (boundaryArea_le_streamStepWidth tokenCount |>.trans
        (streamWidth_le_compactFormulaTransformAdjacentStepPublicWidth
          width tokenCount))

theorem CompactFormulaTransformStateAtRows.coordinateFits
    {tokenTable width tokenCount stateBoundary stateCount index : Nat}
    {coordinates : CompactFormulaTransformStateRowCoordinates}
    {sizeWitness : CompactFormulaTransformStateCoreSizeWitness}
    (hrows : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount index
        coordinates sizeWitness) :
    CompactFormulaTransformStateCoreCoordinateFits
      width tokenCount coordinates sizeWitness :=
  CompactFormulaTransformStateCoreGraph.coordinateFits hrows.2.2.2

theorem CompactAdditiveNatListAtRows.value_size_le_transformStepWidth
    {tokenTable width tokenCount boundaryTable count index value : Nat}
    (hrows : CompactAdditiveNatListAtRows
      tokenTable width tokenCount boundaryTable count index value) :
    Nat.size value ≤
      compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
  rcases hrows with
    ⟨_hindex, left, _hleft, right, _hright,
      _hleftEntry, _hrightEntry, hcell⟩
  exact hcell.2.2.1.trans
    (width_le_compactFormulaTransformAdjacentStepPublicWidth width tokenCount)

structure CompactSyntaxTaskUnconsCoordinateFits
    (width tokenCount tailBoundary tailCount tailBoundarySize
      headKind headBinderArity headRepeatCount : Nat) : Prop where
  tailBoundary_size : Nat.size tailBoundary ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  tailCount_size : Nat.size tailCount ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  tailBoundarySize_size : Nat.size tailBoundarySize ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  headKind_size : Nat.size headKind ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  headBinderArity_size : Nat.size headBinderArity ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  headRepeatCount_size : Nat.size headRepeatCount ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  tailCount_le_tokenCount : tailCount ≤ tokenCount

theorem CompactAdditiveSyntaxTaskListUnconsRowsWithSize.coordinateFits
    {tokenTable width tokenCount sourceBoundary sourceCount
      tailBoundary tailCount tailBoundarySize
      headKind headBinderArity headRepeatCount : Nat}
    (hsourceCount : sourceCount ≤ tokenCount)
    (hrows : CompactAdditiveSyntaxTaskListUnconsRowsWithSize
      tokenTable width tokenCount sourceBoundary sourceCount
        tailBoundary tailCount tailBoundarySize
        headKind headBinderArity headRepeatCount) :
    CompactSyntaxTaskUnconsCoordinateFits width tokenCount
      tailBoundary tailCount tailBoundarySize
        headKind headBinderArity headRepeatCount := by
  rcases hrows with
    ⟨_hsourcePositive, hdrop, _htailRows, hcons,
      htailSizeEq, htailSize⟩
  have hdropCount : sourceCount = 1 + tailCount := hdrop.2.1
  have htailCountSource : tailCount ≤ sourceCount := by omega
  have htailCount : tailCount ≤ tokenCount :=
    htailCountSource.trans hsourceCount
  have htailArea : tailBoundarySize ≤ (tokenCount + 1) * tokenCount :=
    htailSize.trans (listBoundaryArea_le_publicArea htailCount)
  rcases hcons.2.1 with
    ⟨targetLeft, _htargetLeft, targetRight, _htargetRight,
      _hleftEntry, _hrightEntry,
      binderStart, countStart, hkindCell, hbinderCell, hrepeatCell⟩
  refine
    { tailBoundary_size := ?_
      tailCount_size := natSize_le_transformStepWidth_of_le_tokenCount htailCount
      tailBoundarySize_size :=
        natSize_le_transformStepWidth_of_le_boundaryArea htailArea
      headKind_size := hkindCell.2.2.1.trans
        (width_le_compactFormulaTransformAdjacentStepPublicWidth
          width tokenCount)
      headBinderArity_size := hbinderCell.2.2.1.trans
        (width_le_compactFormulaTransformAdjacentStepPublicWidth
          width tokenCount)
      headRepeatCount_size := hrepeatCell.2.2.1.trans
        (width_le_compactFormulaTransformAdjacentStepPublicWidth
          width tokenCount)
      tailCount_le_tokenCount := htailCount }
  rw [← htailSizeEq]
  exact htailArea.trans
    (boundaryArea_le_streamStepWidth tokenCount |>.trans
      (streamWidth_le_compactFormulaTransformAdjacentStepPublicWidth
        width tokenCount))

structure CompactUnifiedParserSyntaxStepWitnessFits
    (width tokenCount : Nat)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates) : Prop where
  slot0_size : Nat.size witness.slot0 ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  slot1_size : Nat.size witness.slot1 ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  slot2_size : Nat.size witness.slot2 ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  slot3_size : Nat.size witness.slot3 ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  slot4_size : Nat.size witness.slot4 ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  slot5_size : Nat.size witness.slot5 ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount
  slot6_size : Nat.size witness.slot6 ≤
    compactFormulaTransformAdjacentStepPublicWidth width tokenCount

def compactUnifiedParserSyntaxStepZeroWitness :
    CompactUnifiedParserSyntaxStepWitnessCoordinates :=
  { slot0 := 0
    slot1 := 0
    slot2 := 0
    slot3 := 0
    slot4 := 0
    slot5 := 0
    slot6 := 0 }

theorem compactUnifiedParserSyntaxStepZeroWitness_fits
    (width tokenCount : Nat) :
    CompactUnifiedParserSyntaxStepWitnessFits width tokenCount
      compactUnifiedParserSyntaxStepZeroWitness := by
  constructor <;>
    simp [compactUnifiedParserSyntaxStepZeroWitness,
      compactFormulaTransformAdjacentStepPublicWidth,
      compactBinaryNatStreamStepWitnessPublicWidth]

theorem CompactUnifiedParserDoneGraphRows.exists_fittingUnifiedWitness
    {tokenTable width tokenCount : Nat}
    {current next : CompactUnifiedParserStateRowCoordinates}
    {doneWitness : CompactUnifiedParserDoneWitnessCoordinates}
    (hrows : CompactUnifiedParserDoneGraphRows
      tokenTable width tokenCount current next doneWitness) :
    ∃ witness : CompactUnifiedParserSyntaxStepWitnessCoordinates,
      CompactUnifiedParserDoneGraphRows
        tokenTable width tokenCount current next witness.done ∧
      CompactUnifiedParserSyntaxStepWitnessFits width tokenCount witness := by
  rcases hrows with ⟨htokens, htasks, hfailed | hcompleted⟩
  · refine ⟨compactUnifiedParserSyntaxStepZeroWitness, ?_,
      compactUnifiedParserSyntaxStepZeroWitness_fits width tokenCount⟩
    exact ⟨htokens, htasks, Or.inl hfailed⟩
  · rcases hcompleted with
      ⟨hcompleted, hsourceSizeEq, hsourceSize,
        htargetSizeEq, htargetSize⟩
    rcases hcompleted with
      ⟨_hsourcePrefix, hsourceLayout,
        _htargetPrefix, htargetLayout, _houtputRows⟩
    have hcount : doneWitness.outputCount ≤ tokenCount :=
      structuredListLayout_count_le_tokenCount hsourceLayout
    have hsourceStart : doneWitness.sourceOutputStart ≤ tokenCount :=
      Nat.le_of_lt (structuredListLayout_start_lt_tokenCount hsourceLayout)
    have htargetStart : doneWitness.targetOutputStart ≤ tokenCount :=
      Nat.le_of_lt (structuredListLayout_start_lt_tokenCount htargetLayout)
    have hsourceArea : doneWitness.sourceOutputBoundarySize ≤
        (tokenCount + 1) * tokenCount :=
      hsourceSize.trans (listBoundaryArea_le_publicArea hcount)
    have htargetArea : doneWitness.targetOutputBoundarySize ≤
        (tokenCount + 1) * tokenCount :=
      htargetSize.trans (listBoundaryArea_le_publicArea hcount)
    let witness :=
      CompactUnifiedParserSyntaxStepWitnessCoordinates.ofDone doneWitness
    refine ⟨witness, ?_, ?_⟩
    · simpa [witness] using
        (show CompactUnifiedParserDoneGraphRows
          tokenTable width tokenCount current next doneWitness from
            ⟨htokens, htasks, Or.inr
              ⟨⟨_hsourcePrefix, hsourceLayout,
                  _htargetPrefix, htargetLayout, _houtputRows⟩,
                hsourceSizeEq, hsourceSize,
                htargetSizeEq, htargetSize⟩⟩)
    · refine
        { slot0_size :=
            natSize_le_transformStepWidth_of_le_tokenCount hsourceStart
          slot1_size := ?_
          slot2_size :=
            natSize_le_transformStepWidth_of_le_boundaryArea hsourceArea
          slot3_size :=
            natSize_le_transformStepWidth_of_le_tokenCount htargetStart
          slot4_size := ?_
          slot5_size :=
            natSize_le_transformStepWidth_of_le_boundaryArea htargetArea
          slot6_size :=
            natSize_le_transformStepWidth_of_le_tokenCount hcount }
      · change Nat.size doneWitness.sourceOutputBoundary ≤ _
        rw [← hsourceSizeEq]
        exact hsourceArea.trans
          (boundaryArea_le_streamStepWidth tokenCount |>.trans
            (streamWidth_le_compactFormulaTransformAdjacentStepPublicWidth
              width tokenCount))
      · change Nat.size doneWitness.targetOutputBoundary ≤ _
        rw [← htargetSizeEq]
        exact htargetArea.trans
          (boundaryArea_le_streamStepWidth tokenCount |>.trans
            (streamWidth_le_compactFormulaTransformAdjacentStepPublicWidth
              width tokenCount))

theorem CompactUnifiedParserEmptyGraphRows.exists_fittingUnifiedWitness
    {tokenTable width tokenCount : Nat}
    {current next : CompactUnifiedParserStateRowCoordinates}
    {emptyWitness : CompactUnifiedParserEmptyWitnessCoordinates}
    (hrows : CompactUnifiedParserEmptyGraphRows
      tokenTable width tokenCount current next emptyWitness) :
    ∃ witness : CompactUnifiedParserSyntaxStepWitnessCoordinates,
      CompactUnifiedParserEmptyGraphRows
        tokenTable width tokenCount current next witness.empty ∧
      CompactUnifiedParserSyntaxStepWitnessFits width tokenCount witness := by
  rcases hrows with
    ⟨hcurrentCount, hnextCount, hcurrentRunning,
      htokenRows, hcompleted⟩
  rcases hcompleted with ⟨hcompleted, hsizeEq, hsize⟩
  rcases hcompleted with
    ⟨_hprefix, hlayout, _hrows⟩
  have hcount : current.tokensCount ≤ tokenCount :=
    structuredListLayout_count_le_tokenCount hlayout
  have hstart : emptyWitness.targetOutputStart ≤ tokenCount :=
    Nat.le_of_lt (structuredListLayout_start_lt_tokenCount hlayout)
  have harea : emptyWitness.targetOutputBoundarySize ≤
      (tokenCount + 1) * tokenCount :=
    hsize.trans (listBoundaryArea_le_publicArea hcount)
  let witness :=
    CompactUnifiedParserSyntaxStepWitnessCoordinates.ofEmpty emptyWitness
  refine ⟨witness, ?_, ?_⟩
  · simpa [witness] using
      (show CompactUnifiedParserEmptyGraphRows
        tokenTable width tokenCount current next emptyWitness from
          ⟨hcurrentCount, hnextCount, hcurrentRunning, htokenRows,
            ⟨⟨_hprefix, hlayout, _hrows⟩, hsizeEq, hsize⟩⟩)
  · refine
      { slot0_size := natSize_le_transformStepWidth_of_le_tokenCount hstart
        slot1_size := ?_
        slot2_size := natSize_le_transformStepWidth_of_le_boundaryArea harea
        slot3_size := by simp [witness,
          CompactUnifiedParserSyntaxStepWitnessCoordinates.ofEmpty]
        slot4_size := by simp [witness,
          CompactUnifiedParserSyntaxStepWitnessCoordinates.ofEmpty]
        slot5_size := by simp [witness,
          CompactUnifiedParserSyntaxStepWitnessCoordinates.ofEmpty]
        slot6_size := by simp [witness,
          CompactUnifiedParserSyntaxStepWitnessCoordinates.ofEmpty] }
    change Nat.size emptyWitness.targetOutputBoundary ≤ _
    rw [← hsizeEq]
    exact harea.trans
      (boundaryArea_le_streamStepWidth tokenCount |>.trans
        (streamWidth_le_compactFormulaTransformAdjacentStepPublicWidth
          width tokenCount))

theorem CompactUnifiedParserSyntaxRepeatRows.exists_fittingUnifiedWitness
    {tokenTable width tokenCount : Nat}
    {current next : CompactUnifiedParserStateRowCoordinates}
    {binderArity repeatCount : Nat}
    {repeatWitness : CompactSyntaxRepeatTaskWitnessCoordinates}
    (hcurrentCount : current.tasksCount ≤ tokenCount)
    (hrows : CompactUnifiedParserSyntaxRepeatRows
      tokenTable width tokenCount current next
        binderArity repeatCount repeatWitness) :
    ∃ witness : CompactUnifiedParserSyntaxStepWitnessCoordinates,
      CompactUnifiedParserSyntaxRepeatRows
        tokenTable width tokenCount current next
          witness.slot0 witness.slot1 witness.repeat ∧
      CompactUnifiedParserSyntaxStepWitnessFits width tokenCount witness := by
  rcases hrows with
    ⟨hcurrentRunning, hnextRunning, htokenRows, huncons,
      hzero | hpositive⟩
  · have hunconsFit :=
      CompactAdditiveSyntaxTaskListUnconsRowsWithSize.coordinateFits
        hcurrentCount huncons
    let normalizedRepeat : CompactSyntaxRepeatTaskWitnessCoordinates :=
      { tailBoundary := repeatWitness.tailBoundary
        tailCount := repeatWitness.tailCount
        tailBoundarySize := repeatWitness.tailBoundarySize
        decrementedCount := 0 }
    let witness := CompactUnifiedParserSyntaxStepWitnessCoordinates.ofRepeat
      binderArity repeatCount normalizedRepeat
    refine ⟨witness, ?_, ?_⟩
    · simpa [witness, normalizedRepeat] using
        (show CompactUnifiedParserSyntaxRepeatRows
          tokenTable width tokenCount current next
            binderArity repeatCount normalizedRepeat from
          ⟨hcurrentRunning, hnextRunning, htokenRows, by
            simpa [normalizedRepeat] using huncons,
            Or.inl ⟨hzero.1, by simpa [normalizedRepeat] using hzero.2⟩⟩)
    · exact
        { slot0_size := hunconsFit.headBinderArity_size
          slot1_size := hunconsFit.headRepeatCount_size
          slot2_size := hunconsFit.tailBoundary_size
          slot3_size := hunconsFit.tailCount_size
          slot4_size := hunconsFit.tailBoundarySize_size
          slot5_size := by simp [witness, normalizedRepeat,
            CompactUnifiedParserSyntaxStepWitnessCoordinates.ofRepeat]
          slot6_size := by simp [witness, normalizedRepeat,
            CompactUnifiedParserSyntaxStepWitnessCoordinates.ofRepeat] }
  · have hunconsFit :=
      CompactAdditiveSyntaxTaskListUnconsRowsWithSize.coordinateFits
        hcurrentCount huncons
    have hdecremented : repeatWitness.decrementedCount ≤ repeatCount := by
      omega
    have hdecrementedSize : Nat.size repeatWitness.decrementedCount ≤
        compactFormulaTransformAdjacentStepPublicWidth width tokenCount :=
      (Nat.size_le_size hdecremented).trans
        hunconsFit.headRepeatCount_size
    let witness := CompactUnifiedParserSyntaxStepWitnessCoordinates.ofRepeat
      binderArity repeatCount repeatWitness
    refine ⟨witness, ?_, ?_⟩
    · simpa [witness] using
        (show CompactUnifiedParserSyntaxRepeatRows
          tokenTable width tokenCount current next
            binderArity repeatCount repeatWitness from
          ⟨hcurrentRunning, hnextRunning, htokenRows, huncons,
            Or.inr hpositive⟩)
    · exact
        { slot0_size := hunconsFit.headBinderArity_size
          slot1_size := hunconsFit.headRepeatCount_size
          slot2_size := hunconsFit.tailBoundary_size
          slot3_size := hunconsFit.tailCount_size
          slot4_size := hunconsFit.tailBoundarySize_size
          slot5_size := hdecrementedSize
          slot6_size := by simp [witness,
            CompactUnifiedParserSyntaxStepWitnessCoordinates.ofRepeat] }

theorem CompactUnifiedParserSyntaxInvalidRows.exists_fittingUnifiedWitness
    {tokenTable width tokenCount : Nat}
    {current next : CompactUnifiedParserStateRowCoordinates}
    {invalidWitness : CompactSyntaxInvalidTaskWitnessCoordinates}
    (hcurrentCount : current.tasksCount ≤ tokenCount)
    (hrows : CompactUnifiedParserSyntaxInvalidRows
      tokenTable width tokenCount current next invalidWitness) :
    ∃ witness : CompactUnifiedParserSyntaxStepWitnessCoordinates,
      CompactUnifiedParserSyntaxInvalidRows
        tokenTable width tokenCount current next witness.invalid ∧
      CompactUnifiedParserSyntaxStepWitnessFits width tokenCount witness := by
  rcases hrows with
    ⟨hcurrentRunning, huncons, hzero, hone, htwo, hfailure⟩
  have hunconsFit :=
    CompactAdditiveSyntaxTaskListUnconsRowsWithSize.coordinateFits
      hcurrentCount huncons
  let witness :=
    CompactUnifiedParserSyntaxStepWitnessCoordinates.ofInvalid invalidWitness
  refine ⟨witness, ?_, ?_⟩
  · simpa [witness] using
      (show CompactUnifiedParserSyntaxInvalidRows
        tokenTable width tokenCount current next invalidWitness from
        ⟨hcurrentRunning, huncons, hzero, hone, htwo, hfailure⟩)
  · exact
      { slot0_size := hunconsFit.tailBoundary_size
        slot1_size := hunconsFit.tailCount_size
        slot2_size := hunconsFit.tailBoundarySize_size
        slot3_size := hunconsFit.headKind_size
        slot4_size := hunconsFit.headBinderArity_size
        slot5_size := hunconsFit.headRepeatCount_size
        slot6_size := by simp [witness,
          CompactUnifiedParserSyntaxStepWitnessCoordinates.ofInvalid] }

theorem CompactUnifiedParserSyntaxTermRows.exists_fittingUnifiedWitness
    {tokenTable width tokenCount : Nat}
    {current next : CompactUnifiedParserStateRowCoordinates}
    {binderArity : Nat}
    {termWitness : CompactSyntaxTermTaskWitnessCoordinates}
    (hcurrentTasksCount : current.tasksCount ≤ tokenCount)
    (hrows : CompactUnifiedParserSyntaxTermRows
      tokenTable width tokenCount current next binderArity termWitness) :
    ∃ witness : CompactUnifiedParserSyntaxStepWitnessCoordinates,
      CompactUnifiedParserSyntaxTermRows
        tokenTable width tokenCount current next witness.slot0 witness.term ∧
      CompactUnifiedParserSyntaxStepWitnessFits width tokenCount witness := by
  rcases hrows with ⟨hcurrentRunning, huncons, hshort | henough⟩
  · have hunconsFit :=
      CompactAdditiveSyntaxTaskListUnconsRowsWithSize.coordinateFits
        hcurrentTasksCount huncons
    let normalizedTerm : CompactSyntaxTermTaskWitnessCoordinates :=
      { tailBoundary := termWitness.tailBoundary
        tailCount := termWitness.tailCount
        tailBoundarySize := termWitness.tailBoundarySize
        tag := 0
        argument := 0
        functionCode := 0 }
    let witness := CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm
      binderArity normalizedTerm
    refine ⟨witness, ?_, ?_⟩
    · simpa [witness, normalizedTerm] using
        (show CompactUnifiedParserSyntaxTermRows
          tokenTable width tokenCount current next binderArity normalizedTerm from
          ⟨hcurrentRunning, by simpa [normalizedTerm] using huncons,
            Or.inl ⟨hshort.1, by simpa [normalizedTerm] using hshort.2⟩⟩)
    · exact
        { slot0_size := hunconsFit.headBinderArity_size
          slot1_size := hunconsFit.tailBoundary_size
          slot2_size := hunconsFit.tailCount_size
          slot3_size := hunconsFit.tailBoundarySize_size
          slot4_size := by simp [witness, normalizedTerm,
            CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm]
          slot5_size := by simp [witness, normalizedTerm,
            CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm]
          slot6_size := by simp [witness, normalizedTerm,
            CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm] }
  · rcases henough with ⟨henoughCount, htagRows, hargumentRows, hcontrol⟩
    have hunconsFit :=
      CompactAdditiveSyntaxTaskListUnconsRowsWithSize.coordinateFits
        hcurrentTasksCount huncons
    have htagSize :=
      CompactAdditiveNatListAtRows.value_size_le_transformStepWidth htagRows
    have hargumentSize :=
      CompactAdditiveNatListAtRows.value_size_le_transformStepWidth hargumentRows
    have hzeroSize : Nat.size 0 ≤
        compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
      simp [compactFormulaTransformAdjacentStepPublicWidth,
        compactBinaryNatStreamStepWitnessPublicWidth]
    let normalizedTerm (functionCode : Nat) :
        CompactSyntaxTermTaskWitnessCoordinates :=
      { tailBoundary := termWitness.tailBoundary
        tailCount := termWitness.tailCount
        tailBoundarySize := termWitness.tailBoundarySize
        tag := termWitness.tag
        argument := termWitness.argument
        functionCode := functionCode }
    let unified (functionCode : Nat) :=
      CompactUnifiedParserSyntaxStepWitnessCoordinates.ofTerm
        binderArity (normalizedTerm functionCode)
    have hunifiedFits (functionCode : Nat)
        (hfunctionCode : Nat.size functionCode ≤
          compactFormulaTransformAdjacentStepPublicWidth width tokenCount) :
        CompactUnifiedParserSyntaxStepWitnessFits width tokenCount
          (unified functionCode) :=
      { slot0_size := hunconsFit.headBinderArity_size
        slot1_size := hunconsFit.tailBoundary_size
        slot2_size := hunconsFit.tailCount_size
        slot3_size := hunconsFit.tailBoundarySize_size
        slot4_size := htagSize
        slot5_size := hargumentSize
        slot6_size := hfunctionCode }
    rcases hcontrol with htagZero | htagOne | htagTwo | htagInvalid
    · refine ⟨unified 0, ?_, hunifiedFits 0 hzeroSize⟩
      simpa [unified, normalizedTerm] using
        (show CompactUnifiedParserSyntaxTermRows
          tokenTable width tokenCount current next binderArity
            (normalizedTerm 0) from
          ⟨hcurrentRunning, by simpa [normalizedTerm] using huncons,
            Or.inr ⟨henoughCount,
              by simpa [normalizedTerm] using htagRows,
              by simpa [normalizedTerm] using hargumentRows,
              Or.inl (by simpa [normalizedTerm] using htagZero)⟩⟩)
    · refine ⟨unified 0, ?_, hunifiedFits 0 hzeroSize⟩
      simpa [unified, normalizedTerm] using
        (show CompactUnifiedParserSyntaxTermRows
          tokenTable width tokenCount current next binderArity
            (normalizedTerm 0) from
          ⟨hcurrentRunning, by simpa [normalizedTerm] using huncons,
            Or.inr ⟨henoughCount,
              by simpa [normalizedTerm] using htagRows,
              by simpa [normalizedTerm] using hargumentRows,
              Or.inr (Or.inl (by simpa [normalizedTerm] using htagOne))⟩⟩)
    · rcases htagTwo with ⟨htagValue, hshortFunction | henoughFunction⟩
      · refine ⟨unified 0, ?_, hunifiedFits 0 hzeroSize⟩
        simpa [unified, normalizedTerm] using
          (show CompactUnifiedParserSyntaxTermRows
            tokenTable width tokenCount current next binderArity
              (normalizedTerm 0) from
            ⟨hcurrentRunning, by simpa [normalizedTerm] using huncons,
              Or.inr ⟨henoughCount,
                by simpa [normalizedTerm] using htagRows,
                by simpa [normalizedTerm] using hargumentRows,
                Or.inr (Or.inr (Or.inl
                  ⟨by simpa [normalizedTerm] using htagValue,
                    Or.inl (by simpa [normalizedTerm] using
                      hshortFunction)⟩))⟩⟩)
      · rcases henoughFunction with
          ⟨henoughFunctionCount, hfunctionRows, hvalidity⟩
        have hfunctionSize :=
          CompactAdditiveNatListAtRows.value_size_le_transformStepWidth
            hfunctionRows
        refine ⟨unified termWitness.functionCode, ?_,
          hunifiedFits termWitness.functionCode hfunctionSize⟩
        simpa [unified, normalizedTerm] using
          (show CompactUnifiedParserSyntaxTermRows
            tokenTable width tokenCount current next binderArity
              (normalizedTerm termWitness.functionCode) from
            ⟨hcurrentRunning, by simpa [normalizedTerm] using huncons,
              Or.inr ⟨henoughCount, htagRows, hargumentRows,
                Or.inr (Or.inr (Or.inl
                  ⟨htagValue, Or.inr
                    ⟨henoughFunctionCount, hfunctionRows, hvalidity⟩⟩))⟩⟩)
    · refine ⟨unified 0, ?_, hunifiedFits 0 hzeroSize⟩
      simpa [unified, normalizedTerm] using
        (show CompactUnifiedParserSyntaxTermRows
          tokenTable width tokenCount current next binderArity
            (normalizedTerm 0) from
          ⟨hcurrentRunning, by simpa [normalizedTerm] using huncons,
            Or.inr ⟨henoughCount,
              by simpa [normalizedTerm] using htagRows,
              by simpa [normalizedTerm] using hargumentRows,
              Or.inr (Or.inr (Or.inr
                (by simpa [normalizedTerm] using htagInvalid)))⟩⟩)

theorem CompactUnifiedParserSyntaxFormulaRows.exists_fittingUnifiedWitness
    {tokenTable width tokenCount : Nat}
    {current next : CompactUnifiedParserStateRowCoordinates}
    {binderArity : Nat}
    {formulaWitness : CompactSyntaxFormulaTaskWitnessCoordinates}
    (hcurrentTasksCount : current.tasksCount ≤ tokenCount)
    (hrows : CompactUnifiedParserSyntaxFormulaRows
      tokenTable width tokenCount current next binderArity formulaWitness) :
    ∃ witness : CompactUnifiedParserSyntaxStepWitnessCoordinates,
      CompactUnifiedParserSyntaxFormulaRows
        tokenTable width tokenCount current next witness.slot0 witness.formula ∧
      CompactUnifiedParserSyntaxStepWitnessFits width tokenCount witness := by
  rcases hrows with ⟨hcurrentRunning, huncons, hshort | henough⟩
  · have hunconsFit :=
      CompactAdditiveSyntaxTaskListUnconsRowsWithSize.coordinateFits
        hcurrentTasksCount huncons
    let normalizedFormula : CompactSyntaxFormulaTaskWitnessCoordinates :=
      { tailBoundary := formulaWitness.tailBoundary
        tailCount := formulaWitness.tailCount
        tailBoundarySize := formulaWitness.tailBoundarySize
        tag := 0
        relationArity := 0
        relationCode := 0 }
    let witness := CompactUnifiedParserSyntaxStepWitnessCoordinates.ofFormula
      binderArity normalizedFormula
    refine ⟨witness, ?_, ?_⟩
    · simpa [witness, normalizedFormula] using
        (show CompactUnifiedParserSyntaxFormulaRows
          tokenTable width tokenCount current next binderArity
            normalizedFormula from
          ⟨hcurrentRunning, by simpa [normalizedFormula] using huncons,
            Or.inl ⟨hshort.1,
              by simpa [normalizedFormula] using hshort.2⟩⟩)
    · exact
        { slot0_size := hunconsFit.headBinderArity_size
          slot1_size := hunconsFit.tailBoundary_size
          slot2_size := hunconsFit.tailCount_size
          slot3_size := hunconsFit.tailBoundarySize_size
          slot4_size := by simp [witness, normalizedFormula,
            CompactUnifiedParserSyntaxStepWitnessCoordinates.ofFormula]
          slot5_size := by simp [witness, normalizedFormula,
            CompactUnifiedParserSyntaxStepWitnessCoordinates.ofFormula]
          slot6_size := by simp [witness, normalizedFormula,
            CompactUnifiedParserSyntaxStepWitnessCoordinates.ofFormula] }
  · rcases henough with ⟨henoughCount, htagRows, hcontrol⟩
    have hunconsFit :=
      CompactAdditiveSyntaxTaskListUnconsRowsWithSize.coordinateFits
        hcurrentTasksCount huncons
    have htagSize :=
      CompactAdditiveNatListAtRows.value_size_le_transformStepWidth htagRows
    have hzeroSize : Nat.size 0 ≤
        compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
      simp [compactFormulaTransformAdjacentStepPublicWidth,
        compactBinaryNatStreamStepWitnessPublicWidth]
    let normalizedFormula (relationArity relationCode : Nat) :
        CompactSyntaxFormulaTaskWitnessCoordinates :=
      { tailBoundary := formulaWitness.tailBoundary
        tailCount := formulaWitness.tailCount
        tailBoundarySize := formulaWitness.tailBoundarySize
        tag := formulaWitness.tag
        relationArity := relationArity
        relationCode := relationCode }
    let unified (relationArity relationCode : Nat) :=
      CompactUnifiedParserSyntaxStepWitnessCoordinates.ofFormula
        binderArity (normalizedFormula relationArity relationCode)
    have hunifiedFits (relationArity relationCode : Nat)
        (haritySize : Nat.size relationArity ≤
          compactFormulaTransformAdjacentStepPublicWidth width tokenCount)
        (hcodeSize : Nat.size relationCode ≤
          compactFormulaTransformAdjacentStepPublicWidth width tokenCount) :
        CompactUnifiedParserSyntaxStepWitnessFits width tokenCount
          (unified relationArity relationCode) :=
      { slot0_size := hunconsFit.headBinderArity_size
        slot1_size := hunconsFit.tailBoundary_size
        slot2_size := hunconsFit.tailCount_size
        slot3_size := hunconsFit.tailBoundarySize_size
        slot4_size := htagSize
        slot5_size := haritySize
        slot6_size := hcodeSize }
    rcases hcontrol with
      hrelation | hatomic | hbinary | hquantifier | hinvalid
    · rcases hrelation with ⟨htagClass, hshortRelation | henoughRelation⟩
      · refine ⟨unified 0 0, ?_, hunifiedFits 0 0 hzeroSize hzeroSize⟩
        simpa [unified, normalizedFormula] using
          (show CompactUnifiedParserSyntaxFormulaRows
            tokenTable width tokenCount current next binderArity
              (normalizedFormula 0 0) from
            ⟨hcurrentRunning, by simpa [normalizedFormula] using huncons,
              Or.inr ⟨henoughCount,
                by simpa [normalizedFormula] using htagRows,
                Or.inl
                  ⟨by simpa [normalizedFormula] using htagClass,
                    Or.inl (by simpa [normalizedFormula] using
                      hshortRelation)⟩⟩⟩)
      · rcases henoughRelation with
          ⟨henoughRelationCount, harityRows, hcodeRows, hvalidity⟩
        have haritySize :=
          CompactAdditiveNatListAtRows.value_size_le_transformStepWidth
            harityRows
        have hcodeSize :=
          CompactAdditiveNatListAtRows.value_size_le_transformStepWidth
            hcodeRows
        refine ⟨unified formulaWitness.relationArity
            formulaWitness.relationCode, ?_,
          hunifiedFits formulaWitness.relationArity
            formulaWitness.relationCode haritySize hcodeSize⟩
        simpa [unified, normalizedFormula] using
          (show CompactUnifiedParserSyntaxFormulaRows
            tokenTable width tokenCount current next binderArity
              (normalizedFormula formulaWitness.relationArity
                formulaWitness.relationCode) from
            ⟨hcurrentRunning, huncons,
              Or.inr ⟨henoughCount, htagRows,
                Or.inl ⟨htagClass, Or.inr
                  ⟨henoughRelationCount, harityRows, hcodeRows,
                    hvalidity⟩⟩⟩⟩)
    · refine ⟨unified 0 0, ?_, hunifiedFits 0 0 hzeroSize hzeroSize⟩
      simpa [unified, normalizedFormula] using
        (show CompactUnifiedParserSyntaxFormulaRows
          tokenTable width tokenCount current next binderArity
            (normalizedFormula 0 0) from
          ⟨hcurrentRunning, by simpa [normalizedFormula] using huncons,
            Or.inr ⟨henoughCount,
              by simpa [normalizedFormula] using htagRows,
              Or.inr (Or.inl
                (by simpa [normalizedFormula] using hatomic))⟩⟩)
    · refine ⟨unified 0 0, ?_, hunifiedFits 0 0 hzeroSize hzeroSize⟩
      simpa [unified, normalizedFormula] using
        (show CompactUnifiedParserSyntaxFormulaRows
          tokenTable width tokenCount current next binderArity
            (normalizedFormula 0 0) from
          ⟨hcurrentRunning, by simpa [normalizedFormula] using huncons,
            Or.inr ⟨henoughCount,
              by simpa [normalizedFormula] using htagRows,
              Or.inr (Or.inr (Or.inl
                (by simpa [normalizedFormula] using hbinary)))⟩⟩)
    · refine ⟨unified 0 0, ?_, hunifiedFits 0 0 hzeroSize hzeroSize⟩
      simpa [unified, normalizedFormula] using
        (show CompactUnifiedParserSyntaxFormulaRows
          tokenTable width tokenCount current next binderArity
            (normalizedFormula 0 0) from
          ⟨hcurrentRunning, by simpa [normalizedFormula] using huncons,
            Or.inr ⟨henoughCount,
              by simpa [normalizedFormula] using htagRows,
              Or.inr (Or.inr (Or.inr (Or.inl
                (by simpa [normalizedFormula] using hquantifier))))⟩⟩)
    · refine ⟨unified 0 0, ?_, hunifiedFits 0 0 hzeroSize hzeroSize⟩
      simpa [unified, normalizedFormula] using
        (show CompactUnifiedParserSyntaxFormulaRows
          tokenTable width tokenCount current next binderArity
            (normalizedFormula 0 0) from
          ⟨hcurrentRunning, by simpa [normalizedFormula] using huncons,
            Or.inr ⟨henoughCount,
              by simpa [normalizedFormula] using htagRows,
              Or.inr (Or.inr (Or.inr (Or.inr
                (by simpa [normalizedFormula] using hinvalid))))⟩⟩)

theorem CompactUnifiedParserSyntaxStepRows.exists_fittingWitness
    {tokenTable width tokenCount : Nat}
    {current next : CompactUnifiedParserStateRowCoordinates}
    {witness : CompactUnifiedParserSyntaxStepWitnessCoordinates}
    (hcurrentTasksCount : current.tasksCount ≤ tokenCount)
    (hrows : CompactUnifiedParserSyntaxStepRows
      tokenTable width tokenCount current next witness) :
    ∃ fittingWitness : CompactUnifiedParserSyntaxStepWitnessCoordinates,
      CompactUnifiedParserSyntaxStepRows
        tokenTable width tokenCount current next fittingWitness ∧
      CompactUnifiedParserSyntaxStepWitnessFits
        width tokenCount fittingWitness := by
  rcases hrows with hdone | hempty | hrepeat | hterm | hformula | hinvalid
  · rcases CompactUnifiedParserDoneGraphRows.exists_fittingUnifiedWitness
      hdone with ⟨fittingWitness, hfitRows, hfit⟩
    exact ⟨fittingWitness, Or.inl hfitRows, hfit⟩
  · rcases CompactUnifiedParserEmptyGraphRows.exists_fittingUnifiedWitness
      hempty with ⟨fittingWitness, hfitRows, hfit⟩
    exact ⟨fittingWitness, Or.inr (Or.inl hfitRows), hfit⟩
  · rcases CompactUnifiedParserSyntaxRepeatRows.exists_fittingUnifiedWitness
      hcurrentTasksCount hrepeat with
      ⟨fittingWitness, hfitRows, hfit⟩
    exact ⟨fittingWitness, Or.inr (Or.inr (Or.inl hfitRows)), hfit⟩
  · rcases CompactUnifiedParserSyntaxTermRows.exists_fittingUnifiedWitness
      hcurrentTasksCount hterm with
      ⟨fittingWitness, hfitRows, hfit⟩
    exact ⟨fittingWitness,
      Or.inr (Or.inr (Or.inr (Or.inl hfitRows))), hfit⟩
  · rcases CompactUnifiedParserSyntaxFormulaRows.exists_fittingUnifiedWitness
      hcurrentTasksCount hformula with
      ⟨fittingWitness, hfitRows, hfit⟩
    exact ⟨fittingWitness,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hfitRows)))), hfit⟩
  · rcases CompactUnifiedParserSyntaxInvalidRows.exists_fittingUnifiedWitness
      hcurrentTasksCount hinvalid with
      ⟨fittingWitness, hfitRows, hfit⟩
    exact ⟨fittingWitness,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hfitRows)))), hfit⟩

theorem compactUnifiedParserSyntaxStepRows_complete_with_fit
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactUnifiedParserStateRowCoordinates}
    {current next : CompactUnifiedParserState}
    (hcurrent : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed current.2.1)
    (hstep : next = compactSyntaxParserStep current) :
    ∃ witness,
      CompactUnifiedParserSyntaxStepRows
        tokenTable width tokenCount currentCoordinates nextCoordinates witness ∧
      CompactUnifiedParserSyntaxStepWitnessFits width tokenCount witness := by
  rcases compactUnifiedParserSyntaxStepRows_complete
      hcurrent hnext hwell hstep with ⟨witness, hrows⟩
  have hcurrentTasksCount : currentCoordinates.tasksCount ≤ tokenCount :=
    structuredListLayout_count_le_tokenCount hcurrent.tasksLayout
  exact CompactUnifiedParserSyntaxStepRows.exists_fittingWitness
    hcurrentTasksCount hrows

theorem CompactFormulaTransformTermOutputRows.consumed_size_le
    {tokenTable width tokenCount : Nat}
    {current next : CompactFormulaTransformStateRowCoordinates}
    {mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount : Nat}
    (hcurrentCount : current.parserTokensCount ≤ tokenCount)
    (hrows : CompactFormulaTransformTermOutputRows
      tokenTable width tokenCount current next mode binderArity tag argument
        consumedCount witnessStart witnessFinish witnessCount) :
    Nat.size consumedCount ≤
      compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
  have hcount := hrows.1
  have hconsumed : consumedCount ≤ current.parserTokensCount := by
    omega
  exact natSize_le_transformStepWidth_of_le_tokenCount
    (hconsumed.trans hcurrentCount)

theorem CompactNegationFormulaTagGraph.mapped_size_le
    {width tokenCount tag mapped : Nat}
    (htagSize : Nat.size tag ≤
      compactFormulaTransformAdjacentStepPublicWidth width tokenCount)
    (hgraph : CompactNegationFormulaTagGraph tag mapped) :
    Nat.size mapped ≤
      compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
  rcases hgraph with hsmall | hlarge
  · rcases hsmall with ⟨htagSmall, hsuccessor | hpredecessor⟩
    · rcases hsuccessor with ⟨pair, _hpair, _htag, hmapped⟩
      have hmappedLe : mapped ≤ 8 := by omega
      exact (natSize_le_of_le hmappedLe).trans
        ((Nat.le_add_left 8 ((tokenCount + 1) * tokenCount)).trans
          (Nat.le_add_left
            ((tokenCount + 1) * tokenCount + 8) width))
    · rcases hpredecessor with ⟨pair, _hpair, _htag, hmapped⟩
      have hmappedLe : mapped ≤ 8 := by omega
      exact (natSize_le_of_le hmappedLe).trans
        ((Nat.le_add_left 8 ((tokenCount + 1) * tokenCount)).trans
          (Nat.le_add_left
            ((tokenCount + 1) * tokenCount + 8) width))
  · simpa [hlarge.2] using htagSize

theorem CompactFormulaTransformFormulaOutputRows.exists_fittingMappedHead
    {tokenTable width tokenCount : Nat}
    {current next : CompactFormulaTransformStateRowCoordinates}
    {mode tag consumedCount mappedHead : Nat}
    (hcurrentCount : current.parserTokensCount ≤ tokenCount)
    (htagSize : Nat.size tag ≤
      compactFormulaTransformAdjacentStepPublicWidth width tokenCount)
    (hrows : CompactFormulaTransformFormulaOutputRows
      tokenTable width tokenCount current next mode tag consumedCount mappedHead) :
    ∃ fittingMappedHead,
      CompactFormulaTransformFormulaOutputRows
        tokenTable width tokenCount current next mode tag consumedCount
          fittingMappedHead ∧
      Nat.size consumedCount ≤
        compactFormulaTransformAdjacentStepPublicWidth width tokenCount ∧
      Nat.size fittingMappedHead ≤
        compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
  rcases hrows with ⟨hcount, hzero | hpositive⟩
  · have hconsumed : consumedCount ≤ current.parserTokensCount := by omega
    have hconsumedSize := natSize_le_transformStepWidth_of_le_tokenCount
      (width := width)
      (hconsumed.trans hcurrentCount)
    refine ⟨0, ⟨hcount, Or.inl hzero⟩, hconsumedSize, ?_⟩
    simp [compactFormulaTransformAdjacentStepPublicWidth,
      compactBinaryNatStreamStepWitnessPublicWidth]
  · rcases hpositive with ⟨hconsumedPositive, hraw | hmodeFour | hnegation⟩
    · have hconsumed : consumedCount ≤ current.parserTokensCount := by omega
      have hconsumedSize := natSize_le_transformStepWidth_of_le_tokenCount
        (width := width)
        (hconsumed.trans hcurrentCount)
      refine ⟨0, ⟨hcount, Or.inr
        ⟨hconsumedPositive, Or.inl hraw⟩⟩, hconsumedSize, ?_⟩
      simp [compactFormulaTransformAdjacentStepPublicWidth,
        compactBinaryNatStreamStepWitnessPublicWidth]
    · have hconsumed : consumedCount ≤ current.parserTokensCount := by omega
      have hconsumedSize := natSize_le_transformStepWidth_of_le_tokenCount
        (width := width)
        (hconsumed.trans hcurrentCount)
      refine ⟨0, ⟨hcount, Or.inr
        ⟨hconsumedPositive, Or.inr (Or.inl hmodeFour)⟩⟩,
          hconsumedSize, ?_⟩
      simp [compactFormulaTransformAdjacentStepPublicWidth,
        compactBinaryNatStreamStepWitnessPublicWidth]
    · have hconsumed : consumedCount ≤ current.parserTokensCount := by omega
      have hconsumedSize := natSize_le_transformStepWidth_of_le_tokenCount
        (width := width)
        (hconsumed.trans hcurrentCount)
      have hmappedSize :=
        CompactNegationFormulaTagGraph.mapped_size_le
          htagSize hnegation.2.2.2.2.2.1
      exact ⟨mappedHead,
        ⟨hcount, Or.inr
          ⟨hconsumedPositive, Or.inr (Or.inr hnegation)⟩⟩,
        hconsumedSize, hmappedSize⟩

theorem compactFormulaTransformStepRows_complete_with_fit
    {tokenTable width tokenCount mode
      witnessStart witnessFinish witnessCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates}
    {current next : CompactFormulaTransformState}
    {transformWitness : List Nat}
    (hcurrent : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount nextCoordinates next)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish transformWitness)
    (hwitnessCount : witnessCount = transformWitness.length)
    (hwell : CompactSyntaxTaskStackFieldsWellFormed current.1.2.1)
    (hstep : next = compactFormulaTransformStep
      (mode, transformWitness) current) :
    ∃ stepWitness consumedCount mappedHead,
      CompactFormulaTransformStepRows tokenTable width tokenCount
        currentCoordinates nextCoordinates mode stepWitness
          consumedCount mappedHead witnessStart witnessFinish witnessCount ∧
      CompactUnifiedParserSyntaxStepWitnessFits
        width tokenCount stepWitness ∧
      Nat.size consumedCount ≤
        compactFormulaTransformAdjacentStepPublicWidth width tokenCount ∧
      Nat.size mappedHead ≤
        compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
  have hparser : next.1 = compactSyntaxParserStep current.1 := by
    calc
      next.1 = (compactFormulaTransformStep
          (mode, transformWitness) current).1 := congrArg Prod.fst hstep
      _ = compactSyntaxParserStep current.1 :=
        compactFormulaTransformStep_parser mode transformWitness current
  rcases compactUnifiedParserSyntaxStepRows_complete_with_fit
      hcurrent.parserLayout hnext.parserLayout hwell hparser with
    ⟨stepWitness, hparserRows, hstepWitnessFit⟩
  have hzeroSize : Nat.size 0 ≤
      compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
    simp [compactFormulaTransformAdjacentStepPublicWidth,
      compactBinaryNatStreamStepWitnessPublicWidth]
  have hquietResult
      (hquiet : CompactFormulaTransformQuietParserRows
        tokenTable width tokenCount currentCoordinates nextCoordinates
          stepWitness) :
      ∃ consumedCount mappedHead,
        CompactFormulaTransformStepRows tokenTable width tokenCount
          currentCoordinates nextCoordinates mode stepWitness
            consumedCount mappedHead witnessStart witnessFinish witnessCount ∧
        Nat.size consumedCount ≤
          compactFormulaTransformAdjacentStepPublicWidth width tokenCount ∧
        Nat.size mappedHead ≤
          compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
    have hparserTokens :=
      compactFormulaTransformQuietParserRows_parser_and_tokens
        hcurrent hnext hquiet
    have houtput := compactFormulaTransformStep_output_eq_of_tokens_eq
      hstep hparserTokens.1 hparserTokens.2
    have houtputRows :=
      (compactFormulaTransformOutputSameRows_iff hcurrent hnext).mpr houtput
    exact ⟨0, 0, Or.inl ⟨hquiet, houtputRows⟩,
      hzeroSize, hzeroSize⟩
  rcases hparserRows with
    hdone | hempty | hrepeat | hterm | hformula | hinvalid
  · rcases hquietResult (Or.inl hdone) with
      ⟨consumedCount, mappedHead, hrows, hconsumed, hmapped⟩
    exact ⟨stepWitness, consumedCount, mappedHead,
      hrows, hstepWitnessFit, hconsumed, hmapped⟩
  · rcases hquietResult (Or.inr (Or.inl hempty)) with
      ⟨consumedCount, mappedHead, hrows, hconsumed, hmapped⟩
    exact ⟨stepWitness, consumedCount, mappedHead,
      hrows, hstepWitnessFit, hconsumed, hmapped⟩
  · rcases hquietResult (Or.inr (Or.inr (Or.inl hrepeat))) with
      ⟨consumedCount, mappedHead, hrows, hconsumed, hmapped⟩
    exact ⟨stepWitness, consumedCount, mappedHead,
      hrows, hstepWitnessFit, hconsumed, hmapped⟩
  · rcases (exists_compactFormulaTransformTermOutputRows_iff_step
      hcurrent hnext hwitness hwitnessCount hterm).mpr hstep with
      ⟨consumedCount, houtputRows⟩
    have hcurrentCount : currentCoordinates.parserTokensCount ≤ tokenCount :=
      structuredListLayout_count_le_tokenCount
        hcurrent.parserLayout.tokensLayout
    have hconsumedSize :=
      CompactFormulaTransformTermOutputRows.consumed_size_le
        hcurrentCount houtputRows
    exact ⟨stepWitness, consumedCount, 0,
      Or.inr (Or.inl ⟨hterm, houtputRows⟩),
      hstepWitnessFit, hconsumedSize, hzeroSize⟩
  · rcases (exists_compactFormulaTransformFormulaOutputRows_iff_step
      (witness := transformWitness) hcurrent hnext hformula).mpr hstep with
      ⟨consumedCount, mappedHead, houtputRows⟩
    have hcurrentCount : currentCoordinates.parserTokensCount ≤ tokenCount :=
      structuredListLayout_count_le_tokenCount
        hcurrent.parserLayout.tokensLayout
    rcases
        CompactFormulaTransformFormulaOutputRows.exists_fittingMappedHead
          hcurrentCount hstepWitnessFit.slot4_size houtputRows with
      ⟨fittingMappedHead, hfittingOutput, hconsumedSize, hmappedSize⟩
    exact ⟨stepWitness, consumedCount, fittingMappedHead,
      Or.inr (Or.inr ⟨hformula, hfittingOutput⟩),
      hstepWitnessFit, hconsumedSize, hmappedSize⟩
  · rcases hquietResult (Or.inr (Or.inr (Or.inr hinvalid))) with
      ⟨consumedCount, mappedHead, hrows, hconsumed, hmapped⟩
    exact ⟨stepWitness, consumedCount, mappedHead,
      hrows, hstepWitnessFit, hconsumed, hmapped⟩

theorem CompactFormulaTransformAdjacentStepRowFits.of_componentFits
    {width tokenCount : Nat}
    {row : CompactFormulaTransformAdjacentStepRow}
    (hcurrent : CompactFormulaTransformStateCoreCoordinateFits
      width tokenCount row.currentCoordinates row.currentSize)
    (hnext : CompactFormulaTransformStateCoreCoordinateFits
      width tokenCount row.nextCoordinates row.nextSize)
    (hstep : CompactUnifiedParserSyntaxStepWitnessFits
      width tokenCount row.stepWitness)
    (hconsumed : Nat.size row.consumedCount ≤
      compactFormulaTransformAdjacentStepPublicWidth width tokenCount)
    (hmapped : Nat.size row.mappedHead ≤
      compactFormulaTransformAdjacentStepPublicWidth width tokenCount) :
    CompactFormulaTransformAdjacentStepRowFits
      (compactFormulaTransformAdjacentStepPublicWidth width tokenCount) row := by
  intro column hcolumn
  have hindex : column <
      (compactFormulaTransformAdjacentStepRowValues row).length := by
    simpa using hcolumn
  let value :=
    (compactFormulaTransformAdjacentStepRowValues row).getI column
  change Nat.size value ≤ _
  have hmem :
      value ∈ compactFormulaTransformAdjacentStepRowValues row := by
    change (compactFormulaTransformAdjacentStepRowValues row).getI column ∈ _
    rw [List.getI_eq_getElem _ hindex]
    exact List.getElem_mem hindex
  simp only [compactFormulaTransformAdjacentStepRowValues,
    List.mem_cons] at hmem
  rcases hmem with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h
  · simpa [h] using hcurrent.start
  · simpa [h] using hcurrent.finish
  · simpa [h] using hcurrent.parserFinish
  · simpa [h] using hcurrent.parserTokensFinish
  · simpa [h] using hcurrent.parserTasksFinish
  · simpa [h] using hcurrent.parserTokensBoundary
  · simpa [h] using hcurrent.parserTokensCount
  · simpa [h] using hcurrent.parserTasksBoundary
  · simpa [h] using hcurrent.parserTasksCount
  · simpa [h] using hcurrent.outputBoundary
  · simpa [h] using hcurrent.outputCount
  · simpa [h] using hcurrent.parserTokensBoundarySize
  · simpa [h] using hcurrent.parserTasksBoundarySize
  · simpa [h] using hcurrent.outputBoundarySize
  · simpa [h] using hnext.start
  · simpa [h] using hnext.finish
  · simpa [h] using hnext.parserFinish
  · simpa [h] using hnext.parserTokensFinish
  · simpa [h] using hnext.parserTasksFinish
  · simpa [h] using hnext.parserTokensBoundary
  · simpa [h] using hnext.parserTokensCount
  · simpa [h] using hnext.parserTasksBoundary
  · simpa [h] using hnext.parserTasksCount
  · simpa [h] using hnext.outputBoundary
  · simpa [h] using hnext.outputCount
  · simpa [h] using hnext.parserTokensBoundarySize
  · simpa [h] using hnext.parserTasksBoundarySize
  · simpa [h] using hnext.outputBoundarySize
  · simpa [h] using hstep.slot0_size
  · simpa [h] using hstep.slot1_size
  · simpa [h] using hstep.slot2_size
  · simpa [h] using hstep.slot3_size
  · simpa [h] using hstep.slot4_size
  · simpa [h] using hstep.slot5_size
  · simpa [h] using hstep.slot6_size
  · simpa [h] using hconsumed
  · rcases h with h | h
    · simpa [h] using hmapped
    · simp at h

def CompactFormulaTransformStateListAdjacentStepRowsWithFit
    (tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat)
    (states : List CompactFormulaTransformState) : Prop :=
  ∀ index < states.length - 1,
    ∃ row : CompactFormulaTransformAdjacentStepRow,
      CompactFormulaTransformAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary states.length index mode
          witnessStart witnessFinish witnessCount row ∧
      CompactBinaryNatStreamStatusDirectLayout
        tokenTable width tokenCount
          row.currentCoordinates.parserTasksFinish
          row.currentCoordinates.parserFinish (states.getI index).1.2.2 ∧
      CompactBinaryNatStreamStatusDirectLayout
        tokenTable width tokenCount
          row.nextCoordinates.parserTasksFinish
          row.nextCoordinates.parserFinish (states.getI (index + 1)).1.2.2 ∧
      CompactFormulaTransformAdjacentStepRowFits
        (compactFormulaTransformAdjacentStepPublicWidth width tokenCount) row

theorem stateListAdjacentStepRowsWithFit_of_localTrace
    {tokenTable width tokenCount stateBoundary fuel mode
      witnessStart witnessFinish witnessCount : Nat}
    {transformWitness : List Nat} {start : CompactFormulaTransformState}
    {states : List CompactFormulaTransformState}
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish transformWitness)
    (hwitnessCount : witnessCount = transformWitness.length)
    (hvalid : CompactFormulaTransformLocalTraceValid
      (mode, transformWitness) fuel start states)
    (hstart : CompactSyntaxTaskStackFieldsWellFormed start.1.2.1) :
    CompactFormulaTransformStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states := by
  intro index hindex
  have hstepIndex : index < fuel := by
    rw [hvalid.1] at hindex
    omega
  have hcurrentIndex : index < states.length := by
    rw [hvalid.1]
    omega
  have hnextIndex : index + 1 < states.length := by
    rw [hvalid.1]
    omega
  rcases exists_compactFormulaTransformStateAtRows_with_fixed_layout
      hrows hcurrentIndex with
    ⟨currentCoordinates, currentSize, hcurrentRows, hcurrentFixed⟩
  rcases exists_compactFormulaTransformStateAtRows_with_fixed_layout
      hrows hnextIndex with
    ⟨nextCoordinates, nextSize, hnextRows, hnextFixed⟩
  have hwell : CompactSyntaxTaskStackFieldsWellFormed
      (states.getI index).1.2.1 :=
    CompactFormulaTransformLocalTraceValid.getI_task_fields_well_formed
      hvalid hstart (Nat.le_of_lt hstepIndex)
  have hstep : states.getI (index + 1) =
      compactFormulaTransformStep
        (mode, transformWitness) (states.getI index) :=
    CompactFormulaTransformLocalTraceValid.getI_step hvalid hstepIndex
  rcases compactFormulaTransformStepRows_complete_with_fit
      hcurrentFixed hnextFixed hwitness hwitnessCount hwell hstep with
    ⟨stepWitness, consumedCount, mappedHead,
      hstepRows, hstepFit, hconsumedFit, hmappedFit⟩
  let row : CompactFormulaTransformAdjacentStepRow :=
    { currentCoordinates := currentCoordinates
      currentSize := currentSize
      nextCoordinates := nextCoordinates
      nextSize := nextSize
      stepWitness := stepWitness
      consumedCount := consumedCount
      mappedHead := mappedHead }
  have hcurrentFit :=
    CompactFormulaTransformStateAtRows.coordinateFits hcurrentRows
  have hnextFit :=
    CompactFormulaTransformStateAtRows.coordinateFits hnextRows
  refine ⟨row, ?_, ?_, ?_, ?_⟩
  · exact ⟨hcurrentRows, hnextRows, hstepRows⟩
  · exact hcurrentFixed.parserLayout.statusLayout
  · exact hnextFixed.parserLayout.statusLayout
  · exact CompactFormulaTransformAdjacentStepRowFits.of_componentFits
      hcurrentFit hnextFit hstepFit hconsumedFit hmappedFit

#print axioms CompactFormulaTransformStateCoreGraph.coordinateFits
#print axioms CompactFormulaTransformStateAtRows.coordinateFits
#print axioms compactUnifiedParserSyntaxStepRows_complete_with_fit
#print axioms compactFormulaTransformStepRows_complete_with_fit
#print axioms CompactFormulaTransformAdjacentStepRowFits.of_componentFits
#print axioms stateListAdjacentStepRowsWithFit_of_localTrace

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
