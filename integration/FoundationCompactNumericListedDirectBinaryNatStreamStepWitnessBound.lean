import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTable
import integration.FoundationCompactNumericListedDirectAtomicListRowRealization

/-!
# Public width bound for stream-step witness rows

Unused branch coordinates are normalized to zero.  Every remaining cursor,
count, decoder witness, and boundary-table code then fits the public width
`(tokenCount + 1) * tokenCount + 8`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBoolListPackedValue
open FoundationCompactNumericListedDirectBoolListDropRows
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectNatListReverseRows
open FoundationCompactNumericListedDirectBinaryNatDecodeFailure
open FoundationCompactNumericListedDirectCompletedStatusReverseRows
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStateFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStepRealization
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTable

def compactBinaryNatStreamStepWitnessPublicWidth (tokenCount : Nat) : Nat :=
  (tokenCount + 1) * tokenCount + 8

theorem natSize_le_streamStepWidth_of_le_tokenCount
    {value tokenCount : Nat} (hvalue : value ≤ tokenCount) :
    Nat.size value ≤ compactBinaryNatStreamStepWitnessPublicWidth tokenCount := by
  have hsize : Nat.size value ≤ value := natSize_le_of_le (Nat.le_refl value)
  have htokenArea : tokenCount ≤ (tokenCount + 1) * tokenCount := by
    rw [Nat.add_mul, one_mul]
    exact Nat.le_add_left tokenCount (tokenCount * tokenCount)
  exact (hsize.trans hvalue).trans
    (htokenArea.trans (by
      simp [compactBinaryNatStreamStepWitnessPublicWidth]))

theorem natSize_le_streamStepWidth_of_le_boundaryArea
    {value tokenCount : Nat}
    (hvalue : value ≤ (tokenCount + 1) * tokenCount) :
    Nat.size value ≤ compactBinaryNatStreamStepWitnessPublicWidth tokenCount := by
  have hsize : Nat.size value ≤ value := natSize_le_of_le (Nat.le_refl value)
  simp only [compactBinaryNatStreamStepWitnessPublicWidth]
  omega

theorem boundaryArea_le_streamStepWidth
    (tokenCount : Nat) :
    (tokenCount + 1) * tokenCount ≤
      compactBinaryNatStreamStepWitnessPublicWidth tokenCount := by
  simp [compactBinaryNatStreamStepWitnessPublicWidth]

theorem tokenCount_le_streamStepWidth (tokenCount : Nat) :
    tokenCount ≤ compactBinaryNatStreamStepWitnessPublicWidth tokenCount := by
  have harea : tokenCount ≤ (tokenCount + 1) * tokenCount := by
    rw [Nat.add_mul, one_mul]
    exact Nat.le_add_left tokenCount (tokenCount * tokenCount)
  exact harea.trans (boundaryArea_le_streamStepWidth tokenCount)

theorem listBoundaryArea_le_publicArea
    {count tokenCount : Nat} (hcount : count ≤ tokenCount) :
    (count + 1) * tokenCount ≤ (tokenCount + 1) * tokenCount :=
  Nat.mul_le_mul_right tokenCount (Nat.add_le_add_right hcount 1)

theorem structuredListLayout_start_lt_tokenCount
    {tokenTable width tokenCount start count finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable) :
    start < tokenCount := by
  rcases hlayout with
    ⟨_bodyStart, _hbodyStart, hheader, _hboundary⟩
  exact hheader.1.1

theorem structuredListLayout_count_le_tokenCount
    {tokenTable width tokenCount start count finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable) :
    count ≤ tokenCount := by
  rcases hlayout with
    ⟨_bodyStart, _hbodyStart, hheader, _hboundary⟩
  exact (Nat.le_add_left count _).trans hheader.2

structure CompactBinaryNatStreamStateCoreCoordinateFits
    (tokenCount : Nat) (coordinates : CompactBinaryNatStreamRowCoordinates)
    (sizeWitness : CompactBinaryNatStreamStateCoreSizeWitness) : Prop where
  start : Nat.size coordinates.start ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  finish : Nat.size coordinates.finish ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  bitsFinish : Nat.size coordinates.bitsFinish ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  decodedFinish : Nat.size coordinates.decodedFinish ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  bitsBoundary : Nat.size coordinates.bitsBoundary ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  bitsCount : Nat.size coordinates.bitsCount ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  decodedBoundary : Nat.size coordinates.decodedBoundary ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  decodedCount : Nat.size coordinates.decodedCount ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  bitsBoundarySize : Nat.size sizeWitness.bitsBoundarySize ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  decodedBoundarySize : Nat.size sizeWitness.decodedBoundarySize ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  finish_le_tokenCount : coordinates.finish ≤ tokenCount
  bitsCount_le_tokenCount : coordinates.bitsCount ≤ tokenCount
  decodedCount_le_tokenCount : coordinates.decodedCount ≤ tokenCount

theorem CompactBinaryNatStreamStateCoreGraph.coordinateFits
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactBinaryNatStreamRowCoordinates}
    {sizeWitness : CompactBinaryNatStreamStateCoreSizeWitness}
    (hgraph : CompactBinaryNatStreamStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    CompactBinaryNatStreamStateCoreCoordinateFits
      tokenCount coordinates sizeWitness := by
  rcases hgraph with
    ⟨houter, hbitsLayout, _hbitsRows,
      hinner, hdecodedLayout, _hdecodedRows,
      hbitsSizeEq, hbitsSize,
      hdecodedSizeEq, hdecodedSize⟩
  have hfinish : coordinates.finish ≤ tokenCount := houter.2.2
  have hbitsCount : coordinates.bitsCount ≤ tokenCount := by
    rcases hbitsLayout with
      ⟨_bodyStart, _hbodyStart, hheader, _hboundary⟩
    exact (Nat.le_add_left coordinates.bitsCount _).trans hheader.2
  have hdecodedCount : coordinates.decodedCount ≤ tokenCount := by
    rcases hdecodedLayout with
      ⟨_bodyStart, _hbodyStart, hheader, _hboundary⟩
    exact (Nat.le_add_left coordinates.decodedCount _).trans hheader.2
  have hbitsArea : sizeWitness.bitsBoundarySize ≤
      (tokenCount + 1) * tokenCount := by
    exact hbitsSize.trans (Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right hbitsCount 1))
  have hdecodedArea : sizeWitness.decodedBoundarySize ≤
      (tokenCount + 1) * tokenCount := by
    exact hdecodedSize.trans (Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right hdecodedCount 1))
  refine
    { start := natSize_le_streamStepWidth_of_le_tokenCount
        ((Nat.le_of_lt houter.1).trans
          ((Nat.le_of_lt houter.2.1).trans hfinish))
      finish := natSize_le_streamStepWidth_of_le_tokenCount hfinish
      bitsFinish := natSize_le_streamStepWidth_of_le_tokenCount
        ((Nat.le_of_lt houter.2.1).trans hfinish)
      decodedFinish := natSize_le_streamStepWidth_of_le_tokenCount
        ((Nat.le_of_lt hinner.2.1).trans hfinish)
      bitsBoundary := ?_
      bitsCount := natSize_le_streamStepWidth_of_le_tokenCount hbitsCount
      decodedBoundary := ?_
      decodedCount :=
        natSize_le_streamStepWidth_of_le_tokenCount hdecodedCount
      bitsBoundarySize :=
        natSize_le_streamStepWidth_of_le_boundaryArea hbitsArea
      decodedBoundarySize :=
        natSize_le_streamStepWidth_of_le_boundaryArea hdecodedArea
      finish_le_tokenCount := hfinish
      bitsCount_le_tokenCount := hbitsCount
      decodedCount_le_tokenCount := hdecodedCount }
  · rw [← hbitsSizeEq]
    exact hbitsArea.trans (boundaryArea_le_streamStepWidth tokenCount)
  · rw [← hdecodedSizeEq]
    exact hdecodedArea.trans (boundaryArea_le_streamStepWidth tokenCount)

structure CompactBinaryNatStreamStepWitnessFits
    (tokenCount : Nat)
    (witness : CompactBinaryNatStreamStepWitnessCoordinates) : Prop where
  branch : Nat.size witness.branch ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  payload : Nat.size witness.payload ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  digitCount : Nat.size witness.digitCount ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  token : Nat.size witness.token ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  consumed : Nat.size witness.consumed ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  sourceOutputStart : Nat.size witness.sourceOutputStart ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  sourceOutputBoundary : Nat.size witness.sourceOutputBoundary ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  sourceOutputBoundarySize : Nat.size witness.sourceOutputBoundarySize ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  targetOutputStart : Nat.size witness.targetOutputStart ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  targetOutputBoundary : Nat.size witness.targetOutputBoundary ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  targetOutputBoundarySize : Nat.size witness.targetOutputBoundarySize ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount
  outputCount : Nat.size witness.outputCount ≤
    compactBinaryNatStreamStepWitnessPublicWidth tokenCount

def compactBinaryNatStreamDoneFailedWitness :
    CompactBinaryNatStreamStepWitnessCoordinates :=
  { branch := 0
    payload := 0
    digitCount := 0
    token := 0
    consumed := 0
    sourceOutputStart := 0
    sourceOutputBoundary := 0
    sourceOutputBoundarySize := 0
    targetOutputStart := 0
    targetOutputBoundary := 0
    targetOutputBoundarySize := 0
    outputCount := 0 }

def compactBinaryNatStreamDoneCompletedWitness
    (witness : CompactBinaryNatStreamStepWitnessCoordinates) :
    CompactBinaryNatStreamStepWitnessCoordinates :=
  { branch := 0
    payload := 0
    digitCount := 0
    token := 0
    consumed := 0
    sourceOutputStart := witness.sourceOutputStart
    sourceOutputBoundary := witness.sourceOutputBoundary
    sourceOutputBoundarySize := witness.sourceOutputBoundarySize
    targetOutputStart := witness.targetOutputStart
    targetOutputBoundary := witness.targetOutputBoundary
    targetOutputBoundarySize := witness.targetOutputBoundarySize
    outputCount := witness.outputCount }

def compactBinaryNatStreamEmptyWitness
    (witness : CompactBinaryNatStreamStepWitnessCoordinates) :
    CompactBinaryNatStreamStepWitnessCoordinates :=
  { branch := 1
    payload := 0
    digitCount := 0
    token := 0
    consumed := 0
    sourceOutputStart := 0
    sourceOutputBoundary := 0
    sourceOutputBoundarySize := 0
    targetOutputStart := witness.targetOutputStart
    targetOutputBoundary := witness.targetOutputBoundary
    targetOutputBoundarySize := witness.targetOutputBoundarySize
    outputCount := 0 }

def compactBinaryNatStreamDecodeFailureWitness
    (witness : CompactBinaryNatStreamStepWitnessCoordinates) :
    CompactBinaryNatStreamStepWitnessCoordinates :=
  { branch := 2
    payload := witness.payload
    digitCount := 0
    token := 0
    consumed := 0
    sourceOutputStart := 0
    sourceOutputBoundary := 0
    sourceOutputBoundarySize := 0
    targetOutputStart := 0
    targetOutputBoundary := 0
    targetOutputBoundarySize := 0
    outputCount := 0 }

def compactBinaryNatStreamDecodeSuccessWitness
    (witness : CompactBinaryNatStreamStepWitnessCoordinates) :
    CompactBinaryNatStreamStepWitnessCoordinates :=
  { branch := 3
    payload := witness.payload
    digitCount := witness.digitCount
    token := witness.token
    consumed := witness.consumed
    sourceOutputStart := 0
    sourceOutputBoundary := 0
    sourceOutputBoundarySize := 0
    targetOutputStart := 0
    targetOutputBoundary := 0
    targetOutputBoundarySize := 0
    outputCount := 0 }

theorem CompactBinaryNatStreamStepStateGraph.exists_fittingWitness
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates : CompactBinaryNatStreamRowCoordinates}
    {currentSize nextSize : CompactBinaryNatStreamStateCoreSizeWitness}
    {witness : CompactBinaryNatStreamStepWitnessCoordinates}
    (hgraph : CompactBinaryNatStreamStepStateGraph
      tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSize nextSize witness) :
    ∃ fittingWitness,
      CompactBinaryNatStreamStepStateGraph
        tokenTable width tokenCount currentCoordinates nextCoordinates
          currentSize nextSize fittingWitness ∧
      CompactBinaryNatStreamStepWitnessFits tokenCount fittingWitness := by
  rcases hgraph with ⟨hcurrentGraph, hnextGraph, hstep⟩
  have hcurrentFit :=
    CompactBinaryNatStreamStateCoreGraph.coordinateFits hcurrentGraph
  rcases hstep with hdone | hempty | hfailure | hsuccess
  · rcases hdone with
      ⟨_hbranch, hbits, hdecoded, hfailed | hcompleted⟩
    · refine ⟨compactBinaryNatStreamDoneFailedWitness,
        ⟨hcurrentGraph, hnextGraph, Or.inl
          ⟨rfl, hbits, hdecoded, Or.inl hfailed⟩⟩, ?_⟩
      refine
        { branch := ?_
          payload := ?_
          digitCount := ?_
          token := ?_
          consumed := ?_
          sourceOutputStart := ?_
          sourceOutputBoundary := ?_
          sourceOutputBoundarySize := ?_
          targetOutputStart := ?_
          targetOutputBoundary := ?_
          targetOutputBoundarySize := ?_
          outputCount := ?_ } <;>
        simp [compactBinaryNatStreamDoneFailedWitness,
          compactBinaryNatStreamStepWitnessPublicWidth]
    · rcases hcompleted with
        ⟨⟨hsourcePrefix, hsourceLayout,
            htargetPrefix, htargetLayout, hsameRows⟩,
          hsourceSizeEq, hsourceSize,
          htargetSizeEq, htargetSize⟩
      have hcount : witness.outputCount ≤ tokenCount :=
        structuredListLayout_count_le_tokenCount hsourceLayout
      have hsourceArea : witness.sourceOutputBoundarySize ≤
          (tokenCount + 1) * tokenCount :=
        hsourceSize.trans (listBoundaryArea_le_publicArea hcount)
      have htargetArea : witness.targetOutputBoundarySize ≤
          (tokenCount + 1) * tokenCount :=
        htargetSize.trans (listBoundaryArea_le_publicArea hcount)
      refine ⟨compactBinaryNatStreamDoneCompletedWitness witness,
        ⟨hcurrentGraph, hnextGraph, Or.inl
          ⟨rfl, hbits, hdecoded, Or.inr
            ⟨⟨hsourcePrefix, hsourceLayout,
                htargetPrefix, htargetLayout, hsameRows⟩,
              hsourceSizeEq, hsourceSize,
              htargetSizeEq, htargetSize⟩⟩⟩, ?_⟩
      refine
        { branch := by
            simp [compactBinaryNatStreamDoneCompletedWitness,
              compactBinaryNatStreamStepWitnessPublicWidth]
          payload := by
            simp [compactBinaryNatStreamDoneCompletedWitness,
              compactBinaryNatStreamStepWitnessPublicWidth]
          digitCount := by
            simp [compactBinaryNatStreamDoneCompletedWitness,
              compactBinaryNatStreamStepWitnessPublicWidth]
          token := by
            simp [compactBinaryNatStreamDoneCompletedWitness,
              compactBinaryNatStreamStepWitnessPublicWidth]
          consumed := by
            simp [compactBinaryNatStreamDoneCompletedWitness,
              compactBinaryNatStreamStepWitnessPublicWidth]
          sourceOutputStart :=
            natSize_le_streamStepWidth_of_le_tokenCount
              (Nat.le_of_lt
                (structuredListLayout_start_lt_tokenCount hsourceLayout))
          sourceOutputBoundary := by
            change Nat.size witness.sourceOutputBoundary ≤
              compactBinaryNatStreamStepWitnessPublicWidth tokenCount
            rw [← hsourceSizeEq]
            exact hsourceArea.trans
              (boundaryArea_le_streamStepWidth tokenCount)
          sourceOutputBoundarySize :=
            natSize_le_streamStepWidth_of_le_boundaryArea hsourceArea
          targetOutputStart :=
            natSize_le_streamStepWidth_of_le_tokenCount
              (Nat.le_of_lt
                (structuredListLayout_start_lt_tokenCount htargetLayout))
          targetOutputBoundary := by
            change Nat.size witness.targetOutputBoundary ≤
              compactBinaryNatStreamStepWitnessPublicWidth tokenCount
            rw [← htargetSizeEq]
            exact htargetArea.trans
              (boundaryArea_le_streamStepWidth tokenCount)
          targetOutputBoundarySize :=
            natSize_le_streamStepWidth_of_le_boundaryArea htargetArea
          outputCount :=
            natSize_le_streamStepWidth_of_le_tokenCount hcount }
  · rcases hempty with
      ⟨_hbranch, hcurrentCount, hnextCount,
        hcurrentRunning, hdecoded, hcompleted⟩
    rcases hcompleted with
      ⟨⟨hprefix, houtputLayout, hreverseRows⟩,
        houtputSizeEq, houtputSize⟩
    have hcount : currentCoordinates.decodedCount ≤ tokenCount :=
      hcurrentFit.decodedCount_le_tokenCount
    have houtputArea : witness.targetOutputBoundarySize ≤
        (tokenCount + 1) * tokenCount :=
      houtputSize.trans (listBoundaryArea_le_publicArea hcount)
    refine ⟨compactBinaryNatStreamEmptyWitness witness,
      ⟨hcurrentGraph, hnextGraph, Or.inr (Or.inl
        ⟨rfl, hcurrentCount, hnextCount,
          hcurrentRunning, hdecoded,
          ⟨⟨hprefix, houtputLayout, hreverseRows⟩,
            houtputSizeEq, houtputSize⟩⟩)⟩, ?_⟩
    refine
      { branch := by
          simp [compactBinaryNatStreamEmptyWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        payload := by
          simp [compactBinaryNatStreamEmptyWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        digitCount := by
          simp [compactBinaryNatStreamEmptyWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        token := by
          simp [compactBinaryNatStreamEmptyWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        consumed := by
          simp [compactBinaryNatStreamEmptyWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        sourceOutputStart := by
          simp [compactBinaryNatStreamEmptyWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        sourceOutputBoundary := by
          simp [compactBinaryNatStreamEmptyWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        sourceOutputBoundarySize := by
          simp [compactBinaryNatStreamEmptyWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        targetOutputStart :=
          natSize_le_streamStepWidth_of_le_tokenCount
            (Nat.le_of_lt
              (structuredListLayout_start_lt_tokenCount houtputLayout))
        targetOutputBoundary := by
          change Nat.size witness.targetOutputBoundary ≤
            compactBinaryNatStreamStepWitnessPublicWidth tokenCount
          rw [← houtputSizeEq]
          exact houtputArea.trans
            (boundaryArea_le_streamStepWidth tokenCount)
        targetOutputBoundarySize :=
          natSize_le_streamStepWidth_of_le_boundaryArea houtputArea
        outputCount := by
          simp [compactBinaryNatStreamEmptyWitness,
            compactBinaryNatStreamStepWitnessPublicWidth] }
  · rcases hfailure with
      ⟨_hbranch, hpositive, hcurrentRunning, hdecode,
        hbits, hdecoded, hnextFailed⟩
    have hpayload : Nat.size witness.payload ≤
        compactBinaryNatStreamStepWitnessPublicWidth tokenCount :=
      (hdecode.1.1.trans hcurrentFit.bitsCount_le_tokenCount).trans
        (tokenCount_le_streamStepWidth tokenCount)
    refine ⟨compactBinaryNatStreamDecodeFailureWitness witness,
      ⟨hcurrentGraph, hnextGraph, Or.inr (Or.inr (Or.inl
        ⟨rfl, hpositive, hcurrentRunning, hdecode,
          hbits, hdecoded, hnextFailed⟩))⟩, ?_⟩
    refine
      { branch := by
          change Nat.size 2 ≤
            compactBinaryNatStreamStepWitnessPublicWidth tokenCount
          exact (show Nat.size 2 ≤ 8 by decide).trans (by
            simp [compactBinaryNatStreamStepWitnessPublicWidth])
        payload := hpayload
        digitCount := by
          simp [compactBinaryNatStreamDecodeFailureWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        token := by
          simp [compactBinaryNatStreamDecodeFailureWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        consumed := by
          simp [compactBinaryNatStreamDecodeFailureWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        sourceOutputStart := by
          simp [compactBinaryNatStreamDecodeFailureWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        sourceOutputBoundary := by
          simp [compactBinaryNatStreamDecodeFailureWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        sourceOutputBoundarySize := by
          simp [compactBinaryNatStreamDecodeFailureWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        targetOutputStart := by
          simp [compactBinaryNatStreamDecodeFailureWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        targetOutputBoundary := by
          simp [compactBinaryNatStreamDecodeFailureWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        targetOutputBoundarySize := by
          simp [compactBinaryNatStreamDecodeFailureWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        outputCount := by
          simp [compactBinaryNatStreamDecodeFailureWitness,
            compactBinaryNatStreamStepWitnessPublicWidth] }
  · rcases hsuccess with
      ⟨_hbranch, hpositive, hcurrentRunning,
        hdecode, hcons, hnextRunning⟩
    have hpayload : Nat.size witness.payload ≤
        compactBinaryNatStreamStepWitnessPublicWidth tokenCount :=
      (hdecode.1.1.trans hcurrentFit.bitsCount_le_tokenCount).trans
        (tokenCount_le_streamStepWidth tokenCount)
    have hdigitCount : witness.digitCount ≤ currentCoordinates.bitsCount := by
      have hnext := hdecode.2.1.2.1
      have hnextEq := hdecode.2.1.1
      omega
    have hdigitSize := natSize_le_streamStepWidth_of_le_tokenCount
      (hdigitCount.trans hcurrentFit.bitsCount_le_tokenCount)
    have htokenSize : Nat.size witness.token ≤
        compactBinaryNatStreamStepWitnessPublicWidth tokenCount :=
      (hdecode.2.1.2.2.1.trans hdigitCount).trans
        (hcurrentFit.bitsCount_le_tokenCount.trans
          (tokenCount_le_streamStepWidth tokenCount))
    have hconsumed : witness.consumed ≤ currentCoordinates.bitsCount :=
      hdecode.2.1.2.1
    have hconsumedSize := natSize_le_streamStepWidth_of_le_tokenCount
      (hconsumed.trans hcurrentFit.bitsCount_le_tokenCount)
    refine ⟨compactBinaryNatStreamDecodeSuccessWitness witness,
      ⟨hcurrentGraph, hnextGraph, Or.inr (Or.inr (Or.inr
        ⟨rfl, hpositive, hcurrentRunning,
          hdecode, hcons, hnextRunning⟩))⟩, ?_⟩
    refine
      { branch := by
          change Nat.size 3 ≤
            compactBinaryNatStreamStepWitnessPublicWidth tokenCount
          exact (show Nat.size 3 ≤ 8 by decide).trans (by
            simp [compactBinaryNatStreamStepWitnessPublicWidth])
        payload := hpayload
        digitCount := hdigitSize
        token := htokenSize
        consumed := hconsumedSize
        sourceOutputStart := by
          simp [compactBinaryNatStreamDecodeSuccessWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        sourceOutputBoundary := by
          simp [compactBinaryNatStreamDecodeSuccessWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        sourceOutputBoundarySize := by
          simp [compactBinaryNatStreamDecodeSuccessWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        targetOutputStart := by
          simp [compactBinaryNatStreamDecodeSuccessWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        targetOutputBoundary := by
          simp [compactBinaryNatStreamDecodeSuccessWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        targetOutputBoundarySize := by
          simp [compactBinaryNatStreamDecodeSuccessWitness,
            compactBinaryNatStreamStepWitnessPublicWidth]
        outputCount := by
          simp [compactBinaryNatStreamDecodeSuccessWitness,
            compactBinaryNatStreamStepWitnessPublicWidth] }

theorem CompactBinaryNatStreamStepStateRow.rowFits
    {tokenCount : Nat} {row : CompactBinaryNatStreamStepStateRow}
    (hcurrent : CompactBinaryNatStreamStateCoreCoordinateFits
      tokenCount row.currentCoordinates row.currentSize)
    (hnext : CompactBinaryNatStreamStateCoreCoordinateFits
      tokenCount row.nextCoordinates row.nextSize)
    (hwitness : CompactBinaryNatStreamStepWitnessFits
      tokenCount row.witness) :
    CompactBinaryNatStreamStepStateRowFits
      (compactBinaryNatStreamStepWitnessPublicWidth tokenCount) row := by
  intro column hcolumn
  have hall : ∀ value ∈ compactBinaryNatStreamStepStateRowValues row,
      Nat.size value ≤
        compactBinaryNatStreamStepWitnessPublicWidth tokenCount := by
    simp [compactBinaryNatStreamStepStateRowValues,
      hcurrent.start, hcurrent.finish, hcurrent.bitsFinish,
      hcurrent.decodedFinish, hcurrent.bitsBoundary, hcurrent.bitsCount,
      hcurrent.decodedBoundary, hcurrent.decodedCount,
      hcurrent.bitsBoundarySize, hcurrent.decodedBoundarySize,
      hnext.start, hnext.finish, hnext.bitsFinish, hnext.decodedFinish,
      hnext.bitsBoundary, hnext.bitsCount,
      hnext.decodedBoundary, hnext.decodedCount,
      hnext.bitsBoundarySize, hnext.decodedBoundarySize,
      hwitness.branch, hwitness.payload, hwitness.digitCount,
      hwitness.token, hwitness.consumed,
      hwitness.sourceOutputStart, hwitness.sourceOutputBoundary,
      hwitness.sourceOutputBoundarySize, hwitness.targetOutputStart,
      hwitness.targetOutputBoundary, hwitness.targetOutputBoundarySize,
      hwitness.outputCount]
  apply hall
  have hindex : column <
      (compactBinaryNatStreamStepStateRowValues row).length := by
    simpa using hcolumn
  rw [List.getI_eq_getElem _ hindex]
  exact List.getElem_mem hindex

#print axioms CompactBinaryNatStreamStateCoreGraph.coordinateFits
#print axioms CompactBinaryNatStreamStepStateGraph.exists_fittingWitness
#print axioms CompactBinaryNatStreamStepStateRow.rowFits

end FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
