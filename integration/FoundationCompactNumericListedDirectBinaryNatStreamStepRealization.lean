import integration.FoundationCompactNumericListedDirectBinaryNatStreamStateFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepFormula

/-!
# Realization of the pure numeric binary-natural stream step graph

The numeric state-core graphs determine their Boolean and natural-number lists.
The four arithmetic status cases then construct the two typed statuses.  Thus a
numeric step witness realizes an actual `binaryNatStreamStep`, without taking a
typed state or a typed layout as an input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStepRealization

open FoundationCompactBinaryNatStreamMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectCompletedStatusReverseRows
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStateFormula
open CompactBinaryNatStreamStateFixedLayout
open CompactBinaryNatStreamStateCoreFixedLayout

theorem CompactBinaryNatRunningStatusSlice.directLayout
    {tokenTable width tokenCount start finish : Nat}
    (hrunning : CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount start finish) :
    CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start finish none := by
  refine ⟨finish, ?_, trivial⟩
  exact ⟨hrunning, Or.inl ⟨rfl, rfl⟩⟩

theorem CompactBinaryNatFailedStatusSlice.directLayout
    {tokenTable width tokenCount start finish : Nat}
    (hfailed : CompactBinaryNatFailedStatusSlice
      tokenTable width tokenCount start finish) :
    CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start finish (some none) := by
  rcases hfailed with
    ⟨innerStart, _hinnerStart, houterCell, hinnerCell⟩
  have hinnerStartLtFinish : innerStart < finish := by
    have hnext := hinnerCell.2.1
    omega
  have hfinishBound : finish ≤ tokenCount := by
    have hcursor := hinnerCell.1
    have hnext := hinnerCell.2.1
    omega
  have houterLayout : CompactAdditiveOptionLayout
      tokenTable width tokenCount start 1 innerStart finish :=
    ⟨houterCell, Or.inr ⟨rfl, hinnerStartLtFinish, hfinishBound⟩⟩
  have hinnerLayout : CompactAdditiveOptionLayout
      tokenTable width tokenCount innerStart 0 finish finish :=
    ⟨hinnerCell, Or.inl ⟨rfl, rfl⟩⟩
  exact ⟨innerStart, houterLayout, finish, hinnerLayout, trivial⟩

theorem completedStatusDirectLayout_of_numericRows
    {tokenTable width tokenCount statusStart statusFinish
      outputStart outputBoundary outputCount : Nat}
    (hprefix : CompactBinaryNatCompletedStatusPrefix
      tokenTable width tokenCount statusStart outputStart)
    (houtputLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount outputStart outputCount
        statusFinish outputBoundary)
    (houtputUnit : CompactAdditiveUnitBoundaryRows
      tokenCount outputCount outputBoundary)
    (houtputSize : Nat.size outputBoundary ≤
      (outputCount + 1) * tokenCount) :
    ∃ output,
      CompactBinaryNatStreamStatusDirectLayout
        tokenTable width tokenCount statusStart statusFinish
          (some (some output)) := by
  let output := compactAdditiveNatListRowValues
    tokenTable width tokenCount outputBoundary outputCount
  have houtputLength : output.length = outputCount := by
    simp [output]
  have htypedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        outputBoundary output := by
    exact CompactAdditiveUnitBoundaryRows.realizedNatRows houtputUnit
  have htypedLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount outputStart output.length
        statusFinish outputBoundary := by
    simpa only [houtputLength] using houtputLayout
  have htypedSize : Nat.size outputBoundary ≤
      (output.length + 1) * tokenCount := by
    simpa only [houtputLength] using houtputSize
  have hfinishEq : statusFinish = outputStart + 1 + outputCount :=
    CompactAdditiveStructuredListLayout.finish_eq_start_add_count
      houtputLayout houtputUnit
  have hfinishBound : statusFinish ≤ tokenCount := by
    rcases houtputLayout with
      ⟨_bodyStart, _hbodyStart, _hheader, hboundary⟩
    exact hboundary.2.1
  rcases hprefix with
    ⟨innerStart, _hinnerStart, houterCell, hinnerCell⟩
  have hinnerStartLtFinish : innerStart < statusFinish := by
    have hnext := hinnerCell.2.1
    omega
  have houtputStartLtFinish : outputStart < statusFinish := by
    omega
  have houterLayout : CompactAdditiveOptionLayout
      tokenTable width tokenCount statusStart 1 innerStart statusFinish :=
    ⟨houterCell,
      Or.inr ⟨rfl, hinnerStartLtFinish, hfinishBound⟩⟩
  have hinnerLayout : CompactAdditiveOptionLayout
      tokenTable width tokenCount innerStart 1 outputStart statusFinish :=
    ⟨hinnerCell,
      Or.inr ⟨rfl, houtputStartLtFinish, hfinishBound⟩⟩
  exact ⟨output, innerStart, houterLayout,
    outputStart, hinnerLayout, outputBoundary,
    htypedLayout, htypedRows, htypedSize⟩

def CompactBinaryNatStreamStepStateGraph
    (tokenTable width tokenCount : Nat)
    (currentCoordinates nextCoordinates :
      CompactBinaryNatStreamRowCoordinates)
    (currentSize nextSize : CompactBinaryNatStreamStateCoreSizeWitness)
    (witness : CompactBinaryNatStreamStepWitnessCoordinates) : Prop :=
  CompactBinaryNatStreamStateCoreGraph
      tokenTable width tokenCount currentCoordinates currentSize ∧
    CompactBinaryNatStreamStateCoreGraph
      tokenTable width tokenCount nextCoordinates nextSize ∧
    CompactBinaryNatStreamStepGraphRows
      tokenTable width tokenCount currentCoordinates nextCoordinates witness

theorem CompactBinaryNatStreamStepStateGraph.realize
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactBinaryNatStreamRowCoordinates}
    {currentSize nextSize : CompactBinaryNatStreamStateCoreSizeWitness}
    {witness : CompactBinaryNatStreamStepWitnessCoordinates}
    (hgraph : CompactBinaryNatStreamStepStateGraph
      tokenTable width tokenCount currentCoordinates nextCoordinates
        currentSize nextSize witness) :
    ∃ current next : BinaryNatStreamState,
      CompactBinaryNatStreamStateFixedLayout
        tokenTable width tokenCount currentCoordinates current ∧
      CompactBinaryNatStreamStateFixedLayout
        tokenTable width tokenCount nextCoordinates next ∧
      next = binaryNatStreamStep current := by
  rcases hgraph with ⟨hcurrentGraph, hnextGraph, hstep⟩
  rcases hcurrentGraph.realize with
    ⟨currentBits, currentDecoded, hcurrentCore⟩
  rcases hnextGraph.realize with
    ⟨nextBits, nextDecoded, hnextCore⟩
  rcases hstep with hdone | hempty | hfailure | hsuccess
  · rcases hdone with
      ⟨hbranch, hbits, hdecoded, hfailed | hcompleted⟩
    · rcases hfailed with ⟨hcurrentFailed, hnextFailed⟩
      have hcurrentStatus :=
        CompactBinaryNatFailedStatusSlice.directLayout hcurrentFailed
      have hnextStatus :=
        CompactBinaryNatFailedStatusSlice.directLayout hnextFailed
      have hcurrent := hcurrentCore.withStatus hcurrentStatus
      have hnext := hnextCore.withStatus hnextStatus
      have hsemantic :=
        (exists_stepGraphRows_iff_step hcurrent hnext).mp
          ⟨witness, Or.inl
            ⟨hbranch, hbits, hdecoded,
              Or.inl ⟨hcurrentFailed, hnextFailed⟩⟩⟩
      exact ⟨(currentBits, currentDecoded, some none),
        (nextBits, nextDecoded, some none),
        hcurrent, hnext, hsemantic⟩
    · rcases hcompleted with
        ⟨⟨hsourcePrefix, hsourceLayout,
            htargetPrefix, htargetLayout, hsameRows⟩,
          hsourceSizeEq, hsourceSize,
          htargetSizeEq, htargetSize⟩
      have hsourceUnit :=
        CompactAdditiveNatListSameRows.sourceUnitBoundaryRows hsameRows
      have htargetUnit :=
        CompactAdditiveNatListSameRows.targetUnitBoundaryRows hsameRows
      have hsourceSize' : Nat.size witness.sourceOutputBoundary ≤
          (witness.outputCount + 1) * tokenCount := by
        simpa only [hsourceSizeEq] using hsourceSize
      have htargetSize' : Nat.size witness.targetOutputBoundary ≤
          (witness.outputCount + 1) * tokenCount := by
        simpa only [htargetSizeEq] using htargetSize
      rcases completedStatusDirectLayout_of_numericRows
          hsourcePrefix hsourceLayout hsourceUnit hsourceSize' with
        ⟨sourceOutput, hcurrentStatus⟩
      rcases completedStatusDirectLayout_of_numericRows
          htargetPrefix htargetLayout htargetUnit htargetSize' with
        ⟨targetOutput, hnextStatus⟩
      have hcurrent := hcurrentCore.withStatus hcurrentStatus
      have hnext := hnextCore.withStatus hnextStatus
      have hsemantic :=
        (exists_stepGraphRows_iff_step hcurrent hnext).mp
          ⟨witness, Or.inl
            ⟨hbranch, hbits, hdecoded, Or.inr
              ⟨⟨hsourcePrefix, hsourceLayout,
                  htargetPrefix, htargetLayout, hsameRows⟩,
                hsourceSizeEq, hsourceSize,
                htargetSizeEq, htargetSize⟩⟩⟩
      exact ⟨(currentBits, currentDecoded, some (some sourceOutput)),
        (nextBits, nextDecoded, some (some targetOutput)),
        hcurrent, hnext, hsemantic⟩
  · rcases hempty with
      ⟨hbranch, hcurrentCount, hnextCount,
        hcurrentRunning, hdecoded, hcompleted⟩
    rcases hcompleted with
      ⟨⟨hprefix, houtputLayout, hreverseRows⟩,
        houtputSizeEq, houtputSize⟩
    have houtputUnit :=
      CompactAdditiveNatListReverseRows.targetUnitBoundaryRows hreverseRows
    have houtputSize' : Nat.size witness.targetOutputBoundary ≤
        (currentCoordinates.decodedCount + 1) * tokenCount := by
      simpa only [houtputSizeEq] using houtputSize
    have hcurrentStatus :=
      CompactBinaryNatRunningStatusSlice.directLayout hcurrentRunning
    rcases completedStatusDirectLayout_of_numericRows
        hprefix houtputLayout houtputUnit houtputSize' with
      ⟨output, hnextStatus⟩
    have hcurrent := hcurrentCore.withStatus hcurrentStatus
    have hnext := hnextCore.withStatus hnextStatus
    have hsemantic :=
      (exists_stepGraphRows_iff_step hcurrent hnext).mp
        ⟨witness, Or.inr (Or.inl
          ⟨hbranch, hcurrentCount, hnextCount,
            hcurrentRunning, hdecoded,
            ⟨⟨hprefix, houtputLayout, hreverseRows⟩,
              houtputSizeEq, houtputSize⟩⟩)⟩
    exact ⟨(currentBits, currentDecoded, none),
      (nextBits, nextDecoded, some (some output)),
      hcurrent, hnext, hsemantic⟩
  · rcases hfailure with
      ⟨hbranch, hpositive, hcurrentRunning, hdecode,
        hbits, hdecoded, hnextFailed⟩
    have hcurrentStatus :=
      CompactBinaryNatRunningStatusSlice.directLayout hcurrentRunning
    have hnextStatus :=
      CompactBinaryNatFailedStatusSlice.directLayout hnextFailed
    have hcurrent := hcurrentCore.withStatus hcurrentStatus
    have hnext := hnextCore.withStatus hnextStatus
    have hsemantic :=
      (exists_stepGraphRows_iff_step hcurrent hnext).mp
        ⟨witness, Or.inr (Or.inr (Or.inl
          ⟨hbranch, hpositive, hcurrentRunning, hdecode,
            hbits, hdecoded, hnextFailed⟩))⟩
    exact ⟨(currentBits, currentDecoded, none),
      (nextBits, nextDecoded, some none),
      hcurrent, hnext, hsemantic⟩
  · rcases hsuccess with
      ⟨hbranch, hpositive, hcurrentRunning,
        hdecode, hcons, hnextRunning⟩
    have hcurrentStatus :=
      CompactBinaryNatRunningStatusSlice.directLayout hcurrentRunning
    have hnextStatus :=
      CompactBinaryNatRunningStatusSlice.directLayout hnextRunning
    have hcurrent := hcurrentCore.withStatus hcurrentStatus
    have hnext := hnextCore.withStatus hnextStatus
    have hsemantic :=
      (exists_stepGraphRows_iff_step hcurrent hnext).mp
        ⟨witness, Or.inr (Or.inr (Or.inr
          ⟨hbranch, hpositive, hcurrentRunning,
            hdecode, hcons, hnextRunning⟩))⟩
    exact ⟨(currentBits, currentDecoded, none),
      (nextBits, nextDecoded, none),
      hcurrent, hnext, hsemantic⟩

theorem exists_stepStateGraph_iff_realStepLayouts
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactBinaryNatStreamRowCoordinates} :
    (∃ currentSize nextSize witness,
        CompactBinaryNatStreamStepStateGraph
          tokenTable width tokenCount currentCoordinates nextCoordinates
            currentSize nextSize witness) ↔
      ∃ current next : BinaryNatStreamState,
        CompactBinaryNatStreamStateFixedLayout
          tokenTable width tokenCount currentCoordinates current ∧
        CompactBinaryNatStreamStateFixedLayout
          tokenTable width tokenCount nextCoordinates next ∧
        next = binaryNatStreamStep current := by
  constructor
  · rintro ⟨currentSize, nextSize, witness, hgraph⟩
    exact hgraph.realize
  · rintro ⟨current, next, hcurrent, hnext, hsemantic⟩
    rcases toCoreGraph (coreFixedLayout hcurrent) with
      ⟨currentSize, hcurrentGraph⟩
    rcases toCoreGraph (coreFixedLayout hnext) with
      ⟨nextSize, hnextGraph⟩
    rcases (exists_stepGraphRows_iff_step hcurrent hnext).mpr hsemantic with
      ⟨witness, hstep⟩
    exact ⟨currentSize, nextSize, witness,
      hcurrentGraph, hnextGraph, hstep⟩

#print axioms CompactBinaryNatRunningStatusSlice.directLayout
#print axioms CompactBinaryNatFailedStatusSlice.directLayout
#print axioms completedStatusDirectLayout_of_numericRows
#print axioms CompactBinaryNatStreamStepStateGraph.realize
#print axioms exists_stepStateGraph_iff_realStepLayouts

end FoundationCompactNumericListedDirectBinaryNatStreamStepRealization
