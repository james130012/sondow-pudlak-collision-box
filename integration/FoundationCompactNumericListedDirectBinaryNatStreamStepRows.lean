import integration.FoundationCompactNumericListedDirectCompletedStatusSameRows
import integration.FoundationCompactNumericListedDirectBinaryNatDecodeFailure
import integration.FoundationCompactNumericListedDirectBoolListDropRows
import integration.FoundationCompactNumericListedDirectNatListConsRows
import integration.FoundationCompactNumericListedDirectBinaryNatStreamStateLayout

/-!
# Exact direct row graph of one binary-natural stream step

The state layouts are exposed through named numeric coordinates.  Four direct
row relations then represent the done, empty, decode-failure, and
decode-success branches without using a typed next-state equality as input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStepRows

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNatStreamMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStreamStateLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBoolListDropRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectBinaryNatDecodeFailure
open FoundationCompactNumericListedDirectCompletedStatusReverseRows
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepCases

structure CompactBinaryNatStreamRowCoordinates where
  start : Nat
  finish : Nat
  bitsFinish : Nat
  decodedFinish : Nat
  bitsBoundary : Nat
  bitsCount : Nat
  decodedBoundary : Nat
  decodedCount : Nat

structure CompactBinaryNatStreamStateFixedLayout
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactBinaryNatStreamRowCoordinates)
    (state : BinaryNatStreamState) : Prop where
  bitsCount_eq : coordinates.bitsCount = state.1.length
  decodedCount_eq : coordinates.decodedCount = state.2.1.length
  outerSplit : CompactAdditiveProductSplit
    tokenCount coordinates.start coordinates.bitsFinish coordinates.finish
  bitsLayout : CompactAdditiveStructuredListLayout
    tokenTable width tokenCount coordinates.start coordinates.bitsCount
      coordinates.bitsFinish coordinates.bitsBoundary
  bitsRows : CompactAdditiveStructuredListElementRowLayouts
    CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      coordinates.bitsBoundary state.1
  innerSplit : CompactAdditiveProductSplit
    tokenCount coordinates.bitsFinish coordinates.decodedFinish
      coordinates.finish
  decodedLayout : CompactAdditiveStructuredListLayout
    tokenTable width tokenCount coordinates.bitsFinish
      coordinates.decodedCount coordinates.decodedFinish
      coordinates.decodedBoundary
  decodedRows : CompactAdditiveStructuredListElementRowLayouts
    CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      coordinates.decodedBoundary state.2.1
  statusLayout : CompactBinaryNatStreamStatusDirectLayout
    tokenTable width tokenCount coordinates.decodedFinish
      coordinates.finish state.2.2
  bitsBoundarySize : Nat.size coordinates.bitsBoundary ≤
    (coordinates.bitsCount + 1) * tokenCount
  decodedBoundarySize : Nat.size coordinates.decodedBoundary ≤
    (coordinates.decodedCount + 1) * tokenCount

theorem compactBinaryNatStreamStateDirectLayout_iff_fixedCoordinates
    (tokenTable width tokenCount start finish : Nat)
    (state : BinaryNatStreamState) :
    CompactBinaryNatStreamStateDirectLayout
        tokenTable width tokenCount start finish state ↔
      ∃ coordinates : CompactBinaryNatStreamRowCoordinates,
        coordinates.start = start ∧
        coordinates.finish = finish ∧
        CompactBinaryNatStreamStateFixedLayout
          tokenTable width tokenCount coordinates state := by
  constructor
  · rintro ⟨bitsFinish, decodedFinish, bitsBoundary, decodedBoundary,
      houter, hbitsLayout, hbitsRows, hinner,
      hdecodedLayout, hdecodedRows, hstatus,
      hbitsSize, hdecodedSize⟩
    let coordinates : CompactBinaryNatStreamRowCoordinates :=
      { start := start
        finish := finish
        bitsFinish := bitsFinish
        decodedFinish := decodedFinish
        bitsBoundary := bitsBoundary
        bitsCount := state.1.length
        decodedBoundary := decodedBoundary
        decodedCount := state.2.1.length }
    refine ⟨coordinates, rfl, rfl, ?_⟩
    exact
      { bitsCount_eq := rfl
        decodedCount_eq := rfl
        outerSplit := houter
        bitsLayout := hbitsLayout
        bitsRows := hbitsRows
        innerSplit := hinner
        decodedLayout := hdecodedLayout
        decodedRows := hdecodedRows
        statusLayout := hstatus
        bitsBoundarySize := hbitsSize
        decodedBoundarySize := hdecodedSize }
  · rintro ⟨coordinates, hstart, hfinish, hlayout⟩
    rw [← hstart, ← hfinish]
    refine ⟨coordinates.bitsFinish, coordinates.decodedFinish,
      coordinates.bitsBoundary, coordinates.decodedBoundary,
      hlayout.outerSplit, ?_, hlayout.bitsRows,
      hlayout.innerSplit, ?_, hlayout.decodedRows,
      hlayout.statusLayout, ?_, ?_⟩
    · simpa only [hlayout.bitsCount_eq] using hlayout.bitsLayout
    · simpa only [hlayout.decodedCount_eq] using hlayout.decodedLayout
    · simpa only [hlayout.bitsCount_eq] using hlayout.bitsBoundarySize
    · simpa only [hlayout.decodedCount_eq] using
        hlayout.decodedBoundarySize

def CompactBinaryNatCompletedOutputReverseRowsExists
    (tokenTable width tokenCount statusStart statusFinish
      sourceBoundary sourceCount : Nat) : Prop :=
  ∃ outputStart outputBoundary,
    CompactBinaryNatCompletedOutputReverseRows
      tokenTable width tokenCount statusStart statusFinish
        sourceBoundary sourceCount outputStart outputBoundary

def CompactBinaryNatCompletedStatusSameRowsExists
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish : Nat) : Prop :=
  ∃ sourceOutputStart sourceOutputBoundary
      targetOutputStart targetOutputBoundary outputCount,
    CompactBinaryNatCompletedStatusSameRows
      tokenTable width tokenCount
        sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish
        sourceOutputStart sourceOutputBoundary
        targetOutputStart targetOutputBoundary outputCount

def CompactAdditiveBoolListDecodeFailureRowsExists
    (tokenTable width tokenCount boundaryTable bitCount : Nat) : Prop :=
  ∃ payload,
    CompactAdditiveBoolListDecodeFailureRows
      tokenTable width tokenCount boundaryTable bitCount payload

def CompactAdditiveBoolListDecodeSuccessRowsExists
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount token : Nat) :
    Prop :=
  ∃ payload digitCount consumed,
    CompactAdditiveBoolListDecodeSuccessRows
      tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount
        payload digitCount token consumed

def CompactBinaryNatStreamDoneRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactBinaryNatStreamRowCoordinates) : Prop :=
  CompactAdditiveBoolListDropRows
      tokenTable width tokenCount
        current.bitsBoundary current.bitsCount
        next.bitsBoundary next.bitsCount 0 ∧
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount
        current.decodedBoundary current.decodedCount
        next.decodedBoundary next.decodedCount ∧
    ((CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount current.decodedFinish current.finish ∧
      CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount next.decodedFinish next.finish) ∨
      CompactBinaryNatCompletedStatusSameRowsExists
        tokenTable width tokenCount
          current.decodedFinish current.finish
          next.decodedFinish next.finish)

def CompactBinaryNatStreamEmptyRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactBinaryNatStreamRowCoordinates) : Prop :=
  current.bitsCount = 0 ∧
    next.bitsCount = 0 ∧
    CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount current.decodedFinish current.finish ∧
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount
        current.decodedBoundary current.decodedCount
        next.decodedBoundary next.decodedCount ∧
    CompactBinaryNatCompletedOutputReverseRowsExists
      tokenTable width tokenCount next.decodedFinish next.finish
        current.decodedBoundary current.decodedCount

def CompactBinaryNatStreamDecodeFailureRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactBinaryNatStreamRowCoordinates) : Prop :=
  0 < current.bitsCount ∧
    CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount current.decodedFinish current.finish ∧
    CompactAdditiveBoolListDecodeFailureRowsExists
      tokenTable width tokenCount
        current.bitsBoundary current.bitsCount ∧
    CompactAdditiveBoolListDropRows
      tokenTable width tokenCount
        current.bitsBoundary current.bitsCount
        next.bitsBoundary next.bitsCount 0 ∧
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount
        current.decodedBoundary current.decodedCount
        next.decodedBoundary next.decodedCount ∧
    CompactBinaryNatFailedStatusSlice
      tokenTable width tokenCount next.decodedFinish next.finish

def CompactBinaryNatStreamDecodeSuccessRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactBinaryNatStreamRowCoordinates) : Prop :=
  0 < current.bitsCount ∧
    CompactBinaryNatRunningStatusSlice
      tokenTable width tokenCount current.decodedFinish current.finish ∧
    ∃ token,
      CompactAdditiveBoolListDecodeSuccessRowsExists
          tokenTable width tokenCount
            current.bitsBoundary current.bitsCount
            next.bitsBoundary next.bitsCount token ∧
        CompactAdditiveNatListConsRows
          tokenTable width tokenCount
            current.decodedBoundary current.decodedCount
            next.decodedBoundary next.decodedCount token ∧
        CompactBinaryNatRunningStatusSlice
          tokenTable width tokenCount next.decodedFinish next.finish

def CompactBinaryNatStreamStepRows
    (tokenTable width tokenCount : Nat)
    (current next : CompactBinaryNatStreamRowCoordinates) : Prop :=
  CompactBinaryNatStreamDoneRows tokenTable width tokenCount current next ∨
    CompactBinaryNatStreamEmptyRows tokenTable width tokenCount current next ∨
    CompactBinaryNatStreamDecodeFailureRows
      tokenTable width tokenCount current next ∨
    CompactBinaryNatStreamDecodeSuccessRows
      tokenTable width tokenCount current next

theorem compactBinaryNatStreamDoneRows_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactBinaryNatStreamRowCoordinates}
    {current next : BinaryNatStreamState}
    (hcurrent : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    CompactBinaryNatStreamDoneRows
        tokenTable width tokenCount currentCoordinates nextCoordinates ↔
      BinaryNatStreamStepDoneCase current next := by
  constructor
  · rintro ⟨hbitsRows, hdecodedRows, hstatusRows⟩
    have hbitsRows' : CompactAdditiveBoolListDropRows
        tokenTable width tokenCount
          currentCoordinates.bitsBoundary current.1.length
          nextCoordinates.bitsBoundary next.1.length 0 := by
      simpa only [hcurrent.bitsCount_eq, hnext.bitsCount_eq] using hbitsRows
    have hbits : next.1 = current.1 := by
      simpa using
        (CompactAdditiveBoolListDropRows.eq_drop_of_rows
          hbitsRows' hcurrent.bitsRows hnext.bitsRows)
    have hdecodedRows' : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          currentCoordinates.decodedBoundary current.2.1.length
          nextCoordinates.decodedBoundary next.2.1.length := by
      simpa only [hcurrent.decodedCount_eq,
        hnext.decodedCount_eq] using hdecodedRows
    have hdecoded : next.2.1 = current.2.1 :=
      CompactAdditiveNatListSameRows.eq_of_rows
        hdecodedRows' hcurrent.decodedRows hnext.decodedRows
    rcases hstatusRows with hfailed | hcompleted
    · have hcurrentStatus : current.2.2 = some none :=
        (CompactBinaryNatStreamStatusDirectLayout.failed_iff
          hcurrent.statusLayout).mp hfailed.1
      have hnextStatus : next.2.2 = some none :=
        (CompactBinaryNatStreamStatusDirectLayout.failed_iff
          hnext.statusLayout).mp hfailed.2
      have hstate : next = current := by
        rcases current with ⟨currentBits, currentDecoded, currentStatus⟩
        rcases next with ⟨nextBits, nextDecoded, nextStatus⟩
        simp only at hbits hdecoded hcurrentStatus hnextStatus ⊢
        simp [hbits, hdecoded, hcurrentStatus, hnextStatus]
      exact ⟨none, hcurrentStatus, hstate⟩
    · rcases
          (completedStatusSameRows_iff
            hcurrent.statusLayout hnext.statusLayout).mp hcompleted with
        ⟨output, hcurrentStatus, hnextStatus⟩
      have hstate : next = current := by
        rcases current with ⟨currentBits, currentDecoded, currentStatus⟩
        rcases next with ⟨nextBits, nextDecoded, nextStatus⟩
        simp only at hbits hdecoded hcurrentStatus hnextStatus ⊢
        simp [hbits, hdecoded, hcurrentStatus, hnextStatus]
      exact ⟨some output, hcurrentStatus, hstate⟩
  · rintro ⟨result, hcurrentStatus, hstate⟩
    subst next
    have hbitsRows : CompactAdditiveBoolListDropRows
        tokenTable width tokenCount
          currentCoordinates.bitsBoundary current.1.length
          nextCoordinates.bitsBoundary current.1.length 0 :=
      CompactAdditiveStructuredListElementRowLayouts.boolDropRows
        hcurrent.bitsRows hnext.bitsRows (by simp) (by simp)
    have hdecodedRows : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          currentCoordinates.decodedBoundary current.2.1.length
          nextCoordinates.decodedBoundary current.2.1.length :=
      CompactAdditiveStructuredListElementRowLayouts.natSameRows
        hcurrent.decodedRows hnext.decodedRows rfl
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hcurrent.bitsCount_eq,
        hnext.bitsCount_eq] using hbitsRows
    · simpa only [hcurrent.decodedCount_eq,
        hnext.decodedCount_eq] using hdecodedRows
    · cases result with
      | none =>
          left
          exact
            ⟨(CompactBinaryNatStreamStatusDirectLayout.failed_iff
                hcurrent.statusLayout).mpr hcurrentStatus,
              (CompactBinaryNatStreamStatusDirectLayout.failed_iff
                hnext.statusLayout).mpr hcurrentStatus⟩
      | some output =>
          right
          exact (completedStatusSameRows_iff
            hcurrent.statusLayout hnext.statusLayout).mpr
              ⟨output, hcurrentStatus, hcurrentStatus⟩

theorem compactBinaryNatStreamEmptyRows_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactBinaryNatStreamRowCoordinates}
    {current next : BinaryNatStreamState}
    (hcurrent : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    CompactBinaryNatStreamEmptyRows
        tokenTable width tokenCount currentCoordinates nextCoordinates ↔
      BinaryNatStreamStepEmptyCase current next := by
  constructor
  · rintro ⟨hcurrentCount, hnextCount, hcurrentRunning,
      hdecodedRows, hcompleted⟩
    have hcurrentBits : current.1 = [] := by
      exact List.eq_nil_of_length_eq_zero
        (hcurrent.bitsCount_eq.symm.trans hcurrentCount)
    have hnextBits : next.1 = [] := by
      exact List.eq_nil_of_length_eq_zero
        (hnext.bitsCount_eq.symm.trans hnextCount)
    have hcurrentStatus : current.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mp hcurrentRunning
    have hdecodedRows' : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          currentCoordinates.decodedBoundary current.2.1.length
          nextCoordinates.decodedBoundary next.2.1.length := by
      simpa only [hcurrent.decodedCount_eq,
        hnext.decodedCount_eq] using hdecodedRows
    have hdecoded : next.2.1 = current.2.1 :=
      CompactAdditiveNatListSameRows.eq_of_rows
        hdecodedRows' hcurrent.decodedRows hnext.decodedRows
    have hnextStatus :
        next.2.2 = some (some current.2.1.reverse) :=
      (completedOutputReverseRows_iff
        hcurrent.decodedRows hnext.statusLayout).mp (by
          simpa only [CompactBinaryNatCompletedOutputReverseRowsExists,
            hcurrent.decodedCount_eq] using hcompleted)
    refine ⟨hcurrentStatus, hcurrentBits, ?_⟩
    rcases current with ⟨currentBits, currentDecoded, currentStatus⟩
    rcases next with ⟨nextBits, nextDecoded, nextStatus⟩
    simp only at hcurrentBits hnextBits hdecoded hnextStatus ⊢
    simp [hnextBits, hdecoded, hnextStatus]
  · rintro ⟨hcurrentStatus, hcurrentBits, hstate⟩
    subst next
    have hcurrentCount : currentCoordinates.bitsCount = 0 := by
      simpa [hcurrentBits] using hcurrent.bitsCount_eq
    have hnextCount : nextCoordinates.bitsCount = 0 := by
      simpa using hnext.bitsCount_eq
    have hcurrentRunning : CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount
          currentCoordinates.decodedFinish currentCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mpr hcurrentStatus
    have hdecodedRows : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          currentCoordinates.decodedBoundary current.2.1.length
          nextCoordinates.decodedBoundary current.2.1.length :=
      CompactAdditiveStructuredListElementRowLayouts.natSameRows
        hcurrent.decodedRows hnext.decodedRows rfl
    have hcompleted : CompactBinaryNatCompletedOutputReverseRowsExists
        tokenTable width tokenCount
          nextCoordinates.decodedFinish nextCoordinates.finish
          currentCoordinates.decodedBoundary current.2.1.length :=
      (completedOutputReverseRows_iff
        hcurrent.decodedRows hnext.statusLayout).mpr rfl
    refine ⟨hcurrentCount, hnextCount, hcurrentRunning, ?_, ?_⟩
    · simpa only [hcurrent.decodedCount_eq,
        hnext.decodedCount_eq] using hdecodedRows
    · simpa only [hcurrent.decodedCount_eq] using hcompleted

theorem compactBinaryNatStreamDecodeFailureRows_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactBinaryNatStreamRowCoordinates}
    {current next : BinaryNatStreamState}
    (hcurrent : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    CompactBinaryNatStreamDecodeFailureRows
        tokenTable width tokenCount currentCoordinates nextCoordinates ↔
      BinaryNatStreamStepDecodeFailureCase current next := by
  constructor
  · rintro ⟨hpositive, hcurrentRunning, hdecodeFailure,
      hbitsRows, hdecodedRows, hnextFailed⟩
    have hcurrentStatus : current.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mp hcurrentRunning
    have hcurrentBits : current.1 ≠ [] := by
      intro hnil
      have hcountZero : currentCoordinates.bitsCount = 0 := by
        simpa [hnil] using hcurrent.bitsCount_eq
      omega
    have hdecode : decodeBinaryNat current.1 = none :=
      (decodeBinaryNat_eq_none_iff_directBoolListRows
        hcurrent.bitsRows).mpr (by
          simpa only [CompactAdditiveBoolListDecodeFailureRowsExists,
            hcurrent.bitsCount_eq] using hdecodeFailure)
    have hbitsRows' : CompactAdditiveBoolListDropRows
        tokenTable width tokenCount
          currentCoordinates.bitsBoundary current.1.length
          nextCoordinates.bitsBoundary next.1.length 0 := by
      simpa only [hcurrent.bitsCount_eq,
        hnext.bitsCount_eq] using hbitsRows
    have hbits : next.1 = current.1 := by
      simpa using
        (CompactAdditiveBoolListDropRows.eq_drop_of_rows
          hbitsRows' hcurrent.bitsRows hnext.bitsRows)
    have hdecodedRows' : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          currentCoordinates.decodedBoundary current.2.1.length
          nextCoordinates.decodedBoundary next.2.1.length := by
      simpa only [hcurrent.decodedCount_eq,
        hnext.decodedCount_eq] using hdecodedRows
    have hdecoded : next.2.1 = current.2.1 :=
      CompactAdditiveNatListSameRows.eq_of_rows
        hdecodedRows' hcurrent.decodedRows hnext.decodedRows
    have hnextStatus : next.2.2 = some none :=
      (CompactBinaryNatStreamStatusDirectLayout.failed_iff
        hnext.statusLayout).mp hnextFailed
    refine ⟨hcurrentStatus, hcurrentBits, hdecode, ?_⟩
    rcases current with ⟨currentBits, currentDecoded, currentStatus⟩
    rcases next with ⟨nextBits, nextDecoded, nextStatus⟩
    simp only at hbits hdecoded hnextStatus ⊢
    simp [hbits, hdecoded, hnextStatus]
  · rintro ⟨hcurrentStatus, hcurrentBits, hdecode, hstate⟩
    subst next
    have hpositive : 0 < currentCoordinates.bitsCount := by
      rw [hcurrent.bitsCount_eq]
      exact List.length_pos_iff.mpr hcurrentBits
    have hcurrentRunning : CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount
          currentCoordinates.decodedFinish currentCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mpr hcurrentStatus
    have hdecodeFailure : CompactAdditiveBoolListDecodeFailureRowsExists
        tokenTable width tokenCount
          currentCoordinates.bitsBoundary current.1.length :=
      (decodeBinaryNat_eq_none_iff_directBoolListRows
        hcurrent.bitsRows).mp hdecode
    have hbitsRows : CompactAdditiveBoolListDropRows
        tokenTable width tokenCount
          currentCoordinates.bitsBoundary current.1.length
          nextCoordinates.bitsBoundary current.1.length 0 :=
      CompactAdditiveStructuredListElementRowLayouts.boolDropRows
        hcurrent.bitsRows hnext.bitsRows (by simp) (by simp)
    have hdecodedRows : CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          currentCoordinates.decodedBoundary current.2.1.length
          nextCoordinates.decodedBoundary current.2.1.length :=
      CompactAdditiveStructuredListElementRowLayouts.natSameRows
        hcurrent.decodedRows hnext.decodedRows rfl
    have hnextFailed : CompactBinaryNatFailedStatusSlice
        tokenTable width tokenCount
          nextCoordinates.decodedFinish nextCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.failed_iff
        hnext.statusLayout).mpr rfl
    refine ⟨hpositive, hcurrentRunning, ?_, ?_, ?_, hnextFailed⟩
    · simpa only [hcurrent.bitsCount_eq] using hdecodeFailure
    · simpa only [hcurrent.bitsCount_eq,
        hnext.bitsCount_eq] using hbitsRows
    · simpa only [hcurrent.decodedCount_eq,
        hnext.decodedCount_eq] using hdecodedRows

theorem compactBinaryNatStreamDecodeSuccessRows_iff
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactBinaryNatStreamRowCoordinates}
    {current next : BinaryNatStreamState}
    (hcurrent : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    CompactBinaryNatStreamDecodeSuccessRows
        tokenTable width tokenCount currentCoordinates nextCoordinates ↔
      BinaryNatStreamStepDecodeSuccessCase current next := by
  constructor
  · rintro ⟨hpositive, hcurrentRunning, token,
      hdecodeRows, hconsRows, hnextRunning⟩
    have hcurrentStatus : current.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mp hcurrentRunning
    have hcurrentBits : current.1 ≠ [] := by
      intro hnil
      have hcountZero : currentCoordinates.bitsCount = 0 := by
        simpa [hnil] using hcurrent.bitsCount_eq
      omega
    have hdecode : decodeBinaryNat current.1 = some (token, next.1) :=
      (decodeBinaryNat_eq_some_iff_directBoolListRows
        hcurrent.bitsRows hnext.bitsRows).mpr (by
          simpa only [CompactAdditiveBoolListDecodeSuccessRowsExists,
            hcurrent.bitsCount_eq,
            hnext.bitsCount_eq] using hdecodeRows)
    have hconsRows' : CompactAdditiveNatListConsRows
        tokenTable width tokenCount
          currentCoordinates.decodedBoundary current.2.1.length
          nextCoordinates.decodedBoundary next.2.1.length token := by
      simpa only [hcurrent.decodedCount_eq,
        hnext.decodedCount_eq] using hconsRows
    have hdecoded : next.2.1 = token :: current.2.1 :=
      CompactAdditiveNatListConsRows.eq_cons_of_rows
        hconsRows' hcurrent.decodedRows hnext.decodedRows
    have hnextStatus : next.2.2 = none :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hnext.statusLayout).mp hnextRunning
    refine ⟨token, next.1, hcurrentStatus, hcurrentBits, hdecode, ?_⟩
    rcases current with ⟨currentBits, currentDecoded, currentStatus⟩
    rcases next with ⟨nextBits, nextDecoded, nextStatus⟩
    simp only at hdecoded hnextStatus ⊢
    simp [hdecoded, hnextStatus]
  · rintro ⟨token, suffix, hcurrentStatus,
      hcurrentBits, hdecode, hstate⟩
    subst next
    have hpositive : 0 < currentCoordinates.bitsCount := by
      rw [hcurrent.bitsCount_eq]
      exact List.length_pos_iff.mpr hcurrentBits
    have hcurrentRunning : CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount
          currentCoordinates.decodedFinish currentCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hcurrent.statusLayout).mpr hcurrentStatus
    have hdecodeRows : CompactAdditiveBoolListDecodeSuccessRowsExists
        tokenTable width tokenCount
          currentCoordinates.bitsBoundary current.1.length
          nextCoordinates.bitsBoundary suffix.length token :=
      (decodeBinaryNat_eq_some_iff_directBoolListRows
        hcurrent.bitsRows hnext.bitsRows).mp hdecode
    have hconsRows : CompactAdditiveNatListConsRows
        tokenTable width tokenCount
          currentCoordinates.decodedBoundary current.2.1.length
          nextCoordinates.decodedBoundary (token :: current.2.1).length
          token :=
      CompactAdditiveStructuredListElementRowLayouts.natConsRows
        hcurrent.decodedRows hnext.decodedRows rfl
    have hnextRunning : CompactBinaryNatRunningStatusSlice
        tokenTable width tokenCount
          nextCoordinates.decodedFinish nextCoordinates.finish :=
      (CompactBinaryNatStreamStatusDirectLayout.running_iff
        hnext.statusLayout).mpr rfl
    refine ⟨hpositive, hcurrentRunning, token, ?_, ?_, hnextRunning⟩
    · simpa only [hcurrent.bitsCount_eq,
        hnext.bitsCount_eq] using hdecodeRows
    · simpa only [hcurrent.decodedCount_eq,
        hnext.decodedCount_eq] using hconsRows

theorem compactBinaryNatStreamStepRows_iff_cases
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactBinaryNatStreamRowCoordinates}
    {current next : BinaryNatStreamState}
    (hcurrent : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    CompactBinaryNatStreamStepRows
        tokenTable width tokenCount currentCoordinates nextCoordinates ↔
      BinaryNatStreamStepCases current next := by
  simp only [CompactBinaryNatStreamStepRows, BinaryNatStreamStepCases]
  rw [compactBinaryNatStreamDoneRows_iff hcurrent hnext]
  rw [compactBinaryNatStreamEmptyRows_iff hcurrent hnext]
  rw [compactBinaryNatStreamDecodeFailureRows_iff hcurrent hnext]
  rw [compactBinaryNatStreamDecodeSuccessRows_iff hcurrent hnext]

theorem compactBinaryNatStreamStepRows_iff_step
    {tokenTable width tokenCount : Nat}
    {currentCoordinates nextCoordinates :
      CompactBinaryNatStreamRowCoordinates}
    {current next : BinaryNatStreamState}
    (hcurrent : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount currentCoordinates current)
    (hnext : CompactBinaryNatStreamStateFixedLayout
      tokenTable width tokenCount nextCoordinates next) :
    CompactBinaryNatStreamStepRows
        tokenTable width tokenCount currentCoordinates nextCoordinates ↔
      next = binaryNatStreamStep current := by
  rw [compactBinaryNatStreamStepRows_iff_cases hcurrent hnext]
  exact binaryNatStreamStepCases_iff current next

#print axioms compactBinaryNatStreamStateDirectLayout_iff_fixedCoordinates
#print axioms compactBinaryNatStreamDoneRows_iff
#print axioms compactBinaryNatStreamEmptyRows_iff
#print axioms compactBinaryNatStreamDecodeFailureRows_iff
#print axioms compactBinaryNatStreamDecodeSuccessRows_iff
#print axioms compactBinaryNatStreamStepRows_iff_cases
#print axioms compactBinaryNatStreamStepRows_iff_step

end FoundationCompactNumericListedDirectBinaryNatStreamStepRows
