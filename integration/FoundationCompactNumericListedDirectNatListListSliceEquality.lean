import integration.FoundationCompactNumericListedDirectNatListSliceEquality

/-!
# Equality of complete direct nested-list slices

Equal list values have equal count headers.  Their element rows are equal
slice by slice, and concatenating those row equalities yields equality of the
complete additive encoding interval.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListListSliceEquality

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectNatListSliceEquality
open FoundationCompactNumericListedDirectTokenStreamInverse

theorem CompactFixedWidthTokenSlicesEq.append
    {tokenTable width tokenCount
      sourceStart sourceMiddle sourceFinish
      targetStart targetMiddle targetFinish : Nat}
    (hleft : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
      sourceStart sourceMiddle targetStart targetMiddle)
    (hright : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
      sourceMiddle sourceFinish targetMiddle targetFinish) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish := by
  rcases hleft with
    ⟨leftCount, hleftCount, hsourceMiddle, htargetMiddle,
      hsourceMiddleBound, htargetMiddleBound, hleftBits⟩
  rcases hright with
    ⟨rightCount, hrightCount, hsourceFinish, htargetFinish,
      hsourceFinishBound, htargetFinishBound, hrightBits⟩
  refine ⟨leftCount + rightCount, ?_, ?_, ?_,
    hsourceFinishBound, htargetFinishBound, ?_⟩
  · omega
  · omega
  · omega
  · intro offset hoffset bitIndex hbitIndex
    by_cases hleftOffset : offset < leftCount
    · exact hleftBits offset hleftOffset bitIndex hbitIndex
    · have hrightOffset : offset - leftCount < rightCount := by omega
      have hsourceOffset : sourceStart + offset =
          sourceMiddle + (offset - leftCount) := by omega
      have htargetOffset : targetStart + offset =
          targetMiddle + (offset - leftCount) := by omega
      rw [hsourceOffset, htargetOffset]
      exact hrightBits (offset - leftCount) hrightOffset
        bitIndex hbitIndex

theorem CompactAdditiveTokenCell.slicesEq_of_same_value
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish value : Nat}
    (hsource : CompactAdditiveTokenCell
      tokenTable width tokenCount sourceStart value sourceFinish)
    (htarget : CompactAdditiveTokenCell
      tokenTable width tokenCount targetStart value targetFinish) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish := by
  rcases hsource with ⟨hsourceStart, hsourceFinish, hsourceEntry⟩
  rcases htarget with ⟨htargetStart, htargetFinish, htargetEntry⟩
  refine ⟨1, by omega, hsourceFinish, htargetFinish,
    by omega, by omega, ?_⟩
  intro offset hoffset bitIndex hbitIndex
  have hoffsetZero : offset = 0 := by omega
  subst offset
  simpa using (hsourceEntry.2 bitIndex hbitIndex).trans
    (htargetEntry.2 bitIndex hbitIndex).symm

theorem CompactAdditiveNatListListDirectLayout.slicesEq_of_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceValues targetValues : List (List Nat)}
    (hsource : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceValues)
    (htarget : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetValues)
    (hvalues : sourceValues = targetValues) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish := by
  subst targetValues
  rcases hsource with
    ⟨sourceBoundary, sourceLayout, sourceRows, _hsourceSize⟩
  rcases htarget with
    ⟨targetBoundary, targetLayout, targetRows, _htargetSize⟩
  rcases sourceLayout with
    ⟨sourceBodyStart, _hsourceBodyStart,
      sourceHeader, sourceBoundaries⟩
  rcases targetLayout with
    ⟨targetBodyStart, _htargetBodyStart,
      targetHeader, targetBoundaries⟩
  have hheader : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
      sourceStart sourceBodyStart targetStart targetBodyStart :=
    CompactAdditiveTokenCell.slicesEq_of_same_value
      sourceHeader.1 targetHeader.1
  let rec bodySlices
      (index : Nat) (hindex : index ≤ sourceValues.length)
      (sourceCursor targetCursor : Nat)
      (hsourceCursor : CompactFixedWidthEntry
        sourceBoundary tokenCount index sourceCursor)
      (htargetCursor : CompactFixedWidthEntry
        targetBoundary tokenCount index targetCursor) :
      CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
        sourceCursor sourceFinish targetCursor targetFinish := by
    by_cases hend : index = sourceValues.length
    · subst index
      have hsourceCursorFinish : sourceCursor = sourceFinish :=
        (CompactFixedWidthEntry.value_eq_tableValue hsourceCursor).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            sourceBoundaries.2.2.2.1).symm
      have htargetCursorFinish : targetCursor = targetFinish :=
        (CompactFixedWidthEntry.value_eq_tableValue htargetCursor).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            targetBoundaries.2.2.2.1).symm
      subst sourceCursor
      subst targetCursor
      exact ⟨0, by omega, by omega, by omega,
        sourceBoundaries.2.1, targetBoundaries.2.1,
        fun offset hoffset _bitIndex _hbitIndex => by omega⟩
    · have hrow : index < sourceValues.length := by omega
      rcases sourceRows index hrow with
        ⟨sourceLeft, _hsourceLeft,
          sourceRight, _hsourceRight,
          hsourceLeftEntry, hsourceRightEntry, hsourceRow⟩
      rcases targetRows index hrow with
        ⟨targetLeft, _htargetLeft,
          targetRight, _htargetRight,
          htargetLeftEntry, htargetRightEntry, htargetRow⟩
      have hsourceLeft : sourceCursor = sourceLeft :=
        (CompactFixedWidthEntry.value_eq_tableValue hsourceCursor).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hsourceLeftEntry).symm
      have htargetLeft : targetCursor = targetLeft :=
        (CompactFixedWidthEntry.value_eq_tableValue htargetCursor).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            htargetLeftEntry).symm
      subst sourceLeft
      subst targetLeft
      have hrowSlices : CompactFixedWidthTokenSlicesEq
          tokenTable width tokenCount
          sourceCursor sourceRight targetCursor targetRight :=
        CompactAdditiveNatListDirectLayout.slicesEq_of_eq
          hsourceRow htargetRow rfl
      have htail := bodySlices (index + 1) (by omega)
        sourceRight targetRight hsourceRightEntry htargetRightEntry
      exact CompactFixedWidthTokenSlicesEq.append hrowSlices htail
    termination_by sourceValues.length - index
  have hbody : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
      sourceBodyStart sourceFinish targetBodyStart targetFinish :=
    bodySlices 0 (by omega) sourceBodyStart targetBodyStart
      sourceBoundaries.2.2.1 targetBoundaries.2.2.1
  exact CompactFixedWidthTokenSlicesEq.append hheader hbody

#print axioms CompactFixedWidthTokenSlicesEq.append
#print axioms CompactAdditiveTokenCell.slicesEq_of_same_value
#print axioms CompactAdditiveNatListListDirectLayout.slicesEq_of_eq

end FoundationCompactNumericListedDirectNatListListSliceEquality
