import integration.FoundationCompactNumericListedDirectCrossTableSliceEquality
import integration.FoundationCompactNumericListedDirectNatListListSliceEquality

/-!
# Equality of direct nested-list slices in different token tables

The nested-list layout has a count cell followed by one direct natural-list
layout per element.  Cross-table equality composes over those consecutive
pieces just as it does within a single table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectTokenStreamInverse

theorem CompactFixedWidthCrossTableSlicesEq.append
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceMiddle sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetMiddle targetFinish : Nat}
    (hleft : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceMiddle
      targetTable targetWidth targetTokenCount targetStart targetMiddle)
    (hright : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceMiddle sourceFinish
      targetTable targetWidth targetTokenCount targetMiddle targetFinish) :
    CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish := by
  rcases hleft with
    ⟨leftCount, hleftSourceCount, hleftTargetCount, hsourceMiddle, htargetMiddle,
      hsourceMiddleBound, htargetMiddleBound, hleftBits⟩
  rcases hright with
    ⟨rightCount, hrightSourceCount, hrightTargetCount, hsourceFinish, htargetFinish,
      hsourceFinishBound, htargetFinishBound, hrightBits⟩
  refine ⟨leftCount + rightCount, ?_, ?_, ?_, ?_,
    hsourceFinishBound, htargetFinishBound, ?_⟩
  · omega
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
      exact hrightBits (offset - leftCount) hrightOffset bitIndex hbitIndex

theorem CompactFixedWidthCrossTableSlicesEq.subslice
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish
      offset count : Nat}
    (heq : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish)
    (hwithin : offset + count ≤ sourceFinish - sourceStart) :
    CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount
        (sourceStart + offset) (sourceStart + offset + count)
      targetTable targetWidth targetTokenCount
        (targetStart + offset) (targetStart + offset + count) := by
  rcases heq with
    ⟨total, hsourceCount, htargetCount, hsourceFinish, htargetFinish,
      hsourceFinishBound, htargetFinishBound, hbits⟩
  refine ⟨count, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · intro innerOffset hinnerOffset bitIndex hbitIndex
    have htotalOffset : offset + innerOffset < total := by omega
    simpa [Nat.add_assoc] using hbits (offset + innerOffset) htotalOffset
      bitIndex hbitIndex

private theorem fixedWidthEntry_cross_true_iff
    {sourceTable sourceWidth sourceIndex
      targetTable targetWidth targetIndex value bitIndex : Nat}
    (hsource : CompactFixedWidthEntry
      sourceTable sourceWidth sourceIndex value)
    (htarget : CompactFixedWidthEntry
      targetTable targetWidth targetIndex value) :
    (bitIndex < sourceWidth ∧
        sourceTable.testBit (sourceIndex * sourceWidth + bitIndex) = true) ↔
      (bitIndex < targetWidth ∧
        targetTable.testBit (targetIndex * targetWidth + bitIndex) = true) := by
  constructor
  · rintro ⟨hsourceWidth, hsourceTrue⟩
    have hvalueTrue : value.testBit bitIndex = true := by
      rw [← hsource.2 bitIndex hsourceWidth]
      exact hsourceTrue
    have htargetWidth : bitIndex < targetWidth := by
      by_contra hnot
      have hvalueLt : value < 2 ^ bitIndex :=
        Nat.size_le.mp (htarget.1.trans (Nat.le_of_not_gt hnot))
      rw [Nat.testBit_eq_false_of_lt hvalueLt] at hvalueTrue
      simp at hvalueTrue
    refine ⟨htargetWidth, ?_⟩
    rw [htarget.2 bitIndex htargetWidth]
    exact hvalueTrue
  · rintro ⟨htargetWidth, htargetTrue⟩
    have hvalueTrue : value.testBit bitIndex = true := by
      rw [← htarget.2 bitIndex htargetWidth]
      exact htargetTrue
    have hsourceWidth : bitIndex < sourceWidth := by
      by_contra hnot
      have hvalueLt : value < 2 ^ bitIndex :=
        Nat.size_le.mp (hsource.1.trans (Nat.le_of_not_gt hnot))
      rw [Nat.testBit_eq_false_of_lt hvalueLt] at hvalueTrue
      simp at hvalueTrue
    refine ⟨hsourceWidth, ?_⟩
    rw [hsource.2 bitIndex hsourceWidth]
    exact hvalueTrue

theorem CompactAdditiveTokenCell.crossTableSlicesEq_of_same_value
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish value : Nat}
    (hsource : CompactAdditiveTokenCell
      sourceTable sourceWidth sourceTokenCount sourceStart value sourceFinish)
    (htarget : CompactAdditiveTokenCell
      targetTable targetWidth targetTokenCount targetStart value targetFinish) :
    CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish := by
  rcases hsource with ⟨hsourceStart, hsourceFinish, hsourceEntry⟩
  rcases htarget with ⟨htargetStart, htargetFinish, htargetEntry⟩
  refine ⟨1, by omega, by omega, hsourceFinish, htargetFinish,
    by omega, by omega, ?_⟩
  intro offset hoffset bitIndex _hbitIndex
  have hoffsetZero : offset = 0 := by omega
  subst offset
  simpa using fixedWidthEntry_cross_true_iff hsourceEntry htargetEntry
    (bitIndex := bitIndex)

theorem CompactFixedWidthCrossTableSlicesEq.of_natListListLayouts
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat}
    {values : List (List Nat)}
    (hsource : CompactAdditiveNatListListDirectLayout
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish values)
    (htarget : CompactAdditiveNatListListDirectLayout
      targetTable targetWidth targetTokenCount targetStart targetFinish values) :
    CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish := by
  rcases hsource with
    ⟨sourceBoundary, sourceLayout, sourceRows, _hsourceSize⟩
  rcases htarget with
    ⟨targetBoundary, targetLayout, targetRows, _htargetSize⟩
  rcases sourceLayout with
    ⟨sourceBodyStart, _hsourceBodyStart, sourceHeader, sourceBoundaries⟩
  rcases targetLayout with
    ⟨targetBodyStart, _htargetBodyStart, targetHeader, targetBoundaries⟩
  have hheader := CompactAdditiveTokenCell.crossTableSlicesEq_of_same_value
    sourceHeader.1 targetHeader.1
  let rec bodySlices
      (index : Nat) (hindex : index ≤ values.length)
      (sourceCursor targetCursor : Nat)
      (hsourceCursor : CompactFixedWidthEntry
        sourceBoundary sourceTokenCount index sourceCursor)
      (htargetCursor : CompactFixedWidthEntry
        targetBoundary targetTokenCount index targetCursor) :
      CompactFixedWidthCrossTableSlicesEq
        sourceTable sourceWidth sourceTokenCount sourceCursor sourceFinish
        targetTable targetWidth targetTokenCount targetCursor targetFinish := by
    by_cases hend : index = values.length
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
      exact ⟨0, by omega, by omega, by omega, by omega,
        sourceBoundaries.2.1, targetBoundaries.2.1,
        fun offset hoffset _bitIndex _hbitIndex => by omega⟩
    · have hrow : index < values.length := by omega
      rcases sourceRows index hrow with
        ⟨sourceLeft, _hsourceLeft, sourceRight, _hsourceRight,
          hsourceLeftEntry, hsourceRightEntry, hsourceRow⟩
      rcases targetRows index hrow with
        ⟨targetLeft, _htargetLeft, targetRight, _htargetRight,
          htargetLeftEntry, htargetRightEntry, htargetRow⟩
      have hsourceLeft : sourceCursor = sourceLeft :=
        (CompactFixedWidthEntry.value_eq_tableValue hsourceCursor).trans
          (CompactFixedWidthEntry.value_eq_tableValue hsourceLeftEntry).symm
      have htargetLeft : targetCursor = targetLeft :=
        (CompactFixedWidthEntry.value_eq_tableValue htargetCursor).trans
          (CompactFixedWidthEntry.value_eq_tableValue htargetLeftEntry).symm
      subst sourceLeft
      subst targetLeft
      have hrowSlices := CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
        hsourceRow htargetRow
      have htail := bodySlices (index + 1) (by omega)
        sourceRight targetRight hsourceRightEntry htargetRightEntry
      exact CompactFixedWidthCrossTableSlicesEq.append hrowSlices htail
    termination_by values.length - index
  have hbody := bodySlices 0 (by omega) sourceBodyStart targetBodyStart
    sourceBoundaries.2.2.1 targetBoundaries.2.2.1
  exact CompactFixedWidthCrossTableSlicesEq.append hheader hbody

theorem CompactFixedWidthCrossTableSlicesEq.natListListValues_eq
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat}
    {sourceValues targetValues : List (List Nat)}
    (heq : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish)
    (hsource : CompactAdditiveNatListListDirectLayout
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish sourceValues)
    (htarget : CompactAdditiveNatListListDirectLayout
      targetTable targetWidth targetTokenCount targetStart targetFinish targetValues) :
    targetValues = sourceValues := by
  rcases hsource with
    ⟨sourceBoundary, hsourceStructure, hsourceRows, _hsourceSize⟩
  rcases htarget with
    ⟨targetBoundary, htargetStructure, htargetRows, _htargetSize⟩
  rcases hsourceStructure with
    ⟨sourceBodyStart, _hsourceBodyBound, hsourceHeader, hsourceBoundary⟩
  rcases htargetStructure with
    ⟨targetBodyStart, _htargetBodyBound, htargetHeader, htargetBoundary⟩
  have hsourceBody : sourceBodyStart = sourceStart + 1 := hsourceHeader.1.2.1
  have htargetBody : targetBodyStart = targetStart + 1 := htargetHeader.1.2.1
  have hsourceStartFinish : sourceStart < sourceFinish := by
    have hbodyFinish :=
      FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.start_le_finish
        hsourceBoundary
    omega
  have hlengthSourceTarget : sourceValues.length = targetValues.length := by
    have hsourceCountEntry : CompactFixedWidthEntry sourceTable sourceWidth
        (sourceStart + 0) sourceValues.length := by
      simpa using hsourceHeader.1.2.2
    have htargetCountEntry : CompactFixedWidthEntry targetTable targetWidth
        (targetStart + 0) targetValues.length := by
      simpa using htargetHeader.1.2.2
    exact heq.entryValue_eq_at_offset (by omega) hsourceCountEntry htargetCountEntry
  have hitem
      (index : Nat) (hindex : index < sourceValues.length)
      (offset : Nat) (hoffset : offset < sourceFinish - sourceStart)
      (hsourceAt : CompactFixedWidthEntry sourceBoundary sourceTokenCount index
        (sourceStart + offset))
      (htargetAt : CompactFixedWidthEntry targetBoundary targetTokenCount index
        (targetStart + offset)) :
      targetValues.getI index = sourceValues.getI index ∧
      ∃ nextOffset,
        nextOffset = offset + 1 + (sourceValues.getI index).length ∧
        CompactFixedWidthEntry sourceBoundary sourceTokenCount (index + 1)
          (sourceStart + nextOffset) ∧
        CompactFixedWidthEntry targetBoundary targetTokenCount (index + 1)
          (targetStart + nextOffset) := by
    have htargetIndex : index < targetValues.length := by omega
    rcases hsourceRows index hindex with
      ⟨sourceLeft, _hsourceLeft, sourceRight, _hsourceRight,
        hsourceLeftEntry, hsourceRightEntry, hsourceValue⟩
    rcases htargetRows index htargetIndex with
      ⟨targetLeft, _htargetLeft, targetRight, _htargetRight,
        htargetLeftEntry, htargetRightEntry, htargetValue⟩
    have hsourceLeft : sourceLeft = sourceStart + offset :=
      (CompactFixedWidthEntry.value_eq_tableValue hsourceLeftEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hsourceAt).symm
    have htargetLeft : targetLeft = targetStart + offset :=
      (CompactFixedWidthEntry.value_eq_tableValue htargetLeftEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue htargetAt).symm
    have hsourceInnerFinish :=
      FoundationCompactNumericListedDirectVerifierPayloadEquality.CompactAdditiveNatListDirectLayout.finish_eq
        hsourceValue
    have htargetInnerFinish :=
      FoundationCompactNumericListedDirectVerifierPayloadEquality.CompactAdditiveNatListDirectLayout.finish_eq
        htargetValue
    have hinnerLength : (sourceValues.getI index).length =
        (targetValues.getI index).length := by
      have hsourceInnerHeader :=
        FoundationCompactNumericListedDirectVerifierPayloadEquality.CompactAdditiveNatListDirectLayout.headerEntry
          hsourceValue
      have htargetInnerHeader :=
        FoundationCompactNumericListedDirectVerifierPayloadEquality.CompactAdditiveNatListDirectLayout.headerEntry
          htargetValue
      rw [hsourceLeft] at hsourceInnerHeader
      rw [htargetLeft] at htargetInnerHeader
      exact heq.entryValue_eq_at_offset hoffset hsourceInnerHeader htargetInnerHeader
    let nextOffset := offset + 1 + (sourceValues.getI index).length
    have hsourceRight : sourceRight = sourceStart + nextOffset := by
      dsimp only [nextOffset]
      omega
    have htargetRight : targetRight = targetStart + nextOffset := by
      dsimp only [nextOffset]
      omega
    have hsourceRightFinish : sourceRight ≤ sourceFinish :=
      FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_mono
        hsourceBoundary (by omega) (by rfl) hsourceRightEntry hsourceBoundary.2.2.2.1
    have hwithin : offset + (1 + (sourceValues.getI index).length) ≤
        sourceFinish - sourceStart := by omega
    have hinnerSlices :=
      FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality.CompactFixedWidthCrossTableSlicesEq.subslice
        heq hwithin
    have hsourceValueAligned : CompactAdditiveNatListDirectLayout
        sourceTable sourceWidth sourceTokenCount
        (sourceStart + offset)
        (sourceStart + offset + (1 + (sourceValues.getI index).length))
        (sourceValues.getI index) := by
      simpa [hsourceLeft, hsourceRight, nextOffset, Nat.add_assoc] using hsourceValue
    have htargetValueAligned : CompactAdditiveNatListDirectLayout
        targetTable targetWidth targetTokenCount
        (targetStart + offset)
        (targetStart + offset + (1 + (sourceValues.getI index).length))
        (targetValues.getI index) := by
      simpa [htargetLeft, htargetRight, nextOffset, hinnerLength, Nat.add_assoc] using htargetValue
    have hinnerEq := CompactFixedWidthCrossTableSlicesEq.natListValues_eq
      hinnerSlices hsourceValueAligned htargetValueAligned
    refine ⟨hinnerEq, nextOffset, rfl, ?_, ?_⟩
    · simpa [hsourceRight] using hsourceRightEntry
    · simpa [htargetRight] using htargetRightEntry
  have haligned : ∀ index < sourceValues.length,
      ∃ offset, offset < sourceFinish - sourceStart ∧
        CompactFixedWidthEntry sourceBoundary sourceTokenCount index
          (sourceStart + offset) ∧
        CompactFixedWidthEntry targetBoundary targetTokenCount index
          (targetStart + offset) := by
    intro index hindex
    induction index with
    | zero =>
        refine ⟨1, ?_, ?_, ?_⟩
        · have hbodyFinish :=
            FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_lt_finish
              hsourceBoundary hindex hsourceBoundary.2.2.1
          omega
        · simpa [hsourceBody] using hsourceBoundary.2.2.1
        · simpa [htargetBody] using htargetBoundary.2.2.1
    | succ index ih =>
        have hprevious : index < sourceValues.length := by omega
        rcases ih hprevious with ⟨offset, hoffset, hsourceAt, htargetAt⟩
        rcases hitem index hprevious offset hoffset hsourceAt htargetAt with
          ⟨_hvalue, nextOffset, _hnextOffset, hsourceNext, htargetNext⟩
        have hnextInside :=
          FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_lt_finish
            hsourceBoundary hindex hsourceNext
        refine ⟨nextOffset, ?_, hsourceNext, htargetNext⟩
        omega
  apply List.ext_getElem
  · exact hlengthSourceTarget.symm
  · intro index htargetIndex hsourceIndex
    rcases haligned index hsourceIndex with ⟨offset, hoffset, hsourceAt, htargetAt⟩
    have hvalue := (hitem index hsourceIndex offset hoffset hsourceAt htargetAt).1
    simpa [List.getI_eq_getElem _ htargetIndex,
      List.getI_eq_getElem _ hsourceIndex] using hvalue

#print axioms CompactFixedWidthCrossTableSlicesEq.append
#print axioms CompactFixedWidthCrossTableSlicesEq.subslice
#print axioms CompactAdditiveTokenCell.crossTableSlicesEq_of_same_value
#print axioms CompactFixedWidthCrossTableSlicesEq.of_natListListLayouts
#print axioms CompactFixedWidthCrossTableSlicesEq.natListListValues_eq

end FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality
