import integration.FoundationCompactNumericListedDirectVerifierFinishRealization
import integration.FoundationCompactNumericListedDirectTokenSliceEquality

/-!
# Determinacy of realized verifier payloads

Equal fixed-width token slices determine equal typed payload components.  The
first layer below handles flat natural-number lists and is reused for proof and
certificate streams as well as nested formula-token lists.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPayloadEquality

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectTokenSliceEquality

theorem compactAdditiveBoolTag_injective :
    Function.Injective compactAdditiveBoolTag := by
  intro left right heq
  cases left <;> cases right <;>
    simp [compactAdditiveBoolTag] at heq ⊢

theorem CompactAdditiveStructuredListLayout.start_lt_finish
    {tokenTable width tokenCount start count finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable) :
    start < finish := by
  rcases hlayout with
    ⟨bodyStart, _hbodyStart, hheader, hboundary⟩
  have hbody : bodyStart = start + 1 := hheader.1.2.1
  have hbodyFinish :=
    FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.start_le_finish
      hboundary
  omega

theorem CompactAdditiveStructuredListLayout.finish_eq_start_add_one_of_count_zero
    {tokenTable width tokenCount start finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start 0 finish boundaryTable) :
    finish = start + 1 := by
  rcases hlayout with
    ⟨bodyStart, _hbodyStart, hheader, hboundary⟩
  have hbody : bodyStart = start + 1 := hheader.1.2.1
  have hfinishBody : finish = bodyStart :=
    (CompactFixedWidthEntry.value_eq_tableValue
      hboundary.2.2.2.1).trans
      (CompactFixedWidthEntry.value_eq_tableValue hboundary.2.2.1).symm
  omega

theorem CompactAdditiveNatListDirectLayout.valueEntry
    {tokenTable width tokenCount start finish : Nat}
    {values : List Nat}
    (hlayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount start finish values)
    (index : Nat) (hindex : index < values.length) :
    CompactFixedWidthEntry tokenTable width (start + 1 + index)
      (values.getI index) := by
  rcases hlayout with
    ⟨boundaryTable, hstructure, hrows, _hsize⟩
  have hunit :=
    CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows hrows
  have hcanonical :=
    CompactAdditiveStructuredListLayout.entry_eq_start_add
      hstructure hunit index (by omega)
  rcases hrows index hindex with
    ⟨left, _hleft, right, _hright,
      hleftEntry, _hrightEntry, hvalue⟩
  have hleft : left = start + 1 + index :=
    (CompactFixedWidthEntry.value_eq_tableValue hleftEntry).trans
      (CompactFixedWidthEntry.value_eq_tableValue hcanonical).symm
  simpa [hleft] using hvalue.2.2

theorem CompactAdditiveNatListDirectLayout.finish_eq
    {tokenTable width tokenCount start finish : Nat}
    {values : List Nat}
    (hlayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount start finish values) :
    finish = start + 1 + values.length := by
  rcases hlayout with
    ⟨_boundaryTable, hstructure, hrows, _hsize⟩
  have hunit :=
    CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows hrows
  exact CompactAdditiveStructuredListLayout.finish_eq_start_add_count
    hstructure hunit

theorem CompactAdditiveNatListDirectLayout.headerEntry
    {tokenTable width tokenCount start finish : Nat}
    {values : List Nat}
    (hlayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount start finish values) :
    CompactFixedWidthEntry tokenTable width start values.length := by
  rcases hlayout with
    ⟨_boundaryTable, hstructure, _hrows, _hsize⟩
  rcases hstructure with
    ⟨_bodyStart, _hbodyStart, hheader, _hboundary⟩
  exact hheader.1.2.2

theorem CompactFixedWidthTokenSlicesEq.natListValues_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceValues targetValues : List Nat}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish)
    (hsource : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceValues)
    (htarget : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetValues) :
    targetValues = sourceValues := by
  have hsourceFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hsource
  have htargetFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq htarget
  rcases heq with
    ⟨count, _hcount, hsourceCount, htargetCount,
      _hsourceBound, _htargetBound, hbits⟩
  have hlength : targetValues.length = sourceValues.length := by
    omega
  apply List.ext_getElem
  · exact hlength
  · intro index htargetIndex hsourceIndex
    have hsourceEntry :=
      CompactAdditiveNatListDirectLayout.valueEntry
        hsource index hsourceIndex
    have htargetEntry :=
      CompactAdditiveNatListDirectLayout.valueEntry
        htarget index htargetIndex
    have hoffset : 1 + index < count := by omega
    have hsourceValue : sourceValues[index] =
        compactFixedWidthTableValue tokenTable width
          (sourceStart + (1 + index)) := by
      rw [← List.getI_eq_getElem sourceValues hsourceIndex]
      simpa [Nat.add_assoc] using
        (CompactFixedWidthEntry.value_eq_tableValue hsourceEntry)
    have htargetValue : targetValues[index] =
        compactFixedWidthTableValue tokenTable width
          (targetStart + (1 + index)) := by
      rw [← List.getI_eq_getElem targetValues htargetIndex]
      simpa [Nat.add_assoc] using
        (CompactFixedWidthEntry.value_eq_tableValue htargetEntry)
    rw [hsourceValue, htargetValue]
    apply Nat.eq_of_testBit_eq
    intro bitIndex
    by_cases hbitIndex : bitIndex < width
    · exact (compactFixedWidthTableValue_testBit
          tokenTable width (targetStart + (1 + index)) bitIndex
          hbitIndex).trans
        ((hbits (1 + index) hoffset bitIndex hbitIndex).symm.trans
          (compactFixedWidthTableValue_testBit
            tokenTable width (sourceStart + (1 + index)) bitIndex
            hbitIndex).symm)
    · have hwidth : width ≤ bitIndex := Nat.le_of_not_gt hbitIndex
      have hsourceSize := compactFixedWidthTableValue_size_le
        tokenTable width (sourceStart + (1 + index))
      have htargetSize := compactFixedWidthTableValue_size_le
        tokenTable width (targetStart + (1 + index))
      rw [Nat.testBit_eq_false_of_lt
          (Nat.size_le.mp (hsourceSize.trans hwidth)),
        Nat.testBit_eq_false_of_lt
          (Nat.size_le.mp (htargetSize.trans hwidth))]

theorem CompactFixedWidthTokenSlicesEq.natListPrefix_eq
    {tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit
      sourceStart sourceFinish targetStart targetFinish offset : Nat}
    {sourceValues targetValues : List Nat}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit)
    (hsourceStart : sourceStart = sourceBase + offset)
    (htargetStart : targetStart = targetBase + offset)
    (hoffset : offset < sourceLimit - sourceBase)
    (hsourceFinishBound : sourceFinish ≤ sourceLimit)
    (_htargetFinishBound : targetFinish ≤ targetLimit)
    (hsource : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceValues)
    (htarget : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetValues) :
    ∃ finishOffset,
      sourceFinish = sourceBase + finishOffset ∧
      targetFinish = targetBase + finishOffset ∧
      targetValues = sourceValues := by
  have hsourceHeader :=
    CompactAdditiveNatListDirectLayout.headerEntry hsource
  have htargetHeader :=
    CompactAdditiveNatListDirectLayout.headerEntry htarget
  have hsourceHeaderAligned : CompactFixedWidthEntry tokenTable width
      (sourceBase + offset) sourceValues.length := by
    simpa [hsourceStart] using hsourceHeader
  have htargetHeaderAligned : CompactFixedWidthEntry tokenTable width
      (targetBase + offset) targetValues.length := by
    simpa [htargetStart] using htargetHeader
  have hlength : sourceValues.length = targetValues.length :=
    CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
      heq hoffset hsourceHeaderAligned htargetHeaderAligned
  have hsourceFinishDirect :=
    CompactAdditiveNatListDirectLayout.finish_eq hsource
  have htargetFinishDirect :=
    CompactAdditiveNatListDirectLayout.finish_eq htarget
  let finishOffset := offset + 1 + sourceValues.length
  have hsourceFinish : sourceFinish = sourceBase + finishOffset := by
    dsimp only [finishOffset]
    omega
  have htargetFinish : targetFinish = targetBase + finishOffset := by
    dsimp only [finishOffset]
    omega
  have hwithin :
      offset + (1 + sourceValues.length) ≤
        sourceLimit - sourceBase := by
    omega
  have hslices := CompactFixedWidthTokenSlicesEq.subslice
    heq offset (1 + sourceValues.length) hwithin
  have hsourceAligned : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount
      (sourceBase + offset)
      (sourceBase + offset + (1 + sourceValues.length)) sourceValues := by
    simpa [hsourceStart, hsourceFinish, finishOffset,
      Nat.add_assoc] using hsource
  have htargetAligned : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount
      (targetBase + offset)
      (targetBase + offset + (1 + sourceValues.length)) targetValues := by
    simpa [htargetStart, htargetFinish, finishOffset, hlength,
      Nat.add_assoc] using htarget
  have hvaluesEq := CompactFixedWidthTokenSlicesEq.natListValues_eq
    hslices hsourceAligned htargetAligned
  exact ⟨finishOffset, hsourceFinish, htargetFinish, hvaluesEq⟩

theorem CompactFixedWidthTokenSlicesEq.natListListValues_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceValues targetValues : List (List Nat)}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish)
    (hsource : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceValues)
    (htarget : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetValues) :
    targetValues = sourceValues := by
  rcases hsource with
    ⟨sourceBoundary, hsourceStructure, hsourceRows, _hsourceSize⟩
  rcases htarget with
    ⟨targetBoundary, htargetStructure, htargetRows, _htargetSize⟩
  rcases hsourceStructure with
    ⟨sourceBodyStart, _hsourceBodyBound,
      hsourceHeader, hsourceBoundary⟩
  rcases htargetStructure with
    ⟨targetBodyStart, _htargetBodyBound,
      htargetHeader, htargetBoundary⟩
  have hsourceBody : sourceBodyStart = sourceStart + 1 :=
    hsourceHeader.1.2.1
  have htargetBody : targetBodyStart = targetStart + 1 :=
    htargetHeader.1.2.1
  have hsourceStartFinish : sourceStart < sourceFinish := by
    have hbodyFinish :=
      FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.start_le_finish
        hsourceBoundary
    omega
  have hlengthSourceTarget :
      sourceValues.length = targetValues.length := by
    have hsourceCountEntry : CompactFixedWidthEntry tokenTable width
        (sourceStart + 0) sourceValues.length := by
      simpa using hsourceHeader.1.2.2
    have htargetCountEntry : CompactFixedWidthEntry tokenTable width
        (targetStart + 0) targetValues.length := by
      simpa using htargetHeader.1.2.2
    have hcountEq :=
      CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
        heq (by omega) hsourceCountEntry htargetCountEntry
    exact hcountEq
  have hitem
      (index : Nat) (hindex : index < sourceValues.length)
      (offset : Nat) (hoffset : offset < sourceFinish - sourceStart)
      (hsourceAt : CompactFixedWidthEntry sourceBoundary tokenCount index
        (sourceStart + offset))
      (htargetAt : CompactFixedWidthEntry targetBoundary tokenCount index
        (targetStart + offset)) :
      targetValues.getI index = sourceValues.getI index ∧
      ∃ nextOffset,
        nextOffset = offset + 1 + (sourceValues.getI index).length ∧
        CompactFixedWidthEntry sourceBoundary tokenCount (index + 1)
          (sourceStart + nextOffset) ∧
        CompactFixedWidthEntry targetBoundary tokenCount (index + 1)
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
      CompactAdditiveNatListDirectLayout.finish_eq hsourceValue
    have htargetInnerFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq htargetValue
    have hinnerLength :
        (sourceValues.getI index).length =
          (targetValues.getI index).length := by
      have hsourceInnerHeader :=
        CompactAdditiveNatListDirectLayout.headerEntry hsourceValue
      have htargetInnerHeader :=
        CompactAdditiveNatListDirectLayout.headerEntry htargetValue
      rw [hsourceLeft] at hsourceInnerHeader
      rw [htargetLeft] at htargetInnerHeader
      exact CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
        heq hoffset hsourceInnerHeader htargetInnerHeader
    let nextOffset :=
      offset + 1 + (sourceValues.getI index).length
    have hsourceRight : sourceRight = sourceStart + nextOffset := by
      dsimp only [nextOffset]
      omega
    have htargetRight : targetRight = targetStart + nextOffset := by
      dsimp only [nextOffset]
      omega
    have hsourceRightFinish : sourceRight ≤ sourceFinish :=
      FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_mono
        hsourceBoundary
        (by omega) (by rfl) hsourceRightEntry hsourceBoundary.2.2.2.1
    have hwithin :
        offset + (1 + (sourceValues.getI index).length) ≤
          sourceFinish - sourceStart := by
      omega
    have hinnerSlices := CompactFixedWidthTokenSlicesEq.subslice
      heq offset (1 + (sourceValues.getI index).length) hwithin
    have hsourceValueAligned : CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount
        (sourceStart + offset)
        (sourceStart + offset + (1 + (sourceValues.getI index).length))
        (sourceValues.getI index) := by
      simpa [hsourceLeft, hsourceRight, nextOffset, Nat.add_assoc] using
        hsourceValue
    have htargetValueAligned : CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount
        (targetStart + offset)
        (targetStart + offset + (1 + (sourceValues.getI index).length))
        (targetValues.getI index) := by
      simpa [htargetLeft, htargetRight, nextOffset, hinnerLength,
        Nat.add_assoc] using htargetValue
    have hinnerEq := CompactFixedWidthTokenSlicesEq.natListValues_eq
      hinnerSlices hsourceValueAligned htargetValueAligned
    refine ⟨hinnerEq, nextOffset, rfl, ?_, ?_⟩
    · simpa [hsourceRight] using hsourceRightEntry
    · simpa [htargetRight] using htargetRightEntry
  have haligned : ∀ index < sourceValues.length,
      ∃ offset,
        offset < sourceFinish - sourceStart ∧
        CompactFixedWidthEntry sourceBoundary tokenCount index
          (sourceStart + offset) ∧
        CompactFixedWidthEntry targetBoundary tokenCount index
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
        rcases ih hprevious with
          ⟨offset, hoffset, hsourceAt, htargetAt⟩
        rcases hitem index hprevious offset hoffset
            hsourceAt htargetAt with
          ⟨_hvalue, nextOffset, _hnextOffset,
            hsourceNext, htargetNext⟩
        have hnextInside :=
          FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_lt_finish
            hsourceBoundary hindex hsourceNext
        refine ⟨nextOffset, ?_, hsourceNext, htargetNext⟩
        omega
  apply List.ext_getElem
  · exact hlengthSourceTarget.symm
  · intro index htargetIndex hsourceIndex
    rcases haligned index hsourceIndex with
      ⟨offset, hoffset, hsourceAt, htargetAt⟩
    have hvalue := (hitem index hsourceIndex offset hoffset
      hsourceAt htargetAt).1
    simpa [List.getI_eq_getElem _ htargetIndex,
      List.getI_eq_getElem _ hsourceIndex] using hvalue

theorem CompactFixedWidthTokenSlicesEq.natListListPrefix_eq
    {tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit
      sourceStart sourceFinish targetStart targetFinish offset : Nat}
    {sourceValues targetValues : List (List Nat)}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit)
    (hsourceStart : sourceStart = sourceBase + offset)
    (htargetStart : targetStart = targetBase + offset)
    (hoffset : offset < sourceLimit - sourceBase)
    (hsourceFinishBound : sourceFinish ≤ sourceLimit)
    (htargetFinishBound : targetFinish ≤ targetLimit)
    (hsource : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceValues)
    (htarget : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetValues) :
    ∃ finishOffset,
      sourceFinish = sourceBase + finishOffset ∧
      targetFinish = targetBase + finishOffset ∧
      targetValues = sourceValues := by
  rcases hsource with
    ⟨sourceBoundary, hsourceStructure, hsourceRows, _hsourceSize⟩
  rcases htarget with
    ⟨targetBoundary, htargetStructure, htargetRows, _htargetSize⟩
  rcases hsourceStructure with
    ⟨sourceBodyStart, _hsourceBodyBound,
      hsourceHeader, hsourceBoundary⟩
  rcases htargetStructure with
    ⟨targetBodyStart, _htargetBodyBound,
      htargetHeader, htargetBoundary⟩
  have hsourceBody : sourceBodyStart = sourceBase + (offset + 1) := by
    have hbody : sourceBodyStart = sourceStart + 1 :=
      hsourceHeader.1.2.1
    omega
  have htargetBody : targetBodyStart = targetBase + (offset + 1) := by
    have hbody : targetBodyStart = targetStart + 1 :=
      htargetHeader.1.2.1
    omega
  have hlengthSourceTarget :
      sourceValues.length = targetValues.length := by
    have hsourceCountEntry : CompactFixedWidthEntry tokenTable width
        (sourceBase + offset) sourceValues.length := by
      simpa [hsourceStart] using hsourceHeader.1.2.2
    have htargetCountEntry : CompactFixedWidthEntry tokenTable width
        (targetBase + offset) targetValues.length := by
      simpa [htargetStart] using htargetHeader.1.2.2
    exact CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
      heq hoffset hsourceCountEntry htargetCountEntry
  have hitem
      (index : Nat) (hindex : index < sourceValues.length)
      (rowOffset : Nat)
      (hrowOffset : rowOffset < sourceLimit - sourceBase)
      (hsourceAt : CompactFixedWidthEntry sourceBoundary tokenCount index
        (sourceBase + rowOffset))
      (htargetAt : CompactFixedWidthEntry targetBoundary tokenCount index
        (targetBase + rowOffset)) :
      targetValues.getI index = sourceValues.getI index ∧
      ∃ nextOffset,
        nextOffset = rowOffset + 1 + (sourceValues.getI index).length ∧
        CompactFixedWidthEntry sourceBoundary tokenCount (index + 1)
          (sourceBase + nextOffset) ∧
        CompactFixedWidthEntry targetBoundary tokenCount (index + 1)
          (targetBase + nextOffset) := by
    have htargetIndex : index < targetValues.length := by omega
    rcases hsourceRows index hindex with
      ⟨sourceLeft, _hsourceLeft, sourceRight, _hsourceRight,
        hsourceLeftEntry, hsourceRightEntry, hsourceValue⟩
    rcases htargetRows index htargetIndex with
      ⟨targetLeft, _htargetLeft, targetRight, _htargetRight,
        htargetLeftEntry, htargetRightEntry, htargetValue⟩
    have hsourceLeft : sourceLeft = sourceBase + rowOffset :=
      (CompactFixedWidthEntry.value_eq_tableValue hsourceLeftEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hsourceAt).symm
    have htargetLeft : targetLeft = targetBase + rowOffset :=
      (CompactFixedWidthEntry.value_eq_tableValue htargetLeftEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue htargetAt).symm
    have hsourceInnerFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hsourceValue
    have htargetInnerFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq htargetValue
    have hinnerLength :
        (sourceValues.getI index).length =
          (targetValues.getI index).length := by
      have hsourceInnerHeader :=
        CompactAdditiveNatListDirectLayout.headerEntry hsourceValue
      have htargetInnerHeader :=
        CompactAdditiveNatListDirectLayout.headerEntry htargetValue
      rw [hsourceLeft] at hsourceInnerHeader
      rw [htargetLeft] at htargetInnerHeader
      exact CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
        heq hrowOffset hsourceInnerHeader htargetInnerHeader
    let nextOffset :=
      rowOffset + 1 + (sourceValues.getI index).length
    have hsourceRight : sourceRight = sourceBase + nextOffset := by
      dsimp only [nextOffset]
      omega
    have htargetRight : targetRight = targetBase + nextOffset := by
      dsimp only [nextOffset]
      omega
    have hsourceRightFinish : sourceRight ≤ sourceFinish :=
      FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_mono
        hsourceBoundary
        (by omega) (by rfl) hsourceRightEntry hsourceBoundary.2.2.2.1
    have hwithin :
        rowOffset + (1 + (sourceValues.getI index).length) ≤
          sourceLimit - sourceBase := by
      omega
    have hinnerSlices := CompactFixedWidthTokenSlicesEq.subslice
      heq rowOffset (1 + (sourceValues.getI index).length) hwithin
    have hsourceValueAligned : CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount
        (sourceBase + rowOffset)
        (sourceBase + rowOffset +
          (1 + (sourceValues.getI index).length))
        (sourceValues.getI index) := by
      simpa [hsourceLeft, hsourceRight, nextOffset, Nat.add_assoc] using
        hsourceValue
    have htargetValueAligned : CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount
        (targetBase + rowOffset)
        (targetBase + rowOffset +
          (1 + (sourceValues.getI index).length))
        (targetValues.getI index) := by
      simpa [htargetLeft, htargetRight, nextOffset, hinnerLength,
        Nat.add_assoc] using htargetValue
    have hinnerEq := CompactFixedWidthTokenSlicesEq.natListValues_eq
      hinnerSlices hsourceValueAligned htargetValueAligned
    refine ⟨hinnerEq, nextOffset, rfl, ?_, ?_⟩
    · simpa [hsourceRight] using hsourceRightEntry
    · simpa [htargetRight] using htargetRightEntry
  have haligned : ∀ index < sourceValues.length,
      ∃ rowOffset,
        rowOffset < sourceLimit - sourceBase ∧
        CompactFixedWidthEntry sourceBoundary tokenCount index
          (sourceBase + rowOffset) ∧
        CompactFixedWidthEntry targetBoundary tokenCount index
          (targetBase + rowOffset) := by
    intro index hindex
    induction index with
    | zero =>
        refine ⟨offset + 1, ?_, ?_, ?_⟩
        · have hbodyFinish :=
            FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_lt_finish
              hsourceBoundary hindex hsourceBoundary.2.2.1
          omega
        · simpa [hsourceBody] using hsourceBoundary.2.2.1
        · simpa [htargetBody] using htargetBoundary.2.2.1
    | succ index ih =>
        have hprevious : index < sourceValues.length := by omega
        rcases ih hprevious with
          ⟨rowOffset, hrowOffset, hsourceAt, htargetAt⟩
        rcases hitem index hprevious rowOffset hrowOffset
            hsourceAt htargetAt with
          ⟨_hvalue, nextOffset, _hnextOffset,
            hsourceNext, htargetNext⟩
        have hnextInside :=
          FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_lt_finish
            hsourceBoundary hindex hsourceNext
        refine ⟨nextOffset, ?_, hsourceNext, htargetNext⟩
        omega
  have hvaluesEq : targetValues = sourceValues := by
    apply List.ext_getElem
    · exact hlengthSourceTarget.symm
    · intro index htargetIndex hsourceIndex
      rcases haligned index hsourceIndex with
        ⟨rowOffset, hrowOffset, hsourceAt, htargetAt⟩
      have hvalue := (hitem index hsourceIndex rowOffset hrowOffset
        hsourceAt htargetAt).1
      simpa [List.getI_eq_getElem _ htargetIndex,
        List.getI_eq_getElem _ hsourceIndex] using hvalue
  by_cases hempty : sourceValues.length = 0
  · have htargetEmpty : targetValues.length = 0 := by omega
    have hsourceFinishEntry : CompactFixedWidthEntry sourceBoundary tokenCount
        0 sourceFinish := by
      simpa [hempty] using hsourceBoundary.2.2.2.1
    have htargetFinishEntry : CompactFixedWidthEntry targetBoundary tokenCount
        0 targetFinish := by
      simpa [htargetEmpty] using htargetBoundary.2.2.2.1
    have hsourceFinish : sourceFinish = sourceBodyStart :=
      (CompactFixedWidthEntry.value_eq_tableValue hsourceFinishEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hsourceBoundary.2.2.1).symm
    have htargetFinish : targetFinish = targetBodyStart :=
      (CompactFixedWidthEntry.value_eq_tableValue htargetFinishEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          htargetBoundary.2.2.1).symm
    refine ⟨offset + 1, ?_, ?_, hvaluesEq⟩ <;> omega
  · let lastIndex := sourceValues.length - 1
    have hlastIndex : lastIndex < sourceValues.length := by
      dsimp only [lastIndex]
      omega
    rcases haligned lastIndex hlastIndex with
      ⟨rowOffset, hrowOffset, hsourceAt, htargetAt⟩
    rcases hitem lastIndex hlastIndex rowOffset hrowOffset
        hsourceAt htargetAt with
      ⟨_hvalue, finishOffset, _hfinishOffset,
        hsourceFinal, htargetFinal⟩
    have hlastSucc : lastIndex + 1 = sourceValues.length := by
      dsimp only [lastIndex]
      omega
    have htargetLastSucc : lastIndex + 1 = targetValues.length := by
      omega
    have hsourceFinalAtCount : CompactFixedWidthEntry sourceBoundary tokenCount
        sourceValues.length (sourceBase + finishOffset) := by
      simpa [hlastSucc] using hsourceFinal
    have htargetFinalAtCount : CompactFixedWidthEntry targetBoundary tokenCount
        targetValues.length (targetBase + finishOffset) := by
      simpa [htargetLastSucc] using htargetFinal
    have hsourceFinish : sourceFinish = sourceBase + finishOffset :=
      (CompactFixedWidthEntry.value_eq_tableValue
        hsourceBoundary.2.2.2.1).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hsourceFinalAtCount).symm
    have htargetFinish : targetFinish = targetBase + finishOffset :=
      (CompactFixedWidthEntry.value_eq_tableValue
        htargetBoundary.2.2.2.1).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          htargetFinalAtCount).symm
    exact ⟨finishOffset, hsourceFinish, htargetFinish, hvaluesEq⟩

theorem CompactFixedWidthTokenSlicesEq.childResultValue_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceValue targetValue : CompactNumericChildResult}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish)
    (hsource : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceValue)
    (htarget : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetValue) :
    targetValue = sourceValue := by
  rcases hsource with
    ⟨sourceGammaFinish, sourceGammaBoundary, sourceBoolValue,
      hsourceProduct, hsourceGammaLayout, hsourceGammaRows,
      hsourceBoolValue, hsourceBool, hsourceGammaSize⟩
  rcases htarget with
    ⟨targetGammaFinish, targetGammaBoundary, targetBoolValue,
      htargetProduct, htargetGammaLayout, htargetGammaRows,
      htargetBoolValue, htargetBool, htargetGammaSize⟩
  rcases hsourceProduct with
    ⟨hsourceStartGamma, hsourceGammaFinishLt, hsourceFinishBound⟩
  rcases htargetProduct with
    ⟨htargetStartGamma, htargetGammaFinishLt, htargetFinishBound⟩
  have hsourceFinish : sourceFinish = sourceGammaFinish + 1 :=
    hsourceBool.1.2.1
  have htargetFinish : targetFinish = targetGammaFinish + 1 :=
    htargetBool.1.2.1
  have hsliceLength :
      sourceFinish - sourceStart = targetFinish - targetStart := by
    rcases heq with
      ⟨count, _hcount, hsourceCount, htargetCount,
        _hsourceBound, _htargetBound, _hbits⟩
    omega
  let gammaCount := sourceGammaFinish - sourceStart
  have hsourceGammaFinish :
      sourceGammaFinish = sourceStart + gammaCount := by
    dsimp only [gammaCount]
    omega
  have htargetGammaFinish :
      targetGammaFinish = targetStart + gammaCount := by
    dsimp only [gammaCount]
    omega
  have hgammaWithin :
      0 + gammaCount ≤ sourceFinish - sourceStart := by
    dsimp only [gammaCount]
    omega
  have hgammaSlices := CompactFixedWidthTokenSlicesEq.subslice
    heq 0 gammaCount hgammaWithin
  have hgammaSlicesAligned : CompactFixedWidthTokenSlicesEq
      tokenTable width tokenCount
      sourceStart sourceGammaFinish targetStart targetGammaFinish := by
    simpa [hsourceGammaFinish, htargetGammaFinish] using hgammaSlices
  have hsourceGamma : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount sourceStart sourceGammaFinish
        sourceValue.1 :=
    ⟨sourceGammaBoundary, hsourceGammaLayout,
      hsourceGammaRows, hsourceGammaSize⟩
  have htargetGamma : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount targetStart targetGammaFinish
        targetValue.1 :=
    ⟨targetGammaBoundary, htargetGammaLayout,
      htargetGammaRows, htargetGammaSize⟩
  have hgammaEq : targetValue.1 = sourceValue.1 :=
    CompactFixedWidthTokenSlicesEq.natListListValues_eq
      hgammaSlicesAligned hsourceGamma htargetGamma
  have hboolOffset : gammaCount < sourceFinish - sourceStart := by
    dsimp only [gammaCount]
    omega
  have hsourceBoolEntry : CompactFixedWidthEntry tokenTable width
      (sourceStart + gammaCount) sourceBoolValue := by
    simpa [hsourceGammaFinish] using hsourceBool.1.2.2
  have htargetBoolEntry : CompactFixedWidthEntry tokenTable width
      (targetStart + gammaCount) targetBoolValue := by
    simpa [htargetGammaFinish] using htargetBool.1.2.2
  have hboolValueEq : sourceBoolValue = targetBoolValue :=
    CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
      heq hboolOffset hsourceBoolEntry htargetBoolEntry
  have htagEq : compactAdditiveBoolTag sourceValue.2 =
      compactAdditiveBoolTag targetValue.2 :=
    hsourceBoolValue.symm.trans (hboolValueEq.trans htargetBoolValue)
  have hboolEq : sourceValue.2 = targetValue.2 := by
    cases hsourceResult : sourceValue.2 <;>
      cases htargetResult : targetValue.2 <;>
      simp [hsourceResult, htargetResult, compactAdditiveBoolTag] at htagEq ⊢
  exact Prod.ext hgammaEq hboolEq.symm

theorem CompactFixedWidthTokenSlicesEq.childResultPrefix_eq
    {tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit
      sourceStart sourceFinish targetStart targetFinish offset : Nat}
    {sourceValue targetValue : CompactNumericChildResult}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit)
    (hsourceStart : sourceStart = sourceBase + offset)
    (htargetStart : targetStart = targetBase + offset)
    (hoffset : offset < sourceLimit - sourceBase)
    (hsourceFinishBound : sourceFinish ≤ sourceLimit)
    (htargetFinishBound : targetFinish ≤ targetLimit)
    (hsource : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceValue)
    (htarget : CompactNumericChildResultDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetValue) :
    ∃ finishOffset,
      sourceFinish = sourceBase + finishOffset ∧
      targetFinish = targetBase + finishOffset ∧
      targetValue = sourceValue := by
  rcases hsource with
    ⟨sourceGammaFinish, sourceGammaBoundary, sourceBoolValue,
      hsourceProduct, hsourceGammaLayout, hsourceGammaRows,
      hsourceBoolValue, hsourceBool, hsourceGammaSize⟩
  rcases htarget with
    ⟨targetGammaFinish, targetGammaBoundary, targetBoolValue,
      htargetProduct, htargetGammaLayout, htargetGammaRows,
      htargetBoolValue, htargetBool, htargetGammaSize⟩
  rcases hsourceProduct with
    ⟨hsourceStartGamma, hsourceGammaFinishLt, _hsourceFinishBound⟩
  rcases htargetProduct with
    ⟨htargetStartGamma, htargetGammaFinishLt, _htargetFinishBound⟩
  have hsourceGamma : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount sourceStart sourceGammaFinish
        sourceValue.1 :=
    ⟨sourceGammaBoundary, hsourceGammaLayout,
      hsourceGammaRows, hsourceGammaSize⟩
  have htargetGamma : CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount targetStart targetGammaFinish
        targetValue.1 :=
    ⟨targetGammaBoundary, htargetGammaLayout,
      htargetGammaRows, htargetGammaSize⟩
  have hsourceGammaBound : sourceGammaFinish ≤ sourceLimit := by omega
  have htargetGammaBound : targetGammaFinish ≤ targetLimit := by omega
  rcases CompactFixedWidthTokenSlicesEq.natListListPrefix_eq
      heq hsourceStart htargetStart hoffset
      hsourceGammaBound htargetGammaBound hsourceGamma htargetGamma with
    ⟨gammaOffset, hsourceGammaAt, htargetGammaAt, hgammaEq⟩
  have hboolOffset : gammaOffset < sourceLimit - sourceBase := by
    omega
  have hsourceBoolEntry : CompactFixedWidthEntry tokenTable width
      (sourceBase + gammaOffset) sourceBoolValue := by
    simpa [hsourceGammaAt] using hsourceBool.1.2.2
  have htargetBoolEntry : CompactFixedWidthEntry tokenTable width
      (targetBase + gammaOffset) targetBoolValue := by
    simpa [htargetGammaAt] using htargetBool.1.2.2
  have hboolValueEq : sourceBoolValue = targetBoolValue :=
    CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
      heq hboolOffset hsourceBoolEntry htargetBoolEntry
  have htagEq : compactAdditiveBoolTag sourceValue.2 =
      compactAdditiveBoolTag targetValue.2 :=
    hsourceBoolValue.symm.trans (hboolValueEq.trans htargetBoolValue)
  have hboolEq : sourceValue.2 = targetValue.2 := by
    cases hsourceResult : sourceValue.2 <;>
      cases htargetResult : targetValue.2 <;>
      simp [hsourceResult, htargetResult, compactAdditiveBoolTag] at htagEq ⊢
  have hvalueEq : targetValue = sourceValue :=
    Prod.ext hgammaEq hboolEq.symm
  refine ⟨gammaOffset + 1, ?_, ?_, hvalueEq⟩
  · have hfinish : sourceFinish = sourceGammaFinish + 1 :=
      hsourceBool.1.2.1
    omega
  · have hfinish : targetFinish = targetGammaFinish + 1 :=
      htargetBool.1.2.1
    omega

theorem CompactFixedWidthTokenSlicesEq.nodeFieldsPrefix_eq
    {tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit
      sourceStart sourceFinish targetStart targetFinish offset : Nat}
    {sourceFields targetFields : CompactNumericNodeFields}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit)
    (hsourceStart : sourceStart = sourceBase + offset)
    (htargetStart : targetStart = targetBase + offset)
    (hoffset : offset < sourceLimit - sourceBase)
    (hsourceFinishBound : sourceFinish ≤ sourceLimit)
    (htargetFinishBound : targetFinish ≤ targetLimit)
    (hsource : CompactNumericNodeFieldsDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceFields)
    (htarget : CompactNumericNodeFieldsDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetFields) :
    ∃ finishOffset,
      sourceFinish = sourceBase + finishOffset ∧
      targetFinish = targetBase + finishOffset ∧
      targetFields = sourceFields := by
  rcases hsource with
    ⟨sourceGammaFinish, sourceFirstFinish, sourceSecondFinish,
      sourceWitnessFinish, hsourceGamma, hsourceFirst,
      hsourceSecond, hsourceWitness, hsourceSuffix⟩
  rcases htarget with
    ⟨targetGammaFinish, targetFirstFinish, targetSecondFinish,
      targetWitnessFinish, htargetGamma, htargetFirst,
      htargetSecond, htargetWitness, htargetSuffix⟩
  have hsourceFirstFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hsourceFirst
  have hsourceSecondFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hsourceSecond
  have hsourceWitnessFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hsourceWitness
  have hsourceSuffixFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hsourceSuffix
  have htargetFirstFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq htargetFirst
  have htargetSecondFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq htargetSecond
  have htargetWitnessFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq htargetWitness
  have htargetSuffixFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq htargetSuffix
  rcases CompactFixedWidthTokenSlicesEq.natListListPrefix_eq
      heq hsourceStart htargetStart hoffset
      (by omega) (by omega) hsourceGamma htargetGamma with
    ⟨gammaOffset, hsourceGammaAt, htargetGammaAt, hgammaEq⟩
  rcases CompactFixedWidthTokenSlicesEq.natListPrefix_eq
      (offset := gammaOffset) heq hsourceGammaAt htargetGammaAt
      (by omega) (by omega) (by omega) hsourceFirst htargetFirst with
    ⟨firstOffset, hsourceFirstAt, htargetFirstAt, hfirstEq⟩
  rcases CompactFixedWidthTokenSlicesEq.natListPrefix_eq
      (offset := firstOffset) heq hsourceFirstAt htargetFirstAt
      (by omega) (by omega) (by omega) hsourceSecond htargetSecond with
    ⟨secondOffset, hsourceSecondAt, htargetSecondAt, hsecondEq⟩
  rcases CompactFixedWidthTokenSlicesEq.natListPrefix_eq
      (offset := secondOffset) heq hsourceSecondAt htargetSecondAt
      (by omega) (by omega) (by omega) hsourceWitness htargetWitness with
    ⟨witnessOffset, hsourceWitnessAt, htargetWitnessAt, hwitnessEq⟩
  rcases CompactFixedWidthTokenSlicesEq.natListPrefix_eq
      (offset := witnessOffset) heq hsourceWitnessAt htargetWitnessAt
      (by omega) hsourceFinishBound htargetFinishBound
      hsourceSuffix htargetSuffix with
    ⟨finishOffset, hsourceFinishAt, htargetFinishAt, hsuffixEq⟩
  have hfieldsEq : targetFields = sourceFields :=
    Prod.ext hgammaEq
      (Prod.ext hfirstEq
        (Prod.ext hsecondEq (Prod.ext hwitnessEq hsuffixEq)))
  exact ⟨finishOffset, hsourceFinishAt, htargetFinishAt, hfieldsEq⟩

theorem CompactFixedWidthTokenSlicesEq.verifierTaskPrefix_eq
    {tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit
      sourceStart sourceFinish targetStart targetFinish offset : Nat}
    {sourceTask targetTask : CompactNumericVerifierTask}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit)
    (hsourceStart : sourceStart = sourceBase + offset)
    (htargetStart : targetStart = targetBase + offset)
    (hoffset : offset < sourceLimit - sourceBase)
    (hsourceFinishBound : sourceFinish ≤ sourceLimit)
    (htargetFinishBound : targetFinish ≤ targetLimit)
    (hsource : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceTask)
    (htarget : CompactNumericVerifierTaskDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetTask) :
    ∃ finishOffset,
      sourceFinish = sourceBase + finishOffset ∧
      targetFinish = targetBase + finishOffset ∧
      targetTask = sourceTask := by
  rcases hsource with
    ⟨sourceFieldsStart, hsourceTag, hsourceFields⟩
  rcases htarget with
    ⟨targetFieldsStart, htargetTag, htargetFields⟩
  have hsourceTagEntry : CompactFixedWidthEntry tokenTable width
      (sourceBase + offset) sourceTask.1 := by
    simpa [hsourceStart] using hsourceTag.2.2
  have htargetTagEntry : CompactFixedWidthEntry tokenTable width
      (targetBase + offset) targetTask.1 := by
    simpa [htargetStart] using htargetTag.2.2
  have htagEq : sourceTask.1 = targetTask.1 :=
    CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
      heq hoffset hsourceTagEntry htargetTagEntry
  have hsourceFieldsAt : sourceFieldsStart =
      sourceBase + (offset + 1) := by
    have hnext : sourceFieldsStart = sourceStart + 1 := hsourceTag.2.1
    omega
  have htargetFieldsAt : targetFieldsStart =
      targetBase + (offset + 1) := by
    have hnext : targetFieldsStart = targetStart + 1 := htargetTag.2.1
    omega
  have hsourceFieldsStartFinish : sourceFieldsStart < sourceFinish := by
    rcases hsourceFields with
      ⟨gammaFinish, firstFinish, secondFinish, witnessFinish,
        hgamma, hfirst, hsecond, hwitness, hsuffix⟩
    rcases hgamma with
      ⟨_gammaBoundary, hgammaLayout, _hgammaRows, _hgammaSize⟩
    have hgammaStartFinish :=
      CompactAdditiveStructuredListLayout.start_lt_finish hgammaLayout
    have hfirstFinish := CompactAdditiveNatListDirectLayout.finish_eq hfirst
    have hsecondFinish := CompactAdditiveNatListDirectLayout.finish_eq hsecond
    have hwitnessFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hwitness
    have hsuffixFinish := CompactAdditiveNatListDirectLayout.finish_eq hsuffix
    omega
  have hfieldsOffset : offset + 1 < sourceLimit - sourceBase := by
    omega
  rcases CompactFixedWidthTokenSlicesEq.nodeFieldsPrefix_eq
      heq hsourceFieldsAt htargetFieldsAt hfieldsOffset
      hsourceFinishBound htargetFinishBound hsourceFields htargetFields with
    ⟨finishOffset, hsourceFinishAt, htargetFinishAt, hfieldsEq⟩
  have htaskEq : targetTask = sourceTask :=
    Prod.ext htagEq.symm hfieldsEq
  exact ⟨finishOffset, hsourceFinishAt, htargetFinishAt, htaskEq⟩

theorem CompactFixedWidthTokenSlicesEq.structuredListPrefix_eq
    {alpha : Type*} [Inhabited alpha]
    (ElementLayout : Nat → Nat → Nat → Nat → Nat → alpha → Prop)
    {tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit
      sourceStart sourceFinish targetStart targetFinish offset
      sourceBoundary targetBoundary : Nat}
    {sourceValues targetValues : List alpha}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit)
    (hsourceStart : sourceStart = sourceBase + offset)
    (htargetStart : targetStart = targetBase + offset)
    (hoffset : offset < sourceLimit - sourceBase)
    (hsourceFinishBound : sourceFinish ≤ sourceLimit)
    (htargetFinishBound : targetFinish ≤ targetLimit)
    (hsourceLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount sourceStart sourceValues.length
        sourceFinish sourceBoundary)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      ElementLayout tokenTable width tokenCount sourceBoundary sourceValues)
    (htargetLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount targetStart targetValues.length
        targetFinish targetBoundary)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      ElementLayout tokenTable width tokenCount targetBoundary targetValues)
    (helement :
      ∀ {sourceElementStart sourceElementFinish
          targetElementStart targetElementFinish rowOffset : Nat}
        {sourceValue targetValue : alpha},
        sourceElementStart = sourceBase + rowOffset →
        targetElementStart = targetBase + rowOffset →
        rowOffset < sourceLimit - sourceBase →
        sourceElementFinish ≤ sourceLimit →
        targetElementFinish ≤ targetLimit →
        ElementLayout tokenTable width tokenCount
          sourceElementStart sourceElementFinish sourceValue →
        ElementLayout tokenTable width tokenCount
          targetElementStart targetElementFinish targetValue →
        ∃ finishOffset,
          sourceElementFinish = sourceBase + finishOffset ∧
          targetElementFinish = targetBase + finishOffset ∧
          targetValue = sourceValue) :
    ∃ finishOffset,
      sourceFinish = sourceBase + finishOffset ∧
      targetFinish = targetBase + finishOffset ∧
      targetValues = sourceValues := by
  rcases hsourceLayout with
    ⟨sourceBodyStart, _hsourceBodyBound,
      hsourceHeader, hsourceBoundary⟩
  rcases htargetLayout with
    ⟨targetBodyStart, _htargetBodyBound,
      htargetHeader, htargetBoundary⟩
  have hsourceBody : sourceBodyStart = sourceBase + (offset + 1) := by
    have hbody : sourceBodyStart = sourceStart + 1 :=
      hsourceHeader.1.2.1
    omega
  have htargetBody : targetBodyStart = targetBase + (offset + 1) := by
    have hbody : targetBodyStart = targetStart + 1 :=
      htargetHeader.1.2.1
    omega
  have hlengthSourceTarget :
      sourceValues.length = targetValues.length := by
    have hsourceCountEntry : CompactFixedWidthEntry tokenTable width
        (sourceBase + offset) sourceValues.length := by
      simpa [hsourceStart] using hsourceHeader.1.2.2
    have htargetCountEntry : CompactFixedWidthEntry tokenTable width
        (targetBase + offset) targetValues.length := by
      simpa [htargetStart] using htargetHeader.1.2.2
    exact CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
      heq hoffset hsourceCountEntry htargetCountEntry
  have hitem
      (index : Nat) (hindex : index < sourceValues.length)
      (rowOffset : Nat)
      (hrowOffset : rowOffset < sourceLimit - sourceBase)
      (hsourceAt : CompactFixedWidthEntry sourceBoundary tokenCount index
        (sourceBase + rowOffset))
      (htargetAt : CompactFixedWidthEntry targetBoundary tokenCount index
        (targetBase + rowOffset)) :
      targetValues.getI index = sourceValues.getI index ∧
      ∃ nextOffset,
        CompactFixedWidthEntry sourceBoundary tokenCount (index + 1)
          (sourceBase + nextOffset) ∧
        CompactFixedWidthEntry targetBoundary tokenCount (index + 1)
          (targetBase + nextOffset) := by
    have htargetIndex : index < targetValues.length := by omega
    rcases hsourceRows index hindex with
      ⟨sourceLeft, _hsourceLeft, sourceRight, _hsourceRight,
        hsourceLeftEntry, hsourceRightEntry, hsourceValue⟩
    rcases htargetRows index htargetIndex with
      ⟨targetLeft, _htargetLeft, targetRight, _htargetRight,
        htargetLeftEntry, htargetRightEntry, htargetValue⟩
    have hsourceLeft : sourceLeft = sourceBase + rowOffset :=
      (CompactFixedWidthEntry.value_eq_tableValue hsourceLeftEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue hsourceAt).symm
    have htargetLeft : targetLeft = targetBase + rowOffset :=
      (CompactFixedWidthEntry.value_eq_tableValue htargetLeftEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue htargetAt).symm
    have hsourceRightFinish : sourceRight ≤ sourceFinish :=
      FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_mono
        hsourceBoundary
        (by omega) (by rfl) hsourceRightEntry hsourceBoundary.2.2.2.1
    have htargetRightFinish : targetRight ≤ targetFinish :=
      FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_mono
        htargetBoundary
        (by omega) (by rfl) htargetRightEntry htargetBoundary.2.2.2.1
    rcases helement hsourceLeft htargetLeft hrowOffset
        (hsourceRightFinish.trans hsourceFinishBound)
        (htargetRightFinish.trans htargetFinishBound)
        hsourceValue htargetValue with
      ⟨nextOffset, hsourceRight, htargetRight, hvalueEq⟩
    refine ⟨hvalueEq, nextOffset, ?_, ?_⟩
    · simpa [hsourceRight] using hsourceRightEntry
    · simpa [htargetRight] using htargetRightEntry
  have haligned : ∀ index < sourceValues.length,
      ∃ rowOffset,
        rowOffset < sourceLimit - sourceBase ∧
        CompactFixedWidthEntry sourceBoundary tokenCount index
          (sourceBase + rowOffset) ∧
        CompactFixedWidthEntry targetBoundary tokenCount index
          (targetBase + rowOffset) := by
    intro index hindex
    induction index with
    | zero =>
        refine ⟨offset + 1, ?_, ?_, ?_⟩
        · have hbodyFinish :=
            FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_lt_finish
              hsourceBoundary hindex hsourceBoundary.2.2.1
          omega
        · simpa [hsourceBody] using hsourceBoundary.2.2.1
        · simpa [htargetBody] using htargetBoundary.2.2.1
    | succ index ih =>
        have hprevious : index < sourceValues.length := by omega
        rcases ih hprevious with
          ⟨rowOffset, hrowOffset, hsourceAt, htargetAt⟩
        rcases hitem index hprevious rowOffset hrowOffset
            hsourceAt htargetAt with
          ⟨_hvalue, nextOffset, hsourceNext, htargetNext⟩
        have hnextInside :=
          FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_lt_finish
            hsourceBoundary hindex hsourceNext
        refine ⟨nextOffset, ?_, hsourceNext, htargetNext⟩
        omega
  have hvaluesEq : targetValues = sourceValues := by
    apply List.ext_getElem
    · exact hlengthSourceTarget.symm
    · intro index htargetIndex hsourceIndex
      rcases haligned index hsourceIndex with
        ⟨rowOffset, hrowOffset, hsourceAt, htargetAt⟩
      have hvalue := (hitem index hsourceIndex rowOffset hrowOffset
        hsourceAt htargetAt).1
      simpa [List.getI_eq_getElem _ htargetIndex,
        List.getI_eq_getElem _ hsourceIndex] using hvalue
  by_cases hempty : sourceValues.length = 0
  · have htargetEmpty : targetValues.length = 0 := by omega
    have hsourceFinishEntry : CompactFixedWidthEntry sourceBoundary tokenCount
        0 sourceFinish := by
      simpa [hempty] using hsourceBoundary.2.2.2.1
    have htargetFinishEntry : CompactFixedWidthEntry targetBoundary tokenCount
        0 targetFinish := by
      simpa [htargetEmpty] using htargetBoundary.2.2.2.1
    have hsourceFinish : sourceFinish = sourceBodyStart :=
      (CompactFixedWidthEntry.value_eq_tableValue hsourceFinishEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hsourceBoundary.2.2.1).symm
    have htargetFinish : targetFinish = targetBodyStart :=
      (CompactFixedWidthEntry.value_eq_tableValue htargetFinishEntry).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          htargetBoundary.2.2.1).symm
    refine ⟨offset + 1, ?_, ?_, hvaluesEq⟩ <;> omega
  · let lastIndex := sourceValues.length - 1
    have hlastIndex : lastIndex < sourceValues.length := by
      dsimp only [lastIndex]
      omega
    rcases haligned lastIndex hlastIndex with
      ⟨rowOffset, hrowOffset, hsourceAt, htargetAt⟩
    rcases hitem lastIndex hlastIndex rowOffset hrowOffset
        hsourceAt htargetAt with
      ⟨_hvalue, finishOffset, hsourceFinal, htargetFinal⟩
    have hlastSucc : lastIndex + 1 = sourceValues.length := by
      dsimp only [lastIndex]
      omega
    have htargetLastSucc : lastIndex + 1 = targetValues.length := by
      omega
    have hsourceFinalAtCount : CompactFixedWidthEntry sourceBoundary tokenCount
        sourceValues.length (sourceBase + finishOffset) := by
      simpa [hlastSucc] using hsourceFinal
    have htargetFinalAtCount : CompactFixedWidthEntry targetBoundary tokenCount
        targetValues.length (targetBase + finishOffset) := by
      simpa [htargetLastSucc] using htargetFinal
    have hsourceFinish : sourceFinish = sourceBase + finishOffset :=
      (CompactFixedWidthEntry.value_eq_tableValue
        hsourceBoundary.2.2.2.1).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          hsourceFinalAtCount).symm
    have htargetFinish : targetFinish = targetBase + finishOffset :=
      (CompactFixedWidthEntry.value_eq_tableValue
        htargetBoundary.2.2.2.1).trans
        (CompactFixedWidthEntry.value_eq_tableValue
          htargetFinalAtCount).symm
    exact ⟨finishOffset, hsourceFinish, htargetFinish, hvaluesEq⟩

theorem CompactFixedWidthTokenSlicesEq.verifierTaskListPrefix_eq
    {tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit
      sourceStart sourceFinish targetStart targetFinish offset
      sourceBoundary targetBoundary : Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit)
    (hsourceStart : sourceStart = sourceBase + offset)
    (htargetStart : targetStart = targetBase + offset)
    (hoffset : offset < sourceLimit - sourceBase)
    (hsourceFinishBound : sourceFinish ≤ sourceLimit)
    (htargetFinishBound : targetFinish ≤ targetLimit)
    (hsourceLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount sourceStart sourceTasks.length
        sourceFinish sourceBoundary)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        sourceBoundary sourceTasks)
    (htargetLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount targetStart targetTasks.length
        targetFinish targetBoundary)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
        targetBoundary targetTasks) :
    ∃ finishOffset,
      sourceFinish = sourceBase + finishOffset ∧
      targetFinish = targetBase + finishOffset ∧
      targetTasks = sourceTasks := by
  apply CompactFixedWidthTokenSlicesEq.structuredListPrefix_eq
    CompactNumericVerifierTaskDirectLayout heq hsourceStart htargetStart
      hoffset hsourceFinishBound htargetFinishBound
      hsourceLayout hsourceRows htargetLayout htargetRows
  intro sourceElementStart sourceElementFinish
    targetElementStart targetElementFinish rowOffset
    sourceTask targetTask hsourceElementStart htargetElementStart
    hrowOffset hsourceElementFinishBound htargetElementFinishBound
    hsourceTask htargetTask
  exact CompactFixedWidthTokenSlicesEq.verifierTaskPrefix_eq
    heq hsourceElementStart htargetElementStart hrowOffset
      hsourceElementFinishBound htargetElementFinishBound
      hsourceTask htargetTask

theorem CompactFixedWidthTokenSlicesEq.childResultListPrefix_eq
    {tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit
      sourceStart sourceFinish targetStart targetFinish offset
      sourceBoundary targetBoundary : Nat}
    {sourceValues targetValues : List CompactNumericChildResult}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit)
    (hsourceStart : sourceStart = sourceBase + offset)
    (htargetStart : targetStart = targetBase + offset)
    (hoffset : offset < sourceLimit - sourceBase)
    (hsourceFinishBound : sourceFinish ≤ sourceLimit)
    (htargetFinishBound : targetFinish ≤ targetLimit)
    (hsourceLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount sourceStart sourceValues.length
        sourceFinish sourceBoundary)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary sourceValues)
    (htargetLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount targetStart targetValues.length
        targetFinish targetBoundary)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary targetValues) :
    ∃ finishOffset,
      sourceFinish = sourceBase + finishOffset ∧
      targetFinish = targetBase + finishOffset ∧
      targetValues = sourceValues := by
  apply CompactFixedWidthTokenSlicesEq.structuredListPrefix_eq
    CompactNumericChildResultDirectLayout heq hsourceStart htargetStart
      hoffset hsourceFinishBound htargetFinishBound
      hsourceLayout hsourceRows htargetLayout htargetRows
  intro sourceElementStart sourceElementFinish
    targetElementStart targetElementFinish rowOffset
    sourceValue targetValue hsourceElementStart htargetElementStart
    hrowOffset hsourceElementFinishBound htargetElementFinishBound
    hsourceValue htargetValue
  exact CompactFixedWidthTokenSlicesEq.childResultPrefix_eq
    heq hsourceElementStart htargetElementStart hrowOffset
      hsourceElementFinishBound htargetElementFinishBound
      hsourceValue htargetValue

theorem CompactAdditiveOptionBoolDirectLayout.start_lt_finish
    {tokenTable width tokenCount start finish : Nat}
    {status : Option Bool}
    (hlayout : CompactAdditiveOptionBoolDirectLayout
      tokenTable width tokenCount start finish status) :
    start < finish := by
  rcases hlayout with
    ⟨_tag, payloadStart, hoption, hstatus⟩
  have hpayloadStart : payloadStart = start + 1 := hoption.1.2.1
  rcases hstatus with hnone | hsome
  · omega
  · rcases hsome with ⟨_result, _hstatus, _htag, hbool⟩
    have hboolFinish : finish = payloadStart + 1 := hbool.1.2.1
    omega

theorem CompactFixedWidthTokenSlicesEq.optionBoolPrefix_eq
    {tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit
      sourceStart sourceFinish targetStart targetFinish offset : Nat}
    {sourceStatus targetStatus : Option Bool}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceBase sourceLimit targetBase targetLimit)
    (hsourceStart : sourceStart = sourceBase + offset)
    (htargetStart : targetStart = targetBase + offset)
    (hoffset : offset < sourceLimit - sourceBase)
    (hsourceFinishBound : sourceFinish ≤ sourceLimit)
    (htargetFinishBound : targetFinish ≤ targetLimit)
    (hsource : CompactAdditiveOptionBoolDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceStatus)
    (htarget : CompactAdditiveOptionBoolDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetStatus) :
    ∃ finishOffset,
      sourceFinish = sourceBase + finishOffset ∧
      targetFinish = targetBase + finishOffset ∧
      targetStatus = sourceStatus := by
  rcases hsource with
    ⟨sourceTag, sourcePayloadStart, hsourceOption, hsourceCase⟩
  rcases htarget with
    ⟨targetTag, targetPayloadStart, htargetOption, htargetCase⟩
  have hsourceTagEntry : CompactFixedWidthEntry tokenTable width
      (sourceBase + offset) sourceTag := by
    simpa [hsourceStart] using hsourceOption.1.2.2
  have htargetTagEntry : CompactFixedWidthEntry tokenTable width
      (targetBase + offset) targetTag := by
    simpa [htargetStart] using htargetOption.1.2.2
  have htagEq : sourceTag = targetTag :=
    CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
      heq hoffset hsourceTagEntry htargetTagEntry
  have hsourcePayloadAt : sourcePayloadStart =
      sourceBase + (offset + 1) := by
    have hnext : sourcePayloadStart = sourceStart + 1 :=
      hsourceOption.1.2.1
    omega
  have htargetPayloadAt : targetPayloadStart =
      targetBase + (offset + 1) := by
    have hnext : targetPayloadStart = targetStart + 1 :=
      htargetOption.1.2.1
    omega
  rcases hsourceCase with hsourceNone | hsourceSome
  · rcases hsourceNone with
      ⟨hsourceStatus, hsourceTagZero, hsourceFinish⟩
    rcases htargetCase with htargetNone | htargetSome
    · rcases htargetNone with
        ⟨htargetStatus, _htargetTagZero, htargetFinish⟩
      refine ⟨offset + 1, ?_, ?_, ?_⟩
      · omega
      · omega
      · rw [htargetStatus, hsourceStatus]
    · rcases htargetSome with
        ⟨_targetResult, _htargetStatus, htargetTagOne, _htargetBool⟩
      omega
  · rcases hsourceSome with
      ⟨sourceResult, hsourceStatus, hsourceTagOne, hsourceBool⟩
    rcases htargetCase with htargetNone | htargetSome
    · rcases htargetNone with
        ⟨_htargetStatus, htargetTagZero, _htargetFinish⟩
      omega
    · rcases htargetSome with
        ⟨targetResult, htargetStatus, _htargetTagOne, htargetBool⟩
      have hboolOffset : offset + 1 < sourceLimit - sourceBase := by
        have hsourceBoolFinish : sourceFinish = sourcePayloadStart + 1 :=
          hsourceBool.1.2.1
        omega
      have hsourceBoolEntry : CompactFixedWidthEntry tokenTable width
          (sourceBase + (offset + 1))
          (compactAdditiveBoolTag sourceResult) := by
        simpa [hsourcePayloadAt] using hsourceBool.1.2.2
      have htargetBoolEntry : CompactFixedWidthEntry tokenTable width
          (targetBase + (offset + 1))
          (compactAdditiveBoolTag targetResult) := by
        simpa [htargetPayloadAt] using htargetBool.1.2.2
      have hresultTagEq : compactAdditiveBoolTag sourceResult =
          compactAdditiveBoolTag targetResult :=
        CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
          heq hboolOffset hsourceBoolEntry htargetBoolEntry
      have hresultEq : targetResult = sourceResult :=
        (compactAdditiveBoolTag_injective hresultTagEq).symm
      have hsourceFinish : sourceFinish =
          sourceBase + (offset + 2) := by
        have hfinish : sourceFinish = sourcePayloadStart + 1 :=
          hsourceBool.1.2.1
        omega
      have htargetFinish : targetFinish =
          targetBase + (offset + 2) := by
        have hfinish : targetFinish = targetPayloadStart + 1 :=
          htargetBool.1.2.1
        omega
      refine ⟨offset + 2, hsourceFinish, htargetFinish, ?_⟩
      rw [htargetStatus, hsourceStatus, hresultEq]

theorem CompactFixedWidthTokenSlicesEq.verifierStateValue_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    {sourceState targetState : CompactNumericVerifierState}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish)
    (hsource : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish sourceState)
    (htarget : CompactNumericVerifierStateDirectLayout
      tokenTable width tokenCount targetStart targetFinish targetState) :
    targetState = sourceState := by
  rcases hsource with
    ⟨sourceProofFinish, sourceCertificateFinish, sourceTasksFinish,
      sourceValuesFinish, sourceTaskBoundary, sourceValueBoundary,
      hsourceProof, hsourceCertificate,
      hsourceTasks, hsourceTaskRows, _hsourceTaskSize,
      hsourceValues, hsourceValueRows, _hsourceValueSize,
      hsourceStatus⟩
  rcases htarget with
    ⟨targetProofFinish, targetCertificateFinish, targetTasksFinish,
      targetValuesFinish, targetTaskBoundary, targetValueBoundary,
      htargetProof, htargetCertificate,
      htargetTasks, htargetTaskRows, _htargetTaskSize,
      htargetValues, htargetValueRows, _htargetValueSize,
      htargetStatus⟩
  have hsourceProofFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hsourceProof
  have htargetProofFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq htargetProof
  have hsourceCertificateFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hsourceCertificate
  have htargetCertificateFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq htargetCertificate
  have hsourceTasksStartFinish :=
    CompactAdditiveStructuredListLayout.start_lt_finish hsourceTasks
  have htargetTasksStartFinish :=
    CompactAdditiveStructuredListLayout.start_lt_finish htargetTasks
  have hsourceValuesStartFinish :=
    CompactAdditiveStructuredListLayout.start_lt_finish hsourceValues
  have htargetValuesStartFinish :=
    CompactAdditiveStructuredListLayout.start_lt_finish htargetValues
  have hsourceStatusStartFinish :=
    CompactAdditiveOptionBoolDirectLayout.start_lt_finish hsourceStatus
  have htargetStatusStartFinish :=
    CompactAdditiveOptionBoolDirectLayout.start_lt_finish htargetStatus
  rcases CompactFixedWidthTokenSlicesEq.natListPrefix_eq
      (offset := 0) heq rfl rfl (by omega) (by omega) (by omega)
      hsourceProof htargetProof with
    ⟨proofOffset, hsourceProofAt, htargetProofAt, hproofEq⟩
  rcases CompactFixedWidthTokenSlicesEq.natListPrefix_eq
      (offset := proofOffset) heq hsourceProofAt htargetProofAt
      (by omega) (by omega) (by omega)
      hsourceCertificate htargetCertificate with
    ⟨certificateOffset, hsourceCertificateAt,
      htargetCertificateAt, hcertificateEq⟩
  rcases CompactFixedWidthTokenSlicesEq.verifierTaskListPrefix_eq
      (offset := certificateOffset) heq
      hsourceCertificateAt htargetCertificateAt
      (by omega) (by omega) (by omega)
      hsourceTasks hsourceTaskRows htargetTasks htargetTaskRows with
    ⟨tasksOffset, hsourceTasksAt, htargetTasksAt, htasksEq⟩
  rcases CompactFixedWidthTokenSlicesEq.childResultListPrefix_eq
      (offset := tasksOffset) heq hsourceTasksAt htargetTasksAt
      (by omega) (by omega) (by omega)
      hsourceValues hsourceValueRows htargetValues htargetValueRows with
    ⟨valuesOffset, hsourceValuesAt, htargetValuesAt, hvaluesEq⟩
  rcases CompactFixedWidthTokenSlicesEq.optionBoolPrefix_eq
      (offset := valuesOffset) heq hsourceValuesAt htargetValuesAt
      (by omega) (by omega) (by omega) hsourceStatus htargetStatus with
    ⟨_finishOffset, _hsourceFinishAt, _htargetFinishAt, hstatusEq⟩
  exact Prod.ext
    (Prod.ext (Prod.ext hproofEq hcertificateEq)
      (Prod.ext htasksEq hvaluesEq)) hstatusEq

theorem CompactFixedWidthTokenSlicesEq.childResultListValues_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish
      sourceBoundary targetBoundary : Nat}
    {sourceValues targetValues : List CompactNumericChildResult}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish)
    (hsourceLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount sourceStart sourceValues.length
        sourceFinish sourceBoundary)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary sourceValues)
    (htargetLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount targetStart targetValues.length
        targetFinish targetBoundary)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary targetValues) :
    targetValues = sourceValues := by
  rcases hsourceLayout with
    ⟨sourceBodyStart, _hsourceBodyBound,
      hsourceHeader, hsourceBoundary⟩
  rcases htargetLayout with
    ⟨targetBodyStart, _htargetBodyBound,
      htargetHeader, htargetBoundary⟩
  have hsourceBody : sourceBodyStart = sourceStart + 1 :=
    hsourceHeader.1.2.1
  have htargetBody : targetBodyStart = targetStart + 1 :=
    htargetHeader.1.2.1
  have hsourceStartFinish : sourceStart < sourceFinish := by
    have hbodyFinish :=
      FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.start_le_finish
        hsourceBoundary
    omega
  have hlengthSourceTarget :
      sourceValues.length = targetValues.length := by
    have hsourceCountEntry : CompactFixedWidthEntry tokenTable width
        (sourceStart + 0) sourceValues.length := by
      simpa using hsourceHeader.1.2.2
    have htargetCountEntry : CompactFixedWidthEntry tokenTable width
        (targetStart + 0) targetValues.length := by
      simpa using htargetHeader.1.2.2
    exact CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
      heq (by omega) hsourceCountEntry htargetCountEntry
  have hitem
      (index : Nat) (hindex : index < sourceValues.length)
      (offset : Nat) (hoffset : offset < sourceFinish - sourceStart)
      (hsourceAt : CompactFixedWidthEntry sourceBoundary tokenCount index
        (sourceStart + offset))
      (htargetAt : CompactFixedWidthEntry targetBoundary tokenCount index
        (targetStart + offset)) :
      targetValues.getI index = sourceValues.getI index ∧
      ∃ nextOffset,
        CompactFixedWidthEntry sourceBoundary tokenCount (index + 1)
          (sourceStart + nextOffset) ∧
        CompactFixedWidthEntry targetBoundary tokenCount (index + 1)
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
    have hsourceRightFinish : sourceRight ≤ sourceFinish :=
      FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_mono
        hsourceBoundary
        (by omega) (by rfl) hsourceRightEntry hsourceBoundary.2.2.2.1
    have htargetRightFinish : targetRight ≤ targetFinish :=
      FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_mono
        htargetBoundary
        (by omega) (by rfl) htargetRightEntry htargetBoundary.2.2.2.1
    rcases CompactFixedWidthTokenSlicesEq.childResultPrefix_eq
        heq hsourceLeft htargetLeft hoffset
        hsourceRightFinish htargetRightFinish hsourceValue htargetValue with
      ⟨nextOffset, hsourceRight, htargetRight, hvalueEq⟩
    refine ⟨hvalueEq, nextOffset, ?_, ?_⟩
    · simpa [hsourceRight] using hsourceRightEntry
    · simpa [htargetRight] using htargetRightEntry
  have haligned : ∀ index < sourceValues.length,
      ∃ offset,
        offset < sourceFinish - sourceStart ∧
        CompactFixedWidthEntry sourceBoundary tokenCount index
          (sourceStart + offset) ∧
        CompactFixedWidthEntry targetBoundary tokenCount index
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
        rcases ih hprevious with
          ⟨offset, hoffset, hsourceAt, htargetAt⟩
        rcases hitem index hprevious offset hoffset
            hsourceAt htargetAt with
          ⟨_hvalue, nextOffset, hsourceNext, htargetNext⟩
        have hnextInside :=
          FoundationCompactNumericListedDirectVerifierValueRealization.CompactAdditiveBoundaryTable.entry_lt_finish
            hsourceBoundary hindex hsourceNext
        refine ⟨nextOffset, ?_, hsourceNext, htargetNext⟩
        omega
  apply List.ext_getElem
  · exact hlengthSourceTarget.symm
  · intro index htargetIndex hsourceIndex
    rcases haligned index hsourceIndex with
      ⟨offset, hoffset, hsourceAt, htargetAt⟩
    have hvalue := (hitem index hsourceIndex offset hoffset
      hsourceAt htargetAt).1
    simpa [List.getI_eq_getElem _ htargetIndex,
      List.getI_eq_getElem _ hsourceIndex] using hvalue

#print axioms compactAdditiveBoolTag_injective
#print axioms CompactAdditiveStructuredListLayout.start_lt_finish
#print axioms CompactAdditiveStructuredListLayout.finish_eq_start_add_one_of_count_zero
#print axioms CompactAdditiveNatListDirectLayout.valueEntry
#print axioms CompactAdditiveNatListDirectLayout.finish_eq
#print axioms CompactAdditiveNatListDirectLayout.headerEntry
#print axioms CompactFixedWidthTokenSlicesEq.natListValues_eq
#print axioms CompactFixedWidthTokenSlicesEq.natListPrefix_eq
#print axioms CompactFixedWidthTokenSlicesEq.natListListValues_eq
#print axioms CompactFixedWidthTokenSlicesEq.natListListPrefix_eq
#print axioms CompactFixedWidthTokenSlicesEq.childResultValue_eq
#print axioms CompactFixedWidthTokenSlicesEq.childResultPrefix_eq
#print axioms CompactFixedWidthTokenSlicesEq.nodeFieldsPrefix_eq
#print axioms CompactFixedWidthTokenSlicesEq.verifierTaskPrefix_eq
#print axioms CompactFixedWidthTokenSlicesEq.structuredListPrefix_eq
#print axioms CompactFixedWidthTokenSlicesEq.verifierTaskListPrefix_eq
#print axioms CompactFixedWidthTokenSlicesEq.childResultListPrefix_eq
#print axioms CompactAdditiveOptionBoolDirectLayout.start_lt_finish
#print axioms CompactFixedWidthTokenSlicesEq.optionBoolPrefix_eq
#print axioms CompactFixedWidthTokenSlicesEq.verifierStateValue_eq
#print axioms CompactFixedWidthTokenSlicesEq.childResultListValues_eq

end FoundationCompactNumericListedDirectVerifierPayloadEquality
