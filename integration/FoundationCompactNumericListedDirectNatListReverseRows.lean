import integration.FoundationCompactNumericListedDirectNatListConsRows

/-!
# Direct row graph for natural-number list reversal

For every target index the formula supplies the unique source index whose sum
with the target index and one is the common list length.  The corresponding
one-token rows are then compared by the direct atomic-row relation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListReverseRows

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicRowEquality

def CompactAdditiveNatListReverseRows
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount : Nat) : Prop :=
  targetCount = sourceCount ∧
    ∀ targetIndex < targetCount,
      ∃ sourceIndex, sourceIndex < sourceCount ∧
        sourceIndex + targetIndex + 1 = sourceCount ∧
      ∃ sourceLeft, sourceLeft ≤ tokenCount ∧
      ∃ sourceRight, sourceRight ≤ tokenCount ∧
      ∃ targetLeft, targetLeft ≤ tokenCount ∧
      ∃ targetRight, targetRight ≤ tokenCount ∧
        CompactFixedWidthEntry sourceBoundary tokenCount
          sourceIndex sourceLeft ∧
        CompactFixedWidthEntry sourceBoundary tokenCount
          (sourceIndex + 1) sourceRight ∧
        CompactFixedWidthEntry targetBoundary tokenCount
          targetIndex targetLeft ∧
        CompactFixedWidthEntry targetBoundary tokenCount
          (targetIndex + 1) targetRight ∧
        CompactAdditiveAtomicRowEq tokenTable width tokenCount
          sourceLeft sourceRight targetLeft targetRight

def compactAdditiveNatListReverseRowsDef : 𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount.
    targetCount = sourceCount ∧
    ∀ targetIndex < targetCount,
      ∃ sourceIndex < sourceCount,
        sourceIndex + targetIndex + 1 = sourceCount ∧
        ∃ sourceLeft <⁺ tokenCount,
          ∃ sourceRight <⁺ tokenCount,
            ∃ targetLeft <⁺ tokenCount,
              ∃ targetRight <⁺ tokenCount,
                !(compactFixedWidthEntryDef)
                  sourceBoundary tokenCount sourceIndex sourceLeft ∧
                !(compactFixedWidthEntryDef)
                  sourceBoundary tokenCount
                    (sourceIndex + 1) sourceRight ∧
                !(compactFixedWidthEntryDef)
                  targetBoundary tokenCount targetIndex targetLeft ∧
                !(compactFixedWidthEntryDef)
                  targetBoundary tokenCount
                    (targetIndex + 1) targetRight ∧
                sourceLeft < tokenCount ∧
                sourceRight = sourceLeft + 1 ∧
                targetLeft < tokenCount ∧
                targetRight = targetLeft + 1 ∧
                ∀ bitIndex < width,
                  ((sourceLeft * width + bitIndex) ∈ tokenTable ↔
                    (targetLeft * width + bitIndex) ∈ tokenTable)”

@[simp] theorem compactAdditiveNatListReverseRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount : Nat) :
    compactAdditiveNatListReverseRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount] ↔
      CompactAdditiveNatListReverseRows
        tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount := by
  have hsizeSelf : ∀ value : Nat, Nat.size value ≤ value := by
    intro value
    exact natSize_le_of_le (Nat.le_refl value)
  simp [compactAdditiveNatListReverseRowsDef,
    CompactAdditiveNatListReverseRows, CompactAdditiveAtomicRowEq,
    compactFixedWidthEntryDef, CompactFixedWidthEntry,
    arithmeticMem_nat_iff_testBit, foundationNatLE_iff_standard,
    hsizeSelf]

theorem compactAdditiveNatListReverseRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListReverseRowsDef.val := by
  simp [compactAdditiveNatListReverseRowsDef]

theorem CompactAdditiveStructuredListElementRowLayouts.natReverseRows
    {tokenTable width tokenCount sourceBoundary targetBoundary : Nat}
    {source target : List Nat}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      targetBoundary target)
    (hreverse : target = source.reverse) :
    CompactAdditiveNatListReverseRows
      tokenTable width tokenCount sourceBoundary source.length
        targetBoundary target.length := by
  have hcount : target.length = source.length := by simp [hreverse]
  refine ⟨hcount, ?_⟩
  intro targetIndex htargetIndex
  let sourceIndex := source.length - 1 - targetIndex
  have hsourceIndex : sourceIndex < source.length := by
    dsimp only [sourceIndex]
    omega
  have hindexSum : sourceIndex + targetIndex + 1 = source.length := by
    dsimp only [sourceIndex]
    omega
  rcases hsource sourceIndex hsourceIndex with
    ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
      hsourceLeftEntry, hsourceRightEntry, hsourceLayout⟩
  rcases htarget targetIndex htargetIndex with
    ⟨targetLeft, htargetLeft, targetRight, htargetRight,
      htargetLeftEntry, htargetRightEntry, htargetLayout⟩
  have hvalue : source.getI sourceIndex = target.getI targetIndex := by
    have hreverseIndex : targetIndex < source.reverse.length := by
      simpa [hreverse] using htargetIndex
    rw [hreverse]
    rw [List.getI_eq_getElem _ hsourceIndex]
    rw [List.getI_eq_getElem _ hreverseIndex]
    rw [List.getElem_reverse]
  have hrowEq : CompactAdditiveAtomicRowEq
      tokenTable width tokenCount
        sourceLeft sourceRight targetLeft targetRight := by
    rw [hvalue] at hsourceLayout
    exact CompactAdditiveTokenCell.atomicRowEq
      hsourceLayout htargetLayout
  exact ⟨sourceIndex, hsourceIndex, hindexSum,
    sourceLeft, hsourceLeft, sourceRight, hsourceRight,
    targetLeft, htargetLeft, targetRight, htargetRight,
    hsourceLeftEntry, hsourceRightEntry,
    htargetLeftEntry, htargetRightEntry, hrowEq⟩

theorem CompactAdditiveNatListReverseRows.eq_reverse_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary : Nat}
    {source target : List Nat}
    (hreverseRows : CompactAdditiveNatListReverseRows
      tokenTable width tokenCount sourceBoundary source.length
        targetBoundary target.length)
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      targetBoundary target) :
    target = source.reverse := by
  have hcount := hreverseRows.1
  have hrowPairs := hreverseRows.2
  apply List.ext_getElem
  · simp
    omega
  · intro targetIndex htargetIndex hreverseIndex
    rcases hrowPairs targetIndex htargetIndex with
      ⟨sourceIndex, hsourceIndex, hindexSum,
        sourceLeft, _hsourceLeft, sourceRight, _hsourceRight,
        targetLeft, _htargetLeft, targetRight, _htargetRight,
        hsourceLeftEntry, hsourceRightEntry,
        htargetLeftEntry, htargetRightEntry, hrowEq⟩
    have hsourceIndexEq :
        sourceIndex = source.length - 1 - targetIndex := by omega
    rcases hsource sourceIndex hsourceIndex with
      ⟨rowSourceLeft, _hrowSourceLeft, rowSourceRight,
        _hrowSourceRight, hrowSourceLeftEntry,
        hrowSourceRightEntry, hsourceLayout⟩
    rcases htarget targetIndex htargetIndex with
      ⟨rowTargetLeft, _hrowTargetLeft, rowTargetRight,
        _hrowTargetRight, hrowTargetLeftEntry,
        hrowTargetRightEntry, htargetLayout⟩
    have hsourceLeft : sourceLeft = rowSourceLeft :=
      (CompactFixedWidthEntry.value_eq_tableValue
        hsourceLeftEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowSourceLeftEntry).symm
    have hsourceRight : sourceRight = rowSourceRight :=
      (CompactFixedWidthEntry.value_eq_tableValue
        hsourceRightEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowSourceRightEntry).symm
    have htargetLeft : targetLeft = rowTargetLeft :=
      (CompactFixedWidthEntry.value_eq_tableValue
        htargetLeftEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowTargetLeftEntry).symm
    have htargetRight : targetRight = rowTargetRight :=
      (CompactFixedWidthEntry.value_eq_tableValue
        htargetRightEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowTargetRightEntry).symm
    subst sourceLeft
    subst sourceRight
    subst targetLeft
    subst targetRight
    have hvalue := hrowEq.natValue_eq hsourceLayout htargetLayout
    rw [List.getI_eq_getElem _ hsourceIndex] at hvalue
    rw [List.getI_eq_getElem _ htargetIndex] at hvalue
    rw [List.getElem_reverse]
    simpa only [← hsourceIndexEq] using hvalue.symm

theorem compactAdditiveNatListReverseRows_iff_reverse_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary : Nat}
    {source target : List Nat}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      targetBoundary target) :
    CompactAdditiveNatListReverseRows
        tokenTable width tokenCount sourceBoundary source.length
          targetBoundary target.length ↔
      target = source.reverse := by
  constructor
  · intro hreverseRows
    exact hreverseRows.eq_reverse_of_rows hsource htarget
  · intro hreverse
    exact CompactAdditiveStructuredListElementRowLayouts.natReverseRows
      hsource htarget hreverse

#print axioms compactAdditiveNatListReverseRowsDef_spec
#print axioms compactAdditiveNatListReverseRowsDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.natReverseRows
#print axioms CompactAdditiveNatListReverseRows.eq_reverse_of_rows
#print axioms compactAdditiveNatListReverseRows_iff_reverse_of_rows

end FoundationCompactNumericListedDirectNatListReverseRows
