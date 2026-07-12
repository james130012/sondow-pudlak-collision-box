import integration.FoundationCompactNumericListedDirectAtomicRowEquality

/-!
# Direct equality of two natural-number list row tables

Equal counts and pairwise equal one-token rows are equivalent to equality of
the represented natural-number lists under their exact atomic row layouts.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListSameRows

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicRowEquality

def CompactAdditiveNatListSameRows
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount : Nat) : Prop :=
  targetCount = sourceCount ∧
    ∀ index < sourceCount,
      ∃ sourceLeft, sourceLeft ≤ tokenCount ∧
      ∃ sourceRight, sourceRight ≤ tokenCount ∧
      ∃ targetLeft, targetLeft ≤ tokenCount ∧
      ∃ targetRight, targetRight ≤ tokenCount ∧
        CompactFixedWidthEntry sourceBoundary tokenCount index sourceLeft ∧
        CompactFixedWidthEntry sourceBoundary tokenCount
          (index + 1) sourceRight ∧
        CompactFixedWidthEntry targetBoundary tokenCount index targetLeft ∧
        CompactFixedWidthEntry targetBoundary tokenCount
          (index + 1) targetRight ∧
        CompactAdditiveAtomicRowEq tokenTable width tokenCount
          sourceLeft sourceRight targetLeft targetRight

def compactAdditiveNatListSameRowsDef : 𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount.
    targetCount = sourceCount ∧
    ∀ index < sourceCount,
      ∃ sourceLeft <⁺ tokenCount,
        ∃ sourceRight <⁺ tokenCount,
          ∃ targetLeft <⁺ tokenCount,
            ∃ targetRight <⁺ tokenCount,
              !(compactFixedWidthEntryDef)
                sourceBoundary tokenCount index sourceLeft ∧
              !(compactFixedWidthEntryDef)
                sourceBoundary tokenCount (index + 1) sourceRight ∧
              !(compactFixedWidthEntryDef)
                targetBoundary tokenCount index targetLeft ∧
              !(compactFixedWidthEntryDef)
                targetBoundary tokenCount (index + 1) targetRight ∧
              sourceLeft < tokenCount ∧
              sourceRight = sourceLeft + 1 ∧
              targetLeft < tokenCount ∧
              targetRight = targetLeft + 1 ∧
              ∀ bitIndex < width,
                ((sourceLeft * width + bitIndex) ∈ tokenTable ↔
                  (targetLeft * width + bitIndex) ∈ tokenTable)”

@[simp] theorem compactAdditiveNatListSameRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount : Nat) :
    compactAdditiveNatListSameRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount] ↔
      CompactAdditiveNatListSameRows
        tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount := by
  have hsizeSelf : ∀ value : Nat, Nat.size value ≤ value := by
    intro value
    exact natSize_le_of_le (Nat.le_refl value)
  simp [compactAdditiveNatListSameRowsDef,
    CompactAdditiveNatListSameRows, CompactAdditiveAtomicRowEq,
    compactFixedWidthEntryDef, CompactFixedWidthEntry,
    arithmeticMem_nat_iff_testBit, foundationNatLE_iff_standard,
    hsizeSelf]

theorem compactAdditiveNatListSameRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListSameRowsDef.val := by
  simp [compactAdditiveNatListSameRowsDef]

theorem CompactAdditiveStructuredListElementRowLayouts.natSameRows
    {tokenTable width tokenCount sourceBoundary targetBoundary : Nat}
    {source target : List Nat}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      targetBoundary target)
    (hsame : target = source) :
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount sourceBoundary source.length
        targetBoundary target.length := by
  subst target
  refine ⟨rfl, ?_⟩
  intro index hindex
  rcases hsource index hindex with
    ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
      hsourceLeftEntry, hsourceRightEntry, hsourceLayout⟩
  rcases htarget index hindex with
    ⟨targetLeft, htargetLeft, targetRight, htargetRight,
      htargetLeftEntry, htargetRightEntry, htargetLayout⟩
  have hrowEq : CompactAdditiveAtomicRowEq
      tokenTable width tokenCount
        sourceLeft sourceRight targetLeft targetRight :=
    CompactAdditiveTokenCell.atomicRowEq
      hsourceLayout htargetLayout
  exact ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
    targetLeft, htargetLeft, targetRight, htargetRight,
    hsourceLeftEntry, hsourceRightEntry,
    htargetLeftEntry, htargetRightEntry, hrowEq⟩

theorem CompactAdditiveNatListSameRows.eq_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary : Nat}
    {source target : List Nat}
    (hsameRows : CompactAdditiveNatListSameRows
      tokenTable width tokenCount sourceBoundary source.length
        targetBoundary target.length)
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      targetBoundary target) :
    target = source := by
  have hcount := hsameRows.1
  have hrowPairs := hsameRows.2
  apply List.ext_getElem
  · omega
  · intro index htargetIndex hsourceIndex
    rcases hrowPairs index hsourceIndex with
      ⟨sourceLeft, _hsourceLeft, sourceRight, _hsourceRight,
        targetLeft, _htargetLeft, targetRight, _htargetRight,
        hsourceLeftEntry, hsourceRightEntry,
        htargetLeftEntry, htargetRightEntry, hrowEq⟩
    rcases hsource index hsourceIndex with
      ⟨rowSourceLeft, _hrowSourceLeft, rowSourceRight,
        _hrowSourceRight, hrowSourceLeftEntry,
        hrowSourceRightEntry, hsourceLayout⟩
    rcases htarget index htargetIndex with
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
    exact hvalue.symm

theorem compactAdditiveNatListSameRows_iff_eq_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary : Nat}
    {source target : List Nat}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      targetBoundary target) :
    CompactAdditiveNatListSameRows
        tokenTable width tokenCount sourceBoundary source.length
          targetBoundary target.length ↔
      target = source := by
  constructor
  · intro hsameRows
    exact hsameRows.eq_of_rows hsource htarget
  · intro hsame
    exact CompactAdditiveStructuredListElementRowLayouts.natSameRows
      hsource htarget hsame

#print axioms compactAdditiveNatListSameRowsDef_spec
#print axioms compactAdditiveNatListSameRowsDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.natSameRows
#print axioms CompactAdditiveNatListSameRows.eq_of_rows
#print axioms compactAdditiveNatListSameRows_iff_eq_of_rows

end FoundationCompactNumericListedDirectNatListSameRows
