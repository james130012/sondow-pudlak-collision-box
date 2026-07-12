import integration.FoundationCompactNumericListedDirectAtomicRowEquality

/-!
# Direct row graph for natural-number list cons

The target row zero carries the new head token.  Every later target row is
bitwise identical to the preceding source row.  The resulting bounded graph
is proved equivalent to `target = head :: source` under the real row layouts.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListConsRows

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicRowEquality

def CompactAdditiveNatListConsRows
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head : Nat) :
    Prop :=
  targetCount = sourceCount + 1 ∧
    (∃ targetLeft, targetLeft ≤ tokenCount ∧
      ∃ targetRight, targetRight ≤ tokenCount ∧
        CompactFixedWidthEntry targetBoundary tokenCount 0 targetLeft ∧
        CompactFixedWidthEntry targetBoundary tokenCount 1 targetRight ∧
        CompactAdditiveTokenCell
          tokenTable width tokenCount targetLeft head targetRight) ∧
    ∀ index < sourceCount,
      ∃ sourceLeft, sourceLeft ≤ tokenCount ∧
      ∃ sourceRight, sourceRight ≤ tokenCount ∧
      ∃ targetLeft, targetLeft ≤ tokenCount ∧
      ∃ targetRight, targetRight ≤ tokenCount ∧
        CompactFixedWidthEntry sourceBoundary tokenCount index sourceLeft ∧
        CompactFixedWidthEntry sourceBoundary tokenCount
          (index + 1) sourceRight ∧
        CompactFixedWidthEntry targetBoundary tokenCount
          (index + 1) targetLeft ∧
        CompactFixedWidthEntry targetBoundary tokenCount
          (index + 2) targetRight ∧
        CompactAdditiveAtomicRowEq tokenTable width tokenCount
          sourceLeft sourceRight targetLeft targetRight

def compactAdditiveNatListConsRowsDef : 𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head.
    targetCount = sourceCount + 1 ∧
    (∃ targetLeft <⁺ tokenCount,
      ∃ targetRight <⁺ tokenCount,
        !(compactFixedWidthEntryDef)
          targetBoundary tokenCount 0 targetLeft ∧
        !(compactFixedWidthEntryDef)
          targetBoundary tokenCount 1 targetRight ∧
        targetLeft < tokenCount ∧
        targetRight = targetLeft + 1 ∧
        !(compactFixedWidthEntryDef)
          tokenTable width targetLeft head) ∧
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
                targetBoundary tokenCount (index + 1) targetLeft ∧
              !(compactFixedWidthEntryDef)
                targetBoundary tokenCount (index + 2) targetRight ∧
              sourceLeft < tokenCount ∧
              sourceRight = sourceLeft + 1 ∧
              targetLeft < tokenCount ∧
              targetRight = targetLeft + 1 ∧
              ∀ bitIndex < width,
                ((sourceLeft * width + bitIndex) ∈ tokenTable ↔
                  (targetLeft * width + bitIndex) ∈ tokenTable)”

@[simp] theorem compactAdditiveNatListConsRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount head : Nat) :
    compactAdditiveNatListConsRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount, head] ↔
      CompactAdditiveNatListConsRows
        tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount head := by
  have hsizeSelf : ∀ value : Nat, Nat.size value ≤ value := by
    intro value
    exact natSize_le_of_le (Nat.le_refl value)
  simp [compactAdditiveNatListConsRowsDef,
    CompactAdditiveNatListConsRows, CompactAdditiveAtomicRowEq,
    CompactAdditiveTokenCell, compactFixedWidthEntryDef,
    CompactFixedWidthEntry, arithmeticMem_nat_iff_testBit,
    foundationNatLE_iff_standard, hsizeSelf]
  aesop

theorem compactAdditiveNatListConsRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListConsRowsDef.val := by
  simp [compactAdditiveNatListConsRowsDef]

theorem CompactAdditiveStructuredListElementRowLayouts.natConsRows
    {tokenTable width tokenCount sourceBoundary targetBoundary head : Nat}
    {source target : List Nat}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      targetBoundary target)
    (hcons : target = head :: source) :
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount sourceBoundary source.length
        targetBoundary target.length head := by
  have hcount : target.length = source.length + 1 := by simp [hcons]
  have htargetZero : 0 < target.length := by omega
  rcases htarget 0 htargetZero with
    ⟨headLeft, hheadLeft, headRight, hheadRight,
      hheadLeftEntry, hheadRightEntry, hheadLayout⟩
  have hheadLayout' : CompactAdditiveTokenCell
      tokenTable width tokenCount headLeft head headRight := by
    simpa [CompactAdditiveNatValueDirectLayout, hcons] using hheadLayout
  refine ⟨hcount, ⟨headLeft, hheadLeft, headRight, hheadRight,
    hheadLeftEntry, hheadRightEntry, hheadLayout'⟩, ?_⟩
  intro index hindex
  have htargetIndex : index + 1 < target.length := by omega
  rcases hsource index hindex with
    ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
      hsourceLeftEntry, hsourceRightEntry, hsourceLayout⟩
  rcases htarget (index + 1) htargetIndex with
    ⟨targetLeft, htargetLeft, targetRight, htargetRight,
      htargetLeftEntry, htargetRightEntry, htargetLayout⟩
  have hvalue : source.getI index = target.getI (index + 1) := by
    rw [hcons]
    simp
  have hrowEq : CompactAdditiveAtomicRowEq
      tokenTable width tokenCount
        sourceLeft sourceRight targetLeft targetRight := by
    rw [hvalue] at hsourceLayout
    exact CompactAdditiveTokenCell.atomicRowEq
      hsourceLayout htargetLayout
  exact ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
    targetLeft, htargetLeft, targetRight, htargetRight,
    hsourceLeftEntry, hsourceRightEntry,
    htargetLeftEntry, htargetRightEntry, hrowEq⟩

theorem CompactAdditiveNatListConsRows.eq_cons_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary head : Nat}
    {source target : List Nat}
    (hconsRows : CompactAdditiveNatListConsRows
      tokenTable width tokenCount sourceBoundary source.length
        targetBoundary target.length head)
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      targetBoundary target) :
    target = head :: source := by
  have hcount := hconsRows.1
  have hhead := hconsRows.2.1
  have htailRows := hconsRows.2.2
  apply List.ext_getElem
  · simp
    omega
  · intro index htargetIndex hconsIndex
    cases index with
    | zero =>
        rcases hhead with
          ⟨headLeft, _hheadLeft, headRight, _hheadRight,
            hheadLeftEntry, _hheadRightEntry, hheadCell⟩
        rcases htarget 0 htargetIndex with
          ⟨rowLeft, _hrowLeft, rowRight, _hrowRight,
            hrowLeftEntry, _hrowRightEntry, htargetLayout⟩
        have hleft : headLeft = rowLeft :=
          (CompactFixedWidthEntry.value_eq_tableValue
            hheadLeftEntry).trans
              (CompactFixedWidthEntry.value_eq_tableValue
                hrowLeftEntry).symm
        subst headLeft
        have hvalue : head = target.getI 0 :=
          (CompactAdditiveTokenCell.value_eq_tableValue hheadCell).trans
            (CompactAdditiveTokenCell.value_eq_tableValue
              htargetLayout).symm
        rw [List.getI_eq_getElem _ htargetIndex] at hvalue
        simpa using hvalue.symm
    | succ index =>
        have hsourceIndex : index < source.length := by omega
        rcases htailRows index hsourceIndex with
          ⟨sourceLeft, _hsourceLeft, sourceRight, _hsourceRight,
            targetLeft, _htargetLeft, targetRight, _htargetRight,
            hsourceLeftEntry, hsourceRightEntry,
            htargetLeftEntry, htargetRightEntry, hrowEq⟩
        rcases hsource index hsourceIndex with
          ⟨rowSourceLeft, _hrowSourceLeft, rowSourceRight,
            _hrowSourceRight, hrowSourceLeftEntry,
            hrowSourceRightEntry, hsourceLayout⟩
        rcases htarget (index + 1) htargetIndex with
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
        simpa using hvalue.symm

theorem compactAdditiveNatListConsRows_iff_cons_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary head : Nat}
    {source target : List Nat}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
      targetBoundary target) :
    CompactAdditiveNatListConsRows
        tokenTable width tokenCount sourceBoundary source.length
          targetBoundary target.length head ↔
      target = head :: source := by
  constructor
  · intro hconsRows
    exact hconsRows.eq_cons_of_rows hsource htarget
  · intro hcons
    exact CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hsource htarget hcons

#print axioms compactAdditiveNatListConsRowsDef_spec
#print axioms compactAdditiveNatListConsRowsDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.natConsRows
#print axioms CompactAdditiveNatListConsRows.eq_cons_of_rows
#print axioms compactAdditiveNatListConsRows_iff_cons_of_rows

end FoundationCompactNumericListedDirectNatListConsRows
