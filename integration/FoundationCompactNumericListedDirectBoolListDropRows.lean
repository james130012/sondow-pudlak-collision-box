import integration.FoundationCompactNumericListedDirectAtomicRowEquality
import integration.FoundationCompactNumericListedDirectFlexibleBinaryNatDecode

/-!
# Direct row graph for dropping a Boolean-list prefix

The target list starts at a certified source offset and every target Boolean
row is bitwise identical to the corresponding shifted source row.  The final
theorem identifies this bounded graph exactly with `target = source.drop n`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBoolListDropRows

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactVerifierBitCostPrimitives
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectBoolListPackedValue
open FoundationCompactNumericListedDirectFlexibleBinaryNatDecode

def CompactAdditiveBoolListDropRows
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount consumed : Nat) :
    Prop :=
  consumed ≤ sourceCount ∧
    sourceCount = consumed + targetCount ∧
    ∀ index < targetCount,
      ∃ sourceLeft, sourceLeft ≤ tokenCount ∧
      ∃ sourceRight, sourceRight ≤ tokenCount ∧
      ∃ targetLeft, targetLeft ≤ tokenCount ∧
      ∃ targetRight, targetRight ≤ tokenCount ∧
        CompactFixedWidthEntry sourceBoundary tokenCount
          (consumed + index) sourceLeft ∧
        CompactFixedWidthEntry sourceBoundary tokenCount
          (consumed + index + 1) sourceRight ∧
        CompactFixedWidthEntry targetBoundary tokenCount index targetLeft ∧
        CompactFixedWidthEntry targetBoundary tokenCount
          (index + 1) targetRight ∧
        CompactAdditiveAtomicRowEq tokenTable width tokenCount
          sourceLeft sourceRight targetLeft targetRight

def compactAdditiveBoolListDropRowsDef : 𝚺₀.Semisentence 8 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount consumed.
    consumed ≤ sourceCount ∧
    sourceCount = consumed + targetCount ∧
    ∀ index < targetCount,
      ∃ sourceLeft <⁺ tokenCount,
        ∃ sourceRight <⁺ tokenCount,
          ∃ targetLeft <⁺ tokenCount,
            ∃ targetRight <⁺ tokenCount,
              !(compactFixedWidthEntryDef)
                sourceBoundary tokenCount
                  (consumed + index) sourceLeft ∧
              !(compactFixedWidthEntryDef)
                sourceBoundary tokenCount
                  (consumed + index + 1) sourceRight ∧
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

@[simp] theorem compactAdditiveBoolListDropRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount consumed : Nat) :
    compactAdditiveBoolListDropRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          consumed] ↔
      CompactAdditiveBoolListDropRows
        tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount consumed := by
  have hsizeSelf : ∀ value : Nat, Nat.size value ≤ value := by
    intro value
    exact natSize_le_of_le (Nat.le_refl value)
  simp [compactAdditiveBoolListDropRowsDef,
    CompactAdditiveBoolListDropRows, CompactAdditiveAtomicRowEq,
    compactFixedWidthEntryDef, CompactFixedWidthEntry,
    arithmeticMem_nat_iff_testBit, foundationNatLE_iff_standard,
    hsizeSelf]

theorem compactAdditiveBoolListDropRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveBoolListDropRowsDef.val := by
  simp [compactAdditiveBoolListDropRowsDef]

theorem CompactAdditiveStructuredListElementRowLayouts.boolDropRows
    {tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat}
    {source target : List Bool}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      targetBoundary target)
    (hconsumed : consumed ≤ source.length)
    (hdrop : target = source.drop consumed) :
    CompactAdditiveBoolListDropRows
      tokenTable width tokenCount sourceBoundary source.length
        targetBoundary target.length consumed := by
  have hcount : source.length = consumed + target.length := by
    rw [hdrop, List.length_drop]
    omega
  refine ⟨hconsumed, hcount, ?_⟩
  intro index hindex
  have hsourceIndex : consumed + index < source.length := by omega
  rcases hsource (consumed + index) hsourceIndex with
    ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
      hsourceLeftEntry, hsourceRightEntry, hsourceLayout⟩
  rcases htarget index hindex with
    ⟨targetLeft, htargetLeft, targetRight, htargetRight,
      htargetLeftEntry, htargetRightEntry, htargetLayout⟩
  have hvalue : source.getI (consumed + index) = target.getI index := by
    have hdropIndex : index < (source.drop consumed).length := by
      simpa [hdrop] using hindex
    rw [hdrop]
    rw [List.getI_eq_getElem _ hsourceIndex]
    rw [List.getI_eq_getElem _ hdropIndex]
    simp
  have hrowEq : CompactAdditiveAtomicRowEq
      tokenTable width tokenCount
        sourceLeft sourceRight targetLeft targetRight := by
    rw [hvalue] at hsourceLayout
    exact CompactAdditiveTokenCell.atomicRowEq
      hsourceLayout.1 htargetLayout.1
  exact ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
    targetLeft, htargetLeft, targetRight, htargetRight,
    hsourceLeftEntry, hsourceRightEntry,
    htargetLeftEntry, htargetRightEntry, hrowEq⟩

theorem CompactAdditiveBoolListDropRows.eq_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat}
    {source target : List Bool}
    (hdropRows : CompactAdditiveBoolListDropRows
      tokenTable width tokenCount sourceBoundary source.length
        targetBoundary target.length consumed)
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      targetBoundary target) :
    target = source.drop consumed := by
  have hconsumed := hdropRows.1
  have hcount := hdropRows.2.1
  have hrowPairs := hdropRows.2.2
  apply List.ext_getElem
  · rw [List.length_drop]
    omega
  · intro index htargetIndex hdropIndex
    have hsourceIndex : consumed + index < source.length := by omega
    rcases hrowPairs index htargetIndex with
      ⟨sourceLeft, _hsourceLeft, sourceRight, _hsourceRight,
        targetLeft, _htargetLeft, targetRight, _htargetRight,
        hsourceLeftEntry, hsourceRightEntry,
        htargetLeftEntry, htargetRightEntry, hrowEq⟩
    rcases hsource (consumed + index) hsourceIndex with
      ⟨rowSourceLeft, _hrowSourceLeft, rowSourceRight,
        _hrowSourceRight, hrowSourceLeftEntry,
        hrowSourceRightEntry, hsourceLayout⟩
    rcases htarget index htargetIndex with
      ⟨rowTargetLeft, _hrowTargetLeft, rowTargetRight,
        _hrowTargetRight, hrowTargetLeftEntry,
        hrowTargetRightEntry, htargetLayout⟩
    have hsourceLeftEq : sourceLeft = rowSourceLeft := by
      exact (CompactFixedWidthEntry.value_eq_tableValue
        hsourceLeftEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowSourceLeftEntry).symm
    have hsourceRightEq : sourceRight = rowSourceRight := by
      exact (CompactFixedWidthEntry.value_eq_tableValue
        hsourceRightEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowSourceRightEntry).symm
    have htargetLeftEq : targetLeft = rowTargetLeft := by
      exact (CompactFixedWidthEntry.value_eq_tableValue
        htargetLeftEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowTargetLeftEntry).symm
    have htargetRightEq : targetRight = rowTargetRight := by
      exact (CompactFixedWidthEntry.value_eq_tableValue
        htargetRightEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowTargetRightEntry).symm
    subst sourceLeft
    subst sourceRight
    subst targetLeft
    subst targetRight
    have hvalue := hrowEq.boolValue_eq hsourceLayout htargetLayout
    rw [List.getI_eq_getElem _ hsourceIndex] at hvalue
    rw [List.getI_eq_getElem _ htargetIndex] at hvalue
    simpa using hvalue.symm

theorem compactAdditiveBoolListDropRows_iff_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat}
    {source target : List Bool}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      targetBoundary target) :
    CompactAdditiveBoolListDropRows
        tokenTable width tokenCount sourceBoundary source.length
          targetBoundary target.length consumed ↔
      consumed ≤ source.length ∧ target = source.drop consumed := by
  constructor
  · intro hdropRows
    exact ⟨hdropRows.1,
      hdropRows.eq_drop_of_rows hsource htarget⟩
  · rintro ⟨hconsumed, hdrop⟩
    exact CompactAdditiveStructuredListElementRowLayouts.boolDropRows
      hsource htarget hconsumed hdrop

/-- A successful decoder step expressed entirely through the source packed
value, a flexible noncanonical segment, and the exact target suffix rows. -/
def CompactAdditiveBoolListDecodeSuccessRows
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      payload digitCount token consumed : Nat) : Prop :=
  CompactAdditiveBoolListPackedValue
      tokenTable width tokenCount sourceBoundary sourceCount payload ∧
    CompactBinaryNatFlexibleDecodeSegment
      payload sourceCount 0 digitCount token consumed ∧
    CompactAdditiveBoolListDropRows
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount consumed

def compactAdditiveBoolListDecodeSuccessRowsDef :
    𝚺₀.Semisentence 11 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      payload digitCount token consumed.
    !(compactAdditiveBoolListPackedValueDef)
      tokenTable width tokenCount sourceBoundary sourceCount payload ∧
    !(compactBinaryNatFlexibleDecodeSegmentDef)
      payload sourceCount 0 digitCount token consumed ∧
    !(compactAdditiveBoolListDropRowsDef)
      tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount consumed”

@[simp] theorem compactAdditiveBoolListDecodeSuccessRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      payload digitCount token consumed : Nat) :
    compactAdditiveBoolListDecodeSuccessRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          payload, digitCount, token, consumed] ↔
      CompactAdditiveBoolListDecodeSuccessRows
        tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount
          payload digitCount token consumed := by
  simp [compactAdditiveBoolListDecodeSuccessRowsDef,
    CompactAdditiveBoolListDecodeSuccessRows]
  have hpackedEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount,
            sourceBoundary, sourceCount, targetBoundary, targetCount,
            payload, digitCount, token, consumed]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2, #3, #4, #7]) =
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, payload] := by
    funext index
    fin_cases index <;> rfl
  have hsegmentEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount,
            sourceBoundary, sourceCount, targetBoundary, targetCount,
            payload, digitCount, token, consumed]
          Empty.elim ∘
        ![(#7 : Semiterm ℒₒᵣ Empty 11), #4, ↑(0 : Nat), #8, #9, #10]) =
        ![payload, sourceCount, 0, digitCount, token, consumed] := by
    funext index
    fin_cases index <;> rfl
  have hdropEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount,
            sourceBoundary, sourceCount, targetBoundary, targetCount,
            payload, digitCount, token, consumed]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2, #3, #4, #5, #6,
          #10]) =
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          consumed] := by
    funext index
    fin_cases index <;> rfl
  rw [hpackedEnv, hsegmentEnv, hdropEnv]
  simp

theorem compactAdditiveBoolListDecodeSuccessRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveBoolListDecodeSuccessRowsDef.val := by
  simp [compactAdditiveBoolListDecodeSuccessRowsDef]

theorem decodeBinaryNat_eq_some_iff_directBoolListRows
    {tokenTable width tokenCount sourceBoundary targetBoundary token : Nat}
    {source target : List Bool}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      targetBoundary target) :
    decodeBinaryNat source = some (token, target) ↔
      ∃ payload digitCount consumed,
        CompactAdditiveBoolListDecodeSuccessRows
          tokenTable width tokenCount
            sourceBoundary source.length targetBoundary target.length
            payload digitCount token consumed := by
  constructor
  · intro hdecode
    rcases (decodeBinaryNat_eq_some_iff_flexibleSegment
      source token target).mp hdecode with
      ⟨digitCount, hsegment, htargetDrop⟩
    let consumed := 2 * digitCount + 2
    refine ⟨natOfBitsList source, digitCount, consumed,
      ?_, hsegment, ?_⟩
    · exact CompactAdditiveStructuredListElementRowLayouts.boolPackedValue
        hsource
    · exact CompactAdditiveStructuredListElementRowLayouts.boolDropRows
        hsource htarget hsegment.2.1 htargetDrop
  · rintro ⟨payload, digitCount, consumed,
      hpacked, hsegment, hdropRows⟩
    have hpayload : payload = natOfBitsList source :=
      hpacked.eq_natOfBitsList_of_rows hsource
    subst payload
    have hconsumed : consumed = 2 * digitCount + 2 := by
      simpa using hsegment.1
    subst consumed
    have htargetDrop : target = source.drop (2 * digitCount + 2) :=
      hdropRows.eq_drop_of_rows hsource htarget
    rw [htargetDrop]
    exact hsegment.decode

#print axioms compactAdditiveBoolListDropRowsDef_spec
#print axioms compactAdditiveBoolListDropRowsDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.boolDropRows
#print axioms CompactAdditiveBoolListDropRows.eq_drop_of_rows
#print axioms compactAdditiveBoolListDropRows_iff_drop_of_rows
#print axioms compactAdditiveBoolListDecodeSuccessRowsDef_spec
#print axioms compactAdditiveBoolListDecodeSuccessRowsDef_sigmaZero
#print axioms decodeBinaryNat_eq_some_iff_directBoolListRows

end FoundationCompactNumericListedDirectBoolListDropRows
