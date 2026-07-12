import integration.FoundationCompactNumericListedDirectAtomicRowEquality

/-!
# Direct row graph for dropping a natural-number-list prefix

The target list begins at a certified source index.  Every target atomic row
is equal to the corresponding shifted source row.  Under the real row layouts
the bounded graph is exactly `target = source.drop consumed`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListDropRows

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicRowEquality

def CompactAdditiveNatListDropRows
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

def compactAdditiveNatListDropRowsDef : 𝚺₀.Semisentence 8 := .mkSigma
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
              !(compactAdditiveAtomicRowEqDef)
                tokenTable width tokenCount
                  sourceLeft sourceRight targetLeft targetRight”

@[simp] theorem compactAdditiveNatListDropRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount consumed : Nat) :
    compactAdditiveNatListDropRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          consumed] ↔
      CompactAdditiveNatListDropRows
        tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount consumed := by
  have hrow
      (targetRight targetLeft sourceRight sourceLeft index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![targetRight, targetLeft, sourceRight, sourceLeft, index,
                tokenTable, width, tokenCount,
                sourceBoundary, sourceCount, targetBoundary, targetCount,
                consumed]
              Empty.elim ∘
            ![(#5 : Semiterm ℒₒᵣ Empty 13), #6, #7,
              #3, #2, #1, #0])
          Empty.elim) compactAdditiveAtomicRowEqDef.val ↔
        CompactAdditiveAtomicRowEq tokenTable width tokenCount
          sourceLeft sourceRight targetLeft targetRight := by
    have henv :
        (Semiterm.val
            ![targetRight, targetLeft, sourceRight, sourceLeft, index,
              tokenTable, width, tokenCount,
              sourceBoundary, sourceCount, targetBoundary, targetCount,
              consumed]
            Empty.elim ∘
          ![(#5 : Semiterm ℒₒᵣ Empty 13), #6, #7,
            #3, #2, #1, #0]) =
          ![tokenTable, width, tokenCount,
            sourceLeft, sourceRight, targetLeft, targetRight] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    simp
  simp [compactAdditiveNatListDropRowsDef,
    CompactAdditiveNatListDropRows, hrow]

theorem compactAdditiveNatListDropRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListDropRowsDef.val := by
  simp [compactAdditiveNatListDropRowsDef]

theorem CompactAdditiveStructuredListElementRowLayouts.natDropRows
    {tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat}
    {source target : List Nat}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hconsumed : consumed ≤ source.length)
    (hdrop : target = source.drop consumed) :
    CompactAdditiveNatListDropRows
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
      hsourceLayout htargetLayout
  exact ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
    targetLeft, htargetLeft, targetRight, htargetRight,
    hsourceLeftEntry, hsourceRightEntry,
    htargetLeftEntry, htargetRightEntry, hrowEq⟩

theorem CompactAdditiveNatListDropRows.eq_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat}
    {source target : List Nat}
    (hdropRows : CompactAdditiveNatListDropRows
      tokenTable width tokenCount sourceBoundary source.length
        targetBoundary target.length consumed)
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
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
    have hsourceLeftEq : sourceLeft = rowSourceLeft :=
      (CompactFixedWidthEntry.value_eq_tableValue
        hsourceLeftEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowSourceLeftEntry).symm
    have hsourceRightEq : sourceRight = rowSourceRight :=
      (CompactFixedWidthEntry.value_eq_tableValue
        hsourceRightEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowSourceRightEntry).symm
    have htargetLeftEq : targetLeft = rowTargetLeft :=
      (CompactFixedWidthEntry.value_eq_tableValue
        htargetLeftEntry).trans
          (CompactFixedWidthEntry.value_eq_tableValue
            hrowTargetLeftEntry).symm
    have htargetRightEq : targetRight = rowTargetRight :=
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

theorem compactAdditiveNatListDropRows_iff_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat}
    {source target : List Nat}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    CompactAdditiveNatListDropRows
        tokenTable width tokenCount sourceBoundary source.length
          targetBoundary target.length consumed ↔
      consumed ≤ source.length ∧ target = source.drop consumed := by
  constructor
  · intro hdropRows
    exact ⟨hdropRows.1,
      hdropRows.eq_drop_of_rows hsource htarget⟩
  · rintro ⟨hconsumed, hdrop⟩
    exact CompactAdditiveStructuredListElementRowLayouts.natDropRows
      hsource htarget hconsumed hdrop

#print axioms compactAdditiveNatListDropRowsDef_spec
#print axioms compactAdditiveNatListDropRowsDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.natDropRows
#print axioms CompactAdditiveNatListDropRows.eq_drop_of_rows
#print axioms compactAdditiveNatListDropRows_iff_drop_of_rows

end FoundationCompactNumericListedDirectNatListDropRows
