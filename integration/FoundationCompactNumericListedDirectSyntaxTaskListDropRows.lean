import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRows

/-!
# Direct row graph for dropping a syntax-task-list prefix

The target task list begins at a certified source index.  Every target
three-token row is equal to the corresponding shifted source row.  The bounded
graph is proved equivalent to `target = source.drop consumed` under the real
task row layouts; parser task popping is the instance `consumed = 1`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropRows

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows

def CompactAdditiveSyntaxTaskListDropRows
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
        CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount
          sourceLeft sourceRight targetLeft targetRight

def compactAdditiveSyntaxTaskListDropRowsDef :
    𝚺₀.Semisentence 8 := .mkSigma
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
              !(compactAdditiveSyntaxTaskRowEqDef)
                tokenTable width tokenCount
                  sourceLeft sourceRight targetLeft targetRight”

@[simp] theorem compactAdditiveSyntaxTaskListDropRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount consumed : Nat) :
    compactAdditiveSyntaxTaskListDropRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          consumed] ↔
      CompactAdditiveSyntaxTaskListDropRows
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
          Empty.elim) compactAdditiveSyntaxTaskRowEqDef.val ↔
        CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount
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
  simp [compactAdditiveSyntaxTaskListDropRowsDef,
    CompactAdditiveSyntaxTaskListDropRows, hrow]

theorem compactAdditiveSyntaxTaskListDropRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveSyntaxTaskListDropRowsDef.val := by
  simp [compactAdditiveSyntaxTaskListDropRowsDef]

theorem CompactAdditiveStructuredListElementRowLayouts.taskDropRows
    {tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat}
    {source target : List CompactSyntaxTask}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hconsumed : consumed ≤ source.length)
    (hdrop : target = source.drop consumed) :
    CompactAdditiveSyntaxTaskListDropRows
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
  have hrowEq : CompactAdditiveSyntaxTaskRowEq
      tokenTable width tokenCount
        sourceLeft sourceRight targetLeft targetRight := by
    rw [hvalue] at hsourceLayout
    exact CompactSyntaxTaskDirectLayout.rowEq
      hsourceLayout htargetLayout
  exact ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
    targetLeft, htargetLeft, targetRight, htargetRight,
    hsourceLeftEntry, hsourceRightEntry,
    htargetLeftEntry, htargetRightEntry, hrowEq⟩

theorem CompactAdditiveSyntaxTaskListDropRows.eq_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat}
    {source target : List CompactSyntaxTask}
    (hdropRows : CompactAdditiveSyntaxTaskListDropRows
      tokenTable width tokenCount sourceBoundary source.length
        targetBoundary target.length consumed)
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
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
    have hvalue := hrowEq.value_eq hsourceLayout htargetLayout
    rw [List.getI_eq_getElem _ hsourceIndex] at hvalue
    rw [List.getI_eq_getElem _ htargetIndex] at hvalue
    simpa using hvalue.symm

theorem compactAdditiveSyntaxTaskListDropRows_iff_drop_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat}
    {source target : List CompactSyntaxTask}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    CompactAdditiveSyntaxTaskListDropRows
        tokenTable width tokenCount sourceBoundary source.length
          targetBoundary target.length consumed ↔
      consumed ≤ source.length ∧ target = source.drop consumed := by
  constructor
  · intro hdropRows
    exact ⟨hdropRows.1,
      hdropRows.eq_drop_of_rows hsource htarget⟩
  · rintro ⟨hconsumed, hdrop⟩
    exact CompactAdditiveStructuredListElementRowLayouts.taskDropRows
      hsource htarget hconsumed hdrop

#print axioms compactAdditiveSyntaxTaskListDropRowsDef_spec
#print axioms compactAdditiveSyntaxTaskListDropRowsDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.taskDropRows
#print axioms CompactAdditiveSyntaxTaskListDropRows.eq_drop_of_rows
#print axioms compactAdditiveSyntaxTaskListDropRows_iff_drop_of_rows

end FoundationCompactNumericListedDirectSyntaxTaskListDropRows
