import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRows

/-!
# Direct row graph for syntax-task list cons

The target row zero carries a supplied three-field syntax task.  Every later
target row equals the preceding source task row.  The bounded graph is proved
equivalent to `target = head :: source` under exact task row layouts.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRows

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows

def CompactAdditiveSyntaxTaskListConsRows
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat) : Prop :=
  targetCount = sourceCount + 1 ∧
    (∃ targetLeft, targetLeft ≤ tokenCount ∧
      ∃ targetRight, targetRight ≤ tokenCount ∧
        CompactFixedWidthEntry targetBoundary tokenCount 0 targetLeft ∧
        CompactFixedWidthEntry targetBoundary tokenCount 1 targetRight ∧
        CompactSyntaxTaskDirectLayout tokenTable width tokenCount
          targetLeft targetRight
          (headKind, headBinderArity, headRepeatCount)) ∧
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
        CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount
          sourceLeft sourceRight targetLeft targetRight

def compactAdditiveSyntaxTaskListConsRowsDef :
    𝚺₀.Semisentence 10 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount.
    targetCount = sourceCount + 1 ∧
    (∃ targetLeft <⁺ tokenCount,
      ∃ targetRight <⁺ tokenCount,
        !(compactFixedWidthEntryDef)
          targetBoundary tokenCount 0 targetLeft ∧
        !(compactFixedWidthEntryDef)
          targetBoundary tokenCount 1 targetRight ∧
        !(compactSyntaxTaskDirectLayoutDef)
          tokenTable width tokenCount targetLeft targetRight
            headKind headBinderArity headRepeatCount) ∧
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
              !(compactAdditiveSyntaxTaskRowEqDef)
                tokenTable width tokenCount
                  sourceLeft sourceRight targetLeft targetRight”

@[simp] theorem compactAdditiveSyntaxTaskListConsRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      headKind headBinderArity headRepeatCount : Nat) :
    compactAdditiveSyntaxTaskListConsRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount,
          headKind, headBinderArity, headRepeatCount] ↔
      CompactAdditiveSyntaxTaskListConsRows
        tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount
          headKind headBinderArity headRepeatCount := by
  have hhead (targetRight targetLeft : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![targetRight, targetLeft,
                tokenTable, width, tokenCount,
                sourceBoundary, sourceCount, targetBoundary, targetCount,
                headKind, headBinderArity, headRepeatCount]
              Empty.elim ∘
            ![(#2 : Semiterm ℒₒᵣ Empty 12), #3, #4, #1, #0,
              #9, #10, #11])
          Empty.elim) compactSyntaxTaskDirectLayoutDef.val ↔
        CompactSyntaxTaskDirectLayout tokenTable width tokenCount
          targetLeft targetRight
            (headKind, headBinderArity, headRepeatCount) := by
    have henv :
        (Semiterm.val
            ![targetRight, targetLeft,
              tokenTable, width, tokenCount,
              sourceBoundary, sourceCount, targetBoundary, targetCount,
              headKind, headBinderArity, headRepeatCount]
            Empty.elim ∘
          ![(#2 : Semiterm ℒₒᵣ Empty 12), #3, #4, #1, #0,
            #9, #10, #11]) =
          ![tokenTable, width, tokenCount,
            targetLeft, targetRight,
            headKind, headBinderArity, headRepeatCount] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    simp
  have hrow
      (targetRight targetLeft sourceRight sourceLeft index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![targetRight, targetLeft, sourceRight, sourceLeft, index,
                tokenTable, width, tokenCount,
                sourceBoundary, sourceCount, targetBoundary, targetCount,
                headKind, headBinderArity, headRepeatCount]
              Empty.elim ∘
            ![(#5 : Semiterm ℒₒᵣ Empty 15), #6, #7,
              #3, #2, #1, #0])
          Empty.elim) compactAdditiveSyntaxTaskRowEqDef.val ↔
        CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount
          sourceLeft sourceRight targetLeft targetRight := by
    have henv :
        (Semiterm.val
            ![targetRight, targetLeft, sourceRight, sourceLeft, index,
              tokenTable, width, tokenCount,
              sourceBoundary, sourceCount, targetBoundary, targetCount,
              headKind, headBinderArity, headRepeatCount]
            Empty.elim ∘
          ![(#5 : Semiterm ℒₒᵣ Empty 15), #6, #7,
            #3, #2, #1, #0]) =
          ![tokenTable, width, tokenCount,
            sourceLeft, sourceRight, targetLeft, targetRight] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    simp
  simp [compactAdditiveSyntaxTaskListConsRowsDef,
    CompactAdditiveSyntaxTaskListConsRows, hhead, hrow]
  intro _hcount _targetLeft _htargetLeft
    _targetRight _htargetRight
    _hleftEntry _hrightEntry _hheadLayout
  constructor
  · intro htail index hindex
    exact htail index hindex
  · intro htail index hindex
    exact htail index hindex

theorem compactAdditiveSyntaxTaskListConsRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveSyntaxTaskListConsRowsDef.val := by
  simp [compactAdditiveSyntaxTaskListConsRowsDef]

theorem CompactAdditiveStructuredListElementRowLayouts.taskConsRows
    {tokenTable width tokenCount sourceBoundary targetBoundary : Nat}
    {head : CompactSyntaxTask}
    {source target : List CompactSyntaxTask}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hcons : target = head :: source) :
    CompactAdditiveSyntaxTaskListConsRows
      tokenTable width tokenCount sourceBoundary source.length
        targetBoundary target.length head.1 head.2.1 head.2.2 := by
  have hcount : target.length = source.length + 1 := by simp [hcons]
  have htargetZero : 0 < target.length := by omega
  rcases htarget 0 htargetZero with
    ⟨headLeft, hheadLeft, headRight, hheadRight,
      hheadLeftEntry, hheadRightEntry, hheadLayout⟩
  have hheadLayout' : CompactSyntaxTaskDirectLayout
      tokenTable width tokenCount headLeft headRight head := by
    simpa [hcons] using hheadLayout
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

theorem CompactAdditiveSyntaxTaskListConsRows.eq_cons_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary : Nat}
    {head : CompactSyntaxTask}
    {source target : List CompactSyntaxTask}
    (hconsRows : CompactAdditiveSyntaxTaskListConsRows
      tokenTable width tokenCount sourceBoundary source.length
        targetBoundary target.length head.1 head.2.1 head.2.2)
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
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
            hheadLeftEntry, hheadRightEntry, hheadLayout⟩
        rcases htarget 0 htargetIndex with
          ⟨rowLeft, _hrowLeft, rowRight, _hrowRight,
            hrowLeftEntry, hrowRightEntry, htargetLayout⟩
        have hleft : headLeft = rowLeft :=
          (CompactFixedWidthEntry.value_eq_tableValue
            hheadLeftEntry).trans
              (CompactFixedWidthEntry.value_eq_tableValue
                hrowLeftEntry).symm
        have hright : headRight = rowRight :=
          (CompactFixedWidthEntry.value_eq_tableValue
            hheadRightEntry).trans
              (CompactFixedWidthEntry.value_eq_tableValue
                hrowRightEntry).symm
        subst headLeft
        subst headRight
        have hrowEq : CompactAdditiveSyntaxTaskRowEq
            tokenTable width tokenCount
              rowLeft rowRight rowLeft rowRight :=
          CompactSyntaxTaskDirectLayout.rowEq
            hheadLayout hheadLayout
        have hvalue := CompactAdditiveSyntaxTaskRowEq.value_eq
          hrowEq hheadLayout htargetLayout
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
        have hvalue := hrowEq.value_eq hsourceLayout htargetLayout
        rw [List.getI_eq_getElem _ hsourceIndex] at hvalue
        rw [List.getI_eq_getElem _ htargetIndex] at hvalue
        simpa using hvalue.symm

theorem compactAdditiveSyntaxTaskListConsRows_iff_cons_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary : Nat}
    {head : CompactSyntaxTask}
    {source target : List CompactSyntaxTask}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    CompactAdditiveSyntaxTaskListConsRows
        tokenTable width tokenCount sourceBoundary source.length
          targetBoundary target.length head.1 head.2.1 head.2.2 ↔
      target = head :: source := by
  constructor
  · intro hconsRows
    exact hconsRows.eq_cons_of_rows hsource htarget
  · intro hcons
    exact CompactAdditiveStructuredListElementRowLayouts.taskConsRows
      hsource htarget hcons

#print axioms compactAdditiveSyntaxTaskListConsRowsDef_spec
#print axioms compactAdditiveSyntaxTaskListConsRowsDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.taskConsRows
#print axioms CompactAdditiveSyntaxTaskListConsRows.eq_cons_of_rows
#print axioms compactAdditiveSyntaxTaskListConsRows_iff_cons_of_rows

end FoundationCompactNumericListedDirectSyntaxTaskListConsRows
