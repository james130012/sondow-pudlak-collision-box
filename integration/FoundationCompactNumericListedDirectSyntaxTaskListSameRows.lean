import integration.FoundationCompactNumericListedDirectAtomicRowEquality
import integration.FoundationCompactNumericListedDirectSyntaxTaskRowRealization

/-!
# Direct equality of two syntax-task list row tables

Each syntax task occupies three consecutive natural-number token cells.  A
bounded arithmetic row relation compares all three fixed-width blocks, and a
list relation applies it at every task index.  Under exact typed row layouts,
the resulting Delta-zero relation is equivalent to equality of the task lists.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSyntaxTaskListSameRows

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization

def CompactAdditiveSyntaxTaskRowEq
    (tokenTable width tokenCount
      sourceLeft sourceRight targetLeft targetRight : Nat) : Prop :=
  CompactAdditiveAtomicRowEq tokenTable width tokenCount
      sourceLeft (sourceLeft + 1) targetLeft (targetLeft + 1) ∧
    CompactAdditiveAtomicRowEq tokenTable width tokenCount
      (sourceLeft + 1) (sourceLeft + 2)
      (targetLeft + 1) (targetLeft + 2) ∧
    CompactAdditiveAtomicRowEq tokenTable width tokenCount
      (sourceLeft + 2) sourceRight (targetLeft + 2) targetRight

def compactAdditiveSyntaxTaskRowEqDef : 𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount
      sourceLeft sourceRight targetLeft targetRight.
    !(compactAdditiveAtomicRowEqDef)
      tokenTable width tokenCount
      sourceLeft (sourceLeft + 1) targetLeft (targetLeft + 1) ∧
    !(compactAdditiveAtomicRowEqDef)
      tokenTable width tokenCount
      (sourceLeft + 1) (sourceLeft + 2)
      (targetLeft + 1) (targetLeft + 2) ∧
    !(compactAdditiveAtomicRowEqDef)
      tokenTable width tokenCount
      (sourceLeft + 2) sourceRight (targetLeft + 2) targetRight”

@[simp] theorem compactAdditiveSyntaxTaskRowEqDef_spec
    (tokenTable width tokenCount
      sourceLeft sourceRight targetLeft targetRight : Nat) :
    compactAdditiveSyntaxTaskRowEqDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceLeft, sourceRight, targetLeft, targetRight] ↔
      CompactAdditiveSyntaxTaskRowEq
        tokenTable width tokenCount
          sourceLeft sourceRight targetLeft targetRight := by
  let env : Fin 7 → Nat :=
    ![tokenTable, width, tokenCount,
      sourceLeft, sourceRight, targetLeft, targetRight]
  change compactAdditiveSyntaxTaskRowEqDef.val.Evalb env ↔ _
  have hkindEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 7), #1, #2, #3,
          ‘(#3 + 1)’, #5, ‘(#5 + 1)’]) =
        ![tokenTable, width, tokenCount,
          sourceLeft, sourceLeft + 1, targetLeft, targetLeft + 1] := by
    funext index
    fin_cases index <;> rfl
  have hbinderEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 7), #1, #2,
          ‘(#3 + 1)’, ‘(#3 + 2)’, ‘(#5 + 1)’, ‘(#5 + 2)’]) =
        ![tokenTable, width, tokenCount,
          sourceLeft + 1, sourceLeft + 2,
          targetLeft + 1, targetLeft + 2] := by
    funext index
    fin_cases index <;> rfl
  have hcountEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 7), #1, #2,
          ‘(#3 + 2)’, #4, ‘(#5 + 2)’, #6]) =
        ![tokenTable, width, tokenCount,
          sourceLeft + 2, sourceRight, targetLeft + 2, targetRight] := by
    funext index
    fin_cases index <;> rfl
  simp [compactAdditiveSyntaxTaskRowEqDef,
    CompactAdditiveSyntaxTaskRowEq,
    hkindEnv, hbinderEnv, hcountEnv]

theorem compactAdditiveSyntaxTaskRowEqDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveSyntaxTaskRowEqDef.val := by
  simp [compactAdditiveSyntaxTaskRowEqDef]

theorem CompactSyntaxTaskDirectLayout.rowEq
    {tokenTable width tokenCount
      sourceLeft sourceRight targetLeft targetRight : Nat}
    {task : CompactSyntaxTask}
    (hsource : CompactSyntaxTaskDirectLayout
      tokenTable width tokenCount sourceLeft sourceRight task)
    (htarget : CompactSyntaxTaskDirectLayout
      tokenTable width tokenCount targetLeft targetRight task) :
    CompactAdditiveSyntaxTaskRowEq
      tokenTable width tokenCount
        sourceLeft sourceRight targetLeft targetRight := by
  rcases hsource with
    ⟨sourceBinderStart, sourceCountStart,
      hsourceKind, hsourceBinder, hsourceCount⟩
  rcases htarget with
    ⟨targetBinderStart, targetCountStart,
      htargetKind, htargetBinder, htargetCount⟩
  have hsourceBinderStart : sourceBinderStart = sourceLeft + 1 :=
    hsourceKind.2.1
  have htargetBinderStart : targetBinderStart = targetLeft + 1 :=
    htargetKind.2.1
  have hsourceCountStart : sourceCountStart = sourceLeft + 2 := by
    have hnext := hsourceBinder.2.1
    omega
  have htargetCountStart : targetCountStart = targetLeft + 2 := by
    have hnext := htargetBinder.2.1
    omega
  have hsourceKind' : CompactAdditiveTokenCell
      tokenTable width tokenCount sourceLeft task.1 (sourceLeft + 1) := by
    simpa [hsourceBinderStart] using hsourceKind
  have htargetKind' : CompactAdditiveTokenCell
      tokenTable width tokenCount targetLeft task.1 (targetLeft + 1) := by
    simpa [htargetBinderStart] using htargetKind
  have hsourceBinder' : CompactAdditiveTokenCell
      tokenTable width tokenCount
        (sourceLeft + 1) task.2.1 (sourceLeft + 2) := by
    simpa [hsourceBinderStart, hsourceCountStart] using hsourceBinder
  have htargetBinder' : CompactAdditiveTokenCell
      tokenTable width tokenCount
        (targetLeft + 1) task.2.1 (targetLeft + 2) := by
    simpa [htargetBinderStart, htargetCountStart] using htargetBinder
  have hsourceCount' : CompactAdditiveTokenCell
      tokenTable width tokenCount
        (sourceLeft + 2) task.2.2 sourceRight := by
    simpa [hsourceCountStart] using hsourceCount
  have htargetCount' : CompactAdditiveTokenCell
      tokenTable width tokenCount
        (targetLeft + 2) task.2.2 targetRight := by
    simpa [htargetCountStart] using htargetCount
  exact ⟨
    FoundationCompactNumericListedDirectAtomicRowEquality.CompactAdditiveTokenCell.atomicRowEq
      hsourceKind' htargetKind',
    FoundationCompactNumericListedDirectAtomicRowEquality.CompactAdditiveTokenCell.atomicRowEq
      hsourceBinder' htargetBinder',
    FoundationCompactNumericListedDirectAtomicRowEquality.CompactAdditiveTokenCell.atomicRowEq
      hsourceCount' htargetCount'⟩

theorem CompactAdditiveSyntaxTaskRowEq.value_eq
    {tokenTable width tokenCount
      sourceLeft sourceRight targetLeft targetRight : Nat}
    {sourceTask targetTask : CompactSyntaxTask}
    (heq : CompactAdditiveSyntaxTaskRowEq
      tokenTable width tokenCount
        sourceLeft sourceRight targetLeft targetRight)
    (hsource : CompactSyntaxTaskDirectLayout
      tokenTable width tokenCount sourceLeft sourceRight sourceTask)
    (htarget : CompactSyntaxTaskDirectLayout
      tokenTable width tokenCount targetLeft targetRight targetTask) :
    sourceTask = targetTask := by
  rcases heq with ⟨hkindEq, hbinderEq, hcountEq⟩
  rcases hsource with
    ⟨sourceBinderStart, sourceCountStart,
      hsourceKind, hsourceBinder, hsourceCount⟩
  rcases htarget with
    ⟨targetBinderStart, targetCountStart,
      htargetKind, htargetBinder, htargetCount⟩
  have hsourceBinderStart : sourceBinderStart = sourceLeft + 1 :=
    hsourceKind.2.1
  have htargetBinderStart : targetBinderStart = targetLeft + 1 :=
    htargetKind.2.1
  have hsourceCountStart : sourceCountStart = sourceLeft + 2 := by
    have hnext := hsourceBinder.2.1
    omega
  have htargetCountStart : targetCountStart = targetLeft + 2 := by
    have hnext := htargetBinder.2.1
    omega
  have hsourceKind' : CompactAdditiveTokenCell
      tokenTable width tokenCount sourceLeft sourceTask.1
        (sourceLeft + 1) := by
    simpa [hsourceBinderStart] using hsourceKind
  have htargetKind' : CompactAdditiveTokenCell
      tokenTable width tokenCount targetLeft targetTask.1
        (targetLeft + 1) := by
    simpa [htargetBinderStart] using htargetKind
  have hsourceBinder' : CompactAdditiveTokenCell
      tokenTable width tokenCount
        (sourceLeft + 1) sourceTask.2.1 (sourceLeft + 2) := by
    simpa [hsourceBinderStart, hsourceCountStart] using hsourceBinder
  have htargetBinder' : CompactAdditiveTokenCell
      tokenTable width tokenCount
        (targetLeft + 1) targetTask.2.1 (targetLeft + 2) := by
    simpa [htargetBinderStart, htargetCountStart] using htargetBinder
  have hsourceCount' : CompactAdditiveTokenCell
      tokenTable width tokenCount
        (sourceLeft + 2) sourceTask.2.2 sourceRight := by
    simpa [hsourceCountStart] using hsourceCount
  have htargetCount' : CompactAdditiveTokenCell
      tokenTable width tokenCount
        (targetLeft + 2) targetTask.2.2 targetRight := by
    simpa [htargetCountStart] using htargetCount
  have hkind : sourceTask.1 = targetTask.1 :=
    hkindEq.value_eq hsourceKind' htargetKind'
  have hbinder : sourceTask.2.1 = targetTask.2.1 :=
    hbinderEq.value_eq hsourceBinder' htargetBinder'
  have hcount : sourceTask.2.2 = targetTask.2.2 :=
    hcountEq.value_eq hsourceCount' htargetCount'
  exact Prod.ext hkind (Prod.ext hbinder hcount)

def CompactAdditiveSyntaxTaskListSameRows
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
        CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount
          sourceLeft sourceRight targetLeft targetRight

def compactAdditiveSyntaxTaskListSameRowsDef :
    𝚺₀.Semisentence 7 := .mkSigma
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
              !(compactAdditiveSyntaxTaskRowEqDef)
                tokenTable width tokenCount
                sourceLeft sourceRight targetLeft targetRight”

@[simp] theorem compactAdditiveSyntaxTaskListSameRowsDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount : Nat) :
    compactAdditiveSyntaxTaskListSameRowsDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, targetBoundary, targetCount] ↔
      CompactAdditiveSyntaxTaskListSameRows
        tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount := by
  have hrow
      (targetRight targetLeft sourceRight sourceLeft index : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![targetRight, targetLeft, sourceRight, sourceLeft, index,
                tokenTable, width, tokenCount,
                sourceBoundary, sourceCount, targetBoundary, targetCount]
              Empty.elim ∘
            ![(#5 : Semiterm ℒₒᵣ Empty 12), #6, #7,
              #3, #2, #1, #0])
          Empty.elim) compactAdditiveSyntaxTaskRowEqDef.val ↔
        CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount
          sourceLeft sourceRight targetLeft targetRight := by
    have henv :
        (Semiterm.val
            ![targetRight, targetLeft, sourceRight, sourceLeft, index,
              tokenTable, width, tokenCount,
              sourceBoundary, sourceCount, targetBoundary, targetCount]
            Empty.elim ∘
          ![(#5 : Semiterm ℒₒᵣ Empty 12), #6, #7,
            #3, #2, #1, #0]) =
          ![tokenTable, width, tokenCount,
            sourceLeft, sourceRight, targetLeft, targetRight] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    simp
  simp [compactAdditiveSyntaxTaskListSameRowsDef,
    CompactAdditiveSyntaxTaskListSameRows, hrow]

theorem compactAdditiveSyntaxTaskListSameRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveSyntaxTaskListSameRowsDef.val := by
  simp [compactAdditiveSyntaxTaskListSameRowsDef]

theorem CompactAdditiveStructuredListElementRowLayouts.taskSameRows
    {tokenTable width tokenCount sourceBoundary targetBoundary : Nat}
    {source target : List CompactSyntaxTask}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsame : target = source) :
    CompactAdditiveSyntaxTaskListSameRows
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
  exact ⟨sourceLeft, hsourceLeft, sourceRight, hsourceRight,
    targetLeft, htargetLeft, targetRight, htargetRight,
    hsourceLeftEntry, hsourceRightEntry,
    htargetLeftEntry, htargetRightEntry,
    CompactSyntaxTaskDirectLayout.rowEq
      hsourceLayout htargetLayout⟩

theorem CompactAdditiveSyntaxTaskListSameRows.eq_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary : Nat}
    {source target : List CompactSyntaxTask}
    (hsameRows : CompactAdditiveSyntaxTaskListSameRows
      tokenTable width tokenCount sourceBoundary source.length
        targetBoundary target.length)
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
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
    have hvalue := hrowEq.value_eq hsourceLayout htargetLayout
    rw [List.getI_eq_getElem _ hsourceIndex] at hvalue
    rw [List.getI_eq_getElem _ htargetIndex] at hvalue
    exact hvalue.symm

theorem compactAdditiveSyntaxTaskListSameRows_iff_eq_of_rows
    {tokenTable width tokenCount sourceBoundary targetBoundary : Nat}
    {source target : List CompactSyntaxTask}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htarget : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    CompactAdditiveSyntaxTaskListSameRows
        tokenTable width tokenCount sourceBoundary source.length
          targetBoundary target.length ↔
      target = source := by
  constructor
  · intro hsameRows
    exact hsameRows.eq_of_rows hsource htarget
  · intro hsame
    exact CompactAdditiveStructuredListElementRowLayouts.taskSameRows
      hsource htarget hsame

#print axioms compactAdditiveSyntaxTaskRowEqDef_spec
#print axioms compactAdditiveSyntaxTaskRowEqDef_sigmaZero
#print axioms CompactSyntaxTaskDirectLayout.rowEq
#print axioms CompactAdditiveSyntaxTaskRowEq.value_eq
#print axioms compactAdditiveSyntaxTaskListSameRowsDef_spec
#print axioms compactAdditiveSyntaxTaskListSameRowsDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.taskSameRows
#print axioms CompactAdditiveSyntaxTaskListSameRows.eq_of_rows
#print axioms compactAdditiveSyntaxTaskListSameRows_iff_eq_of_rows

end FoundationCompactNumericListedDirectSyntaxTaskListSameRows
