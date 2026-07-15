import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefix
import integration.FoundationCompactNumericListedDirectNatListAtRows

/-!
# Bounded append of two explicit natural values

The target preserves every row of the source list and adds two explicitly
checked rows.  Under exact layouts this is precisely `target = source ++
[first, second]`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListAppendTwoValues

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAtRows

def CompactAdditiveNatListAppendTwoValues
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second : Nat) : Prop :=
  targetFinish = targetStart + 1 + targetCount ∧
    targetCount = sourceCount + 2 ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (sourceStart + 1) sourceFinish
      (targetStart + 1) (targetStart + 1 + sourceCount) ∧
    CompactAdditiveNatListAtRows tokenTable width tokenCount
      targetBoundary targetCount sourceCount first ∧
    CompactAdditiveNatListAtRows tokenTable width tokenCount
      targetBoundary targetCount (sourceCount + 1) second

def compactAdditiveNatListAppendTwoValuesDef :
    𝚺₀.Semisentence 12 := .mkSigma
  “tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second.
    targetFinish = targetStart + 1 + targetCount ∧
    targetCount = sourceCount + 2 ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        (sourceStart + 1) sourceFinish
        (targetStart + 1) (targetStart + 1 + sourceCount) ∧
    !(compactAdditiveNatListAtRowsDef)
      tokenTable width tokenCount targetBoundary targetCount
        sourceCount first ∧
    !(compactAdditiveNatListAtRowsDef)
      tokenTable width tokenCount targetBoundary targetCount
        (sourceCount + 1) second”

@[simp] theorem compactAdditiveNatListAppendTwoValuesDef_spec
    (tokenTable width tokenCount
      sourceStart sourceFinish sourceCount
      targetStart targetFinish targetBoundary targetCount
      first second : Nat) :
    compactAdditiveNatListAppendTwoValuesDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceStart, sourceFinish, sourceCount,
          targetStart, targetFinish, targetBoundary, targetCount,
          first, second] ↔
      CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
        sourceStart sourceFinish sourceCount
        targetStart targetFinish targetBoundary targetCount
        first second := by
  have hslices :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount,
                sourceStart, sourceFinish, sourceCount,
                targetStart, targetFinish, targetBoundary, targetCount,
                first, second]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2,
              ‘(#3 + 1)’, #4, ‘(#6 + 1)’, ‘((#6 + 1) + #5)’])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          (sourceStart + 1) sourceFinish
          (targetStart + 1) (targetStart + 1 + sourceCount) := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount,
              sourceStart, sourceFinish, sourceCount,
              targetStart, targetFinish, targetBoundary, targetCount,
              first, second]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2,
            ‘(#3 + 1)’, #4, ‘(#6 + 1)’, ‘((#6 + 1) + #5)’]) =
          ![tokenTable, width, tokenCount,
            sourceStart + 1, sourceFinish,
            targetStart + 1, targetStart + 1 + sourceCount] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
        (sourceStart + 1) sourceFinish
        (targetStart + 1) (targetStart + 1 + sourceCount)
  have hfirst :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount,
                sourceStart, sourceFinish, sourceCount,
                targetStart, targetFinish, targetBoundary, targetCount,
                first, second]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2,
              #8, #9, #5, #10])
          Empty.elim) compactAdditiveNatListAtRowsDef.val ↔
        CompactAdditiveNatListAtRows tokenTable width tokenCount
          targetBoundary targetCount sourceCount first := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount,
              sourceStart, sourceFinish, sourceCount,
              targetStart, targetFinish, targetBoundary, targetCount,
              first, second]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2,
            #8, #9, #5, #10]) =
          ![tokenTable, width, tokenCount,
            targetBoundary, targetCount, sourceCount, first] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactAdditiveNatListAtRowsDef_spec
      tokenTable width tokenCount targetBoundary targetCount sourceCount first
  have hsecond :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount,
                sourceStart, sourceFinish, sourceCount,
                targetStart, targetFinish, targetBoundary, targetCount,
                first, second]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2,
              #8, #9, ‘(#5 + 1)’, #11])
          Empty.elim) compactAdditiveNatListAtRowsDef.val ↔
        CompactAdditiveNatListAtRows tokenTable width tokenCount
          targetBoundary targetCount (sourceCount + 1) second := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount,
              sourceStart, sourceFinish, sourceCount,
              targetStart, targetFinish, targetBoundary, targetCount,
              first, second]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2,
            #8, #9, ‘(#5 + 1)’, #11]) =
          ![tokenTable, width, tokenCount,
            targetBoundary, targetCount, sourceCount + 1, second] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactAdditiveNatListAtRowsDef_spec
      tokenTable width tokenCount targetBoundary targetCount
        (sourceCount + 1) second
  simp [compactAdditiveNatListAppendTwoValuesDef,
    CompactAdditiveNatListAppendTwoValues, hslices, hfirst, hsecond]
  tauto

theorem compactAdditiveNatListAppendTwoValuesDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListAppendTwoValuesDef.val := by
  simp [compactAdditiveNatListAppendTwoValuesDef]

theorem compactAdditiveNatListAppendTwoValues_iff
    {tokenTable width tokenCount sourceStart sourceFinish
      targetStart targetFinish targetBoundary first second : Nat}
    {source target : List Nat}
    (hsource : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      sourceStart sourceFinish source)
    (htarget : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      targetStart targetFinish target)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    CompactAdditiveNatListAppendTwoValues tokenTable width tokenCount
        sourceStart sourceFinish source.length
        targetStart targetFinish targetBoundary target.length first second ↔
      target = source ++ [first, second] := by
  constructor
  · rintro ⟨_htargetFinish, hcount, hslices,
      hfirstRows, hsecondRows⟩
    have hsourceFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hsource
    have hfirstValue :=
      (compactAdditiveNatListAtRows_iff_getI
        htargetRows source.length first).mp hfirstRows
    have hsecondValue :=
      (compactAdditiveNatListAtRows_iff_getI
        htargetRows (source.length + 1) second).mp hsecondRows
    apply List.ext_getElem
    · simpa using hcount
    · intro index htargetIndex happendIndex
      by_cases hindex : index < source.length
      · have hsourceEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            hsource index hindex
        have htargetEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            htarget index htargetIndex
        have hvalue := CompactFixedWidthTokenSlicesEq.bodyValue_eq
          (sourceStart := sourceStart + 1)
          (sourceFinish := sourceFinish)
          (targetStart := targetStart + 1)
          (targetFinish := targetStart + 1 + source.length)
          (offset := index)
          hslices (by omega)
            (by simpa [Nat.add_assoc] using hsourceEntry)
            (by simpa [Nat.add_assoc] using htargetEntry)
        rw [List.getI_eq_getElem source hindex] at hvalue
        rw [List.getI_eq_getElem target htargetIndex] at hvalue
        simpa [List.getElem_append, hindex] using hvalue.symm
      · have hsourceLe : source.length ≤ index := Nat.le_of_not_gt hindex
        have hindexCases : index = source.length ∨
            index = source.length + 1 := by
          omega
        rcases hindexCases with rfl | rfl
        · have hfirstEq := hfirstValue.2
          rw [List.getI_eq_getElem target htargetIndex] at hfirstEq
          simpa using hfirstEq
        · have hsecondEq := hsecondValue.2
          rw [List.getI_eq_getElem target htargetIndex] at hsecondEq
          simpa using hsecondEq
  · intro htargetEq
    have hslices :=
      CompactAdditiveNatListDirectLayout.bodySlicesEq
        (targetOffset := 0) hsource htarget
        (by simp [htargetEq]) (by
          intro index hindex
          rw [htargetEq]
          rw [List.getI_eq_getElem source hindex]
          rw [List.getI_eq_getElem (source ++ [first, second]) (by simp; omega)]
          simp [List.getElem_append, hindex])
    have hfirstRows : CompactAdditiveNatListAtRows
        tokenTable width tokenCount targetBoundary target.length
          source.length first :=
      (compactAdditiveNatListAtRows_iff_getI
        htargetRows source.length first).mpr (by
          rw [htargetEq]
          refine ⟨by simp, ?_⟩
          simpa using
            (List.getI_append_right source [first, second]
              source.length (by omega)))
    have hsecondRows : CompactAdditiveNatListAtRows
        tokenTable width tokenCount targetBoundary target.length
          (source.length + 1) second :=
      (compactAdditiveNatListAtRows_iff_getI
        htargetRows (source.length + 1) second).mpr (by
          rw [htargetEq]
          refine ⟨by simp, ?_⟩
          simpa using
            (List.getI_append_right source [first, second]
              (source.length + 1) (by omega)))
    have htargetFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq htarget
    exact ⟨htargetFinish, by simp [htargetEq],
      hslices, hfirstRows, hsecondRows⟩

#print axioms compactAdditiveNatListAppendTwoValuesDef_spec
#print axioms compactAdditiveNatListAppendTwoValuesDef_sigmaZero
#print axioms compactAdditiveNatListAppendTwoValues_iff

end FoundationCompactNumericListedDirectNatListAppendTwoValues
