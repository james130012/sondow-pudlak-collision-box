import integration.FoundationCompactNumericListedDirectFormulaSetChecks

/-!
# Bounded append graph for direct natural-number lists

The list header stores the resulting count.  The two source bodies are copied
bit for bit into consecutive target body intervals.  Under valid direct list
layouts this Delta-zero relation is exactly `target = left ++ right`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListAppendSlices

open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectArithmeticPrimitives

def CompactAdditiveNatListAppendSlices
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat) : Prop :=
  targetCount = leftCount + rightCount ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (leftStart + 1) leftFinish
      (targetStart + 1) (targetStart + 1 + leftCount) ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (rightStart + 1) rightFinish
      (targetStart + 1 + leftCount) targetFinish

def compactAdditiveNatListAppendSlicesDef :
    𝚺₀.Semisentence 12 := .mkSigma
  “tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount.
    targetCount = leftCount + rightCount ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        (leftStart + 1) leftFinish
        (targetStart + 1) (targetStart + 1 + leftCount) ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        (rightStart + 1) rightFinish
        (targetStart + 1 + leftCount) targetFinish”

@[simp] theorem compactAdditiveNatListAppendSlicesDef_spec
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat) :
    compactAdditiveNatListAppendSlicesDef.val.Evalb
        ![tokenTable, width, tokenCount,
          leftStart, leftFinish, leftCount,
          rightStart, rightFinish, rightCount,
          targetStart, targetFinish, targetCount] ↔
      CompactAdditiveNatListAppendSlices tokenTable width tokenCount
        leftStart leftFinish leftCount
        rightStart rightFinish rightCount
        targetStart targetFinish targetCount := by
  have hleftSlices :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount,
                leftStart, leftFinish, leftCount,
                rightStart, rightFinish, rightCount,
                targetStart, targetFinish, targetCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2,
              ‘(#3 + 1)’, #4, ‘(#9 + 1)’, ‘((#9 + 1) + #5)’])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          (leftStart + 1) leftFinish
          (targetStart + 1) (targetStart + 1 + leftCount) := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount,
              leftStart, leftFinish, leftCount,
              rightStart, rightFinish, rightCount,
              targetStart, targetFinish, targetCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2,
            ‘(#3 + 1)’, #4, ‘(#9 + 1)’, ‘((#9 + 1) + #5)’]) =
          ![tokenTable, width, tokenCount,
            leftStart + 1, leftFinish,
            targetStart + 1, targetStart + 1 + leftCount] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
        (leftStart + 1) leftFinish
        (targetStart + 1) (targetStart + 1 + leftCount)
  have hrightSlices :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount,
                leftStart, leftFinish, leftCount,
                rightStart, rightFinish, rightCount,
                targetStart, targetFinish, targetCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2,
              ‘(#6 + 1)’, #7, ‘((#9 + 1) + #5)’, #10])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          (rightStart + 1) rightFinish
          (targetStart + 1 + leftCount) targetFinish := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount,
              leftStart, leftFinish, leftCount,
              rightStart, rightFinish, rightCount,
              targetStart, targetFinish, targetCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 12), #1, #2,
            ‘(#6 + 1)’, #7, ‘((#9 + 1) + #5)’, #10]) =
          ![tokenTable, width, tokenCount,
            rightStart + 1, rightFinish,
            targetStart + 1 + leftCount, targetFinish] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
        (rightStart + 1) rightFinish
        (targetStart + 1 + leftCount) targetFinish
  simp [compactAdditiveNatListAppendSlicesDef,
    CompactAdditiveNatListAppendSlices, hleftSlices, hrightSlices]

theorem compactAdditiveNatListAppendSlicesDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListAppendSlicesDef.val := by
  simp [compactAdditiveNatListAppendSlicesDef]

theorem CompactFixedWidthTokenSlicesEq.bodyValue_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish offset : Nat}
    {sourceValue targetValue : Nat}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish)
    (hoffset : offset < sourceFinish - sourceStart)
    (hsource : CompactFixedWidthEntry tokenTable width
      (sourceStart + offset) sourceValue)
    (htarget : CompactFixedWidthEntry tokenTable width
      (targetStart + offset) targetValue) :
    sourceValue = targetValue :=
  CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
    heq hoffset hsource htarget

theorem CompactAdditiveNatListDirectLayout.bodySlicesEq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish targetOffset : Nat}
    {source target : List Nat}
    (hsource : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish source)
    (htarget : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount targetStart targetFinish target)
    (hfit : targetOffset + source.length <= target.length)
    (hvalues : forall index, index < source.length ->
      source.getI index = target.getI (targetOffset + index)) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (sourceStart + 1) sourceFinish
      (targetStart + 1 + targetOffset)
      (targetStart + 1 + targetOffset + source.length) := by
  have hsourceFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hsource
  have htargetFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq htarget
  have hsourceSlice :=
    CompactAdditiveNatListDirectLayout.toSlice hsource
  have htargetSlice :=
    CompactAdditiveNatListDirectLayout.toSlice htarget
  have hsourceBound : sourceFinish <= tokenCount := by
    rcases hsourceSlice with
      ⟨bodyStart, _hbodyStart, hheader, hfinish⟩
    rw [hfinish]
    exact hheader.2
  have htargetBound :
      targetStart + 1 + targetOffset + source.length <= tokenCount := by
    have hfull : targetFinish <= tokenCount := by
      rcases htargetSlice with
        ⟨bodyStart, _hbodyStart, hheader, hfinish⟩
      rw [hfinish]
      exact hheader.2
    omega
  refine ⟨source.length, ?_, ?_, rfl,
    hsourceBound, htargetBound, ?_⟩
  · omega
  · omega
  · intro offset hoffset bitIndex hbitIndex
    have htargetIndex : targetOffset + offset < target.length := by omega
    have hsourceEntry :=
      CompactAdditiveNatListDirectLayout.valueEntry
        hsource offset hoffset
    have htargetEntry :=
      CompactAdditiveNatListDirectLayout.valueEntry
        htarget (targetOffset + offset) htargetIndex
    have hvalue := hvalues offset hoffset
    rw [hvalue] at hsourceEntry
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (hsourceEntry.2 bitIndex hbitIndex).trans
        (htargetEntry.2 bitIndex hbitIndex).symm

theorem compactAdditiveNatListAppendSlices_iff_append
    {tokenTable width tokenCount
      leftStart leftFinish rightStart rightFinish
      targetStart targetFinish : Nat}
    {left right target : List Nat}
    (hleft : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      leftStart leftFinish left)
    (hright : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      rightStart rightFinish right)
    (htarget : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      targetStart targetFinish target) :
    CompactAdditiveNatListAppendSlices tokenTable width tokenCount
        leftStart leftFinish left.length
        rightStart rightFinish right.length
        targetStart targetFinish target.length ↔
      target = left ++ right := by
  constructor
  · rintro ⟨hcount, hleftSlices, hrightSlices⟩
    have hleftFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hleft
    have hrightFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hright
    apply List.ext_getElem
    · simpa using hcount
    · intro index htargetIndex happendIndex
      by_cases hindex : index < left.length
      · have hleftEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            hleft index hindex
        have htargetEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            htarget index (by omega)
        have hvalue := CompactFixedWidthTokenSlicesEq.bodyValue_eq
          (sourceStart := leftStart + 1)
          (sourceFinish := leftFinish)
          (targetStart := targetStart + 1)
          (targetFinish := targetStart + 1 + left.length)
          (offset := index)
          hleftSlices (by omega) (by simpa [Nat.add_assoc] using hleftEntry)
            (by simpa [Nat.add_assoc] using htargetEntry)
        rw [List.getI_eq_getElem left hindex] at hvalue
        rw [List.getI_eq_getElem target htargetIndex] at hvalue
        simpa [List.getElem_append, hindex] using hvalue.symm
      · have hrightIndex : index - left.length < right.length := by omega
        have hrightEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            hright (index - left.length) hrightIndex
        have htargetEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            htarget index (by omega)
        have hvalue := CompactFixedWidthTokenSlicesEq.bodyValue_eq
          (sourceStart := rightStart + 1)
          (sourceFinish := rightFinish)
          (targetStart := targetStart + 1 + left.length)
          (targetFinish := targetFinish)
          (offset := index - left.length)
          hrightSlices (by omega)
            (by simpa [Nat.add_assoc] using hrightEntry)
            (by
              have hindexEq : left.length + (index - left.length) = index := by
                omega
              simpa [Nat.add_assoc, hindexEq] using htargetEntry)
        rw [List.getI_eq_getElem right hrightIndex] at hvalue
        rw [List.getI_eq_getElem target htargetIndex] at hvalue
        have hleftLe : left.length <= index := Nat.le_of_not_gt hindex
        simpa [List.getElem_append, hindex, hleftLe] using hvalue.symm
  · intro htargetEq
    have hcount : target.length = left.length + right.length := by
      simp [htargetEq]
    have hleftSlices :=
      CompactAdditiveNatListDirectLayout.bodySlicesEq
        (targetOffset := 0) hleft htarget (by simp [htargetEq]) (by
          intro index hindex
          rw [htargetEq]
          rw [List.getI_eq_getElem left hindex]
          rw [List.getI_eq_getElem (left ++ right) (by simp; omega)]
          simp [List.getElem_append, hindex])
    have hrightSlicesRaw :=
      CompactAdditiveNatListDirectLayout.bodySlicesEq
        (targetOffset := left.length) hright htarget
          (by simp [htargetEq]) (by
          intro index hindex
          rw [htargetEq]
          rw [List.getI_eq_getElem right hindex]
          rw [List.getI_eq_getElem (left ++ right) (by simp; omega)]
          simp [List.getElem_append, hindex])
    have htargetFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq htarget
    have hrightSlices : CompactFixedWidthTokenSlicesEq
        tokenTable width tokenCount
        (rightStart + 1) rightFinish
        (targetStart + 1 + left.length) targetFinish := by
      convert hrightSlicesRaw using 1 <;> omega
    exact ⟨hcount, hleftSlices, hrightSlices⟩

#print axioms compactAdditiveNatListAppendSlicesDef_spec
#print axioms compactAdditiveNatListAppendSlicesDef_sigmaZero
#print axioms compactAdditiveNatListAppendSlices_iff_append

end FoundationCompactNumericListedDirectNatListAppendSlices
