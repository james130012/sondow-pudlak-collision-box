import integration.FoundationCompactNumericListedDirectNatListAppendSlices

/-!
# Bounded append of a directly encoded source prefix

The target list first copies an already encoded left list and then copies a
prefix of a second encoded natural-number list.  This is the common output
update used by syntax-directed formula transformations: parser steps consume
a prefix of their remaining input and append that prefix to emitted output.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListAppendSourcePrefix

open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListAppendSlices

def CompactAdditiveNatListAppendSourcePrefix
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat) : Prop :=
  prefixCount ≤ sourceCount ∧
    sourceStart + 1 + prefixCount ≤ sourceFinish ∧
    targetCount = leftCount + prefixCount ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (leftStart + 1) leftFinish
      (targetStart + 1) (targetStart + 1 + leftCount) ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (sourceStart + 1) (sourceStart + 1 + prefixCount)
      (targetStart + 1 + leftCount) targetFinish

def compactAdditiveNatListAppendSourcePrefixDef :
    𝚺₀.Semisentence 13 := .mkSigma
  “tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount.
    prefixCount ≤ sourceCount ∧
    sourceStart + 1 + prefixCount ≤ sourceFinish ∧
    targetCount = leftCount + prefixCount ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        (leftStart + 1) leftFinish
        (targetStart + 1) (targetStart + 1 + leftCount) ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        (sourceStart + 1) (sourceStart + 1 + prefixCount)
        (targetStart + 1 + leftCount) targetFinish”

@[simp] theorem compactAdditiveNatListAppendSourcePrefixDef_spec
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat) :
    compactAdditiveNatListAppendSourcePrefixDef.val.Evalb
        ![tokenTable, width, tokenCount,
          leftStart, leftFinish, leftCount,
          sourceStart, sourceFinish, sourceCount, prefixCount,
          targetStart, targetFinish, targetCount] ↔
      CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
        leftStart leftFinish leftCount
        sourceStart sourceFinish sourceCount prefixCount
        targetStart targetFinish targetCount := by
  have hleftSlices :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount,
                leftStart, leftFinish, leftCount,
                sourceStart, sourceFinish, sourceCount, prefixCount,
                targetStart, targetFinish, targetCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2,
              ‘(#3 + 1)’, #4, ‘(#10 + 1)’, ‘((#10 + 1) + #5)’])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          (leftStart + 1) leftFinish
          (targetStart + 1) (targetStart + 1 + leftCount) := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount,
              leftStart, leftFinish, leftCount,
              sourceStart, sourceFinish, sourceCount, prefixCount,
              targetStart, targetFinish, targetCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2,
            ‘(#3 + 1)’, #4, ‘(#10 + 1)’, ‘((#10 + 1) + #5)’]) =
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
  have hsourceSlices :
      (Semiformula.Eval
          (Semiterm.val
              ![tokenTable, width, tokenCount,
                leftStart, leftFinish, leftCount,
                sourceStart, sourceFinish, sourceCount, prefixCount,
                targetStart, targetFinish, targetCount]
              Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2,
              ‘(#6 + 1)’, ‘((#6 + 1) + #9)’,
              ‘((#10 + 1) + #5)’, #11])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          (sourceStart + 1) (sourceStart + 1 + prefixCount)
          (targetStart + 1 + leftCount) targetFinish := by
    have henv :
        (Semiterm.val
            ![tokenTable, width, tokenCount,
              leftStart, leftFinish, leftCount,
              sourceStart, sourceFinish, sourceCount, prefixCount,
              targetStart, targetFinish, targetCount]
            Empty.elim ∘
          ![(#0 : Semiterm ℒₒᵣ Empty 13), #1, #2,
            ‘(#6 + 1)’, ‘((#6 + 1) + #9)’,
            ‘((#10 + 1) + #5)’, #11]) =
          ![tokenTable, width, tokenCount,
            sourceStart + 1, sourceStart + 1 + prefixCount,
            targetStart + 1 + leftCount, targetFinish] := by
      funext coordinate
      fin_cases coordinate <;> simp
    rw [henv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
        (sourceStart + 1) (sourceStart + 1 + prefixCount)
        (targetStart + 1 + leftCount) targetFinish
  simp [compactAdditiveNatListAppendSourcePrefixDef,
    CompactAdditiveNatListAppendSourcePrefix,
    hleftSlices, hsourceSlices]

theorem compactAdditiveNatListAppendSourcePrefixDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListAppendSourcePrefixDef.val := by
  simp [compactAdditiveNatListAppendSourcePrefixDef]

theorem compactAdditiveNatListAppendSourcePrefix_iff
    {tokenTable width tokenCount
      leftStart leftFinish sourceStart sourceFinish
      targetStart targetFinish prefixCount : Nat}
    {left source target : List Nat}
    (hleft : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount leftStart leftFinish left)
    (hsource : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount sourceStart sourceFinish source)
    (htarget : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount targetStart targetFinish target) :
    CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
        leftStart leftFinish left.length
        sourceStart sourceFinish source.length prefixCount
        targetStart targetFinish target.length ↔
      prefixCount ≤ source.length ∧
        target = left ++ source.take prefixCount := by
  constructor
  · rintro ⟨hprefix, _hsourceWithin, hcount,
      hleftSlices, hsourceSlices⟩
    have hleftFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hleft
    refine ⟨hprefix, ?_⟩
    apply List.ext_getElem
    · simpa [List.length_take, hprefix] using hcount
    · intro index htargetIndex happendIndex
      by_cases hindex : index < left.length
      · have hleftEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            hleft index hindex
        have htargetEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            htarget index htargetIndex
        have hvalue := CompactFixedWidthTokenSlicesEq.bodyValue_eq
          (sourceStart := leftStart + 1)
          (sourceFinish := leftFinish)
          (targetStart := targetStart + 1)
          (targetFinish := targetStart + 1 + left.length)
          (offset := index)
          hleftSlices (by omega)
            (by simpa [Nat.add_assoc] using hleftEntry)
            (by simpa [Nat.add_assoc] using htargetEntry)
        rw [List.getI_eq_getElem left hindex] at hvalue
        rw [List.getI_eq_getElem target htargetIndex] at hvalue
        simpa [List.getElem_append, hindex] using hvalue.symm
      · have hleftLe : left.length ≤ index := Nat.le_of_not_gt hindex
        have hsourceIndex : index - left.length < prefixCount := by
          have htargetLength : target.length = left.length + prefixCount :=
            hcount
          omega
        have hsourceFullIndex : index - left.length < source.length := by
          omega
        have hsourceEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            hsource (index - left.length) hsourceFullIndex
        have htargetEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            htarget index htargetIndex
        have hvalue := CompactFixedWidthTokenSlicesEq.bodyValue_eq
          (sourceStart := sourceStart + 1)
          (sourceFinish := sourceStart + 1 + prefixCount)
          (targetStart := targetStart + 1 + left.length)
          (targetFinish := targetFinish)
          (offset := index - left.length)
          hsourceSlices (by omega)
            (by simpa [Nat.add_assoc] using hsourceEntry)
            (by
              have hindexEq : left.length + (index - left.length) = index := by
                omega
              simpa [Nat.add_assoc, hindexEq] using htargetEntry)
        rw [List.getI_eq_getElem source hsourceFullIndex] at hvalue
        rw [List.getI_eq_getElem target htargetIndex] at hvalue
        simpa [List.getElem_append, hindex, hleftLe,
          List.getElem_take] using hvalue.symm
  · rintro ⟨hprefix, htargetEq⟩
    have hsourceFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hsource
    have htargetFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq htarget
    have hcount : target.length = left.length + prefixCount := by
      simp [htargetEq, List.length_take, hprefix]
    have hleftSlices :=
      CompactAdditiveNatListDirectLayout.bodySlicesEq
        (targetOffset := 0) hleft htarget
        (by simp [htargetEq, List.length_take, hprefix]) (by
          intro index hindex
          rw [htargetEq]
          rw [List.getI_eq_getElem left hindex]
          rw [List.getI_eq_getElem
            (left ++ source.take prefixCount) (by simp; omega)]
          simp [List.getElem_append, hindex])
    have hsourceBound : sourceStart + 1 + prefixCount ≤ tokenCount := by
      have hfinishBound : sourceFinish ≤ tokenCount := by
        rcases CompactAdditiveNatListDirectLayout.toSlice hsource with
          ⟨_bodyStart, _hbodyStart, hheader, hfinish⟩
        rw [hfinish]
        exact hheader.2
      omega
    have htargetBound : targetFinish ≤ tokenCount := by
      rcases CompactAdditiveNatListDirectLayout.toSlice htarget with
        ⟨_bodyStart, _hbodyStart, hheader, hfinish⟩
      rw [hfinish]
      exact hheader.2
    have hsourceSlices : CompactFixedWidthTokenSlicesEq
        tokenTable width tokenCount
        (sourceStart + 1) (sourceStart + 1 + prefixCount)
        (targetStart + 1 + left.length) targetFinish := by
      refine ⟨prefixCount, ?_, rfl, ?_, hsourceBound, htargetBound, ?_⟩
      · omega
      · omega
      · intro offset hoffset bitIndex hbitIndex
        have hsourceIndex : offset < source.length := by omega
        have htargetIndex : left.length + offset < target.length := by omega
        have hsourceEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            hsource offset hsourceIndex
        have htargetEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            htarget (left.length + offset) htargetIndex
        have hvalue : source.getI offset =
            target.getI (left.length + offset) := by
          rw [htargetEq]
          rw [List.getI_eq_getElem source hsourceIndex]
          rw [List.getI_eq_getElem
            (left ++ source.take prefixCount) (by simp; omega)]
          simp [List.getElem_append, List.getElem_take, hoffset]
        simpa [Nat.add_assoc] using
          (hsourceEntry.2 bitIndex hbitIndex).trans
            ((congrArg (fun value => value.testBit bitIndex) hvalue).trans
              (htargetEntry.2 bitIndex hbitIndex).symm)
    exact ⟨hprefix, by omega, hcount, hleftSlices, hsourceSlices⟩

#print axioms compactAdditiveNatListAppendSourcePrefixDef_spec
#print axioms compactAdditiveNatListAppendSourcePrefixDef_sigmaZero
#print axioms compactAdditiveNatListAppendSourcePrefix_iff

end FoundationCompactNumericListedDirectNatListAppendSourcePrefix
