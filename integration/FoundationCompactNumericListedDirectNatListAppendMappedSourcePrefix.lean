import integration.FoundationCompactNumericListedDirectNatListAppendTwoValues

/-!
# Bounded append of a source prefix with a replaced head

This relation preserves an emitted-output list, appends a nonempty prefix of
an encoded source list, and replaces only the first appended value.  It is the
direct arithmetic update needed by the formula-negation transform.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefix

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAtRows

def CompactAdditiveNatListAppendMappedSourcePrefix
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat) : Prop :=
  1 ≤ prefixCount ∧
    prefixCount ≤ sourceCount ∧
    sourceStart + 1 + prefixCount ≤ sourceFinish ∧
    targetFinish = targetStart + 1 + targetCount ∧
    targetCount = leftCount + prefixCount ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (leftStart + 1) leftFinish
      (targetStart + 1) (targetStart + 1 + leftCount) ∧
    CompactAdditiveNatListAtRows tokenTable width tokenCount
      targetBoundary targetCount leftCount mappedHead ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (sourceStart + 2) (sourceStart + 1 + prefixCount)
      (targetStart + 2 + leftCount) targetFinish

def compactAdditiveNatListAppendMappedSourcePrefixDef :
    𝚺₀.Semisentence 15 := .mkSigma
  “tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount mappedHead.
    1 ≤ prefixCount ∧
    prefixCount ≤ sourceCount ∧
    sourceStart + 1 + prefixCount ≤ sourceFinish ∧
    targetFinish = targetStart + 1 + targetCount ∧
    targetCount = leftCount + prefixCount ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        (leftStart + 1) leftFinish
        (targetStart + 1) (targetStart + 1 + leftCount) ∧
    !(compactAdditiveNatListAtRowsDef)
      tokenTable width tokenCount targetBoundary targetCount
        leftCount mappedHead ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
        (sourceStart + 2) (sourceStart + 1 + prefixCount)
        (targetStart + 2 + leftCount) targetFinish”

@[simp] theorem compactAdditiveNatListAppendMappedSourcePrefixDef_spec
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat) :
    compactAdditiveNatListAppendMappedSourcePrefixDef.val.Evalb
        ![tokenTable, width, tokenCount,
          leftStart, leftFinish, leftCount,
          sourceStart, sourceFinish, sourceCount, prefixCount,
          targetStart, targetFinish, targetBoundary, targetCount,
          mappedHead] ↔
      CompactAdditiveNatListAppendMappedSourcePrefix
        tokenTable width tokenCount
        leftStart leftFinish leftCount
        sourceStart sourceFinish sourceCount prefixCount
        targetStart targetFinish targetBoundary targetCount mappedHead := by
  let env : Fin 15 → Nat :=
    ![tokenTable, width, tokenCount,
      leftStart, leftFinish, leftCount,
      sourceStart, sourceFinish, sourceCount, prefixCount,
      targetStart, targetFinish, targetBoundary, targetCount, mappedHead]
  change compactAdditiveNatListAppendMappedSourcePrefixDef.val.Evalb env ↔ _
  have hleftEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2,
          ‘(#3 + 1)’, #4, ‘(#10 + 1)’, ‘((#10 + 1) + #5)’]) =
        ![tokenTable, width, tokenCount,
          leftStart + 1, leftFinish,
          targetStart + 1, targetStart + 1 + leftCount] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have hheadEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2,
          #12, #13, #5, #14]) =
        ![tokenTable, width, tokenCount,
          targetBoundary, targetCount, leftCount, mappedHead] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htailEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2,
          ‘(#6 + 2)’, ‘((#6 + 1) + #9)’,
          ‘((#10 + 2) + #5)’, #11]) =
        ![tokenTable, width, tokenCount,
          sourceStart + 2, sourceStart + 1 + prefixCount,
          targetStart + 2 + leftCount, targetFinish] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have hleftSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2,
              ‘(#3 + 1)’, #4, ‘(#10 + 1)’, ‘((#10 + 1) + #5)’])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          (leftStart + 1) leftFinish
          (targetStart + 1) (targetStart + 1 + leftCount) := by
    rw [hleftEnv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
        (leftStart + 1) leftFinish
        (targetStart + 1) (targetStart + 1 + leftCount)
  have hheadSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2,
              #12, #13, #5, #14])
          Empty.elim) compactAdditiveNatListAtRowsDef.val ↔
        CompactAdditiveNatListAtRows tokenTable width tokenCount
          targetBoundary targetCount leftCount mappedHead := by
    rw [hheadEnv]
    exact compactAdditiveNatListAtRowsDef_spec
      tokenTable width tokenCount targetBoundary targetCount
        leftCount mappedHead
  have htailSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 15), #1, #2,
              ‘(#6 + 2)’, ‘((#6 + 1) + #9)’,
              ‘((#10 + 2) + #5)’, #11])
          Empty.elim) compactFixedWidthTokenSlicesEqDef.val ↔
        CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          (sourceStart + 2) (sourceStart + 1 + prefixCount)
          (targetStart + 2 + leftCount) targetFinish := by
    rw [htailEnv]
    exact compactFixedWidthTokenSlicesEqDef_spec
      tokenTable width tokenCount
        (sourceStart + 2) (sourceStart + 1 + prefixCount)
        (targetStart + 2 + leftCount) targetFinish
  simp [compactAdditiveNatListAppendMappedSourcePrefixDef,
    CompactAdditiveNatListAppendMappedSourcePrefix,
    env, hleftSpec, hheadSpec, htailSpec]

theorem compactAdditiveNatListAppendMappedSourcePrefixDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveNatListAppendMappedSourcePrefixDef.val := by
  simp [compactAdditiveNatListAppendMappedSourcePrefixDef]

private theorem mappedPrefix_length
    (source : List Nat) (prefixCount mappedHead : Nat)
    (hpositive : 1 ≤ prefixCount)
    (hprefix : prefixCount ≤ source.length) :
    (mappedHead :: (source.take prefixCount).drop 1).length = prefixCount := by
  rw [List.length_cons, List.length_drop, List.length_take,
    Nat.min_eq_left hprefix]
  omega

private theorem mappedPrefix_getI_zero
    (source : List Nat) (prefixCount mappedHead : Nat) :
    (mappedHead :: (source.take prefixCount).drop 1).getI 0 = mappedHead := by
  simp

private theorem mappedPrefix_getI_succ
    (source : List Nat) (prefixCount mappedHead offset : Nat)
    (hoffset : offset + 1 < prefixCount)
    (hsource : prefixCount ≤ source.length) :
    (mappedHead :: (source.take prefixCount).drop 1).getI (offset + 1) =
      source.getI (offset + 1) := by
  have hsourceIndex : offset + 1 < source.length := by omega
  have hmappedIndex : offset + 1 <
      (mappedHead :: (source.take prefixCount).drop 1).length := by
    have hpositive : 1 ≤ prefixCount := by omega
    rw [mappedPrefix_length source prefixCount mappedHead hpositive hsource]
    omega
  rw [List.getI_eq_getElem _ hmappedIndex]
  rw [List.getI_eq_getElem source hsourceIndex]
  simp [List.getElem_drop, List.getElem_take]

theorem compactAdditiveNatListAppendMappedSourcePrefix_iff
    {tokenTable width tokenCount
      leftStart leftFinish sourceStart sourceFinish
      targetStart targetFinish targetBoundary prefixCount mappedHead : Nat}
    {left source target : List Nat}
    (hleft : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      leftStart leftFinish left)
    (hsource : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      sourceStart sourceFinish source)
    (htarget : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      targetStart targetFinish target)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        targetBoundary target) :
    CompactAdditiveNatListAppendMappedSourcePrefix
        tokenTable width tokenCount
        leftStart leftFinish left.length
        sourceStart sourceFinish source.length prefixCount
        targetStart targetFinish targetBoundary target.length mappedHead ↔
      1 ≤ prefixCount ∧
        prefixCount ≤ source.length ∧
        target = left ++
          (mappedHead :: (source.take prefixCount).drop 1) := by
  constructor
  · rintro ⟨hpositive, hprefix, _hsourceWithin,
      _htargetFinish, hcount, hleftSlices, hheadRows, htailSlices⟩
    refine ⟨hpositive, hprefix, ?_⟩
    have hleftFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hleft
    have hheadValue :=
      (compactAdditiveNatListAtRows_iff_getI
        htargetRows left.length mappedHead).mp hheadRows
    apply List.ext_getElem
    · rw [List.length_append,
        mappedPrefix_length source prefixCount mappedHead hpositive hprefix]
      exact hcount
    · intro index htargetIndex happendIndex
      by_cases hindex : index < left.length
      · have hleftEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry hleft index hindex
        have htargetEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            htarget index htargetIndex
        have hvalue := CompactFixedWidthTokenSlicesEq.bodyValue_eq
          (sourceStart := leftStart + 1)
          (sourceFinish := leftFinish)
          (targetStart := targetStart + 1)
          (targetFinish := targetStart + 1 + left.length)
          (offset := index) hleftSlices (by omega)
            (by simpa [Nat.add_assoc] using hleftEntry)
            (by simpa [Nat.add_assoc] using htargetEntry)
        rw [List.getI_eq_getElem left hindex] at hvalue
        rw [List.getI_eq_getElem target htargetIndex] at hvalue
        simpa [List.getElem_append, hindex] using hvalue.symm
      · have hleftLe : left.length ≤ index := Nat.le_of_not_gt hindex
        let offset := index - left.length
        have hindexEq : index = left.length + offset := by
          dsimp [offset]
          omega
        have hoffset : offset < prefixCount := by
          dsimp [offset]
          omega
        by_cases hoffsetZero : offset = 0
        · have hindexStart : index = left.length := by omega
          have hheadEq := hheadValue.2
          have htargetStartIndex : left.length < target.length := by omega
          rw [List.getI_eq_getElem target htargetStartIndex] at hheadEq
          simpa [hindexStart, mappedPrefix_getI_zero] using hheadEq
        · have hoffsetPositive : 1 ≤ offset := Nat.one_le_iff_ne_zero.mpr hoffsetZero
          let tailOffset := offset - 1
          have hoffsetEq : offset = tailOffset + 1 := by
            dsimp [tailOffset]
            omega
          have hsourceIndex : offset < source.length := by omega
          have hsourceEntry :=
            CompactAdditiveNatListDirectLayout.valueEntry
              hsource offset hsourceIndex
          have htargetEntry :=
            CompactAdditiveNatListDirectLayout.valueEntry
              htarget index htargetIndex
          have hvalue := CompactFixedWidthTokenSlicesEq.bodyValue_eq
            (sourceStart := sourceStart + 2)
            (sourceFinish := sourceStart + 1 + prefixCount)
            (targetStart := targetStart + 2 + left.length)
            (targetFinish := targetFinish)
            (offset := tailOffset) htailSlices (by
              dsimp [tailOffset]
              omega)
              (by
                convert hsourceEntry using 1 <;> omega)
              (by
                convert htargetEntry using 1 <;> omega)
          rw [List.getI_eq_getElem source hsourceIndex] at hvalue
          rw [List.getI_eq_getElem target htargetIndex] at hvalue
          have hmappedValue := mappedPrefix_getI_succ
            source prefixCount mappedHead tailOffset (by omega) hprefix
          rw [show tailOffset + 1 = offset by omega] at hmappedValue
          rw [List.getI_eq_getElem source hsourceIndex] at hmappedValue
          have hmappedIndex : offset <
              (mappedHead :: (source.take prefixCount).drop 1).length := by
            rw [mappedPrefix_length source prefixCount mappedHead
              hpositive hprefix]
            exact hoffset
          rw [List.getI_eq_getElem _ hmappedIndex] at hmappedValue
          simpa [List.getElem_append, hindex, hleftLe,
            hindexEq] using hvalue.symm.trans hmappedValue.symm
  · rintro ⟨hpositive, hprefix, htargetEq⟩
    let mappedPrefix := mappedHead :: (source.take prefixCount).drop 1
    have hmappedLength : mappedPrefix.length = prefixCount := by
      exact mappedPrefix_length source prefixCount mappedHead
        hpositive hprefix
    have hleftSlices :=
      CompactAdditiveNatListDirectLayout.bodySlicesEq
        (targetOffset := 0) hleft htarget
        (by simp [htargetEq, hmappedLength]) (by
          intro index hindex
          rw [htargetEq]
          rw [List.getI_eq_getElem left hindex]
          rw [List.getI_eq_getElem (left ++ mappedPrefix) (by simp; omega)]
          simp [List.getElem_append, hindex])
    have hheadRows : CompactAdditiveNatListAtRows
        tokenTable width tokenCount targetBoundary target.length
          left.length mappedHead :=
      (compactAdditiveNatListAtRows_iff_getI
        htargetRows left.length mappedHead).mpr (by
          rw [htargetEq]
          refine ⟨by simp [hmappedLength], ?_⟩
          change (left ++ mappedPrefix).getI left.length = mappedHead
          have happend := List.getI_append_right
            left mappedPrefix left.length (by omega)
          simpa [mappedPrefix, mappedPrefix_getI_zero] using happend)
    have hsourceFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq hsource
    have htargetFinish :=
      CompactAdditiveNatListDirectLayout.finish_eq htarget
    have htargetLength : target.length = left.length + prefixCount := by
      rw [htargetEq, List.length_append, hmappedLength]
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
    have htailSlices : CompactFixedWidthTokenSlicesEq
        tokenTable width tokenCount
        (sourceStart + 2) (sourceStart + 1 + prefixCount)
        (targetStart + 2 + left.length) targetFinish := by
      refine ⟨prefixCount - 1, ?_, ?_, ?_, ?_, htargetBound, ?_⟩
      · omega
      · omega
      · omega
      · omega
      · intro offset hoffset bitIndex hbitIndex
        have hsourceIndex : offset + 1 < source.length := by omega
        have htargetIndex : left.length + (offset + 1) < target.length := by
          rw [htargetEq]
          simp [hmappedLength]
          omega
        have hsourceEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            hsource (offset + 1) hsourceIndex
        have htargetEntry :=
          CompactAdditiveNatListDirectLayout.valueEntry
            htarget (left.length + (offset + 1)) htargetIndex
        have hmappedValue := mappedPrefix_getI_succ
          source prefixCount mappedHead offset (by omega) hprefix
        have htargetValue : source.getI (offset + 1) =
            target.getI (left.length + (offset + 1)) := by
          rw [htargetEq]
          change source.getI (offset + 1) =
            (left ++ mappedPrefix).getI (left.length + (offset + 1))
          have happend := List.getI_append_right left mappedPrefix
            (left.length + (offset + 1)) (by omega)
          rw [happend]
          simpa [mappedPrefix] using hmappedValue.symm
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (hsourceEntry.2 bitIndex hbitIndex).trans
            ((congrArg (fun value => value.testBit bitIndex)
              htargetValue).trans
                (htargetEntry.2 bitIndex hbitIndex).symm)
    exact ⟨hpositive, hprefix, by omega, htargetFinish,
      htargetLength,
      hleftSlices, hheadRows, htailSlices⟩

#print axioms compactAdditiveNatListAppendMappedSourcePrefixDef_spec
#print axioms compactAdditiveNatListAppendMappedSourcePrefixDef_sigmaZero
#print axioms compactAdditiveNatListAppendMappedSourcePrefix_iff

end FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefix
