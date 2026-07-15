import integration.FoundationCompactNumericListedDirectAtomicRowEquality

/-!
# Direct bounded equality of arbitrary token slices

Two slices are equal when they have the same length and every fixed-width bit
in every token row agrees.  This relation is independent of the typed value
stored in the slice and can therefore preserve complete verifier payloads.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTokenSliceEquality

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse

def CompactFixedWidthTokenSlicesEq
    (tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat) : Prop :=
  ∃ count, count ≤ tokenCount ∧
    sourceFinish = sourceStart + count ∧
    targetFinish = targetStart + count ∧
    sourceFinish ≤ tokenCount ∧
    targetFinish ≤ tokenCount ∧
    ∀ offset < count,
      ∀ bitIndex < width,
        tokenTable.testBit ((sourceStart + offset) * width + bitIndex) =
          tokenTable.testBit ((targetStart + offset) * width + bitIndex)

def compactFixedWidthTokenSlicesEqDef :
    𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish.
    ∃ count <⁺ tokenCount,
      sourceFinish = sourceStart + count ∧
      targetFinish = targetStart + count ∧
      sourceFinish ≤ tokenCount ∧
      targetFinish ≤ tokenCount ∧
      ∀ offset < count,
        ∀ bitIndex < width,
          (((sourceStart + offset) * width + bitIndex) ∈ tokenTable ↔
            ((targetStart + offset) * width + bitIndex) ∈ tokenTable)”

@[simp] theorem compactFixedWidthTokenSlicesEqDef_spec
    (tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat) :
    compactFixedWidthTokenSlicesEqDef.val.Evalb
        ![tokenTable, width, tokenCount,
          sourceStart, sourceFinish, targetStart, targetFinish] ↔
      CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
        sourceStart sourceFinish targetStart targetFinish := by
  simp [compactFixedWidthTokenSlicesEqDef,
    CompactFixedWidthTokenSlicesEq, arithmeticMem_nat_iff_testBit]

theorem compactFixedWidthTokenSlicesEqDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFixedWidthTokenSlicesEqDef.val := by
  simp [compactFixedWidthTokenSlicesEqDef]

theorem CompactFixedWidthTokenSlicesEq.refl
    {tokenTable width tokenCount start finish : Nat}
    (hstart : start ≤ finish) (hfinish : finish ≤ tokenCount) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      start finish start finish := by
  refine ⟨finish - start, ?_, ?_, ?_, hfinish, hfinish, ?_⟩
  · omega
  · omega
  · omega
  · intro offset _hoffset bitIndex _hbitIndex
    rfl

theorem CompactFixedWidthTokenSlicesEq.symm
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      targetStart targetFinish sourceStart sourceFinish := by
  rcases heq with
    ⟨count, hcount, hsource, htarget,
      hsourceFinish, htargetFinish, hbits⟩
  exact ⟨count, hcount, htarget, hsource,
    htargetFinish, hsourceFinish,
    fun offset hoffset bitIndex hbitIndex =>
      (hbits offset hoffset bitIndex hbitIndex).symm⟩

theorem CompactFixedWidthTokenSlicesEq.subslice
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish : Nat}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish)
    (offset count : Nat)
    (hwithin : offset + count ≤ sourceFinish - sourceStart) :
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      (sourceStart + offset) (sourceStart + offset + count)
      (targetStart + offset) (targetStart + offset + count) := by
  rcases heq with
    ⟨totalCount, htotalCount, hsource, htarget,
      hsourceBound, htargetBound, hbits⟩
  have hsourceCount : sourceFinish - sourceStart = totalCount := by
    omega
  have htargetCount : targetFinish - targetStart = totalCount := by
    omega
  have hcount : count ≤ tokenCount := by
    omega
  refine ⟨count, hcount, rfl, rfl, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro innerOffset hinnerOffset bitIndex hbitIndex
    have hoverall : offset + innerOffset < totalCount := by omega
    simpa [Nat.add_assoc] using
      hbits (offset + innerOffset) hoverall bitIndex hbitIndex

theorem CompactFixedWidthTokenSlicesEq.entryValue_eq
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish count offset
      sourceValue targetValue : Nat}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish)
    (hsourceFinish : sourceFinish = sourceStart + count)
    (htargetFinish : targetFinish = targetStart + count)
    (hoffset : offset < count)
    (hsource : CompactFixedWidthEntry tokenTable width
      (sourceStart + offset) sourceValue)
    (htarget : CompactFixedWidthEntry tokenTable width
      (targetStart + offset) targetValue) :
    sourceValue = targetValue := by
  rcases heq with
    ⟨storedCount, _hstoredCount, hsourceStored, htargetStored,
      _hsourceBound, _htargetBound, hbits⟩
  have hcount : storedCount = count := by omega
  subst storedCount
  apply Nat.eq_of_testBit_eq
  intro bitIndex
  by_cases hbit : bitIndex < width
  · exact (hsource.2 bitIndex hbit).symm.trans
      ((hbits offset hoffset bitIndex hbit).trans
        (htarget.2 bitIndex hbit))
  · have hwidth : width ≤ bitIndex := Nat.le_of_not_gt hbit
    have hsourceLt : sourceValue < 2 ^ bitIndex :=
      Nat.size_le.mp (hsource.1.trans hwidth)
    have htargetLt : targetValue < 2 ^ bitIndex :=
      Nat.size_le.mp (htarget.1.trans hwidth)
    rw [Nat.testBit_eq_false_of_lt hsourceLt,
      Nat.testBit_eq_false_of_lt htargetLt]

theorem CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
    {tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish offset
      sourceValue targetValue : Nat}
    (heq : CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish)
    (hoffset : offset < sourceFinish - sourceStart)
    (hsource : CompactFixedWidthEntry tokenTable width
      (sourceStart + offset) sourceValue)
    (htarget : CompactFixedWidthEntry tokenTable width
      (targetStart + offset) targetValue) :
    sourceValue = targetValue := by
  rcases heq with
    ⟨count, hcount, hsourceFinish, htargetFinish,
      hsourceBound, htargetBound, hbits⟩
  have hcountEq : count = sourceFinish - sourceStart := by omega
  subst count
  exact CompactFixedWidthTokenSlicesEq.entryValue_eq
    ⟨sourceFinish - sourceStart, hcount, hsourceFinish, htargetFinish,
      hsourceBound, htargetBound, hbits⟩
    hsourceFinish htargetFinish hoffset hsource htarget

theorem compactFixedWidthTokenSlicesEq_tableCode
    (tokens : List Nat) (width sourceStart targetStart count : Nat)
    (hwidth : ∀ token ∈ tokens, Nat.size token ≤ width)
    (hsource : sourceStart + count ≤ tokens.length)
    (htarget : targetStart + count ≤ tokens.length)
    (hvalues : ∀ offset < count,
      tokens.getI (sourceStart + offset) =
        tokens.getI (targetStart + offset)) :
    CompactFixedWidthTokenSlicesEq
      (compactFixedWidthTableCode width tokens) width tokens.length
      sourceStart (sourceStart + count)
      targetStart (targetStart + count) := by
  refine ⟨count, ?_, rfl, rfl, hsource, htarget, ?_⟩
  · omega
  · intro offset hoffset bitIndex hbitIndex
    have hsourceIndex : sourceStart + offset < tokens.length := by omega
    have htargetIndex : targetStart + offset < tokens.length := by omega
    have hsourceEntry := compactFixedWidthTableCode_entry width tokens
      (sourceStart + offset) hsourceIndex hwidth
    have htargetEntry := compactFixedWidthTableCode_entry width tokens
      (targetStart + offset) htargetIndex hwidth
    exact (hsourceEntry.2 bitIndex hbitIndex).trans
      ((congrArg (fun value => value.testBit bitIndex)
        (hvalues offset hoffset)).trans
        (htargetEntry.2 bitIndex hbitIndex).symm)

#print axioms compactFixedWidthTokenSlicesEqDef_spec
#print axioms compactFixedWidthTokenSlicesEqDef_sigmaZero
#print axioms CompactFixedWidthTokenSlicesEq.refl
#print axioms CompactFixedWidthTokenSlicesEq.symm
#print axioms CompactFixedWidthTokenSlicesEq.subslice
#print axioms CompactFixedWidthTokenSlicesEq.entryValue_eq
#print axioms CompactFixedWidthTokenSlicesEq.entryValue_eq_at_offset
#print axioms compactFixedWidthTokenSlicesEq_tableCode

end FoundationCompactNumericListedDirectTokenSliceEquality
