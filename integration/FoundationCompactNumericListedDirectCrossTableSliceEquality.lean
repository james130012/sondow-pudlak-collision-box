import integration.FoundationCompactNumericListedDirectVerifierPayloadEquality

/-!
# Exact equality of token slices stored in different tables

Two independently built canonical graphs may use different fixed-width token
tables.  This relation binds one slice from each table by requiring every
corresponding decoded token bit to agree, including the zero extension above
the smaller row width.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCrossTableSliceEquality

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierPayloadEquality

def CompactFixedWidthCrossTableSlicesEq
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    Prop :=
  ∃ count, count ≤ sourceTokenCount ∧ count ≤ targetTokenCount ∧
    sourceFinish = sourceStart + count ∧
    targetFinish = targetStart + count ∧
    sourceFinish ≤ sourceTokenCount ∧
    targetFinish ≤ targetTokenCount ∧
    ∀ offset < count,
      ∀ bitIndex < sourceWidth + targetWidth,
        (bitIndex < sourceWidth ∧
            sourceTable.testBit
              ((sourceStart + offset) * sourceWidth + bitIndex) = true) ↔
          (bitIndex < targetWidth ∧
            targetTable.testBit
              ((targetStart + offset) * targetWidth + bitIndex) = true)

def compactFixedWidthCrossTableSlicesEqDef :
    𝚺₀.Semisentence 10 := .mkSigma
  “sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish.
    ∃ count <⁺ sourceTokenCount,
      count ≤ targetTokenCount ∧
      sourceFinish = sourceStart + count ∧
      targetFinish = targetStart + count ∧
      sourceFinish ≤ sourceTokenCount ∧
      targetFinish ≤ targetTokenCount ∧
      ∀ offset < count,
        ∀ bitIndex < sourceWidth + targetWidth,
          ((bitIndex < sourceWidth ∧
              ((sourceStart + offset) * sourceWidth + bitIndex) ∈
                sourceTable) ↔
            (bitIndex < targetWidth ∧
              ((targetStart + offset) * targetWidth + bitIndex) ∈
                targetTable))”

@[simp] theorem compactFixedWidthCrossTableSlicesEqDef_spec
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    compactFixedWidthCrossTableSlicesEqDef.val.Evalb
        ![sourceTable, sourceWidth, sourceTokenCount, sourceStart, sourceFinish,
          targetTable, targetWidth, targetTokenCount, targetStart,
          targetFinish] ↔
      CompactFixedWidthCrossTableSlicesEq
        sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
        targetTable targetWidth targetTokenCount targetStart targetFinish := by
  simp [compactFixedWidthCrossTableSlicesEqDef,
    CompactFixedWidthCrossTableSlicesEq, arithmeticMem_nat_iff_testBit]

theorem compactFixedWidthCrossTableSlicesEqDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFixedWidthCrossTableSlicesEqDef.val := by
  simp [compactFixedWidthCrossTableSlicesEqDef]

private theorem fixedWidthEntry_cross_true_iff
    {sourceTable sourceWidth sourceIndex
      targetTable targetWidth targetIndex value bitIndex : Nat}
    (hsource : CompactFixedWidthEntry
      sourceTable sourceWidth sourceIndex value)
    (htarget : CompactFixedWidthEntry
      targetTable targetWidth targetIndex value) :
    (bitIndex < sourceWidth ∧
        sourceTable.testBit (sourceIndex * sourceWidth + bitIndex) = true) ↔
      (bitIndex < targetWidth ∧
        targetTable.testBit (targetIndex * targetWidth + bitIndex) = true) := by
  constructor
  · rintro ⟨hsourceWidth, hsourceTrue⟩
    have hvalueTrue : value.testBit bitIndex = true := by
      rw [← hsource.2 bitIndex hsourceWidth]
      exact hsourceTrue
    have htargetWidth : bitIndex < targetWidth := by
      by_contra hnot
      have hvalueLt : value < 2 ^ bitIndex :=
        Nat.size_le.mp (htarget.1.trans (Nat.le_of_not_gt hnot))
      have hvalueFalse := Nat.testBit_eq_false_of_lt hvalueLt
      rw [hvalueFalse] at hvalueTrue
      simp at hvalueTrue
    refine ⟨htargetWidth, ?_⟩
    rw [htarget.2 bitIndex htargetWidth]
    exact hvalueTrue
  · rintro ⟨htargetWidth, htargetTrue⟩
    have hvalueTrue : value.testBit bitIndex = true := by
      rw [← htarget.2 bitIndex htargetWidth]
      exact htargetTrue
    have hsourceWidth : bitIndex < sourceWidth := by
      by_contra hnot
      have hvalueLt : value < 2 ^ bitIndex :=
        Nat.size_le.mp (hsource.1.trans (Nat.le_of_not_gt hnot))
      have hvalueFalse := Nat.testBit_eq_false_of_lt hvalueLt
      rw [hvalueFalse] at hvalueTrue
      simp at hvalueTrue
    refine ⟨hsourceWidth, ?_⟩
    rw [hsource.2 bitIndex hsourceWidth]
    exact hvalueTrue

theorem CompactFixedWidthCrossTableSlicesEq.entryValue_eq_at_offset
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish
      offset sourceValue targetValue : Nat}
    (heq : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish)
    (hoffset : offset < sourceFinish - sourceStart)
    (hsource : CompactFixedWidthEntry sourceTable sourceWidth
      (sourceStart + offset) sourceValue)
    (htarget : CompactFixedWidthEntry targetTable targetWidth
      (targetStart + offset) targetValue) :
    sourceValue = targetValue := by
  rcases heq with
    ⟨count, _hsourceCountBound, _htargetCountBound,
      hsourceFinish, _htargetFinish,
      _hsourceFinishBound, _htargetFinishBound, hbits⟩
  have hcount : count = sourceFinish - sourceStart := by omega
  subst count
  apply Nat.eq_of_testBit_eq
  intro bitIndex
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hsourceTrue
    have hsourceWidth : bitIndex < sourceWidth := by
      by_contra hnot
      have hsourceLt : sourceValue < 2 ^ bitIndex :=
        Nat.size_le.mp (hsource.1.trans (Nat.le_of_not_gt hnot))
      have hsourceFalse := Nat.testBit_eq_false_of_lt hsourceLt
      rw [hsourceFalse] at hsourceTrue
      simp at hsourceTrue
    have hsourceTableTrue : sourceTable.testBit
        ((sourceStart + offset) * sourceWidth + bitIndex) = true := by
      rw [hsource.2 bitIndex hsourceWidth]
      exact hsourceTrue
    have htargetExtended :=
      (hbits offset hoffset bitIndex (by omega)).mp
        ⟨hsourceWidth, hsourceTableTrue⟩
    rcases htargetExtended with ⟨htargetWidth, htargetTableTrue⟩
    rw [htarget.2 bitIndex htargetWidth] at htargetTableTrue
    exact htargetTableTrue
  · intro htargetTrue
    have htargetWidth : bitIndex < targetWidth := by
      by_contra hnot
      have htargetLt : targetValue < 2 ^ bitIndex :=
        Nat.size_le.mp (htarget.1.trans (Nat.le_of_not_gt hnot))
      have htargetFalse := Nat.testBit_eq_false_of_lt htargetLt
      rw [htargetFalse] at htargetTrue
      simp at htargetTrue
    have htargetTableTrue : targetTable.testBit
        ((targetStart + offset) * targetWidth + bitIndex) = true := by
      rw [htarget.2 bitIndex htargetWidth]
      exact htargetTrue
    have hsourceExtended :=
      (hbits offset hoffset bitIndex (by omega)).mpr
        ⟨htargetWidth, htargetTableTrue⟩
    rcases hsourceExtended with ⟨hsourceWidth, hsourceTableTrue⟩
    rw [hsource.2 bitIndex hsourceWidth] at hsourceTableTrue
    exact hsourceTableTrue

theorem CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat}
    {values : List Nat}
    (hsource : CompactAdditiveNatListDirectLayout
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish values)
    (htarget : CompactAdditiveNatListDirectLayout
      targetTable targetWidth targetTokenCount targetStart targetFinish values) :
    CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish := by
  have hsourceFinish := CompactAdditiveNatListDirectLayout.finish_eq hsource
  have htargetFinish := CompactAdditiveNatListDirectLayout.finish_eq htarget
  have hsourceBound : sourceFinish ≤ sourceTokenCount := by
    rcases hsource with ⟨_boundary, hstructure, _hrows, _hsize⟩
    rcases hstructure with ⟨_bodyStart, _hbodyBound, _hheader, hboundary⟩
    exact hboundary.2.1
  have htargetBound : targetFinish ≤ targetTokenCount := by
    rcases htarget with ⟨_boundary, hstructure, _hrows, _hsize⟩
    rcases hstructure with ⟨_bodyStart, _hbodyBound, _hheader, hboundary⟩
    exact hboundary.2.1
  let count := 1 + values.length
  refine ⟨count, ?_, ?_, ?_, ?_, hsourceBound, htargetBound, ?_⟩
  · dsimp only [count]
    omega
  · dsimp only [count]
    omega
  · dsimp only [count]
    omega
  · dsimp only [count]
    omega
  · intro offset hoffset bitIndex _hbitIndex
    by_cases hoffsetZero : offset = 0
    · subst offset
      have hsourceEntry := CompactAdditiveNatListDirectLayout.headerEntry hsource
      have htargetEntry := CompactAdditiveNatListDirectLayout.headerEntry htarget
      simpa using fixedWidthEntry_cross_true_iff
        hsourceEntry htargetEntry (bitIndex := bitIndex)
    · obtain ⟨index, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hoffsetZero
      have hindex : index < values.length := by
        dsimp only [count] at hoffset
        omega
      have hsourceEntry :=
        CompactAdditiveNatListDirectLayout.valueEntry hsource index hindex
      have htargetEntry :=
        CompactAdditiveNatListDirectLayout.valueEntry htarget index hindex
      have hsourceEntry' : CompactFixedWidthEntry sourceTable sourceWidth
          (sourceStart + (index + 1)) (values.getI index) := by
        convert hsourceEntry using 1 <;> omega
      have htargetEntry' : CompactFixedWidthEntry targetTable targetWidth
          (targetStart + (index + 1)) (values.getI index) := by
        convert htargetEntry using 1 <;> omega
      exact fixedWidthEntry_cross_true_iff
        hsourceEntry' htargetEntry' (bitIndex := bitIndex)

theorem CompactFixedWidthCrossTableSlicesEq.natListValues_eq
    {sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat}
    {sourceValues targetValues : List Nat}
    (heq : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish)
    (hsource : CompactAdditiveNatListDirectLayout
      sourceTable sourceWidth sourceTokenCount
      sourceStart sourceFinish sourceValues)
    (htarget : CompactAdditiveNatListDirectLayout
      targetTable targetWidth targetTokenCount
      targetStart targetFinish targetValues) :
    targetValues = sourceValues := by
  have hsourceFinish := CompactAdditiveNatListDirectLayout.finish_eq hsource
  have htargetFinish := CompactAdditiveNatListDirectLayout.finish_eq htarget
  rcases heq with
    ⟨count, hsourceCountBound, htargetCountBound,
      hsourceCount, htargetCount,
      hsourceBound, htargetBound, hbits⟩
  have hlength : targetValues.length = sourceValues.length := by omega
  let heq' : CompactFixedWidthCrossTableSlicesEq
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish :=
    ⟨count, hsourceCountBound, htargetCountBound,
      hsourceCount, htargetCount, hsourceBound, htargetBound, hbits⟩
  apply List.ext_getElem
  · exact hlength
  · intro index htargetIndex hsourceIndex
    have hsourceEntry :=
      CompactAdditiveNatListDirectLayout.valueEntry hsource index hsourceIndex
    have htargetEntry :=
      CompactAdditiveNatListDirectLayout.valueEntry htarget index htargetIndex
    have hoffset : 1 + index < sourceFinish - sourceStart := by omega
    have hsourceEntry' : CompactFixedWidthEntry sourceTable sourceWidth
        (sourceStart + (1 + index)) (sourceValues.getI index) := by
      simpa [Nat.add_assoc] using hsourceEntry
    have htargetEntry' : CompactFixedWidthEntry targetTable targetWidth
        (targetStart + (1 + index)) (targetValues.getI index) := by
      simpa [Nat.add_assoc] using htargetEntry
    have hvalue := heq'.entryValue_eq_at_offset
      hoffset hsourceEntry' htargetEntry'
    simpa only [List.getI_eq_getElem sourceValues hsourceIndex,
      List.getI_eq_getElem targetValues htargetIndex] using hvalue.symm

#print axioms compactFixedWidthCrossTableSlicesEqDef_spec
#print axioms compactFixedWidthCrossTableSlicesEqDef_sigmaZero
#print axioms CompactFixedWidthCrossTableSlicesEq.entryValue_eq_at_offset
#print axioms CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
#print axioms CompactFixedWidthCrossTableSlicesEq.natListValues_eq

end FoundationCompactNumericListedDirectCrossTableSliceEquality
