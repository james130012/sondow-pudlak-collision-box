import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepCases

/-!
# Flexible direct segments for the real binary-natural decoder

Unlike the canonical token segment, the real decoder accepts redundant high
zero data pairs.  The explicit `digitCount` below records the consumed pair
count independently of `Nat.size token`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFlexibleBinaryNatDecode

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactVerifierBitCostPrimitives
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau

def binaryNatEscapedPrefix (data : List Bool) : List Bool :=
  compactEscapedNatBits data ++ [false, false]

@[simp] theorem binaryNatEscapedPrefix_length (data : List Bool) :
    (binaryNatEscapedPrefix data).length = 2 * data.length + 2 := by
  simp [binaryNatEscapedPrefix]

theorem decodeBinaryNat_escapedPrefix_append
    (data suffix : List Bool) :
    decodeBinaryNat (binaryNatEscapedPrefix data ++ suffix) =
      some (natOfBitsList data, suffix) := by
  induction data with
  | nil =>
      simp [binaryNatEscapedPrefix, compactEscapedNatBits,
        decodeBinaryNat, natOfBitsList]
  | cons bit data ih =>
      rw [show binaryNatEscapedPrefix (bit :: data) ++ suffix =
          true :: bit :: (binaryNatEscapedPrefix data ++ suffix) by
        simp [binaryNatEscapedPrefix, compactEscapedNatBits,
          List.append_assoc]]
      simp only [decodeBinaryNat]
      rw [ih]
      rfl

theorem decodeBinaryNat_eq_some_exists_escapedPrefix
    {bits suffix : List Bool} {token : Nat}
    (hdecode : decodeBinaryNat bits = some (token, suffix)) :
    ∃ data,
      bits = binaryNatEscapedPrefix data ++ suffix ∧
      token = natOfBitsList data := by
  induction bits using List.twoStepInduction generalizing token suffix with
  | nil => simp [decodeBinaryNat] at hdecode
  | singleton bit => cases bit <;> simp [decodeBinaryNat] at hdecode
  | cons_cons first second rest ihRest _ihCons =>
      cases first with
      | false =>
          cases second with
          | false =>
              simp [decodeBinaryNat] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              exact ⟨[], by simp [binaryNatEscapedPrefix,
                compactEscapedNatBits], rfl⟩
          | true => simp [decodeBinaryNat] at hdecode
      | true =>
          cases hrest : decodeBinaryNat rest with
          | none => simp [decodeBinaryNat, hrest] at hdecode
          | some result =>
              rcases result with ⟨restToken, restSuffix⟩
              have ih := ihRest hrest
              simp [decodeBinaryNat, hrest] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              rcases ih with ⟨data, hrestBits, hrestToken⟩
              refine ⟨second :: data, ?_, ?_⟩
              · simp [binaryNatEscapedPrefix, compactEscapedNatBits,
                  hrestBits, List.append_assoc]
              · simp [natOfBitsList, hrestToken]

theorem decodeBinaryNat_eq_some_iff_escapedPrefix
    (bits : List Bool) (token : Nat) (suffix : List Bool) :
    decodeBinaryNat bits = some (token, suffix) ↔
      ∃ data,
        bits = binaryNatEscapedPrefix data ++ suffix ∧
        token = natOfBitsList data := by
  constructor
  · exact decodeBinaryNat_eq_some_exists_escapedPrefix
  · rintro ⟨data, rfl, rfl⟩
    exact decodeBinaryNat_escapedPrefix_append data suffix

/-- Direct segment for the real decoder.  `digitCount` may exceed the honest
binary size of `token`; all additional high data bits are forced to zero by
the `Nat.size token ≤ digitCount` guard and the bit equalities. -/
def CompactBinaryNatFlexibleDecodeSegment
    (payload bitCount offset digitCount token next : Nat) : Prop :=
  next = offset + 2 * digitCount + 2 ∧
    next ≤ bitCount ∧
    Nat.size token ≤ digitCount ∧
    (∀ index < digitCount,
      payload.testBit (offset + 2 * index) = true ∧
      payload.testBit (offset + 2 * index + 1) =
        token.testBit index) ∧
    payload.testBit (offset + 2 * digitCount) = false ∧
    payload.testBit (offset + 2 * digitCount + 1) = false

def compactBinaryNatFlexibleDecodeSegmentDef : 𝚺₀.Semisentence 6 := .mkSigma
  “payload bitCount offset digitCount token next.
    ∃ size <⁺ token,
      !(compactNatSizeDef) size token ∧
      size ≤ digitCount ∧
      next = offset + 2 * digitCount + 2 ∧
      next ≤ bitCount ∧
      (∀ index < digitCount,
        (offset + 2 * index) ∈ payload ∧
        ((offset + 2 * index + 1) ∈ payload ↔ index ∈ token)) ∧
      (offset + 2 * digitCount) ∉ payload ∧
      (offset + 2 * digitCount + 1) ∉ payload”

@[simp] theorem compactBinaryNatFlexibleDecodeSegmentDef_spec
    (payload bitCount offset digitCount token next : Nat) :
    compactBinaryNatFlexibleDecodeSegmentDef.val.Evalb
        ![payload, bitCount, offset, digitCount, token, next] ↔
      CompactBinaryNatFlexibleDecodeSegment
        payload bitCount offset digitCount token next := by
  have hsize : Nat.size token ≤ token := by
    rw [Nat.size_le]
    exact token.lt_two_pow_self
  simp [compactBinaryNatFlexibleDecodeSegmentDef,
    CompactBinaryNatFlexibleDecodeSegment,
    arithmeticMem_nat_iff_testBit,
    foundationNatLE_iff_standard, hsize,
    and_assoc, and_left_comm, and_comm]
  aesop

theorem compactBinaryNatFlexibleDecodeSegmentDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatFlexibleDecodeSegmentDef.val := by
  simp [compactBinaryNatFlexibleDecodeSegmentDef]

theorem compactBinaryNatFlexibleDecodeSegment_escapedPrefix
    (data suffix : List Bool) :
    let bits := binaryNatEscapedPrefix data ++ suffix
    CompactBinaryNatFlexibleDecodeSegment
      (natOfBitsList bits) bits.length 0 data.length
      (natOfBitsList data) (2 * data.length + 2) := by
  let bits := binaryNatEscapedPrefix data ++ suffix
  have hsize : Nat.size (natOfBitsList data) ≤ data.length := by
    rw [Nat.size_le]
    exact natOfBitsList_lt_two_pow_length data
  have hnextBound : 2 * data.length + 2 ≤ bits.length := by
    simp [bits]
  refine ⟨by omega, hnextBound, hsize, ?_, ?_, ?_⟩
  · intro index hindex
    constructor
    · rw [natOfBitsList_testBit_eq_getI]
      simp only [Nat.zero_add]
      rw [List.getI_append _ _ _ (by
        rw [binaryNatEscapedPrefix_length]
        omega)]
      rw [binaryNatEscapedPrefix]
      rw [List.getI_append _ _ _ (by simp; omega)]
      exact compactEscapedNatBits_getI_marker data index hindex
    · rw [natOfBitsList_testBit_eq_getI]
      simp only [Nat.zero_add]
      rw [List.getI_append _ _ _ (by
        rw [binaryNatEscapedPrefix_length]
        omega)]
      rw [binaryNatEscapedPrefix]
      rw [List.getI_append _ _ _ (by simp; omega)]
      rw [compactEscapedNatBits_getI_data data index hindex]
      exact (natOfBitsList_testBit_eq_getI data index).symm
  · rw [natOfBitsList_testBit_eq_getI]
    simp only [Nat.zero_add]
    rw [List.getI_append _ _ _ (by
      rw [binaryNatEscapedPrefix_length]
      omega)]
    rw [binaryNatEscapedPrefix]
    rw [List.getI_append_right]
    · simp
    · simp
  · rw [natOfBitsList_testBit_eq_getI]
    simp only [Nat.zero_add]
    rw [List.getI_append _ _ _ (by
      rw [binaryNatEscapedPrefix_length]
      omega)]
    rw [binaryNatEscapedPrefix]
    rw [List.getI_append_right]
    · simp
    · simp

theorem compactBinaryNatFlexibleDecodeSegment_of_decode
    {bits suffix : List Bool} {token : Nat}
    (hdecode : decodeBinaryNat bits = some (token, suffix)) :
    ∃ digitCount,
      CompactBinaryNatFlexibleDecodeSegment
        (natOfBitsList bits) bits.length 0 digitCount token
          (2 * digitCount + 2) ∧
      suffix = bits.drop (2 * digitCount + 2) := by
  rcases decodeBinaryNat_eq_some_exists_escapedPrefix hdecode with
    ⟨data, hbits, htoken⟩
  refine ⟨data.length, ?_, ?_⟩
  · rw [hbits, htoken]
    exact compactBinaryNatFlexibleDecodeSegment_escapedPrefix data suffix
  · rw [hbits]
    simp [binaryNatEscapedPrefix_length]

def flexibleBinaryNatDecodeData
    (bits : List Bool) (digitCount : Nat) : List Bool :=
  (List.range digitCount).map fun index =>
    bits.getI (2 * index + 1)

@[simp] theorem flexibleBinaryNatDecodeData_length
    (bits : List Bool) (digitCount : Nat) :
    (flexibleBinaryNatDecodeData bits digitCount).length = digitCount := by
  simp [flexibleBinaryNatDecodeData]

theorem flexibleBinaryNatDecodeData_getI
    (bits : List Bool) (digitCount index : Nat)
    (hindex : index < digitCount) :
    (flexibleBinaryNatDecodeData bits digitCount).getI index =
      bits.getI (2 * index + 1) := by
  rw [List.getI_eq_getElem _ (by simpa using hindex)]
  simp [flexibleBinaryNatDecodeData]

theorem binaryNatEscapedPrefix_getI_marker
    (data : List Bool) (index : Nat) (hindex : index < data.length) :
    (binaryNatEscapedPrefix data).getI (2 * index) = true := by
  rw [binaryNatEscapedPrefix]
  rw [List.getI_append _ _ _ (by simp; omega)]
  exact compactEscapedNatBits_getI_marker data index hindex

theorem binaryNatEscapedPrefix_getI_data
    (data : List Bool) (index : Nat) (hindex : index < data.length) :
    (binaryNatEscapedPrefix data).getI (2 * index + 1) =
      data.getI index := by
  rw [binaryNatEscapedPrefix]
  rw [List.getI_append _ _ _ (by simp; omega)]
  exact compactEscapedNatBits_getI_data data index hindex

@[simp] theorem binaryNatEscapedPrefix_getI_terminator_zero
    (data : List Bool) :
    (binaryNatEscapedPrefix data).getI (2 * data.length) = false := by
  rw [binaryNatEscapedPrefix]
  rw [List.getI_append_right]
  · simp
  · simp

@[simp] theorem binaryNatEscapedPrefix_getI_terminator_one
    (data : List Bool) :
    (binaryNatEscapedPrefix data).getI (2 * data.length + 1) = false := by
  rw [binaryNatEscapedPrefix]
  rw [List.getI_append_right]
  · simp
  · simp

theorem CompactBinaryNatFlexibleDecodeSegment.token_eq_reconstructedData
    {bits : List Bool} {digitCount token : Nat}
    (hsegment : CompactBinaryNatFlexibleDecodeSegment
      (natOfBitsList bits) bits.length 0 digitCount token
        (2 * digitCount + 2)) :
    token = natOfBitsList
      (flexibleBinaryNatDecodeData bits digitCount) := by
  rcases hsegment with
    ⟨_hnext, _hbound, hsize, hdata, _hzero, _hone⟩
  apply Nat.eq_of_testBit_eq
  intro index
  by_cases hindex : index < digitCount
  · rw [natOfBitsList_testBit_eq_getI]
    rw [flexibleBinaryNatDecodeData_getI bits digitCount index hindex]
    rw [← natOfBitsList_testBit_eq_getI bits (2 * index + 1)]
    simpa only [Nat.zero_add] using (hdata index hindex).2.symm
  · have hdigitCount : digitCount ≤ index := Nat.le_of_not_gt hindex
    have htokenLt : token < 2 ^ index :=
      Nat.size_le.mp (hsize.trans hdigitCount)
    rw [Nat.testBit_eq_false_of_lt htokenLt]
    rw [natOfBitsList_testBit_eq_getI]
    rw [List.getI_eq_default _ (by
      simp [flexibleBinaryNatDecodeData]
      omega)]
    rfl

theorem CompactBinaryNatFlexibleDecodeSegment.take_eq_escapedPrefix
    {bits : List Bool} {digitCount token : Nat}
    (hsegment : CompactBinaryNatFlexibleDecodeSegment
      (natOfBitsList bits) bits.length 0 digitCount token
        (2 * digitCount + 2)) :
    bits.take (2 * digitCount + 2) =
      binaryNatEscapedPrefix
        (flexibleBinaryNatDecodeData bits digitCount) := by
  let data := flexibleBinaryNatDecodeData bits digitCount
  rcases hsegment with
    ⟨_hnext, hbound, _hsize, hdata, hzero, hone⟩
  have hdataLength : data.length = digitCount := by simp [data]
  apply List.ext_getElem
  · simp [hbound]
  · intro position htake hprefix
    have htakeLength :
        (bits.take (2 * digitCount + 2)).length ≤
          2 * digitCount + 2 := List.length_take_le _ _
    have hpositionConsumed : position < 2 * digitCount + 2 :=
      htake.trans_le htakeLength
    have hpositionBits : position < bits.length := by
      exact hpositionConsumed.trans_le hbound
    rw [List.getElem_take]
    rw [← List.getI_eq_getElem _ hpositionBits]
    rw [← List.getI_eq_getElem _ hprefix]
    by_cases hdataPosition : position < 2 * digitCount
    · rcases Nat.even_or_odd' position with
        ⟨index, hposition | hposition⟩
      · subst position
        have hindex : index < digitCount := by omega
        rw [binaryNatEscapedPrefix_getI_marker data index (by
          simpa [data] using hindex)]
        rw [← natOfBitsList_testBit_eq_getI bits (2 * index)]
        simpa using (hdata index hindex).1
      · subst position
        have hindex : index < digitCount := by omega
        rw [binaryNatEscapedPrefix_getI_data data index (by
          simpa [data] using hindex)]
        exact (flexibleBinaryNatDecodeData_getI
          bits digitCount index hindex).symm
    · have hterminator :
          position = 2 * digitCount ∨
            position = 2 * digitCount + 1 := by
        have hprefixLength :
            (binaryNatEscapedPrefix data).length =
              2 * digitCount + 2 := by simp [data]
        omega
      rcases hterminator with hposition | hposition
      · subst position
        have hprefixTerminator :=
          binaryNatEscapedPrefix_getI_terminator_zero data
        rw [hdataLength] at hprefixTerminator
        rw [hprefixTerminator]
        rw [← natOfBitsList_testBit_eq_getI bits (2 * digitCount)]
        simpa using hzero
      · subst position
        have hprefixTerminator :=
          binaryNatEscapedPrefix_getI_terminator_one data
        rw [hdataLength] at hprefixTerminator
        rw [hprefixTerminator]
        rw [← natOfBitsList_testBit_eq_getI bits
          (2 * digitCount + 1)]
        simpa using hone

theorem CompactBinaryNatFlexibleDecodeSegment.bits_eq_escapedPrefix_drop
    {bits : List Bool} {digitCount token : Nat}
    (hsegment : CompactBinaryNatFlexibleDecodeSegment
      (natOfBitsList bits) bits.length 0 digitCount token
        (2 * digitCount + 2)) :
    bits = binaryNatEscapedPrefix
        (flexibleBinaryNatDecodeData bits digitCount) ++
      bits.drop (2 * digitCount + 2) := by
  calc
    bits = bits.take (2 * digitCount + 2) ++
        bits.drop (2 * digitCount + 2) :=
      (List.take_append_drop (2 * digitCount + 2) bits).symm
    _ = binaryNatEscapedPrefix
          (flexibleBinaryNatDecodeData bits digitCount) ++
        bits.drop (2 * digitCount + 2) := by
      rw [hsegment.take_eq_escapedPrefix]

theorem CompactBinaryNatFlexibleDecodeSegment.decode
    {bits : List Bool} {digitCount token : Nat}
    (hsegment : CompactBinaryNatFlexibleDecodeSegment
      (natOfBitsList bits) bits.length 0 digitCount token
        (2 * digitCount + 2)) :
    decodeBinaryNat bits =
      some (token, bits.drop (2 * digitCount + 2)) := by
  have hbits := hsegment.bits_eq_escapedPrefix_drop
  have htoken := hsegment.token_eq_reconstructedData
  calc
    decodeBinaryNat bits =
        decodeBinaryNat
          (binaryNatEscapedPrefix
              (flexibleBinaryNatDecodeData bits digitCount) ++
            bits.drop (2 * digitCount + 2)) :=
      congrArg decodeBinaryNat hbits
    _ = some
        (natOfBitsList (flexibleBinaryNatDecodeData bits digitCount),
          bits.drop (2 * digitCount + 2)) :=
      decodeBinaryNat_escapedPrefix_append
        (flexibleBinaryNatDecodeData bits digitCount)
        (bits.drop (2 * digitCount + 2))
    _ = some (token, bits.drop (2 * digitCount + 2)) := by
      rw [htoken]

theorem decodeBinaryNat_eq_some_iff_flexibleSegment
    (bits : List Bool) (token : Nat) (suffix : List Bool) :
    decodeBinaryNat bits = some (token, suffix) ↔
      ∃ digitCount,
        CompactBinaryNatFlexibleDecodeSegment
          (natOfBitsList bits) bits.length 0 digitCount token
            (2 * digitCount + 2) ∧
        suffix = bits.drop (2 * digitCount + 2) := by
  constructor
  · exact compactBinaryNatFlexibleDecodeSegment_of_decode
  · rintro ⟨digitCount, hsegment, rfl⟩
    exact hsegment.decode

#print axioms decodeBinaryNat_escapedPrefix_append
#print axioms decodeBinaryNat_eq_some_iff_escapedPrefix
#print axioms compactBinaryNatFlexibleDecodeSegmentDef_spec
#print axioms compactBinaryNatFlexibleDecodeSegmentDef_sigmaZero
#print axioms compactBinaryNatFlexibleDecodeSegment_escapedPrefix
#print axioms compactBinaryNatFlexibleDecodeSegment_of_decode
#print axioms CompactBinaryNatFlexibleDecodeSegment.token_eq_reconstructedData
#print axioms CompactBinaryNatFlexibleDecodeSegment.take_eq_escapedPrefix
#print axioms CompactBinaryNatFlexibleDecodeSegment.decode
#print axioms decodeBinaryNat_eq_some_iff_flexibleSegment

end FoundationCompactNumericListedDirectFlexibleBinaryNatDecode
