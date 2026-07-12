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

#print axioms decodeBinaryNat_escapedPrefix_append
#print axioms decodeBinaryNat_eq_some_iff_escapedPrefix
#print axioms compactBinaryNatFlexibleDecodeSegmentDef_spec
#print axioms compactBinaryNatFlexibleDecodeSegmentDef_sigmaZero
#print axioms compactBinaryNatFlexibleDecodeSegment_escapedPrefix
#print axioms compactBinaryNatFlexibleDecodeSegment_of_decode

end FoundationCompactNumericListedDirectFlexibleBinaryNatDecode
