import integration.FoundationCompactNumericListedDirectFlexibleBinaryNatDecode
import integration.FoundationCompactNumericListedDirectBoolListPackedValue

/-!
# Direct bounded failure graph for the binary-natural decoder

Decoder success is determined by a bounded marker shape: `digitCount` marker
bits are true and the following marker/data pair is `00`.  Failure is exactly
the bounded absence of such a shape.  No token-size bound is postulated.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatDecodeFailure

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactVerifierBitCostPrimitives
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBoolListPackedValue
open FoundationCompactNumericListedDirectFlexibleBinaryNatDecode

/-- The decoder reaches a `00` terminator after `digitCount` escaped data
pairs.  Data bits themselves are unrestricted. -/
def CompactBinaryNatDecodeShape
    (payload bitCount digitCount : Nat) : Prop :=
  2 * digitCount + 2 ≤ bitCount ∧
    (∀ index < digitCount,
      payload.testBit (2 * index) = true) ∧
    payload.testBit (2 * digitCount) = false ∧
    payload.testBit (2 * digitCount + 1) = false

def compactBinaryNatDecodeShapeDef : 𝚺₀.Semisentence 3 := .mkSigma
  “payload bitCount digitCount.
    2 * digitCount + 2 ≤ bitCount ∧
    (∀ index < digitCount, (2 * index) ∈ payload) ∧
    (2 * digitCount) ∉ payload ∧
    (2 * digitCount + 1) ∉ payload”

@[simp] theorem compactBinaryNatDecodeShapeDef_spec
    (payload bitCount digitCount : Nat) :
    compactBinaryNatDecodeShapeDef.val.Evalb
        ![payload, bitCount, digitCount] ↔
      CompactBinaryNatDecodeShape payload bitCount digitCount := by
  simp [compactBinaryNatDecodeShapeDef, CompactBinaryNatDecodeShape,
    arithmeticMem_nat_iff_testBit]
  rfl

theorem compactBinaryNatDecodeShapeDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatDecodeShapeDef.val := by
  simp [compactBinaryNatDecodeShapeDef]

/-- Every candidate terminator position has an explicit local obstruction. -/
def CompactBinaryNatNoDecodeShape (payload bitCount : Nat) : Prop :=
  ∀ digitCount < bitCount,
    bitCount < 2 * digitCount + 2 ∨
      (∃ index < digitCount,
        payload.testBit (2 * index) = false) ∨
      payload.testBit (2 * digitCount) = true ∨
      payload.testBit (2 * digitCount + 1) = true

def compactBinaryNatNoDecodeShapeDef : 𝚺₀.Semisentence 2 := .mkSigma
  “payload bitCount.
    ∀ digitCount < bitCount,
      bitCount < 2 * digitCount + 2 ∨
      (∃ index < digitCount, (2 * index) ∉ payload) ∨
      (2 * digitCount) ∈ payload ∨
      (2 * digitCount + 1) ∈ payload”

@[simp] theorem compactBinaryNatNoDecodeShapeDef_spec
    (payload bitCount : Nat) :
    compactBinaryNatNoDecodeShapeDef.val.Evalb ![payload, bitCount] ↔
      CompactBinaryNatNoDecodeShape payload bitCount := by
  simp [compactBinaryNatNoDecodeShapeDef,
    CompactBinaryNatNoDecodeShape,
    arithmeticMem_nat_iff_testBit]
  rfl

theorem compactBinaryNatNoDecodeShapeDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactBinaryNatNoDecodeShapeDef.val := by
  simp [compactBinaryNatNoDecodeShapeDef]

theorem compactBinaryNatNoDecodeShape_iff_forall_not_shape
    (payload bitCount : Nat) :
    CompactBinaryNatNoDecodeShape payload bitCount ↔
      ∀ digitCount < bitCount,
        ¬ CompactBinaryNatDecodeShape payload bitCount digitCount := by
  constructor
  · intro hfailure digitCount hdigitCount hshape
    rcases hshape with
      ⟨hshapeBound, hshapeMarkers, hshapeZero, hshapeOne⟩
    rcases hfailure digitCount hdigitCount with
      hbound | hmarker | hzero | hone
    · omega
    · rcases hmarker with ⟨index, hindex, hmarker⟩
      have := hshapeMarkers index hindex
      simp [hmarker] at this
    · simp [hzero] at hshapeZero
    · simp [hone] at hshapeOne
  · intro hnone digitCount hdigitCount
    by_cases hbound : 2 * digitCount + 2 ≤ bitCount
    · by_cases hmarkers : ∀ index < digitCount,
          payload.testBit (2 * index) = true
      · by_cases hzero : payload.testBit (2 * digitCount) = false
        · by_cases hone :
              payload.testBit (2 * digitCount + 1) = false
          · exact (hnone digitCount hdigitCount
              ⟨hbound, hmarkers, hzero, hone⟩).elim
          · right; right; right
            simpa using Bool.eq_true_of_not_eq_false hone
        · right; right; left
          simpa using Bool.eq_true_of_not_eq_false hzero
      · right; left
        push Not at hmarkers
        rcases hmarkers with ⟨index, hindex, hmarker⟩
        exact ⟨index, hindex,
          Bool.eq_false_of_not_eq_true hmarker⟩
    · left
      omega

theorem CompactBinaryNatFlexibleDecodeSegment.decodeShape
    {payload bitCount digitCount token : Nat}
    (hsegment : CompactBinaryNatFlexibleDecodeSegment
      payload bitCount 0 digitCount token (2 * digitCount + 2)) :
    CompactBinaryNatDecodeShape payload bitCount digitCount := by
  rcases hsegment with
    ⟨_hnext, hbound, _hsize, hdata, hzero, hone⟩
  exact ⟨hbound,
    fun index hindex => by
      simpa only [Nat.zero_add] using (hdata index hindex).1,
    by simpa only [Nat.zero_add] using hzero,
    by simpa only [Nat.zero_add] using hone⟩

theorem CompactBinaryNatDecodeShape.flexibleSegment
    {bits : List Bool} {digitCount : Nat}
    (hshape : CompactBinaryNatDecodeShape
      (natOfBitsList bits) bits.length digitCount) :
    ∃ token,
      CompactBinaryNatFlexibleDecodeSegment
        (natOfBitsList bits) bits.length 0 digitCount token
          (2 * digitCount + 2) := by
  let data := flexibleBinaryNatDecodeData bits digitCount
  let token := natOfBitsList data
  have hsize : Nat.size token ≤ digitCount := by
    dsimp only [token]
    rw [Nat.size_le]
    simpa [data] using natOfBitsList_lt_two_pow_length data
  refine ⟨token, by
    refine ⟨by omega, hshape.1, hsize, ?_,
      by simpa only [Nat.zero_add] using hshape.2.2.1,
      by simpa only [Nat.zero_add] using hshape.2.2.2⟩
    intro index hindex
    constructor
    · simpa using hshape.2.1 index hindex
    · simp only [Nat.zero_add]
      rw [natOfBitsList_testBit_eq_getI]
      dsimp only [token]
      rw [natOfBitsList_testBit_eq_getI]
      exact (flexibleBinaryNatDecodeData_getI
        bits digitCount index hindex).symm⟩

theorem CompactBinaryNatDecodeShape.decode_ne_none
    {bits : List Bool} {digitCount : Nat}
    (hshape : CompactBinaryNatDecodeShape
      (natOfBitsList bits) bits.length digitCount) :
    decodeBinaryNat bits ≠ none := by
  rcases hshape.flexibleSegment with ⟨token, hsegment⟩
  rw [hsegment.decode]
  simp

theorem decodeBinaryNat_eq_none_iff_noDecodeShape (bits : List Bool) :
    decodeBinaryNat bits = none ↔
      CompactBinaryNatNoDecodeShape
        (natOfBitsList bits) bits.length := by
  constructor
  · intro hnone
    apply (compactBinaryNatNoDecodeShape_iff_forall_not_shape
      (natOfBitsList bits) bits.length).2
    intro digitCount _hdigitCount hshape
    exact hshape.decode_ne_none hnone
  · intro hnoShape
    have hnone :=
      (compactBinaryNatNoDecodeShape_iff_forall_not_shape
        (natOfBitsList bits) bits.length).1 hnoShape
    cases hdecode : decodeBinaryNat bits with
    | none => rfl
    | some result =>
        rcases result with ⟨token, suffix⟩
        rcases compactBinaryNatFlexibleDecodeSegment_of_decode hdecode with
          ⟨digitCount, hsegment, _hsuffix⟩
        have hshape :=
          CompactBinaryNatFlexibleDecodeSegment.decodeShape hsegment
        have hdigitCount : digitCount < bits.length := by
          have hbound := hshape.1
          omega
        exact (hnone digitCount hdigitCount hshape).elim

def CompactAdditiveBoolListDecodeFailureRows
    (tokenTable width tokenCount boundaryTable bitCount payload : Nat) : Prop :=
  CompactAdditiveBoolListPackedValue
      tokenTable width tokenCount boundaryTable bitCount payload ∧
    CompactBinaryNatNoDecodeShape payload bitCount

def compactAdditiveBoolListDecodeFailureRowsFormulaBundle :
    𝚺₀.Semisentence 6 × 𝚺₀.Semisentence 2 :=
  (compactAdditiveBoolListPackedValueDef,
    compactBinaryNatNoDecodeShapeDef)

@[simp] theorem compactAdditiveBoolListDecodeFailureRowsFormulaBundle_spec
    (tokenTable width tokenCount boundaryTable bitCount payload : Nat) :
    (compactAdditiveBoolListDecodeFailureRowsFormulaBundle.1.val.Evalb
        ![tokenTable, width, tokenCount,
          boundaryTable, bitCount, payload] ∧
      compactAdditiveBoolListDecodeFailureRowsFormulaBundle.2.val.Evalb
        ![payload, bitCount]) ↔
      CompactAdditiveBoolListDecodeFailureRows
        tokenTable width tokenCount boundaryTable bitCount payload := by
  simp [compactAdditiveBoolListDecodeFailureRowsFormulaBundle,
    CompactAdditiveBoolListDecodeFailureRows]

theorem decodeBinaryNat_eq_none_iff_directBoolListRows
    {tokenTable width tokenCount boundaryTable : Nat}
    {bits : List Bool}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      boundaryTable bits) :
    decodeBinaryNat bits = none ↔
      ∃ payload,
        CompactAdditiveBoolListDecodeFailureRows
          tokenTable width tokenCount boundaryTable bits.length payload := by
  constructor
  · intro hnone
    refine ⟨natOfBitsList bits,
      CompactAdditiveStructuredListElementRowLayouts.boolPackedValue hrows,
      ?_⟩
    exact (decodeBinaryNat_eq_none_iff_noDecodeShape bits).mp hnone
  · rintro ⟨payload, hpacked, hnoShape⟩
    have hpayload : payload = natOfBitsList bits :=
      hpacked.eq_natOfBitsList_of_rows hrows
    subst payload
    exact (decodeBinaryNat_eq_none_iff_noDecodeShape bits).mpr hnoShape

#print axioms compactBinaryNatDecodeShapeDef_spec
#print axioms compactBinaryNatDecodeShapeDef_sigmaZero
#print axioms compactBinaryNatNoDecodeShapeDef_spec
#print axioms compactBinaryNatNoDecodeShapeDef_sigmaZero
#print axioms compactBinaryNatNoDecodeShape_iff_forall_not_shape
#print axioms CompactBinaryNatFlexibleDecodeSegment.decodeShape
#print axioms CompactBinaryNatDecodeShape.flexibleSegment
#print axioms CompactBinaryNatDecodeShape.decode_ne_none
#print axioms decodeBinaryNat_eq_none_iff_noDecodeShape
#print axioms compactAdditiveBoolListDecodeFailureRowsFormulaBundle_spec
#print axioms decodeBinaryNat_eq_none_iff_directBoolListRows

end FoundationCompactNumericListedDirectBinaryNatDecodeFailure
