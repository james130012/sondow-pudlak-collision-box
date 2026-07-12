import integration.FoundationCompactNumericListedDirectAtomicListLayouts

/-!
# Exact packed values for direct Boolean-list rows

The relation below reads every Boolean row through the same boundary table
used by the structured-list layout and identifies those rows with one packed
natural-number value.  Under the real row semantics, that value is exactly
`natOfBitsList values`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBoolListPackedValue

open FoundationCompactVerifierBitCostPrimitives
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts

/-- One packed natural number reads exactly the Boolean tags selected by the
common structured-list boundary table. -/
def CompactAdditiveBoolListPackedValue
    (tokenTable width tokenCount boundaryTable bitCount payload : Nat) : Prop :=
  Nat.size payload ≤ bitCount ∧
    ∀ index < bitCount,
      ∃ left, left ≤ tokenCount ∧
      ∃ right, right ≤ tokenCount ∧
        CompactFixedWidthEntry boundaryTable tokenCount index left ∧
        CompactFixedWidthEntry boundaryTable tokenCount (index + 1) right ∧
        ((payload.testBit index = true ∧
            CompactAdditiveTokenCell
              tokenTable width tokenCount left 1 right) ∨
          (payload.testBit index ≠ true ∧
            CompactAdditiveTokenCell
              tokenTable width tokenCount left 0 right))

def compactAdditiveBoolListPackedValueDef : 𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount boundaryTable bitCount payload.
    ∃ payloadSize <⁺ payload,
      !(compactNatSizeDef) payloadSize payload ∧
      payloadSize ≤ bitCount ∧
      ∀ index < bitCount,
        ∃ left <⁺ tokenCount,
          ∃ right <⁺ tokenCount,
            !(compactFixedWidthEntryDef)
              boundaryTable tokenCount index left ∧
            !(compactFixedWidthEntryDef)
              boundaryTable tokenCount (index + 1) right ∧
            (((index ∈ payload) ∧
                left < tokenCount ∧ right = left + 1 ∧
                !(compactFixedWidthEntryDef)
                  tokenTable width left 1) ∨
              ((index ∉ payload) ∧
                left < tokenCount ∧ right = left + 1 ∧
                !(compactFixedWidthEntryDef)
                  tokenTable width left 0))”

@[simp] theorem compactAdditiveBoolListPackedValueDef_spec
    (tokenTable width tokenCount boundaryTable bitCount payload : Nat) :
    compactAdditiveBoolListPackedValueDef.val.Evalb
        ![tokenTable, width, tokenCount, boundaryTable, bitCount, payload] ↔
      CompactAdditiveBoolListPackedValue
        tokenTable width tokenCount boundaryTable bitCount payload := by
  have hsizeSelf : ∀ value : Nat, Nat.size value ≤ value := by
    intro value
    exact natSize_le_of_le (Nat.le_refl value)
  simp [compactAdditiveBoolListPackedValueDef,
    CompactAdditiveBoolListPackedValue,
    compactFixedWidthEntryDef, CompactAdditiveTokenCell,
    CompactFixedWidthEntry,
    arithmeticMem_nat_iff_testBit, foundationNatLE_iff_standard,
    hsizeSelf]

theorem compactAdditiveBoolListPackedValueDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveBoolListPackedValueDef.val := by
  simp [compactAdditiveBoolListPackedValueDef]

theorem CompactAdditiveStructuredListElementRowLayouts.boolPackedValue
    {tokenTable width tokenCount boundaryTable : Nat}
    {values : List Bool}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      boundaryTable values) :
    CompactAdditiveBoolListPackedValue
      tokenTable width tokenCount boundaryTable values.length
        (natOfBitsList values) := by
  refine ⟨?_, ?_⟩
  · rw [Nat.size_le]
    exact natOfBitsList_lt_two_pow_length values
  · intro index hindex
    rcases hrows index hindex with
      ⟨left, hleft, right, hright, hleftEntry, hrightEntry, hlayout⟩
    refine ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, ?_⟩
    cases hvalue : values.getI index with
    | false =>
        right
        constructor
        · rw [natOfBitsList_testBit_eq_getI, hvalue]
          simp
        · simpa [CompactAdditiveBoolValueDirectLayout,
            compactAdditiveBoolTag, hvalue] using hlayout.1
    | true =>
        left
        constructor
        · rw [natOfBitsList_testBit_eq_getI, hvalue]
        · simpa [CompactAdditiveBoolValueDirectLayout,
            compactAdditiveBoolTag, hvalue] using hlayout.1

theorem CompactAdditiveBoolListPackedValue.eq_natOfBitsList_of_rows
    {tokenTable width tokenCount boundaryTable payload : Nat}
    {values : List Bool}
    (hpacked : CompactAdditiveBoolListPackedValue
      tokenTable width tokenCount boundaryTable values.length payload)
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      boundaryTable values) :
    payload = natOfBitsList values := by
  apply Nat.eq_of_testBit_eq
  intro index
  by_cases hindex : index < values.length
  · rcases hpacked.2 index hindex with
      ⟨packedLeft, _hpackedLeftBound, packedRight,
        _hpackedRightBound, hpackedLeftEntry, _hpackedRightEntry,
        hpackedBit⟩
    rcases hrows index hindex with
      ⟨rowLeft, _hrowLeftBound, rowRight, _hrowRightBound,
        hrowLeftEntry, _hrowRightEntry, hrowLayout⟩
    have hleft : packedLeft = rowLeft := by
      calc
        packedLeft =
            compactFixedWidthTableValue
              boundaryTable tokenCount index :=
          FoundationCompactNumericListedDirectTokenStreamInverse.CompactFixedWidthEntry.value_eq_tableValue
            hpackedLeftEntry
        _ = rowLeft :=
          (FoundationCompactNumericListedDirectTokenStreamInverse.CompactFixedWidthEntry.value_eq_tableValue
            hrowLeftEntry).symm
    subst packedLeft
    have hrowSlice : CompactAdditiveBoolSlice
        tokenTable width tokenCount rowLeft
          (compactAdditiveBoolTag (values.getI index)) rowRight := by
      simpa [CompactAdditiveBoolValueDirectLayout] using hrowLayout
    rw [natOfBitsList_testBit_eq_getI]
    rcases hpackedBit with ⟨hpayloadBit, honeSlice⟩ |
        ⟨hpayloadBit, hzeroSlice⟩
    · have htag : compactAdditiveBoolTag (values.getI index) = 1 :=
        (CompactAdditiveTokenCell.value_eq_tableValue hrowSlice.1).trans
          (CompactAdditiveTokenCell.value_eq_tableValue honeSlice).symm
      cases hvalue : values.getI index with
      | false => simp [compactAdditiveBoolTag, hvalue] at htag
      | true => simpa [hvalue] using hpayloadBit
    · have htag : compactAdditiveBoolTag (values.getI index) = 0 :=
        (CompactAdditiveTokenCell.value_eq_tableValue hrowSlice.1).trans
          (CompactAdditiveTokenCell.value_eq_tableValue hzeroSlice).symm
      cases hvalue : values.getI index with
      | false =>
          cases hpayloadValue : payload.testBit index with
          | false => rfl
          | true => exact (hpayloadBit hpayloadValue).elim
      | true => simp [compactAdditiveBoolTag, hvalue] at htag
  · have hindexLe : values.length ≤ index := Nat.le_of_not_gt hindex
    have hpayloadLt : payload < 2 ^ index :=
      Nat.size_le.mp (hpacked.1.trans hindexLe)
    rw [Nat.testBit_eq_false_of_lt hpayloadLt]
    rw [natOfBitsList_testBit_eq_getI]
    rw [List.getI_eq_default _ (by omega)]
    rfl

theorem compactAdditiveBoolListPackedValue_iff_eq_natOfBitsList_of_rows
    {tokenTable width tokenCount boundaryTable payload : Nat}
    {values : List Bool}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveBoolValueDirectLayout tokenTable width tokenCount
      boundaryTable values) :
    CompactAdditiveBoolListPackedValue
        tokenTable width tokenCount boundaryTable values.length payload ↔
      payload = natOfBitsList values := by
  constructor
  · intro hpacked
    exact hpacked.eq_natOfBitsList_of_rows hrows
  · rintro rfl
    exact CompactAdditiveStructuredListElementRowLayouts.boolPackedValue hrows

#print axioms compactAdditiveBoolListPackedValueDef_spec
#print axioms compactAdditiveBoolListPackedValueDef_sigmaZero
#print axioms CompactAdditiveStructuredListElementRowLayouts.boolPackedValue
#print axioms CompactAdditiveBoolListPackedValue.eq_natOfBitsList_of_rows
#print axioms compactAdditiveBoolListPackedValue_iff_eq_natOfBitsList_of_rows

end FoundationCompactNumericListedDirectBoolListPackedValue
