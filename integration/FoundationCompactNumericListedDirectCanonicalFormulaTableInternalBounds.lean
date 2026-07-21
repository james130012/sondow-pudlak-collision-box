import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceInputTableau

/-!
# Public internal bounds for the canonical formula-code tableau

All witnesses are the values computed from the decoded formula token list.
The theorem below keeps their numerical and binary-size bounds tied to the
same public `formulaCode`; it does not reselect witnesses from formula truth.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCanonicalFormulaTableInternalBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierAcceptedTraceInputTableau

/-- The canonical formula tableau, together with all bounds needed to compile
its internal bounded quantifiers, is controlled by the public formula-code
bit length. -/
theorem compactNumericListedDirectCanonicalFormulaTable_internalBounds
    (formulaTokens : List Nat) (formulaCode : Nat)
    (hcode : formulaCode = compactAdditivePackedCode formulaTokens) :
    let width := (compactBinaryNatPayloadBits formulaTokens).length
    let tokenTable := compactFixedWidthTableCode width formulaTokens
    let offsetTable := compactFixedWidthTableCode width
      (compactBinaryNatTokenOffsets formulaTokens)
    let payload := compactBinaryNatPayloadValue formulaTokens
    let sentinel := 2 ^ width
    CompactCanonicalPackedTokenStreamTableauAtWidth
        formulaCode formulaTokens.length tokenTable offsetTable width /\
      payload <= formulaCode /\
      sentinel <= formulaCode /\
      width + 1 = Nat.size formulaCode /\
      formulaTokens.length <= Nat.size formulaCode /\
      (forall token, token ∈ formulaTokens ->
        Nat.size token <= Nat.size formulaCode) /\
      (forall offset, offset ∈ compactBinaryNatTokenOffsets formulaTokens ->
        offset <= Nat.size formulaCode) /\
      Nat.size tokenTable <=
        Nat.size formulaCode * Nat.size formulaCode /\
      Nat.size offsetTable <=
        Nat.size formulaCode * Nat.size formulaCode := by
  let width := (compactBinaryNatPayloadBits formulaTokens).length
  let tokenTable := compactFixedWidthTableCode width formulaTokens
  let offsetTable := compactFixedWidthTableCode width
    (compactBinaryNatTokenOffsets formulaTokens)
  let payload := compactBinaryNatPayloadValue formulaTokens
  let sentinel := 2 ^ width
  have htableau : CompactCanonicalPackedTokenStreamTableauAtWidth
      formulaCode formulaTokens.length tokenTable offsetTable width := by
    rw [hcode]
    simpa only [width, tokenTable, offsetTable] using
      compactCanonicalPackedTokenStreamTableauAtWidth_canonical formulaTokens
  have hpayloadSentinel : payload < sentinel := by
    exact natOfBitsList_lt_two_pow_length
      (compactBinaryNatPayloadBits formulaTokens)
  have hpacked : compactAdditivePackedCode formulaTokens =
      payload + sentinel := by
    change packBinaryString (compactBinaryNatPayloadBits formulaTokens) =
      compactBinaryNatPayloadValue formulaTokens + 2 ^ width
    exact packBinaryString_eq_payload_add_sentinel
      (compactBinaryNatPayloadBits formulaTokens)
  have hformulaCode : formulaCode = payload + sentinel :=
    hcode.trans hpacked
  have hpayloadCode : payload <= formulaCode := by omega
  have hsentinelCode : sentinel <= formulaCode := by omega
  have hwidthSize : width + 1 = Nat.size formulaCode := by
    rw [hcode, compactAdditivePackedCode_size]
    simp only [width, compactBinaryNatPayloadBits,
      compactAdditiveTokenBitLength]
  have hwidthCodeSize : width <= Nat.size formulaCode := by omega
  have hcountWidth : formulaTokens.length <= width := by
    exact compactBinaryNatToken_count_le_payloadLength formulaTokens
  have hcountCodeSize : formulaTokens.length <= Nat.size formulaCode :=
    hcountWidth.trans hwidthCodeSize
  have htokenSize : forall token, token ∈ formulaTokens ->
      Nat.size token <= Nat.size formulaCode := by
    intro token htoken
    exact (compactBinaryNatToken_size_le_payloadLength
      formulaTokens token htoken).trans hwidthCodeSize
  have hoffset : forall offset,
      offset ∈ compactBinaryNatTokenOffsets formulaTokens ->
        offset <= Nat.size formulaCode := by
    intro offset hoffset
    exact (compactBinaryNatTokenOffsets_mem_le_payloadLength
      formulaTokens offset hoffset).trans hwidthCodeSize
  have hsizes :=
    compactBinaryNatTokenStreamTableau_canonical_size_bounds formulaTokens
  have htokenTable : Nat.size tokenTable <=
      Nat.size formulaCode * Nat.size formulaCode := by
    exact hsizes.1.trans
      (Nat.mul_le_mul hcountCodeSize hwidthCodeSize)
  have hcountSuccCodeSize : formulaTokens.length + 1 <=
      Nat.size formulaCode := by omega
  have hoffsetTable : Nat.size offsetTable <=
      Nat.size formulaCode * Nat.size formulaCode := by
    exact hsizes.2.trans
      (Nat.mul_le_mul hcountSuccCodeSize hwidthCodeSize)
  exact ⟨htableau, hpayloadCode, hsentinelCode, hwidthSize,
    hcountCodeSize, htokenSize, hoffset, htokenTable, hoffsetTable⟩

#print axioms
  compactNumericListedDirectCanonicalFormulaTable_internalBounds

end FoundationCompactNumericListedDirectCanonicalFormulaTableInternalBounds
