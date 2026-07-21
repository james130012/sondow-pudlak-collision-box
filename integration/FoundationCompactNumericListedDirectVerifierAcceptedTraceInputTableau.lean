import integration.FoundationCompactNumericListedDirectTokenStreamInverse
import integration.FoundationCompactNumericListedDirectAtomicListRowRealization

/-!
# Canonical public-input tableau with an exposed token width

The existing canonical packed-stream relation existentially binds its payload
width.  The accepted-trace input bridge needs that same width as a public
arithmetic coordinate so it can compare decoded input tokens with the two
initial verifier-state lists row by row.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTraceInputTableau

open FoundationCompactAdditiveTokenCodec
open FoundationCompactListedPackedBitTokenSynchronization
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTokenStreamInverse

def CompactCanonicalPackedTokenStreamTableauAtWidth
    (code tokenCount tokenTable offsetTable width : Nat) : Prop :=
  exists payload, payload <= code /\
  width <= code /\
  exists sentinel, sentinel <= code /\
    sentinel = 2 ^ width /\
    payload < sentinel /\
    code = payload + sentinel /\
    CompactBinaryNatTokenStreamTableau
      payload width sentinel tokenCount tokenTable offsetTable

def compactCanonicalPackedTokenStreamTableauAtWidthDef :
    HierarchySymbol.sigmaZero.Semisentence 5 := .mkSigma
  “code tokenCount tokenTable offsetTable width.
    ∃ payload <⁺ code,
      width ≤ code ∧
      ∃ sentinel <⁺ code,
        !expDef sentinel width ∧
        payload < sentinel ∧
        code = payload + sentinel ∧
        !(compactBinaryNatTokenStreamTableauDef)
          payload width sentinel tokenCount tokenTable offsetTable”

@[simp] theorem compactCanonicalPackedTokenStreamTableauAtWidthDef_spec
    (code tokenCount tokenTable offsetTable width : Nat) :
    compactCanonicalPackedTokenStreamTableauAtWidthDef.val.Evalb
        ![code, tokenCount, tokenTable, offsetTable, width] ↔
      CompactCanonicalPackedTokenStreamTableauAtWidth
        code tokenCount tokenTable offsetTable width := by
  simp [compactCanonicalPackedTokenStreamTableauAtWidthDef,
    CompactCanonicalPackedTokenStreamTableauAtWidth,
    compactBinaryNatTokenStreamTableauDef,
    CompactBinaryNatTokenStreamTableau,
    foundationNatLE_iff_standard]

theorem compactCanonicalPackedTokenStreamTableauAtWidthDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactCanonicalPackedTokenStreamTableauAtWidthDef.val :=
  compactCanonicalPackedTokenStreamTableauAtWidthDef.sigma_prop

theorem CompactCanonicalPackedTokenStreamTableauAtWidth.to_unexposed
    {code tokenCount tokenTable offsetTable width : Nat}
    (hvalid : CompactCanonicalPackedTokenStreamTableauAtWidth
      code tokenCount tokenTable offsetTable width) :
    CompactCanonicalPackedTokenStreamTableau
      code tokenCount tokenTable offsetTable := by
  rcases hvalid with
    ⟨payload, hpayloadCode, hwidthCode, sentinel, hsentinelCode,
      hsentinel, hpayload, hcode, htableau⟩
  exact ⟨payload, hpayloadCode, width, hwidthCode,
    sentinel, hsentinelCode, hsentinel, hpayload, hcode, htableau⟩

def compactCanonicalPackedTokenStreamTableauAtWidthTokens
    (tokenCount tokenTable width : Nat) : List Nat :=
  compactFixedWidthTableValues tokenTable width tokenCount

@[simp] theorem compactCanonicalPackedTokenStreamTableauAtWidthTokens_length
    (tokenCount tokenTable width : Nat) :
    (compactCanonicalPackedTokenStreamTableauAtWidthTokens
      tokenCount tokenTable width).length = tokenCount := by
  simp [compactCanonicalPackedTokenStreamTableauAtWidthTokens]

theorem CompactCanonicalPackedTokenStreamTableauAtWidth.code_eq_canonical
    {code tokenCount tokenTable offsetTable width : Nat}
    (hvalid : CompactCanonicalPackedTokenStreamTableauAtWidth
      code tokenCount tokenTable offsetTable width) :
    code = compactAdditivePackedCode
      (compactCanonicalPackedTokenStreamTableauAtWidthTokens
        tokenCount tokenTable width) := by
  rcases hvalid with
    ⟨payload, _hpayloadCode, _hwidthCode, sentinel, _hsentinelCode,
      hsentinel, hpayload, hcode, htableau⟩
  let tokens := compactCanonicalPackedTokenStreamTableauAtWidthTokens
    tokenCount tokenTable width
  have hpayloadPow : payload < 2 ^ width := by
    rwa [← hsentinel]
  have hpayloadEq :=
    CompactBinaryNatTokenStreamTableau.payload_eq_extracted
      htableau hpayloadPow
  change payload = compactBinaryNatPayloadValue tokens at hpayloadEq
  have hextracted :=
    CompactBinaryNatTokenStreamTableau.extracted_valid htableau
  have hlength :=
    CompactBinaryNatExtractedTokenStreamValid.payloadLength_eq hextracted
  change width = (compactBinaryNatPayloadBits tokens).length at hlength
  have hcanonicalCode : compactAdditivePackedCode tokens =
      payload + sentinel := by
    change FoundationSuccinctFiniteConsistencyTarget.packBinaryString
      (compactBinaryNatPayloadBits tokens) = payload + sentinel
    rw [packBinaryString_eq_payload_add_sentinel]
    change compactBinaryNatPayloadValue tokens +
      2 ^ (compactBinaryNatPayloadBits tokens).length = payload + sentinel
    rw [← hpayloadEq, ← hlength, ← hsentinel]
  exact hcode.trans hcanonicalCode.symm

theorem CompactCanonicalPackedTokenStreamTableauAtWidth.decode
    {code tokenCount tokenTable offsetTable width : Nat}
    (hvalid : CompactCanonicalPackedTokenStreamTableauAtWidth
      code tokenCount tokenTable offsetTable width) :
    compactPackedTokenStream code = some
      (compactCanonicalPackedTokenStreamTableauAtWidthTokens
        tokenCount tokenTable width) := by
  rw [hvalid.code_eq_canonical]
  exact compactPackedTokenStream_additivePackedCode _

theorem CompactCanonicalPackedTokenStreamTableauAtWidth.packedPayloadLength_eq
    {code tokenCount tokenTable offsetTable width : Nat}
    (hvalid : CompactCanonicalPackedTokenStreamTableauAtWidth
      code tokenCount tokenTable offsetTable width) :
    FoundationSuccinctFiniteConsistencyTarget.packedPayloadLength code =
      width := by
  have hcode := hvalid.code_eq_canonical
  rcases hvalid with
    ⟨payload, _hpayloadCode, _hwidthCode, sentinel, _hsentinelCode,
      _hsentinel, _hpayload, _hcode, htableau⟩
  let tokens := compactCanonicalPackedTokenStreamTableauAtWidthTokens
    tokenCount tokenTable width
  have hextracted :=
    CompactBinaryNatTokenStreamTableau.extracted_valid htableau
  have hlength :=
    CompactBinaryNatExtractedTokenStreamValid.payloadLength_eq hextracted
  change width = (compactBinaryNatPayloadBits tokens).length at hlength
  rw [hcode]
  unfold FoundationSuccinctFiniteConsistencyTarget.packedPayloadLength
  rw [compactAdditivePackedCode_size]
  change compactAdditiveTokenBitLength tokens = width
  simpa [compactAdditiveTokenBitLength, compactBinaryNatPayloadBits] using
    hlength.symm

theorem compactCanonicalPackedTokenStreamTableauAtWidth_entry
    (tokenCount tokenTable width index : Nat)
    (hindex : index < tokenCount) :
    CompactFixedWidthEntry tokenTable width index
      ((compactCanonicalPackedTokenStreamTableauAtWidthTokens
        tokenCount tokenTable width).getI index) := by
  rw [compactCanonicalPackedTokenStreamTableauAtWidthTokens]
  rw [List.getI_eq_getElem _ (by simp [hindex])]
  simp only [compactFixedWidthTableValues, List.getElem_map,
    List.getElem_range]
  exact compactFixedWidthTableValue_entry tokenTable width index

theorem compactCanonicalPackedTokenStreamTableauAtWidth_canonical
    (tokens : List Nat) :
    let width := (compactBinaryNatPayloadBits tokens).length
    CompactCanonicalPackedTokenStreamTableauAtWidth
      (compactAdditivePackedCode tokens)
      tokens.length
      (compactFixedWidthTableCode width tokens)
      (compactFixedWidthTableCode width
        (compactBinaryNatTokenOffsets tokens))
      width := by
  let width := (compactBinaryNatPayloadBits tokens).length
  let payload := compactBinaryNatPayloadValue tokens
  let sentinel := 2 ^ width
  let code := compactAdditivePackedCode tokens
  have hcode : code = payload + sentinel := by
    change FoundationSuccinctFiniteConsistencyTarget.packBinaryString
      (compactBinaryNatPayloadBits tokens) =
        compactBinaryNatPayloadValue tokens + 2 ^ width
    exact packBinaryString_eq_payload_add_sentinel
      (compactBinaryNatPayloadBits tokens)
  have hpayload : payload < sentinel :=
    natOfBitsList_lt_two_pow_length
      (compactBinaryNatPayloadBits tokens)
  have hsentinelCode : sentinel ≤ code := by omega
  have hpayloadCode : payload ≤ code := by omega
  have hwidthCode : width ≤ code := by
    exact (Nat.le_of_lt width.lt_two_pow_self).trans hsentinelCode
  refine ⟨payload, hpayloadCode, hwidthCode, sentinel, hsentinelCode,
    rfl, hpayload, hcode, ?_⟩
  exact compactBinaryNatTokenStreamTableau_canonical tokens

#print axioms compactCanonicalPackedTokenStreamTableauAtWidthDef_spec
#print axioms compactCanonicalPackedTokenStreamTableauAtWidthDef_sigmaZero
#print axioms CompactCanonicalPackedTokenStreamTableauAtWidth.to_unexposed
#print axioms CompactCanonicalPackedTokenStreamTableauAtWidth.code_eq_canonical
#print axioms CompactCanonicalPackedTokenStreamTableauAtWidth.decode
#print axioms
  CompactCanonicalPackedTokenStreamTableauAtWidth.packedPayloadLength_eq
#print axioms compactCanonicalPackedTokenStreamTableauAtWidth_entry
#print axioms compactCanonicalPackedTokenStreamTableauAtWidth_canonical

end FoundationCompactNumericListedDirectVerifierAcceptedTraceInputTableau
