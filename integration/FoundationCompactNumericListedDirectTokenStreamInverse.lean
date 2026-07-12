import integration.FoundationCompactNumericListedDirectTokenStreamTableau

/-!
# Inverse extraction for the direct token-stream tableau

This module proves that a valid fixed-width tableau determines one canonical
token stream.  Public codes with redundant high zero bits are first normalized;
the normalization does not increase their honest binary length.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTokenStreamInverse

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau

def compactFixedWidthTableValue
    (table width index : Nat) : Nat :=
  FoundationCompactVerifierBitCostPrimitives.natOfBitsList <|
    (List.range width).map fun bitIndex =>
      table.testBit (index * width + bitIndex)

theorem compactFixedWidthTableValue_testBit
    (table width index bitIndex : Nat) (hbitIndex : bitIndex < width) :
    (compactFixedWidthTableValue table width index).testBit bitIndex =
      table.testBit (index * width + bitIndex) := by
  rw [compactFixedWidthTableValue,
    natOfBitsList_testBit_eq_getI]
  rw [List.getI_eq_getElem _ (by simpa using hbitIndex)]
  simp

theorem CompactFixedWidthEntry.value_eq_tableValue
    {table width index value : Nat}
    (hentry : CompactFixedWidthEntry table width index value) :
    value = compactFixedWidthTableValue table width index := by
  apply Nat.eq_of_testBit_eq
  intro bitIndex
  by_cases hbitIndex : bitIndex < width
  · rw [compactFixedWidthTableValue_testBit _ _ _ _ hbitIndex]
    exact (hentry.2 bitIndex hbitIndex).symm
  · have hwidthLe : width ≤ bitIndex := Nat.le_of_not_gt hbitIndex
    have hvalueLt : value < 2 ^ bitIndex :=
      Nat.size_le.mp (hentry.1.trans hwidthLe)
    have htableValueSize :
        Nat.size (compactFixedWidthTableValue table width index) ≤ width := by
      rw [Nat.size_le]
      simpa [compactFixedWidthTableValue] using
        natOfBitsList_lt_two_pow_length
          ((List.range width).map fun bit =>
            table.testBit (index * width + bit))
    have htableValueLt :
        compactFixedWidthTableValue table width index < 2 ^ bitIndex :=
      Nat.size_le.mp (htableValueSize.trans hwidthLe)
    rw [Nat.testBit_eq_false_of_lt hvalueLt,
      Nat.testBit_eq_false_of_lt htableValueLt]

def compactFixedWidthTableValues
    (table width count : Nat) : List Nat :=
  (List.range count).map fun index =>
    compactFixedWidthTableValue table width index

@[simp] theorem compactFixedWidthTableValues_length
    (table width count : Nat) :
    (compactFixedWidthTableValues table width count).length = count := by
  simp [compactFixedWidthTableValues]

theorem compactFixedWidthTableValues_getI
    (table width count index : Nat) (hindex : index < count) :
    (compactFixedWidthTableValues table width count).getI index =
      compactFixedWidthTableValue table width index := by
  rw [List.getI_eq_getElem _ (by simpa using hindex)]
  simp [compactFixedWidthTableValues]

def CompactBinaryNatExtractedTokenStreamValid
    (payload payloadLength tokenCount tokenTable offsetTable : Nat) : Prop :=
  let tokens := compactFixedWidthTableValues
    tokenTable payloadLength tokenCount
  let offsets := compactFixedWidthTableValues
    offsetTable payloadLength (tokenCount + 1)
  offsets.getI 0 = 0 ∧
    offsets.getI tokenCount = payloadLength ∧
    ∀ index < tokenCount,
      CompactBinaryNatTokenSegment payload
        (offsets.getI index) (tokens.getI index)
        (offsets.getI (index + 1))

theorem CompactBinaryNatTokenStreamTableau.extracted_valid
    {payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat}
    (htableau : CompactBinaryNatTokenStreamTableau
      payload payloadLength sentinel tokenCount tokenTable offsetTable) :
    CompactBinaryNatExtractedTokenStreamValid
      payload payloadLength tokenCount tokenTable offsetTable := by
  rcases htableau with ⟨_, _, hzero, hfinal, hrows⟩
  simp only [CompactBinaryNatExtractedTokenStreamValid]
  have hzeroValue := CompactFixedWidthEntry.value_eq_tableValue hzero
  have hfinalValue := CompactFixedWidthEntry.value_eq_tableValue hfinal
  refine ⟨?_, ?_, ?_⟩
  · rw [compactFixedWidthTableValues_getI _ _ _ 0 (by omega)]
    exact hzeroValue.symm
  · rw [compactFixedWidthTableValues_getI _ _ _ tokenCount (by omega)]
    exact hfinalValue.symm
  · intro index hindex
    rcases hrows index hindex with
      ⟨token, _, offset, _, next, _, htoken, hoffset, hnext, hsegment⟩
    have htokenValue := CompactFixedWidthEntry.value_eq_tableValue htoken
    have hoffsetValue := CompactFixedWidthEntry.value_eq_tableValue hoffset
    have hnextValue := CompactFixedWidthEntry.value_eq_tableValue hnext
    rw [compactFixedWidthTableValues_getI _ _ _ index hindex]
    rw [compactFixedWidthTableValues_getI _ _ _ index (by omega)]
    rw [compactFixedWidthTableValues_getI _ _ _ (index + 1) (by omega)]
    simpa [htokenValue, hoffsetValue, hnextValue] using hsegment

theorem CompactBinaryNatTokenSegment.testBit_eq_of_interval
    {left right offset token next bitIndex : Nat}
    (hleft : CompactBinaryNatTokenSegment left offset token next)
    (hright : CompactBinaryNatTokenSegment right offset token next)
    (hlower : offset ≤ bitIndex) (hupper : bitIndex < next) :
    left.testBit bitIndex = right.testBit bitIndex := by
  rcases hleft with ⟨hleftNext, hleftBits, hleftZero, hleftOne⟩
  rcases hright with ⟨hrightNext, hrightBits, hrightZero, hrightOne⟩
  let delta := bitIndex - offset
  have hbitIndex : bitIndex = offset + delta := by
    simp [delta, Nat.add_sub_of_le hlower]
  have hdelta : delta < 2 * Nat.size token + 2 := by
    omega
  by_cases hdata : delta < 2 * Nat.size token
  · rcases Nat.even_or_odd' delta with ⟨index, hdeltaEven | hdeltaOdd⟩
    · have hindex : index < Nat.size token := by omega
      have hposition : bitIndex = offset + 2 * index := by omega
      rw [hposition]
      exact (hleftBits index hindex).1.trans
        (hrightBits index hindex).1.symm
    · have hindex : index < Nat.size token := by omega
      have hposition : bitIndex = offset + 2 * index + 1 := by omega
      rw [hposition]
      exact (hleftBits index hindex).2.trans
        (hrightBits index hindex).2.symm
  · have hterminator :
        delta = 2 * Nat.size token ∨
          delta = 2 * Nat.size token + 1 := by
      omega
    rcases hterminator with hdeltaZero | hdeltaOne
    · have hposition : bitIndex = offset + 2 * Nat.size token := by
        omega
      rw [hposition, hleftZero, hrightZero]
    · have hposition :
          bitIndex = offset + 2 * Nat.size token + 1 := by
        omega
      rw [hposition, hleftOne, hrightOne]

theorem compactBinaryNatTokenOffsets_cover
    (tokens : List Nat) (bitIndex : Nat)
    (hbitIndex : bitIndex < (compactBinaryNatPayloadBits tokens).length) :
    ∃ index, index < tokens.length ∧
      (compactBinaryNatTokenOffsets tokens).getI index ≤ bitIndex ∧
      bitIndex <
        (compactBinaryNatTokenOffsets tokens).getI (index + 1) := by
  induction tokens generalizing bitIndex with
  | nil => simp at hbitIndex
  | cons token tokens ih =>
      let width := compactBinaryNatTokenWidth token
      have hpayloadLength :
          (compactBinaryNatPayloadBits (token :: tokens)).length =
            width + (compactBinaryNatPayloadBits tokens).length := by
        rw [compactBinaryNatPayloadBits_cons, List.length_append]
        rw [← compactBinaryNatTokenWidth_eq_code_length]
      by_cases hhead : bitIndex < width
      · refine ⟨0, by simp, ?_, ?_⟩
        · simp [compactBinaryNatTokenOffsets]
        · rw [compactBinaryNatTokenOffsets_getI_succ
            token tokens 0 (by simp)]
          simpa [width, compactBinaryNatTokenOffsets] using hhead
      · have hwidthLe : width ≤ bitIndex := Nat.le_of_not_gt hhead
        let tailBit := bitIndex - width
        have hbitIndexEq : bitIndex = width + tailBit := by
          simp [tailBit, Nat.add_sub_of_le hwidthLe]
        have htailBit :
            tailBit < (compactBinaryNatPayloadBits tokens).length := by
          rw [hpayloadLength] at hbitIndex
          omega
        rcases ih tailBit htailBit with
          ⟨index, hindex, hlower, hupper⟩
        have hcurrentIndex :
            index < (compactBinaryNatTokenOffsets tokens).length := by
          rw [compactBinaryNatTokenOffsets_length]
          omega
        have hnextIndex :
            index + 1 < (compactBinaryNatTokenOffsets tokens).length := by
          rw [compactBinaryNatTokenOffsets_length]
          omega
        refine ⟨index + 1, by simp; omega, ?_, ?_⟩
        · rw [compactBinaryNatTokenOffsets_getI_succ
            token tokens index hcurrentIndex]
          omega
        · rw [show index + 1 + 1 = (index + 1) + 1 by rfl]
          rw [compactBinaryNatTokenOffsets_getI_succ
            token tokens (index + 1) hnextIndex]
          omega

theorem CompactBinaryNatExtractedTokenStreamValid.offset_eq_canonical
    {payload payloadLength tokenCount tokenTable offsetTable : Nat}
    (hvalid : CompactBinaryNatExtractedTokenStreamValid
      payload payloadLength tokenCount tokenTable offsetTable)
    (index : Nat) (hindex : index ≤ tokenCount) :
    let tokens := compactFixedWidthTableValues
      tokenTable payloadLength tokenCount
    let offsets := compactFixedWidthTableValues
      offsetTable payloadLength (tokenCount + 1)
    offsets.getI index =
      (compactBinaryNatTokenOffsets tokens).getI index := by
  simp only [CompactBinaryNatExtractedTokenStreamValid] at hvalid
  let tokens := compactFixedWidthTableValues
    tokenTable payloadLength tokenCount
  let offsets := compactFixedWidthTableValues
    offsetTable payloadLength (tokenCount + 1)
  change offsets.getI index =
    (compactBinaryNatTokenOffsets tokens).getI index
  rcases hvalid with ⟨hzero, _, hrows⟩
  change (∀ index < tokenCount,
    CompactBinaryNatTokenSegment payload
      (offsets.getI index) (tokens.getI index)
      (offsets.getI (index + 1))) at hrows
  revert hindex
  induction index with
  | zero =>
      intro _
      simpa [tokens, offsets] using hzero
  | succ index ih =>
      intro hindex
      have hindexLt : index < tokenCount := by omega
      have hprevious := ih (by omega)
      have hsegment := hrows index hindexLt
      have hcanonical := compactBinaryNatPayloadValue_segment
        tokens index (by simpa [tokens] using hindexLt)
      have hsegmentNext := hsegment.1
      have hcanonicalNext := hcanonical.1
      omega

theorem CompactBinaryNatExtractedTokenStreamValid.payloadLength_eq
    {payload payloadLength tokenCount tokenTable offsetTable : Nat}
    (hvalid : CompactBinaryNatExtractedTokenStreamValid
      payload payloadLength tokenCount tokenTable offsetTable) :
    let tokens := compactFixedWidthTableValues
      tokenTable payloadLength tokenCount
    payloadLength = (compactBinaryNatPayloadBits tokens).length := by
  have hoffsetEq :=
    CompactBinaryNatExtractedTokenStreamValid.offset_eq_canonical
      hvalid tokenCount (by rfl)
  let tokens := compactFixedWidthTableValues
    tokenTable payloadLength tokenCount
  let offsets := compactFixedWidthTableValues
    offsetTable payloadLength (tokenCount + 1)
  simp only [CompactBinaryNatExtractedTokenStreamValid] at hvalid
  rcases hvalid with ⟨_, hfinal, _⟩
  change offsets.getI tokenCount = payloadLength at hfinal
  change offsets.getI tokenCount =
    (compactBinaryNatTokenOffsets tokens).getI tokenCount at hoffsetEq
  have htokensLength : tokens.length = tokenCount := by
    simp [tokens]
  have hcanonicalLength := compactBinaryNatPayloadBits_length tokens
  rw [htokensLength] at hcanonicalLength
  change payloadLength = (compactBinaryNatPayloadBits tokens).length
  omega

theorem CompactBinaryNatTokenStreamTableau.payload_eq_extracted
    {payload payloadLength sentinel tokenCount tokenTable offsetTable : Nat}
    (htableau : CompactBinaryNatTokenStreamTableau
      payload payloadLength sentinel tokenCount tokenTable offsetTable)
    (hpayload : payload < 2 ^ payloadLength) :
    let tokens := compactFixedWidthTableValues
      tokenTable payloadLength tokenCount
    payload = compactBinaryNatPayloadValue tokens := by
  have hvalid :=
    CompactBinaryNatTokenStreamTableau.extracted_valid htableau
  have hvalidForOffsets := hvalid
  have hlength :=
    CompactBinaryNatExtractedTokenStreamValid.payloadLength_eq hvalid
  let tokens := compactFixedWidthTableValues
    tokenTable payloadLength tokenCount
  let offsets := compactFixedWidthTableValues
    offsetTable payloadLength (tokenCount + 1)
  change payloadLength = (compactBinaryNatPayloadBits tokens).length at hlength
  have htokensLength : tokens.length = tokenCount := by
    simp [tokens]
  simp only [CompactBinaryNatExtractedTokenStreamValid] at hvalid
  change offsets.getI 0 = 0 ∧
    offsets.getI tokenCount = payloadLength ∧
    ∀ index < tokenCount,
      CompactBinaryNatTokenSegment payload
        (offsets.getI index) (tokens.getI index)
        (offsets.getI (index + 1)) at hvalid
  rcases hvalid with ⟨_, _, hrows⟩
  change payload = compactBinaryNatPayloadValue tokens
  apply Nat.eq_of_testBit_eq
  intro bitIndex
  by_cases hbitIndex : bitIndex < payloadLength
  · have hbitCanonical :
        bitIndex < (compactBinaryNatPayloadBits tokens).length := by
      rwa [← hlength]
    rcases compactBinaryNatTokenOffsets_cover
      tokens bitIndex hbitCanonical with
      ⟨index, hindex, hlower, hupper⟩
    have hindexCount : index < tokenCount := by
      rw [← htokensLength]
      exact hindex
    have hnextCount : index + 1 ≤ tokenCount := by
      omega
    have hoffset :=
      CompactBinaryNatExtractedTokenStreamValid.offset_eq_canonical
        hvalidForOffsets index (by omega)
    have hnext :=
      CompactBinaryNatExtractedTokenStreamValid.offset_eq_canonical
        hvalidForOffsets (index + 1) hnextCount
    change offsets.getI index =
      (compactBinaryNatTokenOffsets tokens).getI index at hoffset
    change offsets.getI (index + 1) =
      (compactBinaryNatTokenOffsets tokens).getI (index + 1) at hnext
    have hpayloadSegment := hrows index hindexCount
    rw [hoffset, hnext] at hpayloadSegment
    have hcanonicalSegment := compactBinaryNatPayloadValue_segment
      tokens index hindex
    exact CompactBinaryNatTokenSegment.testBit_eq_of_interval
      hpayloadSegment hcanonicalSegment hlower hupper
  · have hlengthLe : payloadLength ≤ bitIndex :=
      Nat.le_of_not_gt hbitIndex
    have hpayloadSize : Nat.size payload ≤ payloadLength :=
      Nat.size_le.mpr hpayload
    have hpayloadBitLt : payload < 2 ^ bitIndex :=
      Nat.size_le.mp (hpayloadSize.trans hlengthLe)
    have hcanonicalLt :
        compactBinaryNatPayloadValue tokens < 2 ^ payloadLength := by
      change FoundationCompactVerifierBitCostPrimitives.natOfBitsList
          (compactBinaryNatPayloadBits tokens) < 2 ^ payloadLength
      rw [hlength]
      exact natOfBitsList_lt_two_pow_length
        (compactBinaryNatPayloadBits tokens)
    have hcanonicalSize :
        Nat.size (compactBinaryNatPayloadValue tokens) ≤ payloadLength :=
      Nat.size_le.mpr hcanonicalLt
    have hcanonicalBitLt :
        compactBinaryNatPayloadValue tokens < 2 ^ bitIndex :=
      Nat.size_le.mp (hcanonicalSize.trans hlengthLe)
    rw [Nat.testBit_eq_false_of_lt hpayloadBitLt,
      Nat.testBit_eq_false_of_lt hcanonicalBitLt]

def CompactCanonicalPackedTokenStreamTableau
    (code tokenCount tokenTable offsetTable : Nat) : Prop :=
  ∃ payload, payload ≤ code ∧
  ∃ payloadLength, payloadLength ≤ code ∧
  ∃ sentinel, sentinel ≤ code ∧
    sentinel = 2 ^ payloadLength ∧
    payload < sentinel ∧
    code = payload + sentinel ∧
    CompactBinaryNatTokenStreamTableau
      payload payloadLength sentinel tokenCount tokenTable offsetTable

def compactCanonicalPackedTokenStreamTableauDef : 𝚺₀.Semisentence 4 := .mkSigma
  “code tokenCount tokenTable offsetTable.
    ∃ payload <⁺ code,
    ∃ payloadLength <⁺ code,
    ∃ sentinel <⁺ code,
      !expDef sentinel payloadLength ∧
      payload < sentinel ∧
      code = payload + sentinel ∧
      !(compactBinaryNatTokenStreamTableauDef)
        payload payloadLength sentinel tokenCount tokenTable offsetTable”

@[simp] theorem compactCanonicalPackedTokenStreamTableauDef_spec
    (code tokenCount tokenTable offsetTable : Nat) :
    compactCanonicalPackedTokenStreamTableauDef.val.Evalb
        ![code, tokenCount, tokenTable, offsetTable] ↔
      CompactCanonicalPackedTokenStreamTableau
        code tokenCount tokenTable offsetTable := by
  simp [compactCanonicalPackedTokenStreamTableauDef,
    CompactCanonicalPackedTokenStreamTableau,
    compactBinaryNatTokenStreamTableauDef,
    CompactBinaryNatTokenStreamTableau,
    foundationNatLE_iff_standard]

theorem compactCanonicalPackedTokenStreamTableauDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCanonicalPackedTokenStreamTableauDef.val := by
  simp [compactCanonicalPackedTokenStreamTableauDef]

theorem CompactCanonicalPackedTokenStreamTableau.exists_canonical_tokens
    {code tokenCount tokenTable offsetTable : Nat}
    (hvalid : CompactCanonicalPackedTokenStreamTableau
      code tokenCount tokenTable offsetTable) :
    ∃ tokens : List Nat,
      tokens.length = tokenCount ∧
      code = FoundationCompactAdditiveTokenCodec.compactAdditivePackedCode
        tokens := by
  rcases hvalid with
    ⟨payload, _, payloadLength, _, sentinel, _, hsentinel,
      hpayload, hcode, htableau⟩
  let tokens := compactFixedWidthTableValues
    tokenTable payloadLength tokenCount
  have hpayloadPow : payload < 2 ^ payloadLength := by
    rwa [← hsentinel]
  have hpayloadEq :=
    CompactBinaryNatTokenStreamTableau.payload_eq_extracted
      htableau hpayloadPow
  change payload = compactBinaryNatPayloadValue tokens at hpayloadEq
  have hextracted :=
    CompactBinaryNatTokenStreamTableau.extracted_valid htableau
  have hlength :=
    CompactBinaryNatExtractedTokenStreamValid.payloadLength_eq hextracted
  change payloadLength = (compactBinaryNatPayloadBits tokens).length at hlength
  have hcanonicalCode :
      FoundationCompactAdditiveTokenCodec.compactAdditivePackedCode tokens =
        payload + sentinel := by
    change FoundationSuccinctFiniteConsistencyTarget.packBinaryString
      (compactBinaryNatPayloadBits tokens) = payload + sentinel
    rw [packBinaryString_eq_payload_add_sentinel]
    change compactBinaryNatPayloadValue tokens +
      2 ^ (compactBinaryNatPayloadBits tokens).length = payload + sentinel
    rw [← hpayloadEq, ← hlength, ← hsentinel]
  refine ⟨tokens, by simp [tokens], ?_⟩
  exact hcode.trans hcanonicalCode.symm

theorem compactCanonicalPackedTokenStreamTableau_canonical
    (tokens : List Nat) :
    let payloadLength := (compactBinaryNatPayloadBits tokens).length
    CompactCanonicalPackedTokenStreamTableau
      (FoundationCompactAdditiveTokenCodec.compactAdditivePackedCode tokens)
      tokens.length
      (compactFixedWidthTableCode payloadLength tokens)
      (compactFixedWidthTableCode payloadLength
        (compactBinaryNatTokenOffsets tokens)) := by
  let payloadLength := (compactBinaryNatPayloadBits tokens).length
  let payload := compactBinaryNatPayloadValue tokens
  let sentinel := 2 ^ payloadLength
  let code := FoundationCompactAdditiveTokenCodec.compactAdditivePackedCode tokens
  have hcode : code = payload + sentinel := by
    change FoundationSuccinctFiniteConsistencyTarget.packBinaryString
      (compactBinaryNatPayloadBits tokens) =
        compactBinaryNatPayloadValue tokens + 2 ^ payloadLength
    exact packBinaryString_eq_payload_add_sentinel
      (compactBinaryNatPayloadBits tokens)
  have hpayload : payload < sentinel := by
    exact natOfBitsList_lt_two_pow_length
      (compactBinaryNatPayloadBits tokens)
  have hsentinelLe : sentinel ≤ code := by omega
  have hpayloadLe : payload ≤ code := by omega
  have hlengthLe : payloadLength ≤ code :=
    (Nat.le_of_lt payloadLength.lt_two_pow_self).trans hsentinelLe
  refine ⟨payload, hpayloadLe, payloadLength, hlengthLe,
    sentinel, hsentinelLe, rfl, hpayload, hcode, ?_⟩
  exact compactBinaryNatTokenStreamTableau_canonical tokens

theorem exists_canonicalPackedTokenStreamTableau_iff
    (code : Nat) :
    (∃ tokenCount tokenTable offsetTable,
      CompactCanonicalPackedTokenStreamTableau
        code tokenCount tokenTable offsetTable) ↔
      ∃ tokens : List Nat,
        code = FoundationCompactAdditiveTokenCodec.compactAdditivePackedCode
          tokens := by
  constructor
  · rintro ⟨tokenCount, tokenTable, offsetTable, htableau⟩
    rcases htableau.exists_canonical_tokens with
      ⟨tokens, _, hcode⟩
    exact ⟨tokens, hcode⟩
  · rintro ⟨tokens, rfl⟩
    let payloadLength := (compactBinaryNatPayloadBits tokens).length
    exact ⟨tokens.length,
      compactFixedWidthTableCode payloadLength tokens,
      compactFixedWidthTableCode payloadLength
        (compactBinaryNatTokenOffsets tokens),
      compactCanonicalPackedTokenStreamTableau_canonical tokens⟩

theorem CompactCanonicalPackedTokenStreamTableau.decode
    {code tokenCount tokenTable offsetTable : Nat}
    (hvalid : CompactCanonicalPackedTokenStreamTableau
      code tokenCount tokenTable offsetTable) :
    ∃ tokens : List Nat,
      tokens.length = tokenCount ∧
      FoundationCompactListedPackedBitTokenSynchronization.compactPackedTokenStream
        code = some tokens := by
  rcases hvalid.exists_canonical_tokens with
    ⟨tokens, hlength, hcode⟩
  refine ⟨tokens, hlength, ?_⟩
  rw [hcode]
  exact FoundationCompactAdditiveTokenCodec.compactPackedTokenStream_additivePackedCode
    tokens

theorem compactPackedTokenStream_to_canonical_tableau
    {code : Nat} {tokens : List Nat}
    (hdecode :
      FoundationCompactListedPackedBitTokenSynchronization.compactPackedTokenStream
        code = some tokens) :
    ∃ normalizedCode tokenTable offsetTable,
      normalizedCode =
        FoundationCompactAdditiveTokenCodec.compactAdditivePackedCode tokens ∧
      Nat.size normalizedCode ≤ Nat.size code ∧
      CompactCanonicalPackedTokenStreamTableau
        normalizedCode tokens.length tokenTable offsetTable := by
  rcases
      (FoundationCompactListedPackedBitTokenSynchronization.compactPackedTokenStream_success_iff
        code tokens).mp hdecode with
    ⟨payloadBits, hpayloadBits, htokens⟩
  have hcanonicalLength :=
    FoundationCompactBinaryNatStreamSynchronization.binaryNatTokensDecode_canonical_bit_length
      htokens
  have hpack :=
    (FoundationCompactListedVerifierArithmeticInput.packedPayloadBits_eq_some_iff
      code payloadBits).mp hpayloadBits
  let normalizedCode :=
    FoundationCompactAdditiveTokenCodec.compactAdditivePackedCode tokens
  let payloadLength := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode payloadLength tokens
  let offsetTable := compactFixedWidthTableCode payloadLength
    (compactBinaryNatTokenOffsets tokens)
  have hsize : Nat.size normalizedCode ≤ Nat.size code := by
    rw [show normalizedCode =
      FoundationCompactAdditiveTokenCodec.compactAdditivePackedCode tokens by
      rfl]
    rw [FoundationCompactAdditiveTokenCodec.compactAdditivePackedCode_size]
    rw [← hpack,
      FoundationSuccinctFiniteConsistencyTarget.size_packBinaryString]
    simpa [FoundationCompactAdditiveTokenCodec.compactAdditiveTokenBitLength,
      compactBinaryNatPayloadBits] using hcanonicalLength
  refine ⟨normalizedCode, tokenTable, offsetTable, rfl, hsize, ?_⟩
  exact compactCanonicalPackedTokenStreamTableau_canonical tokens

#print axioms CompactFixedWidthEntry.value_eq_tableValue
#print axioms CompactBinaryNatTokenStreamTableau.extracted_valid
#print axioms CompactBinaryNatTokenSegment.testBit_eq_of_interval
#print axioms compactBinaryNatTokenOffsets_cover
#print axioms CompactBinaryNatExtractedTokenStreamValid.offset_eq_canonical
#print axioms CompactBinaryNatTokenStreamTableau.payload_eq_extracted
#print axioms compactCanonicalPackedTokenStreamTableauDef_spec
#print axioms compactCanonicalPackedTokenStreamTableauDef_sigmaZero
#print axioms CompactCanonicalPackedTokenStreamTableau.exists_canonical_tokens
#print axioms compactCanonicalPackedTokenStreamTableau_canonical
#print axioms exists_canonicalPackedTokenStreamTableau_iff
#print axioms CompactCanonicalPackedTokenStreamTableau.decode
#print axioms compactPackedTokenStream_to_canonical_tableau

end FoundationCompactNumericListedDirectTokenStreamInverse
