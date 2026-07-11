import integration.FoundationCompactNumericListedStateBounds
import integration.FoundationCompactBinaryNatStreamSynchronization

/-!
# Honest bounds for the remaining compact direct-trace components

This module bounds each semantic component of a valid direct trace by the
two public packed inputs.  It starts with the shared bit-stream-to-token-list
weight bridge used by both public token streams.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTraceBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactListedVerifierArithmeticInput
open FoundationCompactBinaryNatStreamMachine
open FoundationCompactBinaryNatStreamSynchronization
open FoundationCompactListedPackedBitTokenSynchronization
open FoundationCompactPackedTokenStreamDirectTrace
open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedStateBounds
open FoundationCompactNumericListedParseDecomposition
open FoundationCompactParserDirectTrace
open FoundationCompactProofTokenMachine
open FoundationCompactProofTokenMachineInversion
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedRootFieldsDirectTrace
open FoundationCompactNumericSyntaxValueParser

/-- Honest typed-list weight budget for tokens decoded from a bit stream of
length at most `bitLength`. -/
def compactNumericDecodedTokenListWeightBound (bitLength : Nat) : Nat :=
  Nat.size bitLength + 1 + bitLength

theorem compactNumericDecodedTokenListWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericDecodedTokenListWeightBound left <=
      compactNumericDecodedTokenListWeightBound right := by
  have hsize := Nat.size_le_size h
  unfold compactNumericDecodedTokenListWeightBound
  omega

theorem compactAdditiveValueWeight_natList_elements_sum
    (tokens : List Nat) :
    (tokens.map compactAdditiveValueWeight).sum =
      compactAdditiveTokenWeight tokens := by
  induction tokens with
  | nil => simp
  | cons token tokens ih =>
      rw [List.map_cons, List.sum_cons, compactAdditiveValueWeight_nat,
        compactAdditiveTokenWeight_cons, ih]

theorem compactAdditiveValueWeight_natList_le_of_tokensDecode
    {bits : List Bool} {tokens : List Nat} {suffix : List Bool}
    (hrelation : BinaryNatTokensDecode tokens bits suffix) :
    compactAdditiveValueWeight tokens <=
      compactNumericDecodedTokenListWeightBound bits.length := by
  have htokenLengthRaw := binaryNatTokensDecode_length hrelation
  have htokenLength : tokens.length <= bits.length := by omega
  have hcanonicalRaw :=
    binaryNatTokensDecode_canonical_bit_length hrelation
  have hcanonical : (tokens.flatMap binaryNatCode).length <=
      bits.length := by omega
  have hbitLength : compactAdditiveTokenBitLength tokens <= bits.length := by
    simpa [compactAdditiveTokenBitLength] using hcanonical
  rw [compactAdditiveTokenBitLength_eq_two_mul_weight] at hbitLength
  have htokenWeight : compactAdditiveTokenWeight tokens <= bits.length := by
    omega
  have hsize := Nat.size_le_size htokenLength
  have helements := compactAdditiveValueWeight_natList_elements_sum tokens
  rw [compactAdditiveValueWeight_list, helements]
  unfold compactNumericDecodedTokenListWeightBound
  omega

theorem compactAdditiveValueWeight_natList_le_of_decodeBinaryNatStream
    {bits : List Bool} {tokens : List Nat}
    (hdecode : decodeBinaryNatStream bits = some tokens) :
    compactAdditiveValueWeight tokens <=
      compactNumericDecodedTokenListWeightBound bits.length := by
  have hrelation :=
    (decodeBinaryNatStream_success_iff bits tokens).mp hdecode
  exact compactAdditiveValueWeight_natList_le_of_tokensDecode hrelation

theorem compactPackedTokenStreamDirectTraceValid_decode
    {code : Nat} {tokens : List Nat}
    {trace : CompactPackedTokenStreamDirectTrace}
    (hvalid : CompactPackedTokenStreamDirectTraceValid code tokens trace) :
    decodeBinaryNatStream trace.1 = some tokens := by
  have hstream : compactPackedTokenStream code = some tokens :=
    (compactPackedTokenStream_eq_some_iff_exists_directTrace
      code tokens).mpr ⟨trace, hvalid⟩
  have hpayload : packedPayloadBits code = some trace.1 := by
    exact hvalid.1
  unfold compactPackedTokenStream at hstream
  rw [hpayload] at hstream
  simp only [Option.bind_some] at hstream
  rw [binaryNatStreamTokens_eq_decodeBinaryNatStream] at hstream
  exact hstream

theorem compactPackedTokenStreamDirectTraceValid_token_weight_le
    {code : Nat} {tokens : List Nat}
    {trace : CompactPackedTokenStreamDirectTrace}
    (hvalid : CompactPackedTokenStreamDirectTraceValid code tokens trace) :
    compactAdditiveValueWeight tokens <=
      compactNumericDecodedTokenListWeightBound (Nat.size code) := by
  have hdecode := compactPackedTokenStreamDirectTraceValid_decode hvalid
  have hraw :=
    compactAdditiveValueWeight_natList_le_of_decodeBinaryNatStream hdecode
  have hpayload : packedPayloadBits code = some trace.1 := hvalid.1
  have hpack := (packedPayloadBits_eq_some_iff code trace.1).mp hpayload
  have hlength : trace.1.length <= Nat.size code := by
    rw [← hpack, size_packBinaryString]
    omega
  exact hraw.trans
    (compactNumericDecodedTokenListWeightBound_mono hlength)

theorem compactNumericListedDirectTrace_certifiedTokens_weight_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight
        (compactNumericDirectTraceCertifiedTokens trace) <=
      compactNumericDecodedTokenListWeightBound (Nat.size code) := by
  unfold CompactNumericListedDirectTraceValid at hvalid
  exact compactPackedTokenStreamDirectTraceValid_token_weight_le hvalid.1

theorem compactNumericListedDirectTrace_formulaTokens_weight_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight
        (compactNumericDirectTraceFormulaTokens trace) <=
      compactNumericDecodedTokenListWeightBound (Nat.size formulaCode) := by
  unfold CompactNumericListedDirectTraceValid at hvalid
  exact compactPackedTokenStreamDirectTraceValid_token_weight_le hvalid.2.1

theorem compactNumericListedDirectTrace_formulaValue_weight_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight
        (compactNumericDirectTraceFormulaValue trace) <=
      compactNumericDecodedTokenListWeightBound (Nat.size formulaCode) := by
  unfold CompactNumericListedDirectTraceValid at hvalid
  have hvalue := hvalid.2.2.2.2.2.2.1
  unfold CompactNumericWholeFormulaResidualValid at hvalue
  rw [hvalue]
  exact compactPackedTokenStreamDirectTraceValid_token_weight_le hvalid.2.1

theorem compactListedProofNodeFieldsParser_tag_le_ten
    {tokens : List Nat} {tag : Nat} {fields : CompactNumericNodeFields}
    (hparser : compactListedProofNodeFieldsParser tokens =
      some (tag, fields)) :
    tag <= 10 := by
  cases tokens with
  | nil =>
      simp [compactListedProofNodeFieldsParser] at hparser
  | cons head tail =>
      by_cases h0 : head = 0
      · have hboth : compactNodeSequentFormulaFields 0 tail =
            some fields ∧ 0 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0,
            compactTagNumericNodeFields] using hparser
        omega
      by_cases h1 : head = 1
      · have hboth : compactNodeSequentClosedFormulaFields tail =
            some fields ∧ 1 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1,
            compactTagNumericNodeFields] using hparser
        omega
      by_cases h2 : head = 2
      · have hboth : compactNodeSequentOnlyFields tail = some fields ∧
            2 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2,
            compactTagNumericNodeFields] using hparser
        omega
      by_cases h3 : head = 3
      · have hboth : compactNodeSequentTwoFormulaFields 0 tail =
            some fields ∧ 3 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3,
            compactTagNumericNodeFields] using hparser
        omega
      by_cases h4 : head = 4
      · have hboth : compactNodeSequentTwoFormulaFields 0 tail =
            some fields ∧ 4 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            compactTagNumericNodeFields] using hparser
        omega
      by_cases h5 : head = 5
      · have hboth : compactNodeSequentFormulaFields 1 tail =
            some fields ∧ 5 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, compactTagNumericNodeFields] using hparser
        omega
      by_cases h6 : head = 6
      · have hboth : compactNodeSequentFormulaTermFields 1 0 tail =
            some fields ∧ 6 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, h6, compactTagNumericNodeFields] using hparser
        omega
      by_cases h7 : head = 7
      · have hboth : compactNodeSequentOnlyFields tail = some fields ∧
            7 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, h6, h7, compactTagNumericNodeFields] using hparser
        omega
      by_cases h8 : head = 8
      · have hboth : compactNodeSequentOnlyFields tail = some fields ∧
            8 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, h6, h7, h8, compactTagNumericNodeFields] using hparser
        omega
      by_cases h9 : head = 9
      · have hboth : compactNodeSequentFormulaFields 0 tail =
            some fields ∧ 9 = tag := by
          simpa [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
            h5, h6, h7, h8, h9, compactTagNumericNodeFields] using hparser
        omega
      simp [compactListedProofNodeFieldsParser, h0, h1, h2, h3, h4,
        h5, h6, h7, h8, h9] at hparser

theorem compactNumericListedDirectTraceValid_proofParser
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactProofTokenParser
        (compactNumericDirectTraceCertifiedTokens trace) =
      some (compactNumericDirectTraceParts trace).2.1 := by
  unfold CompactNumericListedDirectTraceValid at hvalid
  apply (compactProofTokenParser_eq_some_iff_exists_directTrace
    (compactNumericDirectTraceCertifiedTokens trace)
    (compactNumericDirectTraceParts trace).2.1).mpr
  exact ⟨compactNumericDirectTraceProofParserTrace trace,
    hvalid.2.2.1⟩

theorem compactNumericListedDirectTraceValid_rootParser
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactListedProofNodeFieldsParser
        (compactNumericDirectTraceParts trace).1 =
      some (compactNumericDirectTraceRoot trace) := by
  unfold CompactNumericListedDirectTraceValid at hvalid
  have hresidual := hvalid.2.2.2.2.2.1
  apply (compactListedProofNodeFieldsParser_eq_some_iff_exists_directTrace
    (compactNumericDirectTraceParts trace).1
    (compactNumericDirectTraceRoot trace)).mpr
  exact ⟨compactNumericDirectTraceRootBranchTrace trace,
    hresidual.2.1⟩

def compactNumericCertifiedPartsWeightBound (W : Nat) : Nat :=
  W + W + compactNumericNestedListWeightBound W

theorem compactNumericCertifiedPartsWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericCertifiedPartsWeightBound left <=
      compactNumericCertifiedPartsWeightBound right := by
  have hnested := compactNumericNestedListWeightBound_mono h
  unfold compactNumericCertifiedPartsWeightBound
  omega

theorem compactNumericNodeFieldsWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericNodeFieldsWeightBound left <=
      compactNumericNodeFieldsWeightBound right := by
  have hnested := compactNumericNestedListWeightBound_mono h
  have hscaled := Nat.mul_le_mul_left 4 h
  unfold compactNumericNodeFieldsWeightBound
  omega

theorem compactNumericVerifierTaskWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericVerifierTaskWeightBound left <=
      compactNumericVerifierTaskWeightBound right := by
  have hfields := compactNumericNodeFieldsWeightBound_mono h
  unfold compactNumericVerifierTaskWeightBound
  omega

theorem compactNumericListedDirectTrace_parts_components_weight_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight (compactNumericDirectTraceParts trace).1 <=
        compactAdditiveValueWeight
          (compactNumericDirectTraceCertifiedTokens trace) ∧
      compactAdditiveValueWeight
          (compactNumericDirectTraceParts trace).2.1 <=
        compactAdditiveValueWeight
          (compactNumericDirectTraceCertifiedTokens trace) ∧
      compactAdditiveValueWeight
          (compactNumericDirectTraceParts trace).2.2 <=
        compactNumericNestedListWeightBound
          (compactAdditiveValueWeight
            (compactNumericDirectTraceCertifiedTokens trace)) := by
  have hproofParser :=
    compactNumericListedDirectTraceValid_proofParser hvalid
  obtain ⟨tree, htokens⟩ :=
    (compactProofTokenParser_success_iff
      (compactNumericDirectTraceCertifiedTokens trace)
      (compactNumericDirectTraceParts trace).2.1).mp hproofParser
  have hfull := hvalid
  unfold CompactNumericListedDirectTraceValid at hfull
  have hresidual := hfull.2.2.2.2.2.1
  have hproofEq : (compactNumericDirectTraceParts trace).1 =
      compactListedProofTokens tree := by
    rw [hresidual.1, htokens, consumedTokenPrefix_append]
  have hproofInfix : compactListedProofTokens tree <:+:
      compactNumericDirectTraceCertifiedTokens trace := by
    rw [htokens]
    exact (List.prefix_append _ _).isInfix
  have hproofWeight :
      compactAdditiveValueWeight (compactNumericDirectTraceParts trace).1 <=
        compactAdditiveValueWeight
          (compactNumericDirectTraceCertifiedTokens trace) := by
    rw [hproofEq]
    exact compactAdditiveValueWeight_infix_le hproofInfix
  have hcertificateSuffix :
      (compactNumericDirectTraceParts trace).2.1 <:+
        compactNumericDirectTraceCertifiedTokens trace :=
    ⟨compactListedProofTokens tree, htokens.symm⟩
  have hcertificateWeight :
      compactAdditiveValueWeight
          (compactNumericDirectTraceParts trace).2.1 <=
        compactAdditiveValueWeight
          (compactNumericDirectTraceCertifiedTokens trace) :=
    compactAdditiveValueWeight_suffix_le hcertificateSuffix
  have hrootParser :=
    compactNumericListedDirectTraceValid_rootParser hvalid
  have hrootFieldsCurrent :=
    compactListedProofNodeFieldsParser_componentsWithin hrootParser
  have hrootFields := hrootFieldsCurrent.mono hproofWeight
  have hGamma : compactAdditiveValueWeight
        (compactNumericDirectTraceParts trace).2.2 <=
      compactNumericNestedListWeightBound
        (compactAdditiveValueWeight
          (compactNumericDirectTraceCertifiedTokens trace)) := by
    rw [hresidual.2.2]
    exact hrootFields.1
  exact ⟨hproofWeight, hcertificateWeight, hGamma⟩

theorem compactNumericListedDirectTrace_parts_weight_raw_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight (compactNumericDirectTraceParts trace) <=
      compactNumericCertifiedPartsWeightBound
        (compactAdditiveValueWeight
          (compactNumericDirectTraceCertifiedTokens trace)) := by
  rcases compactNumericListedDirectTrace_parts_components_weight_le hvalid with
    ⟨hproof, hcertificate, hGamma⟩
  rw [compactAdditiveValueWeight_prod,
    compactAdditiveValueWeight_prod]
  unfold compactNumericCertifiedPartsWeightBound
  omega

theorem compactNumericListedDirectTrace_parts_weight_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight (compactNumericDirectTraceParts trace) <=
      compactNumericCertifiedPartsWeightBound
        (compactNumericDecodedTokenListWeightBound (Nat.size code)) := by
  have hraw := compactNumericListedDirectTrace_parts_weight_raw_le hvalid
  have htokens :=
    compactNumericListedDirectTrace_certifiedTokens_weight_le hvalid
  exact hraw.trans (compactNumericCertifiedPartsWeightBound_mono htokens)

theorem compactNumericListedDirectTrace_root_weight_raw_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight (compactNumericDirectTraceRoot trace) <=
      compactNumericVerifierTaskWeightBound
        (compactAdditiveValueWeight
          (compactNumericDirectTraceCertifiedTokens trace)) := by
  have hrootParser :=
    compactNumericListedDirectTraceValid_rootParser hvalid
  have htag := compactListedProofNodeFieldsParser_tag_le_ten hrootParser
  have hparts :=
    compactNumericListedDirectTrace_parts_components_weight_le hvalid
  have hfieldsCurrent :=
    compactListedProofNodeFieldsParser_componentsWithin hrootParser
  have hfields := hfieldsCurrent.mono hparts.1
  exact (show CompactNumericVerifierTaskWithin
      (compactAdditiveValueWeight
        (compactNumericDirectTraceCertifiedTokens trace))
      (compactNumericDirectTraceRoot trace) from ⟨htag, hfields⟩).weight_le

theorem compactNumericListedDirectTrace_root_weight_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight (compactNumericDirectTraceRoot trace) <=
      compactNumericVerifierTaskWeightBound
        (compactNumericDecodedTokenListWeightBound (Nat.size code)) := by
  have hraw := compactNumericListedDirectTrace_root_weight_raw_le hvalid
  have htokens :=
    compactNumericListedDirectTrace_certifiedTokens_weight_le hvalid
  exact hraw.trans (compactNumericVerifierTaskWeightBound_mono htokens)

/-! ## Packed bit-stream state traces -/

/-- Exact source invariant for a binary-Nat stream state.  The second state
field is the reverse of a token prefix actually decoded from `initialBits`,
and the status can only report that same prefix. -/
def BinaryNatStreamStateSourceOf
    (initialBits : List Bool) (state : BinaryNatStreamState) : Prop :=
  ∃ decoded : List Nat,
    state.2.1 = decoded.reverse ∧
      BinaryNatTokensDecode decoded initialBits state.1 ∧
      (state.2.2 = none ∨ state.2.2 = some none ∨
        state.2.2 = some (some decoded))

theorem binaryNatStreamInitialState_source
    (bits : List Bool) :
    BinaryNatStreamStateSourceOf bits (binaryNatStreamInitialState bits) := by
  exact ⟨[], by simp [binaryNatStreamInitialState],
    BinaryNatTokensDecode.nil bits, by simp [binaryNatStreamInitialState]⟩

theorem binaryNatStreamStep_preserves_source
    (initialBits : List Bool) (state : BinaryNatStreamState)
    (hsource : BinaryNatStreamStateSourceOf initialBits state) :
    BinaryNatStreamStateSourceOf initialBits (binaryNatStreamStep state) := by
  rcases state with ⟨remaining, decodedRev, status⟩
  rcases hsource with ⟨decoded, hdecodedRev, hdecodePrefix, hstatus⟩
  change decodedRev = decoded.reverse at hdecodedRev
  change BinaryNatTokensDecode decoded initialBits remaining at hdecodePrefix
  cases status with
  | some result =>
      simpa [binaryNatStreamStep] using
        (show BinaryNatStreamStateSourceOf initialBits
          (remaining, decodedRev, some result) from
            ⟨decoded, hdecodedRev, hdecodePrefix, hstatus⟩)
  | none =>
      cases remaining with
      | nil =>
          change BinaryNatStreamStateSourceOf initialBits
            ([], decodedRev, some (some decodedRev.reverse))
          refine ⟨decoded, hdecodedRev, hdecodePrefix, ?_⟩
          right
          right
          simp [binaryNatStreamStep, binaryNatStreamRunningStep,
            hdecodedRev]
      | cons bit bits =>
          cases hdecode : decodeBinaryNat (bit :: bits) with
          | none =>
              simp only [binaryNatStreamStep, Option.isSome_none,
                Bool.false_eq_true, ↓reduceIte,
                binaryNatStreamRunningStep, List.cons_ne_nil,
                if_false, hdecode]
              change BinaryNatStreamStateSourceOf initialBits
                (bit :: bits, decodedRev, some none)
              refine ⟨decoded, hdecodedRev, hdecodePrefix, ?_⟩
              right
              left
              simp [binaryNatStreamStep, binaryNatStreamRunningStep, hdecode]
          | some parsed =>
              rcases parsed with ⟨token, suffix⟩
              simp only [binaryNatStreamStep, Option.isSome_none,
                Bool.false_eq_true, ↓reduceIte,
                binaryNatStreamRunningStep, List.cons_ne_nil,
                if_false, hdecode]
              change BinaryNatStreamStateSourceOf initialBits
                (suffix, token :: decodedRev, none)
              refine ⟨decoded ++ [token], ?_, ?_, ?_⟩
              · simp [hdecodedRev]
              · exact binaryNatTokensDecode_append hdecodePrefix
                  (.cons hdecode (.nil suffix))
              · left
                rfl

theorem binaryNatStream_iterate_preserves_source
    (initialBits : List Bool) (stepCount : Nat)
    (state : BinaryNatStreamState)
    (hsource : BinaryNatStreamStateSourceOf initialBits state) :
    BinaryNatStreamStateSourceOf initialBits
      ((binaryNatStreamStep^[stepCount]) state) := by
  induction stepCount generalizing state with
  | zero => simpa
  | succ stepCount ih =>
      rw [Function.iterate_succ_apply]
      exact ih _
        (binaryNatStreamStep_preserves_source initialBits state hsource)

theorem binaryNatStreamStateAt_source
    (bits : List Bool) (stepIndex : Nat) :
    BinaryNatStreamStateSourceOf bits
      (binaryNatStreamStateAt
        (binaryNatStreamInitialState bits) stepIndex) := by
  unfold binaryNatStreamStateAt
  exact binaryNatStream_iterate_preserves_source bits stepIndex _
    (binaryNatStreamInitialState_source bits)

theorem binaryNatStreamLocalTrace_member_source
    {bits : List Bool} {fuel : Nat}
    {states : List BinaryNatStreamState}
    (hvalid : BinaryNatStreamLocalTraceValid fuel
      (binaryNatStreamInitialState bits) states)
    {state : BinaryNatStreamState} (hstate : state ∈ states) :
    BinaryNatStreamStateSourceOf bits state := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical := binaryNatStreamLocalTraceValid_stateAt hvalid hle
  unfold binaryNatStreamTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = binaryNatStreamStateAt
      (binaryNatStreamInitialState bits) stepIndex :=
    Option.some.inj hcanonical
  rw [heq]
  exact binaryNatStreamStateAt_source bits stepIndex

def compactNumericBoolListWeightBound (lengthBound : Nat) : Nat :=
  Nat.size lengthBound + 1 + 2 * lengthBound

theorem compactNumericBoolListWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericBoolListWeightBound left <=
      compactNumericBoolListWeightBound right := by
  have hsize := Nat.size_le_size h
  have hscaled := Nat.mul_le_mul_left 2 h
  unfold compactNumericBoolListWeightBound
  omega

theorem compactAdditiveValueWeight_boolList_le
    {values : List Bool} {lengthBound : Nat}
    (hlength : values.length <= lengthBound) :
    compactAdditiveValueWeight values <=
      compactNumericBoolListWeightBound lengthBound := by
  have hraw := compactAdditiveValueWeight_list_le values 2
    (fun value _ => compactAdditiveValueWeight_bool_le value)
  have hsize := Nat.size_le_size hlength
  have hscaled := Nat.mul_le_mul_right 2 hlength
  unfold compactNumericBoolListWeightBound
  omega

theorem compactAdditiveValueWeight_reverse
    {alpha : Type*} [Primcodable alpha] [CompactAdditiveTokenCodec alpha]
    (values : List alpha) :
    compactAdditiveValueWeight values.reverse =
      compactAdditiveValueWeight values := by
  simp [compactAdditiveValueWeight_list]

def compactNumericBinaryNatStreamStateWeightBound
    (bitLength : Nat) : Nat :=
  compactNumericBoolListWeightBound bitLength +
    compactNumericDecodedTokenListWeightBound bitLength +
    (4 + compactNumericDecodedTokenListWeightBound bitLength)

theorem compactNumericBinaryNatStreamStateWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericBinaryNatStreamStateWeightBound left <=
      compactNumericBinaryNatStreamStateWeightBound right := by
  have hbool := compactNumericBoolListWeightBound_mono h
  have htokens := compactNumericDecodedTokenListWeightBound_mono h
  unfold compactNumericBinaryNatStreamStateWeightBound
  omega

theorem BinaryNatStreamStateSourceOf.weight_le
    {initialBits : List Bool} {state : BinaryNatStreamState}
    (hsource : BinaryNatStreamStateSourceOf initialBits state) :
    compactAdditiveValueWeight state <=
      compactNumericBinaryNatStreamStateWeightBound initialBits.length := by
  rcases hsource with ⟨decoded, hdecodedRev, hrelation, hstatus⟩
  have hlengthRaw := binaryNatTokensDecode_length hrelation
  have hremainingLength : state.1.length <= initialBits.length := by omega
  have hremaining :=
    compactAdditiveValueWeight_boolList_le hremainingLength
  have hdecoded :=
    compactAdditiveValueWeight_natList_le_of_tokensDecode hrelation
  have hdecodedRev : compactAdditiveValueWeight state.2.1 <=
      compactNumericDecodedTokenListWeightBound initialBits.length := by
    rw [hdecodedRev, compactAdditiveValueWeight_reverse]
    exact hdecoded
  have hstatusWeight : compactAdditiveValueWeight state.2.2 <=
      4 + compactNumericDecodedTokenListWeightBound initialBits.length := by
    rcases hstatus with hnone | hstatus
    · rw [hnone]
      simp
      omega
    rcases hstatus with hfailed | hsucceeded
    · rw [hfailed]
      simp
      omega
    · rw [hsucceeded]
      simp only [compactAdditiveValueWeight_option_some]
      omega
  rw [compactAdditiveValueWeight_prod,
    compactAdditiveValueWeight_prod]
  unfold compactNumericBinaryNatStreamStateWeightBound
  omega

def compactNumericPackedTokenStreamTraceWeightBound
    (bitLength : Nat) : Nat :=
  compactNumericBoolListWeightBound bitLength +
    (Nat.size (bitLength + 2) + 1 +
      (bitLength + 2) *
        compactNumericBinaryNatStreamStateWeightBound bitLength)

theorem compactNumericPackedTokenStreamTraceWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericPackedTokenStreamTraceWeightBound left <=
      compactNumericPackedTokenStreamTraceWeightBound right := by
  have hbool := compactNumericBoolListWeightBound_mono h
  have hstate := compactNumericBinaryNatStreamStateWeightBound_mono h
  have hlength : left + 2 <= right + 2 := by omega
  have hsize := Nat.size_le_size hlength
  have hproduct := Nat.mul_le_mul hlength hstate
  unfold compactNumericPackedTokenStreamTraceWeightBound
  omega

theorem compactPackedTokenStreamDirectTraceValid_trace_weight_raw_le
    {code : Nat} {tokens : List Nat}
    {trace : CompactPackedTokenStreamDirectTrace}
    (hvalid : CompactPackedTokenStreamDirectTraceValid code tokens trace) :
    compactAdditiveValueWeight trace <=
      compactNumericPackedTokenStreamTraceWeightBound trace.1.length := by
  have hstates := hvalid.2.1
  have hpayload := compactAdditiveValueWeight_boolList_le
    (Nat.le_refl trace.1.length)
  have hrow : ∀ state ∈ trace.2,
      compactAdditiveValueWeight state <=
        compactNumericBinaryNatStreamStateWeightBound trace.1.length := by
    intro state hstate
    exact (binaryNatStreamLocalTrace_member_source hstates hstate).weight_le
  have htable := compactAdditiveValueWeight_list_le trace.2
    (compactNumericBinaryNatStreamStateWeightBound trace.1.length) hrow
  have htraceLength : trace.2.length = trace.1.length + 2 := by
    have := hstates.1
    omega
  rw [compactAdditiveValueWeight_prod]
  unfold compactNumericPackedTokenStreamTraceWeightBound
  rw [htraceLength] at htable
  omega

theorem compactPackedTokenStreamDirectTraceValid_trace_weight_le
    {code : Nat} {tokens : List Nat}
    {trace : CompactPackedTokenStreamDirectTrace}
    (hvalid : CompactPackedTokenStreamDirectTraceValid code tokens trace) :
    compactAdditiveValueWeight trace <=
      compactNumericPackedTokenStreamTraceWeightBound (Nat.size code) := by
  have hraw :=
    compactPackedTokenStreamDirectTraceValid_trace_weight_raw_le hvalid
  have hpayload : packedPayloadBits code = some trace.1 := hvalid.1
  have hpack := (packedPayloadBits_eq_some_iff code trace.1).mp hpayload
  have hlength : trace.1.length <= Nat.size code := by
    rw [← hpack, size_packBinaryString]
    omega
  exact hraw.trans
    (compactNumericPackedTokenStreamTraceWeightBound_mono hlength)

theorem compactNumericListedDirectTrace_certifiedStreamTrace_weight_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight
        (compactNumericDirectTraceCertifiedStreamTrace trace) <=
      compactNumericPackedTokenStreamTraceWeightBound (Nat.size code) := by
  unfold CompactNumericListedDirectTraceValid at hvalid
  exact compactPackedTokenStreamDirectTraceValid_trace_weight_le hvalid.1

theorem compactNumericListedDirectTrace_formulaStreamTrace_weight_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight
        (compactNumericDirectTraceFormulaStreamTrace trace) <=
      compactNumericPackedTokenStreamTraceWeightBound
        (Nat.size formulaCode) := by
  unfold CompactNumericListedDirectTraceValid at hvalid
  exact compactPackedTokenStreamDirectTraceValid_trace_weight_le hvalid.2.1

#print axioms compactAdditiveValueWeight_natList_le_of_decodeBinaryNatStream
#print axioms compactPackedTokenStreamDirectTraceValid_token_weight_le
#print axioms compactNumericListedDirectTrace_certifiedTokens_weight_le
#print axioms compactNumericListedDirectTrace_formulaTokens_weight_le
#print axioms compactNumericListedDirectTrace_formulaValue_weight_le
#print axioms compactNumericListedDirectTrace_parts_weight_le
#print axioms compactNumericListedDirectTrace_root_weight_le
#print axioms binaryNatStreamLocalTrace_member_source
#print axioms compactPackedTokenStreamDirectTraceValid_trace_weight_le
#print axioms compactNumericListedDirectTrace_certifiedStreamTrace_weight_le
#print axioms compactNumericListedDirectTrace_formulaStreamTrace_weight_le

end FoundationCompactNumericListedDirectTraceBounds
