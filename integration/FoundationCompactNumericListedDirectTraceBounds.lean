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
open FoundationCompactArithmeticSymbolCode
open FoundationCompactParserDirectTrace
open FoundationCompactProofTokenMachine
open FoundationCompactProofTokenMachineInversion
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedRootFieldsDirectTrace
open FoundationCompactSequentValueDirectTrace
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTokenMachineInversion
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactCertificateTokenMachineInversion

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

/-! ## Structural-certificate parser trace -/

def CompactCertificateParserTaskSource
    (task : CompactCertificateTask) : Prop :=
  task = compactStructuralCertificateTask ∨
    task = compactPAAxiomCertificateTask

def CompactCertificateParserStateSourceOf
    (initialTokens : List Nat) (state : CompactCertificateParserState) : Prop :=
  state.1 <:+ initialTokens ∧
    (∀ task ∈ state.2.1, CompactCertificateParserTaskSource task) ∧
    (state.2.2 = none ∨ state.2.2 = some none ∨
      state.2.2 = some (some state.1))

theorem compactPAAxiomCertificateTokenParser_suffix
    {tokens suffix : List Nat}
    (hparser : compactPAAxiomCertificateTokenParser tokens = some suffix) :
    suffix <:+ tokens := by
  obtain ⟨certificate, htokens⟩ :=
    (FoundationCompactCertificateTokenMachineInversion.compactPAAxiomCertificateTokenParser_success_iff
      tokens suffix).mp hparser
  exact ⟨compactPAAxiomCertificateTokens certificate, htokens.symm⟩

theorem compactCertificateParserStateSource_continue
    {initialTokens tokens : List Nat} {tasks : List CompactCertificateTask}
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks, CompactCertificateParserTaskSource task) :
    CompactCertificateParserStateSourceOf initialTokens
      (compactSyntaxContinue tokens tasks) := by
  exact ⟨hstream, htasks, by simp [compactSyntaxContinue]⟩

theorem compactCertificateParserStateSource_failure
    {initialTokens tokens : List Nat} {tasks : List CompactCertificateTask}
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks, CompactCertificateParserTaskSource task) :
    CompactCertificateParserStateSourceOf initialTokens
      (compactSyntaxFailure tokens tasks) := by
  exact ⟨hstream, htasks, by simp [compactSyntaxFailure]⟩

theorem compactStructuralCertificateNodeTokenStep_preserves_source
    {initialTokens tokens : List Nat} {tasks : List CompactCertificateTask}
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks, CompactCertificateParserTaskSource task) :
    CompactCertificateParserStateSourceOf initialTokens
      (compactStructuralCertificateNodeTokenStep tokens tasks) := by
  cases tokens with
  | nil =>
      simpa [compactStructuralCertificateNodeTokenStep] using
        compactCertificateParserStateSource_failure hstream htasks
  | cons tag suffix =>
      have hsuffix : suffix <:+ initialTokens :=
        (List.suffix_cons tag suffix).trans hstream
      by_cases h0 : tag = 0
      · simpa [compactStructuralCertificateNodeTokenStep, h0] using
          compactCertificateParserStateSource_continue hsuffix htasks
      by_cases h1 : tag = 1
      · have hnewTasks : ∀ task ∈
            compactPAAxiomCertificateTask :: tasks,
            CompactCertificateParserTaskSource task := by
          intro task htask
          simp only [List.mem_cons] at htask
          rcases htask with rfl | htask
          · exact Or.inr rfl
          · exact htasks task htask
        simpa [compactStructuralCertificateNodeTokenStep, h0, h1] using
          compactCertificateParserStateSource_continue hsuffix hnewTasks
      by_cases h2 : tag = 2
      · have hnewTasks : ∀ task ∈
            compactStructuralCertificateTask :: tasks,
            CompactCertificateParserTaskSource task := by
          intro task htask
          simp only [List.mem_cons] at htask
          rcases htask with rfl | htask
          · exact Or.inl rfl
          · exact htasks task htask
        simpa [compactStructuralCertificateNodeTokenStep, h0, h1, h2] using
          compactCertificateParserStateSource_continue hsuffix hnewTasks
      by_cases h3 : tag = 3
      · have hnewTasks : ∀ task ∈
            compactStructuralCertificateTask ::
              compactStructuralCertificateTask :: tasks,
            CompactCertificateParserTaskSource task := by
          intro task htask
          simp only [List.mem_cons] at htask
          rcases htask with rfl | htask
          · exact Or.inl rfl
          rcases htask with rfl | htask
          · exact Or.inl rfl
          · exact htasks task htask
        simpa [compactStructuralCertificateNodeTokenStep, h0, h1, h2, h3]
          using compactCertificateParserStateSource_continue hsuffix hnewTasks
      simpa [compactStructuralCertificateNodeTokenStep, h0, h1, h2, h3]
        using compactCertificateParserStateSource_failure hstream htasks

theorem compactCertificateAxiomTokenStep_preserves_source
    {initialTokens tokens : List Nat} {tasks : List CompactCertificateTask}
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks, CompactCertificateParserTaskSource task) :
    CompactCertificateParserStateSourceOf initialTokens
      (compactCertificateAxiomTokenStep tokens tasks) := by
  cases hparser : compactPAAxiomCertificateTokenParser tokens with
  | none =>
      rw [compactCertificateAxiomTokenStep, hparser]
      exact compactCertificateParserStateSource_failure hstream htasks
  | some suffix =>
      have hsuffix : suffix <:+ initialTokens :=
        (compactPAAxiomCertificateTokenParser_suffix hparser).trans hstream
      rw [compactCertificateAxiomTokenStep, hparser]
      exact compactCertificateParserStateSource_continue hsuffix htasks

theorem compactCertificateParserInitialState_source
    (tokens : List Nat) :
    CompactCertificateParserStateSourceOf tokens
      (compactCertificateParserInitialState tokens) := by
  refine ⟨List.suffix_refl tokens, ?_, by simp [
    compactCertificateParserInitialState]⟩
  intro task htask
  simp only [compactCertificateParserInitialState, List.mem_cons,
    List.not_mem_nil, or_false] at htask
  subst task
  exact Or.inl rfl

theorem compactCertificateParserStep_preserves_source
    (initialTokens : List Nat) (state : CompactCertificateParserState)
    (hsource : CompactCertificateParserStateSourceOf initialTokens state) :
    CompactCertificateParserStateSourceOf initialTokens
      (compactCertificateParserStep state) := by
  rcases state with ⟨tokens, tasks, status⟩
  rcases hsource with ⟨hstream, htasks, hstatus⟩
  cases status with
  | some result =>
      simpa [compactCertificateParserStep] using
        (show CompactCertificateParserStateSourceOf initialTokens
          (tokens, tasks, some result) from ⟨hstream, htasks, hstatus⟩)
  | none =>
      cases tasks with
      | nil =>
          exact ⟨hstream, by simp,
            by simp [compactCertificateParserStep,
              compactCertificateParserRunningStep]⟩
      | cons task restTasks =>
          have htask := htasks task (by simp)
          have hrest : ∀ nextTask ∈ restTasks,
              CompactCertificateParserTaskSource nextTask := by
            intro nextTask hnextTask
            exact htasks nextTask (List.mem_cons_of_mem task hnextTask)
          rcases htask with hstructural | haxiom
          · subst task
            simpa using
              compactStructuralCertificateNodeTokenStep_preserves_source
                hstream hrest
          · subst task
            simpa using
              compactCertificateAxiomTokenStep_preserves_source hstream hrest

theorem compactCertificateParser_iterate_preserves_source
    (initialTokens : List Nat) (stepCount : Nat)
    (state : CompactCertificateParserState)
    (hsource : CompactCertificateParserStateSourceOf initialTokens state) :
    CompactCertificateParserStateSourceOf initialTokens
      ((compactCertificateParserStep^[stepCount]) state) := by
  induction stepCount generalizing state with
  | zero => simpa
  | succ stepCount ih =>
      rw [Function.iterate_succ_apply]
      exact ih _
        (compactCertificateParserStep_preserves_source
          initialTokens state hsource)

theorem compactStructuralCertificateNodeTokenStep_task_length_le
    (tokens : List Nat) (tasks : List CompactCertificateTask) :
    (compactStructuralCertificateNodeTokenStep tokens tasks).2.1.length <=
      tasks.length + 2 := by
  cases tokens with
  | nil => simp [compactStructuralCertificateNodeTokenStep,
      compactSyntaxFailure]
  | cons tag suffix =>
      by_cases h0 : tag = 0
      · simp [compactStructuralCertificateNodeTokenStep, h0,
          compactSyntaxContinue]
      by_cases h1 : tag = 1
      · simp [compactStructuralCertificateNodeTokenStep, h0, h1,
          compactSyntaxContinue]
      by_cases h2 : tag = 2
      · simp [compactStructuralCertificateNodeTokenStep, h0, h1, h2,
          compactSyntaxContinue]
      by_cases h3 : tag = 3
      · simp [compactStructuralCertificateNodeTokenStep, h0, h1, h2, h3,
          compactSyntaxContinue]
      simp [compactStructuralCertificateNodeTokenStep, h0, h1, h2, h3,
        compactSyntaxFailure]

theorem compactCertificateParserStep_task_length_le
    (initialTokens : List Nat) (state : CompactCertificateParserState)
    (hsource : CompactCertificateParserStateSourceOf initialTokens state) :
    (compactCertificateParserStep state).2.1.length <=
      state.2.1.length + 1 := by
  rcases state with ⟨tokens, tasks, status⟩
  rcases hsource with ⟨_hstream, htasks, _hstatus⟩
  cases status with
  | some result => simp [compactCertificateParserStep]
  | none =>
      cases tasks with
      | nil => simp [compactCertificateParserStep,
          compactCertificateParserRunningStep]
      | cons task restTasks =>
          have htask := htasks task (by simp)
          rcases htask with hstructural | haxiom
          · subst task
            have hnode :=
              compactStructuralCertificateNodeTokenStep_task_length_le
                tokens restTasks
            simpa using hnode
          · subst task
            cases hparser : compactPAAxiomCertificateTokenParser tokens <;>
              simp [compactCertificateParserStep,
                compactCertificateParserRunningStep,
                compactCertificateTaskTokenStep,
                compactPAAxiomCertificateTask,
                compactCertificateAxiomTokenStep,
                compactSyntaxFailure, compactSyntaxContinue, hparser] <;>
              omega

theorem compactCertificateParser_iterate_task_length_le
    (initialTokens : List Nat) (stepCount : Nat)
    (state : CompactCertificateParserState)
    (hsource : CompactCertificateParserStateSourceOf initialTokens state) :
    ((compactCertificateParserStep^[stepCount]) state).2.1.length <=
      state.2.1.length + stepCount := by
  induction stepCount generalizing state with
  | zero => simp
  | succ stepCount ih =>
      rw [Function.iterate_succ_apply]
      have hstepSource := compactCertificateParserStep_preserves_source
        initialTokens state hsource
      have hstepLength := compactCertificateParserStep_task_length_le
        initialTokens state hsource
      have htail := ih _ hstepSource
      omega

theorem compactCertificateParserStateAt_source
    (tokens : List Nat) (stepIndex : Nat) :
    CompactCertificateParserStateSourceOf tokens
      (compactParserStateAt compactCertificateParserStep
        (compactCertificateParserInitialState tokens) stepIndex) := by
  unfold compactParserStateAt
  exact compactCertificateParser_iterate_preserves_source tokens stepIndex _
    (compactCertificateParserInitialState_source tokens)

theorem compactCertificateParserStateAt_task_length_le
    (tokens : List Nat) (stepIndex : Nat) :
    (compactParserStateAt compactCertificateParserStep
      (compactCertificateParserInitialState tokens) stepIndex).2.1.length <=
      1 + stepIndex := by
  unfold compactParserStateAt
  have hraw := compactCertificateParser_iterate_task_length_le
    tokens stepIndex (compactCertificateParserInitialState tokens)
      (compactCertificateParserInitialState_source tokens)
  simpa [compactCertificateParserInitialState] using hraw

theorem compactCertificateParserLocalTrace_member_source
    {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactCertificateParserStep fuel
      (compactCertificateParserInitialState tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    CompactCertificateParserStateSourceOf tokens state := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical := compactParserLocalTraceValid_stateAt hvalid hle
  unfold compactParserTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = compactParserStateAt compactCertificateParserStep
      (compactCertificateParserInitialState tokens) stepIndex :=
    Option.some.inj hcanonical
  rw [heq]
  exact compactCertificateParserStateAt_source tokens stepIndex

theorem compactCertificateParserLocalTrace_member_task_length_le
    {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactCertificateParserStep fuel
      (compactCertificateParserInitialState tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    state.2.1.length <= 1 + fuel := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical := compactParserLocalTraceValid_stateAt hvalid hle
  unfold compactParserTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = compactParserStateAt compactCertificateParserStep
      (compactCertificateParserInitialState tokens) stepIndex :=
    Option.some.inj hcanonical
  rw [heq]
  have hraw := compactCertificateParserStateAt_task_length_le tokens stepIndex
  omega

theorem CompactCertificateParserTaskSource.weight_le
    {task : CompactCertificateTask}
    (htask : CompactCertificateParserTaskSource task) :
    compactAdditiveValueWeight task <= 16 := by
  rcases htask with rfl | rfl <;>
    norm_num [compactStructuralCertificateTask,
      compactPAAxiomCertificateTask,
      compactAdditiveValueWeight_prod,
      compactAdditiveValueWeight_nat] <;>
    decide

theorem CompactCertificateParserStateSourceOf.status_weight_le
    {initialTokens : List Nat} {state : CompactCertificateParserState}
    (hsource : CompactCertificateParserStateSourceOf initialTokens state) :
    compactAdditiveValueWeight state.2.2 <=
      4 + compactAdditiveValueWeight initialTokens := by
  have hstream := compactAdditiveValueWeight_suffix_le hsource.1
  rcases hsource.2.2 with hnone | hstatus
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

def compactNumericCertificateParserStateWeightBound
    (streamWeight fuel : Nat) : Nat :=
  streamWeight +
    (Nat.size (1 + fuel) + 1 + (1 + fuel) * 16) +
    (4 + streamWeight)

theorem compactNumericCertificateParserStateWeightBound_mono
    {streamLeft streamRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft <= streamRight)
    (hfuel : fuelLeft <= fuelRight) :
    compactNumericCertificateParserStateWeightBound streamLeft fuelLeft <=
      compactNumericCertificateParserStateWeightBound streamRight fuelRight := by
  have hfuelAdd : 1 + fuelLeft <= 1 + fuelRight := by omega
  have hfuelSize := Nat.size_le_size hfuelAdd
  have hfuelTasks := Nat.mul_le_mul_right 16 hfuelAdd
  unfold compactNumericCertificateParserStateWeightBound
  omega

theorem compactCertificateParserLocalTrace_member_state_weight_le
    {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactCertificateParserStep fuel
      (compactCertificateParserInitialState tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    compactAdditiveValueWeight state <=
      compactNumericCertificateParserStateWeightBound
        (compactAdditiveValueWeight tokens) fuel := by
  have hsource :=
    compactCertificateParserLocalTrace_member_source hvalid hstate
  have hstream := compactAdditiveValueWeight_suffix_le hsource.1
  have htaskLength :=
    compactCertificateParserLocalTrace_member_task_length_le hvalid hstate
  have htasksRaw := compactAdditiveValueWeight_list_le state.2.1 16
    (fun task htask =>
      (hsource.2.1 task htask).weight_le)
  have htaskSize := Nat.size_le_size htaskLength
  have htaskProduct := Nat.mul_le_mul_right 16 htaskLength
  have htasks : compactAdditiveValueWeight state.2.1 <=
      Nat.size (1 + fuel) + 1 + (1 + fuel) * 16 := by
    omega
  have hstatus := hsource.status_weight_le
  rw [compactAdditiveValueWeight_prod,
    compactAdditiveValueWeight_prod]
  unfold compactNumericCertificateParserStateWeightBound
  omega

def compactNumericCertificateParserTraceWeightBound
    (streamWeight fuel : Nat) : Nat :=
  Nat.size (fuel + 1) + 1 +
    (fuel + 1) *
      compactNumericCertificateParserStateWeightBound streamWeight fuel

theorem compactNumericCertificateParserTraceWeightBound_mono
    {streamLeft streamRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft <= streamRight)
    (hfuel : fuelLeft <= fuelRight) :
    compactNumericCertificateParserTraceWeightBound streamLeft fuelLeft <=
      compactNumericCertificateParserTraceWeightBound streamRight fuelRight := by
  have hfuelAdd : fuelLeft + 1 <= fuelRight + 1 := by omega
  have hfuelSize := Nat.size_le_size hfuelAdd
  have hstate := compactNumericCertificateParserStateWeightBound_mono
    hstream hfuel
  have htable := Nat.mul_le_mul hfuelAdd hstate
  unfold compactNumericCertificateParserTraceWeightBound
  omega

def compactNumericCertificateParserFuelWeightBound
    (streamWeight : Nat) : Nat :=
  16 * (streamWeight + 1) * (streamWeight + 1) + 8

theorem compactCertificateParserFuelBound_le_weightBound
    {tokens : List Nat} {streamWeight : Nat}
    (hweight : compactAdditiveValueWeight tokens <= streamWeight) :
    compactCertificateParserFuelBound tokens <=
      compactNumericCertificateParserFuelWeightBound streamWeight := by
  have hlength := compactAdditiveValueWeight_natList_length_le tokens
  have hlengthWeight : tokens.length + 1 <= streamWeight + 1 := by omega
  have hscaled := Nat.mul_le_mul_left 16 hlengthWeight
  have hquadratic := Nat.mul_le_mul hscaled hlengthWeight
  unfold compactCertificateParserFuelBound
    compactNumericCertificateParserFuelWeightBound
  omega

def compactNumericCertificateParserPublicTraceWeightBound
    (bitLength : Nat) : Nat :=
  let streamWeight := compactNumericDecodedTokenListWeightBound bitLength
  compactNumericCertificateParserTraceWeightBound streamWeight
    (compactNumericCertificateParserFuelWeightBound streamWeight)

theorem compactCertificateTokenParserDirectTraceValid_weight_le
    {tokens suffix : List Nat}
    {states : CompactCertificateTokenParserDirectTrace}
    (hvalid : CompactCertificateTokenParserDirectTraceValid
      tokens suffix states) :
    compactAdditiveValueWeight states <=
      compactNumericCertificateParserTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactCertificateParserFuelBound tokens) := by
  have hlocal := hvalid.1
  have hrows := compactAdditiveValueWeight_list_le states
    (compactNumericCertificateParserStateWeightBound
      (compactAdditiveValueWeight tokens)
      (compactCertificateParserFuelBound tokens))
    (fun state hstate =>
      compactCertificateParserLocalTrace_member_state_weight_le
        hlocal hstate)
  unfold compactNumericCertificateParserTraceWeightBound
  rw [hlocal.1] at hrows
  exact hrows

theorem compactNumericListedDirectTrace_certificateParserTrace_weight_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight
        (compactNumericDirectTraceCertificateParserTrace trace) <=
      compactNumericCertificateParserPublicTraceWeightBound
        (Nat.size code) := by
  have hfull := hvalid
  unfold CompactNumericListedDirectTraceValid at hfull
  have hparser : CompactCertificateTokenParserDirectTraceValid
      (compactNumericDirectTraceParts trace).2.1 []
      (compactNumericDirectTraceCertificateParserTrace trace) :=
    hfull.2.2.2.1
  have hraw :=
    compactCertificateTokenParserDirectTraceValid_weight_le hparser
  have hcertificateCurrent :=
    (compactNumericListedDirectTrace_parts_components_weight_le hvalid).2.1
  have hcertified :=
    compactNumericListedDirectTrace_certifiedTokens_weight_le hvalid
  have hcertificate :
      compactAdditiveValueWeight
          (compactNumericDirectTraceParts trace).2.1 <=
        compactNumericDecodedTokenListWeightBound (Nat.size code) :=
    hcertificateCurrent.trans hcertified
  have hfuel := compactCertificateParserFuelBound_le_weightBound hcertificate
  unfold compactNumericCertificateParserPublicTraceWeightBound
  exact hraw.trans
    (compactNumericCertificateParserTraceWeightBound_mono
      hcertificate hfuel)

/-! ## Formula-parser state trace -/

theorem compactAdditiveValueWeight_nat_mem_le
    {value : Nat} {values : List Nat} (hmem : value ∈ values) :
    compactAdditiveValueWeight value <=
      compactAdditiveValueWeight values := by
  have hinfix : [value] <:+: values :=
    (List.singleton_infix_iff value values).2 hmem
  have hsingleton := compactAdditiveValueWeight_infix_le hinfix
  have hitem : compactAdditiveValueWeight value <=
      compactAdditiveValueWeight [value] := by
    simp [compactAdditiveValueWeight_list]
  exact hitem.trans hsingleton

theorem compactTokenAt_weight_le_of_suffix
    {initialTokens tokens : List Nat}
    (hstream : tokens <:+ initialTokens) (index : Nat) :
    compactAdditiveValueWeight (compactTokenAt index tokens) <=
      compactAdditiveValueWeight initialTokens := by
  unfold compactTokenAt
  cases hget : tokens[index]? with
  | none =>
      change compactAdditiveValueWeight 0 <=
        compactAdditiveValueWeight initialTokens
      simpa [compactAdditiveValueWeight_nat] using
        compactAdditiveValueWeight_list_pos initialTokens
  | some token =>
      have hmemTokens : token ∈ tokens := List.mem_of_getElem? hget
      rcases hstream with ⟨front, hwhole⟩
      have hmemInitial : token ∈ initialTokens := by
        rw [← hwhole]
        simp [hmemTokens]
      change compactAdditiveValueWeight token <=
        compactAdditiveValueWeight initialTokens
      exact compactAdditiveValueWeight_nat_mem_le hmemInitial

def CompactSyntaxParserTaskWithin
    (initialTokens : List Nat) (binderCap : Nat)
    (task : CompactSyntaxTask) : Prop :=
  task.1 <= 2 ∧
    task.2.1 <= binderCap ∧
    compactAdditiveValueWeight task.2.2 <=
      compactAdditiveValueWeight initialTokens

theorem CompactSyntaxParserTaskWithin.mono
    {initialTokens : List Nat} {binderLeft binderRight : Nat}
    {task : CompactSyntaxTask}
    (htask : CompactSyntaxParserTaskWithin
      initialTokens binderLeft task)
    (hbinder : binderLeft <= binderRight) :
    CompactSyntaxParserTaskWithin initialTokens binderRight task := by
  exact ⟨htask.1, htask.2.1.trans hbinder, htask.2.2⟩

theorem compactTermTask_within
    {initialTokens : List Nat} {binderArity binderCap : Nat}
    (hbinder : binderArity <= binderCap) :
    CompactSyntaxParserTaskWithin initialTokens binderCap
      (compactTermTask binderArity) := by
  refine ⟨by simp [compactTermTask], by simpa [compactTermTask], ?_⟩
  simpa [compactTermTask] using
    compactAdditiveValueWeight_list_pos initialTokens

theorem compactFormulaTask_within
    {initialTokens : List Nat} {binderArity binderCap : Nat}
    (hbinder : binderArity <= binderCap) :
    CompactSyntaxParserTaskWithin initialTokens binderCap
      (compactFormulaTask binderArity) := by
  refine ⟨by simp [compactFormulaTask], by simpa [compactFormulaTask], ?_⟩
  simpa [compactFormulaTask] using
    compactAdditiveValueWeight_list_pos initialTokens

theorem compactRepeatTermTask_within
    {initialTokens : List Nat} {binderArity binderCap count : Nat}
    (hbinder : binderArity <= binderCap)
    (hcount : compactAdditiveValueWeight count <=
      compactAdditiveValueWeight initialTokens) :
    CompactSyntaxParserTaskWithin initialTokens binderCap
      (compactRepeatTermTask binderArity count) := by
  refine ⟨by simp [compactRepeatTermTask], ?_, ?_⟩
  · simpa [compactRepeatTermTask] using hbinder
  · simpa [compactRepeatTermTask] using hcount

def CompactSyntaxParserStateSourceOf
    (initialTokens : List Nat) (binderCap : Nat)
    (state : CompactSyntaxParserState) : Prop :=
  state.1 <:+ initialTokens ∧
    (∀ task ∈ state.2.1,
      CompactSyntaxParserTaskWithin initialTokens binderCap task) ∧
    (state.2.2 = none ∨ state.2.2 = some none ∨
      state.2.2 = some (some state.1))

theorem CompactSyntaxParserStateSourceOf.mono
    {initialTokens : List Nat} {binderLeft binderRight : Nat}
    {state : CompactSyntaxParserState}
    (hsource : CompactSyntaxParserStateSourceOf
      initialTokens binderLeft state)
    (hbinder : binderLeft <= binderRight) :
    CompactSyntaxParserStateSourceOf initialTokens binderRight state := by
  refine ⟨hsource.1, ?_, hsource.2.2⟩
  intro task htask
  exact (hsource.2.1 task htask).mono hbinder

theorem compactSyntaxParserStateSource_continue
    {initialTokens tokens : List Nat} {binderCap : Nat}
    {tasks : List CompactSyntaxTask}
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens binderCap task) :
    CompactSyntaxParserStateSourceOf initialTokens binderCap
      (compactSyntaxContinue tokens tasks) := by
  exact ⟨hstream, htasks, by simp [compactSyntaxContinue]⟩

theorem compactSyntaxParserStateSource_failure
    {initialTokens tokens : List Nat} {binderCap : Nat}
    {tasks : List CompactSyntaxTask}
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens binderCap task) :
    CompactSyntaxParserStateSourceOf initialTokens binderCap
      (compactSyntaxFailure tokens tasks) := by
  exact ⟨hstream, htasks, by simp [compactSyntaxFailure]⟩

theorem compactSyntaxParserStateSource_continue_push
    {initialTokens tokens : List Nat} {binderCap : Nat}
    {task : CompactSyntaxTask} {tasks : List CompactSyntaxTask}
    (hstream : tokens <:+ initialTokens)
    (htask : CompactSyntaxParserTaskWithin initialTokens binderCap task)
    (htasks : ∀ oldTask ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens binderCap oldTask) :
    CompactSyntaxParserStateSourceOf initialTokens binderCap
      (compactSyntaxContinue tokens (task :: tasks)) := by
  apply compactSyntaxParserStateSource_continue hstream
  intro nextTask hnext
  simp only [List.mem_cons] at hnext
  rcases hnext with rfl | hnext
  · exact htask
  · exact htasks nextTask hnext

theorem compactSyntaxParserStateSource_continue_push_two
    {initialTokens tokens : List Nat} {binderCap : Nat}
    {first second : CompactSyntaxTask} {tasks : List CompactSyntaxTask}
    (hstream : tokens <:+ initialTokens)
    (hfirst : CompactSyntaxParserTaskWithin initialTokens binderCap first)
    (hsecond : CompactSyntaxParserTaskWithin initialTokens binderCap second)
    (htasks : ∀ oldTask ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens binderCap oldTask) :
    CompactSyntaxParserStateSourceOf initialTokens binderCap
      (compactSyntaxContinue tokens (first :: second :: tasks)) := by
  apply compactSyntaxParserStateSource_continue hstream
  intro nextTask hnext
  simp only [List.mem_cons] at hnext
  rcases hnext with rfl | hnext
  · exact hfirst
  rcases hnext with rfl | hnext
  · exact hsecond
  · exact htasks nextTask hnext

theorem compactAdditiveValueWeight_nat_sub_le
    (value amount : Nat) :
    compactAdditiveValueWeight (value - amount) <=
      compactAdditiveValueWeight value := by
  have hvalue : value - amount <= value := Nat.sub_le value amount
  have hsize := Nat.size_le_size hvalue
  simp only [compactAdditiveValueWeight_nat]
  omega

theorem compactTermTokenStep_preserves_source
    {initialTokens tokens : List Nat} {binderArity binderCap : Nat}
    {tasks : List CompactSyntaxTask}
    (hbinder : binderArity <= binderCap)
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens binderCap task) :
    CompactSyntaxParserStateSourceOf initialTokens (binderCap + 1)
      (compactTermTokenStep (binderArity, tokens, tasks)) := by
  have hbinderNext : binderArity <= binderCap + 1 := by omega
  have htasksNext : ∀ task ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens (binderCap + 1) task := by
    intro task htask
    exact (htasks task htask).mono (by omega)
  have hdropTwo : tokens.drop 2 <:+ initialTokens :=
    (List.drop_suffix 2 tokens).trans hstream
  have hdropThree : tokens.drop 3 <:+ initialTokens :=
    (List.drop_suffix 3 tokens).trans hstream
  have hargument := compactTokenAt_weight_le_of_suffix hstream 1
  by_cases hlengthTwo : 2 <= tokens.length
  · by_cases htagZero : compactTokenAt 0 tokens = 0
    · by_cases hbound : compactTokenAt 1 tokens < binderArity
      · simpa [compactTermTokenStep, hlengthTwo, htagZero, hbound] using
          compactSyntaxParserStateSource_continue hdropTwo htasksNext
      · simpa [compactTermTokenStep, hlengthTwo, htagZero, hbound] using
          compactSyntaxParserStateSource_failure hstream htasksNext
    · by_cases htagOne : compactTokenAt 0 tokens = 1
      · simpa [compactTermTokenStep, hlengthTwo, htagZero, htagOne] using
          compactSyntaxParserStateSource_continue hdropTwo htasksNext
      · by_cases htagTwo : compactTokenAt 0 tokens = 2
        · by_cases hlengthThree : 3 <= tokens.length
          · by_cases hvalid : ArithmeticFuncCodeValid
                (compactTokenAt 1 tokens) (compactTokenAt 2 tokens)
            · have hrepeat := compactRepeatTermTask_within
                (initialTokens := initialTokens)
                (binderCap := binderCap + 1)
                hbinderNext hargument
              simpa [compactTermTokenStep, hlengthTwo, htagZero, htagOne,
                htagTwo, hlengthThree, hvalid] using
                compactSyntaxParserStateSource_continue_push
                  hdropThree hrepeat htasksNext
            · simpa [compactTermTokenStep, hlengthTwo, htagZero, htagOne,
                htagTwo, hlengthThree, hvalid] using
                compactSyntaxParserStateSource_failure hstream htasksNext
          · simpa [compactTermTokenStep, hlengthTwo, htagZero, htagOne,
              htagTwo, hlengthThree] using
              compactSyntaxParserStateSource_failure hstream htasksNext
        · simpa [compactTermTokenStep, hlengthTwo, htagZero, htagOne,
            htagTwo] using
            compactSyntaxParserStateSource_failure hstream htasksNext
  · simpa [compactTermTokenStep, hlengthTwo] using
      compactSyntaxParserStateSource_failure hstream htasksNext

theorem compactFormulaTokenStep_preserves_source
    {initialTokens tokens : List Nat} {binderArity binderCap : Nat}
    {tasks : List CompactSyntaxTask}
    (hbinder : binderArity <= binderCap)
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens binderCap task) :
    CompactSyntaxParserStateSourceOf initialTokens (binderCap + 1)
      (compactFormulaTokenStep (binderArity, tokens, tasks)) := by
  have hbinderNext : binderArity <= binderCap + 1 := by omega
  have hbinderSucc : binderArity + 1 <= binderCap + 1 := by omega
  have htasksNext : ∀ task ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens (binderCap + 1) task := by
    intro task htask
    exact (htasks task htask).mono (by omega)
  have hdropOne : tokens.drop 1 <:+ initialTokens :=
    (List.drop_suffix 1 tokens).trans hstream
  have hdropThree : tokens.drop 3 <:+ initialTokens :=
    (List.drop_suffix 3 tokens).trans hstream
  have harity := compactTokenAt_weight_le_of_suffix hstream 1
  have hformula := compactFormulaTask_within
    (initialTokens := initialTokens) hbinderNext
  have hquantifiedFormula := compactFormulaTask_within
    (initialTokens := initialTokens) hbinderSucc
  by_cases hlengthOne : 1 <= tokens.length
  · by_cases htagZero : compactTokenAt 0 tokens = 0
    · by_cases hlengthThree : 3 <= tokens.length
      · by_cases hvalid : ArithmeticRelCodeValid
            (compactTokenAt 1 tokens) (compactTokenAt 2 tokens)
        · have hrepeat := compactRepeatTermTask_within
            (initialTokens := initialTokens)
            (binderCap := binderCap + 1) hbinderNext harity
          simpa [compactFormulaTokenStep, hlengthOne, htagZero,
            hlengthThree, hvalid] using
            compactSyntaxParserStateSource_continue_push
              hdropThree hrepeat htasksNext
        · simpa [compactFormulaTokenStep, hlengthOne, htagZero,
            hlengthThree, hvalid] using
            compactSyntaxParserStateSource_failure hstream htasksNext
      · simpa [compactFormulaTokenStep, hlengthOne, htagZero,
          hlengthThree] using
          compactSyntaxParserStateSource_failure hstream htasksNext
    · by_cases htagOne : compactTokenAt 0 tokens = 1
      · by_cases hlengthThree : 3 <= tokens.length
        · by_cases hvalid : ArithmeticRelCodeValid
              (compactTokenAt 1 tokens) (compactTokenAt 2 tokens)
          · have hrepeat := compactRepeatTermTask_within
              (initialTokens := initialTokens)
              (binderCap := binderCap + 1) hbinderNext harity
            simpa [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
              hlengthThree, hvalid] using
              compactSyntaxParserStateSource_continue_push
                hdropThree hrepeat htasksNext
          · simpa [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
              hlengthThree, hvalid] using
              compactSyntaxParserStateSource_failure hstream htasksNext
        · simpa [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
            hlengthThree] using
            compactSyntaxParserStateSource_failure hstream htasksNext
      · by_cases htagTwo : compactTokenAt 0 tokens = 2
        · simpa [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
            htagTwo] using
            compactSyntaxParserStateSource_continue hdropOne htasksNext
        · by_cases htagThree : compactTokenAt 0 tokens = 3
          · simpa [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
              htagTwo, htagThree] using
              compactSyntaxParserStateSource_continue hdropOne htasksNext
          · by_cases htagFour : compactTokenAt 0 tokens = 4
            · simpa [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
                htagTwo, htagThree, htagFour] using
                compactSyntaxParserStateSource_continue_push_two hdropOne
                  hformula hformula htasksNext
            · by_cases htagFive : compactTokenAt 0 tokens = 5
              · simpa [compactFormulaTokenStep, hlengthOne, htagZero,
                  htagOne, htagTwo, htagThree, htagFour, htagFive] using
                  compactSyntaxParserStateSource_continue_push_two hdropOne
                    hformula hformula htasksNext
              · by_cases htagSix : compactTokenAt 0 tokens = 6
                · simpa [compactFormulaTokenStep, hlengthOne, htagZero,
                    htagOne, htagTwo, htagThree, htagFour, htagFive,
                    htagSix] using
                    compactSyntaxParserStateSource_continue_push hdropOne
                      hquantifiedFormula htasksNext
                · by_cases htagSeven : compactTokenAt 0 tokens = 7
                  · simpa [compactFormulaTokenStep, hlengthOne, htagZero,
                      htagOne, htagTwo, htagThree, htagFour, htagFive,
                      htagSix, htagSeven] using
                      compactSyntaxParserStateSource_continue_push hdropOne
                        hquantifiedFormula htasksNext
                  · simpa [compactFormulaTokenStep, hlengthOne, htagZero,
                      htagOne, htagTwo, htagThree, htagFour, htagFive,
                      htagSix, htagSeven] using
                      compactSyntaxParserStateSource_failure
                        hstream htasksNext
  · simpa [compactFormulaTokenStep, hlengthOne] using
      compactSyntaxParserStateSource_failure hstream htasksNext

theorem compactRepeatTermTokenStep_preserves_source
    {initialTokens tokens : List Nat} {binderCap : Nat}
    {task : CompactSyntaxTask} {tasks : List CompactSyntaxTask}
    (htask : CompactSyntaxParserTaskWithin initialTokens binderCap task)
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ oldTask ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens binderCap oldTask) :
    CompactSyntaxParserStateSourceOf initialTokens (binderCap + 1)
      (compactRepeatTermTokenStep (task, tokens, tasks)) := by
  unfold CompactSyntaxParserTaskWithin at htask
  have hbinderNext : task.2.1 <= binderCap + 1 := by omega
  have htasksNext : ∀ oldTask ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens (binderCap + 1) oldTask := by
    intro oldTask hold
    exact (htasks oldTask hold).mono (by omega)
  by_cases hzero : task.2.2 = 0
  · simpa [compactRepeatTermTokenStep, hzero] using
      compactSyntaxParserStateSource_continue hstream htasksNext
  · have hterm := compactTermTask_within
        (initialTokens := initialTokens) hbinderNext
    have hcount : compactAdditiveValueWeight (task.2.2 - 1) <=
        compactAdditiveValueWeight initialTokens :=
      (compactAdditiveValueWeight_nat_sub_le task.2.2 1).trans htask.2.2
    have hrepeat := compactRepeatTermTask_within
      (initialTokens := initialTokens) hbinderNext hcount
    simpa [compactRepeatTermTokenStep, hzero] using
      compactSyntaxParserStateSource_continue_push_two hstream
        hterm hrepeat htasksNext

theorem compactSyntaxTaskTokenStep_preserves_source
    {initialTokens tokens : List Nat} {binderCap : Nat}
    {task : CompactSyntaxTask} {tasks : List CompactSyntaxTask}
    (htask : CompactSyntaxParserTaskWithin initialTokens binderCap task)
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ oldTask ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens binderCap oldTask) :
    CompactSyntaxParserStateSourceOf initialTokens (binderCap + 1)
      (compactSyntaxTaskTokenStep (task, tokens, tasks)) := by
  unfold CompactSyntaxParserTaskWithin at htask
  by_cases hterm : task.1 = 0
  · simpa [compactSyntaxTaskTokenStep, hterm] using
      compactTermTokenStep_preserves_source htask.2.1 hstream htasks
  by_cases hformula : task.1 = 1
  · simpa [compactSyntaxTaskTokenStep, hterm, hformula] using
      compactFormulaTokenStep_preserves_source htask.2.1 hstream htasks
  by_cases hrepeat : task.1 = 2
  · simpa [compactSyntaxTaskTokenStep, hterm, hformula, hrepeat] using
      compactRepeatTermTokenStep_preserves_source htask hstream htasks
  exfalso
  omega

theorem compactSyntaxParserStep_preserves_source
    (initialTokens : List Nat) (binderCap : Nat)
    (state : CompactSyntaxParserState)
    (hsource : CompactSyntaxParserStateSourceOf
      initialTokens binderCap state) :
    CompactSyntaxParserStateSourceOf initialTokens (binderCap + 1)
      (compactSyntaxParserStep state) := by
  rcases state with ⟨tokens, tasks, status⟩
  rcases hsource with ⟨hstream, htasks, hstatus⟩
  cases status with
  | some result =>
      simpa [compactSyntaxParserStep] using
        (show CompactSyntaxParserStateSourceOf
          initialTokens (binderCap + 1) (tokens, tasks, some result) from
          CompactSyntaxParserStateSourceOf.mono
            (⟨hstream, htasks, hstatus⟩ :
              CompactSyntaxParserStateSourceOf
                initialTokens binderCap (tokens, tasks, some result))
            (by omega))
  | none =>
      cases tasks with
      | nil =>
          exact ⟨hstream, by simp,
            by simp [compactSyntaxParserStep, compactSyntaxRunningStep]⟩
      | cons task restTasks =>
          have htask := htasks task (by simp)
          have hrest : ∀ oldTask ∈ restTasks,
              CompactSyntaxParserTaskWithin
                initialTokens binderCap oldTask := by
            intro oldTask hold
            exact htasks oldTask (List.mem_cons_of_mem task hold)
          simpa [compactSyntaxParserStep, compactSyntaxRunningStep] using
            compactSyntaxTaskTokenStep_preserves_source
              htask hstream hrest

theorem compactFormulaParserInitialState_source
    (binderArity : Nat) (tokens : List Nat) :
    CompactSyntaxParserStateSourceOf tokens binderArity
      (compactFormulaParserInitialState binderArity tokens) := by
  refine ⟨List.suffix_refl tokens, ?_, by simp [
    compactFormulaParserInitialState]⟩
  intro task htask
  simp only [compactFormulaParserInitialState, List.mem_cons,
    List.not_mem_nil, or_false] at htask
  subst task
  exact compactFormulaTask_within (by rfl)

theorem compactSyntaxParser_iterate_preserves_source
    (initialTokens : List Nat) (binderCap stepCount : Nat)
    (state : CompactSyntaxParserState)
    (hsource : CompactSyntaxParserStateSourceOf
      initialTokens binderCap state) :
    CompactSyntaxParserStateSourceOf initialTokens
      (binderCap + stepCount)
      ((compactSyntaxParserStep^[stepCount]) state) := by
  induction stepCount generalizing binderCap state with
  | zero => simpa
  | succ stepCount ih =>
      rw [Function.iterate_succ_apply]
      have hstep := compactSyntaxParserStep_preserves_source
        initialTokens binderCap state hsource
      have htail := ih (binderCap + 1) _ hstep
      convert htail using 1 <;> omega

theorem compactFormulaParserStateAt_source
    (binderArity : Nat) (tokens : List Nat) (stepIndex : Nat) :
    CompactSyntaxParserStateSourceOf tokens (binderArity + stepIndex)
      (compactParserStateAt compactSyntaxParserStep
        (compactFormulaParserInitialState binderArity tokens)
        stepIndex) := by
  unfold compactParserStateAt
  exact compactSyntaxParser_iterate_preserves_source tokens binderArity
    stepIndex _ (compactFormulaParserInitialState_source binderArity tokens)

theorem compactTermTokenStep_task_length_le
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    (compactTermTokenStep (binderArity, tokens, tasks)).2.1.length <=
      tasks.length + 1 := by
  by_cases hlengthTwo : 2 <= tokens.length
  · by_cases htagZero : compactTokenAt 0 tokens = 0
    · by_cases hbound : compactTokenAt 1 tokens < binderArity <;>
        simp [compactTermTokenStep, hlengthTwo, htagZero, hbound,
          compactSyntaxContinue, compactSyntaxFailure]
    · by_cases htagOne : compactTokenAt 0 tokens = 1
      · simp [compactTermTokenStep, hlengthTwo, htagZero, htagOne,
          compactSyntaxContinue]
      · by_cases htagTwo : compactTokenAt 0 tokens = 2
        · by_cases hlengthThree : 3 <= tokens.length
          · by_cases hvalid : ArithmeticFuncCodeValid
                (compactTokenAt 1 tokens) (compactTokenAt 2 tokens) <;>
              simp [compactTermTokenStep, hlengthTwo, htagZero, htagOne,
                htagTwo, hlengthThree, hvalid, compactSyntaxContinue,
                compactSyntaxFailure]
          · simp [compactTermTokenStep, hlengthTwo, htagZero, htagOne,
              htagTwo, hlengthThree, compactSyntaxFailure]
        · simp [compactTermTokenStep, hlengthTwo, htagZero, htagOne,
            htagTwo, compactSyntaxFailure]
  · simp [compactTermTokenStep, hlengthTwo, compactSyntaxFailure]

theorem compactFormulaTokenStep_task_length_le
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    (compactFormulaTokenStep (binderArity, tokens, tasks)).2.1.length <=
      tasks.length + 2 := by
  by_cases hlengthOne : 1 <= tokens.length
  · by_cases htagZero : compactTokenAt 0 tokens = 0
    · by_cases hlengthThree : 3 <= tokens.length
      · by_cases hvalid : ArithmeticRelCodeValid
            (compactTokenAt 1 tokens) (compactTokenAt 2 tokens) <;>
          simp [compactFormulaTokenStep, hlengthOne, htagZero,
            hlengthThree, hvalid, compactSyntaxContinue,
            compactSyntaxFailure]
      · simp [compactFormulaTokenStep, hlengthOne, htagZero,
          hlengthThree, compactSyntaxFailure]
    · by_cases htagOne : compactTokenAt 0 tokens = 1
      · by_cases hlengthThree : 3 <= tokens.length
        · by_cases hvalid : ArithmeticRelCodeValid
              (compactTokenAt 1 tokens) (compactTokenAt 2 tokens) <;>
            simp [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
              hlengthThree, hvalid, compactSyntaxContinue,
              compactSyntaxFailure]
        · simp [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
            hlengthThree, compactSyntaxFailure]
      · by_cases htagTwo : compactTokenAt 0 tokens = 2
        · simp [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
            htagTwo, compactSyntaxContinue]
        · by_cases htagThree : compactTokenAt 0 tokens = 3
          · simp [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
              htagTwo, htagThree, compactSyntaxContinue]
          · by_cases htagFour : compactTokenAt 0 tokens = 4
            · simp [compactFormulaTokenStep, hlengthOne, htagZero, htagOne,
                htagTwo, htagThree, htagFour, compactSyntaxContinue]
            · by_cases htagFive : compactTokenAt 0 tokens = 5
              · simp [compactFormulaTokenStep, hlengthOne, htagZero,
                  htagOne, htagTwo, htagThree, htagFour, htagFive,
                  compactSyntaxContinue]
              · by_cases htagSix : compactTokenAt 0 tokens = 6
                · simp [compactFormulaTokenStep, hlengthOne, htagZero,
                    htagOne, htagTwo, htagThree, htagFour, htagFive,
                    htagSix, compactSyntaxContinue]
                · by_cases htagSeven : compactTokenAt 0 tokens = 7
                  · simp [compactFormulaTokenStep, hlengthOne, htagZero,
                      htagOne, htagTwo, htagThree, htagFour, htagFive,
                      htagSix, htagSeven, compactSyntaxContinue]
                  · simp [compactFormulaTokenStep, hlengthOne, htagZero,
                      htagOne, htagTwo, htagThree, htagFour, htagFive,
                      htagSix, htagSeven, compactSyntaxFailure]
  · simp [compactFormulaTokenStep, hlengthOne, compactSyntaxFailure]

theorem compactRepeatTermTokenStep_task_length_le
    (task : CompactSyntaxTask) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    (compactRepeatTermTokenStep (task, tokens, tasks)).2.1.length <=
      tasks.length + 2 := by
  by_cases hzero : task.2.2 = 0 <;>
    simp [compactRepeatTermTokenStep, hzero, compactSyntaxContinue]

theorem compactSyntaxTaskTokenStep_task_length_le
    (task : CompactSyntaxTask) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    (compactSyntaxTaskTokenStep (task, tokens, tasks)).2.1.length <=
      tasks.length + 2 := by
  by_cases hterm : task.1 = 0
  · have hraw := compactTermTokenStep_task_length_le
      task.2.1 tokens tasks
    have hweaken :
        (compactTermTokenStep (task.2.1, tokens, tasks)).2.1.length <=
          tasks.length + 2 := by omega
    simpa [compactSyntaxTaskTokenStep, hterm] using hweaken
  by_cases hformula : task.1 = 1
  · simpa [compactSyntaxTaskTokenStep, hterm, hformula] using
      compactFormulaTokenStep_task_length_le task.2.1 tokens tasks
  by_cases hrepeat : task.1 = 2
  · simpa [compactSyntaxTaskTokenStep, hterm, hformula, hrepeat] using
      compactRepeatTermTokenStep_task_length_le task tokens tasks
  simp [compactSyntaxTaskTokenStep, hterm, hformula, hrepeat,
    compactSyntaxFailure]

theorem compactSyntaxParserStep_task_length_le
    (state : CompactSyntaxParserState) :
    (compactSyntaxParserStep state).2.1.length <=
      state.2.1.length + 1 := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | some result => simp [compactSyntaxParserStep]
  | none =>
      cases tasks with
      | nil => simp [compactSyntaxParserStep, compactSyntaxRunningStep]
      | cons task restTasks =>
          simpa [compactSyntaxParserStep, compactSyntaxRunningStep] using
            compactSyntaxTaskTokenStep_task_length_le
              task tokens restTasks

theorem compactSyntaxParser_iterate_task_length_le
    (stepCount : Nat) (state : CompactSyntaxParserState) :
    ((compactSyntaxParserStep^[stepCount]) state).2.1.length <=
      state.2.1.length + stepCount := by
  induction stepCount generalizing state with
  | zero => simp
  | succ stepCount ih =>
      rw [Function.iterate_succ_apply]
      have hstep := compactSyntaxParserStep_task_length_le state
      have htail := ih (compactSyntaxParserStep state)
      omega

theorem compactFormulaParserStateAt_task_length_le
    (binderArity : Nat) (tokens : List Nat) (stepIndex : Nat) :
    (compactParserStateAt compactSyntaxParserStep
      (compactFormulaParserInitialState binderArity tokens)
      stepIndex).2.1.length <= 1 + stepIndex := by
  unfold compactParserStateAt
  have hraw := compactSyntaxParser_iterate_task_length_le stepIndex
    (compactFormulaParserInitialState binderArity tokens)
  simpa [compactFormulaParserInitialState] using hraw

theorem compactFormulaParserLocalTrace_member_source
    {binderArity : Nat} {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactSyntaxParserStep fuel
      (compactFormulaParserInitialState binderArity tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    CompactSyntaxParserStateSourceOf tokens (binderArity + fuel) state := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical := compactParserLocalTraceValid_stateAt hvalid hle
  unfold compactParserTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = compactParserStateAt compactSyntaxParserStep
      (compactFormulaParserInitialState binderArity tokens) stepIndex :=
    Option.some.inj hcanonical
  rw [heq]
  exact CompactSyntaxParserStateSourceOf.mono
    (compactFormulaParserStateAt_source binderArity tokens stepIndex)
    (by omega)

theorem compactFormulaParserLocalTrace_member_task_length_le
    {binderArity : Nat} {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactSyntaxParserStep fuel
      (compactFormulaParserInitialState binderArity tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    state.2.1.length <= 1 + fuel := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical := compactParserLocalTraceValid_stateAt hvalid hle
  unfold compactParserTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = compactParserStateAt compactSyntaxParserStep
      (compactFormulaParserInitialState binderArity tokens) stepIndex :=
    Option.some.inj hcanonical
  rw [heq]
  have hraw := compactFormulaParserStateAt_task_length_le
    binderArity tokens stepIndex
  omega

def compactNumericSyntaxParserTaskWeightBound
    (streamWeight binderCap : Nat) : Nat :=
  (Nat.size 2 + 1) + (Nat.size binderCap + 1) + streamWeight

theorem CompactSyntaxParserTaskWithin.weight_le
    {initialTokens : List Nat} {binderCap : Nat}
    {task : CompactSyntaxTask}
    (htask : CompactSyntaxParserTaskWithin
      initialTokens binderCap task) :
    compactAdditiveValueWeight task <=
      compactNumericSyntaxParserTaskWeightBound
        (compactAdditiveValueWeight initialTokens) binderCap := by
  unfold CompactSyntaxParserTaskWithin at htask
  have hkind := Nat.size_le_size htask.1
  have hbinder := Nat.size_le_size htask.2.1
  rw [compactAdditiveValueWeight_prod,
    compactAdditiveValueWeight_prod,
    compactAdditiveValueWeight_nat,
    compactAdditiveValueWeight_nat]
  unfold compactNumericSyntaxParserTaskWeightBound
  omega

theorem compactNumericSyntaxParserTaskWeightBound_mono
    {streamLeft streamRight binderLeft binderRight : Nat}
    (hstream : streamLeft <= streamRight)
    (hbinder : binderLeft <= binderRight) :
    compactNumericSyntaxParserTaskWeightBound streamLeft binderLeft <=
      compactNumericSyntaxParserTaskWeightBound streamRight binderRight := by
  have hsize := Nat.size_le_size hbinder
  unfold compactNumericSyntaxParserTaskWeightBound
  omega

theorem CompactSyntaxParserStateSourceOf.status_weight_le
    {initialTokens : List Nat} {binderCap : Nat}
    {state : CompactSyntaxParserState}
    (hsource : CompactSyntaxParserStateSourceOf
      initialTokens binderCap state) :
    compactAdditiveValueWeight state.2.2 <=
      4 + compactAdditiveValueWeight initialTokens := by
  have hstream := compactAdditiveValueWeight_suffix_le hsource.1
  rcases hsource.2.2 with hnone | hstatus
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

def compactNumericFormulaParserStateWeightBound
    (streamWeight binderCap fuel : Nat) : Nat :=
  streamWeight +
    (Nat.size (1 + fuel) + 1 +
      (1 + fuel) *
        compactNumericSyntaxParserTaskWeightBound
          streamWeight binderCap) +
    (4 + streamWeight)

theorem compactNumericFormulaParserStateWeightBound_mono
    {streamLeft streamRight binderLeft binderRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft <= streamRight)
    (hbinder : binderLeft <= binderRight)
    (hfuel : fuelLeft <= fuelRight) :
    compactNumericFormulaParserStateWeightBound
        streamLeft binderLeft fuelLeft <=
      compactNumericFormulaParserStateWeightBound
        streamRight binderRight fuelRight := by
  have hfuelAdd : 1 + fuelLeft <= 1 + fuelRight := by omega
  have hfuelSize := Nat.size_le_size hfuelAdd
  have htask := compactNumericSyntaxParserTaskWeightBound_mono
    hstream hbinder
  have htaskList := Nat.mul_le_mul hfuelAdd htask
  unfold compactNumericFormulaParserStateWeightBound
  omega

theorem compactFormulaParserLocalTrace_member_state_weight_le
    {binderArity : Nat} {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactSyntaxParserStep fuel
      (compactFormulaParserInitialState binderArity tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    compactAdditiveValueWeight state <=
      compactNumericFormulaParserStateWeightBound
        (compactAdditiveValueWeight tokens) (binderArity + fuel) fuel := by
  have hsource := compactFormulaParserLocalTrace_member_source hvalid hstate
  have hstream := compactAdditiveValueWeight_suffix_le hsource.1
  have htaskLength :=
    compactFormulaParserLocalTrace_member_task_length_le hvalid hstate
  have htasksRaw := compactAdditiveValueWeight_list_le state.2.1
    (compactNumericSyntaxParserTaskWeightBound
      (compactAdditiveValueWeight tokens) (binderArity + fuel))
    (fun task htask => (hsource.2.1 task htask).weight_le)
  have htaskSize := Nat.size_le_size htaskLength
  have htaskProduct := Nat.mul_le_mul_right
    (compactNumericSyntaxParserTaskWeightBound
      (compactAdditiveValueWeight tokens) (binderArity + fuel))
    htaskLength
  have htasks : compactAdditiveValueWeight state.2.1 <=
      Nat.size (1 + fuel) + 1 + (1 + fuel) *
        compactNumericSyntaxParserTaskWeightBound
          (compactAdditiveValueWeight tokens) (binderArity + fuel) := by
    omega
  have hstatus := hsource.status_weight_le
  rw [compactAdditiveValueWeight_prod,
    compactAdditiveValueWeight_prod]
  unfold compactNumericFormulaParserStateWeightBound
  omega

def compactNumericFormulaParserTraceWeightBound
    (streamWeight binderArity fuel : Nat) : Nat :=
  Nat.size (fuel + 1) + 1 +
    (fuel + 1) *
      compactNumericFormulaParserStateWeightBound
        streamWeight (binderArity + fuel) fuel

theorem compactNumericFormulaParserTraceWeightBound_mono
    {streamLeft streamRight binderLeft binderRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft <= streamRight)
    (hbinder : binderLeft <= binderRight)
    (hfuel : fuelLeft <= fuelRight) :
    compactNumericFormulaParserTraceWeightBound
        streamLeft binderLeft fuelLeft <=
      compactNumericFormulaParserTraceWeightBound
        streamRight binderRight fuelRight := by
  have hfuelAdd : fuelLeft + 1 <= fuelRight + 1 := by omega
  have hfuelSize := Nat.size_le_size hfuelAdd
  have hbinderFuel : binderLeft + fuelLeft <=
      binderRight + fuelRight := by omega
  have hstate := compactNumericFormulaParserStateWeightBound_mono
    hstream hbinderFuel hfuel
  have htable := Nat.mul_le_mul hfuelAdd hstate
  unfold compactNumericFormulaParserTraceWeightBound
  omega

theorem compactFormulaTokenParserDirectTraceValid_weight_le
    {binderArity : Nat} {tokens suffix : List Nat}
    {states : CompactFormulaTokenParserDirectTrace}
    (hvalid : CompactFormulaTokenParserDirectTraceValid
      binderArity tokens suffix states) :
    compactAdditiveValueWeight states <=
      compactNumericFormulaParserTraceWeightBound
        (compactAdditiveValueWeight tokens) binderArity
        (compactSyntaxRunFuelBound tokens) := by
  have hlocal := hvalid.1
  have hrows := compactAdditiveValueWeight_list_le states
    (compactNumericFormulaParserStateWeightBound
      (compactAdditiveValueWeight tokens)
      (binderArity + compactSyntaxRunFuelBound tokens)
      (compactSyntaxRunFuelBound tokens))
    (fun state hstate =>
      compactFormulaParserLocalTrace_member_state_weight_le
        hlocal hstate)
  unfold compactNumericFormulaParserTraceWeightBound
  rw [hlocal.1] at hrows
  exact hrows

theorem compactSyntaxRunFuelBound_le_weightBound
    {tokens : List Nat} {streamWeight : Nat}
    (hweight : compactAdditiveValueWeight tokens <= streamWeight) :
    compactSyntaxRunFuelBound tokens <=
      compactNumericCertificateParserFuelWeightBound streamWeight := by
  have hlength := compactAdditiveValueWeight_natList_length_le tokens
  have hlengthWeight : tokens.length + 1 <= streamWeight + 1 := by omega
  have hscaled := Nat.mul_le_mul_left 16 hlengthWeight
  have hquadratic := Nat.mul_le_mul hscaled hlengthWeight
  unfold compactSyntaxRunFuelBound
    compactNumericCertificateParserFuelWeightBound
  omega

def compactNumericFormulaParserPublicTraceWeightBound
    (bitLength : Nat) : Nat :=
  let streamWeight := compactNumericDecodedTokenListWeightBound bitLength
  let fuel := compactNumericCertificateParserFuelWeightBound streamWeight
  compactNumericFormulaParserTraceWeightBound streamWeight 0 fuel

theorem compactNumericListedDirectTrace_formulaParserTrace_weight_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight
        (compactNumericDirectTraceFormulaParserTrace trace) <=
      compactNumericFormulaParserPublicTraceWeightBound
        (Nat.size formulaCode) := by
  have hfull := hvalid
  unfold CompactNumericListedDirectTraceValid at hfull
  have hparser : CompactFormulaTokenParserDirectTraceValid 0
      (compactNumericDirectTraceFormulaTokens trace) []
      (compactNumericDirectTraceFormulaParserTrace trace) :=
    hfull.2.2.2.2.1
  have hraw := compactFormulaTokenParserDirectTraceValid_weight_le hparser
  have htokens :=
    compactNumericListedDirectTrace_formulaTokens_weight_le hvalid
  have hfuel := compactSyntaxRunFuelBound_le_weightBound htokens
  unfold compactNumericFormulaParserPublicTraceWeightBound
  exact hraw.trans
    (compactNumericFormulaParserTraceWeightBound_mono
      htokens (by rfl) hfuel)

/-! ## Listed-proof parser state trace -/

def CompactProofParserTaskWithin
    (initialTokens : List Nat) (task : CompactProofParserTask) : Prop :=
  task.1 <= 8 ∧
    task.2.1 <= 1 ∧
    compactAdditiveValueWeight task.2.2 <=
      compactAdditiveValueWeight initialTokens

theorem compactProofTask_within
    (initialTokens : List Nat) :
    CompactProofParserTaskWithin initialTokens compactProofTask := by
  refine ⟨by simp [compactProofTask], by simp [compactProofTask], ?_⟩
  simpa [compactProofTask] using
    compactAdditiveValueWeight_list_pos initialTokens

theorem compactProofFormulaTask_within
    {initialTokens : List Nat} {binderArity : Nat}
    (hbinder : binderArity <= 1) :
    CompactProofParserTaskWithin initialTokens
      (compactProofFormulaTask binderArity) := by
  refine ⟨by simp [compactProofFormulaTask],
    by simpa [compactProofFormulaTask], ?_⟩
  simpa [compactProofFormulaTask] using
    compactAdditiveValueWeight_list_pos initialTokens

theorem compactProofClosedFormulaTask_within
    {initialTokens : List Nat} {binderArity : Nat}
    (hbinder : binderArity <= 1) :
    CompactProofParserTaskWithin initialTokens
      (compactProofClosedFormulaTask binderArity) := by
  refine ⟨by simp [compactProofClosedFormulaTask],
    by simpa [compactProofClosedFormulaTask], ?_⟩
  simpa [compactProofClosedFormulaTask] using
    compactAdditiveValueWeight_list_pos initialTokens

theorem compactProofTermTask_within
    {initialTokens : List Nat} {binderArity : Nat}
    (hbinder : binderArity <= 1) :
    CompactProofParserTaskWithin initialTokens
      (compactProofTermTask binderArity) := by
  refine ⟨by simp [compactProofTermTask],
    by simpa [compactProofTermTask], ?_⟩
  simpa [compactProofTermTask] using
    compactAdditiveValueWeight_list_pos initialTokens

theorem compactProofRepeatFormulaTask_within
    {initialTokens : List Nat} {count : Nat}
    (hcount : compactAdditiveValueWeight count <=
      compactAdditiveValueWeight initialTokens) :
    CompactProofParserTaskWithin initialTokens
      (compactProofRepeatFormulaTask count) := by
  refine ⟨by simp [compactProofRepeatFormulaTask],
    by simp [compactProofRepeatFormulaTask], ?_⟩
  simpa [compactProofRepeatFormulaTask] using hcount

theorem compactProofSequentTask_within
    (initialTokens : List Nat) :
    CompactProofParserTaskWithin initialTokens compactProofSequentTask := by
  refine ⟨by simp [compactProofSequentTask],
    by simp [compactProofSequentTask], ?_⟩
  simpa [compactProofSequentTask] using
    compactAdditiveValueWeight_list_pos initialTokens

def CompactProofParserStateSourceOf
    (initialTokens : List Nat) (state : CompactProofParserState) : Prop :=
  state.1 <:+ initialTokens ∧
    (∀ task ∈ state.2.1,
      CompactProofParserTaskWithin initialTokens task) ∧
    (state.2.2 = none ∨ state.2.2 = some none ∨
      state.2.2 = some (some state.1))

theorem compactProofParserStateSource_continue
    {initialTokens tokens : List Nat}
    {tasks : List CompactProofParserTask}
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks,
      CompactProofParserTaskWithin initialTokens task) :
    CompactProofParserStateSourceOf initialTokens
      (compactSyntaxContinue tokens tasks) := by
  exact ⟨hstream, htasks, by simp [compactSyntaxContinue]⟩

theorem compactProofParserStateSource_failure
    {initialTokens tokens : List Nat}
    {tasks : List CompactProofParserTask}
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks,
      CompactProofParserTaskWithin initialTokens task) :
    CompactProofParserStateSourceOf initialTokens
      (compactSyntaxFailure tokens tasks) := by
  exact ⟨hstream, htasks, by simp [compactSyntaxFailure]⟩

theorem compactProofParserStateSource_continue_prepend
    {initialTokens tokens : List Nat}
    {newTasks tasks : List CompactProofParserTask}
    (hstream : tokens <:+ initialTokens)
    (hnew : ∀ task ∈ newTasks,
      CompactProofParserTaskWithin initialTokens task)
    (htasks : ∀ task ∈ tasks,
      CompactProofParserTaskWithin initialTokens task) :
    CompactProofParserStateSourceOf initialTokens
      (compactSyntaxContinue tokens (newTasks ++ tasks)) := by
  apply compactProofParserStateSource_continue hstream
  intro task htask
  simp only [List.mem_append] at htask
  rcases htask with htask | htask
  · exact hnew task htask
  · exact htasks task htask

theorem compactFormulaTokenParser_suffix_of_success
    {binderArity : Nat} {tokens suffix : List Nat}
    (hparser : compactFormulaTokenParser binderArity tokens = some suffix) :
    suffix <:+ tokens := by
  obtain ⟨formula, htokens⟩ :=
    (compactFormulaTokenParser_success_iff
      binderArity tokens suffix).mp hparser
  exact ⟨compactArithmeticFormulaTokens formula, htokens.symm⟩

theorem compactTermTokenParser_suffix_of_success
    {binderArity : Nat} {tokens suffix : List Nat}
    (hparser : compactTermTokenParser binderArity tokens = some suffix) :
    suffix <:+ tokens := by
  obtain ⟨term, htokens⟩ :=
    (compactTermTokenParser_success_iff
      binderArity tokens suffix).mp hparser
  exact ⟨compactArithmeticTermTokens term, htokens.symm⟩

theorem compactClosedFormulaTokenParser_suffix_of_success
    {binderArity : Nat} {tokens suffix : List Nat}
    (hparser : compactClosedFormulaTokenParser
      binderArity tokens = some suffix) :
    suffix <:+ tokens := by
  obtain ⟨formula, _hclosed, htokens⟩ :=
    (compactClosedFormulaTokenParser_success_iff
      binderArity tokens suffix).mp hparser
  exact ⟨compactArithmeticFormulaTokens formula, htokens.symm⟩

theorem compactProofFormulaTokenStep_preserves_source
    {initialTokens tokens : List Nat} {binderArity : Nat}
    {tasks : List CompactProofParserTask}
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks,
      CompactProofParserTaskWithin initialTokens task) :
    CompactProofParserStateSourceOf initialTokens
      (compactProofFormulaTokenStep (binderArity, tokens, tasks)) := by
  cases hparser : compactFormulaTokenParser binderArity tokens with
  | none =>
      rw [compactProofFormulaTokenStep, hparser]
      exact compactProofParserStateSource_failure hstream htasks
  | some suffix =>
      have hsuffix :=
        (compactFormulaTokenParser_suffix_of_success hparser).trans hstream
      rw [compactProofFormulaTokenStep, hparser]
      exact compactProofParserStateSource_continue hsuffix htasks

theorem compactProofTermTokenStep_preserves_source
    {initialTokens tokens : List Nat} {binderArity : Nat}
    {tasks : List CompactProofParserTask}
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks,
      CompactProofParserTaskWithin initialTokens task) :
    CompactProofParserStateSourceOf initialTokens
      (compactProofTermTokenStep (binderArity, tokens, tasks)) := by
  cases hparser : compactTermTokenParser binderArity tokens with
  | none =>
      rw [compactProofTermTokenStep, hparser]
      exact compactProofParserStateSource_failure hstream htasks
  | some suffix =>
      have hsuffix :=
        (compactTermTokenParser_suffix_of_success hparser).trans hstream
      rw [compactProofTermTokenStep, hparser]
      exact compactProofParserStateSource_continue hsuffix htasks

theorem compactProofClosedFormulaTokenStep_preserves_source
    {initialTokens tokens : List Nat} {binderArity : Nat}
    {tasks : List CompactProofParserTask}
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks,
      CompactProofParserTaskWithin initialTokens task) :
    CompactProofParserStateSourceOf initialTokens
      (compactProofClosedFormulaTokenStep
        (binderArity, tokens, tasks)) := by
  cases hparser : compactClosedFormulaTokenParser binderArity tokens with
  | none =>
      rw [compactProofClosedFormulaTokenStep, hparser]
      exact compactProofParserStateSource_failure hstream htasks
  | some suffix =>
      have hsuffix :=
        (compactClosedFormulaTokenParser_suffix_of_success hparser).trans
          hstream
      rw [compactProofClosedFormulaTokenStep, hparser]
      exact compactProofParserStateSource_continue hsuffix htasks

theorem compactProofRepeatFormulaTokenStep_preserves_source
    {initialTokens tokens : List Nat}
    {task : CompactProofParserTask}
    {tasks : List CompactProofParserTask}
    (htask : CompactProofParserTaskWithin initialTokens task)
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ oldTask ∈ tasks,
      CompactProofParserTaskWithin initialTokens oldTask) :
    CompactProofParserStateSourceOf initialTokens
      (compactProofRepeatFormulaTokenStep (task, tokens, tasks)) := by
  unfold CompactProofParserTaskWithin at htask
  by_cases hzero : task.2.2 = 0
  · simpa [compactProofRepeatFormulaTokenStep, hzero] using
      compactProofParserStateSource_continue hstream htasks
  · have hformula := compactProofFormulaTask_within
        (initialTokens := initialTokens) (binderArity := 0) (by omega)
    have hcount : compactAdditiveValueWeight (task.2.2 - 1) <=
        compactAdditiveValueWeight initialTokens :=
      (compactAdditiveValueWeight_nat_sub_le task.2.2 1).trans htask.2.2
    have hrepeat := compactProofRepeatFormulaTask_within hcount
    have hnew : ∀ nextTask ∈
        [compactProofFormulaTask 0,
          compactProofRepeatFormulaTask (task.2.2 - 1)],
        CompactProofParserTaskWithin initialTokens nextTask := by
      intro nextTask hnext
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
      rcases hnext with rfl | rfl
      · exact hformula
      · exact hrepeat
    simpa [compactProofRepeatFormulaTokenStep, hzero] using
      compactProofParserStateSource_continue_prepend
        hstream hnew htasks

theorem compactProofSequentTokenStep_preserves_source
    {initialTokens tokens : List Nat}
    {tasks : List CompactProofParserTask}
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks,
      CompactProofParserTaskWithin initialTokens task) :
    CompactProofParserStateSourceOf initialTokens
      (compactProofSequentTokenStep tokens tasks) := by
  cases tokens with
  | nil =>
      simpa [compactProofSequentTokenStep] using
        compactProofParserStateSource_failure hstream htasks
  | cons count suffix =>
      have hsuffix : suffix <:+ initialTokens :=
        (List.suffix_cons count suffix).trans hstream
      have hcount : compactAdditiveValueWeight count <=
          compactAdditiveValueWeight initialTokens := by
        simpa [compactTokenAt] using
          compactTokenAt_weight_le_of_suffix hstream 0
      have hrepeat := compactProofRepeatFormulaTask_within hcount
      have hnew : ∀ nextTask ∈ [compactProofRepeatFormulaTask count],
          CompactProofParserTaskWithin initialTokens nextTask := by
        intro nextTask hnext
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
        subst nextTask
        exact hrepeat
      simpa [compactProofSequentTokenStep] using
        compactProofParserStateSource_continue_prepend
          hsuffix hnew htasks

theorem compactProofNodeTokenStep_preserves_source
    {initialTokens tokens : List Nat}
    {tasks : List CompactProofParserTask}
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks,
      CompactProofParserTaskWithin initialTokens task) :
    CompactProofParserStateSourceOf initialTokens
      (compactProofNodeTokenStep tokens tasks) := by
  have hproof := compactProofTask_within initialTokens
  have hformulaZero := compactProofFormulaTask_within
    (initialTokens := initialTokens) (binderArity := 0) (by omega)
  have hformulaOne := compactProofFormulaTask_within
    (initialTokens := initialTokens) (binderArity := 1) (by omega)
  have hclosedZero := compactProofClosedFormulaTask_within
    (initialTokens := initialTokens) (binderArity := 0) (by omega)
  have htermZero := compactProofTermTask_within
    (initialTokens := initialTokens) (binderArity := 0) (by omega)
  have hsequent := compactProofSequentTask_within initialTokens
  cases tokens with
  | nil =>
      simpa [compactProofNodeTokenStep] using
        compactProofParserStateSource_failure hstream htasks
  | cons tag suffix =>
      have hsuffix : suffix <:+ initialTokens :=
        (List.suffix_cons tag suffix).trans hstream
      by_cases h0 : tag = 0
      · have hnew : ∀ nextTask ∈
            [compactProofSequentTask, compactProofFormulaTask 0],
            CompactProofParserTaskWithin initialTokens nextTask := by
          intro nextTask hnext
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
          rcases hnext with rfl | rfl
          · exact hsequent
          · exact hformulaZero
        simpa [compactProofNodeTokenStep, h0] using
          compactProofParserStateSource_continue_prepend
            hsuffix hnew htasks
      by_cases h1 : tag = 1
      · have hnew : ∀ nextTask ∈
            [compactProofSequentTask, compactProofClosedFormulaTask 0],
            CompactProofParserTaskWithin initialTokens nextTask := by
          intro nextTask hnext
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
          rcases hnext with rfl | rfl
          · exact hsequent
          · exact hclosedZero
        simpa [compactProofNodeTokenStep, h0, h1] using
          compactProofParserStateSource_continue_prepend
            hsuffix hnew htasks
      by_cases h2 : tag = 2
      · have hnew : ∀ nextTask ∈ [compactProofSequentTask],
            CompactProofParserTaskWithin initialTokens nextTask := by
          intro nextTask hnext
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
          subst nextTask
          exact hsequent
        simpa [compactProofNodeTokenStep, h0, h1, h2] using
          compactProofParserStateSource_continue_prepend
            hsuffix hnew htasks
      by_cases h3 : tag = 3
      · have hnew : ∀ nextTask ∈
            [compactProofSequentTask, compactProofFormulaTask 0,
              compactProofFormulaTask 0, compactProofTask,
              compactProofTask],
            CompactProofParserTaskWithin initialTokens nextTask := by
          intro nextTask hnext
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
          rcases hnext with rfl | rfl | rfl | rfl | rfl
          · exact hsequent
          · exact hformulaZero
          · exact hformulaZero
          · exact hproof
          · exact hproof
        simpa [compactProofNodeTokenStep, h0, h1, h2, h3] using
          compactProofParserStateSource_continue_prepend
            hsuffix hnew htasks
      by_cases h4 : tag = 4
      · have hnew : ∀ nextTask ∈
            [compactProofSequentTask, compactProofFormulaTask 0,
              compactProofFormulaTask 0, compactProofTask],
            CompactProofParserTaskWithin initialTokens nextTask := by
          intro nextTask hnext
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
          rcases hnext with rfl | rfl | rfl | rfl
          · exact hsequent
          · exact hformulaZero
          · exact hformulaZero
          · exact hproof
        simpa [compactProofNodeTokenStep, h0, h1, h2, h3, h4] using
          compactProofParserStateSource_continue_prepend
            hsuffix hnew htasks
      by_cases h5 : tag = 5
      · have hnew : ∀ nextTask ∈
            [compactProofSequentTask, compactProofFormulaTask 1,
              compactProofTask],
            CompactProofParserTaskWithin initialTokens nextTask := by
          intro nextTask hnext
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
          rcases hnext with rfl | rfl | rfl
          · exact hsequent
          · exact hformulaOne
          · exact hproof
        simpa [compactProofNodeTokenStep, h0, h1, h2, h3, h4, h5] using
          compactProofParserStateSource_continue_prepend
            hsuffix hnew htasks
      by_cases h6 : tag = 6
      · have hnew : ∀ nextTask ∈
            [compactProofSequentTask, compactProofFormulaTask 1,
              compactProofTermTask 0, compactProofTask],
            CompactProofParserTaskWithin initialTokens nextTask := by
          intro nextTask hnext
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
          rcases hnext with rfl | rfl | rfl | rfl
          · exact hsequent
          · exact hformulaOne
          · exact htermZero
          · exact hproof
        simpa [compactProofNodeTokenStep, h0, h1, h2, h3, h4, h5, h6] using
          compactProofParserStateSource_continue_prepend
            hsuffix hnew htasks
      by_cases h7 : tag = 7
      · have hnew : ∀ nextTask ∈
            [compactProofSequentTask, compactProofTask],
            CompactProofParserTaskWithin initialTokens nextTask := by
          intro nextTask hnext
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
          rcases hnext with rfl | rfl
          · exact hsequent
          · exact hproof
        simpa [compactProofNodeTokenStep, h0, h1, h2, h3, h4, h5, h6,
          h7] using compactProofParserStateSource_continue_prepend
            hsuffix hnew htasks
      by_cases h8 : tag = 8
      · have hnew : ∀ nextTask ∈
            [compactProofSequentTask, compactProofTask],
            CompactProofParserTaskWithin initialTokens nextTask := by
          intro nextTask hnext
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
          rcases hnext with rfl | rfl
          · exact hsequent
          · exact hproof
        simpa [compactProofNodeTokenStep, h0, h1, h2, h3, h4, h5, h6,
          h7, h8] using compactProofParserStateSource_continue_prepend
            hsuffix hnew htasks
      by_cases h9 : tag = 9
      · have hnew : ∀ nextTask ∈
            [compactProofSequentTask, compactProofFormulaTask 0,
              compactProofTask, compactProofTask],
            CompactProofParserTaskWithin initialTokens nextTask := by
          intro nextTask hnext
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
          rcases hnext with rfl | rfl | rfl | rfl
          · exact hsequent
          · exact hformulaZero
          · exact hproof
          · exact hproof
        simpa [compactProofNodeTokenStep, h0, h1, h2, h3, h4, h5, h6,
          h7, h8, h9] using
          compactProofParserStateSource_continue_prepend
            hsuffix hnew htasks
      simpa [compactProofNodeTokenStep, h0, h1, h2, h3, h4, h5, h6,
        h7, h8, h9] using
        compactProofParserStateSource_failure hstream htasks

theorem compactProofParserTaskTokenStep_preserves_source
    {initialTokens tokens : List Nat}
    {task : CompactProofParserTask}
    {tasks : List CompactProofParserTask}
    (htask : CompactProofParserTaskWithin initialTokens task)
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ oldTask ∈ tasks,
      CompactProofParserTaskWithin initialTokens oldTask) :
    CompactProofParserStateSourceOf initialTokens
      (compactProofParserTaskTokenStep (task, tokens, tasks)) := by
  by_cases hproof : task.1 = 3
  · simpa [compactProofParserTaskTokenStep, hproof] using
      compactProofNodeTokenStep_preserves_source hstream htasks
  by_cases hformula : task.1 = 4
  · simpa [compactProofParserTaskTokenStep, hproof, hformula] using
      compactProofFormulaTokenStep_preserves_source hstream htasks
  by_cases hterm : task.1 = 5
  · simpa [compactProofParserTaskTokenStep, hproof, hformula, hterm] using
      compactProofTermTokenStep_preserves_source hstream htasks
  by_cases hrepeat : task.1 = 6
  · simpa [compactProofParserTaskTokenStep, hproof, hformula, hterm,
      hrepeat] using compactProofRepeatFormulaTokenStep_preserves_source
        htask hstream htasks
  by_cases hsequent : task.1 = 7
  · simpa [compactProofParserTaskTokenStep, hproof, hformula, hterm,
      hrepeat, hsequent] using
        compactProofSequentTokenStep_preserves_source hstream htasks
  by_cases hclosed : task.1 = 8
  · simpa [compactProofParserTaskTokenStep, hproof, hformula, hterm,
      hrepeat, hsequent, hclosed] using
        compactProofClosedFormulaTokenStep_preserves_source hstream htasks
  simpa [compactProofParserTaskTokenStep, hproof, hformula, hterm,
    hrepeat, hsequent, hclosed] using
    compactProofParserStateSource_failure hstream htasks

theorem compactProofParserStep_preserves_source
    (initialTokens : List Nat) (state : CompactProofParserState)
    (hsource : CompactProofParserStateSourceOf initialTokens state) :
    CompactProofParserStateSourceOf initialTokens
      (compactProofParserStep state) := by
  rcases state with ⟨tokens, tasks, status⟩
  rcases hsource with ⟨hstream, htasks, hstatus⟩
  cases status with
  | some result =>
      simpa [compactProofParserStep] using
        (show CompactProofParserStateSourceOf initialTokens
          (tokens, tasks, some result) from ⟨hstream, htasks, hstatus⟩)
  | none =>
      cases tasks with
      | nil =>
          exact ⟨hstream, by simp,
            by simp [compactProofParserStep,
              compactProofParserRunningStep]⟩
      | cons task restTasks =>
          have htask := htasks task (by simp)
          have hrest : ∀ oldTask ∈ restTasks,
              CompactProofParserTaskWithin initialTokens oldTask := by
            intro oldTask hold
            exact htasks oldTask (List.mem_cons_of_mem task hold)
          simpa [compactProofParserStep,
            compactProofParserRunningStep] using
            compactProofParserTaskTokenStep_preserves_source
              htask hstream hrest

theorem compactProofParserInitialState_source
    (tokens : List Nat) :
    CompactProofParserStateSourceOf tokens
      (compactProofParserInitialState tokens) := by
  refine ⟨List.suffix_refl tokens, ?_, by simp [
    compactProofParserInitialState]⟩
  intro task htask
  simp only [compactProofParserInitialState, List.mem_cons,
    List.not_mem_nil, or_false] at htask
  subst task
  exact compactProofTask_within tokens

theorem compactProofParser_iterate_preserves_source
    (initialTokens : List Nat) (stepCount : Nat)
    (state : CompactProofParserState)
    (hsource : CompactProofParserStateSourceOf initialTokens state) :
    CompactProofParserStateSourceOf initialTokens
      ((compactProofParserStep^[stepCount]) state) := by
  induction stepCount generalizing state with
  | zero => simpa
  | succ stepCount ih =>
      rw [Function.iterate_succ_apply]
      exact ih _
        (compactProofParserStep_preserves_source
          initialTokens state hsource)

theorem compactProofParserStateAt_source
    (tokens : List Nat) (stepIndex : Nat) :
    CompactProofParserStateSourceOf tokens
      (compactParserStateAt compactProofParserStep
        (compactProofParserInitialState tokens) stepIndex) := by
  unfold compactParserStateAt
  exact compactProofParser_iterate_preserves_source tokens stepIndex _
    (compactProofParserInitialState_source tokens)

theorem compactProofParserLocalTrace_member_source
    {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactProofParserStep fuel
      (compactProofParserInitialState tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    CompactProofParserStateSourceOf tokens state := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical := compactParserLocalTraceValid_stateAt hvalid hle
  unfold compactParserTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = compactParserStateAt compactProofParserStep
      (compactProofParserInitialState tokens) stepIndex :=
    Option.some.inj hcanonical
  rw [heq]
  exact compactProofParserStateAt_source tokens stepIndex

theorem compactProofFormulaTokenStep_task_length_le
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactProofParserTask) :
    (compactProofFormulaTokenStep
      (binderArity, tokens, tasks)).2.1.length <= tasks.length := by
  cases hparser : compactFormulaTokenParser binderArity tokens <;>
    simp [compactProofFormulaTokenStep, hparser,
      compactSyntaxContinue, compactSyntaxFailure]

theorem compactProofTermTokenStep_task_length_le
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactProofParserTask) :
    (compactProofTermTokenStep
      (binderArity, tokens, tasks)).2.1.length <= tasks.length := by
  cases hparser : compactTermTokenParser binderArity tokens <;>
    simp [compactProofTermTokenStep, hparser,
      compactSyntaxContinue, compactSyntaxFailure]

theorem compactProofClosedFormulaTokenStep_task_length_le
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactProofParserTask) :
    (compactProofClosedFormulaTokenStep
      (binderArity, tokens, tasks)).2.1.length <= tasks.length := by
  cases hparser : compactClosedFormulaTokenParser binderArity tokens <;>
    simp [compactProofClosedFormulaTokenStep, hparser,
      compactSyntaxContinue, compactSyntaxFailure]

theorem compactProofRepeatFormulaTokenStep_task_length_le
    (task : CompactProofParserTask) (tokens : List Nat)
    (tasks : List CompactProofParserTask) :
    (compactProofRepeatFormulaTokenStep
      (task, tokens, tasks)).2.1.length <= tasks.length + 2 := by
  by_cases hzero : task.2.2 = 0 <;>
    simp [compactProofRepeatFormulaTokenStep, hzero,
      compactSyntaxContinue]

theorem compactProofSequentTokenStep_task_length_le
    (tokens : List Nat) (tasks : List CompactProofParserTask) :
    (compactProofSequentTokenStep tokens tasks).2.1.length <=
      tasks.length + 1 := by
  cases tokens <;>
    simp [compactProofSequentTokenStep, compactSyntaxContinue,
      compactSyntaxFailure]

theorem compactProofNodeTokenStep_task_length_le
    (tokens : List Nat) (tasks : List CompactProofParserTask) :
    (compactProofNodeTokenStep tokens tasks).2.1.length <=
      tasks.length + 5 := by
  cases tokens with
  | nil => simp [compactProofNodeTokenStep, compactSyntaxFailure]
  | cons tag suffix =>
      by_cases h0 : tag = 0
      · simp [compactProofNodeTokenStep, h0, compactSyntaxContinue]
      by_cases h1 : tag = 1
      · simp [compactProofNodeTokenStep, h0, h1, compactSyntaxContinue]
      by_cases h2 : tag = 2
      · simp [compactProofNodeTokenStep, h0, h1, h2,
          compactSyntaxContinue]
      by_cases h3 : tag = 3
      · simp [compactProofNodeTokenStep, h0, h1, h2, h3,
          compactSyntaxContinue]
      by_cases h4 : tag = 4
      · simp [compactProofNodeTokenStep, h0, h1, h2, h3, h4,
          compactSyntaxContinue]
      by_cases h5 : tag = 5
      · simp [compactProofNodeTokenStep, h0, h1, h2, h3, h4, h5,
          compactSyntaxContinue]
      by_cases h6 : tag = 6
      · simp [compactProofNodeTokenStep, h0, h1, h2, h3, h4, h5, h6,
          compactSyntaxContinue]
      by_cases h7 : tag = 7
      · simp [compactProofNodeTokenStep, h0, h1, h2, h3, h4, h5, h6,
          h7, compactSyntaxContinue]
      by_cases h8 : tag = 8
      · simp [compactProofNodeTokenStep, h0, h1, h2, h3, h4, h5, h6,
          h7, h8, compactSyntaxContinue]
      by_cases h9 : tag = 9
      · simp [compactProofNodeTokenStep, h0, h1, h2, h3, h4, h5, h6,
          h7, h8, h9, compactSyntaxContinue]
      simp [compactProofNodeTokenStep, h0, h1, h2, h3, h4, h5, h6,
        h7, h8, h9, compactSyntaxFailure]

theorem compactProofParserTaskTokenStep_task_length_le
    (task : CompactProofParserTask) (tokens : List Nat)
    (tasks : List CompactProofParserTask) :
    (compactProofParserTaskTokenStep
      (task, tokens, tasks)).2.1.length <= tasks.length + 5 := by
  by_cases hproof : task.1 = 3
  · simpa [compactProofParserTaskTokenStep, hproof] using
      compactProofNodeTokenStep_task_length_le tokens tasks
  by_cases hformula : task.1 = 4
  · have hraw := compactProofFormulaTokenStep_task_length_le
      task.2.1 tokens tasks
    have hweaken :
        (compactProofFormulaTokenStep
          (task.2.1, tokens, tasks)).2.1.length <= tasks.length + 5 := by
      omega
    simpa [compactProofParserTaskTokenStep, hproof, hformula] using hweaken
  by_cases hterm : task.1 = 5
  · have hraw := compactProofTermTokenStep_task_length_le
      task.2.1 tokens tasks
    have hweaken :
        (compactProofTermTokenStep
          (task.2.1, tokens, tasks)).2.1.length <= tasks.length + 5 := by
      omega
    simpa [compactProofParserTaskTokenStep, hproof, hformula, hterm] using
      hweaken
  by_cases hrepeat : task.1 = 6
  · have hraw := compactProofRepeatFormulaTokenStep_task_length_le
      task tokens tasks
    have hweaken :
        (compactProofRepeatFormulaTokenStep
          (task, tokens, tasks)).2.1.length <= tasks.length + 5 := by
      omega
    simpa [compactProofParserTaskTokenStep, hproof, hformula, hterm,
      hrepeat] using hweaken
  by_cases hsequent : task.1 = 7
  · have hraw := compactProofSequentTokenStep_task_length_le tokens tasks
    have hweaken :
        (compactProofSequentTokenStep tokens tasks).2.1.length <=
          tasks.length + 5 := by omega
    simpa [compactProofParserTaskTokenStep, hproof, hformula, hterm,
      hrepeat, hsequent] using hweaken
  by_cases hclosed : task.1 = 8
  · have hraw := compactProofClosedFormulaTokenStep_task_length_le
      task.2.1 tokens tasks
    have hweaken :
        (compactProofClosedFormulaTokenStep
          (task.2.1, tokens, tasks)).2.1.length <= tasks.length + 5 := by
      omega
    simpa [compactProofParserTaskTokenStep, hproof, hformula, hterm,
      hrepeat, hsequent, hclosed] using hweaken
  simp [compactProofParserTaskTokenStep, hproof, hformula, hterm,
    hrepeat, hsequent, hclosed, compactSyntaxFailure]

theorem compactProofParserStep_task_length_le
    (state : CompactProofParserState) :
    (compactProofParserStep state).2.1.length <=
      state.2.1.length + 4 := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | some result => simp [compactProofParserStep]
  | none =>
      cases tasks with
      | nil => simp [compactProofParserStep, compactProofParserRunningStep]
      | cons task restTasks =>
          simpa [compactProofParserStep,
            compactProofParserRunningStep] using
            compactProofParserTaskTokenStep_task_length_le
              task tokens restTasks

theorem compactProofParser_iterate_task_length_le
    (stepCount : Nat) (state : CompactProofParserState) :
    ((compactProofParserStep^[stepCount]) state).2.1.length <=
      state.2.1.length + 4 * stepCount := by
  induction stepCount generalizing state with
  | zero => simp
  | succ stepCount ih =>
      rw [Function.iterate_succ_apply]
      have hstep := compactProofParserStep_task_length_le state
      have htail := ih (compactProofParserStep state)
      omega

theorem compactProofParserStateAt_task_length_le
    (tokens : List Nat) (stepIndex : Nat) :
    (compactParserStateAt compactProofParserStep
      (compactProofParserInitialState tokens) stepIndex).2.1.length <=
      1 + 4 * stepIndex := by
  unfold compactParserStateAt
  have hraw := compactProofParser_iterate_task_length_le stepIndex
    (compactProofParserInitialState tokens)
  simpa [compactProofParserInitialState] using hraw

theorem compactProofParserLocalTrace_member_task_length_le
    {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactProofParserStep fuel
      (compactProofParserInitialState tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    state.2.1.length <= 1 + 4 * fuel := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical := compactParserLocalTraceValid_stateAt hvalid hle
  unfold compactParserTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = compactParserStateAt compactProofParserStep
      (compactProofParserInitialState tokens) stepIndex :=
    Option.some.inj hcanonical
  rw [heq]
  have hraw := compactProofParserStateAt_task_length_le tokens stepIndex
  have hscaled := Nat.mul_le_mul_left 4 hle
  omega

def compactNumericProofParserTaskWeightBound
    (streamWeight : Nat) : Nat :=
  (Nat.size 8 + 1) + (Nat.size 1 + 1) + streamWeight

theorem CompactProofParserTaskWithin.weight_le
    {initialTokens : List Nat} {task : CompactProofParserTask}
    (htask : CompactProofParserTaskWithin initialTokens task) :
    compactAdditiveValueWeight task <=
      compactNumericProofParserTaskWeightBound
        (compactAdditiveValueWeight initialTokens) := by
  unfold CompactProofParserTaskWithin at htask
  have hkind := Nat.size_le_size htask.1
  have hbinder := Nat.size_le_size htask.2.1
  rw [compactAdditiveValueWeight_prod,
    compactAdditiveValueWeight_prod,
    compactAdditiveValueWeight_nat,
    compactAdditiveValueWeight_nat]
  unfold compactNumericProofParserTaskWeightBound
  omega

theorem compactNumericProofParserTaskWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericProofParserTaskWeightBound left <=
      compactNumericProofParserTaskWeightBound right := by
  unfold compactNumericProofParserTaskWeightBound
  omega

theorem CompactProofParserStateSourceOf.status_weight_le
    {initialTokens : List Nat} {state : CompactProofParserState}
    (hsource : CompactProofParserStateSourceOf initialTokens state) :
    compactAdditiveValueWeight state.2.2 <=
      4 + compactAdditiveValueWeight initialTokens := by
  have hstream := compactAdditiveValueWeight_suffix_le hsource.1
  rcases hsource.2.2 with hnone | hstatus
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

def compactNumericProofParserStateWeightBound
    (streamWeight fuel : Nat) : Nat :=
  streamWeight +
    (Nat.size (1 + 4 * fuel) + 1 +
      (1 + 4 * fuel) *
        compactNumericProofParserTaskWeightBound streamWeight) +
    (4 + streamWeight)

theorem compactNumericProofParserStateWeightBound_mono
    {streamLeft streamRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft <= streamRight)
    (hfuel : fuelLeft <= fuelRight) :
    compactNumericProofParserStateWeightBound streamLeft fuelLeft <=
      compactNumericProofParserStateWeightBound streamRight fuelRight := by
  have hfuelScaled : 1 + 4 * fuelLeft <= 1 + 4 * fuelRight := by
    omega
  have hfuelSize := Nat.size_le_size hfuelScaled
  have htask := compactNumericProofParserTaskWeightBound_mono hstream
  have htaskList := Nat.mul_le_mul hfuelScaled htask
  unfold compactNumericProofParserStateWeightBound
  omega

theorem compactProofParserLocalTrace_member_state_weight_le
    {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactProofParserStep fuel
      (compactProofParserInitialState tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    compactAdditiveValueWeight state <=
      compactNumericProofParserStateWeightBound
        (compactAdditiveValueWeight tokens) fuel := by
  have hsource := compactProofParserLocalTrace_member_source hvalid hstate
  have hstream := compactAdditiveValueWeight_suffix_le hsource.1
  have htaskLength :=
    compactProofParserLocalTrace_member_task_length_le hvalid hstate
  have htasksRaw := compactAdditiveValueWeight_list_le state.2.1
    (compactNumericProofParserTaskWeightBound
      (compactAdditiveValueWeight tokens))
    (fun task htask => (hsource.2.1 task htask).weight_le)
  have htaskSize := Nat.size_le_size htaskLength
  have htaskProduct := Nat.mul_le_mul_right
    (compactNumericProofParserTaskWeightBound
      (compactAdditiveValueWeight tokens)) htaskLength
  have htasks : compactAdditiveValueWeight state.2.1 <=
      Nat.size (1 + 4 * fuel) + 1 +
        (1 + 4 * fuel) *
          compactNumericProofParserTaskWeightBound
            (compactAdditiveValueWeight tokens) := by
    omega
  have hstatus := hsource.status_weight_le
  rw [compactAdditiveValueWeight_prod,
    compactAdditiveValueWeight_prod]
  unfold compactNumericProofParserStateWeightBound
  omega

def compactNumericProofParserTraceWeightBound
    (streamWeight fuel : Nat) : Nat :=
  Nat.size (fuel + 1) + 1 +
    (fuel + 1) *
      compactNumericProofParserStateWeightBound streamWeight fuel

theorem compactNumericProofParserTraceWeightBound_mono
    {streamLeft streamRight fuelLeft fuelRight : Nat}
    (hstream : streamLeft <= streamRight)
    (hfuel : fuelLeft <= fuelRight) :
    compactNumericProofParserTraceWeightBound streamLeft fuelLeft <=
      compactNumericProofParserTraceWeightBound streamRight fuelRight := by
  have hfuelAdd : fuelLeft + 1 <= fuelRight + 1 := by omega
  have hfuelSize := Nat.size_le_size hfuelAdd
  have hstate := compactNumericProofParserStateWeightBound_mono
    hstream hfuel
  have htable := Nat.mul_le_mul hfuelAdd hstate
  unfold compactNumericProofParserTraceWeightBound
  omega

theorem compactProofTokenParserDirectTraceValid_weight_le
    {tokens suffix : List Nat}
    {states : CompactProofTokenParserDirectTrace}
    (hvalid : CompactProofTokenParserDirectTraceValid
      tokens suffix states) :
    compactAdditiveValueWeight states <=
      compactNumericProofParserTraceWeightBound
        (compactAdditiveValueWeight tokens)
        (compactProofParserFuelBound tokens) := by
  have hlocal := hvalid.1
  have hrows := compactAdditiveValueWeight_list_le states
    (compactNumericProofParserStateWeightBound
      (compactAdditiveValueWeight tokens)
      (compactProofParserFuelBound tokens))
    (fun state hstate =>
      compactProofParserLocalTrace_member_state_weight_le hlocal hstate)
  unfold compactNumericProofParserTraceWeightBound
  rw [hlocal.1] at hrows
  exact hrows

def compactNumericProofParserFuelWeightBound
    (streamWeight : Nat) : Nat :=
  32 * (streamWeight + 1) * (streamWeight + 1) + 16

theorem compactProofParserFuelBound_le_weightBound
    {tokens : List Nat} {streamWeight : Nat}
    (hweight : compactAdditiveValueWeight tokens <= streamWeight) :
    compactProofParserFuelBound tokens <=
      compactNumericProofParserFuelWeightBound streamWeight := by
  have hlength := compactAdditiveValueWeight_natList_length_le tokens
  have hlengthWeight : tokens.length + 1 <= streamWeight + 1 := by omega
  have hscaled := Nat.mul_le_mul_left 32 hlengthWeight
  have hquadratic := Nat.mul_le_mul hscaled hlengthWeight
  unfold compactProofParserFuelBound
    compactNumericProofParserFuelWeightBound
  omega

def compactNumericProofParserPublicTraceWeightBound
    (bitLength : Nat) : Nat :=
  let streamWeight := compactNumericDecodedTokenListWeightBound bitLength
  compactNumericProofParserTraceWeightBound streamWeight
    (compactNumericProofParserFuelWeightBound streamWeight)

theorem compactNumericListedDirectTrace_proofParserTrace_weight_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight
        (compactNumericDirectTraceProofParserTrace trace) <=
      compactNumericProofParserPublicTraceWeightBound
        (Nat.size code) := by
  have hfull := hvalid
  unfold CompactNumericListedDirectTraceValid at hfull
  have hparser : CompactProofTokenParserDirectTraceValid
      (compactNumericDirectTraceCertifiedTokens trace)
      (compactNumericDirectTraceParts trace).2.1
      (compactNumericDirectTraceProofParserTrace trace) :=
    hfull.2.2.1
  have hraw := compactProofTokenParserDirectTraceValid_weight_le hparser
  have htokens :=
    compactNumericListedDirectTrace_certifiedTokens_weight_le hvalid
  have hfuel := compactProofParserFuelBound_le_weightBound htokens
  unfold compactNumericProofParserPublicTraceWeightBound
  exact hraw.trans
    (compactNumericProofParserTraceWeightBound_mono htokens hfuel)

/-! ## Root-field nested direct trace -/

theorem compactTermParserInitialState_source
    (binderArity : Nat) (tokens : List Nat) :
    CompactSyntaxParserStateSourceOf tokens binderArity
      (compactTermParserInitialState binderArity tokens) := by
  refine ⟨List.suffix_refl tokens, ?_, by simp [
    compactTermParserInitialState]⟩
  intro task htask
  simp only [compactTermParserInitialState, List.mem_cons,
    List.not_mem_nil, or_false] at htask
  subst task
  exact compactTermTask_within (by rfl)

theorem compactTermParserStateAt_source
    (binderArity : Nat) (tokens : List Nat) (stepIndex : Nat) :
    CompactSyntaxParserStateSourceOf tokens (binderArity + stepIndex)
      (compactParserStateAt compactSyntaxParserStep
        (compactTermParserInitialState binderArity tokens)
        stepIndex) := by
  unfold compactParserStateAt
  exact compactSyntaxParser_iterate_preserves_source tokens binderArity
    stepIndex _ (compactTermParserInitialState_source binderArity tokens)

theorem compactTermParserStateAt_task_length_le
    (binderArity : Nat) (tokens : List Nat) (stepIndex : Nat) :
    (compactParserStateAt compactSyntaxParserStep
      (compactTermParserInitialState binderArity tokens)
      stepIndex).2.1.length <= 1 + stepIndex := by
  unfold compactParserStateAt
  have hraw := compactSyntaxParser_iterate_task_length_le stepIndex
    (compactTermParserInitialState binderArity tokens)
  simpa [compactTermParserInitialState] using hraw

theorem compactTermParserLocalTrace_member_source
    {binderArity : Nat} {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactSyntaxParserStep fuel
      (compactTermParserInitialState binderArity tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    CompactSyntaxParserStateSourceOf tokens (binderArity + fuel) state := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical := compactParserLocalTraceValid_stateAt hvalid hle
  unfold compactParserTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = compactParserStateAt compactSyntaxParserStep
      (compactTermParserInitialState binderArity tokens) stepIndex :=
    Option.some.inj hcanonical
  rw [heq]
  exact CompactSyntaxParserStateSourceOf.mono
    (compactTermParserStateAt_source binderArity tokens stepIndex)
    (by omega)

theorem compactTermParserLocalTrace_member_task_length_le
    {binderArity : Nat} {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactSyntaxParserStep fuel
      (compactTermParserInitialState binderArity tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    state.2.1.length <= 1 + fuel := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical := compactParserLocalTraceValid_stateAt hvalid hle
  unfold compactParserTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = compactParserStateAt compactSyntaxParserStep
      (compactTermParserInitialState binderArity tokens) stepIndex :=
    Option.some.inj hcanonical
  rw [heq]
  have hraw := compactTermParserStateAt_task_length_le
    binderArity tokens stepIndex
  omega

theorem compactTermParserLocalTrace_member_state_weight_le
    {binderArity : Nat} {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactSyntaxParserStep fuel
      (compactTermParserInitialState binderArity tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    compactAdditiveValueWeight state <=
      compactNumericFormulaParserStateWeightBound
        (compactAdditiveValueWeight tokens) (binderArity + fuel) fuel := by
  have hsource := compactTermParserLocalTrace_member_source hvalid hstate
  have hstream := compactAdditiveValueWeight_suffix_le hsource.1
  have htaskLength :=
    compactTermParserLocalTrace_member_task_length_le hvalid hstate
  have htasksRaw := compactAdditiveValueWeight_list_le state.2.1
    (compactNumericSyntaxParserTaskWeightBound
      (compactAdditiveValueWeight tokens) (binderArity + fuel))
    (fun task htask => (hsource.2.1 task htask).weight_le)
  have htaskSize := Nat.size_le_size htaskLength
  have htaskProduct := Nat.mul_le_mul_right
    (compactNumericSyntaxParserTaskWeightBound
      (compactAdditiveValueWeight tokens) (binderArity + fuel))
    htaskLength
  have htasks : compactAdditiveValueWeight state.2.1 <=
      Nat.size (1 + fuel) + 1 + (1 + fuel) *
        compactNumericSyntaxParserTaskWeightBound
          (compactAdditiveValueWeight tokens) (binderArity + fuel) := by
    omega
  have hstatus := hsource.status_weight_le
  rw [compactAdditiveValueWeight_prod,
    compactAdditiveValueWeight_prod]
  unfold compactNumericFormulaParserStateWeightBound
  omega

theorem compactTermTokenParserDirectTraceValid_weight_le
    {binderArity : Nat} {tokens suffix : List Nat}
    {states : CompactTermTokenParserDirectTrace}
    (hvalid : CompactTermTokenParserDirectTraceValid
      binderArity tokens suffix states) :
    compactAdditiveValueWeight states <=
      compactNumericFormulaParserTraceWeightBound
        (compactAdditiveValueWeight tokens) binderArity
        (compactSyntaxRunFuelBound tokens) := by
  have hlocal := hvalid.1
  have hrows := compactAdditiveValueWeight_list_le states
    (compactNumericFormulaParserStateWeightBound
      (compactAdditiveValueWeight tokens)
      (binderArity + compactSyntaxRunFuelBound tokens)
      (compactSyntaxRunFuelBound tokens))
    (fun state hstate =>
      compactTermParserLocalTrace_member_state_weight_le hlocal hstate)
  unfold compactNumericFormulaParserTraceWeightBound
  rw [hlocal.1] at hrows
  exact hrows

theorem compactClosedTermTokenStep_preserves_source
    {initialTokens tokens : List Nat} {binderArity binderCap : Nat}
    {tasks : List CompactSyntaxTask}
    (hbinder : binderArity <= binderCap)
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ task ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens binderCap task) :
    CompactSyntaxParserStateSourceOf initialTokens (binderCap + 1)
      (compactClosedTermTokenStep (binderArity, tokens, tasks)) := by
  have hbinderNext : binderArity <= binderCap + 1 := by omega
  have htasksNext : ∀ task ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens (binderCap + 1) task := by
    intro task htask
    exact (htasks task htask).mono (by omega)
  have hdropTwo : tokens.drop 2 <:+ initialTokens :=
    (List.drop_suffix 2 tokens).trans hstream
  have hdropThree : tokens.drop 3 <:+ initialTokens :=
    (List.drop_suffix 3 tokens).trans hstream
  have hargument := compactTokenAt_weight_le_of_suffix hstream 1
  by_cases hlengthTwo : 2 <= tokens.length
  · by_cases htagZero : compactTokenAt 0 tokens = 0
    · by_cases hbound : compactTokenAt 1 tokens < binderArity
      · simpa [compactClosedTermTokenStep, hlengthTwo, htagZero, hbound]
          using compactSyntaxParserStateSource_continue
            hdropTwo htasksNext
      · simpa [compactClosedTermTokenStep, hlengthTwo, htagZero, hbound]
          using compactSyntaxParserStateSource_failure hstream htasksNext
    · by_cases htagOne : compactTokenAt 0 tokens = 1
      · simpa [compactClosedTermTokenStep, hlengthTwo, htagZero, htagOne]
          using compactSyntaxParserStateSource_failure hstream htasksNext
      · by_cases htagTwo : compactTokenAt 0 tokens = 2
        · by_cases hlengthThree : 3 <= tokens.length
          · by_cases hvalid : ArithmeticFuncCodeValid
                (compactTokenAt 1 tokens) (compactTokenAt 2 tokens)
            · have hrepeat := compactRepeatTermTask_within
                (initialTokens := initialTokens)
                (binderCap := binderCap + 1)
                hbinderNext hargument
              simpa [compactClosedTermTokenStep, hlengthTwo, htagZero,
                htagOne, htagTwo, hlengthThree, hvalid] using
                compactSyntaxParserStateSource_continue_push
                  hdropThree hrepeat htasksNext
            · simpa [compactClosedTermTokenStep, hlengthTwo, htagZero,
                htagOne, htagTwo, hlengthThree, hvalid] using
                compactSyntaxParserStateSource_failure hstream htasksNext
          · simpa [compactClosedTermTokenStep, hlengthTwo, htagZero,
              htagOne, htagTwo, hlengthThree] using
              compactSyntaxParserStateSource_failure hstream htasksNext
        · simpa [compactClosedTermTokenStep, hlengthTwo, htagZero,
            htagOne, htagTwo] using
            compactSyntaxParserStateSource_failure hstream htasksNext
  · simpa [compactClosedTermTokenStep, hlengthTwo] using
      compactSyntaxParserStateSource_failure hstream htasksNext

theorem compactClosedSyntaxTaskTokenStep_preserves_source
    {initialTokens tokens : List Nat} {binderCap : Nat}
    {task : CompactSyntaxTask} {tasks : List CompactSyntaxTask}
    (htask : CompactSyntaxParserTaskWithin initialTokens binderCap task)
    (hstream : tokens <:+ initialTokens)
    (htasks : ∀ oldTask ∈ tasks,
      CompactSyntaxParserTaskWithin initialTokens binderCap oldTask) :
    CompactSyntaxParserStateSourceOf initialTokens (binderCap + 1)
      (compactClosedSyntaxTaskTokenStep (task, tokens, tasks)) := by
  unfold CompactSyntaxParserTaskWithin at htask
  by_cases hterm : task.1 = 0
  · simpa [compactClosedSyntaxTaskTokenStep, hterm] using
      compactClosedTermTokenStep_preserves_source
        htask.2.1 hstream htasks
  by_cases hformula : task.1 = 1
  · simpa [compactClosedSyntaxTaskTokenStep, hterm, hformula] using
      compactFormulaTokenStep_preserves_source htask.2.1 hstream htasks
  by_cases hrepeat : task.1 = 2
  · simpa [compactClosedSyntaxTaskTokenStep, hterm, hformula, hrepeat] using
      compactRepeatTermTokenStep_preserves_source htask hstream htasks
  exfalso
  omega

theorem compactClosedSyntaxParserStep_preserves_source
    (initialTokens : List Nat) (binderCap : Nat)
    (state : CompactSyntaxParserState)
    (hsource : CompactSyntaxParserStateSourceOf
      initialTokens binderCap state) :
    CompactSyntaxParserStateSourceOf initialTokens (binderCap + 1)
      (compactClosedSyntaxParserStep state) := by
  rcases state with ⟨tokens, tasks, status⟩
  rcases hsource with ⟨hstream, htasks, hstatus⟩
  cases status with
  | some result =>
      simpa [compactClosedSyntaxParserStep] using
        (show CompactSyntaxParserStateSourceOf
          initialTokens (binderCap + 1) (tokens, tasks, some result) from
          CompactSyntaxParserStateSourceOf.mono
            (⟨hstream, htasks, hstatus⟩ :
              CompactSyntaxParserStateSourceOf
                initialTokens binderCap (tokens, tasks, some result))
            (by omega))
  | none =>
      cases tasks with
      | nil =>
          exact ⟨hstream,
            by simp [compactClosedSyntaxParserStep,
              compactClosedSyntaxRunningStep],
            by simp [compactClosedSyntaxParserStep,
              compactClosedSyntaxRunningStep]⟩
      | cons task restTasks =>
          have htask := htasks task (by simp)
          have hrest : ∀ oldTask ∈ restTasks,
              CompactSyntaxParserTaskWithin
                initialTokens binderCap oldTask := by
            intro oldTask hold
            exact htasks oldTask (List.mem_cons_of_mem task hold)
          simpa [compactClosedSyntaxParserStep,
            compactClosedSyntaxRunningStep] using
            compactClosedSyntaxTaskTokenStep_preserves_source
              htask hstream hrest

theorem compactClosedSyntaxParser_iterate_preserves_source
    (initialTokens : List Nat) (binderCap stepCount : Nat)
    (state : CompactSyntaxParserState)
    (hsource : CompactSyntaxParserStateSourceOf
      initialTokens binderCap state) :
    CompactSyntaxParserStateSourceOf initialTokens
      (binderCap + stepCount)
      ((compactClosedSyntaxParserStep^[stepCount]) state) := by
  induction stepCount generalizing binderCap state with
  | zero => simpa
  | succ stepCount ih =>
      rw [Function.iterate_succ_apply]
      have hstep := compactClosedSyntaxParserStep_preserves_source
        initialTokens binderCap state hsource
      have htail := ih (binderCap + 1) _ hstep
      convert htail using 1 <;> omega

theorem compactClosedFormulaParserStateAt_source
    (binderArity : Nat) (tokens : List Nat) (stepIndex : Nat) :
    CompactSyntaxParserStateSourceOf tokens (binderArity + stepIndex)
      (compactParserStateAt compactClosedSyntaxParserStep
        (compactFormulaParserInitialState binderArity tokens)
        stepIndex) := by
  unfold compactParserStateAt
  exact compactClosedSyntaxParser_iterate_preserves_source
    tokens binderArity stepIndex _
      (compactFormulaParserInitialState_source binderArity tokens)

theorem compactClosedTermTokenStep_task_length_le
    (binderArity : Nat) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    (compactClosedTermTokenStep
      (binderArity, tokens, tasks)).2.1.length <= tasks.length + 1 := by
  by_cases hlengthTwo : 2 <= tokens.length
  · by_cases htagZero : compactTokenAt 0 tokens = 0
    · by_cases hbound : compactTokenAt 1 tokens < binderArity <;>
        simp [compactClosedTermTokenStep, hlengthTwo, htagZero, hbound,
          compactSyntaxContinue, compactSyntaxFailure]
    · by_cases htagOne : compactTokenAt 0 tokens = 1
      · simp [compactClosedTermTokenStep, hlengthTwo, htagZero, htagOne,
          compactSyntaxFailure]
      · by_cases htagTwo : compactTokenAt 0 tokens = 2
        · by_cases hlengthThree : 3 <= tokens.length
          · by_cases hvalid : ArithmeticFuncCodeValid
                (compactTokenAt 1 tokens) (compactTokenAt 2 tokens) <;>
              simp [compactClosedTermTokenStep, hlengthTwo, htagZero,
                htagOne, htagTwo, hlengthThree, hvalid,
                compactSyntaxContinue, compactSyntaxFailure]
          · simp [compactClosedTermTokenStep, hlengthTwo, htagZero,
              htagOne, htagTwo, hlengthThree, compactSyntaxFailure]
        · simp [compactClosedTermTokenStep, hlengthTwo, htagZero,
            htagOne, htagTwo, compactSyntaxFailure]
  · simp [compactClosedTermTokenStep, hlengthTwo, compactSyntaxFailure]

theorem compactClosedSyntaxTaskTokenStep_task_length_le
    (task : CompactSyntaxTask) (tokens : List Nat)
    (tasks : List CompactSyntaxTask) :
    (compactClosedSyntaxTaskTokenStep
      (task, tokens, tasks)).2.1.length <= tasks.length + 2 := by
  by_cases hterm : task.1 = 0
  · have hraw := compactClosedTermTokenStep_task_length_le
      task.2.1 tokens tasks
    have hweaken :
        (compactClosedTermTokenStep
          (task.2.1, tokens, tasks)).2.1.length <= tasks.length + 2 := by
      omega
    simpa [compactClosedSyntaxTaskTokenStep, hterm] using hweaken
  by_cases hformula : task.1 = 1
  · simpa [compactClosedSyntaxTaskTokenStep, hterm, hformula] using
      compactFormulaTokenStep_task_length_le task.2.1 tokens tasks
  by_cases hrepeat : task.1 = 2
  · simpa [compactClosedSyntaxTaskTokenStep, hterm, hformula, hrepeat] using
      compactRepeatTermTokenStep_task_length_le task tokens tasks
  simp [compactClosedSyntaxTaskTokenStep, hterm, hformula, hrepeat,
    compactSyntaxFailure]

theorem compactClosedSyntaxParserStep_task_length_le
    (state : CompactSyntaxParserState) :
    (compactClosedSyntaxParserStep state).2.1.length <=
      state.2.1.length + 1 := by
  rcases state with ⟨tokens, tasks, status⟩
  cases status with
  | some result => simp [compactClosedSyntaxParserStep]
  | none =>
      cases tasks with
      | nil =>
          simp [compactClosedSyntaxParserStep,
            compactClosedSyntaxRunningStep]
      | cons task restTasks =>
          simpa [compactClosedSyntaxParserStep,
            compactClosedSyntaxRunningStep] using
            compactClosedSyntaxTaskTokenStep_task_length_le
              task tokens restTasks

theorem compactClosedSyntaxParser_iterate_task_length_le
    (stepCount : Nat) (state : CompactSyntaxParserState) :
    ((compactClosedSyntaxParserStep^[stepCount]) state).2.1.length <=
      state.2.1.length + stepCount := by
  induction stepCount generalizing state with
  | zero => simp
  | succ stepCount ih =>
      rw [Function.iterate_succ_apply]
      have hstep := compactClosedSyntaxParserStep_task_length_le state
      have htail := ih (compactClosedSyntaxParserStep state)
      omega

theorem compactClosedFormulaParserStateAt_task_length_le
    (binderArity : Nat) (tokens : List Nat) (stepIndex : Nat) :
    (compactParserStateAt compactClosedSyntaxParserStep
      (compactFormulaParserInitialState binderArity tokens)
      stepIndex).2.1.length <= 1 + stepIndex := by
  unfold compactParserStateAt
  have hraw := compactClosedSyntaxParser_iterate_task_length_le stepIndex
    (compactFormulaParserInitialState binderArity tokens)
  simpa [compactFormulaParserInitialState] using hraw

theorem compactClosedFormulaParserLocalTrace_member_source
    {binderArity : Nat} {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactClosedSyntaxParserStep fuel
      (compactFormulaParserInitialState binderArity tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    CompactSyntaxParserStateSourceOf tokens (binderArity + fuel) state := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical := compactParserLocalTraceValid_stateAt hvalid hle
  unfold compactParserTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = compactParserStateAt compactClosedSyntaxParserStep
      (compactFormulaParserInitialState binderArity tokens) stepIndex :=
    Option.some.inj hcanonical
  rw [heq]
  exact CompactSyntaxParserStateSourceOf.mono
    (compactClosedFormulaParserStateAt_source
      binderArity tokens stepIndex) (by omega)

theorem compactClosedFormulaParserLocalTrace_member_task_length_le
    {binderArity : Nat} {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactClosedSyntaxParserStep fuel
      (compactFormulaParserInitialState binderArity tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    state.2.1.length <= 1 + fuel := by
  obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
  obtain ⟨hstepIndex, _hget⟩ :=
    List.getElem?_eq_some_iff.mp hstateAt
  have hle : stepIndex <= fuel := by
    rw [hvalid.1] at hstepIndex
    omega
  have hcanonical := compactParserLocalTraceValid_stateAt hvalid hle
  unfold compactParserTraceState? at hcanonical
  rw [hstateAt] at hcanonical
  have heq : state = compactParserStateAt compactClosedSyntaxParserStep
      (compactFormulaParserInitialState binderArity tokens) stepIndex :=
    Option.some.inj hcanonical
  rw [heq]
  have hraw := compactClosedFormulaParserStateAt_task_length_le
    binderArity tokens stepIndex
  omega

theorem compactClosedFormulaParserLocalTrace_member_state_weight_le
    {binderArity : Nat} {tokens : List Nat} {fuel : Nat}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid compactClosedSyntaxParserStep fuel
      (compactFormulaParserInitialState binderArity tokens) states)
    {state : CompactUnifiedParserState} (hstate : state ∈ states) :
    compactAdditiveValueWeight state <=
      compactNumericFormulaParserStateWeightBound
        (compactAdditiveValueWeight tokens) (binderArity + fuel) fuel := by
  have hsource :=
    compactClosedFormulaParserLocalTrace_member_source hvalid hstate
  have hstream := compactAdditiveValueWeight_suffix_le hsource.1
  have htaskLength :=
    compactClosedFormulaParserLocalTrace_member_task_length_le hvalid hstate
  have htasksRaw := compactAdditiveValueWeight_list_le state.2.1
    (compactNumericSyntaxParserTaskWeightBound
      (compactAdditiveValueWeight tokens) (binderArity + fuel))
    (fun task htask => (hsource.2.1 task htask).weight_le)
  have htaskSize := Nat.size_le_size htaskLength
  have htaskProduct := Nat.mul_le_mul_right
    (compactNumericSyntaxParserTaskWeightBound
      (compactAdditiveValueWeight tokens) (binderArity + fuel))
    htaskLength
  have htasks : compactAdditiveValueWeight state.2.1 <=
      Nat.size (1 + fuel) + 1 + (1 + fuel) *
        compactNumericSyntaxParserTaskWeightBound
          (compactAdditiveValueWeight tokens) (binderArity + fuel) := by
    omega
  have hstatus := hsource.status_weight_le
  rw [compactAdditiveValueWeight_prod,
    compactAdditiveValueWeight_prod]
  unfold compactNumericFormulaParserStateWeightBound
  omega

theorem compactClosedFormulaTokenParserDirectTraceValid_weight_le
    {binderArity : Nat} {tokens suffix : List Nat}
    {states : CompactClosedFormulaTokenParserDirectTrace}
    (hvalid : CompactClosedFormulaTokenParserDirectTraceValid
      binderArity tokens suffix states) :
    compactAdditiveValueWeight states <=
      compactNumericFormulaParserTraceWeightBound
        (compactAdditiveValueWeight tokens) binderArity
        (compactSyntaxRunFuelBound tokens) := by
  have hlocal := hvalid.1
  have hrows := compactAdditiveValueWeight_list_le states
    (compactNumericFormulaParserStateWeightBound
      (compactAdditiveValueWeight tokens)
      (binderArity + compactSyntaxRunFuelBound tokens)
      (compactSyntaxRunFuelBound tokens))
    (fun state hstate =>
      compactClosedFormulaParserLocalTrace_member_state_weight_le
        hlocal hstate)
  unfold compactNumericFormulaParserTraceWeightBound
  rw [hlocal.1] at hrows
  exact hrows

def compactNumericRootSyntaxParserTraceWeightBound
    (streamWeight : Nat) : Nat :=
  compactNumericFormulaParserTraceWeightBound streamWeight 1
    (compactNumericCertificateParserFuelWeightBound streamWeight)

theorem compactFormulaTokenParserDirectTraceValid_weight_le_rootBound
    {binderArity : Nat} {tokens suffix : List Nat}
    {states : CompactFormulaTokenParserDirectTrace}
    (hvalid : CompactFormulaTokenParserDirectTraceValid
      binderArity tokens suffix states)
    {streamWeight : Nat}
    (hstream : compactAdditiveValueWeight tokens <= streamWeight)
    (hbinder : binderArity <= 1) :
    compactAdditiveValueWeight states <=
      compactNumericRootSyntaxParserTraceWeightBound streamWeight := by
  have hraw := compactFormulaTokenParserDirectTraceValid_weight_le hvalid
  have hfuel := compactSyntaxRunFuelBound_le_weightBound hstream
  unfold compactNumericRootSyntaxParserTraceWeightBound
  exact hraw.trans
    (compactNumericFormulaParserTraceWeightBound_mono
      hstream hbinder hfuel)

theorem compactTermTokenParserDirectTraceValid_weight_le_rootBound
    {binderArity : Nat} {tokens suffix : List Nat}
    {states : CompactTermTokenParserDirectTrace}
    (hvalid : CompactTermTokenParserDirectTraceValid
      binderArity tokens suffix states)
    {streamWeight : Nat}
    (hstream : compactAdditiveValueWeight tokens <= streamWeight)
    (hbinder : binderArity <= 1) :
    compactAdditiveValueWeight states <=
      compactNumericRootSyntaxParserTraceWeightBound streamWeight := by
  have hraw := compactTermTokenParserDirectTraceValid_weight_le hvalid
  have hfuel := compactSyntaxRunFuelBound_le_weightBound hstream
  unfold compactNumericRootSyntaxParserTraceWeightBound
  exact hraw.trans
    (compactNumericFormulaParserTraceWeightBound_mono
      hstream hbinder hfuel)

theorem compactClosedFormulaTokenParserDirectTraceValid_weight_le_rootBound
    {binderArity : Nat} {tokens suffix : List Nat}
    {states : CompactClosedFormulaTokenParserDirectTrace}
    (hvalid : CompactClosedFormulaTokenParserDirectTraceValid
      binderArity tokens suffix states)
    {streamWeight : Nat}
    (hstream : compactAdditiveValueWeight tokens <= streamWeight)
    (hbinder : binderArity <= 1) :
    compactAdditiveValueWeight states <=
      compactNumericRootSyntaxParserTraceWeightBound streamWeight := by
  have hraw :=
    compactClosedFormulaTokenParserDirectTraceValid_weight_le hvalid
  have hfuel := compactSyntaxRunFuelBound_le_weightBound hstream
  unfold compactNumericRootSyntaxParserTraceWeightBound
  exact hraw.trans
    (compactNumericFormulaParserTraceWeightBound_mono
      hstream hbinder hfuel)

theorem compactAdditiveValueWeight_nil_le_rootSyntaxParserTraceWeightBound
    (streamWeight : Nat) :
    compactAdditiveValueWeight ([] : List CompactUnifiedParserState) <=
      compactNumericRootSyntaxParserTraceWeightBound streamWeight := by
  unfold compactNumericRootSyntaxParserTraceWeightBound
    compactNumericFormulaParserTraceWeightBound
    compactNumericFormulaParserStateWeightBound
    compactNumericSyntaxParserTaskWeightBound
    compactNumericCertificateParserFuelWeightBound
  simp only [compactAdditiveValueWeight_list, List.length_nil,
    List.map_nil, List.sum_nil, Nat.size_zero, zero_add, zero_mul]
  omega

theorem compactFormulaTokenValuesRepeat_components_weight_le
    {count : Nat} {tokens suffix : List Nat}
    {values : List (List Nat)}
    (hrun : compactFormulaTokenValuesRepeat count tokens =
      some (values, suffix)) :
    compactAdditiveValueWeight values <=
        compactNumericNestedListWeightBound
          (compactAdditiveValueWeight tokens) ∧
      compactAdditiveValueWeight suffix <=
        compactAdditiveValueWeight tokens ∧
      count <= compactAdditiveValueWeight tokens := by
  obtain ⟨Gamma, hlength, htokens, hvalues⟩ :=
    compactFormulaTokenValuesRepeat_sound hrun
  let W := compactAdditiveValueWeight tokens
  have hitem : ∀ value ∈ values,
      compactAdditiveValueWeight value <= W := by
    intro value hvalue
    rw [hvalues] at hvalue
    obtain ⟨formula, hformula, rfl⟩ := List.mem_map.mp hvalue
    have hformulaInfix : compactArithmeticFormulaTokens formula <:+:
        Gamma.flatMap compactArithmeticFormulaTokens := by
      simpa [List.flatMap] using
        (List.infix_of_mem_flatten
          (List.mem_map_of_mem
            (f := compactArithmeticFormulaTokens) hformula))
    have hflatMapInfix :
        Gamma.flatMap compactArithmeticFormulaTokens <:+: tokens := by
      rw [htokens]
      exact (List.prefix_append _ _).isInfix
    simpa [W] using compactAdditiveValueWeight_infix_le
      (hformulaInfix.trans hflatMapInfix)
  have hGammaLength : Gamma.length <= tokens.length := by
    have hformulaLength := formulaList_length_le_flatMap_tokenLength Gamma
    rw [htokens]
    simp only [List.length_append]
    omega
  have htokenLength := compactAdditiveValueWeight_natList_length_le tokens
  have hvalueLength : values.length <= W := by
    rw [hvalues]
    simp only [List.length_map]
    exact hGammaLength.trans htokenLength
  have hraw := compactAdditiveValueWeight_list_le values W hitem
  have hsize := Nat.size_le_size hvalueLength
  have hmul := Nat.mul_le_mul_right W hvalueLength
  have hvaluesWeight : compactAdditiveValueWeight values <=
      compactNumericNestedListWeightBound W := by
    unfold compactNumericNestedListWeightBound
    omega
  have hsuffix : suffix <:+ tokens :=
    ⟨Gamma.flatMap compactArithmeticFormulaTokens, htokens.symm⟩
  have hsuffixWeight := compactAdditiveValueWeight_suffix_le hsuffix
  have hcount : count <= W := by
    rw [← hlength]
    exact hGammaLength.trans htokenLength
  exact ⟨hvaluesWeight, hsuffixWeight, hcount⟩

theorem compactFormulaValuesStateAt_components_weight_le
    {tokens : List Nat} {stepIndex : Nat}
    {values : List (List Nat)} {suffix : List Nat}
    (hstate : compactFormulaValuesStateAt
      (compactFormulaTokenValuesInitial tokens) stepIndex =
        some (values, suffix)) :
    compactAdditiveValueWeight values <=
        compactNumericNestedListWeightBound
          (compactAdditiveValueWeight tokens) ∧
      compactAdditiveValueWeight suffix <=
        compactAdditiveValueWeight tokens := by
  have hrun : compactFormulaTokenValuesRepeat stepIndex tokens =
      some (values, suffix) := by
    simpa [compactFormulaTokenValuesRepeat,
      compactFormulaTokenValuesInitial,
      compactFormulaValuesStateAt] using hstate
  have hcomponents :=
    compactFormulaTokenValuesRepeat_components_weight_le hrun
  exact ⟨hcomponents.1, hcomponents.2.1⟩

theorem compactSequentTokenValueDirectTraceValid_repeat_result
    {count : Nat} {tail : List Nat}
    {values : List (List Nat)} {suffix : List Nat}
    {trace : CompactSequentTokenValueDirectTrace}
    (hvalid : CompactSequentTokenValueDirectTraceValid
      (count :: tail) values suffix trace) :
    compactFormulaTokenValuesRepeat count tail =
      some (values, suffix) := by
  have hparser : compactSequentTokenValueParser (count :: tail) =
      some (values, suffix) :=
    (compactSequentTokenValueParser_eq_some_iff_exists_directTrace
      (count :: tail) values suffix).mpr ⟨trace, hvalid⟩
  simpa [compactSequentTokenValueParser] using hparser

def compactNumericSequentStateWeightBound (streamWeight : Nat) : Nat :=
  2 + compactNumericNestedListWeightBound streamWeight + streamWeight

theorem compactSequentTokenValueDirectTraceValid_member_state_weight_le
    {tokens : List Nat} {values : List (List Nat)} {suffix : List Nat}
    {trace : CompactSequentTokenValueDirectTrace}
    (hvalid : CompactSequentTokenValueDirectTraceValid
      tokens values suffix trace)
    {state : CompactFormulaTokenValuesResult} (hstate : state ∈ trace.1) :
    compactAdditiveValueWeight state <=
      compactNumericSequentStateWeightBound
        (compactAdditiveValueWeight tokens) := by
  cases tokens with
  | nil => simp [CompactSequentTokenValueDirectTraceValid] at hvalid
  | cons count tail =>
      unfold CompactSequentTokenValueDirectTraceValid at hvalid
      have hnested := hvalid.1
      have hlocal :=
        compactFormulaValuesNestedLocalTraceValid_implies_local hnested
      have hrun :=
        compactSequentTokenValueDirectTraceValid_repeat_result hvalid
      have hfinalAt : compactFormulaValuesStateAt
          (compactFormulaTokenValuesInitial tail) count =
            some (values, suffix) := by
        simpa [compactFormulaTokenValuesRepeat,
          compactFormulaTokenValuesInitial,
          compactFormulaValuesStateAt] using hrun
      obtain ⟨stepIndex, hstateAt⟩ := List.mem_iff_getElem?.mp hstate
      obtain ⟨hstepIndex, _hget⟩ :=
        List.getElem?_eq_some_iff.mp hstateAt
      have hle : stepIndex <= count := by
        rw [hnested.1] at hstepIndex
        omega
      have hcanonical :=
        compactFormulaValuesLocalTraceValid_stateAt hlocal hle
      unfold compactFormulaValuesTraceState? at hcanonical
      rw [hstateAt] at hcanonical
      have heq : state = compactFormulaValuesStateAt
          (compactFormulaTokenValuesInitial tail) stepIndex :=
        Option.some.inj hcanonical
      obtain ⟨current, hcurrent⟩ :=
        compactFormulaValuesStateAt_eq_some_of_final hfinalAt hle
      rw [heq, hcurrent]
      have hcomponents :=
        compactFormulaValuesStateAt_components_weight_le hcurrent
      have htailSuffix : tail <:+ count :: tail :=
        List.suffix_cons count tail
      have htailWeight :=
        compactAdditiveValueWeight_suffix_le htailSuffix
      have hnestedWeight := compactNumericNestedListWeightBound_mono
        htailWeight
      rw [compactAdditiveValueWeight_option_some,
        compactAdditiveValueWeight_prod]
      unfold compactNumericSequentStateWeightBound
      omega

theorem compactSequentTokenValueDirectTraceValid_count_le_weight
    {count : Nat} {tail : List Nat}
    {values : List (List Nat)} {suffix : List Nat}
    {trace : CompactSequentTokenValueDirectTrace}
    (hvalid : CompactSequentTokenValueDirectTraceValid
      (count :: tail) values suffix trace) :
    count <= compactAdditiveValueWeight (count :: tail) := by
  have hrun :=
    compactSequentTokenValueDirectTraceValid_repeat_result hvalid
  have hcountTail :=
    (compactFormulaTokenValuesRepeat_components_weight_le hrun).2.2
  have htail : tail <:+ count :: tail := List.suffix_cons count tail
  have htailWeight := compactAdditiveValueWeight_suffix_le htail
  exact hcountTail.trans htailWeight

theorem compactSequentTokenValueDirectTraceValid_member_parserTrace_weight_le
    {tokens : List Nat} {values : List (List Nat)} {suffix : List Nat}
    {trace : CompactSequentTokenValueDirectTrace}
    (hvalid : CompactSequentTokenValueDirectTraceValid
      tokens values suffix trace)
    {parserTrace : CompactFormulaTokenParserDirectTrace}
    (hparserTrace : parserTrace ∈ trace.2) :
    compactAdditiveValueWeight parserTrace <=
      compactNumericRootSyntaxParserTraceWeightBound
        (compactAdditiveValueWeight tokens) := by
  cases tokens with
  | nil => simp [CompactSequentTokenValueDirectTraceValid] at hvalid
  | cons count tail =>
      unfold CompactSequentTokenValueDirectTraceValid at hvalid
      have hnested := hvalid.1
      have hlocal :=
        compactFormulaValuesNestedLocalTraceValid_implies_local hnested
      have hrun :=
        compactSequentTokenValueDirectTraceValid_repeat_result hvalid
      have hfinalAt : compactFormulaValuesStateAt
          (compactFormulaTokenValuesInitial tail) count =
            some (values, suffix) := by
        simpa [compactFormulaTokenValuesRepeat,
          compactFormulaTokenValuesInitial,
          compactFormulaValuesStateAt] using hrun
      obtain ⟨stepIndex, htraceAt⟩ :=
        List.mem_iff_getElem?.mp hparserTrace
      obtain ⟨hstepIndex, _hget⟩ :=
        List.getElem?_eq_some_iff.mp htraceAt
      have hlt : stepIndex < count := by
        rw [hnested.2.1] at hstepIndex
        exact hstepIndex
      obtain ⟨current, hcurrentAt⟩ :=
        compactFormulaValuesStateAt_eq_some_of_final hfinalAt
          (Nat.le_of_lt hlt)
      obtain ⟨next, hnextAt⟩ :=
        compactFormulaValuesStateAt_eq_some_of_final hfinalAt
          (by omega : stepIndex + 1 <= count)
      have hcurrentTrace :=
        compactFormulaValuesLocalTraceValid_stateAt hlocal
          (Nat.le_of_lt hlt)
      rw [hcurrentAt] at hcurrentTrace
      have hnextTrace :=
        compactFormulaValuesLocalTraceValid_stateAt hlocal
          (by omega : stepIndex + 1 <= count)
      rw [hnextAt] at hnextTrace
      have hparserTraceAt : compactFormulaValuesParserTrace?
          trace.2 stepIndex = some parserTrace := by
        unfold compactFormulaValuesParserTrace?
        exact htraceAt
      have htransition := hnested.2.2.2 stepIndex hlt
      have hconcrete :
          CompactFormulaValuesConcreteNestedTransitionValid
            current next parserTrace := by
        unfold CompactFormulaValuesNestedTransitionAt at htransition
        dsimp only at htransition
        simpa [hcurrentTrace, hnextTrace, hparserTraceAt] using htransition
      have hcomponents :=
        compactFormulaValuesStateAt_components_weight_le hcurrentAt
      have htailSuffix : tail <:+ count :: tail :=
        List.suffix_cons count tail
      have htailWeight :=
        compactAdditiveValueWeight_suffix_le htailSuffix
      have hstream : compactAdditiveValueWeight current.2 <=
          compactAdditiveValueWeight (count :: tail) :=
        hcomponents.2.trans htailWeight
      exact compactFormulaTokenParserDirectTraceValid_weight_le_rootBound
        hconcrete.1 hstream (by omega)

def compactNumericSequentDirectTraceWeightBound
    (streamWeight : Nat) : Nat :=
  (Nat.size (streamWeight + 1) + 1 +
    (streamWeight + 1) *
      compactNumericSequentStateWeightBound streamWeight) +
  (Nat.size streamWeight + 1 +
    streamWeight *
      compactNumericRootSyntaxParserTraceWeightBound streamWeight)

theorem compactSequentTokenValueDirectTraceValid_weight_le
    {tokens : List Nat} {values : List (List Nat)} {suffix : List Nat}
    {trace : CompactSequentTokenValueDirectTrace}
    (hvalid : CompactSequentTokenValueDirectTraceValid
      tokens values suffix trace) :
    compactAdditiveValueWeight trace <=
      compactNumericSequentDirectTraceWeightBound
        (compactAdditiveValueWeight tokens) := by
  cases tokens with
  | nil => simp [CompactSequentTokenValueDirectTraceValid] at hvalid
  | cons count tail =>
      let W := compactAdditiveValueWeight (count :: tail)
      have hcountRaw :=
        compactSequentTokenValueDirectTraceValid_count_le_weight hvalid
      have hcount : count <= W := by simpa [W] using hcountRaw
      have hfull := hvalid
      unfold CompactSequentTokenValueDirectTraceValid at hfull
      have hnested := hfull.1
      have hstateRows := compactAdditiveValueWeight_list_le trace.1
        (compactNumericSequentStateWeightBound W)
        (fun state hstate => by
          simpa [W] using
            compactSequentTokenValueDirectTraceValid_member_state_weight_le
              hvalid hstate)
      have hstateLength : trace.1.length <= W + 1 := by
        rw [hnested.1]
        omega
      have hstateSize := Nat.size_le_size hstateLength
      have hstateProduct := Nat.mul_le_mul_right
        (compactNumericSequentStateWeightBound W) hstateLength
      have hstates : compactAdditiveValueWeight trace.1 <=
          Nat.size (W + 1) + 1 + (W + 1) *
            compactNumericSequentStateWeightBound W := by
        omega
      have hparserRows := compactAdditiveValueWeight_list_le trace.2
        (compactNumericRootSyntaxParserTraceWeightBound W)
        (fun parserTrace hparserTrace => by
          simpa [W] using
            compactSequentTokenValueDirectTraceValid_member_parserTrace_weight_le
              hvalid hparserTrace)
      have hparserLength : trace.2.length <= W := by
        rw [hnested.2.1]
        exact hcount
      have hparserSize := Nat.size_le_size hparserLength
      have hparserProduct := Nat.mul_le_mul_right
        (compactNumericRootSyntaxParserTraceWeightBound W) hparserLength
      have hparsers : compactAdditiveValueWeight trace.2 <=
          Nat.size W + 1 + W *
            compactNumericRootSyntaxParserTraceWeightBound W := by
        omega
      rw [compactAdditiveValueWeight_prod]
      unfold compactNumericSequentDirectTraceWeightBound
      simpa [W] using Nat.add_le_add hstates hparsers

theorem compactNumericCertificateParserFuelWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericCertificateParserFuelWeightBound left <=
      compactNumericCertificateParserFuelWeightBound right := by
  have hadd : left + 1 <= right + 1 := by omega
  have hscaled := Nat.mul_le_mul_left 16 hadd
  have hquadratic := Nat.mul_le_mul hscaled hadd
  unfold compactNumericCertificateParserFuelWeightBound
  omega

theorem compactNumericRootSyntaxParserTraceWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericRootSyntaxParserTraceWeightBound left <=
      compactNumericRootSyntaxParserTraceWeightBound right := by
  have hfuel := compactNumericCertificateParserFuelWeightBound_mono h
  unfold compactNumericRootSyntaxParserTraceWeightBound
  exact compactNumericFormulaParserTraceWeightBound_mono h (by rfl) hfuel

theorem compactNumericSequentStateWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericSequentStateWeightBound left <=
      compactNumericSequentStateWeightBound right := by
  have hnested := compactNumericNestedListWeightBound_mono h
  unfold compactNumericSequentStateWeightBound
  omega

theorem compactNumericSequentDirectTraceWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericSequentDirectTraceWeightBound left <=
      compactNumericSequentDirectTraceWeightBound right := by
  have hadd : left + 1 <= right + 1 := by omega
  have haddSize := Nat.size_le_size hadd
  have hsize := Nat.size_le_size h
  have hstate := compactNumericSequentStateWeightBound_mono h
  have hstateTable := Nat.mul_le_mul hadd hstate
  have hparser := compactNumericRootSyntaxParserTraceWeightBound_mono h
  have hparserTable := Nat.mul_le_mul h hparser
  unfold compactNumericSequentDirectTraceWeightBound
  omega

theorem compactSequentTokenValueDirectTraceValid_suffix
    {tokens : List Nat} {values : List (List Nat)} {suffix : List Nat}
    {trace : CompactSequentTokenValueDirectTrace}
    (hvalid : CompactSequentTokenValueDirectTraceValid
      tokens values suffix trace) :
    suffix <:+ tokens := by
  have hparser : compactSequentTokenValueParser tokens =
      some (values, suffix) :=
    (compactSequentTokenValueParser_eq_some_iff_exists_directTrace
      tokens values suffix).mpr ⟨trace, hvalid⟩
  obtain ⟨Gamma, htokens, _hvalues⟩ :=
    compactSequentTokenValueParser_sound hparser
  exact ⟨compactSequentListTokens Gamma, htokens.symm⟩

theorem compactAdditiveValueWeight_nil_le_natList
    (tokens : List Nat) :
    compactAdditiveValueWeight ([] : List Nat) <=
      compactAdditiveValueWeight tokens := by
  simpa using compactAdditiveValueWeight_list_pos tokens

def CompactNumericRootFieldTraceComponentsWithin
    (streamWeight : Nat)
    (trace : CompactNumericRootFieldBranchDirectTrace) : Prop :=
  compactAdditiveValueWeight (compactRootBranchAfterSequent trace) <=
      streamWeight ∧
    compactAdditiveValueWeight (compactRootBranchSequentTrace trace) <=
      compactNumericSequentDirectTraceWeightBound streamWeight ∧
    compactAdditiveValueWeight (compactRootBranchAfterFirst trace) <=
      streamWeight ∧
    compactAdditiveValueWeight
        (compactRootBranchFirstFormulaTrace trace) <=
      compactNumericRootSyntaxParserTraceWeightBound streamWeight ∧
    compactAdditiveValueWeight (compactRootBranchFinalSuffix trace) <=
      streamWeight ∧
    compactAdditiveValueWeight
        (compactRootBranchSecondFormulaTrace trace) <=
      compactNumericRootSyntaxParserTraceWeightBound streamWeight ∧
    compactAdditiveValueWeight (compactRootBranchTermTrace trace) <=
      compactNumericRootSyntaxParserTraceWeightBound streamWeight ∧
    compactAdditiveValueWeight
        (compactRootBranchClosedFormulaTrace trace) <=
      compactNumericRootSyntaxParserTraceWeightBound streamWeight

theorem CompactNumericRootFieldTraceComponentsWithin.mono
    {left right : Nat} {trace : CompactNumericRootFieldBranchDirectTrace}
    (hcomponents : CompactNumericRootFieldTraceComponentsWithin left trace)
    (h : left <= right) :
    CompactNumericRootFieldTraceComponentsWithin right trace := by
  have hsequent := compactNumericSequentDirectTraceWeightBound_mono h
  have hsyntax := compactNumericRootSyntaxParserTraceWeightBound_mono h
  exact ⟨hcomponents.1.trans h,
    hcomponents.2.1.trans hsequent,
    hcomponents.2.2.1.trans h,
    hcomponents.2.2.2.1.trans hsyntax,
    hcomponents.2.2.2.2.1.trans h,
    hcomponents.2.2.2.2.2.1.trans hsyntax,
    hcomponents.2.2.2.2.2.2.1.trans hsyntax,
    hcomponents.2.2.2.2.2.2.2.trans hsyntax⟩

theorem compactNodeSequentOnlyDirectTraceValid_componentsWithin
    {tokens : List Nat} {fields : CompactNumericNodeFields}
    {trace : CompactNumericRootFieldBranchDirectTrace}
    (hvalid : CompactNodeSequentOnlyDirectTraceValid
      tokens fields trace) :
    CompactNumericRootFieldTraceComponentsWithin
      (compactAdditiveValueWeight tokens) trace := by
  unfold CompactNodeSequentOnlyDirectTraceValid at hvalid
  dsimp only at hvalid
  rcases hvalid with
    ⟨hsequent, _hfields, hfinal, hafterFirst, hfirst,
      hsecond, hterm, hclosed⟩
  have hafter := compactAdditiveValueWeight_suffix_le
    (compactSequentTokenValueDirectTraceValid_suffix hsequent)
  have hsequentWeight :=
    compactSequentTokenValueDirectTraceValid_weight_le hsequent
  have hnilList := compactAdditiveValueWeight_nil_le_natList tokens
  have hnilSyntax :=
    compactAdditiveValueWeight_nil_le_rootSyntaxParserTraceWeightBound
      (compactAdditiveValueWeight tokens)
  refine ⟨hafter, hsequentWeight, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hafterFirst]
    exact hnilList
  · rw [hfirst]
    exact hnilSyntax
  · rw [← hfinal]
    exact hafter
  · rw [hsecond]
    exact hnilSyntax
  · rw [hterm]
    exact hnilSyntax
  · rw [hclosed]
    exact hnilSyntax

theorem compactNodeSequentFormulaDirectTraceValid_componentsWithin
    {binderArity : Nat} {tokens : List Nat}
    {fields : CompactNumericNodeFields}
    {trace : CompactNumericRootFieldBranchDirectTrace}
    (hvalid : CompactNodeSequentFormulaDirectTraceValid
      binderArity tokens fields trace)
    (hbinder : binderArity <= 1) :
    CompactNumericRootFieldTraceComponentsWithin
      (compactAdditiveValueWeight tokens) trace := by
  unfold CompactNodeSequentFormulaDirectTraceValid at hvalid
  dsimp only at hvalid
  rcases hvalid with
    ⟨hsequent, hformula, _hfields, hfinal,
      hsecond, hterm, hclosed⟩
  have hafterSuffix :=
    compactSequentTokenValueDirectTraceValid_suffix hsequent
  have hafter := compactAdditiveValueWeight_suffix_le hafterSuffix
  have hsequentWeight :=
    compactSequentTokenValueDirectTraceValid_weight_le hsequent
  have hformulaResult :=
    (compactFormulaTokenParser_eq_some_iff_exists_directTrace
      binderArity (compactRootBranchAfterSequent trace)
        (compactRootBranchAfterFirst trace)).mpr
      ⟨compactRootBranchFirstFormulaTrace trace, hformula⟩
  have hfirstSuffix :=
    (compactFormulaTokenParser_suffix_of_success hformulaResult).trans
      hafterSuffix
  have hfirst := compactAdditiveValueWeight_suffix_le hfirstSuffix
  have hformulaWeight :=
    compactFormulaTokenParserDirectTraceValid_weight_le_rootBound
      hformula hafter hbinder
  have hnilSyntax :=
    compactAdditiveValueWeight_nil_le_rootSyntaxParserTraceWeightBound
      (compactAdditiveValueWeight tokens)
  refine ⟨hafter, hsequentWeight, hfirst, hformulaWeight,
    ?_, ?_, ?_, ?_⟩
  · rw [← hfinal]
    exact hfirst
  · rw [hsecond]
    exact hnilSyntax
  · rw [hterm]
    exact hnilSyntax
  · rw [hclosed]
    exact hnilSyntax

theorem compactNodeSequentTwoFormulaDirectTraceValid_componentsWithin
    {binderArity : Nat} {tokens : List Nat}
    {fields : CompactNumericNodeFields}
    {trace : CompactNumericRootFieldBranchDirectTrace}
    (hvalid : CompactNodeSequentTwoFormulaDirectTraceValid
      binderArity tokens fields trace)
    (hbinder : binderArity <= 1) :
    CompactNumericRootFieldTraceComponentsWithin
      (compactAdditiveValueWeight tokens) trace := by
  unfold CompactNodeSequentTwoFormulaDirectTraceValid at hvalid
  dsimp only at hvalid
  rcases hvalid with
    ⟨hsequent, hfirstFormula, hsecondFormula,
      _hfields, hterm, hclosed⟩
  have hafterSuffix :=
    compactSequentTokenValueDirectTraceValid_suffix hsequent
  have hafter := compactAdditiveValueWeight_suffix_le hafterSuffix
  have hsequentWeight :=
    compactSequentTokenValueDirectTraceValid_weight_le hsequent
  have hfirstResult :=
    (compactFormulaTokenParser_eq_some_iff_exists_directTrace
      binderArity (compactRootBranchAfterSequent trace)
        (compactRootBranchAfterFirst trace)).mpr
      ⟨compactRootBranchFirstFormulaTrace trace, hfirstFormula⟩
  have hfirstSuffix :=
    (compactFormulaTokenParser_suffix_of_success hfirstResult).trans
      hafterSuffix
  have hfirst := compactAdditiveValueWeight_suffix_le hfirstSuffix
  have hfirstWeight :=
    compactFormulaTokenParserDirectTraceValid_weight_le_rootBound
      hfirstFormula hafter hbinder
  have hsecondResult :=
    (compactFormulaTokenParser_eq_some_iff_exists_directTrace
      binderArity (compactRootBranchAfterFirst trace)
        (compactRootBranchFinalSuffix trace)).mpr
      ⟨compactRootBranchSecondFormulaTrace trace, hsecondFormula⟩
  have hfinalSuffix :=
    (compactFormulaTokenParser_suffix_of_success hsecondResult).trans
      hfirstSuffix
  have hfinal := compactAdditiveValueWeight_suffix_le hfinalSuffix
  have hsecondWeight :=
    compactFormulaTokenParserDirectTraceValid_weight_le_rootBound
      hsecondFormula hfirst hbinder
  have hnilSyntax :=
    compactAdditiveValueWeight_nil_le_rootSyntaxParserTraceWeightBound
      (compactAdditiveValueWeight tokens)
  refine ⟨hafter, hsequentWeight, hfirst, hfirstWeight,
    hfinal, hsecondWeight, ?_, ?_⟩
  · rw [hterm]
    exact hnilSyntax
  · rw [hclosed]
    exact hnilSyntax

theorem compactNodeSequentFormulaTermDirectTraceValid_componentsWithin
    {formulaArity termArity : Nat} {tokens : List Nat}
    {fields : CompactNumericNodeFields}
    {trace : CompactNumericRootFieldBranchDirectTrace}
    (hvalid : CompactNodeSequentFormulaTermDirectTraceValid
      formulaArity termArity tokens fields trace)
    (hformulaBinder : formulaArity <= 1)
    (htermBinder : termArity <= 1) :
    CompactNumericRootFieldTraceComponentsWithin
      (compactAdditiveValueWeight tokens) trace := by
  unfold CompactNodeSequentFormulaTermDirectTraceValid at hvalid
  dsimp only at hvalid
  rcases hvalid with
    ⟨hsequent, hformula, htermTrace,
      _hfields, hsecond, hclosed⟩
  have hafterSuffix :=
    compactSequentTokenValueDirectTraceValid_suffix hsequent
  have hafter := compactAdditiveValueWeight_suffix_le hafterSuffix
  have hsequentWeight :=
    compactSequentTokenValueDirectTraceValid_weight_le hsequent
  have hformulaResult :=
    (compactFormulaTokenParser_eq_some_iff_exists_directTrace
      formulaArity (compactRootBranchAfterSequent trace)
        (compactRootBranchAfterFirst trace)).mpr
      ⟨compactRootBranchFirstFormulaTrace trace, hformula⟩
  have hfirstSuffix :=
    (compactFormulaTokenParser_suffix_of_success hformulaResult).trans
      hafterSuffix
  have hfirst := compactAdditiveValueWeight_suffix_le hfirstSuffix
  have hformulaWeight :=
    compactFormulaTokenParserDirectTraceValid_weight_le_rootBound
      hformula hafter hformulaBinder
  have htermResult :=
    (compactTermTokenParser_eq_some_iff_exists_directTrace
      termArity (compactRootBranchAfterFirst trace)
        (compactRootBranchFinalSuffix trace)).mpr
      ⟨compactRootBranchTermTrace trace, htermTrace⟩
  have hfinalSuffix :=
    (compactTermTokenParser_suffix_of_success htermResult).trans
      hfirstSuffix
  have hfinal := compactAdditiveValueWeight_suffix_le hfinalSuffix
  have htermWeight :=
    compactTermTokenParserDirectTraceValid_weight_le_rootBound
      htermTrace hfirst htermBinder
  have hnilSyntax :=
    compactAdditiveValueWeight_nil_le_rootSyntaxParserTraceWeightBound
      (compactAdditiveValueWeight tokens)
  refine ⟨hafter, hsequentWeight, hfirst, hformulaWeight,
    hfinal, ?_, htermWeight, ?_⟩
  · rw [hsecond]
    exact hnilSyntax
  · rw [hclosed]
    exact hnilSyntax

theorem compactNodeSequentClosedFormulaDirectTraceValid_componentsWithin
    {tokens : List Nat} {fields : CompactNumericNodeFields}
    {trace : CompactNumericRootFieldBranchDirectTrace}
    (hvalid : CompactNodeSequentClosedFormulaDirectTraceValid
      tokens fields trace) :
    CompactNumericRootFieldTraceComponentsWithin
      (compactAdditiveValueWeight tokens) trace := by
  unfold CompactNodeSequentClosedFormulaDirectTraceValid at hvalid
  dsimp only at hvalid
  rcases hvalid with
    ⟨hsequent, hclosedTrace, _hfields,
      hafterFirst, hfirst, hsecond, hterm⟩
  have hafterSuffix :=
    compactSequentTokenValueDirectTraceValid_suffix hsequent
  have hafter := compactAdditiveValueWeight_suffix_le hafterSuffix
  have hsequentWeight :=
    compactSequentTokenValueDirectTraceValid_weight_le hsequent
  have hclosedResult :=
    (compactClosedFormulaTokenParser_eq_some_iff_exists_directTrace
      0 (compactRootBranchAfterSequent trace)
        (compactRootBranchFinalSuffix trace)).mpr
      ⟨compactRootBranchClosedFormulaTrace trace, hclosedTrace⟩
  have hfinalSuffix :=
    (compactClosedFormulaTokenParser_suffix_of_success hclosedResult).trans
      hafterSuffix
  have hfinal := compactAdditiveValueWeight_suffix_le hfinalSuffix
  have hclosedWeight :=
    compactClosedFormulaTokenParserDirectTraceValid_weight_le_rootBound
      hclosedTrace hafter (by omega)
  have hnilList := compactAdditiveValueWeight_nil_le_natList tokens
  have hnilSyntax :=
    compactAdditiveValueWeight_nil_le_rootSyntaxParserTraceWeightBound
      (compactAdditiveValueWeight tokens)
  refine ⟨hafter, hsequentWeight, ?_, ?_, hfinal, ?_, ?_,
    hclosedWeight⟩
  · rw [hafterFirst]
    exact hnilList
  · rw [hfirst]
    exact hnilSyntax
  · rw [hsecond]
    exact hnilSyntax
  · rw [hterm]
    exact hnilSyntax

theorem compactNumericProofRootDirectTraceValid_componentsWithin
    {tokens : List Nat} {root : CompactNumericProofRoot}
    {trace : CompactNumericRootFieldBranchDirectTrace}
    (hvalid : CompactNumericProofRootDirectTraceValid tokens root trace) :
    CompactNumericRootFieldTraceComponentsWithin
      (compactAdditiveValueWeight tokens) trace := by
  have htailSuffix : tokens.tail <:+ tokens := by
    cases tokens <;> simp
  have htailWeight := compactAdditiveValueWeight_suffix_le htailSuffix
  unfold CompactNumericProofRootDirectTraceValid at hvalid
  rcases hvalid with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · rcases h0 with ⟨_htag, _hroot, hshape⟩
    exact (compactNodeSequentFormulaDirectTraceValid_componentsWithin
      hshape (by omega)).mono htailWeight
  · rcases h1 with ⟨_htag, _hroot, hshape⟩
    exact (compactNodeSequentClosedFormulaDirectTraceValid_componentsWithin
      hshape).mono htailWeight
  · rcases h2 with ⟨_htag, _hroot, hshape⟩
    exact (compactNodeSequentOnlyDirectTraceValid_componentsWithin
      hshape).mono htailWeight
  · rcases h3 with ⟨_htag, _hroot, hshape⟩
    exact (compactNodeSequentTwoFormulaDirectTraceValid_componentsWithin
      hshape (by omega)).mono htailWeight
  · rcases h4 with ⟨_htag, _hroot, hshape⟩
    exact (compactNodeSequentTwoFormulaDirectTraceValid_componentsWithin
      hshape (by omega)).mono htailWeight
  · rcases h5 with ⟨_htag, _hroot, hshape⟩
    exact (compactNodeSequentFormulaDirectTraceValid_componentsWithin
      hshape (by omega)).mono htailWeight
  · rcases h6 with ⟨_htag, _hroot, hshape⟩
    exact (compactNodeSequentFormulaTermDirectTraceValid_componentsWithin
      hshape (by omega) (by omega)).mono htailWeight
  · rcases h7 with ⟨_htag, _hroot, hshape⟩
    exact (compactNodeSequentOnlyDirectTraceValid_componentsWithin
      hshape).mono htailWeight
  · rcases h8 with ⟨_htag, _hroot, hshape⟩
    exact (compactNodeSequentOnlyDirectTraceValid_componentsWithin
      hshape).mono htailWeight
  · rcases h9 with ⟨_htag, _hroot, hshape⟩
    exact (compactNodeSequentFormulaDirectTraceValid_componentsWithin
      hshape (by omega)).mono htailWeight

def compactNumericRootFieldBranchTraceWeightBound
    (streamWeight : Nat) : Nat :=
  3 * streamWeight +
    compactNumericSequentDirectTraceWeightBound streamWeight +
    4 * compactNumericRootSyntaxParserTraceWeightBound streamWeight

theorem CompactNumericRootFieldTraceComponentsWithin.weight_le
    {streamWeight : Nat}
    {trace : CompactNumericRootFieldBranchDirectTrace}
    (hcomponents : CompactNumericRootFieldTraceComponentsWithin
      streamWeight trace) :
    compactAdditiveValueWeight trace <=
      compactNumericRootFieldBranchTraceWeightBound streamWeight := by
  unfold CompactNumericRootFieldTraceComponentsWithin at hcomponents
  simp only [compactRootBranchAfterSequent,
    compactRootBranchSequentTrace,
    compactRootBranchAfterFirst,
    compactRootBranchFirstFormulaTrace,
    compactRootBranchFinalSuffix,
    compactRootBranchSecondFormulaTrace,
    compactRootBranchTermTrace,
    compactRootBranchClosedFormulaTrace] at hcomponents
  simp only [compactAdditiveValueWeight_prod] at hcomponents
  simp only [compactAdditiveValueWeight_prod]
  unfold compactNumericRootFieldBranchTraceWeightBound
  omega

theorem compactNumericListedDirectTrace_rootBranchTrace_weight_le
    {code formulaCode : Nat} {trace : CompactNumericListedDirectTrace}
    (hvalid : CompactNumericListedDirectTraceValid code formulaCode trace) :
    compactAdditiveValueWeight
        (compactNumericDirectTraceRootBranchTrace trace) <=
      compactNumericRootFieldBranchTraceWeightBound
        (compactNumericDecodedTokenListWeightBound (Nat.size code)) := by
  have hfull := hvalid
  unfold CompactNumericListedDirectTraceValid at hfull
  have hresidual := hfull.2.2.2.2.2.1
  unfold CompactNumericCertifiedPartsResidualValid at hresidual
  have hcomponents :=
    compactNumericProofRootDirectTraceValid_componentsWithin hresidual.2.1
  have hproof :=
    (compactNumericListedDirectTrace_parts_components_weight_le hvalid).1
  have hcertified :=
    compactNumericListedDirectTrace_certifiedTokens_weight_le hvalid
  exact (hcomponents.mono (hproof.trans hcertified)).weight_le

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
#print axioms compactPAAxiomCertificateTokenParser_suffix
#print axioms compactCertificateParserLocalTrace_member_source
#print axioms compactCertificateParserLocalTrace_member_state_weight_le
#print axioms compactCertificateTokenParserDirectTraceValid_weight_le
#print axioms compactNumericListedDirectTrace_certificateParserTrace_weight_le
#print axioms compactFormulaParserLocalTrace_member_source
#print axioms compactFormulaParserLocalTrace_member_state_weight_le
#print axioms compactFormulaTokenParserDirectTraceValid_weight_le
#print axioms compactNumericListedDirectTrace_formulaParserTrace_weight_le
#print axioms compactProofParserLocalTrace_member_source
#print axioms compactProofParserLocalTrace_member_state_weight_le
#print axioms compactProofTokenParserDirectTraceValid_weight_le
#print axioms compactNumericListedDirectTrace_proofParserTrace_weight_le
#print axioms compactTermTokenParserDirectTraceValid_weight_le
#print axioms compactClosedFormulaTokenParserDirectTraceValid_weight_le
#print axioms compactSequentTokenValueDirectTraceValid_weight_le
#print axioms compactNumericProofRootDirectTraceValid_componentsWithin
#print axioms compactNumericListedDirectTrace_rootBranchTrace_weight_le

end FoundationCompactNumericListedDirectTraceBounds
