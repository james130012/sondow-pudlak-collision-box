import integration.FoundationCompactNumericListedDirectTraceBounds

/-!
# Bounded numeric witness for the complete direct verifier trace

This module turns the typed direct trace into one deterministic natural-number
certificate.  The certificate checker decodes the supplied trace code and then
checks the existing direct-trace relation; it performs no search or projection.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedBoundedTraceCode

open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedStateBounds
open FoundationCompactNumericListedPublicVerifier

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericRootFieldBranchDirectTracePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericParserDirectTracesPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericParsedDirectTraceDataPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericDirectTraceTailPrimcodable

def compactNumericListedDirectTraceValidDecision
    (input : (Nat × Nat) × CompactNumericListedDirectTrace) : Bool :=
  @decide
    (CompactNumericListedDirectTraceValid input.1.1 input.1.2 input.2)
    (compactNumericListedDirectTraceValid_primrec.choose input)

theorem compactNumericListedDirectTraceValidDecision_primrec :
    Primrec compactNumericListedDirectTraceValidDecision := by
  exact compactNumericListedDirectTraceValid_primrec.choose_spec

@[simp] theorem compactNumericListedDirectTraceValidDecision_eq_true_iff
    (code formulaCode : Nat) (trace : CompactNumericListedDirectTrace) :
    compactNumericListedDirectTraceValidDecision
        ((code, formulaCode), trace) = true ↔
      CompactNumericListedDirectTraceValid code formulaCode trace := by
  simp [compactNumericListedDirectTraceValidDecision]

def compactNumericListedDirectTraceCodeVerifier
    (code formulaCode traceCode : Nat) : Bool :=
  match compactNumericListedDirectTraceCodeDecode traceCode with
  | none => false
  | some trace =>
      compactNumericListedDirectTraceValidDecision
        ((code, formulaCode), trace)

theorem compactNumericListedDirectTraceCodeVerifier_primrec :
    Primrec (fun input : (Nat × Nat) × Nat =>
      compactNumericListedDirectTraceCodeVerifier
        input.1.1 input.1.2 input.2) := by
  let Input := (Nat × Nat) × Nat
  have hdecode : Primrec (fun input : Input =>
      compactNumericListedDirectTraceCodeDecode input.2) :=
    compactNumericListedDirectTraceCodeDecode_primrec.comp Primrec.snd
  have hvalidDecision : Primrec₂
      (fun (input : Input) (trace : CompactNumericListedDirectTrace) =>
        compactNumericListedDirectTraceValidDecision
          ((input.1.1, input.1.2), trace)) := by
    apply Primrec₂.mk
    have hcode : Primrec (fun pair :
        Input × CompactNumericListedDirectTrace => pair.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hformulaCode : Primrec (fun pair :
        Input × CompactNumericListedDirectTrace => pair.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have htrace : Primrec (fun pair :
        Input × CompactNumericListedDirectTrace => pair.2) :=
      Primrec.snd
    exact compactNumericListedDirectTraceValidDecision_primrec.comp
      (Primrec.pair (Primrec.pair hcode hformulaCode) htrace)
  exact
    (Primrec.option_casesOn hdecode (Primrec.const false) hvalidDecision).of_eq
      fun input => by
        cases hdecoded : compactNumericListedDirectTraceCodeDecode input.2 <;>
          simp [compactNumericListedDirectTraceCodeVerifier, hdecoded]

def CompactNumericListedDirectTraceCodeValid
    (code formulaCode traceCode : Nat) : Prop :=
  compactNumericListedDirectTraceCodeVerifier
    code formulaCode traceCode = true

theorem compactNumericListedDirectTraceCodeValid_primrec :
    PrimrecPred (fun input : (Nat × Nat) × Nat =>
      CompactNumericListedDirectTraceCodeValid
        input.1.1 input.1.2 input.2) := by
  exact Primrec.eq.comp
    compactNumericListedDirectTraceCodeVerifier_primrec
    (Primrec.const true)

theorem compactNumericListedDirectTraceCodeValid_iff_exists_trace
    (code formulaCode traceCode : Nat) :
    CompactNumericListedDirectTraceCodeValid code formulaCode traceCode ↔
      ∃ trace : CompactNumericListedDirectTrace,
        compactNumericListedDirectTraceCodeDecode traceCode = some trace ∧
          CompactNumericListedDirectTraceValid code formulaCode trace := by
  cases hdecoded : compactNumericListedDirectTraceCodeDecode traceCode with
  | none =>
      simp [CompactNumericListedDirectTraceCodeValid,
        compactNumericListedDirectTraceCodeVerifier, hdecoded]
  | some trace =>
      simp [CompactNumericListedDirectTraceCodeValid,
        compactNumericListedDirectTraceCodeVerifier, hdecoded]

@[simp] theorem compactNumericListedDirectTraceCodeValid_code_iff
    (code formulaCode : Nat) (trace : CompactNumericListedDirectTrace) :
    CompactNumericListedDirectTraceCodeValid code formulaCode
        (compactNumericListedDirectTraceCode trace) ↔
      CompactNumericListedDirectTraceValid code formulaCode trace := by
  simp [compactNumericListedDirectTraceCodeValid_iff_exists_trace,
    compactNumericListedDirectTraceCodeDecode_code]

theorem compactTraceNatSize_primrec : Primrec Nat.size := by
  exact (Primrec.list_length.comp
    FoundationCompactListedVerifierArithmeticInput.natBits_primrec).of_eq
      fun code => by simp [Nat.size_eq_bits_len]

macro "compact_trace_primrec_arith" : tactic =>
  `(tactic|
    repeat
      first
      | exact Primrec.id
      | exact Primrec.fst
      | exact Primrec.snd
      | exact Primrec.const _
      | apply Primrec.nat_add.comp
      | apply Primrec.nat_mul.comp
      | apply compactTraceNatSize_primrec.comp)

theorem compactNumericDecodedTokenListWeightBound_primrec :
    Primrec compactNumericDecodedTokenListWeightBound := by
  unfold compactNumericDecodedTokenListWeightBound
  compact_trace_primrec_arith

theorem compactNumericPackedTokenStreamTraceWeightBound_primrec :
    Primrec compactNumericPackedTokenStreamTraceWeightBound := by
  unfold compactNumericPackedTokenStreamTraceWeightBound
    compactNumericBoolListWeightBound
    compactNumericBinaryNatStreamStateWeightBound
    compactNumericDecodedTokenListWeightBound
  compact_trace_primrec_arith

theorem compactNumericProofParserPublicTraceWeightBound_primrec :
    Primrec compactNumericProofParserPublicTraceWeightBound := by
  unfold compactNumericProofParserPublicTraceWeightBound
    compactNumericProofParserTraceWeightBound
    compactNumericProofParserStateWeightBound
    compactNumericProofParserTaskWeightBound
    compactNumericProofParserFuelWeightBound
    compactNumericDecodedTokenListWeightBound
  compact_trace_primrec_arith

theorem compactNumericCertificateParserPublicTraceWeightBound_primrec :
    Primrec compactNumericCertificateParserPublicTraceWeightBound := by
  unfold compactNumericCertificateParserPublicTraceWeightBound
    compactNumericCertificateParserTraceWeightBound
    compactNumericCertificateParserStateWeightBound
    compactNumericCertificateParserFuelWeightBound
    compactNumericDecodedTokenListWeightBound
  compact_trace_primrec_arith

theorem compactNumericFormulaParserPublicTraceWeightBound_primrec :
    Primrec compactNumericFormulaParserPublicTraceWeightBound := by
  unfold compactNumericFormulaParserPublicTraceWeightBound
    compactNumericFormulaParserTraceWeightBound
    compactNumericFormulaParserStateWeightBound
    compactNumericSyntaxParserTaskWeightBound
    compactNumericCertificateParserFuelWeightBound
    compactNumericDecodedTokenListWeightBound
  compact_trace_primrec_arith

theorem compactNumericCertifiedPartsWeightBound_primrec :
    Primrec compactNumericCertifiedPartsWeightBound := by
  unfold compactNumericCertifiedPartsWeightBound
    compactNumericNestedListWeightBound
  compact_trace_primrec_arith

theorem compactNumericVerifierTaskWeightBound_primrec :
    Primrec compactNumericVerifierTaskWeightBound := by
  unfold compactNumericVerifierTaskWeightBound
    compactNumericNodeFieldsWeightBound
    compactNumericNestedListWeightBound
  compact_trace_primrec_arith

theorem compactNumericChildResultWeightBound_primrec :
    Primrec compactNumericChildResultWeightBound := by
  unfold compactNumericChildResultWeightBound
    compactNumericNestedListWeightBound
  compact_trace_primrec_arith

theorem compactNumericVerifierPublicFuelWeightBound_primrec :
    Primrec compactNumericVerifierPublicFuelWeightBound := by
  unfold compactNumericVerifierPublicFuelWeightBound
  compact_trace_primrec_arith

theorem compactNumericRootSyntaxParserTraceWeightBound_primrec :
    Primrec compactNumericRootSyntaxParserTraceWeightBound := by
  unfold compactNumericRootSyntaxParserTraceWeightBound
    compactNumericFormulaParserTraceWeightBound
    compactNumericFormulaParserStateWeightBound
    compactNumericSyntaxParserTaskWeightBound
    compactNumericCertificateParserFuelWeightBound
  compact_trace_primrec_arith

theorem compactNumericSequentStateWeightBound_primrec :
    Primrec compactNumericSequentStateWeightBound := by
  unfold compactNumericSequentStateWeightBound
    compactNumericNestedListWeightBound
  compact_trace_primrec_arith

macro "compact_trace_primrec_components" : tactic =>
  `(tactic|
    repeat
      first
      | exact Primrec.id
      | exact Primrec.fst
      | exact Primrec.snd
      | exact Primrec.const _
      | apply Primrec.nat_add.comp
      | apply Primrec.nat_mul.comp
      | apply compactTraceNatSize_primrec.comp
      | apply compactNumericDecodedTokenListWeightBound_primrec.comp
      | apply compactNumericPackedTokenStreamTraceWeightBound_primrec.comp
      | apply compactNumericProofParserPublicTraceWeightBound_primrec.comp
      | apply compactNumericCertificateParserPublicTraceWeightBound_primrec.comp
      | apply compactNumericFormulaParserPublicTraceWeightBound_primrec.comp
      | apply compactNumericCertifiedPartsWeightBound_primrec.comp
      | apply compactNumericVerifierTaskWeightBound_primrec.comp
      | apply compactNumericRootSyntaxParserTraceWeightBound_primrec.comp
      | apply compactNumericSequentStateWeightBound_primrec.comp)

theorem compactNumericSequentDirectTraceWeightBound_primrec :
    Primrec compactNumericSequentDirectTraceWeightBound := by
  unfold compactNumericSequentDirectTraceWeightBound
  compact_trace_primrec_components

theorem compactNumericRootFieldBranchTraceWeightBound_primrec :
    Primrec compactNumericRootFieldBranchTraceWeightBound := by
  unfold compactNumericRootFieldBranchTraceWeightBound
    compactNumericSequentDirectTraceWeightBound
  compact_trace_primrec_components

theorem compactNumericVerifierPublicTableWeightBound_primrec :
    Primrec compactNumericVerifierPublicTableWeightBound := by
  unfold compactNumericVerifierPublicTableWeightBound
    compactNumericVerifierPublicFuelWeightBound
    compactNumericVerifierPublicRowWeightBound
    compactNumericVerifierStateBudget
    compactNumericVerifierTaskWeightBound
    compactNumericChildResultWeightBound
    compactNumericNodeFieldsWeightBound
    compactNumericNestedListWeightBound
  compact_trace_primrec_arith

theorem compactNumericListedDirectTracePublicCodeSizeBound_primrec :
    Primrec₂ compactNumericListedDirectTracePublicCodeSizeBound := by
  apply Primrec₂.mk
  have hproofWeight : Primrec (fun input : Nat × Nat =>
      compactNumericDecodedTokenListWeightBound input.1) :=
    compactNumericDecodedTokenListWeightBound_primrec.comp Primrec.fst
  have hformulaWeight : Primrec (fun input : Nat × Nat =>
      compactNumericDecodedTokenListWeightBound input.2) :=
    compactNumericDecodedTokenListWeightBound_primrec.comp Primrec.snd
  have hproofPacked : Primrec (fun input : Nat × Nat =>
      compactNumericPackedTokenStreamTraceWeightBound input.1) :=
    compactNumericPackedTokenStreamTraceWeightBound_primrec.comp Primrec.fst
  have hformulaPacked : Primrec (fun input : Nat × Nat =>
      compactNumericPackedTokenStreamTraceWeightBound input.2) :=
    compactNumericPackedTokenStreamTraceWeightBound_primrec.comp Primrec.snd
  have hproofParser : Primrec (fun input : Nat × Nat =>
      compactNumericProofParserPublicTraceWeightBound input.1) :=
    compactNumericProofParserPublicTraceWeightBound_primrec.comp Primrec.fst
  have hcertificateParser : Primrec (fun input : Nat × Nat =>
      compactNumericCertificateParserPublicTraceWeightBound input.1) :=
    compactNumericCertificateParserPublicTraceWeightBound_primrec.comp
      Primrec.fst
  have hformulaParser : Primrec (fun input : Nat × Nat =>
      compactNumericFormulaParserPublicTraceWeightBound input.2) :=
    compactNumericFormulaParserPublicTraceWeightBound_primrec.comp Primrec.snd
  have hparts : Primrec (fun input : Nat × Nat =>
      compactNumericCertifiedPartsWeightBound
        (compactNumericDecodedTokenListWeightBound input.1)) :=
    compactNumericCertifiedPartsWeightBound_primrec.comp hproofWeight
  have htask : Primrec (fun input : Nat × Nat =>
      compactNumericVerifierTaskWeightBound
        (compactNumericDecodedTokenListWeightBound input.1)) :=
    compactNumericVerifierTaskWeightBound_primrec.comp hproofWeight
  have hroot : Primrec (fun input : Nat × Nat =>
      compactNumericRootFieldBranchTraceWeightBound
        (compactNumericDecodedTokenListWeightBound input.1)) :=
    compactNumericRootFieldBranchTraceWeightBound_primrec.comp hproofWeight
  have htable : Primrec (fun input : Nat × Nat =>
      compactNumericVerifierPublicTableWeightBound
        (compactNumericDecodedTokenListWeightBound input.1)) :=
    compactNumericVerifierPublicTableWeightBound_primrec.comp hproofWeight
  have hfirst := Primrec.nat_add.comp hproofWeight hproofPacked
  have hsecond := Primrec.nat_add.comp hformulaWeight hformulaPacked
  have hparsers := Primrec.nat_add.comp hproofParser
    (Primrec.nat_add.comp hcertificateParser hformulaParser)
  have htail := Primrec.nat_add.comp hparts
    (Primrec.nat_add.comp htask
      (Primrec.nat_add.comp hroot
        (Primrec.nat_add.comp hformulaWeight htable)))
  have hweight := Primrec.nat_add.comp hfirst
    (Primrec.nat_add.comp hsecond
      (Primrec.nat_add.comp hparsers htail))
  exact (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2) hweight)
    (Primrec.const 1)).of_eq fun input => by rfl

def CompactNumericListedBoundedTraceCodeWitness
    (code formulaCode traceCode : Nat) : Prop :=
  Nat.size traceCode <=
      compactNumericListedDirectTracePublicCodeSizeBound
        (Nat.size code) (Nat.size formulaCode) ∧
    CompactNumericListedDirectTraceCodeValid code formulaCode traceCode

theorem compactNumericListedBoundedTraceCodeWitness_primrec :
    PrimrecPred (fun input : (Nat × Nat) × Nat =>
      CompactNumericListedBoundedTraceCodeWitness
        input.1.1 input.1.2 input.2) := by
  have hcodeSize : Primrec (fun input : (Nat × Nat) × Nat =>
      Nat.size input.1.1) :=
    compactTraceNatSize_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hformulaCodeSize : Primrec (fun input : (Nat × Nat) × Nat =>
      Nat.size input.1.2) :=
    compactTraceNatSize_primrec.comp (Primrec.snd.comp Primrec.fst)
  have htraceCodeSize : Primrec (fun input : (Nat × Nat) × Nat =>
      Nat.size input.2) :=
    compactTraceNatSize_primrec.comp Primrec.snd
  have hbound : Primrec (fun input : (Nat × Nat) × Nat =>
      compactNumericListedDirectTracePublicCodeSizeBound
        (Nat.size input.1.1) (Nat.size input.1.2)) :=
    compactNumericListedDirectTracePublicCodeSizeBound_primrec.comp
      hcodeSize hformulaCodeSize
  have hsizeGuard : PrimrecPred (fun input : (Nat × Nat) × Nat =>
      Nat.size input.2 <=
        compactNumericListedDirectTracePublicCodeSizeBound
          (Nat.size input.1.1) (Nat.size input.1.2)) :=
    Primrec.nat_le.comp htraceCodeSize hbound
  exact (hsizeGuard.and
    compactNumericListedDirectTraceCodeValid_primrec).of_eq fun input => by
      rfl

theorem compactNumericListedPublicVerifier_eq_true_iff_exists_boundedTraceCode
    (code formulaCode : Nat) :
    compactNumericListedPublicVerifier code formulaCode = true ↔
      ∃ traceCode : Nat,
        CompactNumericListedBoundedTraceCodeWitness
          code formulaCode traceCode := by
  constructor
  · intro haccept
    obtain ⟨trace, hvalid⟩ :=
      (compactNumericListedPublicVerifier_eq_true_iff_exists_directTrace
        code formulaCode).mp haccept
    refine ⟨compactNumericListedDirectTraceCode trace, ?_, ?_⟩
    · exact compactNumericListedDirectTraceCode_size_le hvalid
    · exact compactNumericListedDirectTraceCodeValid_code_iff
        code formulaCode trace |>.2 hvalid
  · rintro ⟨traceCode, _hsize, hcode⟩
    obtain ⟨trace, _hdecode, hvalid⟩ :=
      (compactNumericListedDirectTraceCodeValid_iff_exists_trace
        code formulaCode traceCode).mp hcode
    exact
      (compactNumericListedPublicVerifier_eq_true_iff_exists_directTrace
        code formulaCode).mpr ⟨trace, hvalid⟩

#print axioms compactNumericListedDirectTraceCodeVerifier_primrec
#print axioms compactNumericListedDirectTraceCodeValid_primrec
#print axioms compactNumericListedDirectTraceCodeValid_iff_exists_trace
#print axioms compactNumericListedDirectTracePublicCodeSizeBound_primrec
#print axioms compactNumericListedBoundedTraceCodeWitness_primrec
#print axioms compactNumericListedPublicVerifier_eq_true_iff_exists_boundedTraceCode

end FoundationCompactNumericListedBoundedTraceCode
