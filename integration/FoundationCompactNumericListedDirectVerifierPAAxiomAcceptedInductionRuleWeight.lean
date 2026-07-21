import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds
import integration.FoundationCompactNumericListedDirectFormulaTokenWeightBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformFinalOutputBounds
import integration.FoundationCompactNumericListedDirectFormulaFvSupTraceWeightBounds
import integration.FoundationCompactNumericListedDirectFormulaFixitrTraceWeightBounds

/-!
# Original-input bounds for an accepted induction-axiom leaf

The eager direct route serializes the generated induction sentence and all of
its transform traces.  Such a serialization is not polynomial in a sparse
induction certificate without an acceptance hypothesis.  This file uses the
actual guarded PA-axiom checker: acceptance identifies the generated closure
with the supplied candidate and bounds the free-variable depth by the
candidate's genuine binary code length.

The public scale below contains only the three original leaf inputs.  It does
not contain the expanded route, a precomputed trace, or an externally supplied
bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionRuleWeight

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactAdditiveTokenCodec
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertificateTokenMachine
open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTransformationTraceCore
open FoundationCompactSyntaxTransformationTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericFormulaConstructors
open FoundationCompactNumericFormulaFvSup
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericAllClosure
open FoundationCompactNumericPAAxiomComparator
open FoundationCompactNumericGuardedInductionSentence
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericTokenBitLength
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectFormulaTransformValueBounds
open FoundationCompactNumericListedDirectFormulaTransformExactFormula
open FoundationCompactNumericListedDirectFormulaFvSupTraceWeightBounds
open FoundationCompactNumericListedDirectFormulaFixitrTraceWeightBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectGuardedInductionSentenceRoute
open FoundationCompactNumericListedDirectGuardedInductionSentenceRouteCompleteness
open FoundationCompactNumericListedDirectInductionPAAxiomRuleCheckCompleteness
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds
open FoundationCompactNumericListedDirectFormulaTokenWeightBounds

/-- The genuine input scale of a PA leaf before any direct-route value or trace
is generated. -/
def compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : FoundationCompactPAAxiomCertificate.PAAxiomCertificate) : Nat :=
  compactAdditiveValueWeight Gamma +
    compactAdditiveValueWeight (compactSentenceTokens candidate) +
    compactAdditiveValueWeight
      (compactPAAxiomCertificateTokens certificate)

theorem compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_gamma_le
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : FoundationCompactPAAxiomCertificate.PAAxiomCertificate) :
    compactAdditiveValueWeight Gamma ≤
      compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
        Gamma candidate certificate := by
  unfold compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
  omega

theorem compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_candidate_le
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : FoundationCompactPAAxiomCertificate.PAAxiomCertificate) :
    compactAdditiveValueWeight (compactSentenceTokens candidate) ≤
      compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
        Gamma candidate certificate := by
  unfold compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
  omega

theorem compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_certificate_le
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : FoundationCompactPAAxiomCertificate.PAAxiomCertificate) :
    compactAdditiveValueWeight
        (compactPAAxiomCertificateTokens certificate) ≤
      compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
        Gamma candidate certificate := by
  unfold compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
  omega

theorem compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_body_le
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactAdditiveValueWeight (compactArithmeticFormulaTokens body) ≤
      compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
        Gamma candidate (.induction body) := by
  have hsuffix : compactArithmeticFormulaTokens body <:+
      compactPAAxiomCertificateTokens (.induction body) := by
    simp [compactPAAxiomCertificateTokens]
  exact (compactAdditiveValueWeight_suffix_le hsuffix).trans
    (compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_certificate_le
      Gamma candidate (.induction body))

theorem compactAxmRuleCheck_induction_accept_implies_sentence_eq
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    (PAAxiomCertificate.induction body).sentence = candidate := by
  have hand : compactPAAxiomSentenceEqTokens
      (compactPAAxiomCertificateTokens (.induction body),
        compactSentenceTokens candidate) = true ∧
      tokenFormulaMem (compactSentenceTokens candidate) Gamma = true := by
    simpa only [compactAxmRuleCheck, Bool.and_eq_true] using haccept
  exact
    (compactPAAxiomSentenceEqTokens_canonical (.induction body) candidate).mp
      hand.1

theorem compactAxmRuleCheck_induction_accept_implies_depth_le_codeLength
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    (succInd body).fvSup ≤
      (binaryFormulaCode
        (Rewriting.emb candidate :
          LO.FirstOrder.ArithmeticProposition)).length := by
  have hsentence :=
    compactAxmRuleCheck_induction_accept_implies_sentence_eq
      Gamma candidate body haccept
  have htrace := inductionSentenceGuardTrace_complete body candidate hsentence
  have hdepth :=
    (inductionSentenceGuardTrace_result_eq_true_iff body candidate).mp htrace
  simpa [candidateSentenceCodeLength] using hdepth

theorem compactAxmRuleCheck_induction_accept_implies_depth_le_originalWeight
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    (succInd body).fvSup ≤
      2 * compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
        Gamma candidate (.induction body) := by
  have hdepth :=
    compactAxmRuleCheck_induction_accept_implies_depth_le_codeLength
      Gamma candidate body haccept
  have hcode :
      (binaryFormulaCode
        (Rewriting.emb candidate :
          LO.FirstOrder.ArithmeticProposition)).length =
        2 * compactAdditiveTokenWeight
          (compactSentenceTokens candidate) := by
    symm
    simpa [compactSentenceTokens] using
      compactArithmeticFormulaTokens_tokenWeight_le
        (Rewriting.emb candidate :
          LO.FirstOrder.ArithmeticProposition)
  rw [hcode] at hdepth
  have htoken := compactAdditiveTokenWeight_le_valueWeight_natList
    (compactSentenceTokens candidate)
  have hcandidate :=
    compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_candidate_le
      Gamma candidate (.induction body)
  omega

private theorem compactAdditiveValueWeight_tokenFormulaOr_le
    (left right : List Nat) :
    compactAdditiveValueWeight (tokenFormulaOr left right) ≤
      compactAdditiveValueWeight left +
        compactAdditiveValueWeight right + 6 := by
  have hleft := compactAdditiveValueWeight_list_append_le [5] left
  have hright := compactAdditiveValueWeight_list_append_le
    ([5] ++ left) right
  have htag : compactAdditiveValueWeight [5] = 6 := by
    decide
  change compactAdditiveValueWeight ([5] ++ left ++ right) ≤ _
  rw [htag] at hleft
  omega

private theorem compactAdditiveValueWeight_tokenFormulaAll_le
    (body : List Nat) :
    compactAdditiveValueWeight (tokenFormulaAll body) ≤
      compactAdditiveValueWeight body + 6 := by
  have h := compactAdditiveValueWeight_list_append_le [6] body
  have htag : compactAdditiveValueWeight [6] = 6 := by
    decide
  change compactAdditiveValueWeight ([6] ++ body) ≤ _
  rw [htag] at h
  omega

private theorem compactAdditiveValueWeight_replicate_zero_le
    (count : Nat) :
    compactAdditiveValueWeight (List.replicate count 0) ≤
      2 * count + 1 := by
  have hlist := compactAdditiveValueWeight_list_le
    (List.replicate count 0) 1 (by
      intro value hvalue
      simp only [List.mem_replicate] at hvalue
      rcases hvalue with ⟨_, rfl⟩
      simp)
  simp only [List.length_replicate, Nat.mul_one] at hlist
  have hsize := nat_size_le_self_formulaTokenWeight count
  omega

private theorem compactFormulaTransformCanonicalExactResult_output_weight_le
    (mode binderArity : Nat) (witness tokens output : List Nat)
    (hmode : mode ≤ 3)
    (hresult : compactExactFormulaTransformResult
      (compactFormulaTransformResult
        (mode, witness) (binderArity, tokens)) = some output) :
    compactAdditiveValueWeight output ≤
      compactFormulaTransformCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight witness) := by
  have hrunResult : compactFormulaTransformResult
      (mode, witness) (binderArity, tokens) = some (output, []) :=
    compactExactFormulaTransformResult_eq_some_iff.mp hresult
  have hfinalOutput :
      (compactFormulaTransformRun
        (mode, witness) (binderArity, tokens)).2 = output :=
    (compactFormulaTransformStateOutput_eq_some_iff.mp hrunResult).2
  have hbound := compactFormulaTransformCanonicalStateOutput_weight_le
    mode binderArity witness tokens hmode
  change compactAdditiveValueWeight
      (compactFormulaTransformRun
        (mode, witness) (binderArity, tokens)).2 ≤ _ at hbound
  rw [hfinalOutput] at hbound
  exact hbound

private theorem compactGuardedInductionExactTransform_mode_le_three_weight_le
    (mode binderArity : Nat) (witness tokens : List Nat)
    (hmode : mode ≤ 3) :
    compactAdditiveValueWeight
        (compactGuardedInductionExactTransform
          mode witness binderArity tokens) ≤
      compactFormulaTransformCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens)
        (compactAdditiveValueWeight witness) := by
  unfold compactGuardedInductionExactTransform
  cases hresult : compactExactFormulaTransformResult
      (compactFormulaTransformResult
        (mode, witness) (binderArity, tokens)) with
  | none =>
      simp only [Option.getD_none]
      unfold compactFormulaTransformCanonicalOutputWeightBound
        compactFormulaTransformOutputWeightBound
      simp [compactAdditiveValueWeight_list]
  | some output =>
      simp only [Option.getD_some]
      exact compactFormulaTransformCanonicalExactResult_output_weight_le
        mode binderArity witness tokens output hmode hresult

private theorem compactGuardedInductionExactTransform_fvSup_weight_le
    (binderArity : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactGuardedInductionExactTransform
          4 witness binderArity tokens) ≤
      compactFormulaFvSupCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens) := by
  unfold compactGuardedInductionExactTransform
  cases hresult : compactExactFormulaTransformResult
      (compactFormulaTransformResult
        (4, witness) (binderArity, tokens)) with
  | none =>
      simp only [Option.getD_none]
      unfold compactFormulaFvSupCanonicalOutputWeightBound
        compactFormulaFvSupOutputWeightBound
      simp [compactAdditiveValueWeight_list]
  | some output =>
      simp only [Option.getD_some]
      exact
        compactFormulaTransformCanonicalExactResult_fvSup_output_weight_le
          binderArity witness tokens output hresult

private theorem compactFormulaTransformCanonicalStateTrace_fvSup_source_weight_le
    (binderArity : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (4, witness)
          (compactSyntaxRunFuelBound tokens)
          (compactFormulaTransformInitialState binderArity tokens)) ≤
      compactFormulaFvSupTransformCanonicalSourceTraceWeightBound
        (compactAdditiveValueWeight tokens) binderArity := by
  have htrace := compactFormulaTransformCanonicalStateTrace_fvSup_weight_le
    binderArity witness tokens
  have houtput := compactFormulaTransformCanonicalRun_fvSup_output_weight_le
    binderArity witness tokens
  unfold compactFormulaFvSupTransformCanonicalSourceTraceWeightBound
    compactFormulaFvSupTransformCanonicalTraceWeightBound at htrace ⊢
  exact htrace.trans
    (compactFormulaFvSupTransformTraceWeightBound_mono
      (Nat.le_refl _) houtput (Nat.le_refl _) (Nat.le_refl _))

private theorem compactGuardedInductionExactTransform_fixitr_weight_le
    (binderArity : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactGuardedInductionExactTransform
          5 witness binderArity tokens) ≤
      compactFormulaFixitrCanonicalOutputWeightBound
        (compactAdditiveValueWeight tokens) binderArity := by
  unfold compactGuardedInductionExactTransform
  cases hresult : compactExactFormulaTransformResult
      (compactFormulaTransformResult
        (5, witness) (binderArity, tokens)) with
  | none =>
      simp only [Option.getD_none]
      unfold compactFormulaFixitrCanonicalOutputWeightBound
        compactFormulaFixitrOutputWeightBound
        compactFormulaFixitrEmissionWeightBound
      simp [compactAdditiveValueWeight_list]
  | some output =>
      simp only [Option.getD_some]
      exact
        compactFormulaTransformExactResult_fixitr_output_source_weight_le
          binderArity witness tokens output hresult

private def compactFormulaFixitrTransformCanonicalSourceTraceWeightBound
    (streamWeight binderArity : Nat) : Nat :=
  compactFormulaFixitrTransformCanonicalTraceWeightBound
    streamWeight
    (compactFormulaFixitrCanonicalOutputWeightBound
      streamWeight binderArity)
    binderArity

private theorem
    compactFormulaFixitrTransformCanonicalSourceTraceWeightBound_mono
    {streamLeft streamRight binderLeft binderRight : Nat}
    (hstream : streamLeft ≤ streamRight)
    (hbinder : binderLeft ≤ binderRight) :
    compactFormulaFixitrTransformCanonicalSourceTraceWeightBound
        streamLeft binderLeft ≤
      compactFormulaFixitrTransformCanonicalSourceTraceWeightBound
        streamRight binderRight := by
  unfold compactFormulaFixitrTransformCanonicalSourceTraceWeightBound
    compactFormulaFixitrTransformCanonicalTraceWeightBound
  exact compactFormulaFixitrTransformTraceWeightBound_mono
    hstream
    (compactFormulaFixitrCanonicalOutputWeightBound_mono
      hstream hbinder)
    hbinder
    (compactNumericCertificateParserFuelWeightBound_mono hstream)

private theorem compactFormulaTransformCanonicalStateTrace_fixitr_source_weight_le
    (binderArity : Nat) (witness tokens : List Nat) :
    compactAdditiveValueWeight
        (compactFormulaTransformStateTrace
          (5, witness)
          (compactSyntaxRunFuelBound tokens)
          (compactFormulaTransformInitialState binderArity tokens)) ≤
      compactFormulaFixitrTransformCanonicalSourceTraceWeightBound
        (compactAdditiveValueWeight tokens) binderArity := by
  have htrace := compactFormulaTransformCanonicalStateTrace_fixitr_weight_le
    binderArity witness tokens
  have houtput :=
    compactFormulaTransformCanonicalRun_fixitr_output_source_weight_le
      binderArity witness tokens
  unfold compactFormulaFixitrTransformCanonicalSourceTraceWeightBound
    compactFormulaFixitrTransformCanonicalTraceWeightBound at htrace ⊢
  exact htrace.trans
    (compactFormulaFixitrTransformTraceWeightBound_mono
      (Nat.le_refl _) houtput (Nat.le_refl _) (Nat.le_refl _))

private theorem
    compactFormulaFvSupTransformCanonicalSourceTraceWeightBound_mono
    {streamLeft streamRight binderLeft binderRight : Nat}
    (hstream : streamLeft ≤ streamRight)
    (hbinder : binderLeft ≤ binderRight) :
    compactFormulaFvSupTransformCanonicalSourceTraceWeightBound
        streamLeft binderLeft ≤
      compactFormulaFvSupTransformCanonicalSourceTraceWeightBound
        streamRight binderRight := by
  unfold compactFormulaFvSupTransformCanonicalSourceTraceWeightBound
    compactFormulaFvSupTransformCanonicalTraceWeightBound
  exact compactFormulaFvSupTransformTraceWeightBound_mono
    hstream
    (compactFormulaFvSupCanonicalOutputWeightBound_mono hstream)
    hbinder
    (compactNumericCertificateParserFuelWeightBound_mono hstream)

/-- One uniform polynomial enlargement sufficient for any one guarded-route
constructor, formula transform, or complete transform trace whose current
inputs are bounded by `weight`. -/
def compactGuardedInductionLocalWeightEnvelope (weight : Nat) : Nat :=
  weight + 128 +
    (3 * weight + 12) +
    compactFormulaTransformCanonicalOutputWeightBound weight weight +
    compactFormulaTransformCanonicalTraceWeightBound weight weight 1 +
    compactFormulaFvSupCanonicalOutputWeightBound weight +
    compactFormulaFvSupTransformCanonicalSourceTraceWeightBound weight 1 +
    compactFormulaFixitrCanonicalOutputWeightBound weight 1 +
    compactFormulaFixitrTransformCanonicalSourceTraceWeightBound weight 1

theorem compactGuardedInductionLocalWeightEnvelope_mono
    {left right : Nat} (hweight : left ≤ right) :
    compactGuardedInductionLocalWeightEnvelope left ≤
      compactGuardedInductionLocalWeightEnvelope right := by
  have houtput := compactFormulaTransformCanonicalOutputWeightBound_mono
    hweight hweight
  have htrace := compactFormulaTransformCanonicalTraceWeightBound_mono
    hweight hweight (Nat.le_refl 1)
  have hfvOutput :=
    compactFormulaFvSupCanonicalOutputWeightBound_mono hweight
  have hfvTrace :=
    compactFormulaFvSupTransformCanonicalSourceTraceWeightBound_mono
      hweight (Nat.le_refl 1)
  have hfixOutput := compactFormulaFixitrCanonicalOutputWeightBound_mono
    hweight (Nat.le_refl 1)
  have hfixTrace :=
    compactFormulaFixitrTransformCanonicalSourceTraceWeightBound_mono
      hweight (Nat.le_refl 1)
  unfold compactGuardedInductionLocalWeightEnvelope
  omega

theorem compactGuardedInductionLocalWeightEnvelope_inflationary
    (weight : Nat) :
    weight ≤ compactGuardedInductionLocalWeightEnvelope weight := by
  unfold compactGuardedInductionLocalWeightEnvelope
  omega

def compactGuardedInductionInitialWeightEnvelope (weight : Nat) : Nat :=
  4 * weight + 128

theorem compactGuardedInductionInitialWeightEnvelope_mono
    {left right : Nat} (hweight : left <= right) :
    compactGuardedInductionInitialWeightEnvelope left <=
      compactGuardedInductionInitialWeightEnvelope right := by
  unfold compactGuardedInductionInitialWeightEnvelope
  omega

def compactGuardedInductionRouteWeightStage
    (weight stage : Nat) : Nat :=
  ((compactGuardedInductionLocalWeightEnvelope)^[stage])
    (compactGuardedInductionInitialWeightEnvelope weight)

def compactGuardedInductionRouteWeightEnvelope (weight : Nat) : Nat :=
  compactGuardedInductionRouteWeightStage weight 10

@[simp] theorem compactGuardedInductionRouteWeightStage_zero
    (weight : Nat) :
    compactGuardedInductionRouteWeightStage weight 0 =
      compactGuardedInductionInitialWeightEnvelope weight := by
  rfl

theorem compactGuardedInductionRouteWeightStage_succ
    (weight stage : Nat) :
    compactGuardedInductionRouteWeightStage weight (stage + 1) =
      compactGuardedInductionLocalWeightEnvelope
        (compactGuardedInductionRouteWeightStage weight stage) := by
  unfold compactGuardedInductionRouteWeightStage
  rw [Function.iterate_succ_apply']

theorem compactGuardedInductionRouteWeightStage_le_succ
    (weight stage : Nat) :
    compactGuardedInductionRouteWeightStage weight stage ≤
      compactGuardedInductionRouteWeightStage weight (stage + 1) := by
  rw [compactGuardedInductionRouteWeightStage_succ]
  exact compactGuardedInductionLocalWeightEnvelope_inflationary _

theorem compactGuardedInductionRouteWeightStage_mono_index
    (weight : Nat) {left right : Nat} (hstage : left ≤ right) :
    compactGuardedInductionRouteWeightStage weight left ≤
      compactGuardedInductionRouteWeightStage weight right := by
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hstage
  clear hstage
  induction steps with
  | zero => simp
  | succ steps ih =>
      exact ih.trans (by
        simpa [Nat.add_assoc] using
          compactGuardedInductionRouteWeightStage_le_succ
            weight (left + steps))

theorem compactGuardedInductionRouteWeightStage_mono_weight
    {left right : Nat} (hweight : left <= right) (stage : Nat) :
    compactGuardedInductionRouteWeightStage left stage <=
      compactGuardedInductionRouteWeightStage right stage := by
  induction stage with
  | zero =>
      simpa only [compactGuardedInductionRouteWeightStage_zero] using
        compactGuardedInductionInitialWeightEnvelope_mono hweight
  | succ stage inductionHypothesis =>
      simpa only [Nat.succ_eq_add_one,
        compactGuardedInductionRouteWeightStage_succ] using
        compactGuardedInductionLocalWeightEnvelope_mono inductionHypothesis

theorem compactGuardedInductionRouteWeightEnvelope_mono
    {left right : Nat} (hweight : left <= right) :
    compactGuardedInductionRouteWeightEnvelope left <=
      compactGuardedInductionRouteWeightEnvelope right := by
  exact compactGuardedInductionRouteWeightStage_mono_weight hweight 10

/-- Forty is the exact number of canonical chunks in an induction PA-rule
leaf: 25 values, 12 traces, and the three original extra inputs. -/
def compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial
    (weight : Nat) : Nat :=
  40 * compactGuardedInductionRouteWeightEnvelope weight

theorem
    compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial_mono
    {left right : Nat} (hweight : left <= right) :
    compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial left <=
      compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial right := by
  unfold compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial
  exact Nat.mul_le_mul_left 40
    (compactGuardedInductionRouteWeightEnvelope_mono hweight)

private theorem compactGuardedInduction_mode_le_three_output_le_localEnvelope
    (mode binderArity bound : Nat) (witness tokens : List Nat)
    (hmode : mode ≤ 3)
    (htokens : compactAdditiveValueWeight tokens ≤ bound)
    (hwitness : compactAdditiveValueWeight witness ≤ bound) :
    compactAdditiveValueWeight
        (compactGuardedInductionExactTransform
          mode witness binderArity tokens) ≤
      compactGuardedInductionLocalWeightEnvelope bound := by
  have hraw :=
    compactGuardedInductionExactTransform_mode_le_three_weight_le
      mode binderArity witness tokens hmode
  have hpublic := hraw.trans
    (compactFormulaTransformCanonicalOutputWeightBound_mono
      htokens hwitness)
  unfold compactGuardedInductionLocalWeightEnvelope
  omega

private theorem compactGuardedInduction_mode_le_three_trace_le_localEnvelope
    (mode binderArity bound : Nat) (witness tokens : List Nat)
    (hmode : mode ≤ 3) (hbinder : binderArity ≤ 1)
    (htokens : compactAdditiveValueWeight tokens ≤ bound)
    (hwitness : compactAdditiveValueWeight witness ≤ bound) :
    compactAdditiveValueWeight
        (compactGuardedInductionTransformStates
          mode witness binderArity tokens) ≤
      compactGuardedInductionLocalWeightEnvelope bound := by
  have hraw := compactFormulaTransformCanonicalStateTrace_weight_le
    mode binderArity witness tokens hmode
  have hpublic := hraw.trans
    (compactFormulaTransformCanonicalTraceWeightBound_mono
      htokens hwitness hbinder)
  unfold compactGuardedInductionTransformStates
  exact hpublic.trans (by
    unfold compactGuardedInductionLocalWeightEnvelope
    omega)

private theorem compactGuardedInduction_fvSup_output_le_localEnvelope
    (binderArity bound : Nat) (witness tokens : List Nat)
    (htokens : compactAdditiveValueWeight tokens ≤ bound) :
    compactAdditiveValueWeight
        (compactGuardedInductionExactTransform
          4 witness binderArity tokens) ≤
      compactGuardedInductionLocalWeightEnvelope bound := by
  have hraw := compactGuardedInductionExactTransform_fvSup_weight_le
    binderArity witness tokens
  have hpublic := hraw.trans
    (compactFormulaFvSupCanonicalOutputWeightBound_mono htokens)
  unfold compactGuardedInductionLocalWeightEnvelope
  omega

private theorem compactGuardedInduction_fvSup_trace_le_localEnvelope
    (binderArity bound : Nat) (witness tokens : List Nat)
    (hbinder : binderArity ≤ 1)
    (htokens : compactAdditiveValueWeight tokens ≤ bound) :
    compactAdditiveValueWeight
        (compactGuardedInductionTransformStates
          4 witness binderArity tokens) ≤
      compactGuardedInductionLocalWeightEnvelope bound := by
  have hraw :=
    compactFormulaTransformCanonicalStateTrace_fvSup_source_weight_le
      binderArity witness tokens
  have hpublic := hraw.trans
    (compactFormulaFvSupTransformCanonicalSourceTraceWeightBound_mono
      htokens hbinder)
  unfold compactGuardedInductionTransformStates
  exact hpublic.trans (by
    unfold compactGuardedInductionLocalWeightEnvelope
    omega)

private theorem compactGuardedInduction_fixitr_output_le_localEnvelope
    (binderArity bound : Nat) (witness tokens : List Nat)
    (hbinder : binderArity ≤ 1)
    (htokens : compactAdditiveValueWeight tokens ≤ bound) :
    compactAdditiveValueWeight
        (compactGuardedInductionExactTransform
          5 witness binderArity tokens) ≤
      compactGuardedInductionLocalWeightEnvelope bound := by
  have hraw := compactGuardedInductionExactTransform_fixitr_weight_le
    binderArity witness tokens
  have hpublic := hraw.trans
    (compactFormulaFixitrCanonicalOutputWeightBound_mono
      htokens hbinder)
  unfold compactGuardedInductionLocalWeightEnvelope
  omega

private theorem compactGuardedInduction_fixitr_trace_le_localEnvelope
    (binderArity bound : Nat) (witness tokens : List Nat)
    (hbinder : binderArity ≤ 1)
    (htokens : compactAdditiveValueWeight tokens ≤ bound) :
    compactAdditiveValueWeight
        (compactGuardedInductionTransformStates
          5 witness binderArity tokens) ≤
      compactGuardedInductionLocalWeightEnvelope bound := by
  have hraw :=
    compactFormulaTransformCanonicalStateTrace_fixitr_source_weight_le
      binderArity witness tokens
  have hpublic := hraw.trans
    (compactFormulaFixitrTransformCanonicalSourceTraceWeightBound_mono
      htokens hbinder)
  unfold compactGuardedInductionTransformStates
  exact hpublic.trans (by
    unfold compactGuardedInductionLocalWeightEnvelope
    omega)

private theorem compactGuardedInduction_or_le_localEnvelope
    (bound : Nat) (left right : List Nat)
    (hleft : compactAdditiveValueWeight left ≤ bound)
    (hright : compactAdditiveValueWeight right ≤ bound) :
    compactAdditiveValueWeight (tokenFormulaOr left right) ≤
      compactGuardedInductionLocalWeightEnvelope bound := by
  have hraw := compactAdditiveValueWeight_tokenFormulaOr_le left right
  unfold compactGuardedInductionLocalWeightEnvelope
  omega

private theorem compactGuardedInduction_all_le_localEnvelope
    (bound : Nat) (body : List Nat)
    (hbody : compactAdditiveValueWeight body ≤ bound) :
    compactAdditiveValueWeight (tokenFormulaAll body) ≤
      compactGuardedInductionLocalWeightEnvelope bound := by
  have hraw := compactAdditiveValueWeight_tokenFormulaAll_le body
  unfold compactGuardedInductionLocalWeightEnvelope
  omega

private theorem compactAdditiveTokenWeight_flatten_le_of_mem
    (chunks : List (List Nat)) (bound : Nat)
    (hbound : ∀ chunk ∈ chunks,
      compactAdditiveTokenWeight chunk ≤ bound) :
    compactAdditiveTokenWeight chunks.flatten ≤
      chunks.length * bound := by
  induction chunks with
  | nil => simp
  | cons chunk chunks ih =>
      have hhead := hbound chunk (by simp)
      have htail := ih (by
        intro value hvalue
        exact hbound value (by simp [hvalue]))
      rw [List.flatten_cons, compactAdditiveTokenWeight_append,
        List.length_cons, Nat.succ_mul]
      omega

private def compactGuardedInductionOpenSubstitutedFormula
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : LO.FirstOrder.ArithmeticTerm Nat) :
    LO.FirstOrder.ArithmeticProposition :=
  Rewriting.app (Rew.subst ![witness]) (Rewriting.shift body)

private theorem compactGuardedInductionExactTransform_fixitr
    (witness : List Nat) (binderArity : Nat) (tokens : List Nat) :
    compactGuardedInductionExactTransform 5 witness binderArity tokens =
      (compactFormulaFixitrExact binderArity
        (witness.length, tokens)).getD [] := by
  rfl

private theorem compactGuardedInductionBase_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionBase (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens (compactSuccIndBaseFormula body) := by
  change (compactFormulaSubstitutionExact 1
    (compactSuccIndZeroWitnessTokens,
      compactArithmeticFormulaTokens body)).getD [] = _
  rw [compactSuccIndZeroWitnessTokens_canonical,
    compactFormulaSubstitutionExact_canonical]
  rfl

private theorem compactGuardedInductionNegatedBase_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionNegatedBase
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens
        (∼compactSuccIndBaseFormula body) := by
  rw [compactGuardedInductionNegatedBase_eq,
    compactGuardedInductionBase_canonical]
  change (compactFormulaNegationExact 0
    (compactArithmeticFormulaTokens
      (compactSuccIndBaseFormula body))).getD [] = _
  rw [compactFormulaNegationExact_canonical]
  rfl

private theorem compactGuardedInductionOpenZeroShifted_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionOpenZeroShifted
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens (Rewriting.shift body) := by
  rw [compactGuardedInductionOpenZeroShifted_eq]
  change (compactFormulaShiftExact 1
    (compactArithmeticFormulaTokens body)).getD [] = _
  rw [compactFormulaShiftExact_canonical]
  rfl

private theorem compactGuardedInductionOpenZeroSubstituted_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionOpenZeroSubstituted
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens
        (compactGuardedInductionOpenSubstitutedFormula
          body succIndOpenZeroWitness) := by
  rw [compactGuardedInductionOpenZeroSubstituted_eq,
    compactGuardedInductionOpenZeroShifted_canonical]
  change (compactFormulaSubstitutionExact 1
    (compactSuccIndOpenZeroWitnessTokens,
      compactArithmeticFormulaTokens (Rewriting.shift body))).getD [] = _
  rw [compactSuccIndOpenZeroWitnessTokens_canonical,
    compactFormulaSubstitutionExact_canonical]
  rfl

private theorem compactGuardedInductionStepZero_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionStepZero
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens
        (compactSuccIndStepZeroFormula body) := by
  have hnormalized := congrArg
    (fun result : Option (List Nat) => result.getD [])
    (compactSuccIndOpenZeroTokens_canonical body)
  have htokens : compactArithmeticFormulaTokens
      (Rewriting.app (Rew.fixitr (L := ℒₒᵣ) 0 1)
        (compactGuardedInductionOpenSubstitutedFormula
          body succIndOpenZeroWitness)) =
      compactArithmeticFormulaTokens
        (compactSuccIndStepZeroFormula body) := by
    simpa [compactSuccIndOpenZeroTokens,
      compactSuccIndOpenSubstitutionTokens,
      compactGuardedInductionOpenSubstitutedFormula] using hnormalized
  rw [compactGuardedInductionStepZero_eq,
    compactGuardedInductionOpenZeroSubstituted_canonical]
  change (compactFormulaFixitrExact 0
    (1, compactArithmeticFormulaTokens
      (compactGuardedInductionOpenSubstitutedFormula
        body succIndOpenZeroWitness))).getD [] = _
  rw [compactFormulaFixitrExact_canonical]
  exact htokens

private theorem compactGuardedInductionOpenSuccessorShifted_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionOpenSuccessorShifted
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens (Rewriting.shift body) := by
  rw [compactGuardedInductionOpenSuccessorShifted_eq]
  change (compactFormulaShiftExact 1
    (compactArithmeticFormulaTokens body)).getD [] = _
  rw [compactFormulaShiftExact_canonical]
  rfl

private theorem compactGuardedInductionOpenSuccessorSubstituted_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionOpenSuccessorSubstituted
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens
        (compactGuardedInductionOpenSubstitutedFormula
          body succIndOpenSuccessorWitness) := by
  rw [compactGuardedInductionOpenSuccessorSubstituted_eq,
    compactGuardedInductionOpenSuccessorShifted_canonical]
  change (compactFormulaSubstitutionExact 1
    (compactSuccIndOpenSuccessorWitnessTokens,
      compactArithmeticFormulaTokens (Rewriting.shift body))).getD [] = _
  rw [compactSuccIndOpenSuccessorWitnessTokens_canonical,
    compactFormulaSubstitutionExact_canonical]
  rfl

private theorem compactGuardedInductionStepSuccessor_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionStepSuccessor
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens
        (compactSuccIndStepSuccessorFormula body) := by
  have hnormalized := congrArg
    (fun result : Option (List Nat) => result.getD [])
    (compactSuccIndOpenSuccessorTokens_canonical body)
  have htokens : compactArithmeticFormulaTokens
      (Rewriting.app (Rew.fixitr (L := ℒₒᵣ) 0 1)
        (compactGuardedInductionOpenSubstitutedFormula
          body succIndOpenSuccessorWitness)) =
      compactArithmeticFormulaTokens
        (compactSuccIndStepSuccessorFormula body) := by
    simpa [compactSuccIndOpenSuccessorTokens,
      compactSuccIndOpenSubstitutionTokens,
      compactGuardedInductionOpenSubstitutedFormula] using hnormalized
  rw [compactGuardedInductionStepSuccessor_eq,
    compactGuardedInductionOpenSuccessorSubstituted_canonical]
  change (compactFormulaFixitrExact 0
    (1, compactArithmeticFormulaTokens
      (compactGuardedInductionOpenSubstitutedFormula
        body succIndOpenSuccessorWitness))).getD [] = _
  rw [compactFormulaFixitrExact_canonical]
  exact htokens

private theorem compactGuardedInductionNegatedStepZero_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionNegatedStepZero
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens
        (∼compactSuccIndStepZeroFormula body) := by
  rw [compactGuardedInductionNegatedStepZero_eq,
    compactGuardedInductionStepZero_canonical]
  change (compactFormulaNegationExact 1
    (compactArithmeticFormulaTokens
      (compactSuccIndStepZeroFormula body))).getD [] = _
  rw [compactFormulaNegationExact_canonical]
  rfl

private theorem compactGuardedInductionStepDisjunction_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionStepDisjunction
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens
        ((∼compactSuccIndStepZeroFormula body) ⋎
          compactSuccIndStepSuccessorFormula body) := by
  rw [compactGuardedInductionStepDisjunction_eq,
    compactGuardedInductionNegatedStepZero_canonical,
    compactGuardedInductionStepSuccessor_canonical]
  rfl

private theorem compactGuardedInductionQuantifiedStep_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionQuantifiedStep
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens
        (∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
          compactSuccIndStepSuccessorFormula body)) := by
  rw [compactGuardedInductionQuantifiedStep_eq,
    compactGuardedInductionStepDisjunction_canonical]
  rfl

private theorem compactGuardedInductionNegatedQuantifiedStep_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionNegatedQuantifiedStep
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens
        (∼(∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
          compactSuccIndStepSuccessorFormula body))) := by
  rw [compactGuardedInductionNegatedQuantifiedStep_eq,
    compactGuardedInductionQuantifiedStep_canonical]
  change (compactFormulaNegationExact 0
    (compactArithmeticFormulaTokens
      (∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
        compactSuccIndStepSuccessorFormula body)))).getD [] = _
  rw [compactFormulaNegationExact_canonical]
  rfl

private theorem compactGuardedInductionQuantifiedFinal_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionQuantifiedFinal
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens
        (∀⁰ compactSuccIndStepZeroFormula body) := by
  rw [compactGuardedInductionQuantifiedFinal_eq,
    compactGuardedInductionStepZero_canonical]
  rfl

private theorem compactGuardedInductionInnerDisjunction_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionInnerDisjunction
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens
        ((∼(∀⁰ ((∼compactSuccIndStepZeroFormula body) ⋎
          compactSuccIndStepSuccessorFormula body))) ⋎
          (∀⁰ compactSuccIndStepZeroFormula body)) := by
  rw [compactGuardedInductionInnerDisjunction_eq,
    compactGuardedInductionNegatedQuantifiedStep_canonical,
    compactGuardedInductionQuantifiedFinal_canonical]
  rfl

theorem compactGuardedInductionSentence_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionSentence
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens (succInd body) := by
  rw [compactGuardedInductionSentence_eq,
    compactGuardedInductionNegatedBase_canonical,
    compactGuardedInductionInnerDisjunction_canonical]
  change compactArithmeticFormulaTokens
      (compactSuccIndConstructedFormula body) =
    compactArithmeticFormulaTokens (succInd body)
  rw [compactSuccIndConstructedFormula_eq_succInd]

theorem compactGuardedInductionFvarList_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionFvarList
        (compactArithmeticFormulaTokens body) =
      (succInd body).fvarList := by
  rw [compactGuardedInductionFvarList_eq,
    compactGuardedInductionSentence_canonical]
  change (compactExactFormulaTransformResult
    (compactFormulaFvListTokenTransform 0
      (compactArithmeticFormulaTokens (succInd body)))).getD [] = _
  rw [show compactFormulaFvListTokenTransform 0
      (compactArithmeticFormulaTokens (succInd body)) =
        some ((succInd body).fvarList, []) by
    simpa using compactFormulaFvListTokenTransform_canonical_append
      (succInd body) []]
  rfl

theorem compactGuardedInductionDepth_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionDepth
        (compactArithmeticFormulaTokens body) =
      (succInd body).fvSup := by
  rw [compactGuardedInductionDepth_eq,
    compactGuardedInductionFvarList_canonical,
    listFvSup_formula_eq_fvSup]

theorem compactGuardedInductionFixed_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionFixed
        (compactArithmeticFormulaTokens body) =
      compactArithmeticFormulaTokens
        (Rewriting.app
          (Rew.fixitr (L := ℒₒᵣ) 0 (succInd body).fvSup)
          (succInd body)) := by
  rw [compactGuardedInductionFixed_eq,
    compactGuardedInductionExactTransform_fixitr,
    compactGuardedInductionSentence_canonical]
  rw [compactGuardedInductionDepthCapture_length,
    compactGuardedInductionDepth_canonical,
    compactFormulaFixitrExact_canonical]
  rfl

theorem compactGuardedInductionGenerated_canonical
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    compactGuardedInductionGenerated
        (compactArithmeticFormulaTokens body) =
      compactSentenceTokens
        (PAAxiomCertificate.induction body).sentence := by
  rw [compactGuardedInductionGenerated_eq,
    compactGuardedInductionDepth_canonical,
    compactGuardedInductionFixed_canonical]
  calc
    compactAllClosureTokens (succInd body).fvSup
        (compactArithmeticFormulaTokens
          (Rewriting.app
            (Rew.fixitr (L := ℒₒᵣ) 0 (succInd body).fvSup)
            (succInd body))) =
      compactArithmeticFormulaTokens
        (compactInductionClosureFormula body) := by
          simpa [compactInductionClosureFormula] using
            compactAllClosureTokens_canonical
              (Rewriting.app
                (Rew.fixitr (L := ℒₒᵣ) 0 (succInd body).fvSup)
                (succInd body))
    _ = compactSentenceTokens
        (PAAxiomCertificate.induction body).sentence := by
      rw [compactInductionClosureFormula_eq_sentence]
      rfl

@[simp] theorem compactGuardedInductionExecutableData_generated
    (bodyTokens : List Nat) :
    (compactGuardedInductionExecutableData bodyTokens).generated =
      compactGuardedInductionGenerated bodyTokens := by
  rfl

theorem compactGuardedInductionExecutableData_generated_eq_candidate_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    (compactGuardedInductionExecutableData
      (compactArithmeticFormulaTokens body)).generated =
        compactSentenceTokens candidate := by
  rw [compactGuardedInductionExecutableData_generated]
  have hcanonical := compactGuardedInductionGenerated_canonical body
  have hsentence :=
    compactAxmRuleCheck_induction_accept_implies_sentence_eq
      Gamma candidate body haccept
  exact hcanonical.trans (congrArg compactSentenceTokens hsentence)

theorem compactGuardedInductionExecutableData_depth_le_originalWeight_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    (compactGuardedInductionExecutableData
      (compactArithmeticFormulaTokens body)).depth ≤
        2 * compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
          Gamma candidate (.induction body) := by
  change compactGuardedInductionDepth
      (compactArithmeticFormulaTokens body) ≤ _
  rw [compactGuardedInductionDepth_canonical]
  exact compactAxmRuleCheck_induction_accept_implies_depth_le_originalWeight
    Gamma candidate body haccept


private def compactGuardedInductionAcceptedData
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    CompactGuardedInductionExecutableData :=
  compactGuardedInductionExecutableData
    (compactArithmeticFormulaTokens body)

private def compactGuardedInductionAcceptedWeight
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Nat :=
  compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
    Gamma candidate (.induction body)

private structure CompactGuardedInductionAcceptedStageZeroBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Prop where
  bodyBound : compactAdditiveValueWeight
      (compactArithmeticFormulaTokens body) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 0
  zeroWitness : compactAdditiveValueWeight
      compactGuardedInductionZeroWitness ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 0
  openZeroWitness : compactAdditiveValueWeight
      compactGuardedInductionOpenZeroWitness ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 0
  openSuccessorWitness : compactAdditiveValueWeight
      compactGuardedInductionOpenSuccessorWitness ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 0
  captureOne : compactAdditiveValueWeight
      compactGuardedInductionCaptureOne ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 0
  empty : compactAdditiveValueWeight
      compactGuardedInductionEmpty ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 0
  depthCapture : compactAdditiveValueWeight
      (compactGuardedInductionDepthCapture
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 0
  generated : compactAdditiveValueWeight
      (compactGuardedInductionGenerated
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 0

private theorem compactGuardedInductionAcceptedStageZeroBounds_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    CompactGuardedInductionAcceptedStageZeroBounds
      Gamma candidate body := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let candidateTokens := compactSentenceTokens candidate
  let weight := compactGuardedInductionAcceptedWeight Gamma candidate body
  have hbodyWeight : compactAdditiveValueWeight bodyTokens ≤ weight := by
    simpa [bodyTokens, weight,
      compactGuardedInductionAcceptedWeight] using
      compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_body_le
        Gamma candidate body
  have hcandidateWeight :
      compactAdditiveValueWeight candidateTokens ≤ weight := by
    simpa [candidateTokens, weight,
      compactGuardedInductionAcceptedWeight] using
      compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_candidate_le
        Gamma candidate (.induction body)
  have hdepthWeight : compactGuardedInductionDepth bodyTokens ≤
      2 * weight := by
    rw [show compactGuardedInductionDepth bodyTokens =
        (succInd body).fvSup by
      simpa [bodyTokens] using compactGuardedInductionDepth_canonical body]
    simpa [weight, compactGuardedInductionAcceptedWeight] using
      compactAxmRuleCheck_induction_accept_implies_depth_le_originalWeight
        Gamma candidate body haccept
  have hgeneratedEq : compactGuardedInductionGenerated bodyTokens =
      candidateTokens := by
    simpa [bodyTokens, candidateTokens] using
      compactGuardedInductionExecutableData_generated_eq_candidate_of_accept
        Gamma candidate body haccept
  have hgeneratedWeight :
      compactAdditiveValueWeight
        (compactGuardedInductionGenerated bodyTokens) ≤ weight := by
    rw [hgeneratedEq]
    exact hcandidateWeight
  have hconstants :
      compactAdditiveValueWeight compactGuardedInductionZeroWitness ≤ 128 ∧
      compactAdditiveValueWeight compactGuardedInductionOpenZeroWitness ≤ 128 ∧
      compactAdditiveValueWeight
          compactGuardedInductionOpenSuccessorWitness ≤ 128 ∧
      compactAdditiveValueWeight compactGuardedInductionCaptureOne ≤ 128 ∧
      compactAdditiveValueWeight compactGuardedInductionEmpty ≤ 128 := by
    decide
  rcases hconstants with
    ⟨hzeroConst, hopenZeroConst, hopenSuccessorConst,
      hcaptureConst, hemptyConst⟩
  have hweight0 : weight ≤
      compactGuardedInductionRouteWeightStage weight 0 := by
    rw [compactGuardedInductionRouteWeightStage_zero]
    unfold compactGuardedInductionInitialWeightEnvelope
    omega
  have hconst0 : 128 ≤
      compactGuardedInductionRouteWeightStage weight 0 := by
    rw [compactGuardedInductionRouteWeightStage_zero]
    unfold compactGuardedInductionInitialWeightEnvelope
    omega
  have hdepthCaptureRaw :
      compactAdditiveValueWeight
          (compactGuardedInductionDepthCapture bodyTokens) ≤
        2 * compactGuardedInductionDepth bodyTokens + 1 := by
    unfold compactGuardedInductionDepthCapture
    exact compactAdditiveValueWeight_replicate_zero_le _
  have hdepthCapture0 :
      compactAdditiveValueWeight
          (compactGuardedInductionDepthCapture bodyTokens) ≤
        compactGuardedInductionRouteWeightStage weight 0 := by
    rw [compactGuardedInductionRouteWeightStage_zero]
    unfold compactGuardedInductionInitialWeightEnvelope
    omega
  exact
    { bodyBound := hbodyWeight.trans hweight0
      zeroWitness := hzeroConst.trans hconst0
      openZeroWitness := hopenZeroConst.trans hconst0
      openSuccessorWitness := hopenSuccessorConst.trans hconst0
      captureOne := hcaptureConst.trans hconst0
      empty := hemptyConst.trans hconst0
      depthCapture := hdepthCapture0
      generated := hgeneratedWeight.trans hweight0 }

private structure CompactGuardedInductionAcceptedStageOneBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Prop where
  base : compactAdditiveValueWeight
      (compactGuardedInductionBase (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 1
  openZeroShifted : compactAdditiveValueWeight
      (compactGuardedInductionOpenZeroShifted
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 1
  openSuccessorShifted : compactAdditiveValueWeight
      (compactGuardedInductionOpenSuccessorShifted
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 1
  baseTrace : compactAdditiveValueWeight
      (compactGuardedInductionTransformStates
        2 compactGuardedInductionZeroWitness 1
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 1
  shiftTrace : compactAdditiveValueWeight
      (compactGuardedInductionTransformStates
        1 compactGuardedInductionEmpty 1
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 1

private theorem compactGuardedInductionAcceptedStageOneBounds_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    CompactGuardedInductionAcceptedStageOneBounds
      Gamma candidate body := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let weight := compactGuardedInductionAcceptedWeight Gamma candidate body
  have stage0 := compactGuardedInductionAcceptedStageZeroBounds_of_accept
    Gamma candidate body haccept
  have hnext : compactGuardedInductionLocalWeightEnvelope
      (compactGuardedInductionRouteWeightStage weight 0) =
      compactGuardedInductionRouteWeightStage weight 1 := by
    symm
    simpa using compactGuardedInductionRouteWeightStage_succ weight 0
  refine
    { base := ?_
      openZeroShifted := ?_
      openSuccessorShifted := ?_
      baseTrace := ?_
      shiftTrace := ?_ }
  · calc
      compactAdditiveValueWeight (compactGuardedInductionBase bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 0) := by
        exact compactGuardedInduction_mode_le_three_output_le_localEnvelope
          2 1 (compactGuardedInductionRouteWeightStage weight 0)
          compactGuardedInductionZeroWitness bodyTokens (by omega)
          stage0.bodyBound stage0.zeroWitness
      _ = compactGuardedInductionRouteWeightStage weight 1 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionOpenZeroShifted bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 0) := by
        exact compactGuardedInduction_mode_le_three_output_le_localEnvelope
          1 1 (compactGuardedInductionRouteWeightStage weight 0)
          compactGuardedInductionEmpty bodyTokens (by omega)
          stage0.bodyBound stage0.empty
      _ = compactGuardedInductionRouteWeightStage weight 1 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionOpenSuccessorShifted bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 0) := by
        exact compactGuardedInduction_mode_le_three_output_le_localEnvelope
          1 1 (compactGuardedInductionRouteWeightStage weight 0)
          compactGuardedInductionEmpty bodyTokens (by omega)
          stage0.bodyBound stage0.empty
      _ = compactGuardedInductionRouteWeightStage weight 1 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionTransformStates
            2 compactGuardedInductionZeroWitness 1 bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 0) := by
        exact compactGuardedInduction_mode_le_three_trace_le_localEnvelope
          2 1 (compactGuardedInductionRouteWeightStage weight 0)
          compactGuardedInductionZeroWitness bodyTokens
          (by omega) (by omega) stage0.bodyBound stage0.zeroWitness
      _ = compactGuardedInductionRouteWeightStage weight 1 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionTransformStates
            1 compactGuardedInductionEmpty 1 bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 0) := by
        exact compactGuardedInduction_mode_le_three_trace_le_localEnvelope
          1 1 (compactGuardedInductionRouteWeightStage weight 0)
          compactGuardedInductionEmpty bodyTokens
          (by omega) (by omega) stage0.bodyBound stage0.empty
      _ = compactGuardedInductionRouteWeightStage weight 1 := hnext

private structure CompactGuardedInductionAcceptedStageTwoBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Prop where
  negatedBase : compactAdditiveValueWeight
      (compactGuardedInductionNegatedBase
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 2
  openZeroSubstituted : compactAdditiveValueWeight
      (compactGuardedInductionOpenZeroSubstituted
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 2
  openSuccessorSubstituted : compactAdditiveValueWeight
      (compactGuardedInductionOpenSuccessorSubstituted
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 2
  negatedBaseTrace : compactAdditiveValueWeight
      (compactGuardedInductionTransformStates 3
        compactGuardedInductionEmpty 0
        (compactGuardedInductionBase
          (compactArithmeticFormulaTokens body))) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 2
  openZeroSubstitutionTrace : compactAdditiveValueWeight
      (compactGuardedInductionTransformStates 2
        compactGuardedInductionOpenZeroWitness 1
        (compactGuardedInductionOpenZeroShifted
          (compactArithmeticFormulaTokens body))) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 2
  openSuccessorSubstitutionTrace : compactAdditiveValueWeight
      (compactGuardedInductionTransformStates 2
        compactGuardedInductionOpenSuccessorWitness 1
        (compactGuardedInductionOpenSuccessorShifted
          (compactArithmeticFormulaTokens body))) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 2

private theorem compactGuardedInductionAcceptedStageTwoBounds_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    CompactGuardedInductionAcceptedStageTwoBounds
      Gamma candidate body := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let weight := compactGuardedInductionAcceptedWeight Gamma candidate body
  have stage0 := compactGuardedInductionAcceptedStageZeroBounds_of_accept
    Gamma candidate body haccept
  have stage1 := compactGuardedInductionAcceptedStageOneBounds_of_accept
    Gamma candidate body haccept
  have hstage01 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 0 ≤ 1)
  have hempty1 := stage0.empty.trans hstage01
  have hopenZero1 := stage0.openZeroWitness.trans hstage01
  have hopenSuccessor1 := stage0.openSuccessorWitness.trans hstage01
  have hnext : compactGuardedInductionLocalWeightEnvelope
      (compactGuardedInductionRouteWeightStage weight 1) =
      compactGuardedInductionRouteWeightStage weight 2 := by
    symm
    simpa using compactGuardedInductionRouteWeightStage_succ weight 1
  refine
    { negatedBase := ?_
      openZeroSubstituted := ?_
      openSuccessorSubstituted := ?_
      negatedBaseTrace := ?_
      openZeroSubstitutionTrace := ?_
      openSuccessorSubstitutionTrace := ?_ }
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionNegatedBase bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 1) := by
        exact compactGuardedInduction_mode_le_three_output_le_localEnvelope
          3 0 (compactGuardedInductionRouteWeightStage weight 1)
          compactGuardedInductionEmpty
          (compactGuardedInductionBase bodyTokens) (by omega)
          stage1.base hempty1
      _ = compactGuardedInductionRouteWeightStage weight 2 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionOpenZeroSubstituted bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 1) := by
        exact compactGuardedInduction_mode_le_three_output_le_localEnvelope
          2 1 (compactGuardedInductionRouteWeightStage weight 1)
          compactGuardedInductionOpenZeroWitness
          (compactGuardedInductionOpenZeroShifted bodyTokens) (by omega)
          stage1.openZeroShifted hopenZero1
      _ = compactGuardedInductionRouteWeightStage weight 2 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionOpenSuccessorSubstituted bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 1) := by
        exact compactGuardedInduction_mode_le_three_output_le_localEnvelope
          2 1 (compactGuardedInductionRouteWeightStage weight 1)
          compactGuardedInductionOpenSuccessorWitness
          (compactGuardedInductionOpenSuccessorShifted bodyTokens) (by omega)
          stage1.openSuccessorShifted hopenSuccessor1
      _ = compactGuardedInductionRouteWeightStage weight 2 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionTransformStates 3
            compactGuardedInductionEmpty 0
            (compactGuardedInductionBase bodyTokens)) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 1) := by
        exact compactGuardedInduction_mode_le_three_trace_le_localEnvelope
          3 0 (compactGuardedInductionRouteWeightStage weight 1)
          compactGuardedInductionEmpty
          (compactGuardedInductionBase bodyTokens)
          (by omega) (by omega) stage1.base hempty1
      _ = compactGuardedInductionRouteWeightStage weight 2 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionTransformStates 2
            compactGuardedInductionOpenZeroWitness 1
            (compactGuardedInductionOpenZeroShifted bodyTokens)) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 1) := by
        exact compactGuardedInduction_mode_le_three_trace_le_localEnvelope
          2 1 (compactGuardedInductionRouteWeightStage weight 1)
          compactGuardedInductionOpenZeroWitness
          (compactGuardedInductionOpenZeroShifted bodyTokens)
          (by omega) (by omega) stage1.openZeroShifted hopenZero1
      _ = compactGuardedInductionRouteWeightStage weight 2 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionTransformStates 2
            compactGuardedInductionOpenSuccessorWitness 1
            (compactGuardedInductionOpenSuccessorShifted bodyTokens)) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 1) := by
        exact compactGuardedInduction_mode_le_three_trace_le_localEnvelope
          2 1 (compactGuardedInductionRouteWeightStage weight 1)
          compactGuardedInductionOpenSuccessorWitness
          (compactGuardedInductionOpenSuccessorShifted bodyTokens)
          (by omega) (by omega) stage1.openSuccessorShifted hopenSuccessor1
      _ = compactGuardedInductionRouteWeightStage weight 2 := hnext

private structure CompactGuardedInductionAcceptedStageThreeBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Prop where
  stepZero : compactAdditiveValueWeight
      (compactGuardedInductionStepZero
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 3
  stepSuccessor : compactAdditiveValueWeight
      (compactGuardedInductionStepSuccessor
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 3
  stepZeroTrace : compactAdditiveValueWeight
      (compactGuardedInductionTransformStates 5
        compactGuardedInductionCaptureOne 0
        (compactGuardedInductionOpenZeroSubstituted
          (compactArithmeticFormulaTokens body))) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 3
  stepSuccessorTrace : compactAdditiveValueWeight
      (compactGuardedInductionTransformStates 5
        compactGuardedInductionCaptureOne 0
        (compactGuardedInductionOpenSuccessorSubstituted
          (compactArithmeticFormulaTokens body))) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 3

private theorem compactGuardedInductionAcceptedStageThreeBounds_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    CompactGuardedInductionAcceptedStageThreeBounds
      Gamma candidate body := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let weight := compactGuardedInductionAcceptedWeight Gamma candidate body
  have stage2 := compactGuardedInductionAcceptedStageTwoBounds_of_accept
    Gamma candidate body haccept
  have hnext : compactGuardedInductionLocalWeightEnvelope
      (compactGuardedInductionRouteWeightStage weight 2) =
      compactGuardedInductionRouteWeightStage weight 3 := by
    symm
    simpa using compactGuardedInductionRouteWeightStage_succ weight 2
  refine
    { stepZero := ?_
      stepSuccessor := ?_
      stepZeroTrace := ?_
      stepSuccessorTrace := ?_ }
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionStepZero bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 2) := by
        exact compactGuardedInduction_fixitr_output_le_localEnvelope
          0 (compactGuardedInductionRouteWeightStage weight 2)
          compactGuardedInductionCaptureOne
          (compactGuardedInductionOpenZeroSubstituted bodyTokens)
          (by omega) stage2.openZeroSubstituted
      _ = compactGuardedInductionRouteWeightStage weight 3 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionStepSuccessor bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 2) := by
        exact compactGuardedInduction_fixitr_output_le_localEnvelope
          0 (compactGuardedInductionRouteWeightStage weight 2)
          compactGuardedInductionCaptureOne
          (compactGuardedInductionOpenSuccessorSubstituted bodyTokens)
          (by omega) stage2.openSuccessorSubstituted
      _ = compactGuardedInductionRouteWeightStage weight 3 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionTransformStates 5
            compactGuardedInductionCaptureOne 0
            (compactGuardedInductionOpenZeroSubstituted bodyTokens)) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 2) := by
        exact compactGuardedInduction_fixitr_trace_le_localEnvelope
          0 (compactGuardedInductionRouteWeightStage weight 2)
          compactGuardedInductionCaptureOne
          (compactGuardedInductionOpenZeroSubstituted bodyTokens)
          (by omega) stage2.openZeroSubstituted
      _ = compactGuardedInductionRouteWeightStage weight 3 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionTransformStates 5
            compactGuardedInductionCaptureOne 0
            (compactGuardedInductionOpenSuccessorSubstituted bodyTokens)) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 2) := by
        exact compactGuardedInduction_fixitr_trace_le_localEnvelope
          0 (compactGuardedInductionRouteWeightStage weight 2)
          compactGuardedInductionCaptureOne
          (compactGuardedInductionOpenSuccessorSubstituted bodyTokens)
          (by omega) stage2.openSuccessorSubstituted
      _ = compactGuardedInductionRouteWeightStage weight 3 := hnext

private structure CompactGuardedInductionAcceptedStageFourBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Prop where
  negatedStepZero : compactAdditiveValueWeight
      (compactGuardedInductionNegatedStepZero
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 4
  negatedStepZeroTrace : compactAdditiveValueWeight
      (compactGuardedInductionTransformStates 3
        compactGuardedInductionEmpty 1
        (compactGuardedInductionStepZero
          (compactArithmeticFormulaTokens body))) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 4

private theorem compactGuardedInductionAcceptedStageFourBounds_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    CompactGuardedInductionAcceptedStageFourBounds
      Gamma candidate body := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let weight := compactGuardedInductionAcceptedWeight Gamma candidate body
  have stage0 := compactGuardedInductionAcceptedStageZeroBounds_of_accept
    Gamma candidate body haccept
  have stage3 := compactGuardedInductionAcceptedStageThreeBounds_of_accept
    Gamma candidate body haccept
  have hstage03 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 0 ≤ 3)
  have hempty3 := stage0.empty.trans hstage03
  have hnext : compactGuardedInductionLocalWeightEnvelope
      (compactGuardedInductionRouteWeightStage weight 3) =
      compactGuardedInductionRouteWeightStage weight 4 := by
    symm
    simpa using compactGuardedInductionRouteWeightStage_succ weight 3
  refine
    { negatedStepZero := ?_
      negatedStepZeroTrace := ?_ }
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionNegatedStepZero bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 3) := by
        exact compactGuardedInduction_mode_le_three_output_le_localEnvelope
          3 1 (compactGuardedInductionRouteWeightStage weight 3)
          compactGuardedInductionEmpty
          (compactGuardedInductionStepZero bodyTokens) (by omega)
          stage3.stepZero hempty3
      _ = compactGuardedInductionRouteWeightStage weight 4 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionTransformStates 3
            compactGuardedInductionEmpty 1
            (compactGuardedInductionStepZero bodyTokens)) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 3) := by
        exact compactGuardedInduction_mode_le_three_trace_le_localEnvelope
          3 1 (compactGuardedInductionRouteWeightStage weight 3)
          compactGuardedInductionEmpty
          (compactGuardedInductionStepZero bodyTokens)
          (by omega) (by omega) stage3.stepZero hempty3
      _ = compactGuardedInductionRouteWeightStage weight 4 := hnext

private structure CompactGuardedInductionAcceptedStageFiveBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Prop where
  stepDisjunction : compactAdditiveValueWeight
      (compactGuardedInductionStepDisjunction
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 5

private theorem compactGuardedInductionAcceptedStageFiveBounds_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    CompactGuardedInductionAcceptedStageFiveBounds
      Gamma candidate body := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let weight := compactGuardedInductionAcceptedWeight Gamma candidate body
  have stage3 := compactGuardedInductionAcceptedStageThreeBounds_of_accept
    Gamma candidate body haccept
  have stage4 := compactGuardedInductionAcceptedStageFourBounds_of_accept
    Gamma candidate body haccept
  have hstage34 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 3 ≤ 4)
  have hstepSuccessor4 := stage3.stepSuccessor.trans hstage34
  have hnext : compactGuardedInductionLocalWeightEnvelope
      (compactGuardedInductionRouteWeightStage weight 4) =
      compactGuardedInductionRouteWeightStage weight 5 := by
    symm
    simpa using compactGuardedInductionRouteWeightStage_succ weight 4
  refine { stepDisjunction := ?_ }
  calc
    compactAdditiveValueWeight
        (compactGuardedInductionStepDisjunction bodyTokens) ≤
        compactGuardedInductionLocalWeightEnvelope
          (compactGuardedInductionRouteWeightStage weight 4) := by
      exact compactGuardedInduction_or_le_localEnvelope
        (compactGuardedInductionRouteWeightStage weight 4)
        (compactGuardedInductionNegatedStepZero bodyTokens)
        (compactGuardedInductionStepSuccessor bodyTokens)
        stage4.negatedStepZero hstepSuccessor4
    _ = compactGuardedInductionRouteWeightStage weight 5 := hnext

private structure CompactGuardedInductionAcceptedStageSixBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Prop where
  quantifiedStep : compactAdditiveValueWeight
      (compactGuardedInductionQuantifiedStep
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 6
  quantifiedFinal : compactAdditiveValueWeight
      (compactGuardedInductionQuantifiedFinal
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 6

private theorem compactGuardedInductionAcceptedStageSixBounds_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    CompactGuardedInductionAcceptedStageSixBounds
      Gamma candidate body := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let weight := compactGuardedInductionAcceptedWeight Gamma candidate body
  have stage3 := compactGuardedInductionAcceptedStageThreeBounds_of_accept
    Gamma candidate body haccept
  have stage5 := compactGuardedInductionAcceptedStageFiveBounds_of_accept
    Gamma candidate body haccept
  have hstage35 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 3 ≤ 5)
  have hstepZero5 := stage3.stepZero.trans hstage35
  have hnext : compactGuardedInductionLocalWeightEnvelope
      (compactGuardedInductionRouteWeightStage weight 5) =
      compactGuardedInductionRouteWeightStage weight 6 := by
    symm
    simpa using compactGuardedInductionRouteWeightStage_succ weight 5
  refine
    { quantifiedStep := ?_
      quantifiedFinal := ?_ }
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionQuantifiedStep bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 5) := by
        exact compactGuardedInduction_all_le_localEnvelope
          (compactGuardedInductionRouteWeightStage weight 5)
          (compactGuardedInductionStepDisjunction bodyTokens)
          stage5.stepDisjunction
      _ = compactGuardedInductionRouteWeightStage weight 6 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionQuantifiedFinal bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 5) := by
        exact compactGuardedInduction_all_le_localEnvelope
          (compactGuardedInductionRouteWeightStage weight 5)
          (compactGuardedInductionStepZero bodyTokens) hstepZero5
      _ = compactGuardedInductionRouteWeightStage weight 6 := hnext

private structure CompactGuardedInductionAcceptedStageSevenBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Prop where
  negatedQuantifiedStep : compactAdditiveValueWeight
      (compactGuardedInductionNegatedQuantifiedStep
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 7
  negatedQuantifiedStepTrace : compactAdditiveValueWeight
      (compactGuardedInductionTransformStates 3
        compactGuardedInductionEmpty 0
        (compactGuardedInductionQuantifiedStep
          (compactArithmeticFormulaTokens body))) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 7

private theorem compactGuardedInductionAcceptedStageSevenBounds_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    CompactGuardedInductionAcceptedStageSevenBounds
      Gamma candidate body := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let weight := compactGuardedInductionAcceptedWeight Gamma candidate body
  have stage0 := compactGuardedInductionAcceptedStageZeroBounds_of_accept
    Gamma candidate body haccept
  have stage6 := compactGuardedInductionAcceptedStageSixBounds_of_accept
    Gamma candidate body haccept
  have hstage06 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 0 ≤ 6)
  have hempty6 := stage0.empty.trans hstage06
  have hnext : compactGuardedInductionLocalWeightEnvelope
      (compactGuardedInductionRouteWeightStage weight 6) =
      compactGuardedInductionRouteWeightStage weight 7 := by
    symm
    simpa using compactGuardedInductionRouteWeightStage_succ weight 6
  refine
    { negatedQuantifiedStep := ?_
      negatedQuantifiedStepTrace := ?_ }
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionNegatedQuantifiedStep bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 6) := by
        exact compactGuardedInduction_mode_le_three_output_le_localEnvelope
          3 0 (compactGuardedInductionRouteWeightStage weight 6)
          compactGuardedInductionEmpty
          (compactGuardedInductionQuantifiedStep bodyTokens) (by omega)
          stage6.quantifiedStep hempty6
      _ = compactGuardedInductionRouteWeightStage weight 7 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionTransformStates 3
            compactGuardedInductionEmpty 0
            (compactGuardedInductionQuantifiedStep bodyTokens)) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 6) := by
        exact compactGuardedInduction_mode_le_three_trace_le_localEnvelope
          3 0 (compactGuardedInductionRouteWeightStage weight 6)
          compactGuardedInductionEmpty
          (compactGuardedInductionQuantifiedStep bodyTokens)
          (by omega) (by omega) stage6.quantifiedStep hempty6
      _ = compactGuardedInductionRouteWeightStage weight 7 := hnext

private structure CompactGuardedInductionAcceptedStageEightBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Prop where
  innerDisjunction : compactAdditiveValueWeight
      (compactGuardedInductionInnerDisjunction
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 8

private theorem compactGuardedInductionAcceptedStageEightBounds_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    CompactGuardedInductionAcceptedStageEightBounds
      Gamma candidate body := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let weight := compactGuardedInductionAcceptedWeight Gamma candidate body
  have stage6 := compactGuardedInductionAcceptedStageSixBounds_of_accept
    Gamma candidate body haccept
  have stage7 := compactGuardedInductionAcceptedStageSevenBounds_of_accept
    Gamma candidate body haccept
  have hstage67 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 6 ≤ 7)
  have hquantifiedFinal7 := stage6.quantifiedFinal.trans hstage67
  have hnext : compactGuardedInductionLocalWeightEnvelope
      (compactGuardedInductionRouteWeightStage weight 7) =
      compactGuardedInductionRouteWeightStage weight 8 := by
    symm
    simpa using compactGuardedInductionRouteWeightStage_succ weight 7
  refine { innerDisjunction := ?_ }
  calc
    compactAdditiveValueWeight
        (compactGuardedInductionInnerDisjunction bodyTokens) ≤
        compactGuardedInductionLocalWeightEnvelope
          (compactGuardedInductionRouteWeightStage weight 7) := by
      exact compactGuardedInduction_or_le_localEnvelope
        (compactGuardedInductionRouteWeightStage weight 7)
        (compactGuardedInductionNegatedQuantifiedStep bodyTokens)
        (compactGuardedInductionQuantifiedFinal bodyTokens)
        stage7.negatedQuantifiedStep hquantifiedFinal7
    _ = compactGuardedInductionRouteWeightStage weight 8 := hnext

private structure CompactGuardedInductionAcceptedStageNineBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Prop where
  sentence : compactAdditiveValueWeight
      (compactGuardedInductionSentence
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 9

private theorem compactGuardedInductionAcceptedStageNineBounds_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    CompactGuardedInductionAcceptedStageNineBounds
      Gamma candidate body := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let weight := compactGuardedInductionAcceptedWeight Gamma candidate body
  have stage2 := compactGuardedInductionAcceptedStageTwoBounds_of_accept
    Gamma candidate body haccept
  have stage8 := compactGuardedInductionAcceptedStageEightBounds_of_accept
    Gamma candidate body haccept
  have hstage28 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 2 ≤ 8)
  have hnegatedBase8 := stage2.negatedBase.trans hstage28
  have hnext : compactGuardedInductionLocalWeightEnvelope
      (compactGuardedInductionRouteWeightStage weight 8) =
      compactGuardedInductionRouteWeightStage weight 9 := by
    symm
    simpa using compactGuardedInductionRouteWeightStage_succ weight 8
  refine { sentence := ?_ }
  calc
    compactAdditiveValueWeight
        (compactGuardedInductionSentence bodyTokens) ≤
        compactGuardedInductionLocalWeightEnvelope
          (compactGuardedInductionRouteWeightStage weight 8) := by
      exact compactGuardedInduction_or_le_localEnvelope
        (compactGuardedInductionRouteWeightStage weight 8)
        (compactGuardedInductionNegatedBase bodyTokens)
        (compactGuardedInductionInnerDisjunction bodyTokens)
        hnegatedBase8 stage8.innerDisjunction
    _ = compactGuardedInductionRouteWeightStage weight 9 := hnext

private structure CompactGuardedInductionAcceptedStageTenBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) : Prop where
  fvarList : compactAdditiveValueWeight
      (compactGuardedInductionFvarList
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 10
  fixed : compactAdditiveValueWeight
      (compactGuardedInductionFixed
        (compactArithmeticFormulaTokens body)) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 10
  fvarListTrace : compactAdditiveValueWeight
      (compactGuardedInductionTransformStates 4
        compactGuardedInductionEmpty 0
        (compactGuardedInductionSentence
          (compactArithmeticFormulaTokens body))) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 10
  closureTrace : compactAdditiveValueWeight
      (compactGuardedInductionTransformStates 5
        (compactGuardedInductionDepthCapture
          (compactArithmeticFormulaTokens body)) 0
        (compactGuardedInductionSentence
          (compactArithmeticFormulaTokens body))) ≤
    compactGuardedInductionRouteWeightStage
      (compactGuardedInductionAcceptedWeight Gamma candidate body) 10

private theorem compactGuardedInductionAcceptedStageTenBounds_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    CompactGuardedInductionAcceptedStageTenBounds
      Gamma candidate body := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let weight := compactGuardedInductionAcceptedWeight Gamma candidate body
  have stage9 := compactGuardedInductionAcceptedStageNineBounds_of_accept
    Gamma candidate body haccept
  have hnext : compactGuardedInductionLocalWeightEnvelope
      (compactGuardedInductionRouteWeightStage weight 9) =
      compactGuardedInductionRouteWeightStage weight 10 := by
    symm
    simpa using compactGuardedInductionRouteWeightStage_succ weight 9
  refine
    { fvarList := ?_
      fixed := ?_
      fvarListTrace := ?_
      closureTrace := ?_ }
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionFvarList bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 9) := by
        exact compactGuardedInduction_fvSup_output_le_localEnvelope
          0 (compactGuardedInductionRouteWeightStage weight 9)
          compactGuardedInductionEmpty
          (compactGuardedInductionSentence bodyTokens) stage9.sentence
      _ = compactGuardedInductionRouteWeightStage weight 10 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionFixed bodyTokens) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 9) := by
        exact compactGuardedInduction_fixitr_output_le_localEnvelope
          0 (compactGuardedInductionRouteWeightStage weight 9)
          (compactGuardedInductionDepthCapture bodyTokens)
          (compactGuardedInductionSentence bodyTokens)
          (by omega) stage9.sentence
      _ = compactGuardedInductionRouteWeightStage weight 10 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionTransformStates 4
            compactGuardedInductionEmpty 0
            (compactGuardedInductionSentence bodyTokens)) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 9) := by
        exact compactGuardedInduction_fvSup_trace_le_localEnvelope
          0 (compactGuardedInductionRouteWeightStage weight 9)
          compactGuardedInductionEmpty
          (compactGuardedInductionSentence bodyTokens)
          (by omega) stage9.sentence
      _ = compactGuardedInductionRouteWeightStage weight 10 := hnext
  · calc
      compactAdditiveValueWeight
          (compactGuardedInductionTransformStates 5
            (compactGuardedInductionDepthCapture bodyTokens) 0
            (compactGuardedInductionSentence bodyTokens)) ≤
          compactGuardedInductionLocalWeightEnvelope
            (compactGuardedInductionRouteWeightStage weight 9) := by
        exact compactGuardedInduction_fixitr_trace_le_localEnvelope
          0 (compactGuardedInductionRouteWeightStage weight 9)
          (compactGuardedInductionDepthCapture bodyTokens)
          (compactGuardedInductionSentence bodyTokens)
          (by omega) stage9.sentence
      _ = compactGuardedInductionRouteWeightStage weight 10 := hnext

private theorem compactGuardedInductionAcceptedRouteChunkWeight_le
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true)
    (chunk : List Nat)
    (hchunk : chunk ∈ compactGuardedInductionRouteChunks
      (compactGuardedInductionExecutableData
        (compactArithmeticFormulaTokens body))) :
    compactAdditiveTokenWeight chunk ≤
      compactGuardedInductionRouteWeightEnvelope
        (compactGuardedInductionAcceptedWeight Gamma candidate body) := by
  let weight := compactGuardedInductionAcceptedWeight Gamma candidate body
  have stage0 := compactGuardedInductionAcceptedStageZeroBounds_of_accept
    Gamma candidate body haccept
  have stage1 := compactGuardedInductionAcceptedStageOneBounds_of_accept
    Gamma candidate body haccept
  have stage2 := compactGuardedInductionAcceptedStageTwoBounds_of_accept
    Gamma candidate body haccept
  have stage3 := compactGuardedInductionAcceptedStageThreeBounds_of_accept
    Gamma candidate body haccept
  have stage4 := compactGuardedInductionAcceptedStageFourBounds_of_accept
    Gamma candidate body haccept
  have stage5 := compactGuardedInductionAcceptedStageFiveBounds_of_accept
    Gamma candidate body haccept
  have stage6 := compactGuardedInductionAcceptedStageSixBounds_of_accept
    Gamma candidate body haccept
  have stage7 := compactGuardedInductionAcceptedStageSevenBounds_of_accept
    Gamma candidate body haccept
  have stage8 := compactGuardedInductionAcceptedStageEightBounds_of_accept
    Gamma candidate body haccept
  have stage9 := compactGuardedInductionAcceptedStageNineBounds_of_accept
    Gamma candidate body haccept
  have stage10 := compactGuardedInductionAcceptedStageTenBounds_of_accept
    Gamma candidate body haccept
  have hstage0to10 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 0 ≤ 10)
  have hstage1to10 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 1 ≤ 10)
  have hstage2to10 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 2 ≤ 10)
  have hstage3to10 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 3 ≤ 10)
  have hstage4to10 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 4 ≤ 10)
  have hstage5to10 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 5 ≤ 10)
  have hstage6to10 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 6 ≤ 10)
  have hstage7to10 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 7 ≤ 10)
  have hstage8to10 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 8 ≤ 10)
  have hstage9to10 := compactGuardedInductionRouteWeightStage_mono_index
    weight (by omega : 9 ≤ 10)
  change compactAdditiveTokenWeight chunk ≤
    compactGuardedInductionRouteWeightStage weight 10
  simp only [compactGuardedInductionRouteChunks,
    compactGuardedInductionExecutableData, List.mem_cons,
    List.not_mem_nil, or_false] at hchunk
  rcases hchunk with
    (rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl | rfl | rfl |
     rfl)
  all_goals change compactAdditiveValueWeight _ ≤
    compactGuardedInductionRouteWeightStage weight 10
  · exact stage0.bodyBound.trans hstage0to10
  · exact stage0.zeroWitness.trans hstage0to10
  · exact stage0.openZeroWitness.trans hstage0to10
  · exact stage0.openSuccessorWitness.trans hstage0to10
  · exact stage0.captureOne.trans hstage0to10
  · exact stage0.empty.trans hstage0to10
  · exact stage1.base.trans hstage1to10
  · exact stage2.negatedBase.trans hstage2to10
  · exact stage1.openZeroShifted.trans hstage1to10
  · exact stage2.openZeroSubstituted.trans hstage2to10
  · exact stage3.stepZero.trans hstage3to10
  · exact stage1.openSuccessorShifted.trans hstage1to10
  · exact stage2.openSuccessorSubstituted.trans hstage2to10
  · exact stage3.stepSuccessor.trans hstage3to10
  · exact stage4.negatedStepZero.trans hstage4to10
  · exact stage5.stepDisjunction.trans hstage5to10
  · exact stage6.quantifiedStep.trans hstage6to10
  · exact stage7.negatedQuantifiedStep.trans hstage7to10
  · exact stage6.quantifiedFinal.trans hstage6to10
  · exact stage8.innerDisjunction.trans hstage8to10
  · exact stage9.sentence.trans hstage9to10
  · exact stage10.fvarList
  · exact stage0.depthCapture.trans hstage0to10
  · exact stage10.fixed
  · exact stage0.generated.trans hstage0to10
  · exact stage1.baseTrace.trans hstage1to10
  · exact stage2.negatedBaseTrace.trans hstage2to10
  · exact stage1.shiftTrace.trans hstage1to10
  · exact stage2.openZeroSubstitutionTrace.trans hstage2to10
  · exact stage3.stepZeroTrace.trans hstage3to10
  · exact stage1.shiftTrace.trans hstage1to10
  · exact stage2.openSuccessorSubstitutionTrace.trans hstage2to10
  · exact stage3.stepSuccessorTrace.trans hstage3to10
  · exact stage4.negatedStepZeroTrace.trans hstage4to10
  · exact stage7.negatedQuantifiedStepTrace.trans hstage7to10
  · exact stage10.fvarListTrace
  · exact stage10.closureTrace

/-- The complete deterministic induction-rule serialization is polynomial in
the three original PA-leaf inputs, provided the actual checker accepts it. -/
theorem compactNumericVerifierPAAxiomJointLeafRuleInputWeight_induction_le_of_accept
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens (.induction body))) = true) :
    compactNumericVerifierPAAxiomJointLeafRuleInputWeight
        Gamma candidate (.induction body) ≤
      compactNumericVerifierPAAxiomAcceptedInductionRuleWeightPolynomial
        (compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
          Gamma candidate (.induction body)) := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let candidateTokens := compactSentenceTokens candidate
  let weight := compactGuardedInductionAcceptedWeight Gamma candidate body
  let chunks := compactInductionPAAxiomRuleCheckChunks
    bodyTokens candidateTokens Gamma
  change compactAdditiveTokenWeight chunks.flatten ≤
    40 * compactGuardedInductionRouteWeightEnvelope weight
  have hweightRoute : weight ≤
      compactGuardedInductionRouteWeightEnvelope weight := by
    calc
      weight ≤ compactGuardedInductionRouteWeightStage weight 0 := by
        rw [compactGuardedInductionRouteWeightStage_zero]
        unfold compactGuardedInductionInitialWeightEnvelope
        omega
      _ ≤ compactGuardedInductionRouteWeightStage weight 10 :=
        compactGuardedInductionRouteWeightStage_mono_index
          weight (by omega)
      _ = compactGuardedInductionRouteWeightEnvelope weight := by
        rfl
  have hcertificate :
      compactAdditiveValueWeight (22 :: bodyTokens) ≤ weight := by
    simpa [bodyTokens, weight, compactGuardedInductionAcceptedWeight,
      compactPAAxiomCertificateTokens] using
      compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_certificate_le
        Gamma candidate (.induction body)
  have hcandidate :
      compactAdditiveValueWeight candidateTokens ≤ weight := by
    simpa [candidateTokens, weight,
      compactGuardedInductionAcceptedWeight] using
      compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_candidate_le
        Gamma candidate (.induction body)
  have hgamma : compactAdditiveValueWeight Gamma ≤ weight := by
    simpa [weight, compactGuardedInductionAcceptedWeight] using
      compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_gamma_le
        Gamma candidate (.induction body)
  have hchunk : ∀ chunk ∈ chunks,
      compactAdditiveTokenWeight chunk ≤
        compactGuardedInductionRouteWeightEnvelope weight := by
    intro chunk hmem
    simp only [chunks, compactInductionPAAxiomRuleCheckChunks,
      List.mem_append] at hmem
    rcases hmem with hroute | hextra
    · simpa [bodyTokens, weight,
        compactGuardedInductionAcceptedWeight] using
        compactGuardedInductionAcceptedRouteChunkWeight_le
          Gamma candidate body haccept chunk hroute
    · simp only [compactInductionPAAxiomRuleCheckExtraChunks,
        List.mem_cons, List.not_mem_nil, or_false] at hextra
      rcases hextra with (rfl | rfl | rfl)
      · change compactAdditiveValueWeight (22 :: bodyTokens) ≤ _
        exact hcertificate.trans hweightRoute
      · change compactAdditiveValueWeight candidateTokens ≤ _
        exact hcandidate.trans hweightRoute
      · change compactAdditiveValueWeight Gamma ≤ _
        exact hgamma.trans hweightRoute
  have htotal := compactAdditiveTokenWeight_flatten_le_of_mem
    chunks (compactGuardedInductionRouteWeightEnvelope weight) hchunk
  have hlength : chunks.length = 40 := by
    simp [chunks]
  rw [hlength] at htotal
  exact htotal

#print axioms compactAxmRuleCheck_induction_accept_implies_depth_le_originalWeight
#print axioms compactGuardedInductionSentence_canonical
#print axioms compactGuardedInductionDepth_canonical
#print axioms compactGuardedInductionGenerated_canonical
#print axioms
  compactGuardedInductionExecutableData_generated_eq_candidate_of_accept
#print axioms
  compactGuardedInductionExecutableData_depth_le_originalWeight_of_accept
#print axioms
  compactNumericVerifierPAAxiomJointLeafRuleInputWeight_induction_le_of_accept

end FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionRuleWeight
