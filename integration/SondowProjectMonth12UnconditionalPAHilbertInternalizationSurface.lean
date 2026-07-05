import integration.SondowProjectMonth11PAHilbertCheckerSurface
import integration.SondowProjectMonth9Month10ProofLengthGapFrontier
import integration.SondowProjectMonth9Month10Month11ExactProofGapHandoff

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10ProofLengthGapFrontier
open SondowProjectMonth11PAHilbertCheckerSurface
open SondowProjectMonth9Month10Month11ExactProofGapHandoff

/-- Proof-length-free Month 12 checker-search candidate.  This layer exposes
only the executable checker route: syntax, recognizer/interface soundness,
accepted-code exactness, finite enumeration, and the rejection extractor. -/
structure Month12ProofLengthFreeCheckerSearchCandidate
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 2 where
  formulaSyntax : Type
  syntaxCode : formulaSyntax → _root_.FormulaCode
  proofObject : Type
  proofObjectCode : proofObject → Nat
  proofObjectConclusion : proofObject → formulaSyntax
  recognizer : PAHilbertAxiomRecognizer
  inferenceRule : Type
  inferenceRuleName : inferenceRule → PAHilbertInferenceRule
  checker : PAHilbertChecker
  checker_recognizer_eq : checker.recognizer = recognizer
  semantics : PAHilbertDerivabilitySemantics
  recognizerExactness :
    PAHilbertAxiomRecognizerExactness checker.recognizer semantics
  canonicalInterface :
    PAHilbertCanonicalCheckerInterface checker semantics
  checkerSemantics :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data
  finiteEnumeration :
    InternalPudlakTheorem5CheckerFiniteEnumeration checkerSemantics
  rejectionExtractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checkerSemantics finiteEnumeration
  acceptedCodeExactness :
    ∀ formulaCode : _root_.FormulaCode, ∀ code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode checker formulaCode code →
        PAHilbertFormulaCodeDerivable semantics formulaCode

namespace Month12ProofLengthFreeCheckerSearchCandidate

def checkedMeasuredUpperProviderType
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data) :
    Type :=
  Month9Month10AbstractMeasuredUpperProvider
    (month9_month10_checkedProofCodeMeasured
      scale_data candidate.checkerSemantics.toProofCodeSemantics)

def smallCodeSearch
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data) :
    InternalPudlakTheorem5SmallCodeSearch
      scale_data candidate.checkerSemantics.toProofCodeSemantics :=
  candidate.finiteEnumeration.toSmallCodeSearch

def computableSearchExclusion
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      scale_data candidate.checkerSemantics.toProofCodeSemantics
      candidate.smallCodeSearch :=
  candidate.rejectionExtractor.toComputableFiniteSearchExclusion

def toCheckedSearchCollisionEndpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper_provider : candidate.checkedMeasuredUpperProviderType) :
    Month9Month10CheckedSearchCollisionEndpoint scale_data where
  sem := candidate.checkerSemantics.toProofCodeSemantics
  search := candidate.smallCodeSearch
  cert := candidate.computableSearchExclusion
  upper_provider := upper_provider

theorem accepted_decoded_code_to_formulaCode_derivable
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        candidate.checker formulaCode code) :
    PAHilbertFormulaCodeDerivable candidate.semantics formulaCode :=
  candidate.acceptedCodeExactness formulaCode code haccepted

end Month12ProofLengthFreeCheckerSearchCandidate

def checkedSearchUpperTail
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper_provider : candidate.checkedMeasuredUpperProviderType)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :=
  (candidate.toCheckedSearchCollisionEndpoint upper_provider)
    |>.toDirectEndpoint
    |>.toAbstractMeasuredEndpoint
    |>.upperTailOfRationality hrat

theorem computedCollisionN_eq_rejectionExtractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper_provider : candidate.checkedMeasuredUpperProviderType)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((candidate.toCheckedSearchCollisionEndpoint upper_provider).computedCollisionNOfRationality hrat) =
      candidate.rejectionExtractor.witness
        (checkedSearchUpperTail candidate upper_provider hrat).U
        (checkedSearchUpperTail candidate upper_provider hrat).polynomial
        (checkedSearchUpperTail candidate upper_provider hrat).upperN :=
  (candidate.toCheckedSearchCollisionEndpoint upper_provider).computedCollisionN_eq_certWitness hrat

theorem proof_length_free_candidate_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper_provider : candidate.checkedMeasuredUpperProviderType) :
    (candidate.toCheckedSearchCollisionEndpoint upper_provider).Audit ∧
      Nonempty (Month9Month10CheckedSearchCollisionEndpoint scale_data) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data candidate.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        ((candidate.toCheckedSearchCollisionEndpoint upper_provider).computedCollisionNOfRationality hrat) =
          candidate.rejectionExtractor.witness
            (checkedSearchUpperTail candidate upper_provider hrat).U
            (checkedSearchUpperTail candidate upper_provider hrat).polynomial
            (checkedSearchUpperTail candidate upper_provider hrat).upperN) :=
  ⟨(candidate.toCheckedSearchCollisionEndpoint upper_provider).audit,
    ⟨candidate.toCheckedSearchCollisionEndpoint upper_provider⟩,
    ⟨(candidate.toCheckedSearchCollisionEndpoint upper_provider).gap⟩,
    computedCollisionN_eq_rejectionExtractorWitness
      candidate upper_provider⟩

structure Month12ProofLengthTransportResidual
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data) : Prop where
  actualProofLengthMeasured_eq_minProofCodeSizeAt :
    ∀ n : Nat,
      actualProofLengthMeasured scale_data n =
        (candidate.checkerSemantics.minProofCodeSizeAt n : Real)

namespace Month12ProofLengthTransportResidual

theorem toCheckerProofLengthFamilyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data}
    (residual : Month12ProofLengthTransportResidual candidate) :
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness
      candidate.checkerSemantics where
  proof_length_eq_minProofCodeSizeAt := by
    intro n
    simpa [actualProofLengthMeasured]
      using residual.actualProofLengthMeasured_eq_minProofCodeSizeAt n

end Month12ProofLengthTransportResidual

/-- Month 12 checker-generated candidate.  The checker side is separated into
syntax, recognizer, proof objects, executable checking, finite search,
rejection, accepted-code soundness, minimum-code exactness, and the transport
to the project proof-length measurement. -/
structure Month12UnconditionalPAHilbertCheckerInternalizationCandidate
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 2 where
  formulaSyntax : Type
  syntaxCode : formulaSyntax → _root_.FormulaCode
  proofObject : Type
  proofObjectCode : proofObject → Nat
  proofObjectConclusion : proofObject → formulaSyntax
  recognizer : PAHilbertAxiomRecognizer
  inferenceRule : Type
  inferenceRuleName : inferenceRule → PAHilbertInferenceRule
  checker : PAHilbertChecker
  checker_recognizer_eq : checker.recognizer = recognizer
  semantics : PAHilbertDerivabilitySemantics
  recognizerExactness :
    PAHilbertAxiomRecognizerExactness checker.recognizer semantics
  canonicalInterface :
    PAHilbertCanonicalCheckerInterface checker semantics
  checkerSemantics :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data
  finiteEnumeration :
    InternalPudlakTheorem5CheckerFiniteEnumeration checkerSemantics
  rejectionExtractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checkerSemantics finiteEnumeration
  acceptedCodeExactness :
    ∀ formulaCode : _root_.FormulaCode, ∀ code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode checker formulaCode code →
        PAHilbertFormulaCodeDerivable semantics formulaCode
  minProofCodeSizeExactness :
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness checkerSemantics
  proofLengthTransport :
    ∀ n : Nat,
      actualProofLengthMeasured scale_data n =
        (checkerSemantics.minProofCodeSizeAt n : Real)

namespace Month12UnconditionalPAHilbertCheckerInternalizationCandidate

def proofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      candidate.checkerSemantics :=
  candidate.minProofCodeSizeExactness.toCheckerProofLengthExactness

def toCanonicalCalibratedExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore where
  checker := candidate.checker
  semantics := candidate.semantics
  recognizerExactness := candidate.recognizerExactness
  canonicalInterface := candidate.canonicalInterface
  scale_data := scale_data
  checkerSemantics := candidate.checkerSemantics
  finiteEnumeration := candidate.finiteEnumeration
  rejectionExtractor := candidate.rejectionExtractor
  proofLengthExactness := candidate.proofLengthExactness

def toComputableSearchProfile
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data) :
    InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
      scale_data :=
  candidate.rejectionExtractor.toCheckerComputableSearchProfile

def toComputableFiniteSearchNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  candidate.toComputableSearchProfile.toComputableFiniteSearchNoSmallCore
    candidate.proofLengthExactness

def toMonth9Month10ComputableNoSmallProofLengthFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data) :
    Month9Month10ComputableNoSmallProofLengthFrontier.{0} where
  core := candidate.toComputableFiniteSearchNoSmallCore

theorem accepted_decoded_code_to_formulaCode_derivable
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        candidate.checker formulaCode code) :
    PAHilbertFormulaCodeDerivable candidate.semantics formulaCode :=
  candidate.acceptedCodeExactness formulaCode code haccepted

theorem proofLengthTransport_of_familyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data)
    (n : Nat) :
    actualProofLengthMeasured scale_data n =
      (candidate.checkerSemantics.minProofCodeSizeAt n : Real) :=
  candidate.proofLengthTransport n

end Month12UnconditionalPAHilbertCheckerInternalizationCandidate

theorem checker_minProofCodeSize_to_actualProofLength
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data)
    (n : Nat) :
    actualProofLengthMeasured scale_data n =
      (candidate.checkerSemantics.minProofCodeSizeAt n : Real) :=
  candidate.proofLengthTransport n

def actualProofLengthGapConstructor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data) :
    ComputableSearchGapCertificate
      (actualProofLengthMeasured scale_data) :=
  actualProofLengthGapOfComputableFiniteSearchNoSmallCore
    candidate.toComputableFiniteSearchNoSmallCore

theorem actualProofLengthGapConstructor_witness_eq_core
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((actualProofLengthGapConstructor candidate)
        |>.gap_for_polynomial_upper U hU).witness N =
      (candidate.toComputableFiniteSearchNoSmallCore
        |>.computable_search_exclusion).witness U hU N :=
  rfl

theorem actualProofLengthGapConstructor_witness_eq_rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((actualProofLengthGapConstructor candidate)
        |>.gap_for_polynomial_upper U hU).witness N =
      candidate.rejectionExtractor.witness U hU N :=
  rfl

theorem actualProofLengthGapConstructor_strict_at_witness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    U (((actualProofLengthGapConstructor candidate)
        |>.gap_for_polynomial_upper U hU).witness N) <
      actualProofLengthMeasured scale_data
        (((actualProofLengthGapConstructor candidate)
          |>.gap_for_polynomial_upper U hU).witness N) :=
  ((actualProofLengthGapConstructor candidate)
    |>.gap_for_polynomial_upper U hU).strict_at_witness N

structure Month12CheckerGeneratedFinalDeliverables
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 2 where
  candidate :
    Month12UnconditionalPAHilbertCheckerInternalizationCandidate
      scale_data
  canonicalCore : PAHilbertCanonicalCalibratedExactnessCore
  computableNoSmallCore :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}
  proofLengthFrontier :
    Month9Month10ComputableNoSmallProofLengthFrontier.{0}
  actualProofLengthGap :
    ComputableSearchGapCertificate
      (actualProofLengthMeasured scale_data)
  minProofCodeSizeToActualProofLength :
    ∀ n : Nat,
      actualProofLengthMeasured scale_data n =
        (candidate.checkerSemantics.minProofCodeSizeAt n : Real)
  witnessEqRejectionExtractor :
    ∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
      ((actualProofLengthGap.gap_for_polynomial_upper U hU).witness N) =
        candidate.rejectionExtractor.witness U hU N

def finalDeliverablesAdapter
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data) :
    Month12CheckerGeneratedFinalDeliverables scale_data where
  candidate := candidate
  canonicalCore := candidate.toCanonicalCalibratedExactnessCore
  computableNoSmallCore := candidate.toComputableFiniteSearchNoSmallCore
  proofLengthFrontier :=
    candidate.toMonth9Month10ComputableNoSmallProofLengthFrontier
  actualProofLengthGap := actualProofLengthGapConstructor candidate
  minProofCodeSizeToActualProofLength :=
    checker_minProofCodeSize_to_actualProofLength candidate
  witnessEqRejectionExtractor := by
    intro U hU N
    exact actualProofLengthGapConstructor_witness_eq_rejectionExtractor
      candidate U hU N

structure Month12LegacyFinalEndpointResiduals
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop where
  proof_length_eq_scale :
    ∀ n : Nat,
      actualProofLengthMeasured scale_data n =
        scaleMeasured scale_data n
  time_bound_strict :
    ∀ {a b : Nat}, a < b →
      scale_data.time_constructible_bound a <
        scale_data.time_constructible_bound b
  exponent_ne_zero : scale_data.exponent ≠ 0

namespace Month12LegacyFinalEndpointResiduals

theorem scale_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (residuals : Month12LegacyFinalEndpointResiduals scale_data) :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b :=
  Month9Month10ActualProofLengthGapFrontier.scale_strict_of_timeConstructibleBound_strict
    residuals.time_bound_strict residuals.exponent_ne_zero

end Month12LegacyFinalEndpointResiduals

def toLegacyFinalThreeCertificateEndpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data)
    (residuals : Month12LegacyFinalEndpointResiduals scale_data) :
    ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data where
  scale_strict := residuals.scale_strict
  proof_length_gap := by
    change
      ComputableSearchGapCertificate
        (actualProofLengthMeasured scale_data)
    exact actualProofLengthGapConstructor candidate
  proof_length_eq_scale := by
    intro n
    simpa [actualProofLengthMeasured, scaleMeasured]
      using residuals.proof_length_eq_scale n

theorem month12_candidate_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} ∧
      Nonempty Month9Month10ComputableNoSmallProofLengthFrontier.{0} ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
      (∀ n : Nat,
        actualProofLengthMeasured scale_data n =
          (candidate.checkerSemantics.minProofCodeSizeAt n : Real)) := by
  exact
    ⟨⟨candidate.toCanonicalCalibratedExactnessCore⟩,
      ⟨candidate.toComputableFiniteSearchNoSmallCore⟩,
      ⟨candidate.toMonth9Month10ComputableNoSmallProofLengthFrontier⟩,
      ⟨actualProofLengthGapConstructor candidate⟩,
      checker_minProofCodeSize_to_actualProofLength candidate⟩

end SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface
end SondowMainCheckedCodeBridge
