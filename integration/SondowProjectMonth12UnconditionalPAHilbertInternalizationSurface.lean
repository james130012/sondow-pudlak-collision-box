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

theorem proof_length_free_candidate_computed_n_contradiction
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper_provider : candidate.checkedMeasuredUpperProviderType)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (candidate.toCheckedSearchCollisionEndpoint upper_provider)
    |>.computed_n_contradiction hrat

theorem proof_length_free_candidate_not_rational
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper_provider : candidate.checkedMeasuredUpperProviderType) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  (candidate.toCheckedSearchCollisionEndpoint upper_provider).not_rational

theorem proof_length_free_candidate_endpoint_closure
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
            (checkedSearchUpperTail candidate upper_provider hrat).upperN) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    proof_length_free_candidate_closure candidate upper_provider
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.1,
      hclosure.2.2.2,
      proof_length_free_candidate_computed_n_contradiction
        candidate upper_provider,
      proof_length_free_candidate_not_rational candidate upper_provider⟩

def lowerSearchWitnessOfUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data candidate.checkerSemantics.toProofCodeSemantics)) :
    InternalPudlakTheorem5ComputedLowerSearchWitness
      scale_data candidate.checkerSemantics.toProofCodeSemantics
      candidate.smallCodeSearch
      upper.U upper.polynomial upper.upperN :=
  candidate.computableSearchExclusion
    |>.computedLowerSearchWitness upper.U upper.polynomial upper.upperN

theorem lowerSearchWitnessOfUpper_n_eq_rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data candidate.checkerSemantics.toProofCodeSemantics)) :
    (lowerSearchWitnessOfUpper candidate upper).n =
      candidate.rejectionExtractor.witness
        upper.U upper.polynomial upper.upperN :=
  rfl

theorem lowerSearchWitnessOfUpper_K_eq_rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data candidate.checkerSemantics.toProofCodeSemantics)) :
    (lowerSearchWitnessOfUpper candidate upper).K =
      candidate.rejectionExtractor.cutoff
        upper.U upper.polynomial upper.upperN :=
  rfl

theorem lowerSearchWitnessOfUpper_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data candidate.checkerSemantics.toProofCodeSemantics)) :
    let w := lowerSearchWitnessOfUpper candidate upper
    w.n =
        candidate.rejectionExtractor.witness
          upper.U upper.polynomial upper.upperN ∧
      w.K =
        candidate.rejectionExtractor.cutoff
          upper.U upper.polynomial upper.upperN ∧
      upper.upperN ≤ w.n ∧
      upper.U w.n < (w.K : Real) ∧
      (∀ c : candidate.checkerSemantics.Code,
        c ∈ candidate.smallCodeSearch.candidates w.n w.K →
          ¬ candidate.checkerSemantics.checks c
            (scale_data.powerBoundRawCode w.n)) ∧
      (∀ c : candidate.checkerSemantics.Code,
        candidate.checkerSemantics.checks c
          (scale_data.powerBoundRawCode w.n) →
          upper.U w.n < (candidate.checkerSemantics.size c : Real)) ∧
      (candidate.checkerSemantics.toProofCodeSemantics.minProofCodeSize
          (scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) >
        upper.U w.n := by
  dsimp only
  refine ⟨
    lowerSearchWitnessOfUpper_n_eq_rejectionExtractor candidate upper,
    lowerSearchWitnessOfUpper_K_eq_rejectionExtractor candidate upper,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_⟩
  · exact (lowerSearchWitnessOfUpper candidate upper).n_ge
  · exact (lowerSearchWitnessOfUpper candidate upper).cutoff_gt
  · intro c hmem
    exact
      (lowerSearchWitnessOfUpper candidate upper).rejects_candidates c hmem
  · intro c hchecks
    exact (lowerSearchWitnessOfUpper candidate upper).no_small_at_n c hchecks
  · exact (lowerSearchWitnessOfUpper candidate upper).minProofCodeSize_gt

/-- Proof-length-free canonical search core.  Unlike
`PAHilbertCanonicalCalibratedExactnessCore`, this structure intentionally does
not carry proof-length exactness; it is the clean source of the checker-side
finite-search candidate and computed witness. -/
structure PAHilbertCanonicalSearchCore : Type 2 where
  checker : PAHilbertChecker
  semantics : PAHilbertDerivabilitySemantics
  recognizerExactness :
    PAHilbertAxiomRecognizerExactness checker.recognizer semantics
  canonicalInterface :
    PAHilbertCanonicalCheckerInterface checker semantics
  scale_data : InternalPudlakTheorem5ScaleData
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

namespace PAHilbertCanonicalSearchCore

def toProofLengthFreeMonth12Candidate
    (core : PAHilbertCanonicalSearchCore) :
    Month12ProofLengthFreeCheckerSearchCandidate core.scale_data where
  formulaSyntax := PAHilbertFormula
  syntaxCode := PAHilbertFormula.code
  proofObject := PAHilbertProofObject
  proofObjectCode := PAHilbertProofObject.code
  proofObjectConclusion := PAHilbertProofObject.conclusion
  recognizer := core.checker.recognizer
  inferenceRule := PAHilbertInferenceRule
  inferenceRuleName := id
  checker := core.checker
  checker_recognizer_eq := rfl
  semantics := core.semantics
  recognizerExactness := core.recognizerExactness
  canonicalInterface := core.canonicalInterface
  checkerSemantics := core.checkerSemantics
  finiteEnumeration := core.finiteEnumeration
  rejectionExtractor := core.rejectionExtractor
  acceptedCodeExactness := core.acceptedCodeExactness

theorem proofLengthFreeMonth12Candidate_closure
    (core : PAHilbertCanonicalSearchCore)
    (upper_provider :
      (core.toProofLengthFreeMonth12Candidate).checkedMeasuredUpperProviderType) :
    (core.toProofLengthFreeMonth12Candidate
      |>.toCheckedSearchCollisionEndpoint upper_provider).Audit ∧
      Nonempty (Month12ProofLengthFreeCheckerSearchCandidate core.scale_data) ∧
      Nonempty (Month9Month10CheckedSearchCollisionEndpoint core.scale_data) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            core.scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        ((core.toProofLengthFreeMonth12Candidate
          |>.toCheckedSearchCollisionEndpoint upper_provider)
            |>.computedCollisionNOfRationality hrat) =
          core.rejectionExtractor.witness
            (checkedSearchUpperTail
              core.toProofLengthFreeMonth12Candidate upper_provider hrat).U
            (checkedSearchUpperTail
              core.toProofLengthFreeMonth12Candidate upper_provider hrat).polynomial
            (checkedSearchUpperTail
              core.toProofLengthFreeMonth12Candidate upper_provider hrat).upperN) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    proof_length_free_candidate_endpoint_closure
      core.toProofLengthFreeMonth12Candidate upper_provider
  exact
    ⟨hclosure.1,
      ⟨core.toProofLengthFreeMonth12Candidate⟩,
      hclosure.2.1,
      hclosure.2.2.1,
      hclosure.2.2.2.1,
      hclosure.2.2.2.2.1,
      hclosure.2.2.2.2.2⟩

theorem lowerSearchWitnessOfUpper_closure
    (core : PAHilbertCanonicalSearchCore)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          core.scale_data core.checkerSemantics.toProofCodeSemantics)) :
    let w := lowerSearchWitnessOfUpper
      core.toProofLengthFreeMonth12Candidate upper
    w.n =
        core.rejectionExtractor.witness
          upper.U upper.polynomial upper.upperN ∧
      w.K =
        core.rejectionExtractor.cutoff
          upper.U upper.polynomial upper.upperN ∧
      upper.upperN ≤ w.n ∧
      upper.U w.n < (w.K : Real) ∧
      (∀ c : core.checkerSemantics.Code,
        c ∈
          core.toProofLengthFreeMonth12Candidate.smallCodeSearch.candidates
            w.n w.K →
          ¬ core.checkerSemantics.checks c
            (core.scale_data.powerBoundRawCode w.n)) ∧
      (∀ c : core.checkerSemantics.Code,
        core.checkerSemantics.checks c
          (core.scale_data.powerBoundRawCode w.n) →
          upper.U w.n < (core.checkerSemantics.size c : Real)) ∧
      (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
          (core.scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) >
        upper.U w.n :=
  SondowMainCheckedCodeBridge.SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.lowerSearchWitnessOfUpper_closure
    core.toProofLengthFreeMonth12Candidate upper

theorem proofLengthFree_not_rational
    (core : PAHilbertCanonicalSearchCore)
    (upper_provider :
      (core.toProofLengthFreeMonth12Candidate).checkedMeasuredUpperProviderType) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  proof_length_free_candidate_not_rational
    core.toProofLengthFreeMonth12Candidate upper_provider

end PAHilbertCanonicalSearchCore

/-- A canonical calibrated PA/Hilbert core already contains every
proof-length-free component required by the Month 12 checker-search candidate:
the executable checker, recognizer exactness, canonical checker interface,
finite enumeration, rejection extractor, and accepted-code soundness. -/
def PAHilbertCanonicalCalibratedExactnessCore.toCanonicalSearchCore
    (core : PAHilbertCanonicalCalibratedExactnessCore) :
    PAHilbertCanonicalSearchCore where
  checker := core.checker
  semantics := core.semantics
  recognizerExactness := core.recognizerExactness
  canonicalInterface := core.canonicalInterface
  scale_data := core.scale_data
  checkerSemantics := core.checkerSemantics
  finiteEnumeration := core.finiteEnumeration
  rejectionExtractor := core.rejectionExtractor
  acceptedCodeExactness :=
    core.accepted_decoded_code_to_formulaCode_derivable

/-- Compatibility adapter from the calibrated core.  Its statement still
mentions a calibrated core, hence axiom probes correctly see the proof-length
field carried by that core.  For a proof-length-free probe, use
`PAHilbertCanonicalSearchCore.toProofLengthFreeMonth12Candidate`. -/
def PAHilbertCanonicalCalibratedExactnessCore.toProofLengthFreeMonth12Candidate
    (core : PAHilbertCanonicalCalibratedExactnessCore) :
    Month12ProofLengthFreeCheckerSearchCandidate core.scale_data :=
  (PAHilbertCanonicalCalibratedExactnessCore.toCanonicalSearchCore
    core).toProofLengthFreeMonth12Candidate

theorem PAHilbertCanonicalCalibratedExactnessCore.proofLengthFreeMonth12Candidate_closure
    (core : PAHilbertCanonicalCalibratedExactnessCore)
    (upper_provider :
      (PAHilbertCanonicalCalibratedExactnessCore.toProofLengthFreeMonth12Candidate
        core).checkedMeasuredUpperProviderType) :
    ((PAHilbertCanonicalCalibratedExactnessCore.toProofLengthFreeMonth12Candidate
        core)
      |>.toCheckedSearchCollisionEndpoint upper_provider).Audit ∧
      Nonempty (Month12ProofLengthFreeCheckerSearchCandidate core.scale_data) ∧
      Nonempty (Month9Month10CheckedSearchCollisionEndpoint core.scale_data) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            core.scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (((PAHilbertCanonicalCalibratedExactnessCore.toProofLengthFreeMonth12Candidate
          core)
          |>.toCheckedSearchCollisionEndpoint upper_provider)
            |>.computedCollisionNOfRationality hrat) =
          core.rejectionExtractor.witness
            (checkedSearchUpperTail
              (PAHilbertCanonicalCalibratedExactnessCore.toProofLengthFreeMonth12Candidate
                core) upper_provider hrat).U
            (checkedSearchUpperTail
              (PAHilbertCanonicalCalibratedExactnessCore.toProofLengthFreeMonth12Candidate
                core) upper_provider hrat).polynomial
            (checkedSearchUpperTail
              (PAHilbertCanonicalCalibratedExactnessCore.toProofLengthFreeMonth12Candidate
                core) upper_provider hrat).upperN) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    (PAHilbertCanonicalCalibratedExactnessCore.toCanonicalSearchCore core)
      |>.proofLengthFreeMonth12Candidate_closure upper_provider
  simpa [
    PAHilbertCanonicalCalibratedExactnessCore.toProofLengthFreeMonth12Candidate,
    PAHilbertCanonicalCalibratedExactnessCore.toCanonicalSearchCore,
    PAHilbertCanonicalSearchCore.toProofLengthFreeMonth12Candidate]
    using hclosure

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

/-- Upgrade a canonical calibrated PA/Hilbert core to the full Month 12
candidate.  The only extra field beyond the proof-length-free candidate is the
family transport from root project `proof_length` to the checker minimum; it is
obtained by specializing the core's calibrated proof-length exactness to
`powerBoundRawCode n`. -/
def PAHilbertCanonicalCalibratedExactnessCore.toMonth12UnconditionalCandidate
    (core : PAHilbertCanonicalCalibratedExactnessCore) :
    Month12UnconditionalPAHilbertCheckerInternalizationCandidate
      core.scale_data where
  formulaSyntax := PAHilbertFormula
  syntaxCode := PAHilbertFormula.code
  proofObject := PAHilbertProofObject
  proofObjectCode := PAHilbertProofObject.code
  proofObjectConclusion := PAHilbertProofObject.conclusion
  recognizer := core.checker.recognizer
  inferenceRule := PAHilbertInferenceRule
  inferenceRuleName := id
  checker := core.checker
  checker_recognizer_eq := rfl
  semantics := core.semantics
  recognizerExactness := core.recognizerExactness
  canonicalInterface := core.canonicalInterface
  checkerSemantics := core.checkerSemantics
  finiteEnumeration := core.finiteEnumeration
  rejectionExtractor := core.rejectionExtractor
  acceptedCodeExactness := core.accepted_decoded_code_to_formulaCode_derivable
  minProofCodeSizeExactness :=
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness.ofCheckerProofLengthExactness
      core.proofLengthExactness
  proofLengthTransport := by
    intro n
    simpa [actualProofLengthMeasured]
      using core.proofLengthExactness.at_powerBoundRawCode n

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

/-- Closure of the canonical-core-to-Month-12 upgrade.  This is the point where
the checker-generated finite search, actual proof-length gap, and root
proof-length transport are all available from one calibrated core. -/
theorem PAHilbertCanonicalCalibratedExactnessCore.month12_unconditionalCandidate_closure
    (core : PAHilbertCanonicalCalibratedExactnessCore) :
    Nonempty
        (Month12UnconditionalPAHilbertCheckerInternalizationCandidate
          core.scale_data) ∧
      Nonempty PAHilbertCanonicalCalibratedExactnessCore ∧
        Nonempty
          InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} ∧
        Nonempty Month9Month10ComputableNoSmallProofLengthFrontier.{0} ∧
          Nonempty
            (ComputableSearchGapCertificate
              (actualProofLengthMeasured core.scale_data)) ∧
          (∀ n : Nat,
            actualProofLengthMeasured core.scale_data n =
              (core.checkerSemantics.minProofCodeSizeAt n : Real)) := by
  have hclosure :=
    month12_candidate_closure
      (PAHilbertCanonicalCalibratedExactnessCore.toMonth12UnconditionalCandidate
        core)
  exact
    ⟨⟨PAHilbertCanonicalCalibratedExactnessCore.toMonth12UnconditionalCandidate
        core⟩,
      hclosure.1,
      hclosure.2.1,
      hclosure.2.2.1,
      hclosure.2.2.2.1,
      hclosure.2.2.2.2⟩

end SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface
end SondowMainCheckedCodeBridge
