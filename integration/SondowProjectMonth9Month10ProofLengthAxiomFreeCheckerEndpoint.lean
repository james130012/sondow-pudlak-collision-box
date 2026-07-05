import integration.SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth11PAHilbertCheckerSurface
open SondowProjectMonth9Month10Month11ExactProofGapHandoff
open SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface
open Filter

/-- Project-level endpoint for the corrected route that does not mention the
root `proof_length` axiom.  The measured object is the concrete checker minimum
proof-code size exposed through `month9_month10_checkedProofCodeMeasured`. -/
structure ProofLengthAxiomFreeCheckerEndpointChecklist : Prop where
  checkedSearchClosure :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ candidate :
        Month12ProofLengthFreeCheckerSearchCandidate scale_data,
        ∀ upper_provider : candidate.checkedMeasuredUpperProviderType,
          (candidate.toCheckedSearchCollisionEndpoint upper_provider).Audit ∧
            Nonempty (Month9Month10CheckedSearchCollisionEndpoint scale_data) ∧
            Nonempty
              (ComputableSearchGapCertificate
                (month9_month10_checkedProofCodeMeasured
                  scale_data candidate.checkerSemantics.toProofCodeSemantics)) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              ((candidate.toCheckedSearchCollisionEndpoint
                  upper_provider).computedCollisionNOfRationality hrat) =
                candidate.rejectionExtractor.witness
                  (checkedSearchUpperTail
                    candidate upper_provider hrat).U
                  (checkedSearchUpperTail
                    candidate upper_provider hrat).polynomial
                  (checkedSearchUpperTail
                    candidate upper_provider hrat).upperN)

theorem proof_length_axiom_free_checker_endpoint_checklist :
    ProofLengthAxiomFreeCheckerEndpointChecklist where
  checkedSearchClosure := by
    intro scale_data candidate upper_provider
    exact proof_length_free_candidate_closure candidate upper_provider

/-- Stronger final-collision checklist for the proof-length-axiom-free route.
It exposes the endpoint audit, the checked lower-gap certificate, the computed
`n` formula, the contradiction at that `n`, and the resulting non-rationality
claim, all without mentioning the root `proof_length` symbol. -/
structure ProofLengthAxiomFreeCheckerFinalCollisionChecklist : Prop where
  finalClosure :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ candidate :
        Month12ProofLengthFreeCheckerSearchCandidate scale_data,
        ∀ upper_provider : candidate.checkedMeasuredUpperProviderType,
          (candidate.toCheckedSearchCollisionEndpoint upper_provider).Audit ∧
            Nonempty (Month9Month10CheckedSearchCollisionEndpoint scale_data) ∧
            Nonempty
              (ComputableSearchGapCertificate
                (month9_month10_checkedProofCodeMeasured
                  scale_data candidate.checkerSemantics.toProofCodeSemantics)) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              ((candidate.toCheckedSearchCollisionEndpoint
                  upper_provider).computedCollisionNOfRationality hrat) =
                candidate.rejectionExtractor.witness
                  (checkedSearchUpperTail
                    candidate upper_provider hrat).U
                  (checkedSearchUpperTail
                    candidate upper_provider hrat).polynomial
                  (checkedSearchUpperTail
                    candidate upper_provider hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
            ¬ _root_.is_rational _root_.euler_mascheroni

theorem proof_length_axiom_free_checker_final_collision_checklist :
    ProofLengthAxiomFreeCheckerFinalCollisionChecklist where
  finalClosure := by
    intro scale_data candidate upper_provider
    rcases
      (candidate.toCheckedSearchCollisionEndpoint
        upper_provider).closure with
      ⟨haudit, _hdirect, hgap, _hwitness, hcontradiction, hnot⟩
    exact
      ⟨haudit,
        ⟨candidate.toCheckedSearchCollisionEndpoint upper_provider⟩,
        hgap,
        computedCollisionN_eq_rejectionExtractorWitness
          candidate upper_provider,
        hcontradiction,
        hnot⟩

/-- Proof-complexity lower-bound content exposed without the root `proof_length`
symbol.  This is the finite-consistency lower-bound machine in checker/search
form: finite enumeration plus rejection of all small candidates yields
no-small proof codes and the corresponding `minProofCodeSize` lower bound. -/
structure ProofLengthAxiomFreeCheckerLowerBoundMachineChecklist :
    Prop where
  finiteSearchExclusion :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ candidate :
        Month12ProofLengthFreeCheckerSearchCandidate scale_data,
        InternalPudlakTheorem5FiniteSearchExclusion
          scale_data candidate.checkerSemantics.toProofCodeSemantics
          candidate.finiteEnumeration.toSmallCodeSearch
  noSmallProofCodes :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ candidate :
        Month12ProofLengthFreeCheckerSearchCandidate scale_data,
        InternalPudlakTheorem5NoSmallProofCodes
          scale_data candidate.checkerSemantics.toProofCodeSemantics
  minProofCodeSizeLowerBound :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ candidate :
        Month12ProofLengthFreeCheckerSearchCandidate scale_data,
        ∀ f : Nat → Real, _root_.is_polynomial_bound f →
          ∃ᶠ n in atTop,
            (candidate.checkerSemantics.toProofCodeSemantics.minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n
  computedWitnessLowerBound :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ candidate :
        Month12ProofLengthFreeCheckerSearchCandidate scale_data,
        ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f,
          ∀ N : Nat,
            let profile :=
              candidate.rejectionExtractor.toCheckerComputableSearchProfile
            (profile.proof_code_semantics.minProofCodeSize
              (scale_data.powerBoundRawCode
                (profile.computable_search_exclusion.witness f hf N))
              ⟨profile.computable_search_exclusion.witness f hf N, rfl⟩ : Real) >
              f (profile.computable_search_exclusion.witness f hf N)
  computedWitnessEqExtractor :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ candidate :
        Month12ProofLengthFreeCheckerSearchCandidate scale_data,
        ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f,
          ∀ N : Nat,
            let profile :=
              candidate.rejectionExtractor.toCheckerComputableSearchProfile
            profile.computable_search_exclusion.witness f hf N =
            candidate.rejectionExtractor.witness f hf N

theorem proof_length_axiom_free_checker_lower_bound_machine_checklist :
    ProofLengthAxiomFreeCheckerLowerBoundMachineChecklist where
  finiteSearchExclusion := by
    intro scale_data candidate
    exact
      candidate.rejectionExtractor
        |>.toCheckerComputableSearchProfile
        |>.finite_search_exclusion
  noSmallProofCodes := by
    intro scale_data candidate
    exact
      candidate.rejectionExtractor
        |>.toCheckerComputableSearchProfile
        |>.no_small_proof_codes
  minProofCodeSizeLowerBound := by
    intro scale_data candidate f hf
    exact
      candidate.rejectionExtractor
        |>.toCheckerComputableSearchProfile
        |>.toNoSmallProfile
        |>.proof_code_lower_bound f hf
  computedWitnessLowerBound := by
    intro scale_data candidate f hf N
    exact
      candidate.rejectionExtractor
        |>.toCheckerComputableSearchProfile
        |>.computable_search_exclusion
        |>.minProofCodeSize_gt_at_witness f hf N
  computedWitnessEqExtractor := by
    intro scale_data candidate f hf N
    exact
      InternalPudlakTheorem5CheckerComputableRejectionExtractor.toCheckerComputableSearchProfile_witness_eq
        candidate.rejectionExtractor f hf N

/-- Bundled proof-length-axiom-free theorem-5 provider endpoint.  It is the
object the final route should consume before any optional compatibility layer
with the historical root `proof_length` symbol: a concrete checker candidate
plus the Sondow upper provider for the same checked measurement. -/
structure ProofLengthAxiomFreeInternalTheorem5Provider : Type 2 where
  scale_data : InternalPudlakTheorem5ScaleData
  candidate : Month12ProofLengthFreeCheckerSearchCandidate scale_data
  upper_provider : candidate.checkedMeasuredUpperProviderType

namespace ProofLengthAxiomFreeInternalTheorem5Provider

def endpoint
    (h : ProofLengthAxiomFreeInternalTheorem5Provider) :
    Month9Month10CheckedSearchCollisionEndpoint h.scale_data :=
  h.candidate.toCheckedSearchCollisionEndpoint h.upper_provider

def searchProfile
    (h : ProofLengthAxiomFreeInternalTheorem5Provider) :
    InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
      h.scale_data :=
  h.candidate.rejectionExtractor.toCheckerComputableSearchProfile

theorem finiteSearchExclusion
    (h : ProofLengthAxiomFreeInternalTheorem5Provider) :
    InternalPudlakTheorem5FiniteSearchExclusion
      h.scale_data h.candidate.checkerSemantics.toProofCodeSemantics
      h.candidate.finiteEnumeration.toSmallCodeSearch :=
  h.searchProfile.finite_search_exclusion

theorem noSmallProofCodes
    (h : ProofLengthAxiomFreeInternalTheorem5Provider) :
    InternalPudlakTheorem5NoSmallProofCodes
      h.scale_data h.candidate.checkerSemantics.toProofCodeSemantics :=
  h.searchProfile.no_small_proof_codes

theorem minProofCodeSizeLowerBound
    (h : ProofLengthAxiomFreeInternalTheorem5Provider)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) :
    ∃ᶠ n in atTop,
      (h.candidate.checkerSemantics.toProofCodeSemantics.minProofCodeSize
        (h.scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n :=
  h.searchProfile.toNoSmallProfile.proof_code_lower_bound f hf

theorem powerBoundRawCode_eq_scaled_strengthened
    (h : ProofLengthAxiomFreeInternalTheorem5Provider) (n : Nat) :
    h.scale_data.powerBoundRawCode n =
      _root_.strengthenedPartialConsistencyCode (h.scale_data.scale n) :=
  InternalPudlakTheorem5ScaleData.powerBoundRawCode_eq_scaled_strengthened
    h.scale_data n

noncomputable def computedCollisionNOfRationality
    (h : ProofLengthAxiomFreeInternalTheorem5Provider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  h.endpoint.computedCollisionNOfRationality hrat

theorem computedCollisionN_eq_rejectionExtractorWitness
    (h : ProofLengthAxiomFreeInternalTheorem5Provider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      h.candidate.rejectionExtractor.witness
        (checkedSearchUpperTail
          h.candidate h.upper_provider hrat).U
        (checkedSearchUpperTail
          h.candidate h.upper_provider hrat).polynomial
        (checkedSearchUpperTail
          h.candidate h.upper_provider hrat).upperN :=
  SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.computedCollisionN_eq_rejectionExtractorWitness
    h.candidate h.upper_provider hrat

theorem computedCollisionN_ge_upperN
    (h : ProofLengthAxiomFreeInternalTheorem5Provider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (checkedSearchUpperTail
      h.candidate h.upper_provider hrat).upperN ≤
      h.computedCollisionNOfRationality hrat :=
  h.endpoint.toDirectEndpoint.toAbstractMeasuredEndpoint
    |>.computedCollisionN_ge_upperN hrat

theorem lower_at_computedCollisionN
    (h : ProofLengthAxiomFreeInternalTheorem5Provider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (checkedSearchUpperTail
      h.candidate h.upper_provider hrat).U
        (h.computedCollisionNOfRationality hrat) <
      month9_month10_checkedProofCodeMeasured
        h.scale_data h.candidate.checkerSemantics.toProofCodeSemantics
        (h.computedCollisionNOfRationality hrat) :=
  h.endpoint.toDirectEndpoint.toAbstractMeasuredEndpoint
    |>.lower_at_computedCollisionN hrat

theorem upper_at_computedCollisionN
    (h : ProofLengthAxiomFreeInternalTheorem5Provider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    month9_month10_checkedProofCodeMeasured
        h.scale_data h.candidate.checkerSemantics.toProofCodeSemantics
        (h.computedCollisionNOfRationality hrat) ≤
      (checkedSearchUpperTail
        h.candidate h.upper_provider hrat).U
        (h.computedCollisionNOfRationality hrat) :=
  h.endpoint.toDirectEndpoint.toAbstractMeasuredEndpoint
    |>.upper_at_computedCollisionN hrat

theorem computed_n_contradiction
    (h : ProofLengthAxiomFreeInternalTheorem5Provider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.endpoint.computed_n_contradiction hrat

theorem not_rational
    (h : ProofLengthAxiomFreeInternalTheorem5Provider) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.endpoint.not_rational

structure Audit
    (h : ProofLengthAxiomFreeInternalTheorem5Provider) : Prop where
  endpointAudit : h.endpoint.Audit
  finiteSearchExclusion :
    InternalPudlakTheorem5FiniteSearchExclusion
      h.scale_data h.candidate.checkerSemantics.toProofCodeSemantics
      h.candidate.finiteEnumeration.toSmallCodeSearch
  noSmallProofCodes :
    InternalPudlakTheorem5NoSmallProofCodes
      h.scale_data h.candidate.checkerSemantics.toProofCodeSemantics
  minProofCodeSizeLowerBound :
    ∀ f : Nat → Real, ∀ _hf : _root_.is_polynomial_bound f,
      ∃ᶠ n in atTop,
        (h.candidate.checkerSemantics.toProofCodeSemantics.minProofCodeSize
          (h.scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n
  finiteConsistencyRawFamily :
    ∀ n : Nat,
      h.scale_data.powerBoundRawCode n =
        _root_.strengthenedPartialConsistencyCode (h.scale_data.scale n)
  computedWitnessFormula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        h.candidate.rejectionExtractor.witness
          (checkedSearchUpperTail
            h.candidate h.upper_provider hrat).U
          (checkedSearchUpperTail
            h.candidate h.upper_provider hrat).polynomial
          (checkedSearchUpperTail
            h.candidate h.upper_provider hrat).upperN
  computedNGeUpperN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (checkedSearchUpperTail
        h.candidate h.upper_provider hrat).upperN ≤
        h.computedCollisionNOfRationality hrat
  lowerAtComputedN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (checkedSearchUpperTail
        h.candidate h.upper_provider hrat).U
          (h.computedCollisionNOfRationality hrat) <
        month9_month10_checkedProofCodeMeasured
          h.scale_data h.candidate.checkerSemantics.toProofCodeSemantics
          (h.computedCollisionNOfRationality hrat)
  upperAtComputedN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      month9_month10_checkedProofCodeMeasured
          h.scale_data h.candidate.checkerSemantics.toProofCodeSemantics
          (h.computedCollisionNOfRationality hrat) ≤
        (checkedSearchUpperTail
          h.candidate h.upper_provider hrat).U
          (h.computedCollisionNOfRationality hrat)
  contradictionAtComputedN :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    (h : ProofLengthAxiomFreeInternalTheorem5Provider) :
    h.Audit where
  endpointAudit := h.endpoint.audit
  finiteSearchExclusion := h.finiteSearchExclusion
  noSmallProofCodes := h.noSmallProofCodes
  minProofCodeSizeLowerBound := h.minProofCodeSizeLowerBound
  finiteConsistencyRawFamily := h.powerBoundRawCode_eq_scaled_strengthened
  computedWitnessFormula := h.computedCollisionN_eq_rejectionExtractorWitness
  computedNGeUpperN := h.computedCollisionN_ge_upperN
  lowerAtComputedN := h.lower_at_computedCollisionN
  upperAtComputedN := h.upper_at_computedCollisionN
  contradictionAtComputedN := h.computed_n_contradiction
  endpointNotRational := h.not_rational

theorem closure
    (h : ProofLengthAxiomFreeInternalTheorem5Provider) :
    h.Audit ∧
      h.endpoint.Audit ∧
        (∀ f : Nat → Real, ∀ _hf : _root_.is_polynomial_bound f,
          ∃ᶠ n in atTop,
            (h.candidate.checkerSemantics.toProofCodeSemantics.minProofCodeSize
              (h.scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
          (∀ n : Nat,
            h.scale_data.powerBoundRawCode n =
              _root_.strengthenedPartialConsistencyCode
                (h.scale_data.scale n)) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              h.computedCollisionNOfRationality hrat =
                h.candidate.rejectionExtractor.witness
                  (checkedSearchUpperTail
                    h.candidate h.upper_provider hrat).U
                  (checkedSearchUpperTail
                    h.candidate h.upper_provider hrat).polynomial
                  (checkedSearchUpperTail
                    h.candidate h.upper_provider hrat).upperN) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                (checkedSearchUpperTail
                  h.candidate h.upper_provider hrat).upperN ≤
                  h.computedCollisionNOfRationality hrat) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                (checkedSearchUpperTail
                  h.candidate h.upper_provider hrat).U
                    (h.computedCollisionNOfRationality hrat) <
                  month9_month10_checkedProofCodeMeasured
                    h.scale_data
                    h.candidate.checkerSemantics.toProofCodeSemantics
                    (h.computedCollisionNOfRationality hrat)) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                month9_month10_checkedProofCodeMeasured
                    h.scale_data
                    h.candidate.checkerSemantics.toProofCodeSemantics
                    (h.computedCollisionNOfRationality hrat) ≤
                  (checkedSearchUpperTail
                    h.candidate h.upper_provider hrat).U
                    (h.computedCollisionNOfRationality hrat)) ∧
              (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨h.audit,
    h.endpoint.audit,
      h.minProofCodeSizeLowerBound,
      h.powerBoundRawCode_eq_scaled_strengthened,
      h.computedCollisionN_eq_rejectionExtractorWitness,
      h.computedCollisionN_ge_upperN,
      h.lower_at_computedCollisionN,
      h.upper_at_computedCollisionN,
      h.computed_n_contradiction,
      h.not_rational⟩

end ProofLengthAxiomFreeInternalTheorem5Provider

/-! ## Checked-upper instantiation of the proof-length-free provider -/

/-- The narrowest theorem-5 provider: the PA/Hilbert search core plus a
checked-measure upper provider for exactly the same measurement.  This is the
root `proof_length`-free target that the Sondow upper route must eventually
instantiate directly. -/
def theorem5ProviderOfCanonicalSearchCoreCheckedUpper
    (core : PAHilbertCanonicalSearchCore)
    (upper_provider :
      core.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType) :
    ProofLengthAxiomFreeInternalTheorem5Provider where
  scale_data := core.scale_data
  candidate := core.toProofLengthFreeMonth12Candidate
  upper_provider := upper_provider

theorem theorem5ProviderOfCanonicalSearchCoreCheckedUpper_computed_n_eq
    (core : PAHilbertCanonicalSearchCore)
    (upper_provider :
      core.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (theorem5ProviderOfCanonicalSearchCoreCheckedUpper
      core upper_provider).computedCollisionNOfRationality hrat =
      core.rejectionExtractor.witness
        (checkedSearchUpperTail
          core.toProofLengthFreeMonth12Candidate upper_provider hrat).U
        (checkedSearchUpperTail
          core.toProofLengthFreeMonth12Candidate upper_provider hrat).polynomial
        (checkedSearchUpperTail
          core.toProofLengthFreeMonth12Candidate upper_provider hrat).upperN :=
  (theorem5ProviderOfCanonicalSearchCoreCheckedUpper
    core upper_provider).computedCollisionN_eq_rejectionExtractorWitness hrat

theorem theorem5ProviderOfCanonicalSearchCoreCheckedUpper_closure
    (core : PAHilbertCanonicalSearchCore)
    (upper_provider :
      core.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType) :
    (theorem5ProviderOfCanonicalSearchCoreCheckedUpper
      core upper_provider).Audit ∧
      (theorem5ProviderOfCanonicalSearchCoreCheckedUpper
        core upper_provider).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (theorem5ProviderOfCanonicalSearchCoreCheckedUpper
            core upper_provider).computedCollisionNOfRationality hrat =
            core.rejectionExtractor.witness
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate upper_provider hrat).U
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate upper_provider hrat).polynomial
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate upper_provider hrat).upperN) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (checkedSearchUpperTail
              core.toProofLengthFreeMonth12Candidate upper_provider hrat).U
                ((theorem5ProviderOfCanonicalSearchCoreCheckedUpper
                  core upper_provider).computedCollisionNOfRationality hrat) <
              month9_month10_checkedProofCodeMeasured
                core.scale_data core.checkerSemantics.toProofCodeSemantics
                ((theorem5ProviderOfCanonicalSearchCoreCheckedUpper
                  core upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            month9_month10_checkedProofCodeMeasured
                core.scale_data core.checkerSemantics.toProofCodeSemantics
                ((theorem5ProviderOfCanonicalSearchCoreCheckedUpper
                  core upper_provider).computedCollisionNOfRationality hrat) ≤
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate upper_provider hrat).U
                ((theorem5ProviderOfCanonicalSearchCoreCheckedUpper
                  core upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    ⟨(theorem5ProviderOfCanonicalSearchCoreCheckedUpper
        core upper_provider).audit,
      (theorem5ProviderOfCanonicalSearchCoreCheckedUpper
        core upper_provider).endpoint.audit,
      theorem5ProviderOfCanonicalSearchCoreCheckedUpper_computed_n_eq
        core upper_provider,
      (theorem5ProviderOfCanonicalSearchCoreCheckedUpper
        core upper_provider).lower_at_computedCollisionN,
      (theorem5ProviderOfCanonicalSearchCoreCheckedUpper
        core upper_provider).upper_at_computedCollisionN,
      (theorem5ProviderOfCanonicalSearchCoreCheckedUpper
        core upper_provider).computed_n_contradiction,
      (theorem5ProviderOfCanonicalSearchCoreCheckedUpper
        core upper_provider).not_rational⟩

/-! ## Project-upper instantiation of the proof-length-free provider -/

/-- Turn the Sondow project-box upper route into the checked
`minProofCodeSize` upper provider needed by the proof-length-free theorem-5
endpoint.  The only same-object bridge used here is the additive projection
from theorem-5 source proofs to the Sondow project box. -/
def projectUpperProviderForCanonicalSearchCore
    (core : PAHilbertCanonicalSearchCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (core.toProofLengthFreeMonth12Candidate).checkedMeasuredUpperProviderType :=
  checkedUpperProviderOfProjectUpperAndAdditiveProjection
    projection project_upper

/-- Project-level theorem-5 provider that stays on the checked
`minProofCodeSize` measurement.  This avoids the root `proof_length` transport
layer while still recording that the upper tail came from the Sondow project
route plus the additive projection. -/
def theorem5ProviderOfCanonicalSearchCoreProjectUpper
    (core : PAHilbertCanonicalSearchCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    ProofLengthAxiomFreeInternalTheorem5Provider where
  scale_data := core.scale_data
  candidate := core.toProofLengthFreeMonth12Candidate
  upper_provider :=
    projectUpperProviderForCanonicalSearchCore
      core projection project_upper

theorem theorem5ProviderOfCanonicalSearchCoreProjectUpper_computed_n_eq
    (core : PAHilbertCanonicalSearchCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (theorem5ProviderOfCanonicalSearchCoreProjectUpper
      core projection project_upper).computedCollisionNOfRationality hrat =
      core.rejectionExtractor.witness
        (checkedSearchUpperTail
          core.toProofLengthFreeMonth12Candidate
          (projectUpperProviderForCanonicalSearchCore
            core projection project_upper)
          hrat).U
        (checkedSearchUpperTail
          core.toProofLengthFreeMonth12Candidate
          (projectUpperProviderForCanonicalSearchCore
            core projection project_upper)
          hrat).polynomial
        (checkedSearchUpperTail
          core.toProofLengthFreeMonth12Candidate
          (projectUpperProviderForCanonicalSearchCore
            core projection project_upper)
          hrat).upperN :=
  (theorem5ProviderOfCanonicalSearchCoreProjectUpper
    core projection project_upper).computedCollisionN_eq_rejectionExtractorWitness
      hrat

theorem theorem5ProviderOfCanonicalSearchCoreProjectUpper_closure
    (core : PAHilbertCanonicalSearchCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (theorem5ProviderOfCanonicalSearchCoreProjectUpper
      core projection project_upper).Audit ∧
      (theorem5ProviderOfCanonicalSearchCoreProjectUpper
        core projection project_upper).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (theorem5ProviderOfCanonicalSearchCoreProjectUpper
            core projection project_upper).computedCollisionNOfRationality hrat =
            core.rejectionExtractor.witness
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (projectUpperProviderForCanonicalSearchCore
                  core projection project_upper)
                hrat).U
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (projectUpperProviderForCanonicalSearchCore
                  core projection project_upper)
                hrat).polynomial
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (projectUpperProviderForCanonicalSearchCore
                  core projection project_upper)
                hrat).upperN) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (checkedSearchUpperTail
              core.toProofLengthFreeMonth12Candidate
              (projectUpperProviderForCanonicalSearchCore
                core projection project_upper)
              hrat).U
                ((theorem5ProviderOfCanonicalSearchCoreProjectUpper
                  core projection project_upper).computedCollisionNOfRationality hrat) <
              month9_month10_checkedProofCodeMeasured
                core.scale_data core.checkerSemantics.toProofCodeSemantics
                ((theorem5ProviderOfCanonicalSearchCoreProjectUpper
                  core projection project_upper).computedCollisionNOfRationality hrat)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            month9_month10_checkedProofCodeMeasured
                core.scale_data core.checkerSemantics.toProofCodeSemantics
                ((theorem5ProviderOfCanonicalSearchCoreProjectUpper
                  core projection project_upper).computedCollisionNOfRationality hrat) ≤
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (projectUpperProviderForCanonicalSearchCore
                  core projection project_upper)
                hrat).U
                ((theorem5ProviderOfCanonicalSearchCoreProjectUpper
                  core projection project_upper).computedCollisionNOfRationality hrat)) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    ⟨(theorem5ProviderOfCanonicalSearchCoreProjectUpper
        core projection project_upper).audit,
      (theorem5ProviderOfCanonicalSearchCoreProjectUpper
        core projection project_upper).endpoint.audit,
      theorem5ProviderOfCanonicalSearchCoreProjectUpper_computed_n_eq
        core projection project_upper,
      (theorem5ProviderOfCanonicalSearchCoreProjectUpper
        core projection project_upper).lower_at_computedCollisionN,
      (theorem5ProviderOfCanonicalSearchCoreProjectUpper
        core projection project_upper).upper_at_computedCollisionN,
      (theorem5ProviderOfCanonicalSearchCoreProjectUpper
        core projection project_upper).computed_n_contradiction,
      (theorem5ProviderOfCanonicalSearchCoreProjectUpper
        core projection project_upper).not_rational⟩

/-! ## Payload-free upper-provider instantiation -/

/-- Transport a payload-free project-box upper provider to the checked
theorem-5 measurement using the same additive projection as the legacy project
upper route.  Unlike `checkedUpperProviderOfProjectUpperAndAdditiveProjection`,
this adapter does not look inside `SondowProjectLocalS21CollapseConclusion`. -/
def checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (upper_provider : Month9Month10PayloadFreeUpperProvider) :
    Month9Month10AbstractMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured scale_data sem) where
  upper_under_rationality := by
    intro hrat
    rcases upper_provider.upper_under_rationality hrat with
      ⟨U, hU, upperN, hupper⟩
    refine
      ⟨projection.shiftedUpper U,
        projection.shiftedUpper_polynomial U hU,
        upperN,
        ?_⟩
    intro n hn
    have hsource := projection.source_le_project_add n
    have hproject := hupper n hn
    have hchecked :
        (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
          U n + projection.overhead :=
      by nlinarith
    simpa [
      month9_month10_checkedProofCodeMeasured,
      InternalPudlakTheorem5AdditiveProjectBoxProjection.shiftedUpper]
      using hchecked

theorem checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (upper_provider : Month9Month10PayloadFreeUpperProvider) :
    (checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection
      projection upper_provider).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              month9_month10_checkedProofCodeMeasured scale_data sem n ≤
                U n) :=
  (checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection
    projection upper_provider).closure

/-- Project-level theorem-5 provider with a payload-free upper input.  This is
the clean public interface for the final route once the Sondow upper side is
provided without the legacy accepted-certificate payload vocabulary. -/
def theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
    (core : PAHilbertCanonicalSearchCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (upper_provider : Month9Month10PayloadFreeUpperProvider) :
    ProofLengthAxiomFreeInternalTheorem5Provider where
  scale_data := core.scale_data
  candidate := core.toProofLengthFreeMonth12Candidate
  upper_provider :=
    checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection
      projection upper_provider

theorem theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper_computed_n_eq
    (core : PAHilbertCanonicalSearchCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (upper_provider : Month9Month10PayloadFreeUpperProvider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
      core projection upper_provider).computedCollisionNOfRationality hrat =
      core.rejectionExtractor.witness
        (checkedSearchUpperTail
          core.toProofLengthFreeMonth12Candidate
          (checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection
            projection upper_provider)
          hrat).U
        (checkedSearchUpperTail
          core.toProofLengthFreeMonth12Candidate
          (checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection
            projection upper_provider)
          hrat).polynomial
        (checkedSearchUpperTail
          core.toProofLengthFreeMonth12Candidate
          (checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection
            projection upper_provider)
          hrat).upperN :=
  (theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
    core projection upper_provider).computedCollisionN_eq_rejectionExtractorWitness
      hrat

theorem theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper_closure
    (core : PAHilbertCanonicalSearchCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (upper_provider : Month9Month10PayloadFreeUpperProvider) :
    (theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
      core projection upper_provider).Audit ∧
      (theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
        core projection upper_provider).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
            core projection upper_provider).computedCollisionNOfRationality hrat =
            core.rejectionExtractor.witness
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection
                  projection upper_provider)
                hrat).U
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection
                  projection upper_provider)
                hrat).polynomial
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection
                  projection upper_provider)
                hrat).upperN) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (checkedSearchUpperTail
              core.toProofLengthFreeMonth12Candidate
              (checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection
                projection upper_provider)
              hrat).U
                ((theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
                  core projection upper_provider).computedCollisionNOfRationality hrat) <
              month9_month10_checkedProofCodeMeasured
                core.scale_data core.checkerSemantics.toProofCodeSemantics
                ((theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
                  core projection upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            month9_month10_checkedProofCodeMeasured
                core.scale_data core.checkerSemantics.toProofCodeSemantics
                ((theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
                  core projection upper_provider).computedCollisionNOfRationality hrat) ≤
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection
                  projection upper_provider)
                hrat).U
                ((theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
                  core projection upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    ⟨(theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
        core projection upper_provider).audit,
      (theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
        core projection upper_provider).endpoint.audit,
      theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper_computed_n_eq
        core projection upper_provider,
      (theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
        core projection upper_provider).lower_at_computedCollisionN,
      (theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
        core projection upper_provider).upper_at_computedCollisionN,
      (theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
        core projection upper_provider).computed_n_contradiction,
      (theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
        core projection upper_provider).not_rational⟩

/-! ## C-line instantiation of the project upper route -/

/-- Replace the abstract Sondow project upper input by the current concrete
C-line minimal closure certificate.  This keeps the proof-length-free theorem-5
measurement, while making the Sondow upper-route source auditable as
kernel/checker/length data. -/
def theorem5ProviderOfCanonicalSearchCoreCLineMinimalClosure
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (core : PAHilbertCanonicalSearchCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (cline : Nonempty (SondowCLineMinimalClosureCertificate bounds)) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfCanonicalSearchCoreProjectUpper
    core projection
    (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
      cline)

theorem theorem5ProviderOfCanonicalSearchCoreCLineMinimalClosure_closure
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (core : PAHilbertCanonicalSearchCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (cline : Nonempty (SondowCLineMinimalClosureCertificate bounds)) :
    (theorem5ProviderOfCanonicalSearchCoreCLineMinimalClosure
      core projection cline).Audit ∧
      (theorem5ProviderOfCanonicalSearchCoreCLineMinimalClosure
        core projection cline).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (theorem5ProviderOfCanonicalSearchCoreCLineMinimalClosure
            core projection cline).computedCollisionNOfRationality hrat =
            core.rejectionExtractor.witness
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (projectUpperProviderForCanonicalSearchCore
                  core projection
                  (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                    cline))
                hrat).U
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (projectUpperProviderForCanonicalSearchCore
                  core projection
                  (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                    cline))
                hrat).polynomial
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (projectUpperProviderForCanonicalSearchCore
                  core projection
                  (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                    cline))
        hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    theorem5ProviderOfCanonicalSearchCoreProjectUpper_closure
      core projection
      (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
        cline)
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.1,
      hclosure.2.2.2.2.2.1,
      hclosure.2.2.2.2.2.2⟩

/-- C-line entry point with the three explicit nonempty components.  This is
the current narrowest public upper-route instantiation before eliminating the
remaining payload/proof-length conventions inside those component certificates. -/
def theorem5ProviderOfCanonicalSearchCoreCLineKernelCheckerLength
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (core : PAHilbertCanonicalSearchCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfCanonicalSearchCoreCLineMinimalClosure
    core projection
    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
      hkernel hchecker hlength)

theorem theorem5ProviderOfCanonicalSearchCoreCLineKernelCheckerLength_closure
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (core : PAHilbertCanonicalSearchCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    (theorem5ProviderOfCanonicalSearchCoreCLineKernelCheckerLength
      core projection hkernel hchecker hlength).Audit ∧
      (theorem5ProviderOfCanonicalSearchCoreCLineKernelCheckerLength
        core projection hkernel hchecker hlength).endpoint.Audit ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    theorem5ProviderOfCanonicalSearchCoreCLineMinimalClosure_closure
      core projection
      (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
        hkernel hchecker hlength)
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.2.1,
      hclosure.2.2.2.2⟩

/-! ## Search-only singleton PA/Hilbert instantiation -/

/-- Proof-length-free singleton search input for the concrete PA/Hilbert
power-bound checker.  This is the route to use when the lower-bound machine
already supplies a computable search gap for the checker-side calibrated
length, without passing through the root `proof_length` symbol. -/
structure ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  lengthCodeAt : Nat → Nat
  scale_strict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  gap :
    ComputableSearchGapCertificate
      (fun n : Nat => (lengthCodeAt n : Real))

namespace ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput

theorem scale_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data) :
    Function.Injective scale_data.scale := by
  intro a b hscale_eq
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have hstrict :
        scale_data.scale a < scale_data.scale b :=
      input.scale_strict hlt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)
  · exact heq
  · have hstrict :
        scale_data.scale b < scale_data.scale a :=
      input.scale_strict hgt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)

theorem powerBoundRawCode_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data) :
    Function.Injective scale_data.powerBoundRawCode :=
  concretePAHilbert_powerBoundRawCode_injective_of_scale_injective
    scale_data input.scale_injective

def toSingletonGapRejectionInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data) :
    ConcretePAHilbertPowerBoundSingletonGapRejectionInput
      scale_data input.lengthCodeAt where
  powerBoundRawCode_injective :=
    input.powerBoundRawCode_injective
  gap :=
    input.gap

def checkerSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data) :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data :=
  concretePAHilbertPowerBoundCalibratedCheckerSemantics
    scale_data input.lengthCodeAt

def finiteEnumeration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data) :
    InternalPudlakTheorem5CheckerFiniteEnumeration
      input.checkerSemantics :=
  input.toSingletonGapRejectionInput.finiteEnumeration

def rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      input.checkerSemantics input.finiteEnumeration :=
  input.toSingletonGapRejectionInput.toCheckerExtractor

/-- The search-only input builds the canonical proof-length-free search core:
concrete PA/Hilbert syntax, recognizer exactness, canonical checker interface,
finite enumeration, and computable rejection. -/
def toCanonicalSearchCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data) :
    PAHilbertCanonicalSearchCore where
  checker :=
    concretePAHilbertPowerBoundChecker scale_data
  semantics :=
    concretePAHilbertTheorem5DerivabilitySemantics
  recognizerExactness :=
    concretePAHilbertTheorem5AxiomRecognizerExactness
  canonicalInterface :=
    concretePAHilbertPowerBoundCanonicalCheckerInterface scale_data
  scale_data :=
    scale_data
  checkerSemantics :=
    input.checkerSemantics
  finiteEnumeration :=
    input.finiteEnumeration
  rejectionExtractor :=
    input.rejectionExtractor
  acceptedCodeExactness := by
    intro formulaCode code haccepted
    exact
      (concretePAHilbertPowerBoundCanonicalCheckerInterface scale_data)
        |>.accepted_decoded_code_to_formulaCode_derivable
          formulaCode code haccepted

def toProofLengthFreeMonth12Candidate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data) :
    Month12ProofLengthFreeCheckerSearchCandidate scale_data :=
  input.toCanonicalSearchCore.toProofLengthFreeMonth12Candidate

def toProofLengthAxiomFreeCheckedUpperProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (upper_provider :
      input.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfCanonicalSearchCoreCheckedUpper
    input.toCanonicalSearchCore upper_provider

theorem checkedUpperProvider_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (upper_provider :
      input.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType) :
    (input.toProofLengthAxiomFreeCheckedUpperProvider upper_provider).Audit ∧
      (input.toProofLengthAxiomFreeCheckedUpperProvider
        upper_provider).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (input.toProofLengthAxiomFreeCheckedUpperProvider
            upper_provider).computedCollisionNOfRationality hrat =
            input.rejectionExtractor.witness
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate upper_provider hrat).U
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate upper_provider hrat).polynomial
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate upper_provider hrat).upperN) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (checkedSearchUpperTail
              input.toProofLengthFreeMonth12Candidate upper_provider hrat).U
                ((input.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat) <
              month9_month10_checkedProofCodeMeasured
                scale_data input.checkerSemantics.toProofCodeSemantics
                ((input.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            month9_month10_checkedProofCodeMeasured
                scale_data input.checkerSemantics.toProofCodeSemantics
                ((input.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat) ≤
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate upper_provider hrat).U
                ((input.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    theorem5ProviderOfCanonicalSearchCoreCheckedUpper_closure
      input.toCanonicalSearchCore upper_provider

def toProjectUpperProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data input.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    input.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType :=
  projectUpperProviderForCanonicalSearchCore
    input.toCanonicalSearchCore projection project_upper

def toProofLengthAxiomFreeProjectUpperProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data input.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfCanonicalSearchCoreProjectUpper
    input.toCanonicalSearchCore projection project_upper

theorem projectUpperProvider_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data input.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (input.toProofLengthAxiomFreeProjectUpperProvider
      projection project_upper).Audit ∧
      (input.toProofLengthAxiomFreeProjectUpperProvider
        projection project_upper).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (input.toProofLengthAxiomFreeProjectUpperProvider
            projection project_upper).computedCollisionNOfRationality hrat =
            input.rejectionExtractor.witness
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toProjectUpperProvider projection project_upper)
                hrat).U
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toProjectUpperProvider projection project_upper)
                hrat).polynomial
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toProjectUpperProvider projection project_upper)
                hrat).upperN) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (checkedSearchUpperTail
              input.toProofLengthFreeMonth12Candidate
              (input.toProjectUpperProvider projection project_upper)
              hrat).U
                ((input.toProofLengthAxiomFreeProjectUpperProvider
                  projection project_upper).computedCollisionNOfRationality hrat) <
              month9_month10_checkedProofCodeMeasured
                scale_data input.checkerSemantics.toProofCodeSemantics
                ((input.toProofLengthAxiomFreeProjectUpperProvider
                  projection project_upper).computedCollisionNOfRationality hrat)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            month9_month10_checkedProofCodeMeasured
                scale_data input.checkerSemantics.toProofCodeSemantics
                ((input.toProofLengthAxiomFreeProjectUpperProvider
                  projection project_upper).computedCollisionNOfRationality hrat) ≤
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toProjectUpperProvider projection project_upper)
                hrat).U
                ((input.toProofLengthAxiomFreeProjectUpperProvider
                  projection project_upper).computedCollisionNOfRationality hrat)) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    theorem5ProviderOfCanonicalSearchCoreProjectUpper_closure
      input.toCanonicalSearchCore projection project_upper

def toPayloadFreeCheckedUpperProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data input.checkerSemantics.toProofCodeSemantics)
    (upper_provider : Month9Month10PayloadFreeUpperProvider) :
    input.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType :=
  checkedUpperProviderOfPayloadFreeUpperAndAdditiveProjection
    projection upper_provider

def toProofLengthAxiomFreePayloadFreeUpperProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data input.checkerSemantics.toProofCodeSemantics)
    (upper_provider : Month9Month10PayloadFreeUpperProvider) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper
    input.toCanonicalSearchCore projection upper_provider

theorem payloadFreeUpperProvider_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data input.checkerSemantics.toProofCodeSemantics)
    (upper_provider : Month9Month10PayloadFreeUpperProvider) :
    (input.toProofLengthAxiomFreePayloadFreeUpperProvider
      projection upper_provider).Audit ∧
      (input.toProofLengthAxiomFreePayloadFreeUpperProvider
        projection upper_provider).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (input.toProofLengthAxiomFreePayloadFreeUpperProvider
            projection upper_provider).computedCollisionNOfRationality hrat =
            input.rejectionExtractor.witness
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toPayloadFreeCheckedUpperProvider
                  projection upper_provider)
                hrat).U
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toPayloadFreeCheckedUpperProvider
                  projection upper_provider)
                hrat).polynomial
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toPayloadFreeCheckedUpperProvider
                  projection upper_provider)
                hrat).upperN) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (checkedSearchUpperTail
              input.toProofLengthFreeMonth12Candidate
              (input.toPayloadFreeCheckedUpperProvider
                projection upper_provider)
              hrat).U
                ((input.toProofLengthAxiomFreePayloadFreeUpperProvider
                  projection upper_provider).computedCollisionNOfRationality hrat) <
              month9_month10_checkedProofCodeMeasured
                scale_data input.checkerSemantics.toProofCodeSemantics
                ((input.toProofLengthAxiomFreePayloadFreeUpperProvider
                  projection upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            month9_month10_checkedProofCodeMeasured
                scale_data input.checkerSemantics.toProofCodeSemantics
                ((input.toProofLengthAxiomFreePayloadFreeUpperProvider
                  projection upper_provider).computedCollisionNOfRationality hrat) ≤
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toPayloadFreeCheckedUpperProvider
                  projection upper_provider)
                hrat).U
                ((input.toProofLengthAxiomFreePayloadFreeUpperProvider
                  projection upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    theorem5ProviderOfCanonicalSearchCorePayloadFreeUpper_closure
      input.toCanonicalSearchCore projection upper_provider

def toProofLengthAxiomFreeCLineMinimalProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data input.checkerSemantics.toProofCodeSemantics)
    (cline : Nonempty (SondowCLineMinimalClosureCertificate bounds)) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfCanonicalSearchCoreCLineMinimalClosure
    input.toCanonicalSearchCore projection cline

theorem cLineMinimalProvider_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data input.checkerSemantics.toProofCodeSemantics)
    (cline : Nonempty (SondowCLineMinimalClosureCertificate bounds)) :
    (input.toProofLengthAxiomFreeCLineMinimalProvider
      projection cline).Audit ∧
      (input.toProofLengthAxiomFreeCLineMinimalProvider
        projection cline).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (input.toProofLengthAxiomFreeCLineMinimalProvider
            projection cline).computedCollisionNOfRationality hrat =
            input.rejectionExtractor.witness
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (projectUpperProviderForCanonicalSearchCore
                  input.toCanonicalSearchCore projection
                  (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                    cline))
                hrat).U
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (projectUpperProviderForCanonicalSearchCore
                  input.toCanonicalSearchCore projection
                  (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                    cline))
                hrat).polynomial
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (projectUpperProviderForCanonicalSearchCore
                  input.toCanonicalSearchCore projection
                  (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                    cline))
                hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    theorem5ProviderOfCanonicalSearchCoreCLineMinimalClosure_closure
      input.toCanonicalSearchCore projection cline

theorem cLineKernelCheckerLengthProvider_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data input.checkerSemantics.toProofCodeSemantics)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    (theorem5ProviderOfCanonicalSearchCoreCLineKernelCheckerLength
      input.toCanonicalSearchCore projection hkernel hchecker hlength).Audit ∧
      ((theorem5ProviderOfCanonicalSearchCoreCLineKernelCheckerLength
        input.toCanonicalSearchCore projection hkernel hchecker hlength)
          |>.endpoint).Audit ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    theorem5ProviderOfCanonicalSearchCoreCLineKernelCheckerLength_closure
      input.toCanonicalSearchCore projection hkernel hchecker hlength

theorem canonicalSearchCore_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data) :
    Nonempty PAHilbertCanonicalSearchCore :=
  ⟨input.toCanonicalSearchCore⟩

theorem checkedGap_nonempty_of_upperProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (upper_provider :
      input.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType) :
    Nonempty
      (ComputableSearchGapCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data input.checkerSemantics.toProofCodeSemantics)) := by
  have hclosure :=
    PAHilbertCanonicalSearchCore.proofLengthFreeMonth12Candidate_closure
      input.toCanonicalSearchCore
      upper_provider
  exact hclosure.2.2.2.1

end ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput

/-! ## Minimal checked-upper residual frontier -/

/-- The current smallest theorem-5 residual frontier.  It has no root
`proof_length` transport, no project-box proof-length object, and no payload
vocabulary: the lower side is the concrete PA/Hilbert search input, and the
upper side is already stated for the same checked `minProofCodeSize`
measurement. -/
structure Month9Month10CheckedUpperInternalTheorem5Frontier
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  lower_search :
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput scale_data
  upper_provider :
    lower_search.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType

namespace Month9Month10CheckedUpperInternalTheorem5Frontier

def provider
    {scale_data : InternalPudlakTheorem5ScaleData}
    (frontier :
      Month9Month10CheckedUpperInternalTheorem5Frontier scale_data) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  frontier.lower_search.toProofLengthAxiomFreeCheckedUpperProvider
    frontier.upper_provider

def endpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    (frontier :
      Month9Month10CheckedUpperInternalTheorem5Frontier scale_data) :
    Month9Month10CheckedSearchCollisionEndpoint scale_data :=
  frontier.provider.endpoint

noncomputable def computedCollisionNOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    (frontier :
      Month9Month10CheckedUpperInternalTheorem5Frontier scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  frontier.provider.computedCollisionNOfRationality hrat

theorem computedCollisionN_eq_rejectionExtractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (frontier :
      Month9Month10CheckedUpperInternalTheorem5Frontier scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    frontier.computedCollisionNOfRationality hrat =
      frontier.lower_search.rejectionExtractor.witness
        (checkedSearchUpperTail
          frontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.upper_provider hrat).U
        (checkedSearchUpperTail
          frontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.upper_provider hrat).polynomial
        (checkedSearchUpperTail
          frontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.upper_provider hrat).upperN :=
  frontier.provider.computedCollisionN_eq_rejectionExtractorWitness hrat

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (frontier :
      Month9Month10CheckedUpperInternalTheorem5Frontier scale_data) :
    frontier.provider.Audit ∧
      frontier.endpoint.Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (month9_month10_checkedProofCodeMeasured
              scale_data
              frontier.lower_search.checkerSemantics.toProofCodeSemantics)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            frontier.computedCollisionNOfRationality hrat =
              frontier.lower_search.rejectionExtractor.witness
                (checkedSearchUpperTail
                  frontier.lower_search.toProofLengthFreeMonth12Candidate
                  frontier.upper_provider hrat).U
                (checkedSearchUpperTail
                  frontier.lower_search.toProofLengthFreeMonth12Candidate
                  frontier.upper_provider hrat).polynomial
                (checkedSearchUpperTail
                  frontier.lower_search.toProofLengthFreeMonth12Candidate
                  frontier.upper_provider hrat).upperN) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              (checkedSearchUpperTail
                frontier.lower_search.toProofLengthFreeMonth12Candidate
                frontier.upper_provider hrat).U
                  (frontier.computedCollisionNOfRationality hrat) <
                month9_month10_checkedProofCodeMeasured
                  scale_data
                  frontier.lower_search.checkerSemantics.toProofCodeSemantics
                  (frontier.computedCollisionNOfRationality hrat)) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              month9_month10_checkedProofCodeMeasured
                  scale_data
                  frontier.lower_search.checkerSemantics.toProofCodeSemantics
                  (frontier.computedCollisionNOfRationality hrat) ≤
                (checkedSearchUpperTail
                  frontier.lower_search.toProofLengthFreeMonth12Candidate
                  frontier.upper_provider hrat).U
                  (frontier.computedCollisionNOfRationality hrat)) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
            ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    frontier.lower_search.checkedUpperProvider_closure
      frontier.upper_provider
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      frontier.lower_search.checkedGap_nonempty_of_upperProvider
        frontier.upper_provider,
      hclosure.2.2.1,
      hclosure.2.2.2.1,
      hclosure.2.2.2.2.1,
      hclosure.2.2.2.2.2.1,
      hclosure.2.2.2.2.2.2⟩

end Month9Month10CheckedUpperInternalTheorem5Frontier

/-! ## Final-three-certificate instantiation -/

/-- Drop the proof-length transport field of a final three-certificate endpoint
when the target is the proof-length-free checked-search route.  The calibrated
core is still available for compatibility endpoints, but this projection keeps
only the checker/search data needed for computed-witness collision. -/
def finalThreeCanonicalSearchCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    PAHilbertCanonicalSearchCore :=
  PAHilbertCanonicalCalibratedExactnessCore.toCanonicalSearchCore
    endpoint.toCanonicalCalibratedExactnessCore

/-- Project-level entry point from the Month 11-12 final three-certificate
endpoint and the C-line upper closure to the proof-length-free checked-search
theorem-5 provider. -/
def theorem5ProviderOfFinalThreeCLineMinimalClosure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        (finalThreeCanonicalSearchCore endpoint).scale_data
        (finalThreeCanonicalSearchCore endpoint).checkerSemantics.toProofCodeSemantics)
    (cline : Nonempty (SondowCLineMinimalClosureCertificate bounds)) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfCanonicalSearchCoreCLineMinimalClosure
    (finalThreeCanonicalSearchCore endpoint) projection cline

theorem theorem5ProviderOfFinalThreeCLineMinimalClosure_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        (finalThreeCanonicalSearchCore endpoint).scale_data
        (finalThreeCanonicalSearchCore endpoint).checkerSemantics.toProofCodeSemantics)
    (cline : Nonempty (SondowCLineMinimalClosureCertificate bounds)) :
    Nonempty
        (ConcretePAHilbertPowerBoundFinalThreeCertificateDeliverables
          scale_data) ∧
      (theorem5ProviderOfFinalThreeCLineMinimalClosure
        endpoint projection cline).Audit ∧
        (theorem5ProviderOfFinalThreeCLineMinimalClosure
          endpoint projection cline).endpoint.Audit ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    theorem5ProviderOfCanonicalSearchCoreCLineMinimalClosure_closure
      (finalThreeCanonicalSearchCore endpoint) projection cline
  exact
    ⟨ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint.deliverables_nonempty
        endpoint,
      hclosure.1,
      hclosure.2.1,
      hclosure.2.2.2.1,
      hclosure.2.2.2.2⟩

/-- Final-three entry point with the C-line source split into its current three
concrete components. -/
def theorem5ProviderOfFinalThreeCLineKernelCheckerLength
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        (finalThreeCanonicalSearchCore endpoint).scale_data
        (finalThreeCanonicalSearchCore endpoint).checkerSemantics.toProofCodeSemantics)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfFinalThreeCLineMinimalClosure
    endpoint projection
    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
      hkernel hchecker hlength)

theorem theorem5ProviderOfFinalThreeCLineKernelCheckerLength_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        (finalThreeCanonicalSearchCore endpoint).scale_data
        (finalThreeCanonicalSearchCore endpoint).checkerSemantics.toProofCodeSemantics)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    Nonempty
        (ConcretePAHilbertPowerBoundFinalThreeCertificateDeliverables
          scale_data) ∧
      (theorem5ProviderOfFinalThreeCLineKernelCheckerLength
        endpoint projection hkernel hchecker hlength).Audit ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    theorem5ProviderOfFinalThreeCLineMinimalClosure_closure
      endpoint projection
      (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
        hkernel hchecker hlength)
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.2.1,
      hclosure.2.2.2.2⟩

end SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint
end SondowMainCheckedCodeBridge
