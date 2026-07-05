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

/-! ## Generic checked-target upper instantiation -/

/-- Generic checked-target projection for theorem 5.  It separates the
source-to-target `+2` proof from any particular local-Hilbert realization, so a
future internal checker proof can instantiate it without unfolding payload or
root proof-length vocabulary. -/
structure InternalPudlakTheorem5CheckedTargetProjection
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (targetMeasured : Nat → Nat) : Prop where
  source_le_target_add_two :
    ∀ m : Nat,
      sem.minProofCodeSize (scale_data.powerBoundRawCode m) ⟨m, rfl⟩ ≤
        targetMeasured m + 2

/-- Polynomial upper provider for an abstract checked target measurement. -/
structure InternalPudlakTheorem5CheckedTargetUpperProvider
    (targetMeasured : Nat → Nat) : Type where
  upper_under_rationality :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat, ∀ m : Nat, upperN ≤ m →
          (targetMeasured m : Real) ≤ U m

namespace InternalPudlakTheorem5CheckedTargetUpperProvider

structure Audit
    {targetMeasured : Nat → Nat}
    (upper_provider :
      InternalPudlakTheorem5CheckedTargetUpperProvider targetMeasured) :
    Prop where
  upperUnderRationality :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat, ∀ m : Nat, upperN ≤ m →
          (targetMeasured m : Real) ≤ U m

theorem audit
    {targetMeasured : Nat → Nat}
    (upper_provider :
      InternalPudlakTheorem5CheckedTargetUpperProvider targetMeasured) :
    upper_provider.Audit where
  upperUnderRationality := upper_provider.upper_under_rationality

theorem closure
    {targetMeasured : Nat → Nat}
    (upper_provider :
      InternalPudlakTheorem5CheckedTargetUpperProvider targetMeasured) :
    upper_provider.Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ m : Nat, upperN ≤ m →
            (targetMeasured m : Real) ≤ U m) :=
  ⟨upper_provider.audit, upper_provider.upper_under_rationality⟩

end InternalPudlakTheorem5CheckedTargetUpperProvider

/-- Transport an abstract checked-target upper bound to the theorem-5 checked
source measurement through a source-to-target `+2` projection. -/
def checkedUpperProviderOfCheckedTargetProjectionAndUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {targetMeasured : Nat → Nat}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        scale_data sem targetMeasured)
    (upper_provider :
      InternalPudlakTheorem5CheckedTargetUpperProvider
        targetMeasured) :
    Month9Month10AbstractMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured scale_data sem) where
  upper_under_rationality := by
    intro hrat
    rcases upper_provider.upper_under_rationality hrat with
      ⟨U, hU, upperN, hupper⟩
    refine
      ⟨fun m => U m + 2,
        _root_.is_polynomial_bound_add_const hU (by norm_num),
        upperN,
        ?_⟩
    intro m hm
    have hsource :
        (sem.minProofCodeSize (scale_data.powerBoundRawCode m)
          ⟨m, rfl⟩ : Real) ≤ (targetMeasured m : Real) + 2 := by
      exact_mod_cast projection.source_le_target_add_two m
    have htarget := hupper m hm
    have hchecked :
        (sem.minProofCodeSize (scale_data.powerBoundRawCode m)
          ⟨m, rfl⟩ : Real) ≤ U m + 2 := by
      nlinarith
    simpa [month9_month10_checkedProofCodeMeasured] using hchecked

theorem checkedUpperProviderOfCheckedTargetProjectionAndUpper_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {targetMeasured : Nat → Nat}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        scale_data sem targetMeasured)
    (upper_provider :
      InternalPudlakTheorem5CheckedTargetUpperProvider
        targetMeasured) :
    (checkedUpperProviderOfCheckedTargetProjectionAndUpper
      projection upper_provider).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ m : Nat, upperN ≤ m →
            month9_month10_checkedProofCodeMeasured scale_data sem m ≤
              U m) :=
  (checkedUpperProviderOfCheckedTargetProjectionAndUpper
    projection upper_provider).closure

/-- Theorem-5 provider from a generic checked-target projection and target
upper provider. -/
def theorem5ProviderOfCanonicalSearchCoreCheckedTargetUpper
    (core : PAHilbertCanonicalSearchCore)
    {targetMeasured : Nat → Nat}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        targetMeasured)
    (upper_provider :
      InternalPudlakTheorem5CheckedTargetUpperProvider
        targetMeasured) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfCanonicalSearchCoreCheckedUpper core
    (checkedUpperProviderOfCheckedTargetProjectionAndUpper
      projection upper_provider)

theorem theorem5ProviderOfCanonicalSearchCoreCheckedTargetUpper_closure
    (core : PAHilbertCanonicalSearchCore)
    {targetMeasured : Nat → Nat}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        targetMeasured)
    (upper_provider :
      InternalPudlakTheorem5CheckedTargetUpperProvider
        targetMeasured) :
    (theorem5ProviderOfCanonicalSearchCoreCheckedTargetUpper
      core projection upper_provider).Audit ∧
      (theorem5ProviderOfCanonicalSearchCoreCheckedTargetUpper
        core projection upper_provider).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (theorem5ProviderOfCanonicalSearchCoreCheckedTargetUpper
            core projection upper_provider).computedCollisionNOfRationality hrat =
            core.rejectionExtractor.witness
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (checkedUpperProviderOfCheckedTargetProjectionAndUpper
                  projection upper_provider)
                hrat).U
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (checkedUpperProviderOfCheckedTargetProjectionAndUpper
                  projection upper_provider)
                hrat).polynomial
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (checkedUpperProviderOfCheckedTargetProjectionAndUpper
                  projection upper_provider)
                hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    theorem5ProviderOfCanonicalSearchCoreCheckedUpper_closure
      core
      (checkedUpperProviderOfCheckedTargetProjectionAndUpper
        projection upper_provider)
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.1,
      hclosure.2.2.2.2.2.1,
      hclosure.2.2.2.2.2.2⟩

/-! ## Concrete-proof-family checked target upper instantiation -/

/-- Payload-free projection for a raw MiniHilbert concrete proof family.  Unlike
`FormulaCodeHilbertInterpretation`, this object does not carry a
`HilbertProjectionCodeAlignment`, so the only remaining input is the concrete
conjunction-family proof object and the theorem-5 source identification. -/
structure InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)) :
    Prop where
  theorem5_source_eq_family_source :
    ∀ m : Nat,
      sem.minProofCodeSize (scale_data.powerBoundRawCode m) ⟨m, rfl⟩ =
        target_family.rightConjElim.minCheckedCodeSize m

namespace InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection

def targetMeasured
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)) :
    Nat → Nat :=
  fun m => target_family.minCheckedCodeSize m

def toCheckedTargetProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        scale_data sem target_family) :
    InternalPudlakTheorem5CheckedTargetProjection
      scale_data sem (targetMeasured target_family) where
  source_le_target_add_two := by
    intro m
    rw [projection.theorem5_source_eq_family_source m]
    simpa [targetMeasured] using
      target_family.minCheckedCodeSize_rightConjElim_le m

end InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection

/-- Upper provider for a raw MiniHilbert conjunction-family checked minimum. -/
structure InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)) :
    Type (max u v w) where
  upper_under_rationality :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat, ∀ m : Nat, upperN ≤ m →
          (target_family.minCheckedCodeSize m : Real) ≤ U m

namespace InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider

def toCheckedTargetUpperProvider
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family) :
    InternalPudlakTheorem5CheckedTargetUpperProvider
      (InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection.targetMeasured
        target_family) where
  upper_under_rationality := by
    intro hrat
    simpa
      [InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection.targetMeasured]
      using upper_provider.upper_under_rationality hrat

structure Audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family) :
    Prop where
  upperUnderRationality :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat, ∀ m : Nat, upperN ≤ m →
          (target_family.minCheckedCodeSize m : Real) ≤ U m

theorem audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family) :
    upper_provider.Audit where
  upperUnderRationality := upper_provider.upper_under_rationality

theorem closure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family) :
    upper_provider.Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ m : Nat, upperN ≤ m →
            (target_family.minCheckedCodeSize m : Real) ≤ U m) :=
  ⟨upper_provider.audit, upper_provider.upper_under_rationality⟩

end InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider

def concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (hpoly :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real target_family.length)) :
    InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
      target_family where
  upper_under_rationality := by
    intro _hrat
    refine
      ⟨_root_.MiniHilbert.nat_bound_as_real target_family.length,
        hpoly, 0, ?_⟩
    intro m _hm
    have hmin :
        target_family.minCheckedCodeSize m ≤ target_family.length m := by
      rw [_root_.MiniHilbert.ConcreteProofFamily.minCheckedCodeSize_eq_minLength]
      exact target_family.minLength_le_length m
    have hminReal :
        (target_family.minCheckedCodeSize m : Real) ≤
          (target_family.length m : Real) := by
      exact_mod_cast hmin
    simpa [_root_.MiniHilbert.nat_bound_as_real] using hminReal

def checkedUpperProviderOfConcreteProofFamilyProjectionAndTargetUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        scale_data sem target_family)
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family) :
    Month9Month10AbstractMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured scale_data sem) :=
  checkedUpperProviderOfCheckedTargetProjectionAndUpper
    projection.toCheckedTargetProjection
    upper_provider.toCheckedTargetUpperProvider

theorem checkedUpperProviderOfConcreteProofFamilyProjectionAndTargetUpper_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        scale_data sem target_family)
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family) :
    (checkedUpperProviderOfConcreteProofFamilyProjectionAndTargetUpper
      projection upper_provider).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ m : Nat, upperN ≤ m →
            month9_month10_checkedProofCodeMeasured scale_data sem m ≤
              U m) :=
  (checkedUpperProviderOfConcreteProofFamilyProjectionAndTargetUpper
    projection upper_provider).closure

/-- Theorem-5 provider using the payload-free concrete-proof-family target. -/
def theorem5ProviderOfCanonicalSearchCoreConcreteProofFamilyTargetUpper
    (core : PAHilbertCanonicalSearchCore)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        target_family)
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfCanonicalSearchCoreCheckedTargetUpper core
    projection.toCheckedTargetProjection
    upper_provider.toCheckedTargetUpperProvider

theorem theorem5ProviderOfCanonicalSearchCoreConcreteProofFamilyTargetUpper_closure
    (core : PAHilbertCanonicalSearchCore)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        target_family)
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family) :
    (theorem5ProviderOfCanonicalSearchCoreConcreteProofFamilyTargetUpper
      core projection upper_provider).Audit ∧
      (theorem5ProviderOfCanonicalSearchCoreConcreteProofFamilyTargetUpper
        core projection upper_provider).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (theorem5ProviderOfCanonicalSearchCoreConcreteProofFamilyTargetUpper
            core projection upper_provider).computedCollisionNOfRationality
              hrat =
            core.rejectionExtractor.witness
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (checkedUpperProviderOfConcreteProofFamilyProjectionAndTargetUpper
                  projection upper_provider)
                hrat).U
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (checkedUpperProviderOfConcreteProofFamilyProjectionAndTargetUpper
                  projection upper_provider)
                hrat).polynomial
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (checkedUpperProviderOfConcreteProofFamilyProjectionAndTargetUpper
                  projection upper_provider)
                hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    theorem5ProviderOfCanonicalSearchCoreCheckedTargetUpper_closure
      core
      projection.toCheckedTargetProjection
      upper_provider.toCheckedTargetUpperProvider
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.1,
      hclosure.2.2.2.1,
      hclosure.2.2.2.2⟩

/-! ## Local-Hilbert checked target upper instantiation -/

/-- Local-Hilbert source projection for the checked theorem-5 measurement.  This
is the proof-length-free half of
`InternalPudlakTheorem5LocalHilbertProjectBoxProjection`: it keeps the
theorem-5 source identification and the local `source ≤ target + 2` projection,
but deliberately does not identify the target with the root proof-length
project box. -/
structure InternalPudlakTheorem5LocalHilbertCheckedTargetProjection
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Prop where
  local_projection :
    _root_.MiniHilbert.LocalHilbertProofCodeProjectionModel interp
  theorem5_source_eq_local_source :
    ∀ m : Nat,
      sem.minProofCodeSize (scale_data.powerBoundRawCode m) ⟨m, rfl⟩ =
        interp.localHilbertProofCodeSemantics.minProofCodeSize
          (_root_.partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)

namespace InternalPudlakTheorem5LocalHilbertCheckedTargetProjection

def targetMeasured
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nat → Nat :=
  fun m =>
    interp.localHilbertProofCodeSemantics.minProofCodeSize
      (_root_.sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)

def toCheckedTargetProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertCheckedTargetProjection
        scale_data sem interp) :
    InternalPudlakTheorem5CheckedTargetProjection
      scale_data sem (targetMeasured interp) where
  source_le_target_add_two := by
    intro m
    rw [projection.theorem5_source_eq_local_source m]
    exact projection.local_projection.source_le_target_add_two m

end InternalPudlakTheorem5LocalHilbertCheckedTargetProjection

/-- Upper provider for the local-Hilbert target checked size.  This is the
checked-code version of the Sondow upper route target: it bounds the local
reflection-graft target minimum directly, without mentioning root
`proof_length`. -/
structure InternalPudlakTheorem5LocalHilbertCheckedTargetUpperProvider
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Type (max u v w) where
  upper_under_rationality :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat, ∀ m : Nat, upperN ≤ m →
          (interp.localHilbertProofCodeSemantics.minProofCodeSize
            (_root_.sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) :
            Real) ≤ U m

namespace InternalPudlakTheorem5LocalHilbertCheckedTargetUpperProvider

structure Audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (upper_provider :
      InternalPudlakTheorem5LocalHilbertCheckedTargetUpperProvider interp) :
    Prop where
  upperUnderRationality :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat, ∀ m : Nat, upperN ≤ m →
          (interp.localHilbertProofCodeSemantics.minProofCodeSize
            (_root_.sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) :
            Real) ≤ U m

theorem audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (upper_provider :
      InternalPudlakTheorem5LocalHilbertCheckedTargetUpperProvider interp) :
    upper_provider.Audit where
  upperUnderRationality := upper_provider.upper_under_rationality

theorem closure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (upper_provider :
      InternalPudlakTheorem5LocalHilbertCheckedTargetUpperProvider interp) :
    upper_provider.Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ m : Nat, upperN ≤ m →
            (interp.localHilbertProofCodeSemantics.minProofCodeSize
              (_root_.sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) :
              Real) ≤ U m) :=
  ⟨upper_provider.audit, upper_provider.upper_under_rationality⟩

end InternalPudlakTheorem5LocalHilbertCheckedTargetUpperProvider

/-- Transport a local-Hilbert target upper provider through the local projection
to the theorem-5 checked source measurement.  This is the checked-code analogue
of the project-box upper bridge and does not unfold the root proof-length box. -/
def checkedUpperProviderOfLocalHilbertProjectionAndTargetUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertCheckedTargetProjection
        scale_data sem interp)
    (upper_provider :
      InternalPudlakTheorem5LocalHilbertCheckedTargetUpperProvider
        interp) :
    Month9Month10AbstractMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured scale_data sem) where
  upper_under_rationality := by
    intro hrat
    rcases upper_provider.upper_under_rationality hrat with
      ⟨U, hU, upperN, hupper⟩
    refine
      ⟨fun m => U m + 2,
        _root_.is_polynomial_bound_add_const hU (by norm_num),
        upperN,
        ?_⟩
    intro m hm
    have hlocal :
        (interp.localHilbertProofCodeSemantics.minProofCodeSize
          (_root_.partialConsistencyCode m) (Or.inl ⟨m, rfl⟩) : Real) ≤
          (interp.localHilbertProofCodeSemantics.minProofCodeSize
            (_root_.sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) :
            Real) + 2 := by
      exact_mod_cast projection.local_projection.source_le_target_add_two m
    have htarget := hupper m hm
    have hchecked :
        (sem.minProofCodeSize (scale_data.powerBoundRawCode m)
          ⟨m, rfl⟩ : Real) ≤ U m + 2 := by
      rw [projection.theorem5_source_eq_local_source m]
      nlinarith
    simpa [month9_month10_checkedProofCodeMeasured] using hchecked

theorem checkedUpperProviderOfLocalHilbertProjectionAndTargetUpper_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertCheckedTargetProjection
        scale_data sem interp)
    (upper_provider :
      InternalPudlakTheorem5LocalHilbertCheckedTargetUpperProvider
        interp) :
    (checkedUpperProviderOfLocalHilbertProjectionAndTargetUpper
      projection upper_provider).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat, ∀ m : Nat, upperN ≤ m →
            month9_month10_checkedProofCodeMeasured scale_data sem m ≤
              U m) :=
  (checkedUpperProviderOfLocalHilbertProjectionAndTargetUpper
    projection upper_provider).closure

/-- Theorem-5 provider using the local-Hilbert checked target upper route. -/
def theorem5ProviderOfCanonicalSearchCoreLocalHilbertTargetUpper
    (core : PAHilbertCanonicalSearchCore)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertCheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics interp)
    (upper_provider :
      InternalPudlakTheorem5LocalHilbertCheckedTargetUpperProvider
        interp) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfCanonicalSearchCoreCheckedUpper core
    (checkedUpperProviderOfLocalHilbertProjectionAndTargetUpper
      projection upper_provider)

theorem theorem5ProviderOfCanonicalSearchCoreLocalHilbertTargetUpper_closure
    (core : PAHilbertCanonicalSearchCore)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertCheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics interp)
    (upper_provider :
      InternalPudlakTheorem5LocalHilbertCheckedTargetUpperProvider
        interp) :
    (theorem5ProviderOfCanonicalSearchCoreLocalHilbertTargetUpper
      core projection upper_provider).Audit ∧
      (theorem5ProviderOfCanonicalSearchCoreLocalHilbertTargetUpper
        core projection upper_provider).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (theorem5ProviderOfCanonicalSearchCoreLocalHilbertTargetUpper
            core projection upper_provider).computedCollisionNOfRationality hrat =
            core.rejectionExtractor.witness
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (checkedUpperProviderOfLocalHilbertProjectionAndTargetUpper
                  projection upper_provider)
                hrat).U
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (checkedUpperProviderOfLocalHilbertProjectionAndTargetUpper
                  projection upper_provider)
                hrat).polynomial
              (checkedSearchUpperTail
                core.toProofLengthFreeMonth12Candidate
                (checkedUpperProviderOfLocalHilbertProjectionAndTargetUpper
                  projection upper_provider)
                hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    theorem5ProviderOfCanonicalSearchCoreCheckedUpper_closure
      core
      (checkedUpperProviderOfLocalHilbertProjectionAndTargetUpper
        projection upper_provider)
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.1,
      hclosure.2.2.2.2.2.1,
      hclosure.2.2.2.2.2.2⟩

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

/-- Direct checked-measured gap generated by the singleton calibrated checker.
This replaces the old actual-proof-length transport target when the route is
kept entirely on checked proof-code size. -/
def checkedMeasuredGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data) :
    ComputableSearchGapCertificate
      (month9_month10_checkedProofCodeMeasured
        scale_data input.checkerSemantics.toProofCodeSemantics) :=
  month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
    input.rejectionExtractor.toComputableFiniteSearchExclusion

theorem checkedMeasuredGap_witness_eq_inputGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((input.checkedMeasuredGap.gap_for_polynomial_upper U hU).witness N) =
      ((input.gap.gap_for_polynomial_upper U hU).witness N) :=
  rfl

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

theorem checkedUpperProvider_computedCollisionN_eq_checkedMeasuredGapWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    (upper_provider :
      input.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (input.toProofLengthAxiomFreeCheckedUpperProvider
      upper_provider).computedCollisionNOfRationality hrat =
      ((input.checkedMeasuredGap.gap_for_polynomial_upper
        (checkedSearchUpperTail
          input.toProofLengthFreeMonth12Candidate upper_provider hrat).U
        (checkedSearchUpperTail
          input.toProofLengthFreeMonth12Candidate upper_provider hrat).polynomial).witness
        (checkedSearchUpperTail
          input.toProofLengthFreeMonth12Candidate upper_provider hrat).upperN) := by
  let tail :=
    checkedSearchUpperTail
      input.toProofLengthFreeMonth12Candidate upper_provider hrat
  calc
    (input.toProofLengthAxiomFreeCheckedUpperProvider
      upper_provider).computedCollisionNOfRationality hrat
        = input.rejectionExtractor.witness tail.U tail.polynomial tail.upperN :=
          (input.toProofLengthAxiomFreeCheckedUpperProvider
            upper_provider).computedCollisionN_eq_rejectionExtractorWitness hrat
    _ = ((input.gap.gap_for_polynomial_upper tail.U tail.polynomial).witness
          tail.upperN) := rfl
    _ = ((input.checkedMeasuredGap.gap_for_polynomial_upper tail.U tail.polynomial).witness
          tail.upperN) := by
          exact (input.checkedMeasuredGap_witness_eq_inputGap
            tail.U tail.polynomial tail.upperN).symm

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

def concreteProofFamilyProjectionOfLengthCodeAtEq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (hsource :
      ∀ m : Nat,
        input.lengthCodeAt m =
          target_family.rightConjElim.minCheckedCodeSize m) :
    InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
      scale_data input.checkerSemantics.toProofCodeSemantics
      target_family where
  theorem5_source_eq_family_source := by
    intro m
    change input.checkerSemantics.minProofCodeSizeAt m =
      target_family.rightConjElim.minCheckedCodeSize m
    have hmin :
        input.checkerSemantics.minProofCodeSizeAt m =
          input.lengthCodeAt m :=
      concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
        scale_data input.lengthCodeAt m input.powerBoundRawCode_injective
    exact hmin.trans (hsource m)

def toConcreteProofFamilyCheckedUpperProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        scale_data input.checkerSemantics.toProofCodeSemantics
        target_family)
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family) :
    input.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType :=
  checkedUpperProviderOfConcreteProofFamilyProjectionAndTargetUpper
    projection upper_provider

def toProofLengthAxiomFreeConcreteProofFamilyTargetProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        scale_data input.checkerSemantics.toProofCodeSemantics
        target_family)
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfCanonicalSearchCoreConcreteProofFamilyTargetUpper
    input.toCanonicalSearchCore projection upper_provider

theorem concreteProofFamilyTargetProvider_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        scale_data input.checkerSemantics.toProofCodeSemantics
        target_family)
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family) :
    (input.toProofLengthAxiomFreeConcreteProofFamilyTargetProvider
      projection upper_provider).Audit ∧
      (input.toProofLengthAxiomFreeConcreteProofFamilyTargetProvider
        projection upper_provider).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (input.toProofLengthAxiomFreeConcreteProofFamilyTargetProvider
            projection upper_provider).computedCollisionNOfRationality hrat =
            input.rejectionExtractor.witness
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toConcreteProofFamilyCheckedUpperProvider
                  projection upper_provider)
                hrat).U
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toConcreteProofFamilyCheckedUpperProvider
                  projection upper_provider)
                hrat).polynomial
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toConcreteProofFamilyCheckedUpperProvider
                  projection upper_provider)
                hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    theorem5ProviderOfCanonicalSearchCoreConcreteProofFamilyTargetUpper_closure
      input.toCanonicalSearchCore projection upper_provider

def toProofLengthAxiomFreeConcreteProofFamilyLengthPolynomialProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        scale_data input.checkerSemantics.toProofCodeSemantics
        target_family)
    (hpoly :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real target_family.length)) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  input.toProofLengthAxiomFreeConcreteProofFamilyTargetProvider
    projection
    (concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial hpoly)

def toProofLengthAxiomFreeConcreteProofFamilyLengthPolynomialProviderOfEq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (hsource :
      ∀ m : Nat,
        input.lengthCodeAt m =
          target_family.rightConjElim.minCheckedCodeSize m)
    (hpoly :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real target_family.length)) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  input.toProofLengthAxiomFreeConcreteProofFamilyLengthPolynomialProvider
    (input.concreteProofFamilyProjectionOfLengthCodeAtEq hsource)
    hpoly

theorem concreteProofFamilyLengthPolynomialProviderOfEq_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (hsource :
      ∀ m : Nat,
        input.lengthCodeAt m =
          target_family.rightConjElim.minCheckedCodeSize m)
    (hpoly :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real target_family.length)) :
    (input.toProofLengthAxiomFreeConcreteProofFamilyLengthPolynomialProviderOfEq
      hsource hpoly).Audit ∧
      (input.toProofLengthAxiomFreeConcreteProofFamilyLengthPolynomialProviderOfEq
        hsource hpoly).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (input.toProofLengthAxiomFreeConcreteProofFamilyLengthPolynomialProviderOfEq
            hsource hpoly).computedCollisionNOfRationality hrat =
            input.rejectionExtractor.witness
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toConcreteProofFamilyCheckedUpperProvider
                  (input.concreteProofFamilyProjectionOfLengthCodeAtEq hsource)
                  (concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial
                    hpoly))
                hrat).U
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toConcreteProofFamilyCheckedUpperProvider
                  (input.concreteProofFamilyProjectionOfLengthCodeAtEq hsource)
                  (concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial
                    hpoly))
                hrat).polynomial
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toConcreteProofFamilyCheckedUpperProvider
                  (input.concreteProofFamilyProjectionOfLengthCodeAtEq hsource)
                  (concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial
                    hpoly))
                hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    input.concreteProofFamilyTargetProvider_closure
      (input.concreteProofFamilyProjectionOfLengthCodeAtEq hsource)
      (concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial hpoly)

theorem concreteProofFamilyLengthPolynomialProvider_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
        scale_data)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        scale_data input.checkerSemantics.toProofCodeSemantics
        target_family)
    (hpoly :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real target_family.length)) :
    (input.toProofLengthAxiomFreeConcreteProofFamilyLengthPolynomialProvider
      projection hpoly).Audit ∧
      (input.toProofLengthAxiomFreeConcreteProofFamilyLengthPolynomialProvider
        projection hpoly).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (input.toProofLengthAxiomFreeConcreteProofFamilyLengthPolynomialProvider
            projection hpoly).computedCollisionNOfRationality hrat =
            input.rejectionExtractor.witness
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toConcreteProofFamilyCheckedUpperProvider
                  projection
                  (concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial
                    hpoly))
                hrat).U
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toConcreteProofFamilyCheckedUpperProvider
                  projection
                  (concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial
                    hpoly))
                hrat).polynomial
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate
                (input.toConcreteProofFamilyCheckedUpperProvider
                  projection
                  (concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial
                    hpoly))
                hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    input.concreteProofFamilyTargetProvider_closure projection
      (concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial hpoly)

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

/-! ## Concrete-proof-family target frontier -/

/-- The payload-free concrete target frontier.  It replaces the opaque
checked-upper residual by two auditable proof-family fields: theorem-5 source
exactness against the right-conjunction-elimination family, and a Sondow upper
bound for the target conjunction-family checked minimum. -/
structure Month9Month10ConcreteProofFamilyTargetInternalTheorem5Frontier
    (scale_data : InternalPudlakTheorem5ScaleData)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)) :
    Type (max u v w) where
  lower_search :
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput scale_data
  projection :
    InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
      scale_data lower_search.checkerSemantics.toProofCodeSemantics
      target_family
  upper_provider :
    InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
      target_family

namespace Month9Month10ConcreteProofFamilyTargetInternalTheorem5Frontier

def provider
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteProofFamilyTargetInternalTheorem5Frontier
        scale_data target_family) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  theorem5ProviderOfCanonicalSearchCoreConcreteProofFamilyTargetUpper
    frontier.lower_search.toCanonicalSearchCore
    frontier.projection
    frontier.upper_provider

def endpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteProofFamilyTargetInternalTheorem5Frontier
        scale_data target_family) :
    Month9Month10CheckedSearchCollisionEndpoint scale_data :=
  frontier.provider.endpoint

noncomputable def computedCollisionNOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteProofFamilyTargetInternalTheorem5Frontier
        scale_data target_family)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  frontier.provider.computedCollisionNOfRationality hrat

def checkedUpperProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteProofFamilyTargetInternalTheorem5Frontier
        scale_data target_family) :
    frontier.lower_search.toProofLengthFreeMonth12Candidate
      |>.checkedMeasuredUpperProviderType :=
  checkedUpperProviderOfConcreteProofFamilyProjectionAndTargetUpper
    frontier.projection frontier.upper_provider

theorem computedCollisionN_eq_rejectionExtractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteProofFamilyTargetInternalTheorem5Frontier
        scale_data target_family)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    frontier.computedCollisionNOfRationality hrat =
      frontier.lower_search.rejectionExtractor.witness
        (checkedSearchUpperTail
          frontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.checkedUpperProvider hrat).U
        (checkedSearchUpperTail
          frontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.checkedUpperProvider hrat).polynomial
        (checkedSearchUpperTail
          frontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.checkedUpperProvider hrat).upperN :=
  frontier.provider.computedCollisionN_eq_rejectionExtractorWitness hrat

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteProofFamilyTargetInternalTheorem5Frontier
        scale_data target_family) :
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
                  frontier.checkedUpperProvider hrat).U
                (checkedSearchUpperTail
                  frontier.lower_search.toProofLengthFreeMonth12Candidate
                  frontier.checkedUpperProvider hrat).polynomial
                (checkedSearchUpperTail
                  frontier.lower_search.toProofLengthFreeMonth12Candidate
                  frontier.checkedUpperProvider hrat).upperN) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              (checkedSearchUpperTail
                frontier.lower_search.toProofLengthFreeMonth12Candidate
                frontier.checkedUpperProvider hrat).U
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
                  frontier.checkedUpperProvider hrat).U
                  (frontier.computedCollisionNOfRationality hrat)) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
            ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure := frontier.provider.closure
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      frontier.lower_search.checkedGap_nonempty_of_upperProvider
        frontier.checkedUpperProvider,
      hclosure.2.2.2.2.1,
      hclosure.2.2.2.2.2.2.1,
      hclosure.2.2.2.2.2.2.2.1,
      hclosure.2.2.2.2.2.2.2.2.1,
      hclosure.2.2.2.2.2.2.2.2.2⟩

end Month9Month10ConcreteProofFamilyTargetInternalTheorem5Frontier

/-! ## Concrete length-code target frontier -/

/-- Smaller concrete target frontier after eliminating the projection and upper
provider wrappers.  The remaining fields are the real proof obligations: the
chosen checker length code is exactly the right-conjunction-elimination
checked minimum, and the target proof-family length has a polynomial bound. -/
structure Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier
    (scale_data : InternalPudlakTheorem5ScaleData)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)) :
    Type (max u v w) where
  lower_search :
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput scale_data
  lengthCodeAt_eq_family_source :
    ∀ m : Nat,
      lower_search.lengthCodeAt m =
        target_family.rightConjElim.minCheckedCodeSize m
  target_length_polynomial :
    _root_.is_polynomial_bound
      (_root_.MiniHilbert.nat_bound_as_real target_family.length)

namespace Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier

def provider
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier
        scale_data target_family) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  frontier.lower_search
    |>.toProofLengthAxiomFreeConcreteProofFamilyLengthPolynomialProviderOfEq
      frontier.lengthCodeAt_eq_family_source
      frontier.target_length_polynomial

def endpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier
        scale_data target_family) :
    Month9Month10CheckedSearchCollisionEndpoint scale_data :=
  frontier.provider.endpoint

noncomputable def computedCollisionNOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier
        scale_data target_family)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  frontier.provider.computedCollisionNOfRationality hrat

def projection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier
        scale_data target_family) :
    InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
      scale_data
      frontier.lower_search.checkerSemantics.toProofCodeSemantics
      target_family :=
  frontier.lower_search.concreteProofFamilyProjectionOfLengthCodeAtEq
    frontier.lengthCodeAt_eq_family_source

def upperProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier
        scale_data target_family) :
    InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
      target_family :=
  concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial
    frontier.target_length_polynomial

theorem computedCollisionN_eq_rejectionExtractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier
        scale_data target_family)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    frontier.computedCollisionNOfRationality hrat =
      frontier.lower_search.rejectionExtractor.witness
        (checkedSearchUpperTail
          frontier.lower_search.toProofLengthFreeMonth12Candidate
          (frontier.lower_search.toConcreteProofFamilyCheckedUpperProvider
            frontier.projection frontier.upperProvider)
          hrat).U
        (checkedSearchUpperTail
          frontier.lower_search.toProofLengthFreeMonth12Candidate
          (frontier.lower_search.toConcreteProofFamilyCheckedUpperProvider
            frontier.projection frontier.upperProvider)
          hrat).polynomial
        (checkedSearchUpperTail
          frontier.lower_search.toProofLengthFreeMonth12Candidate
          (frontier.lower_search.toConcreteProofFamilyCheckedUpperProvider
            frontier.projection frontier.upperProvider)
          hrat).upperN :=
  frontier.provider.computedCollisionN_eq_rejectionExtractorWitness hrat

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier
        scale_data target_family) :
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
                  (frontier.lower_search.toConcreteProofFamilyCheckedUpperProvider
                    frontier.projection frontier.upperProvider)
                  hrat).U
                (checkedSearchUpperTail
                  frontier.lower_search.toProofLengthFreeMonth12Candidate
                  (frontier.lower_search.toConcreteProofFamilyCheckedUpperProvider
                    frontier.projection frontier.upperProvider)
                  hrat).polynomial
                (checkedSearchUpperTail
                  frontier.lower_search.toProofLengthFreeMonth12Candidate
                  (frontier.lower_search.toConcreteProofFamilyCheckedUpperProvider
                    frontier.projection frontier.upperProvider)
                  hrat).upperN) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              (checkedSearchUpperTail
                frontier.lower_search.toProofLengthFreeMonth12Candidate
                (frontier.lower_search.toConcreteProofFamilyCheckedUpperProvider
                  frontier.projection frontier.upperProvider)
                hrat).U
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
                  (frontier.lower_search.toConcreteProofFamilyCheckedUpperProvider
                    frontier.projection frontier.upperProvider)
                  hrat).U
                  (frontier.computedCollisionNOfRationality hrat)) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
            ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure := frontier.provider.closure
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      frontier.lower_search.checkedGap_nonempty_of_upperProvider
        (frontier.lower_search.toConcreteProofFamilyCheckedUpperProvider
          frontier.projection frontier.upperProvider),
      hclosure.2.2.2.2.1,
      hclosure.2.2.2.2.2.2.1,
      hclosure.2.2.2.2.2.2.2.1,
      hclosure.2.2.2.2.2.2.2.2.1,
      hclosure.2.2.2.2.2.2.2.2.2⟩

end Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier

/-! ## Conj-intro concrete target frontier -/

/-- Concrete target frontier where the conjunction proof family is built from
two component proof families.  This removes the standalone target polynomial
field from the previous frontier: polynomial length of the conjunction family
is derived by `ConcreteProofFamily.conjIntro_length_polynomial`. -/
structure Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier
    (scale_data : InternalPudlakTheorem5ScaleData)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n} :
    Type (max u v w) where
  left_family :
    _root_.MiniHilbert.ConcreteProofFamily Ax A
  right_family :
    _root_.MiniHilbert.ConcreteProofFamily Ax B
  lower_search :
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput scale_data
  lengthCodeAt_eq_conj_source :
    ∀ m : Nat,
      lower_search.lengthCodeAt m =
        (left_family.conjIntro right_family).rightConjElim.minCheckedCodeSize m
  left_length_polynomial :
    _root_.is_polynomial_bound
      (_root_.MiniHilbert.nat_bound_as_real left_family.length)
  right_length_polynomial :
    _root_.is_polynomial_bound
      (_root_.MiniHilbert.nat_bound_as_real right_family.length)

namespace Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier

def targetFamily
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    _root_.MiniHilbert.ConcreteProofFamily Ax
      (fun m => A m ⊓ B m) :=
  frontier.left_family.conjIntro frontier.right_family

theorem target_length_polynomial
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    _root_.is_polynomial_bound
      (_root_.MiniHilbert.nat_bound_as_real
        frontier.targetFamily.length) :=
  frontier.left_family.conjIntro_length_polynomial
    frontier.right_family
    frontier.left_length_polynomial
    frontier.right_length_polynomial

def concreteLengthCodeFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier
      scale_data frontier.targetFamily where
  lower_search :=
    frontier.lower_search
  lengthCodeAt_eq_family_source :=
    frontier.lengthCodeAt_eq_conj_source
  target_length_polynomial :=
    frontier.target_length_polynomial

def provider
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  frontier.concreteLengthCodeFrontier.provider

def endpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10CheckedSearchCollisionEndpoint scale_data :=
  frontier.provider.endpoint

noncomputable def computedCollisionNOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  frontier.provider.computedCollisionNOfRationality hrat

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    frontier.provider.Audit ∧
      frontier.endpoint.Audit ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure := frontier.concreteLengthCodeFrontier.closure
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.2.2.2.2.1,
      hclosure.2.2.2.2.2.2.2⟩

end Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier

/-! ## Canonical conj-intro target search frontier -/

/-- Canonical concrete target-search frontier.  It chooses the checked lower
length code definitionally as the right-conjunction-elimination checked minimum
of the generated conjunction proof family, so the source-exactness equation of
the previous frontier is no longer an external field. -/
structure Month9Month10CanonicalConjIntroTargetSearchFrontier
    (scale_data : InternalPudlakTheorem5ScaleData)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n} :
    Type (max u v w) where
  left_family :
    _root_.MiniHilbert.ConcreteProofFamily Ax A
  right_family :
    _root_.MiniHilbert.ConcreteProofFamily Ax B
  scale_strict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  gap :
    ComputableSearchGapCertificate
      (fun m : Nat =>
        ((left_family.conjIntro right_family)
          |>.rightConjElim
          |>.minCheckedCodeSize m : Real))
  left_length_polynomial :
    _root_.is_polynomial_bound
      (_root_.MiniHilbert.nat_bound_as_real left_family.length)
  right_length_polynomial :
    _root_.is_polynomial_bound
      (_root_.MiniHilbert.nat_bound_as_real right_family.length)

namespace Month9Month10CanonicalConjIntroTargetSearchFrontier

def targetFamily
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10CanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    _root_.MiniHilbert.ConcreteProofFamily Ax
      (fun m => A m ⊓ B m) :=
  frontier.left_family.conjIntro frontier.right_family

def lowerSearch
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10CanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
      scale_data where
  lengthCodeAt :=
    fun m : Nat => frontier.targetFamily.rightConjElim.minCheckedCodeSize m
  scale_strict :=
    frontier.scale_strict
  gap :=
    frontier.gap

def conjIntroLengthCodeFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10CanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier
      scale_data (Ax := Ax) (A := A) (B := B) where
  left_family :=
    frontier.left_family
  right_family :=
    frontier.right_family
  lower_search :=
    frontier.lowerSearch
  lengthCodeAt_eq_conj_source := by
    intro m
    rfl
  left_length_polynomial :=
    frontier.left_length_polynomial
  right_length_polynomial :=
    frontier.right_length_polynomial

def provider
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10CanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  frontier.conjIntroLengthCodeFrontier.provider

def endpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10CanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10CheckedSearchCollisionEndpoint scale_data :=
  frontier.provider.endpoint

noncomputable def computedCollisionNOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10CanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  frontier.provider.computedCollisionNOfRationality hrat

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10CanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    frontier.provider.Audit ∧
      frontier.endpoint.Audit ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure := frontier.conjIntroLengthCodeFrontier.closure
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.1,
      hclosure.2.2.2⟩

end Month9Month10CanonicalConjIntroTargetSearchFrontier

/-! ## Time-bound canonical conj-intro target search frontier -/

/-- Canonical target-search frontier with scale strictness generated from the
primitive time-constructible bound and nonzero exponent.  This removes the
standalone `scale_strict` field from the canonical target frontier. -/
structure Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
    (scale_data : InternalPudlakTheorem5ScaleData)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n} :
    Type (max u v w) where
  left_family :
    _root_.MiniHilbert.ConcreteProofFamily Ax A
  right_family :
    _root_.MiniHilbert.ConcreteProofFamily Ax B
  time_bound_strict :
    ∀ {a b : Nat}, a < b →
      scale_data.time_constructible_bound a <
        scale_data.time_constructible_bound b
  exponent_ne_zero :
    scale_data.exponent ≠ 0
  gap :
    ComputableSearchGapCertificate
      (fun m : Nat =>
        ((left_family.conjIntro right_family)
          |>.rightConjElim
          |>.minCheckedCodeSize m : Real))
  left_length_polynomial :
    _root_.is_polynomial_bound
      (_root_.MiniHilbert.nat_bound_as_real left_family.length)
  right_length_polynomial :
    _root_.is_polynomial_bound
      (_root_.MiniHilbert.nat_bound_as_real right_family.length)

namespace Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier

theorem scale_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectMonth9Month10ProofLengthGapFrontier.Month9Month10ActualProofLengthGapFrontier.scale_strict_of_timeConstructibleBound_strict
    frontier.time_bound_strict frontier.exponent_ne_zero

def canonicalFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10CanonicalConjIntroTargetSearchFrontier
      scale_data (Ax := Ax) (A := A) (B := B) where
  left_family :=
    frontier.left_family
  right_family :=
    frontier.right_family
  scale_strict :=
    frontier.scale_strict
  gap :=
    frontier.gap
  left_length_polynomial :=
    frontier.left_length_polynomial
  right_length_polynomial :=
    frontier.right_length_polynomial

def provider
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  frontier.canonicalFrontier.provider

def endpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10CheckedSearchCollisionEndpoint scale_data :=
  frontier.provider.endpoint

noncomputable def computedCollisionNOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  frontier.provider.computedCollisionNOfRationality hrat

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    frontier.provider.Audit ∧
      frontier.endpoint.Audit ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure := frontier.canonicalFrontier.closure
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.1,
      hclosure.2.2.2⟩

end Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier

/-! ## Local-Hilbert length-code target frontier -/

/-- Local-Hilbert instantiation of the concrete length-code frontier.  Here the
checker-side lower length is not an external equation: it is the local
PA/Hilbert source minimum supplied by the existing projection model, and Month 8
identifies that source minimum with the right-conjunction-elimination checked
minimum of the concrete target proof family.

This bridge is intentionally not advertised as payload-free: the local source
family is the project `partialConsistencyCode`, so the axiom probe still exposes
the payload vocabulary until the payload checker-acceptance bridge is replaced
by a fully internal accepted-code exactness proof. -/
structure Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
    (scale_data : InternalPudlakTheorem5ScaleData)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Type (max u v w) where
  scale_strict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  gap :
    ComputableSearchGapCertificate
      (fun m : Nat =>
        (interp.localHilbertProofCodeSemantics.minProofCodeSize
          (_root_.partialConsistencyCode m) (Or.inl ⟨m, rfl⟩) : Real))
  proof_object_checker :
    _root_.SondowMainCheckedCodeBridge.SondowProjectMonth8ProofLengthInstantiationSurface.Month8ConcreteProofObjectCheckerInterface
      interp
  target_length_polynomial :
    _root_.is_polynomial_bound
      (_root_.MiniHilbert.nat_bound_as_real
        interp.target_proof_family.length)

namespace Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier

def lowerSearch
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput
      scale_data where
  lengthCodeAt :=
    fun m : Nat =>
      interp.localHilbertProofCodeSemantics.minProofCodeSize
        (_root_.partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
  scale_strict :=
    frontier.scale_strict
  gap :=
    frontier.gap

theorem lengthCodeAt_eq_family_source
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp)
    (m : Nat) :
    frontier.lowerSearch.lengthCodeAt m =
      interp.target_proof_family.rightConjElim.minCheckedCodeSize m :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectMonth8ProofLengthInstantiationSurface.Month8ConcreteProofObjectCheckerInterface.source_minProofCodeSize_eq_minChecked
    frontier.proof_object_checker m

def concreteLengthCodeFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp) :
    Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier
      scale_data interp.target_proof_family where
  lower_search :=
    frontier.lowerSearch
  lengthCodeAt_eq_family_source :=
    frontier.lengthCodeAt_eq_family_source
  target_length_polynomial :=
    frontier.target_length_polynomial

def provider
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp) :
    ProofLengthAxiomFreeInternalTheorem5Provider :=
  frontier.concreteLengthCodeFrontier.provider

def endpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp) :
    Month9Month10CheckedSearchCollisionEndpoint scale_data :=
  frontier.provider.endpoint

noncomputable def computedCollisionNOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  frontier.provider.computedCollisionNOfRationality hrat

theorem computedCollisionN_eq_rejectionExtractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    frontier.computedCollisionNOfRationality hrat =
      frontier.concreteLengthCodeFrontier.computedCollisionNOfRationality
        hrat :=
  rfl

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp) :
    frontier.provider.Audit ∧
      frontier.endpoint.Audit ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure := frontier.concreteLengthCodeFrontier.closure
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.2.2.2.2.1,
      hclosure.2.2.2.2.2.2.2⟩

end Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier

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
