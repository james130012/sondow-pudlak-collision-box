import integration.SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
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

end SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint
end SondowMainCheckedCodeBridge
