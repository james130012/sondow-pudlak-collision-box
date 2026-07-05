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

end SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint
end SondowMainCheckedCodeBridge
