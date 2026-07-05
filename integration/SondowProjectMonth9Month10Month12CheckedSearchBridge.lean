import integration.SondowProjectMonth9Month10Month11ExactProofGapHandoff
import integration.SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth9Month10Month12CheckedSearchBridge

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10ProofLengthGapFrontier
open SondowProjectMonth9Month10Month11ExactProofGapHandoff

/-- Proof-length-free slice of the Month 12 checker work.  This is the exact
piece Month 9-10 needs for the checked-search collision route: checker
semantics, finite enumeration, and the computable rejection extractor. -/
structure Month12ProofLengthFreeCheckerSearchCandidate
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 2 where
  checkerSemantics :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data
  finiteEnumeration :
    InternalPudlakTheorem5CheckerFiniteEnumeration checkerSemantics
  rejectionExtractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checkerSemantics finiteEnumeration

namespace Month12ProofLengthFreeCheckerSearchCandidate

def proofCodeSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data) :
    _root_.ProofCodeSemantics.{0}
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) :=
  candidate.checkerSemantics.toProofCodeSemantics

def smallCodeSearch
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data) :
    InternalPudlakTheorem5SmallCodeSearch
      scale_data candidate.proofCodeSemantics :=
  candidate.finiteEnumeration.toSmallCodeSearch

def finiteSearchExclusion
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      scale_data candidate.proofCodeSemantics candidate.smallCodeSearch :=
  candidate.rejectionExtractor.toComputableFiniteSearchExclusion

theorem finiteSearchExclusion_witness_eq_rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    candidate.finiteSearchExclusion.witness U hU N =
      candidate.rejectionExtractor.witness U hU N :=
  rfl

def toCheckedSearchCollisionEndpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data candidate.proofCodeSemantics)) :
    Month9Month10CheckedSearchCollisionEndpoint scale_data where
  sem := candidate.proofCodeSemantics
  search := candidate.smallCodeSearch
  cert := candidate.finiteSearchExclusion
  upper_provider := upper_provider

theorem computedCollisionN_eq_rejectionExtractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data candidate.proofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (candidate.toCheckedSearchCollisionEndpoint
        upper_provider).computedCollisionNOfRationality hrat =
      candidate.rejectionExtractor.witness
        ((candidate.toCheckedSearchCollisionEndpoint upper_provider)
          |>.toDirectEndpoint
          |>.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).U
        ((candidate.toCheckedSearchCollisionEndpoint upper_provider)
          |>.toDirectEndpoint
          |>.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).polynomial
        ((candidate.toCheckedSearchCollisionEndpoint upper_provider)
          |>.toDirectEndpoint
          |>.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).upperN := by
  simpa [toCheckedSearchCollisionEndpoint,
    finiteSearchExclusion_witness_eq_rejectionExtractor] using
    ((candidate.toCheckedSearchCollisionEndpoint upper_provider)
      |>.computedCollisionN_eq_certWitness hrat)

structure Audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data candidate.proofCodeSemantics)) : Prop where
  checkedSearchEndpoint :
    (candidate.toCheckedSearchCollisionEndpoint upper_provider).Audit
  checkedGapKernel :
    Nonempty
      (ComputableSearchGapCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data candidate.proofCodeSemantics))
  computedWitnessFormula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (candidate.toCheckedSearchCollisionEndpoint
          upper_provider).computedCollisionNOfRationality hrat =
        candidate.rejectionExtractor.witness
          ((candidate.toCheckedSearchCollisionEndpoint upper_provider)
            |>.toDirectEndpoint
            |>.toAbstractMeasuredEndpoint
            |>.upperTailOfRationality hrat).U
          ((candidate.toCheckedSearchCollisionEndpoint upper_provider)
            |>.toDirectEndpoint
            |>.toAbstractMeasuredEndpoint
            |>.upperTailOfRationality hrat).polynomial
          ((candidate.toCheckedSearchCollisionEndpoint upper_provider)
            |>.toDirectEndpoint
            |>.toAbstractMeasuredEndpoint
            |>.upperTailOfRationality hrat).upperN
  contradictionAtComputedN :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data candidate.proofCodeSemantics)) :
    Audit candidate upper_provider where
  checkedSearchEndpoint :=
    (candidate.toCheckedSearchCollisionEndpoint upper_provider).audit
  checkedGapKernel :=
    ⟨(candidate.toCheckedSearchCollisionEndpoint upper_provider).gap⟩
  computedWitnessFormula :=
    candidate.computedCollisionN_eq_rejectionExtractorWitness upper_provider
  contradictionAtComputedN :=
    (candidate.toCheckedSearchCollisionEndpoint upper_provider)
      |>.computed_n_contradiction
  endpointNotRational :=
    (candidate.toCheckedSearchCollisionEndpoint upper_provider).not_rational

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data candidate.proofCodeSemantics)) :
    Audit candidate upper_provider ∧
      (candidate.toCheckedSearchCollisionEndpoint upper_provider).Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (month9_month10_checkedProofCodeMeasured
              scale_data candidate.proofCodeSemantics)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (candidate.toCheckedSearchCollisionEndpoint
                upper_provider).computedCollisionNOfRationality hrat =
              candidate.rejectionExtractor.witness
                ((candidate.toCheckedSearchCollisionEndpoint upper_provider)
                  |>.toDirectEndpoint
                  |>.toAbstractMeasuredEndpoint
                  |>.upperTailOfRationality hrat).U
                ((candidate.toCheckedSearchCollisionEndpoint upper_provider)
                  |>.toDirectEndpoint
                  |>.toAbstractMeasuredEndpoint
                  |>.upperTailOfRationality hrat).polynomial
                ((candidate.toCheckedSearchCollisionEndpoint upper_provider)
                  |>.toDirectEndpoint
                  |>.toAbstractMeasuredEndpoint
                  |>.upperTailOfRationality hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨candidate.audit upper_provider,
    (candidate.toCheckedSearchCollisionEndpoint upper_provider).audit,
    ⟨(candidate.toCheckedSearchCollisionEndpoint upper_provider).gap⟩,
    candidate.computedCollisionN_eq_rejectionExtractorWitness upper_provider,
    (candidate.toCheckedSearchCollisionEndpoint upper_provider)
      |>.computed_n_contradiction,
    (candidate.toCheckedSearchCollisionEndpoint upper_provider).not_rational⟩

end Month12ProofLengthFreeCheckerSearchCandidate

abbrev Month12SurfaceProofLengthFreeCheckerSearchCandidate
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 2 :=
  SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.Month12ProofLengthFreeCheckerSearchCandidate
    scale_data

abbrev Month12SurfaceProofLengthTransportResidual
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12SurfaceProofLengthFreeCheckerSearchCandidate scale_data) :
    Prop :=
  SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.Month12ProofLengthTransportResidual
    candidate

def fromSurfaceProofLengthFreeCandidate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12SurfaceProofLengthFreeCheckerSearchCandidate scale_data) :
    Month12ProofLengthFreeCheckerSearchCandidate scale_data where
  checkerSemantics := candidate.checkerSemantics
  finiteEnumeration := candidate.finiteEnumeration
  rejectionExtractor := candidate.rejectionExtractor

/-- Turn the Month 12 transport residual into the exact checked-to-actual bridge
required by the Month 9-10 checked-search route. -/
def checkedToActualBridgeOfSurfaceResidual
    {scale_data : InternalPudlakTheorem5ScaleData}
    {candidate :
      Month12SurfaceProofLengthFreeCheckerSearchCandidate scale_data}
    (residual :
      Month12SurfaceProofLengthTransportResidual candidate) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
      scale_data candidate.checkerSemantics.toProofCodeSemantics where
  checked_eq_actual := by
    intro n
    have hactual :
        actualProofLengthMeasured scale_data n =
          (candidate.checkerSemantics.minProofCodeSizeAt n : Real) :=
      residual.actualProofLengthMeasured_eq_minProofCodeSizeAt n
    simpa [month9_month10_checkedProofCodeMeasured,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
      using hactual.symm

def checkedUpperProviderOfActualUpperProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    {candidate :
      Month12SurfaceProofLengthFreeCheckerSearchCandidate scale_data}
    (residual :
      Month12SurfaceProofLengthTransportResidual candidate)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    Month9Month10AbstractMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured
        scale_data candidate.checkerSemantics.toProofCodeSemantics) :=
  (checkedToActualBridgeOfSurfaceResidual residual)
    |>.transportUpperToCheckedMeasured actual_upper

def toCheckedSearchCollisionEndpointOfActualUpperProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12SurfaceProofLengthFreeCheckerSearchCandidate scale_data)
    (residual :
      Month12SurfaceProofLengthTransportResidual candidate)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    Month9Month10CheckedSearchCollisionEndpoint scale_data :=
  (fromSurfaceProofLengthFreeCandidate candidate)
    |>.toCheckedSearchCollisionEndpoint
      (checkedUpperProviderOfActualUpperProvider residual actual_upper)

theorem checkedUpperProviderOfActualUpperProvider_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {candidate :
      Month12SurfaceProofLengthFreeCheckerSearchCandidate scale_data}
    (residual :
      Month12SurfaceProofLengthTransportResidual candidate)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    (checkedUpperProviderOfActualUpperProvider
      residual actual_upper).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              month9_month10_checkedProofCodeMeasured
                scale_data candidate.checkerSemantics.toProofCodeSemantics n ≤
                U n) :=
  (checkedToActualBridgeOfSurfaceResidual residual)
    |>.transportUpperToCheckedMeasured_closure actual_upper

theorem computedCollisionN_eq_surfaceRejectionExtractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12SurfaceProofLengthFreeCheckerSearchCandidate scale_data)
    (residual :
      Month12SurfaceProofLengthTransportResidual candidate)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (toCheckedSearchCollisionEndpointOfActualUpperProvider
        candidate residual actual_upper).computedCollisionNOfRationality hrat =
      candidate.rejectionExtractor.witness
        ((toCheckedSearchCollisionEndpointOfActualUpperProvider
            candidate residual actual_upper)
          |>.toDirectEndpoint
          |>.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).U
        ((toCheckedSearchCollisionEndpointOfActualUpperProvider
            candidate residual actual_upper)
          |>.toDirectEndpoint
          |>.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).polynomial
        ((toCheckedSearchCollisionEndpointOfActualUpperProvider
            candidate residual actual_upper)
          |>.toDirectEndpoint
          |>.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).upperN := by
  simpa [toCheckedSearchCollisionEndpointOfActualUpperProvider,
    fromSurfaceProofLengthFreeCandidate] using
    (fromSurfaceProofLengthFreeCandidate candidate)
      |>.computedCollisionN_eq_rejectionExtractorWitness
        (checkedUpperProviderOfActualUpperProvider residual actual_upper) hrat

structure Month12SurfaceActualUpperTransportAudit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12SurfaceProofLengthFreeCheckerSearchCandidate scale_data)
    (residual :
      Month12SurfaceProofLengthTransportResidual candidate)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) : Prop where
  checkedToActualBridge :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
      scale_data candidate.checkerSemantics.toProofCodeSemantics
  transportedUpperProvider :
    (checkedUpperProviderOfActualUpperProvider
      residual actual_upper).Audit
  checkedSearchEndpoint :
    (toCheckedSearchCollisionEndpointOfActualUpperProvider
      candidate residual actual_upper).Audit
  checkedGapKernel :
    Nonempty
      (ComputableSearchGapCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data candidate.checkerSemantics.toProofCodeSemantics))
  computedWitnessFormula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (toCheckedSearchCollisionEndpointOfActualUpperProvider
          candidate residual actual_upper).computedCollisionNOfRationality hrat =
        candidate.rejectionExtractor.witness
          ((toCheckedSearchCollisionEndpointOfActualUpperProvider
              candidate residual actual_upper)
            |>.toDirectEndpoint
            |>.toAbstractMeasuredEndpoint
            |>.upperTailOfRationality hrat).U
          ((toCheckedSearchCollisionEndpointOfActualUpperProvider
              candidate residual actual_upper)
            |>.toDirectEndpoint
            |>.toAbstractMeasuredEndpoint
            |>.upperTailOfRationality hrat).polynomial
          ((toCheckedSearchCollisionEndpointOfActualUpperProvider
              candidate residual actual_upper)
            |>.toDirectEndpoint
            |>.toAbstractMeasuredEndpoint
            |>.upperTailOfRationality hrat).upperN
  contradictionAtComputedN :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem month12_surface_actual_upper_transport_audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12SurfaceProofLengthFreeCheckerSearchCandidate scale_data)
    (residual :
      Month12SurfaceProofLengthTransportResidual candidate)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    Month12SurfaceActualUpperTransportAudit
      candidate residual actual_upper where
  checkedToActualBridge :=
    checkedToActualBridgeOfSurfaceResidual residual
  transportedUpperProvider :=
    (checkedUpperProviderOfActualUpperProvider_closure
      residual actual_upper).1
  checkedSearchEndpoint :=
    (toCheckedSearchCollisionEndpointOfActualUpperProvider
      candidate residual actual_upper).audit
  checkedGapKernel :=
    ⟨(toCheckedSearchCollisionEndpointOfActualUpperProvider
      candidate residual actual_upper).gap⟩
  computedWitnessFormula :=
    computedCollisionN_eq_surfaceRejectionExtractorWitness
      candidate residual actual_upper
  contradictionAtComputedN :=
    (toCheckedSearchCollisionEndpointOfActualUpperProvider
      candidate residual actual_upper).computed_n_contradiction
  endpointNotRational :=
    (toCheckedSearchCollisionEndpointOfActualUpperProvider
      candidate residual actual_upper).not_rational

theorem month12_surface_actual_upper_transport_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12SurfaceProofLengthFreeCheckerSearchCandidate scale_data)
    (residual :
      Month12SurfaceProofLengthTransportResidual candidate)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    Month12SurfaceActualUpperTransportAudit
      candidate residual actual_upper ∧
      (toCheckedSearchCollisionEndpointOfActualUpperProvider
        candidate residual actual_upper).Audit ∧
        (checkedUpperProviderOfActualUpperProvider
          residual actual_upper).Audit ∧
          Nonempty
            (ComputableSearchGapCertificate
              (month9_month10_checkedProofCodeMeasured
                scale_data candidate.checkerSemantics.toProofCodeSemantics)) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              (toCheckedSearchCollisionEndpointOfActualUpperProvider
                  candidate residual actual_upper).computedCollisionNOfRationality hrat =
                candidate.rejectionExtractor.witness
                  ((toCheckedSearchCollisionEndpointOfActualUpperProvider
                      candidate residual actual_upper)
                    |>.toDirectEndpoint
                    |>.toAbstractMeasuredEndpoint
                    |>.upperTailOfRationality hrat).U
                  ((toCheckedSearchCollisionEndpointOfActualUpperProvider
                      candidate residual actual_upper)
                    |>.toDirectEndpoint
                    |>.toAbstractMeasuredEndpoint
                    |>.upperTailOfRationality hrat).polynomial
                  ((toCheckedSearchCollisionEndpointOfActualUpperProvider
                      candidate residual actual_upper)
                    |>.toDirectEndpoint
                    |>.toAbstractMeasuredEndpoint
                    |>.upperTailOfRationality hrat).upperN) ∧
              (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                False) ∧
                ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    ⟨month12_surface_actual_upper_transport_audit
      candidate residual actual_upper,
      (toCheckedSearchCollisionEndpointOfActualUpperProvider
        candidate residual actual_upper).audit,
      (checkedUpperProviderOfActualUpperProvider_closure
        residual actual_upper).1,
      ⟨(toCheckedSearchCollisionEndpointOfActualUpperProvider
        candidate residual actual_upper).gap⟩,
      computedCollisionN_eq_surfaceRejectionExtractorWitness
        candidate residual actual_upper,
      (toCheckedSearchCollisionEndpointOfActualUpperProvider
        candidate residual actual_upper).computed_n_contradiction,
      (toCheckedSearchCollisionEndpointOfActualUpperProvider
        candidate residual actual_upper).not_rational⟩

/-- Project-level checklist for the proof-length-free Month12-to-Month9-10
checked-search bridge. -/
structure Month9Month10Month12CheckedSearchBridgeChecklist : Prop where
  candidateClosure :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ candidate : Month12ProofLengthFreeCheckerSearchCandidate scale_data,
        ∀ upper_provider :
          Month9Month10AbstractMeasuredUpperProvider
            (month9_month10_checkedProofCodeMeasured
              scale_data candidate.proofCodeSemantics),
          Month12ProofLengthFreeCheckerSearchCandidate.Audit
            candidate upper_provider ∧
            (candidate.toCheckedSearchCollisionEndpoint
              upper_provider).Audit ∧
              Nonempty
                (ComputableSearchGapCertificate
                  (month9_month10_checkedProofCodeMeasured
                    scale_data candidate.proofCodeSemantics)) ∧
                (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                  (candidate.toCheckedSearchCollisionEndpoint
                      upper_provider).computedCollisionNOfRationality hrat =
                    candidate.rejectionExtractor.witness
                      ((candidate.toCheckedSearchCollisionEndpoint upper_provider)
                        |>.toDirectEndpoint
                        |>.toAbstractMeasuredEndpoint
                        |>.upperTailOfRationality hrat).U
                      ((candidate.toCheckedSearchCollisionEndpoint upper_provider)
                        |>.toDirectEndpoint
                        |>.toAbstractMeasuredEndpoint
                        |>.upperTailOfRationality hrat).polynomial
                      ((candidate.toCheckedSearchCollisionEndpoint upper_provider)
                        |>.toDirectEndpoint
                        |>.toAbstractMeasuredEndpoint
                        |>.upperTailOfRationality hrat).upperN) ∧
                  (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                    False) ∧
                    ¬ _root_.is_rational _root_.euler_mascheroni
  surfaceActualUpperTransportClosure :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ candidate :
        Month12SurfaceProofLengthFreeCheckerSearchCandidate scale_data,
        ∀ residual :
          Month12SurfaceProofLengthTransportResidual candidate,
          ∀ actual_upper :
            Month9Month10AbstractMeasuredUpperProvider
              (actualProofLengthMeasured scale_data),
            Month12SurfaceActualUpperTransportAudit
              candidate residual actual_upper ∧
              (toCheckedSearchCollisionEndpointOfActualUpperProvider
                candidate residual actual_upper).Audit ∧
                (checkedUpperProviderOfActualUpperProvider
                  residual actual_upper).Audit ∧
                  Nonempty
                    (ComputableSearchGapCertificate
                      (month9_month10_checkedProofCodeMeasured
                        scale_data
                        candidate.checkerSemantics.toProofCodeSemantics)) ∧
                  (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                    (toCheckedSearchCollisionEndpointOfActualUpperProvider
                      candidate residual actual_upper).computedCollisionNOfRationality
                      hrat =
                      candidate.rejectionExtractor.witness
                        ((toCheckedSearchCollisionEndpointOfActualUpperProvider
                            candidate residual actual_upper)
                          |>.toDirectEndpoint
                          |>.toAbstractMeasuredEndpoint
                          |>.upperTailOfRationality hrat).U
                        ((toCheckedSearchCollisionEndpointOfActualUpperProvider
                            candidate residual actual_upper)
                          |>.toDirectEndpoint
                          |>.toAbstractMeasuredEndpoint
                          |>.upperTailOfRationality hrat).polynomial
                        ((toCheckedSearchCollisionEndpointOfActualUpperProvider
                            candidate residual actual_upper)
                          |>.toDirectEndpoint
                          |>.toAbstractMeasuredEndpoint
                          |>.upperTailOfRationality hrat).upperN) ∧
                    (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                      False) ∧
                      ¬ _root_.is_rational _root_.euler_mascheroni

theorem month9_month10_month12_checked_search_bridge_checklist :
    Month9Month10Month12CheckedSearchBridgeChecklist where
  candidateClosure := by
    intro scale_data candidate upper_provider
    exact candidate.closure upper_provider
  surfaceActualUpperTransportClosure := by
    intro scale_data candidate residual actual_upper
    exact
      month12_surface_actual_upper_transport_closure
        candidate residual actual_upper

end SondowProjectMonth9Month10Month12CheckedSearchBridge
end SondowMainCheckedCodeBridge
