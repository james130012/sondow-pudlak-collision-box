import integration.SondowProjectMonth11Month12ActualTransportExactness
import integration.SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth9Month10CorrectedActualMeasuredRouteChecklist

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10ProofLengthGapFrontier
open SondowProjectMonth9Month10Month11ExactProofGapHandoff
open SondowProjectMonth11Month12HardResidualElimination
open SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface
open SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint

/-- Exact closure shape for the checker-measured theorem-5 provider.  This is
the root-`proof_length`-free core: the measured object is the concrete
checker-computed `minProofCodeSize`, and the contradiction witness is the
rejection extractor witness. -/
abbrev AxiomFreeProviderClosureStatement
    (provider : ProofLengthAxiomFreeInternalTheorem5Provider) : Prop :=
  provider.Audit ∧
    provider.endpoint.Audit ∧
      (∀ f : Nat → Real, ∀ _hf : _root_.is_polynomial_bound f,
        ∃ᶠ n in Filter.atTop,
          (provider.candidate.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (provider.scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
        (∀ n : Nat,
          provider.scale_data.powerBoundRawCode n =
            _root_.strengthenedPartialConsistencyCode
              (provider.scale_data.scale n)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            provider.computedCollisionNOfRationality hrat =
              provider.candidate.rejectionExtractor.witness
                (checkedSearchUpperTail
                  provider.candidate provider.upper_provider hrat).U
                (checkedSearchUpperTail
                  provider.candidate provider.upper_provider hrat).polynomial
                (checkedSearchUpperTail
                  provider.candidate provider.upper_provider hrat).upperN) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              (checkedSearchUpperTail
                provider.candidate provider.upper_provider hrat).upperN ≤
                provider.computedCollisionNOfRationality hrat) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              (checkedSearchUpperTail
                provider.candidate provider.upper_provider hrat).U
                  (provider.computedCollisionNOfRationality hrat) <
                month9_month10_checkedProofCodeMeasured
                  provider.scale_data
                  provider.candidate.checkerSemantics.toProofCodeSemantics
                  (provider.computedCollisionNOfRationality hrat)) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              month9_month10_checkedProofCodeMeasured
                  provider.scale_data
                  provider.candidate.checkerSemantics.toProofCodeSemantics
                  (provider.computedCollisionNOfRationality hrat) ≤
                (checkedSearchUpperTail
                  provider.candidate provider.upper_provider hrat).U
                  (provider.computedCollisionNOfRationality hrat)) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
            ¬ _root_.is_rational _root_.euler_mascheroni

/-- Receiver-side checklist for the corrected Month 9-10 route.  It records the
usable interface after rejecting the exact-scale route: checked finite search
gives a proof-length-free gap; an actual-transport residual moves that gap to
the project actual proof-length measurement; and the computed witness is the
extractor witness. -/
structure CorrectedActualMeasuredRouteChecklist : Prop where
  axiomFreeProviderClosure :
    ∀ provider : ProofLengthAxiomFreeInternalTheorem5Provider,
      AxiomFreeProviderClosureStatement provider
  checkedGapConstructor :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ checker :
        InternalPudlakTheorem5CheckerSemantics.{0} scale_data,
        ∀ enumeration :
          InternalPudlakTheorem5CheckerFiniteEnumeration checker,
          ∀ extractor :
            InternalPudlakTheorem5CheckerComputableRejectionExtractor
              checker enumeration,
            Nonempty
              (ComputableSearchGapCertificate
                (month9_month10_checkedProofCodeMeasured
                  scale_data checker.toProofCodeSemantics)) ∧
              (∀ U : Nat → Real,
                ∀ hU : _root_.is_polynomial_bound U,
                  ∀ N : Nat,
                    ((checked_minProofCodeSize_gap_constructor extractor
                      |>.gap_for_polynomial_upper U hU).witness N) =
                      extractor.witness U hU N)
  actualResidualFromFamilyExactness :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ checker :
        InternalPudlakTheorem5CheckerSemantics.{0} scale_data,
        ∀ _family :
          InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker,
          CorrectedActualMeasuredResidual checker
  correctedEndpointClosure :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ checker :
        InternalPudlakTheorem5CheckerSemantics.{0} scale_data,
        ∀ enumeration :
          InternalPudlakTheorem5CheckerFiniteEnumeration checker,
          ∀ extractor :
            InternalPudlakTheorem5CheckerComputableRejectionExtractor
              checker enumeration,
            ∀ residual : CorrectedActualMeasuredResidual checker,
              ∀ actual_upper :
                Month9Month10AbstractMeasuredUpperProvider
                  (actualProofLengthMeasured scale_data),
                CorrectedActualMeasuredEndpointAudit
                  extractor residual actual_upper ∧
                  (corrected_actual_measured_endpoint
                    extractor residual actual_upper).Audit ∧
                  Nonempty
                    (ComputableSearchGapCertificate
                      (actualProofLengthMeasured scale_data)) ∧
                  (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                    (corrected_actual_measured_endpoint
                        extractor residual actual_upper).computedCollisionNOfRationality hrat =
                      extractor.witness
                        (corrected_actual_upper_tail
                          extractor residual actual_upper hrat).U
                        (corrected_actual_upper_tail
                          extractor residual actual_upper hrat).polynomial
                        (corrected_actual_upper_tail
                          extractor residual actual_upper hrat).upperN) ∧
                  (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                    False) ∧
                  ¬ _root_.is_rational _root_.euler_mascheroni
  exactScaleRouteRejected :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ checker :
        InternalPudlakTheorem5CheckerSemantics.{0} scale_data,
        ∀ enumeration :
          InternalPudlakTheorem5CheckerFiniteEnumeration checker,
          ∀ _extractor :
            InternalPudlakTheorem5CheckerComputableRejectionExtractor
              checker enumeration,
            ∀ _scale_transport :
              CheckedMinProofCodeSizeEqScaleBlocker checker,
              False

theorem corrected_actual_measured_route_checklist :
    CorrectedActualMeasuredRouteChecklist where
  axiomFreeProviderClosure := by
    intro provider
    exact provider.closure
  checkedGapConstructor := by
    intro scale_data checker enumeration extractor
    exact
      ⟨⟨checked_minProofCodeSize_gap_constructor
        (scale_data := scale_data) (checker := checker)
        (enumeration := enumeration) extractor⟩,
        checked_minProofCodeSize_gap_witness_eq
          (scale_data := scale_data) (checker := checker)
          (enumeration := enumeration) extractor⟩
  actualResidualFromFamilyExactness := by
    intro scale_data checker family
    exact
      { actual_transport :=
          SondowProjectMonth11Month12ActualTransportExactness.your_actual_transport_theorem
            family }
  correctedEndpointClosure := by
    intro scale_data checker enumeration extractor residual actual_upper
    exact
      corrected_actual_measured_endpoint_closure
        (scale_data := scale_data) (checker := checker)
        (enumeration := enumeration)
        extractor residual actual_upper
  exactScaleRouteRejected := by
    intro scale_data checker enumeration extractor scale_transport
    exact
      checked_eq_scale_blocker_impossible
        (scale_data := scale_data) (checker := checker)
        (enumeration := enumeration) extractor scale_transport

end SondowProjectMonth9Month10CorrectedActualMeasuredRouteChecklist
end SondowMainCheckedCodeBridge
