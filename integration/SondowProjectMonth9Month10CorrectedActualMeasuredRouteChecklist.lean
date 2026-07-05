import integration.SondowProjectMonth11Month12ActualTransportExactness

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth9Month10CorrectedActualMeasuredRouteChecklist

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10ProofLengthGapFrontier
open SondowProjectMonth9Month10Month11ExactProofGapHandoff
open SondowProjectMonth11Month12HardResidualElimination

/-- Receiver-side checklist for the corrected Month 9-10 route.  It records the
usable interface after rejecting the exact-scale route: checked finite search
gives a proof-length-free gap; an actual-transport residual moves that gap to
the project actual proof-length measurement; and the computed witness is the
extractor witness. -/
structure CorrectedActualMeasuredRouteChecklist : Prop where
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
