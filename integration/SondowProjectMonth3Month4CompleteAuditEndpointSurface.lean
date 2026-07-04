/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4ReleaseTheoremExportSurface

/-!
# Month 3/Month 4 complete audit endpoint surface

This module is the one-import public endpoint for the current Month 3/Month 4
route.  It repackages the already exported complete audit certificate into an
audit-facing endpoint and keeps the key checklist statements as equivalences,
not one-way implications.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4CompleteAuditEndpointSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4ReleaseTheoremExportSurface

structure CompleteAuditPublicEndpoint
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (n : Nat) (haccepted : SondowAccepted n) : Prop where
  complete_certificate :
    CompleteMonth3Month4AuditCertificate
      rootSide MainRationality SondowAccepted bounds bound n haccepted
  public_gap_instantiation :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality)
  not_main_rationality : ¬ MainRationality
  month3_accepted_proof_predicate_witness :
    Month3AcceptedProofPredicateWitnessExport
      rootSide MainRationality SondowAccepted bounds bound n haccepted
  month4_theorem5_audit_witness :
    Month4Theorem5AuditWitnessExport
      rootSide MainRationality SondowAccepted bounds bound
  month4_exact_external_boundary :
    Month4ExactExternalBoundaryExport
      rootSide MainRationality SondowAccepted bounds bound

theorem public_endpoint_of_complete_audit_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (cert :
      CompleteMonth3Month4AuditCertificate
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    CompleteAuditPublicEndpoint
      rootSide MainRationality SondowAccepted bounds bound n haccepted where
  complete_certificate := cert
  public_gap_instantiation :=
    complete_audit_certificate_to_public_gap_instantiation cert
  not_main_rationality :=
    complete_audit_certificate_not_main_rationality cert
  month3_accepted_proof_predicate_witness :=
    complete_audit_certificate_to_month3_accepted_witness cert
  month4_theorem5_audit_witness :=
    complete_audit_certificate_to_month4_theorem5_audit_witness cert
  month4_exact_external_boundary :=
    complete_audit_certificate_to_month4_exact_external_boundary cert

theorem complete_audit_certificate_iff_public_endpoint
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    CompleteMonth3Month4AuditCertificate
      rootSide MainRationality SondowAccepted bounds bound n haccepted ↔
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted := by
  constructor
  · intro cert
    exact public_endpoint_of_complete_audit_certificate cert
  · intro endpoint
    exact endpoint.complete_certificate

theorem release_final_audit_bridge_iff_public_endpoint
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4ReleaseFinalAuditBridge
      rootSide MainRationality SondowAccepted bounds bound n haccepted ↔
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  (release_final_audit_bridge_iff_complete_audit_certificate
    n haccepted).trans
    (complete_audit_certificate_iff_public_endpoint n haccepted)

theorem public_endpoint_to_complete_audit_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (endpoint :
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    CompleteMonth3Month4AuditCertificate
      rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  endpoint.complete_certificate

theorem public_endpoint_to_release_final_audit_bridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (endpoint :
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month3Month4ReleaseFinalAuditBridge
      rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  complete_audit_certificate_to_final_audit_bridge
    endpoint.complete_certificate

theorem public_endpoint_to_release_public_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (endpoint :
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month3Month4ReleasePublicFinalAudit
      rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  (public_endpoint_to_release_final_audit_bridge endpoint).1

theorem public_endpoint_to_release_verified_dual_witness_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (endpoint :
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month3Month4ReleaseVerifiedDualWitnessAudit
      rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  (public_endpoint_to_release_final_audit_bridge endpoint).2

theorem public_endpoint_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (endpoint :
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  endpoint.public_gap_instantiation

theorem public_endpoint_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (endpoint :
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    ¬ MainRationality :=
  endpoint.not_main_rationality

theorem public_endpoint_to_month3_accepted_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (endpoint :
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month3AcceptedProofPredicateWitnessExport
      rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  endpoint.month3_accepted_proof_predicate_witness

theorem public_endpoint_to_month4_theorem5_audit_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (endpoint :
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month4Theorem5AuditWitnessExport
      rootSide MainRationality SondowAccepted bounds bound :=
  endpoint.month4_theorem5_audit_witness

theorem public_endpoint_to_month4_exact_external_boundary
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (endpoint :
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month4ExactExternalBoundaryExport
      rootSide MainRationality SondowAccepted bounds bound :=
  endpoint.month4_exact_external_boundary

theorem paper_route_iff_public_endpoint
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  (paper_route_iff_complete_audit_certificate n haccepted).trans
    (complete_audit_certificate_iff_public_endpoint n haccepted)

theorem release_public_final_audit_iff_public_endpoint
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4ReleasePublicFinalAudit
        rootSide MainRationality SondowAccepted bounds bound n haccepted ↔
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  (paper_route_iff_release_public_final_audit n haccepted).symm.trans
    (paper_route_iff_public_endpoint n haccepted)

theorem release_verified_dual_witness_audit_iff_public_endpoint
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4ReleaseVerifiedDualWitnessAudit
        rootSide MainRationality SondowAccepted bounds bound n haccepted ↔
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  (paper_route_iff_release_verified_dual_witness_audit n haccepted).symm.trans
    (paper_route_iff_public_endpoint n haccepted)

theorem exactConvention_checklist_iff_public_endpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      CompleteAuditPublicEndpoint
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  (exactConvention_checklist_iff_complete_audit_certificate h m haccepted).trans
    (complete_audit_certificate_iff_public_endpoint m haccepted)

theorem splitMinChecked_checklist_iff_public_endpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      CompleteAuditPublicEndpoint
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  (splitMinChecked_checklist_iff_complete_audit_certificate h m haccepted).trans
    (complete_audit_certificate_iff_public_endpoint m haccepted)

theorem exactFamily_checklist_iff_public_endpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      CompleteAuditPublicEndpoint
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  (exactFamily_checklist_iff_complete_audit_certificate h m haccepted).trans
    (complete_audit_certificate_iff_public_endpoint m haccepted)

theorem paper_route_and_accepted_iff_exists_public_endpoint
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    (Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound ∧
      ∃ n : Nat, SondowAccepted n) ↔
      ∃ n : Nat, ∃ haccepted : SondowAccepted n,
        CompleteAuditPublicEndpoint
          rootSide MainRationality SondowAccepted bounds bound
            n haccepted := by
  constructor
  · rintro ⟨route, ⟨n, haccepted⟩⟩
    exact
      ⟨n, haccepted,
        (paper_route_iff_public_endpoint n haccepted).mp route⟩
  · rintro ⟨n, haccepted, endpoint⟩
    exact
      ⟨(paper_route_iff_public_endpoint n haccepted).mpr endpoint,
        ⟨n, haccepted⟩⟩

theorem exactConvention_checklist_and_accepted_iff_exists_public_endpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    (Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert) ∧
      ∃ m : Nat, SondowAccepted m) ↔
      ∃ m : Nat, ∃ haccepted : SondowAccepted m,
        CompleteAuditPublicEndpoint
          h.toPudlakSideInputs MainRationality SondowAccepted
            bounds bound m haccepted := by
  constructor
  · rintro ⟨checklist, ⟨m, haccepted⟩⟩
    exact
      ⟨m, haccepted,
        (exactConvention_checklist_iff_public_endpoint
          h m haccepted).mp checklist⟩
  · rintro ⟨m, haccepted, endpoint⟩
    exact
      ⟨(exactConvention_checklist_iff_public_endpoint
          h m haccepted).mpr endpoint,
        ⟨m, haccepted⟩⟩

theorem splitMinChecked_checklist_and_accepted_iff_exists_public_endpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    (Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert) ∧
      ∃ m : Nat, SondowAccepted m) ↔
      ∃ m : Nat, ∃ haccepted : SondowAccepted m,
        CompleteAuditPublicEndpoint
          h.toPudlakSideInputs MainRationality SondowAccepted
            bounds bound m haccepted := by
  constructor
  · rintro ⟨checklist, ⟨m, haccepted⟩⟩
    exact
      ⟨m, haccepted,
        (splitMinChecked_checklist_iff_public_endpoint
          h m haccepted).mp checklist⟩
  · rintro ⟨m, haccepted, endpoint⟩
    exact
      ⟨(splitMinChecked_checklist_iff_public_endpoint
          h m haccepted).mpr endpoint,
        ⟨m, haccepted⟩⟩

theorem exactFamily_checklist_and_accepted_iff_exists_public_endpoint
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    (Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert) ∧
      ∃ m : Nat, SondowAccepted m) ↔
      ∃ m : Nat, ∃ haccepted : SondowAccepted m,
        CompleteAuditPublicEndpoint
          h.toPudlakSideInputs MainRationality SondowAccepted
            bounds bound m haccepted := by
  constructor
  · rintro ⟨checklist, ⟨m, haccepted⟩⟩
    exact
      ⟨m, haccepted,
        (exactFamily_checklist_iff_public_endpoint
          h m haccepted).mp checklist⟩
  · rintro ⟨m, haccepted, endpoint⟩
    exact
      ⟨(exactFamily_checklist_iff_public_endpoint
          h m haccepted).mpr endpoint,
        ⟨m, haccepted⟩⟩

end SondowProjectMonth3Month4CompleteAuditEndpointSurface
end SondowMainCheckedCodeBridge
