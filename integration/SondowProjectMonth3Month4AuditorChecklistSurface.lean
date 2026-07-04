/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4CompleteAuditEndpointSurface

/-!
# Month 3/Month 4 auditor checklist surface

This module turns the complete public endpoint into the explicit checklist an
auditor is likely to ask for.  The checklist is equivalent to the endpoint, so
it is not a weaker restatement of the project route.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4AuditorChecklistSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4ReleaseTheoremExportSurface
open SondowProjectMonth3Month4CompleteAuditEndpointSurface

structure PublicAuditorChecklist
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (n : Nat) (haccepted : SondowAccepted n) : Prop where
  release_final_audit_bridge :
    Month3Month4ReleaseFinalAuditBridge
      rootSide MainRationality SondowAccepted bounds bound n haccepted
  release_public_final_audit :
    Month3Month4ReleasePublicFinalAudit
      rootSide MainRationality SondowAccepted bounds bound n haccepted
  release_verified_dual_witness_audit :
    Month3Month4ReleaseVerifiedDualWitnessAudit
      rootSide MainRationality SondowAccepted bounds bound n haccepted
  month3_accepted_proof_predicate_witness :
    Month3AcceptedProofPredicateWitnessExport
      rootSide MainRationality SondowAccepted bounds bound n haccepted
  month4_theorem5_audit_witness :
    Month4Theorem5AuditWitnessExport
      rootSide MainRationality SondowAccepted bounds bound
  month4_exact_external_boundary :
    Month4ExactExternalBoundaryExport
      rootSide MainRationality SondowAccepted bounds bound
  public_gap_instantiation :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality)
  not_main_rationality : ¬ MainRationality

theorem auditor_checklist_of_public_endpoint
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (endpoint :
      CompleteAuditPublicEndpoint
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    PublicAuditorChecklist
      rootSide MainRationality SondowAccepted bounds bound n haccepted where
  release_final_audit_bridge :=
    public_endpoint_to_release_final_audit_bridge endpoint
  release_public_final_audit :=
    public_endpoint_to_release_public_final_audit endpoint
  release_verified_dual_witness_audit :=
    public_endpoint_to_release_verified_dual_witness_audit endpoint
  month3_accepted_proof_predicate_witness :=
    public_endpoint_to_month3_accepted_witness endpoint
  month4_theorem5_audit_witness :=
    public_endpoint_to_month4_theorem5_audit_witness endpoint
  month4_exact_external_boundary :=
    public_endpoint_to_month4_exact_external_boundary endpoint
  public_gap_instantiation :=
    public_endpoint_to_public_gap_instantiation endpoint
  not_main_rationality :=
    public_endpoint_not_main_rationality endpoint

theorem public_endpoint_of_auditor_checklist
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (checklist :
      PublicAuditorChecklist
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    CompleteAuditPublicEndpoint
      rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  public_endpoint_of_complete_audit_certificate
    (complete_audit_certificate_of_final_audit_bridge
      checklist.release_final_audit_bridge)

theorem public_endpoint_iff_auditor_checklist
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    CompleteAuditPublicEndpoint
      rootSide MainRationality SondowAccepted bounds bound n haccepted ↔
      PublicAuditorChecklist
        rootSide MainRationality SondowAccepted bounds bound n haccepted := by
  constructor
  · intro endpoint
    exact auditor_checklist_of_public_endpoint endpoint
  · intro checklist
    exact public_endpoint_of_auditor_checklist checklist

theorem paper_route_iff_auditor_checklist
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      PublicAuditorChecklist
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  (paper_route_iff_public_endpoint n haccepted).trans
    (public_endpoint_iff_auditor_checklist n haccepted)

theorem release_final_audit_bridge_iff_auditor_checklist
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4ReleaseFinalAuditBridge
      rootSide MainRationality SondowAccepted bounds bound n haccepted ↔
      PublicAuditorChecklist
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  (release_final_audit_bridge_iff_public_endpoint n haccepted).trans
    (public_endpoint_iff_auditor_checklist n haccepted)

theorem auditor_checklist_to_month3_accepted_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (checklist :
      PublicAuditorChecklist
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month3AcceptedProofPredicateWitnessExport
      rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  checklist.month3_accepted_proof_predicate_witness

theorem auditor_checklist_to_month4_theorem5_audit_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (checklist :
      PublicAuditorChecklist
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month4Theorem5AuditWitnessExport
      rootSide MainRationality SondowAccepted bounds bound :=
  checklist.month4_theorem5_audit_witness

theorem auditor_checklist_to_month4_exact_external_boundary
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (checklist :
      PublicAuditorChecklist
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month4ExactExternalBoundaryExport
      rootSide MainRationality SondowAccepted bounds bound :=
  checklist.month4_exact_external_boundary

theorem auditor_checklist_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (checklist :
      PublicAuditorChecklist
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  checklist.public_gap_instantiation

theorem auditor_checklist_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (checklist :
      PublicAuditorChecklist
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    ¬ MainRationality :=
  checklist.not_main_rationality

theorem exactConvention_checklist_iff_auditor_checklist
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
      PublicAuditorChecklist
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  (exactConvention_checklist_iff_public_endpoint h m haccepted).trans
    (public_endpoint_iff_auditor_checklist m haccepted)

theorem splitMinChecked_checklist_iff_auditor_checklist
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
      PublicAuditorChecklist
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  (splitMinChecked_checklist_iff_public_endpoint h m haccepted).trans
    (public_endpoint_iff_auditor_checklist m haccepted)

theorem exactFamily_checklist_iff_auditor_checklist
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
      PublicAuditorChecklist
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  (exactFamily_checklist_iff_public_endpoint h m haccepted).trans
    (public_endpoint_iff_auditor_checklist m haccepted)

theorem paper_route_and_accepted_iff_exists_auditor_checklist
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    (Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound ∧
      ∃ n : Nat, SondowAccepted n) ↔
      ∃ n : Nat, ∃ haccepted : SondowAccepted n,
        PublicAuditorChecklist
          rootSide MainRationality SondowAccepted bounds bound
            n haccepted := by
  constructor
  · rintro ⟨route, ⟨n, haccepted⟩⟩
    exact
      ⟨n, haccepted,
        (paper_route_iff_auditor_checklist n haccepted).mp route⟩
  · rintro ⟨n, haccepted, checklist⟩
    exact
      ⟨(paper_route_iff_auditor_checklist n haccepted).mpr checklist,
        ⟨n, haccepted⟩⟩

theorem exactConvention_checklist_and_accepted_iff_exists_auditor_checklist
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
        PublicAuditorChecklist
          h.toPudlakSideInputs MainRationality SondowAccepted
            bounds bound m haccepted := by
  constructor
  · rintro ⟨checklist, ⟨m, haccepted⟩⟩
    exact
      ⟨m, haccepted,
        (exactConvention_checklist_iff_auditor_checklist
          h m haccepted).mp checklist⟩
  · rintro ⟨m, haccepted, audit⟩
    exact
      ⟨(exactConvention_checklist_iff_auditor_checklist
          h m haccepted).mpr audit,
        ⟨m, haccepted⟩⟩

theorem splitMinChecked_checklist_and_accepted_iff_exists_auditor_checklist
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
        PublicAuditorChecklist
          h.toPudlakSideInputs MainRationality SondowAccepted
            bounds bound m haccepted := by
  constructor
  · rintro ⟨checklist, ⟨m, haccepted⟩⟩
    exact
      ⟨m, haccepted,
        (splitMinChecked_checklist_iff_auditor_checklist
          h m haccepted).mp checklist⟩
  · rintro ⟨m, haccepted, audit⟩
    exact
      ⟨(splitMinChecked_checklist_iff_auditor_checklist
          h m haccepted).mpr audit,
        ⟨m, haccepted⟩⟩

theorem exactFamily_checklist_and_accepted_iff_exists_auditor_checklist
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
        PublicAuditorChecklist
          h.toPudlakSideInputs MainRationality SondowAccepted
            bounds bound m haccepted := by
  constructor
  · rintro ⟨checklist, ⟨m, haccepted⟩⟩
    exact
      ⟨m, haccepted,
        (exactFamily_checklist_iff_auditor_checklist
          h m haccepted).mp checklist⟩
  · rintro ⟨m, haccepted, audit⟩
    exact
      ⟨(exactFamily_checklist_iff_auditor_checklist
          h m haccepted).mpr audit,
        ⟨m, haccepted⟩⟩

theorem exists_auditor_checklist_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      ∃ n : Nat, ∃ haccepted : SondowAccepted n,
        PublicAuditorChecklist
          rootSide MainRationality SondowAccepted bounds bound
            n haccepted) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) := by
  rcases audit with ⟨n, haccepted, checklist⟩
  exact auditor_checklist_to_public_gap_instantiation checklist

theorem exists_auditor_checklist_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      ∃ n : Nat, ∃ haccepted : SondowAccepted n,
        PublicAuditorChecklist
          rootSide MainRationality SondowAccepted bounds bound
            n haccepted) :
    ¬ MainRationality := by
  rcases audit with ⟨n, haccepted, checklist⟩
  exact auditor_checklist_not_main_rationality checklist

theorem exists_auditor_checklist_to_month3_accepted_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      ∃ n : Nat, ∃ haccepted : SondowAccepted n,
        PublicAuditorChecklist
          rootSide MainRationality SondowAccepted bounds bound
            n haccepted) :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      Month3AcceptedProofPredicateWitnessExport
        rootSide MainRationality SondowAccepted bounds bound
          n haccepted := by
  rcases audit with ⟨n, haccepted, checklist⟩
  exact
    ⟨n, haccepted,
      auditor_checklist_to_month3_accepted_witness checklist⟩

theorem exists_auditor_checklist_to_month4_theorem5_audit_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      ∃ n : Nat, ∃ haccepted : SondowAccepted n,
        PublicAuditorChecklist
          rootSide MainRationality SondowAccepted bounds bound
            n haccepted) :
    Month4Theorem5AuditWitnessExport
      rootSide MainRationality SondowAccepted bounds bound := by
  rcases audit with ⟨n, haccepted, checklist⟩
  exact auditor_checklist_to_month4_theorem5_audit_witness checklist

theorem exists_auditor_checklist_to_month4_exact_external_boundary
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      ∃ n : Nat, ∃ haccepted : SondowAccepted n,
        PublicAuditorChecklist
          rootSide MainRationality SondowAccepted bounds bound
            n haccepted) :
    Month4ExactExternalBoundaryExport
      rootSide MainRationality SondowAccepted bounds bound := by
  rcases audit with ⟨n, haccepted, checklist⟩
  exact auditor_checklist_to_month4_exact_external_boundary checklist

end SondowProjectMonth3Month4AuditorChecklistSurface
end SondowMainCheckedCodeBridge
