/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4AuditorChecklistSurface

/-!
# Month 3/Month 4 paper-facing collision theorem surface

This module gives the paper a stable theorem-facing endpoint.  It packages the
accepted public auditor checklist together with the collision consequences and
keeps the route-to-certificate statements as equivalences.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4PaperFacingCollisionTheoremSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4ReleaseTheoremExportSurface
open SondowProjectMonth3Month4AuditorChecklistSurface

structure PaperFacingCollisionCertificate
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop where
  auditor_checklist :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      PublicAuditorChecklist
        rootSide MainRationality SondowAccepted bounds bound n haccepted
  public_gap_instantiation :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality)
  not_main_rationality : ¬ MainRationality
  month3_accepted_proof_predicate_witness :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      Month3AcceptedProofPredicateWitnessExport
        rootSide MainRationality SondowAccepted bounds bound n haccepted
  month4_theorem5_audit_witness :
    Month4Theorem5AuditWitnessExport
      rootSide MainRationality SondowAccepted bounds bound
  month4_exact_external_boundary :
    Month4ExactExternalBoundaryExport
      rootSide MainRationality SondowAccepted bounds bound

theorem paper_facing_collision_certificate_of_exists_auditor_checklist
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit :
      ∃ n : Nat, ∃ haccepted : SondowAccepted n,
        PublicAuditorChecklist
          rootSide MainRationality SondowAccepted bounds bound
            n haccepted) :
    PaperFacingCollisionCertificate
      rootSide MainRationality SondowAccepted bounds bound where
  auditor_checklist := audit
  public_gap_instantiation :=
    exists_auditor_checklist_to_public_gap_instantiation audit
  not_main_rationality :=
    exists_auditor_checklist_not_main_rationality audit
  month3_accepted_proof_predicate_witness :=
    exists_auditor_checklist_to_month3_accepted_witness audit
  month4_theorem5_audit_witness :=
    exists_auditor_checklist_to_month4_theorem5_audit_witness audit
  month4_exact_external_boundary :=
    exists_auditor_checklist_to_month4_exact_external_boundary audit

theorem exists_auditor_checklist_iff_paper_facing_collision_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    (∃ n : Nat, ∃ haccepted : SondowAccepted n,
      PublicAuditorChecklist
        rootSide MainRationality SondowAccepted bounds bound n haccepted) ↔
      PaperFacingCollisionCertificate
        rootSide MainRationality SondowAccepted bounds bound := by
  constructor
  · intro audit
    exact paper_facing_collision_certificate_of_exists_auditor_checklist audit
  · intro cert
    exact cert.auditor_checklist

theorem paper_facing_collision_certificate_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      PaperFacingCollisionCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  cert.public_gap_instantiation

theorem paper_facing_collision_certificate_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      PaperFacingCollisionCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  cert.not_main_rationality

theorem paper_facing_collision_certificate_to_month3_accepted_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      PaperFacingCollisionCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    ∃ n : Nat, ∃ haccepted : SondowAccepted n,
      Month3AcceptedProofPredicateWitnessExport
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  cert.month3_accepted_proof_predicate_witness

theorem paper_facing_collision_certificate_to_month4_theorem5_audit_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      PaperFacingCollisionCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    Month4Theorem5AuditWitnessExport
      rootSide MainRationality SondowAccepted bounds bound :=
  cert.month4_theorem5_audit_witness

theorem paper_facing_collision_certificate_to_month4_exact_external_boundary
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      PaperFacingCollisionCertificate
        rootSide MainRationality SondowAccepted bounds bound) :
    Month4ExactExternalBoundaryExport
      rootSide MainRationality SondowAccepted bounds bound :=
  cert.month4_exact_external_boundary

abbrev PaperFacingCollisionTheoremStatement
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  (Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ∧
    ∃ n : Nat, SondowAccepted n) ↔
    PaperFacingCollisionCertificate
      rootSide MainRationality SondowAccepted bounds bound

theorem paper_route_and_accepted_iff_paper_facing_collision_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    PaperFacingCollisionTheoremStatement
      rootSide MainRationality SondowAccepted bounds bound :=
  paper_route_and_accepted_iff_exists_auditor_checklist.trans
    exists_auditor_checklist_iff_paper_facing_collision_certificate

abbrev ExactConventionPaperFacingCollisionStatement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) : Prop :=
  (Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ∧
    ∃ m : Nat, SondowAccepted m) ↔
    PaperFacingCollisionCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound

theorem exactConvention_checklist_and_accepted_iff_paper_facing_collision_certificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    ExactConventionPaperFacingCollisionStatement
      (MainRationality := MainRationality)
      (SondowAccepted := SondowAccepted) bounds bound h :=
  (exactConvention_checklist_and_accepted_iff_exists_auditor_checklist h).trans
    exists_auditor_checklist_iff_paper_facing_collision_certificate

abbrev SplitMinCheckedPaperFacingCollisionStatement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) : Prop :=
  (Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ∧
    ∃ m : Nat, SondowAccepted m) ↔
    PaperFacingCollisionCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound

theorem splitMinChecked_checklist_and_accepted_iff_paper_facing_collision_certificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    SplitMinCheckedPaperFacingCollisionStatement
      (MainRationality := MainRationality)
      (SondowAccepted := SondowAccepted) bounds bound h :=
  (splitMinChecked_checklist_and_accepted_iff_exists_auditor_checklist h).trans
    exists_auditor_checklist_iff_paper_facing_collision_certificate

abbrev ExactFamilyPaperFacingCollisionStatement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) : Prop :=
  (Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ∧
    ∃ m : Nat, SondowAccepted m) ↔
    PaperFacingCollisionCertificate
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound

theorem exactFamily_checklist_and_accepted_iff_paper_facing_collision_certificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    ExactFamilyPaperFacingCollisionStatement
      (MainRationality := MainRationality)
      (SondowAccepted := SondowAccepted) bounds bound h :=
  (exactFamily_checklist_and_accepted_iff_exists_auditor_checklist h).trans
    exists_auditor_checklist_iff_paper_facing_collision_certificate

theorem exactFamily_route_to_public_gap_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (route :
      Nonempty (Σ' gap_cert :
          ProjectComputableGapCertificate
            MainRationality SondowAccepted bounds bound,
          SondowProjectPudlakConcreteBridgeChecklist
            h.toPudlakSideInputs gap_cert) ∧
        ∃ m : Nat, SondowAccepted m) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  paper_facing_collision_certificate_to_public_gap_instantiation
    ((exactFamily_checklist_and_accepted_iff_paper_facing_collision_certificate
      h).mp route)

theorem exactFamily_route_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (route :
      Nonempty (Σ' gap_cert :
          ProjectComputableGapCertificate
            MainRationality SondowAccepted bounds bound,
          SondowProjectPudlakConcreteBridgeChecklist
            h.toPudlakSideInputs gap_cert) ∧
        ∃ m : Nat, SondowAccepted m) :
    ¬ MainRationality :=
  paper_facing_collision_certificate_not_main_rationality
    ((exactFamily_checklist_and_accepted_iff_paper_facing_collision_certificate
      h).mp route)

theorem exactFamily_route_to_month3_accepted_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (route :
      Nonempty (Σ' gap_cert :
          ProjectComputableGapCertificate
            MainRationality SondowAccepted bounds bound,
          SondowProjectPudlakConcreteBridgeChecklist
            h.toPudlakSideInputs gap_cert) ∧
        ∃ m : Nat, SondowAccepted m) :
    ∃ m : Nat, ∃ haccepted : SondowAccepted m,
      Month3AcceptedProofPredicateWitnessExport
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound
          m haccepted :=
  paper_facing_collision_certificate_to_month3_accepted_witness
    ((exactFamily_checklist_and_accepted_iff_paper_facing_collision_certificate
      h).mp route)

theorem exactFamily_route_to_month4_theorem5_audit_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (route :
      Nonempty (Σ' gap_cert :
          ProjectComputableGapCertificate
            MainRationality SondowAccepted bounds bound,
          SondowProjectPudlakConcreteBridgeChecklist
            h.toPudlakSideInputs gap_cert) ∧
        ∃ m : Nat, SondowAccepted m) :
    Month4Theorem5AuditWitnessExport
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  paper_facing_collision_certificate_to_month4_theorem5_audit_witness
    ((exactFamily_checklist_and_accepted_iff_paper_facing_collision_certificate
      h).mp route)

theorem exactFamily_route_to_month4_exact_external_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (route :
      Nonempty (Σ' gap_cert :
          ProjectComputableGapCertificate
            MainRationality SondowAccepted bounds bound,
          SondowProjectPudlakConcreteBridgeChecklist
            h.toPudlakSideInputs gap_cert) ∧
        ∃ m : Nat, SondowAccepted m) :
    Month4ExactExternalBoundaryExport
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  paper_facing_collision_certificate_to_month4_exact_external_boundary
    ((exactFamily_checklist_and_accepted_iff_paper_facing_collision_certificate
      h).mp route)

end SondowProjectMonth3Month4PaperFacingCollisionTheoremSurface
end SondowMainCheckedCodeBridge
