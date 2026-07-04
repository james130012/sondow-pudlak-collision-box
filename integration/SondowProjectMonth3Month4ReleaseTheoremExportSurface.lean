/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4FinalAuditTheoremSurface
import EulerLimit.PudlakTheorem5ExactExternalBoundarySurface

/-!
# Month 3/Month 4 release theorem export surface

This module is the project-level export surface for the current Month 3/Month 4
route.  It keeps the public release endpoint as an equivalence, not as a
one-way weakening:

* paper route;
* public final audit;
* verified dual-witness final audit;
* concrete checklist entries.

The public collision consequences are then projected from the same final audit
bridge.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4ReleaseTheoremExportSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4TheoremIndexSurface
open SondowProjectMonth3Month4VerifiedProjectIndexSurface
open SondowProjectMonth3Month4FinalAuditTheoremSurface

abbrev Month3Month4ReleasePublicFinalAudit
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (n : Nat) (haccepted : SondowAccepted n) : Prop :=
  PublicFinalAuditRoute
    rootSide MainRationality SondowAccepted bounds bound n haccepted

abbrev Month3Month4ReleaseVerifiedDualWitnessAudit
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (n : Nat) (haccepted : SondowAccepted n) : Prop :=
  VerifiedDualWitnessFinalAuditRoute
    rootSide MainRationality SondowAccepted bounds bound n haccepted

abbrev Month3Month4ReleaseFinalAuditBridge
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (n : Nat) (haccepted : SondowAccepted n) : Prop :=
  FinalAuditBridgePair
    rootSide MainRationality SondowAccepted bounds bound n haccepted

abbrev Month3AcceptedProofPredicateWitnessExport
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (n : Nat) (haccepted : SondowAccepted n) : Prop :=
  Nonempty (Σ' pkg : Month3Month4VerifiedProjectInstantiation
    rootSide MainRationality SondowAccepted bounds bound,
    SondowProjectMonth3Month4AcceptedBoundedPAChainSurface.AcceptedMonth3ProofPredicateWitness
      pkg.chain_package n haccepted)

abbrev Month4Theorem5AuditWitnessExport
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  Nonempty (Σ' _pkg : Month3Month4VerifiedProjectInstantiation
    rootSide MainRationality SondowAccepted bounds bound,
    PudlakTheorem5LiteratureInputAuditSurface.ProjectTheorem5AuditWitness)

abbrev Month4ExactExternalBoundaryExport
    (_rootSide : SondowProjectLocalPudlakSideInputs)
    (_MainRationality : Prop) (_SondowAccepted : Nat → Prop)
    (_bounds : SondowComponentBounds) (_bound : Nat → Real) : Prop :=
  _root_.PudlakTheorem5ExactExternalBoundarySurface.Statement

theorem paper_route_iff_release_public_final_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month3Month4ReleasePublicFinalAudit
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  paper_route_iff_public_final_audit n haccepted

theorem paper_route_iff_release_verified_dual_witness_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month3Month4ReleaseVerifiedDualWitnessAudit
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  paper_route_iff_verified_dual_witness_final_audit n haccepted

theorem release_public_final_audit_iff_verified_dual_witness_audit
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4ReleasePublicFinalAudit
        rootSide MainRationality SondowAccepted bounds bound n haccepted ↔
      Month3Month4ReleaseVerifiedDualWitnessAudit
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  public_final_audit_iff_verified_dual_witness_final_audit n haccepted

theorem paper_route_iff_release_final_audit_bridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month3Month4ReleaseFinalAuditBridge
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  paper_route_iff_final_audit_bridge_pair n haccepted

theorem paper_route_and_accepted_iff_exists_release_final_audit_bridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    (Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound ∧
      ∃ n : Nat, SondowAccepted n) ↔
      ∃ n : Nat, ∃ haccepted : SondowAccepted n,
        Month3Month4ReleaseFinalAuditBridge
          rootSide MainRationality SondowAccepted bounds bound
            n haccepted := by
  constructor
  · rintro ⟨route, ⟨n, haccepted⟩⟩
    exact
      ⟨n, haccepted,
        (paper_route_iff_release_final_audit_bridge
          n haccepted).mp route⟩
  · rintro ⟨n, haccepted, bridge⟩
    exact
      ⟨(paper_route_iff_release_final_audit_bridge
          n haccepted).mpr bridge,
        ⟨n, haccepted⟩⟩

theorem release_final_audit_bridge_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (bridge :
      Month3Month4ReleaseFinalAuditBridge
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  paper_route_to_public_gap_instantiation
    ((paper_route_iff_release_final_audit_bridge n haccepted).mpr bridge)

theorem release_final_audit_bridge_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (bridge :
      Month3Month4ReleaseFinalAuditBridge
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    ¬ MainRationality :=
  paper_route_not_main_rationality
    ((paper_route_iff_release_final_audit_bridge n haccepted).mpr bridge)

theorem release_final_audit_bridge_to_month3_accepted_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (bridge :
      Month3Month4ReleaseFinalAuditBridge
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month3AcceptedProofPredicateWitnessExport
      rootSide MainRationality SondowAccepted bounds bound n haccepted := by
  rcases bridge.2 with ⟨⟨pkg, audit⟩⟩
  exact ⟨⟨pkg, audit.month3_accepted_proof_predicate_witness⟩⟩

theorem release_final_audit_bridge_to_month4_theorem5_audit_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (bridge :
      Month3Month4ReleaseFinalAuditBridge
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month4Theorem5AuditWitnessExport
      rootSide MainRationality SondowAccepted bounds bound := by
  rcases bridge.2 with ⟨⟨pkg, audit⟩⟩
  exact ⟨⟨pkg, audit.month4_project_theorem5_audit_witness⟩⟩

theorem theorem5_audit_witness_iff_exact_external_boundary :
    PudlakTheorem5LiteratureInputAuditSurface.ProjectTheorem5AuditWitness ↔
      _root_.PudlakTheorem5ExactExternalBoundarySurface.Statement :=
  _root_.PudlakTheorem5ExactExternalBoundarySurface.statement_iff_project_theorem5_audit_witness.symm

theorem release_final_audit_bridge_to_month4_exact_external_boundary
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (bridge :
      Month3Month4ReleaseFinalAuditBridge
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month4ExactExternalBoundaryExport
      rootSide MainRationality SondowAccepted bounds bound := by
  rcases bridge.2 with ⟨⟨_pkg, audit⟩⟩
  exact audit.month4_exact_external_boundary_statement

structure CompleteMonth3Month4AuditCertificate
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (n : Nat) (haccepted : SondowAccepted n) : Prop where
  final_audit_bridge :
    Month3Month4ReleaseFinalAuditBridge
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

theorem complete_audit_certificate_of_final_audit_bridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (bridge :
      Month3Month4ReleaseFinalAuditBridge
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    CompleteMonth3Month4AuditCertificate
      rootSide MainRationality SondowAccepted bounds bound n haccepted where
  final_audit_bridge := bridge
  month3_accepted_proof_predicate_witness :=
    release_final_audit_bridge_to_month3_accepted_witness bridge
  month4_theorem5_audit_witness :=
    release_final_audit_bridge_to_month4_theorem5_audit_witness bridge
  month4_exact_external_boundary :=
    release_final_audit_bridge_to_month4_exact_external_boundary bridge
  public_gap_instantiation :=
    release_final_audit_bridge_to_public_gap_instantiation bridge
  not_main_rationality :=
    release_final_audit_bridge_not_main_rationality bridge

theorem release_final_audit_bridge_iff_complete_audit_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4ReleaseFinalAuditBridge
      rootSide MainRationality SondowAccepted bounds bound n haccepted ↔
      CompleteMonth3Month4AuditCertificate
        rootSide MainRationality SondowAccepted bounds bound n haccepted := by
  constructor
  · intro bridge
    exact complete_audit_certificate_of_final_audit_bridge bridge
  · intro cert
    exact cert.final_audit_bridge

theorem complete_audit_certificate_to_final_audit_bridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (cert :
      CompleteMonth3Month4AuditCertificate
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month3Month4ReleaseFinalAuditBridge
      rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  cert.final_audit_bridge

theorem complete_audit_certificate_to_month3_accepted_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (cert :
      CompleteMonth3Month4AuditCertificate
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month3AcceptedProofPredicateWitnessExport
      rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  cert.month3_accepted_proof_predicate_witness

theorem complete_audit_certificate_to_month4_theorem5_audit_witness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (cert :
      CompleteMonth3Month4AuditCertificate
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month4Theorem5AuditWitnessExport
      rootSide MainRationality SondowAccepted bounds bound :=
  cert.month4_theorem5_audit_witness

theorem complete_audit_certificate_to_month4_exact_external_boundary
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (cert :
      CompleteMonth3Month4AuditCertificate
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Month4ExactExternalBoundaryExport
      rootSide MainRationality SondowAccepted bounds bound :=
  cert.month4_exact_external_boundary

theorem complete_audit_certificate_to_public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (cert :
      CompleteMonth3Month4AuditCertificate
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  cert.public_gap_instantiation

theorem complete_audit_certificate_not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {haccepted : SondowAccepted n}
    (cert :
      CompleteMonth3Month4AuditCertificate
        rootSide MainRationality SondowAccepted bounds bound n haccepted) :
    ¬ MainRationality :=
  cert.not_main_rationality

theorem exactConvention_checklist_iff_release_final_audit_bridge
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
      Month3Month4ReleaseFinalAuditBridge
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  exactConvention_checklist_iff_final_audit_bridge_pair h m haccepted

theorem splitMinChecked_checklist_iff_release_final_audit_bridge
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
      Month3Month4ReleaseFinalAuditBridge
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  splitMinChecked_checklist_iff_final_audit_bridge_pair h m haccepted

theorem exactFamily_checklist_iff_release_final_audit_bridge
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
      Month3Month4ReleaseFinalAuditBridge
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  exactFamily_checklist_iff_final_audit_bridge_pair h m haccepted

theorem paper_route_iff_complete_audit_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (n : Nat) (haccepted : SondowAccepted n) :
    Month3Month4IndexedPaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      CompleteMonth3Month4AuditCertificate
        rootSide MainRationality SondowAccepted bounds bound n haccepted :=
  (paper_route_iff_release_final_audit_bridge n haccepted).trans
    (release_final_audit_bridge_iff_complete_audit_certificate n haccepted)

theorem exactConvention_checklist_iff_complete_audit_certificate
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
      CompleteMonth3Month4AuditCertificate
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  (exactConvention_checklist_iff_release_final_audit_bridge h m haccepted).trans
    (release_final_audit_bridge_iff_complete_audit_certificate m haccepted)

theorem splitMinChecked_checklist_iff_complete_audit_certificate
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
      CompleteMonth3Month4AuditCertificate
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  (splitMinChecked_checklist_iff_release_final_audit_bridge h m haccepted).trans
    (release_final_audit_bridge_iff_complete_audit_certificate m haccepted)

theorem exactFamily_checklist_iff_complete_audit_certificate
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
      CompleteMonth3Month4AuditCertificate
        h.toPudlakSideInputs MainRationality SondowAccepted
          bounds bound m haccepted :=
  (exactFamily_checklist_iff_release_final_audit_bridge h m haccepted).trans
    (release_final_audit_bridge_iff_complete_audit_certificate m haccepted)

theorem exactConvention_checklist_and_accepted_iff_exists_release_final_audit_bridge
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
        Month3Month4ReleaseFinalAuditBridge
          h.toPudlakSideInputs MainRationality SondowAccepted
            bounds bound m haccepted := by
  constructor
  · rintro ⟨checklist, ⟨m, haccepted⟩⟩
    exact
      ⟨m, haccepted,
        (exactConvention_checklist_iff_release_final_audit_bridge
          h m haccepted).mp checklist⟩
  · rintro ⟨m, haccepted, bridge⟩
    exact
      ⟨(exactConvention_checklist_iff_release_final_audit_bridge
          h m haccepted).mpr bridge,
        ⟨m, haccepted⟩⟩

theorem splitMinChecked_checklist_and_accepted_iff_exists_release_final_audit_bridge
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
        Month3Month4ReleaseFinalAuditBridge
          h.toPudlakSideInputs MainRationality SondowAccepted
            bounds bound m haccepted := by
  constructor
  · rintro ⟨checklist, ⟨m, haccepted⟩⟩
    exact
      ⟨m, haccepted,
        (splitMinChecked_checklist_iff_release_final_audit_bridge
          h m haccepted).mp checklist⟩
  · rintro ⟨m, haccepted, bridge⟩
    exact
      ⟨(splitMinChecked_checklist_iff_release_final_audit_bridge
          h m haccepted).mpr bridge,
        ⟨m, haccepted⟩⟩

theorem exactFamily_checklist_and_accepted_iff_exists_release_final_audit_bridge
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
        Month3Month4ReleaseFinalAuditBridge
          h.toPudlakSideInputs MainRationality SondowAccepted
            bounds bound m haccepted := by
  constructor
  · rintro ⟨checklist, ⟨m, haccepted⟩⟩
    exact
      ⟨m, haccepted,
        (exactFamily_checklist_iff_release_final_audit_bridge
          h m haccepted).mp checklist⟩
  · rintro ⟨m, haccepted, bridge⟩
    exact
      ⟨(exactFamily_checklist_iff_release_final_audit_bridge
          h m haccepted).mpr bridge,
        ⟨m, haccepted⟩⟩

theorem paper_route_and_accepted_iff_exists_complete_audit_certificate
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    (Month3Month4IndexedPaperRoute
        rootSide MainRationality SondowAccepted bounds bound ∧
      ∃ n : Nat, SondowAccepted n) ↔
      ∃ n : Nat, ∃ haccepted : SondowAccepted n,
        CompleteMonth3Month4AuditCertificate
          rootSide MainRationality SondowAccepted bounds bound
            n haccepted := by
  constructor
  · rintro ⟨route, ⟨n, haccepted⟩⟩
    exact
      ⟨n, haccepted,
        (paper_route_iff_complete_audit_certificate
          n haccepted).mp route⟩
  · rintro ⟨n, haccepted, cert⟩
    exact
      ⟨(paper_route_iff_complete_audit_certificate
          n haccepted).mpr cert,
        ⟨n, haccepted⟩⟩

theorem exactConvention_checklist_and_accepted_iff_exists_complete_audit_certificate
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
        CompleteMonth3Month4AuditCertificate
          h.toPudlakSideInputs MainRationality SondowAccepted
            bounds bound m haccepted := by
  constructor
  · rintro ⟨checklist, ⟨m, haccepted⟩⟩
    exact
      ⟨m, haccepted,
        (exactConvention_checklist_iff_complete_audit_certificate
          h m haccepted).mp checklist⟩
  · rintro ⟨m, haccepted, cert⟩
    exact
      ⟨(exactConvention_checklist_iff_complete_audit_certificate
          h m haccepted).mpr cert,
        ⟨m, haccepted⟩⟩

theorem splitMinChecked_checklist_and_accepted_iff_exists_complete_audit_certificate
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
        CompleteMonth3Month4AuditCertificate
          h.toPudlakSideInputs MainRationality SondowAccepted
            bounds bound m haccepted := by
  constructor
  · rintro ⟨checklist, ⟨m, haccepted⟩⟩
    exact
      ⟨m, haccepted,
        (splitMinChecked_checklist_iff_complete_audit_certificate
          h m haccepted).mp checklist⟩
  · rintro ⟨m, haccepted, cert⟩
    exact
      ⟨(splitMinChecked_checklist_iff_complete_audit_certificate
          h m haccepted).mpr cert,
        ⟨m, haccepted⟩⟩

theorem exactFamily_checklist_and_accepted_iff_exists_complete_audit_certificate
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
        CompleteMonth3Month4AuditCertificate
          h.toPudlakSideInputs MainRationality SondowAccepted
            bounds bound m haccepted := by
  constructor
  · rintro ⟨checklist, ⟨m, haccepted⟩⟩
    exact
      ⟨m, haccepted,
        (exactFamily_checklist_iff_complete_audit_certificate
          h m haccepted).mp checklist⟩
  · rintro ⟨m, haccepted, cert⟩
    exact
      ⟨(exactFamily_checklist_iff_complete_audit_certificate
          h m haccepted).mpr cert,
        ⟨m, haccepted⟩⟩

theorem exactConvention_checklist_to_release_public_gap_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  release_final_audit_bridge_to_public_gap_instantiation
    ((exactConvention_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem exactConvention_checklist_to_release_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    ¬ MainRationality :=
  release_final_audit_bridge_not_main_rationality
    ((exactConvention_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem splitMinChecked_checklist_to_release_public_gap_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  release_final_audit_bridge_to_public_gap_instantiation
    ((splitMinChecked_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem splitMinChecked_checklist_to_release_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    ¬ MainRationality :=
  release_final_audit_bridge_not_main_rationality
    ((splitMinChecked_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem exactFamily_checklist_to_release_public_gap_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  release_final_audit_bridge_to_public_gap_instantiation
    ((exactFamily_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem exactFamily_checklist_to_release_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    ¬ MainRationality :=
  release_final_audit_bridge_not_main_rationality
    ((exactFamily_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem exactConvention_checklist_to_release_month3_accepted_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Month3AcceptedProofPredicateWitnessExport
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound
        m haccepted :=
  release_final_audit_bridge_to_month3_accepted_witness
    ((exactConvention_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem splitMinChecked_checklist_to_release_month3_accepted_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Month3AcceptedProofPredicateWitnessExport
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound
        m haccepted :=
  release_final_audit_bridge_to_month3_accepted_witness
    ((splitMinChecked_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem exactFamily_checklist_to_release_month3_accepted_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Month3AcceptedProofPredicateWitnessExport
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound
        m haccepted :=
  release_final_audit_bridge_to_month3_accepted_witness
    ((exactFamily_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem exactConvention_checklist_to_release_month4_theorem5_audit_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Month4Theorem5AuditWitnessExport
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  release_final_audit_bridge_to_month4_theorem5_audit_witness
    ((exactConvention_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem splitMinChecked_checklist_to_release_month4_theorem5_audit_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Month4Theorem5AuditWitnessExport
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  release_final_audit_bridge_to_month4_theorem5_audit_witness
    ((splitMinChecked_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem exactFamily_checklist_to_release_month4_theorem5_audit_witness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Month4Theorem5AuditWitnessExport
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  release_final_audit_bridge_to_month4_theorem5_audit_witness
    ((exactFamily_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem exactConvention_checklist_to_release_month4_exact_external_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Month4ExactExternalBoundaryExport
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  release_final_audit_bridge_to_month4_exact_external_boundary
    ((exactConvention_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem splitMinChecked_checklist_to_release_month4_exact_external_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Month4ExactExternalBoundaryExport
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  release_final_audit_bridge_to_month4_exact_external_boundary
    ((splitMinChecked_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

theorem exactFamily_checklist_to_release_month4_exact_external_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist :
      Nonempty (Σ' gap_cert :
        ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert))
    (m : Nat) (haccepted : SondowAccepted m) :
    Month4ExactExternalBoundaryExport
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  release_final_audit_bridge_to_month4_exact_external_boundary
    ((exactFamily_checklist_iff_release_final_audit_bridge
      h m haccepted).mp checklist)

end SondowProjectMonth3Month4ReleaseTheoremExportSurface
end SondowMainCheckedCodeBridge
