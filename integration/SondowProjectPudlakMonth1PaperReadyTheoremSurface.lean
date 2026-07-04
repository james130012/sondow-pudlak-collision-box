/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakMonth1PublicSyncCandidateSurface

/-!
# Month 1 paper-ready theorem surface

This file is the paper-facing endpoint for the current Month 1 route.  It does
not introduce a new assumption or a new gap criterion.  It gives stable theorem
names showing that the concrete CnBox/Pudlak checklist is equivalent to the
public-sync candidate, and that the checklist directly yields the same audit
endpoints:

* encoding roundtrip and PA finite-consistency transport;
* project same-object closure;
* public gap and public collision instantiation;
* the final `¬ MainRationality` endpoint.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakMonth1PaperReadyTheoremSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakMonth1PublicSyncCandidateSurface

abbrev Month1PaperReadyCollisionRoute
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop :=
  Nonempty (Month1PublicSyncCandidate
    rootSide MainRationality SondowAccepted bounds bound)

abbrev Month1PaperReadyPublicBundleOrigin
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop :=
  Nonempty (Σ' bundle : ProjectPublicCollisionCertificateBundle
    MainRationality SondowAccepted bounds bound,
    SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
      rootSide bundle)

theorem paper_ready_route_iff_public_bundle_origin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Month1PaperReadyCollisionRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month1PaperReadyPublicBundleOrigin
        rootSide MainRationality SondowAccepted bounds bound :=
  Month1PublicSyncCandidate.nonempty_iff_public_bundle_origin

theorem exactConvention_checklist_iff_paper_ready_route
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Month1PaperReadyCollisionRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  Month1PublicSyncCandidate.exactConvention_checklist_iff_public_sync_candidate h

theorem splitMinChecked_checklist_iff_paper_ready_route
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Month1PaperReadyCollisionRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  Month1PublicSyncCandidate.splitMinChecked_checklist_iff_public_sync_candidate h

theorem exactFamily_checklist_iff_paper_ready_route
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Month1PaperReadyCollisionRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  Month1PublicSyncCandidate.exactFamily_checklist_iff_public_sync_candidate h

theorem exactConvention_checklist_to_audit_endpoints
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Month1PublicSyncAuditEndpoints
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound := by
  have candidate_nonempty :
      Month1PaperReadyCollisionRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
    (exactConvention_checklist_iff_paper_ready_route h).mp
      checklist_nonempty
  exact
    Month1PublicSyncCandidate.exactConvention_nonempty_to_audit_endpoints
      h candidate_nonempty

theorem splitMinChecked_checklist_to_audit_endpoints
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Month1PublicSyncAuditEndpoints
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound := by
  have candidate_nonempty :
      Month1PaperReadyCollisionRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
    (splitMinChecked_checklist_iff_paper_ready_route h).mp
      checklist_nonempty
  exact
    Month1PublicSyncCandidate.splitMinChecked_nonempty_to_audit_endpoints
      h candidate_nonempty

theorem exactFamily_checklist_to_audit_endpoints
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Month1PublicSyncAuditEndpoints
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound := by
  have candidate_nonempty :
      Month1PaperReadyCollisionRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
    (exactFamily_checklist_iff_paper_ready_route h).mp
      checklist_nonempty
  exact
    Month1PublicSyncCandidate.exactFamily_nonempty_to_audit_endpoints
      h candidate_nonempty

theorem exactConvention_checklist_to_encoding_probe
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert,
        Month1PublicSyncEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) :=
  (exactConvention_checklist_to_audit_endpoints h checklist_nonempty).encoding_probe

theorem splitMinChecked_checklist_to_encoding_probe
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert,
        Month1PublicSyncEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) :=
  (splitMinChecked_checklist_to_audit_endpoints h checklist_nonempty).encoding_probe

theorem exactFamily_checklist_to_encoding_probe
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert,
        Month1PublicSyncEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) :=
  (exactFamily_checklist_to_audit_endpoints h checklist_nonempty).encoding_probe

theorem exactConvention_checklist_to_same_object_closure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  (exactConvention_checklist_to_audit_endpoints h checklist_nonempty).same_object_closure

theorem splitMinChecked_checklist_to_same_object_closure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_checklist_to_audit_endpoints h checklist_nonempty).same_object_closure

theorem exactFamily_checklist_to_same_object_closure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  (exactFamily_checklist_to_audit_endpoints h checklist_nonempty).same_object_closure

theorem exactConvention_checklist_to_public_gap
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  (exactConvention_checklist_to_audit_endpoints h checklist_nonempty).public_gap_instantiation

theorem splitMinChecked_checklist_to_public_gap
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  (splitMinChecked_checklist_to_audit_endpoints h checklist_nonempty).public_gap_instantiation

theorem exactFamily_checklist_to_public_gap
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  (exactFamily_checklist_to_audit_endpoints h checklist_nonempty).public_gap_instantiation

theorem exactConvention_checklist_to_public_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation MainRationality) :=
  (exactConvention_checklist_to_audit_endpoints h checklist_nonempty).public_collision_instantiation

theorem splitMinChecked_checklist_to_public_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation MainRationality) :=
  (splitMinChecked_checklist_to_audit_endpoints h checklist_nonempty).public_collision_instantiation

theorem exactFamily_checklist_to_public_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation MainRationality) :=
  (exactFamily_checklist_to_audit_endpoints h checklist_nonempty).public_collision_instantiation

theorem exactConvention_checklist_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    ¬ MainRationality :=
  (exactConvention_checklist_to_audit_endpoints h checklist_nonempty).not_main_rationality

theorem splitMinChecked_checklist_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    ¬ MainRationality :=
  (splitMinChecked_checklist_to_audit_endpoints h checklist_nonempty).not_main_rationality

theorem exactFamily_checklist_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (checklist_nonempty : Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert)) :
    ¬ MainRationality :=
  (exactFamily_checklist_to_audit_endpoints h checklist_nonempty).not_main_rationality

/-!
Intentional paper-ready probes.
-/

#check Month1PaperReadyCollisionRoute
#check Month1PaperReadyPublicBundleOrigin
#check paper_ready_route_iff_public_bundle_origin
#check exactConvention_checklist_iff_paper_ready_route
#check splitMinChecked_checklist_iff_paper_ready_route
#check exactFamily_checklist_iff_paper_ready_route
#check exactConvention_checklist_to_audit_endpoints
#check splitMinChecked_checklist_to_audit_endpoints
#check exactFamily_checklist_to_audit_endpoints
#check exactConvention_checklist_to_encoding_probe
#check splitMinChecked_checklist_to_encoding_probe
#check exactFamily_checklist_to_encoding_probe
#check exactConvention_checklist_to_same_object_closure
#check splitMinChecked_checklist_to_same_object_closure
#check exactFamily_checklist_to_same_object_closure
#check exactConvention_checklist_to_public_gap
#check splitMinChecked_checklist_to_public_gap
#check exactFamily_checklist_to_public_gap
#check exactConvention_checklist_to_public_collision
#check splitMinChecked_checklist_to_public_collision
#check exactFamily_checklist_to_public_collision
#check exactConvention_checklist_not_main_rationality
#check splitMinChecked_checklist_not_main_rationality
#check exactFamily_checklist_not_main_rationality

end SondowProjectPudlakMonth1PaperReadyTheoremSurface
end SondowMainCheckedCodeBridge
