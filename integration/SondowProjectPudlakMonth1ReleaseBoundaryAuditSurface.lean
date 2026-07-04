/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakMonth1PaperReadyTheoremSurface

/-!
# Month 1 release-boundary audit surface

This module is the aggregate audit surface for the Month 1
same-object/public-bridge route.  It records, for each of the three project
entry points, the exact release boundary:

* concrete CnBox/Pudlak checklist;
* paper-ready collision route;
* public bundle origin;
* extracted audit endpoints.

The main theorems keep the boundary bidirectional.  A release-boundary audit is
equivalent to the concrete checklist, to the paper-ready route, and to the
public bundle origin; the final public endpoints are fields extracted from that
same audit object.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakMonth1ReleaseBoundaryAuditSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakMonth1PaperReadyTheoremSurface
open SondowProjectPudlakMonth1PublicSyncCandidateSurface

abbrev Month1ConcreteChecklistRoute
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop :=
  Nonempty (Σ' gap_cert :
    ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound,
    SondowProjectPudlakConcreteBridgeChecklist rootSide gap_cert)

abbrev Month1ReleaseBoundaryPaperRoute
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop :=
  Month1PaperReadyCollisionRoute
    rootSide MainRationality SondowAccepted bounds bound

abbrev Month1ReleaseBoundaryPublicOrigin
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop :=
  Month1PaperReadyPublicBundleOrigin
    rootSide MainRationality SondowAccepted bounds bound

abbrev Month1ReleaseBoundaryAuditEndpoints
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop :=
  Month1PublicSyncAuditEndpoints
    rootSide MainRationality SondowAccepted bounds bound

structure Month1ExactConventionReleaseBoundaryAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop where
  concrete_checklist :
    Month1ConcreteChecklistRoute
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound
  paper_ready_route :
    Month1ReleaseBoundaryPaperRoute
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound
  public_bundle_origin :
    Month1ReleaseBoundaryPublicOrigin
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound
  audit_endpoints :
    Month1ReleaseBoundaryAuditEndpoints
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound

structure Month1SplitMinCheckedReleaseBoundaryAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop where
  concrete_checklist :
    Month1ConcreteChecklistRoute
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound
  paper_ready_route :
    Month1ReleaseBoundaryPaperRoute
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound
  public_bundle_origin :
    Month1ReleaseBoundaryPublicOrigin
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound
  audit_endpoints :
    Month1ReleaseBoundaryAuditEndpoints
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound

structure Month1ExactFamilyReleaseBoundaryAudit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop where
  concrete_checklist :
    Month1ConcreteChecklistRoute
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound
  paper_ready_route :
    Month1ReleaseBoundaryPaperRoute
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound
  public_bundle_origin :
    Month1ReleaseBoundaryPublicOrigin
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound
  audit_endpoints :
    Month1ReleaseBoundaryAuditEndpoints
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound

namespace Month1ExactConventionReleaseBoundaryAudit

def ofConcreteChecklist
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
    (checklist :
      Month1ConcreteChecklistRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1ExactConventionReleaseBoundaryAudit
      h MainRationality SondowAccepted bounds bound where
  concrete_checklist := checklist
  paper_ready_route :=
    (exactConvention_checklist_iff_paper_ready_route h).mp checklist
  public_bundle_origin :=
    (paper_ready_route_iff_public_bundle_origin
      (rootSide := h.toPudlakSideInputs)
      (MainRationality := MainRationality)
      (SondowAccepted := SondowAccepted)
      (bounds := bounds)
      (bound := bound)).mp
        ((exactConvention_checklist_iff_paper_ready_route h).mp checklist)
  audit_endpoints :=
    exactConvention_checklist_to_audit_endpoints h checklist

theorem iff_concrete_checklist
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
    Month1ExactConventionReleaseBoundaryAudit
      h MainRationality SondowAccepted bounds bound ↔
      Month1ConcreteChecklistRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound := by
  constructor
  · intro audit
    exact audit.concrete_checklist
  · intro checklist
    exact ofConcreteChecklist h checklist

theorem iff_paper_ready_route
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
    Month1ExactConventionReleaseBoundaryAudit
      h MainRationality SondowAccepted bounds bound ↔
      Month1ReleaseBoundaryPaperRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (iff_concrete_checklist h).trans
    (exactConvention_checklist_iff_paper_ready_route h)

theorem iff_public_bundle_origin
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
    Month1ExactConventionReleaseBoundaryAudit
      h MainRationality SondowAccepted bounds bound ↔
      Month1ReleaseBoundaryPublicOrigin
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (iff_paper_ready_route h).trans
    (paper_ready_route_iff_public_bundle_origin
      (rootSide := h.toPudlakSideInputs)
      (MainRationality := MainRationality)
      (SondowAccepted := SondowAccepted)
      (bounds := bounds)
      (bound := bound))

theorem to_encoding_probe
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign}
    (audit :
      Month1ExactConventionReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert,
        Month1PublicSyncEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) :=
  audit.audit_endpoints.encoding_probe

theorem to_same_object_closure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign}
    (audit :
      Month1ExactConventionReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  audit.audit_endpoints.same_object_closure

theorem to_public_gap
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign}
    (audit :
      Month1ExactConventionReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  audit.audit_endpoints.public_gap_instantiation

theorem to_public_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign}
    (audit :
      Month1ExactConventionReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation
      MainRationality) :=
  audit.audit_endpoints.public_collision_instantiation

theorem not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign}
    (audit :
      Month1ExactConventionReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  audit.audit_endpoints.not_main_rationality

end Month1ExactConventionReleaseBoundaryAudit

namespace Month1SplitMinCheckedReleaseBoundaryAudit

def ofConcreteChecklist
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
    (checklist :
      Month1ConcreteChecklistRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1SplitMinCheckedReleaseBoundaryAudit
      h MainRationality SondowAccepted bounds bound where
  concrete_checklist := checklist
  paper_ready_route :=
    (splitMinChecked_checklist_iff_paper_ready_route h).mp checklist
  public_bundle_origin :=
    (paper_ready_route_iff_public_bundle_origin
      (rootSide := h.toPudlakSideInputs)
      (MainRationality := MainRationality)
      (SondowAccepted := SondowAccepted)
      (bounds := bounds)
      (bound := bound)).mp
        ((splitMinChecked_checklist_iff_paper_ready_route h).mp checklist)
  audit_endpoints :=
    splitMinChecked_checklist_to_audit_endpoints h checklist

theorem iff_concrete_checklist
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
    Month1SplitMinCheckedReleaseBoundaryAudit
      h MainRationality SondowAccepted bounds bound ↔
      Month1ConcreteChecklistRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound := by
  constructor
  · intro audit
    exact audit.concrete_checklist
  · intro checklist
    exact ofConcreteChecklist h checklist

theorem iff_paper_ready_route
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
    Month1SplitMinCheckedReleaseBoundaryAudit
      h MainRationality SondowAccepted bounds bound ↔
      Month1ReleaseBoundaryPaperRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (iff_concrete_checklist h).trans
    (splitMinChecked_checklist_iff_paper_ready_route h)

theorem iff_public_bundle_origin
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
    Month1SplitMinCheckedReleaseBoundaryAudit
      h MainRationality SondowAccepted bounds bound ↔
      Month1ReleaseBoundaryPublicOrigin
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (iff_paper_ready_route h).trans
    (paper_ready_route_iff_public_bundle_origin
      (rootSide := h.toPudlakSideInputs)
      (MainRationality := MainRationality)
      (SondowAccepted := SondowAccepted)
      (bounds := bounds)
      (bound := bound))

theorem to_encoding_probe
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign}
    (audit :
      Month1SplitMinCheckedReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert,
        Month1PublicSyncEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) :=
  audit.audit_endpoints.encoding_probe

theorem to_same_object_closure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign}
    (audit :
      Month1SplitMinCheckedReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  audit.audit_endpoints.same_object_closure

theorem to_public_gap
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign}
    (audit :
      Month1SplitMinCheckedReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  audit.audit_endpoints.public_gap_instantiation

theorem to_public_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign}
    (audit :
      Month1SplitMinCheckedReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation
      MainRationality) :=
  audit.audit_endpoints.public_collision_instantiation

theorem not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign}
    (audit :
      Month1SplitMinCheckedReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  audit.audit_endpoints.not_main_rationality

end Month1SplitMinCheckedReleaseBoundaryAudit

namespace Month1ExactFamilyReleaseBoundaryAudit

def ofConcreteChecklist
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
    (checklist :
      Month1ConcreteChecklistRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1ExactFamilyReleaseBoundaryAudit
      h MainRationality SondowAccepted bounds bound where
  concrete_checklist := checklist
  paper_ready_route :=
    (exactFamily_checklist_iff_paper_ready_route h).mp checklist
  public_bundle_origin :=
    (paper_ready_route_iff_public_bundle_origin
      (rootSide := h.toPudlakSideInputs)
      (MainRationality := MainRationality)
      (SondowAccepted := SondowAccepted)
      (bounds := bounds)
      (bound := bound)).mp
        ((exactFamily_checklist_iff_paper_ready_route h).mp checklist)
  audit_endpoints :=
    exactFamily_checklist_to_audit_endpoints h checklist

theorem iff_concrete_checklist
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
    Month1ExactFamilyReleaseBoundaryAudit
      h MainRationality SondowAccepted bounds bound ↔
      Month1ConcreteChecklistRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound := by
  constructor
  · intro audit
    exact audit.concrete_checklist
  · intro checklist
    exact ofConcreteChecklist h checklist

theorem iff_paper_ready_route
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
    Month1ExactFamilyReleaseBoundaryAudit
      h MainRationality SondowAccepted bounds bound ↔
      Month1ReleaseBoundaryPaperRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (iff_concrete_checklist h).trans
    (exactFamily_checklist_iff_paper_ready_route h)

theorem iff_public_bundle_origin
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
    Month1ExactFamilyReleaseBoundaryAudit
      h MainRationality SondowAccepted bounds bound ↔
      Month1ReleaseBoundaryPublicOrigin
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (iff_paper_ready_route h).trans
    (paper_ready_route_iff_public_bundle_origin
      (rootSide := h.toPudlakSideInputs)
      (MainRationality := MainRationality)
      (SondowAccepted := SondowAccepted)
      (bounds := bounds)
      (bound := bound))

theorem to_encoding_probe
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign}
    (audit :
      Month1ExactFamilyReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert,
        Month1PublicSyncEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) :=
  audit.audit_endpoints.encoding_probe

theorem to_same_object_closure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign}
    (audit :
      Month1ExactFamilyReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  audit.audit_endpoints.same_object_closure

theorem to_public_gap
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign}
    (audit :
      Month1ExactFamilyReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  audit.audit_endpoints.public_gap_instantiation

theorem to_public_collision
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign}
    (audit :
      Month1ExactFamilyReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation
      MainRationality) :=
  audit.audit_endpoints.public_collision_instantiation

theorem not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign}
    (audit :
      Month1ExactFamilyReleaseBoundaryAudit
        h MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  audit.audit_endpoints.not_main_rationality

end Month1ExactFamilyReleaseBoundaryAudit

/-!
Intentional release-boundary probes.
-/

#check Month1ConcreteChecklistRoute
#check Month1ReleaseBoundaryPaperRoute
#check Month1ReleaseBoundaryPublicOrigin
#check Month1ReleaseBoundaryAuditEndpoints
#check Month1ExactConventionReleaseBoundaryAudit
#check Month1SplitMinCheckedReleaseBoundaryAudit
#check Month1ExactFamilyReleaseBoundaryAudit
#check Month1ExactConventionReleaseBoundaryAudit.iff_concrete_checklist
#check Month1ExactConventionReleaseBoundaryAudit.iff_paper_ready_route
#check Month1ExactConventionReleaseBoundaryAudit.iff_public_bundle_origin
#check Month1ExactConventionReleaseBoundaryAudit.to_encoding_probe
#check Month1ExactConventionReleaseBoundaryAudit.to_same_object_closure
#check Month1ExactConventionReleaseBoundaryAudit.to_public_gap
#check Month1ExactConventionReleaseBoundaryAudit.to_public_collision
#check Month1ExactConventionReleaseBoundaryAudit.not_main_rationality
#check Month1SplitMinCheckedReleaseBoundaryAudit.iff_concrete_checklist
#check Month1SplitMinCheckedReleaseBoundaryAudit.iff_paper_ready_route
#check Month1SplitMinCheckedReleaseBoundaryAudit.iff_public_bundle_origin
#check Month1SplitMinCheckedReleaseBoundaryAudit.not_main_rationality
#check Month1ExactFamilyReleaseBoundaryAudit.iff_concrete_checklist
#check Month1ExactFamilyReleaseBoundaryAudit.iff_paper_ready_route
#check Month1ExactFamilyReleaseBoundaryAudit.iff_public_bundle_origin
#check Month1ExactFamilyReleaseBoundaryAudit.not_main_rationality

end SondowProjectPudlakMonth1ReleaseBoundaryAuditSurface
end SondowMainCheckedCodeBridge
