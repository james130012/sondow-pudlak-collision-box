/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakMonth1ReleaseBoundaryAuditSurface

/-!
# Month 1 auditable closure surface

This is the final single-import surface for the current Month 1 proof-probe
closure.  It gives stable public names for the release-boundary audits and
their endpoint extractions, while delegating all proofs to the
release-boundary audit surface.

The intended audit path is:

`concrete checklist ↔ auditable closure ↔ paper-ready route ↔ public bundle
origin`, with endpoint extraction to encoding, same-object closure, public gap,
public collision, and `¬ MainRationality`.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakMonth1AuditableClosureSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakMonth1ReleaseBoundaryAuditSurface

abbrev Month1AuditableConcreteRoute
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop :=
  Month1ConcreteChecklistRoute
    rootSide MainRationality SondowAccepted bounds bound

abbrev Month1AuditablePaperRoute
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop :=
  Month1ReleaseBoundaryPaperRoute
    rootSide MainRationality SondowAccepted bounds bound

abbrev Month1AuditablePublicOrigin
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop :=
  Month1ReleaseBoundaryPublicOrigin
    rootSide MainRationality SondowAccepted bounds bound

abbrev Month1AuditableEndpoints
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop :=
  Month1ReleaseBoundaryAuditEndpoints
    rootSide MainRationality SondowAccepted bounds bound

abbrev Month1AuditableExactConventionClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactConventionInputs
        Ax A B halign)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop :=
  Month1ExactConventionReleaseBoundaryAudit
    h MainRationality SondowAccepted bounds bound

abbrev Month1AuditableSplitMinCheckedClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExactSplitMinCheckedInputs
        Ax A B halign)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop :=
  Month1SplitMinCheckedReleaseBoundaryAudit
    h MainRationality SondowAccepted bounds bound

abbrev Month1AuditableExactFamilyClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (h :
      SondowProjectLocalPudlakBottomExternalTheorem5ExactFamilyExactnessInputs
        Ax A B halign)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop :=
  Month1ExactFamilyReleaseBoundaryAudit
    h MainRationality SondowAccepted bounds bound

theorem exactConvention_closure_iff_concrete
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
    Month1AuditableExactConventionClosure
      h MainRationality SondowAccepted bounds bound ↔
      Month1AuditableConcreteRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  Month1ExactConventionReleaseBoundaryAudit.iff_concrete_checklist h

theorem exactConvention_closure_iff_paper
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
    Month1AuditableExactConventionClosure
      h MainRationality SondowAccepted bounds bound ↔
      Month1AuditablePaperRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  Month1ExactConventionReleaseBoundaryAudit.iff_paper_ready_route h

theorem exactConvention_closure_iff_public_origin
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
    Month1AuditableExactConventionClosure
      h MainRationality SondowAccepted bounds bound ↔
      Month1AuditablePublicOrigin
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  Month1ExactConventionReleaseBoundaryAudit.iff_public_bundle_origin h

theorem splitMinChecked_closure_iff_concrete
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
    Month1AuditableSplitMinCheckedClosure
      h MainRationality SondowAccepted bounds bound ↔
      Month1AuditableConcreteRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  Month1SplitMinCheckedReleaseBoundaryAudit.iff_concrete_checklist h

theorem splitMinChecked_closure_iff_paper
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
    Month1AuditableSplitMinCheckedClosure
      h MainRationality SondowAccepted bounds bound ↔
      Month1AuditablePaperRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  Month1SplitMinCheckedReleaseBoundaryAudit.iff_paper_ready_route h

theorem splitMinChecked_closure_iff_public_origin
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
    Month1AuditableSplitMinCheckedClosure
      h MainRationality SondowAccepted bounds bound ↔
      Month1AuditablePublicOrigin
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  Month1SplitMinCheckedReleaseBoundaryAudit.iff_public_bundle_origin h

theorem exactFamily_closure_iff_concrete
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
    Month1AuditableExactFamilyClosure
      h MainRationality SondowAccepted bounds bound ↔
      Month1AuditableConcreteRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  Month1ExactFamilyReleaseBoundaryAudit.iff_concrete_checklist h

theorem exactFamily_closure_iff_paper
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
    Month1AuditableExactFamilyClosure
      h MainRationality SondowAccepted bounds bound ↔
      Month1AuditablePaperRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  Month1ExactFamilyReleaseBoundaryAudit.iff_paper_ready_route h

theorem exactFamily_closure_iff_public_origin
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
    Month1AuditableExactFamilyClosure
      h MainRationality SondowAccepted bounds bound ↔
      Month1AuditablePublicOrigin
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  Month1ExactFamilyReleaseBoundaryAudit.iff_public_bundle_origin h

theorem exactConvention_closure_to_encoding_probe
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
      Month1AuditableExactConventionClosure
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      Σ' checklist :
        SondowProjectPudlakConcreteBridgeChecklist
          h.toPudlakSideInputs gap_cert,
        SondowProjectPudlakMonth1PublicSyncCandidateSurface.Month1PublicSyncEncodingProbe
          h.toPudlakSideInputs gap_cert checklist) :=
  Month1ExactConventionReleaseBoundaryAudit.to_encoding_probe audit

theorem exactConvention_closure_to_same_object_closure
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
      Month1AuditableExactConventionClosure
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  Month1ExactConventionReleaseBoundaryAudit.to_same_object_closure audit

theorem exactConvention_closure_to_public_gap
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
      Month1AuditableExactConventionClosure
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  Month1ExactConventionReleaseBoundaryAudit.to_public_gap audit

theorem exactConvention_closure_to_public_collision
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
      Month1AuditableExactConventionClosure
        h MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation
      MainRationality) :=
  Month1ExactConventionReleaseBoundaryAudit.to_public_collision audit

theorem exactConvention_closure_not_main_rationality
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
      Month1AuditableExactConventionClosure
        h MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  Month1ExactConventionReleaseBoundaryAudit.not_main_rationality audit

theorem splitMinChecked_closure_not_main_rationality
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
      Month1AuditableSplitMinCheckedClosure
        h MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  Month1SplitMinCheckedReleaseBoundaryAudit.not_main_rationality audit

theorem exactFamily_closure_not_main_rationality
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
      Month1AuditableExactFamilyClosure
        h MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  Month1ExactFamilyReleaseBoundaryAudit.not_main_rationality audit

/-!
Intentional single-import probes.
-/

#check Month1AuditableConcreteRoute
#check Month1AuditablePaperRoute
#check Month1AuditablePublicOrigin
#check Month1AuditableExactConventionClosure
#check Month1AuditableSplitMinCheckedClosure
#check Month1AuditableExactFamilyClosure
#check exactConvention_closure_iff_concrete
#check exactConvention_closure_iff_paper
#check exactConvention_closure_iff_public_origin
#check splitMinChecked_closure_iff_concrete
#check splitMinChecked_closure_iff_paper
#check splitMinChecked_closure_iff_public_origin
#check exactFamily_closure_iff_concrete
#check exactFamily_closure_iff_paper
#check exactFamily_closure_iff_public_origin
#check exactConvention_closure_to_encoding_probe
#check exactConvention_closure_to_same_object_closure
#check exactConvention_closure_to_public_gap
#check exactConvention_closure_to_public_collision
#check exactConvention_closure_not_main_rationality
#check splitMinChecked_closure_not_main_rationality
#check exactFamily_closure_not_main_rationality

end SondowProjectPudlakMonth1AuditableClosureSurface
end SondowMainCheckedCodeBridge
