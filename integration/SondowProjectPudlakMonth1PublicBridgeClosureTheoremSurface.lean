/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakMonth1NoWeakeningAuditSurface

/-!
# Month 1 public bridge closure theorem surface

This is the final single-import theorem layer for the Month 1 same-object and
public bridge closure route.

The layer wraps the no-weakening audit object and exposes:

* equivalences between the concrete route, paper route, checkpoint, and public
  origin;
* the CnBox equation endpoints;
* same-object, public gap, public collision, and `¬ MainRationality` endpoints;
* constructors from the checkpoint, concrete route, paper route, and public
  origin for each Pudlak entry surface.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakMonth1PublicBridgeClosureTheoremSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakMonth1AuditableClosureSurface
open SondowProjectPudlakMonth1EquationEndpointSurface
open SondowProjectPudlakMonth1NoWeakeningAuditSurface
open SondowProjectPudlakMonth1ReleaseCheckpointSurface

structure Month1PublicBridgeClosureTheoremLayer
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop where
  audit :
    Month1ReleaseNoWeakeningAudit
      rootSide MainRationality SondowAccepted bounds bound

namespace Month1PublicBridgeClosureTheoremLayer

theorem concrete_iff_checkpoint
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (layer :
      Month1PublicBridgeClosureTheoremLayer
        rootSide MainRationality SondowAccepted bounds bound) :
    Month1AuditableConcreteRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month1PublicReleaseCheckpoint
        rootSide MainRationality SondowAccepted bounds bound :=
  layer.audit.equivalences.concrete_iff_checkpoint

theorem paper_iff_checkpoint
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (layer :
      Month1PublicBridgeClosureTheoremLayer
        rootSide MainRationality SondowAccepted bounds bound) :
    Month1AuditablePaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month1PublicReleaseCheckpoint
        rootSide MainRationality SondowAccepted bounds bound :=
  layer.audit.equivalences.paper_iff_checkpoint

theorem checkpoint_iff_public_origin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (layer :
      Month1PublicBridgeClosureTheoremLayer
        rootSide MainRationality SondowAccepted bounds bound) :
    Month1PublicReleaseCheckpoint
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month1AuditablePublicOrigin
        rootSide MainRationality SondowAccepted bounds bound :=
  layer.audit.equivalences.checkpoint_iff_public_origin

theorem concrete_iff_public_origin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (layer :
      Month1PublicBridgeClosureTheoremLayer
        rootSide MainRationality SondowAccepted bounds bound) :
    Month1AuditableConcreteRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month1AuditablePublicOrigin
        rootSide MainRationality SondowAccepted bounds bound :=
  layer.audit.equivalences.concrete_iff_public_origin

theorem paper_iff_public_origin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (layer :
      Month1PublicBridgeClosureTheoremLayer
        rootSide MainRationality SondowAccepted bounds bound) :
    Month1AuditablePaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month1AuditablePublicOrigin
        rootSide MainRationality SondowAccepted bounds bound :=
  layer.audit.equivalences.paper_iff_public_origin

theorem equation_endpoints
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (layer :
      Month1PublicBridgeClosureTheoremLayer
        rootSide MainRationality SondowAccepted bounds bound) :
    Month1CnBoxEquationEndpoints :=
  layer.audit.equations

theorem target_eq_box_formula
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (layer :
      Month1PublicBridgeClosureTheoremLayer
        rootSide MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula :=
  layer.audit.target_eq_box_formula m

theorem box_code_roundtrip_to_target
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (layer :
      Month1PublicBridgeClosureTheoremLayer
        rootSide MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m) :=
  layer.audit.box_code_roundtrip_to_target m

theorem carries_iff_pa_finite_consistency
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (layer :
      Month1PublicBridgeClosureTheoremLayer
        rootSide MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m :=
  layer.audit.carries_iff_pa_finite_consistency m

theorem same_object_closure
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (layer :
      Month1PublicBridgeClosureTheoremLayer
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  layer.audit.same_object_closure

theorem public_gap_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (layer :
      Month1PublicBridgeClosureTheoremLayer
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  layer.audit.public_gap_instantiation

theorem public_collision_instantiation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (layer :
      Month1PublicBridgeClosureTheoremLayer
        rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation
      MainRationality) :=
  layer.audit.public_collision_instantiation

theorem not_main_rationality
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (layer :
      Month1PublicBridgeClosureTheoremLayer
        rootSide MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  layer.audit.not_main_rationality

end Month1PublicBridgeClosureTheoremLayer

theorem exactConvention_checkpoint_to_public_bridge_closure
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
    (checkpoint :
      Month1PublicReleaseCheckpoint
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicBridgeClosureTheoremLayer
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  audit := exactConvention_release_checkpoint_to_no_weakening_audit h checkpoint

theorem splitMinChecked_checkpoint_to_public_bridge_closure
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
    (checkpoint :
      Month1PublicReleaseCheckpoint
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicBridgeClosureTheoremLayer
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  audit := splitMinChecked_release_checkpoint_to_no_weakening_audit h checkpoint

theorem exactFamily_checkpoint_to_public_bridge_closure
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
    (checkpoint :
      Month1PublicReleaseCheckpoint
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicBridgeClosureTheoremLayer
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  audit := exactFamily_release_checkpoint_to_no_weakening_audit h checkpoint

theorem exactConvention_concrete_to_public_bridge_closure
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
    (concrete :
      Month1AuditableConcreteRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicBridgeClosureTheoremLayer
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  audit := exactConvention_concrete_to_no_weakening_audit h concrete

theorem splitMinChecked_concrete_to_public_bridge_closure
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
    (concrete :
      Month1AuditableConcreteRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicBridgeClosureTheoremLayer
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  audit := splitMinChecked_concrete_to_no_weakening_audit h concrete

theorem exactFamily_concrete_to_public_bridge_closure
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
    (concrete :
      Month1AuditableConcreteRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicBridgeClosureTheoremLayer
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  audit := exactFamily_concrete_to_no_weakening_audit h concrete

theorem exactConvention_paper_to_public_bridge_closure
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
    (paper :
      Month1AuditablePaperRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicBridgeClosureTheoremLayer
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  audit := exactConvention_paper_to_no_weakening_audit h paper

theorem splitMinChecked_paper_to_public_bridge_closure
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
    (paper :
      Month1AuditablePaperRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicBridgeClosureTheoremLayer
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  audit := splitMinChecked_paper_to_no_weakening_audit h paper

theorem exactFamily_paper_to_public_bridge_closure
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
    (paper :
      Month1AuditablePaperRoute
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicBridgeClosureTheoremLayer
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  audit := exactFamily_paper_to_no_weakening_audit h paper

theorem exactConvention_public_origin_to_public_bridge_closure
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
    (origin :
      Month1AuditablePublicOrigin
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicBridgeClosureTheoremLayer
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  audit := exactConvention_public_origin_to_no_weakening_audit h origin

theorem splitMinChecked_public_origin_to_public_bridge_closure
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
    (origin :
      Month1AuditablePublicOrigin
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicBridgeClosureTheoremLayer
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  audit := splitMinChecked_public_origin_to_no_weakening_audit h origin

theorem exactFamily_public_origin_to_public_bridge_closure
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
    (origin :
      Month1AuditablePublicOrigin
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Month1PublicBridgeClosureTheoremLayer
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  audit := exactFamily_public_origin_to_no_weakening_audit h origin

/-!
Intentional final public bridge closure theorem probes.
-/

#check Month1PublicBridgeClosureTheoremLayer
#check Month1PublicBridgeClosureTheoremLayer.concrete_iff_checkpoint
#check Month1PublicBridgeClosureTheoremLayer.paper_iff_checkpoint
#check Month1PublicBridgeClosureTheoremLayer.checkpoint_iff_public_origin
#check Month1PublicBridgeClosureTheoremLayer.concrete_iff_public_origin
#check Month1PublicBridgeClosureTheoremLayer.paper_iff_public_origin
#check Month1PublicBridgeClosureTheoremLayer.equation_endpoints
#check Month1PublicBridgeClosureTheoremLayer.target_eq_box_formula
#check Month1PublicBridgeClosureTheoremLayer.box_code_roundtrip_to_target
#check Month1PublicBridgeClosureTheoremLayer.carries_iff_pa_finite_consistency
#check Month1PublicBridgeClosureTheoremLayer.same_object_closure
#check Month1PublicBridgeClosureTheoremLayer.public_gap_instantiation
#check Month1PublicBridgeClosureTheoremLayer.public_collision_instantiation
#check Month1PublicBridgeClosureTheoremLayer.not_main_rationality
#check exactConvention_checkpoint_to_public_bridge_closure
#check splitMinChecked_checkpoint_to_public_bridge_closure
#check exactFamily_checkpoint_to_public_bridge_closure
#check exactConvention_concrete_to_public_bridge_closure
#check splitMinChecked_concrete_to_public_bridge_closure
#check exactFamily_concrete_to_public_bridge_closure
#check exactConvention_paper_to_public_bridge_closure
#check splitMinChecked_paper_to_public_bridge_closure
#check exactFamily_paper_to_public_bridge_closure
#check exactConvention_public_origin_to_public_bridge_closure
#check splitMinChecked_public_origin_to_public_bridge_closure
#check exactFamily_public_origin_to_public_bridge_closure

end SondowProjectPudlakMonth1PublicBridgeClosureTheoremSurface
end SondowMainCheckedCodeBridge
