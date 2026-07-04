/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakMonth1ReleaseCheckpointSurface

/-!
# Month 1 no-weakening audit surface

This module packages the public checkpoint route as an audit object showing
that the concrete checklist, the paper-ready route, the public origin, and the
CnBox equation endpoints all refer to the same release checkpoint.

The key audit question is whether the public-facing statement was weakened.
The answer recorded here is a set of equivalences, not one-way implications.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakMonth1NoWeakeningAuditSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakMonth1AuditableClosureSurface
open SondowProjectPudlakMonth1EquationEndpointSurface
open SondowProjectPudlakMonth1PublicOriginEquationReleaseSurface
open SondowProjectPudlakMonth1ReleaseCheckpointSurface

structure Month1ReleaseNoWeakeningEquivalences
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop where
  concrete_iff_checkpoint :
    Month1AuditableConcreteRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month1PublicReleaseCheckpoint
        rootSide MainRationality SondowAccepted bounds bound
  paper_iff_checkpoint :
    Month1AuditablePaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month1PublicReleaseCheckpoint
        rootSide MainRationality SondowAccepted bounds bound
  checkpoint_iff_public_origin :
    Month1PublicReleaseCheckpoint
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month1AuditablePublicOrigin
        rootSide MainRationality SondowAccepted bounds bound
  concrete_iff_public_origin :
    Month1AuditableConcreteRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month1AuditablePublicOrigin
        rootSide MainRationality SondowAccepted bounds bound
  paper_iff_public_origin :
    Month1AuditablePaperRoute
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month1AuditablePublicOrigin
        rootSide MainRationality SondowAccepted bounds bound

structure Month1ReleaseNoWeakeningAudit
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop where
  equivalences :
    Month1ReleaseNoWeakeningEquivalences
      rootSide MainRationality SondowAccepted bounds bound
  equations : Month1CnBoxEquationEndpoints
  target_eq_box_formula :
    ∀ m : Nat,
      BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
        (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula
  box_code_roundtrip_to_target :
    ∀ m : Nat,
      BoundedArithmeticLab.BAFormula.decode
        (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
          some
            (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m)
  carries_iff_pa_finite_consistency :
    ∀ m : Nat,
      BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
        (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
          BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m
  same_object_closure :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)
  public_gap_instantiation :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality)
  public_collision_instantiation :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation
      MainRationality)
  not_main_rationality : ¬ MainRationality

theorem exactConvention_no_weakening_equivalences
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
    Month1ReleaseNoWeakeningEquivalences
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  concrete_iff_checkpoint := exactConvention_concrete_iff_release_checkpoint h
  paper_iff_checkpoint := exactConvention_paper_iff_release_checkpoint h
  checkpoint_iff_public_origin :=
    SondowProjectPudlakMonth1ReleaseCheckpointSurface.checkpoint_iff_public_origin
  concrete_iff_public_origin :=
    (exactConvention_concrete_iff_release_checkpoint h).trans
      SondowProjectPudlakMonth1ReleaseCheckpointSurface.checkpoint_iff_public_origin
  paper_iff_public_origin :=
    (exactConvention_paper_iff_release_checkpoint h).trans
      SondowProjectPudlakMonth1ReleaseCheckpointSurface.checkpoint_iff_public_origin

theorem splitMinChecked_no_weakening_equivalences
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
    Month1ReleaseNoWeakeningEquivalences
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  concrete_iff_checkpoint := splitMinChecked_concrete_iff_release_checkpoint h
  paper_iff_checkpoint := splitMinChecked_paper_iff_release_checkpoint h
  checkpoint_iff_public_origin :=
    SondowProjectPudlakMonth1ReleaseCheckpointSurface.checkpoint_iff_public_origin
  concrete_iff_public_origin :=
    (splitMinChecked_concrete_iff_release_checkpoint h).trans
      SondowProjectPudlakMonth1ReleaseCheckpointSurface.checkpoint_iff_public_origin
  paper_iff_public_origin :=
    (splitMinChecked_paper_iff_release_checkpoint h).trans
      SondowProjectPudlakMonth1ReleaseCheckpointSurface.checkpoint_iff_public_origin

theorem exactFamily_no_weakening_equivalences
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
    Month1ReleaseNoWeakeningEquivalences
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  concrete_iff_checkpoint := exactFamily_concrete_iff_release_checkpoint h
  paper_iff_checkpoint := exactFamily_paper_iff_release_checkpoint h
  checkpoint_iff_public_origin :=
    SondowProjectPudlakMonth1ReleaseCheckpointSurface.checkpoint_iff_public_origin
  concrete_iff_public_origin :=
    (exactFamily_concrete_iff_release_checkpoint h).trans
      SondowProjectPudlakMonth1ReleaseCheckpointSurface.checkpoint_iff_public_origin
  paper_iff_public_origin :=
    (exactFamily_paper_iff_release_checkpoint h).trans
      SondowProjectPudlakMonth1ReleaseCheckpointSurface.checkpoint_iff_public_origin

theorem exactConvention_release_checkpoint_to_no_weakening_audit
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
    Month1ReleaseNoWeakeningAudit
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  equivalences := exactConvention_no_weakening_equivalences h
  equations := exactConvention_release_checkpoint_to_equation_endpoints h checkpoint
  target_eq_box_formula :=
    exactConvention_release_checkpoint_target_eq_box_formula h checkpoint
  box_code_roundtrip_to_target :=
    exactConvention_release_checkpoint_box_code_roundtrip_to_target h checkpoint
  carries_iff_pa_finite_consistency :=
    exactConvention_release_checkpoint_carries_iff_pa_finite_consistency h checkpoint
  same_object_closure :=
    exactConvention_release_checkpoint_to_same_object_closure h checkpoint
  public_gap_instantiation :=
    exactConvention_release_checkpoint_to_public_gap h checkpoint
  public_collision_instantiation :=
    exactConvention_release_checkpoint_to_public_collision h checkpoint
  not_main_rationality :=
    exactConvention_release_checkpoint_not_main_rationality h checkpoint

theorem splitMinChecked_release_checkpoint_to_no_weakening_audit
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
    Month1ReleaseNoWeakeningAudit
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  equivalences := splitMinChecked_no_weakening_equivalences h
  equations := splitMinChecked_release_checkpoint_to_equation_endpoints h checkpoint
  target_eq_box_formula :=
    splitMinChecked_release_checkpoint_target_eq_box_formula h checkpoint
  box_code_roundtrip_to_target :=
    splitMinChecked_release_checkpoint_box_code_roundtrip_to_target h checkpoint
  carries_iff_pa_finite_consistency :=
    splitMinChecked_release_checkpoint_carries_iff_pa_finite_consistency h checkpoint
  same_object_closure :=
    splitMinChecked_release_checkpoint_to_same_object_closure h checkpoint
  public_gap_instantiation :=
    splitMinChecked_release_checkpoint_to_public_gap h checkpoint
  public_collision_instantiation :=
    splitMinChecked_release_checkpoint_to_public_collision h checkpoint
  not_main_rationality :=
    splitMinChecked_release_checkpoint_not_main_rationality h checkpoint

theorem exactFamily_release_checkpoint_to_no_weakening_audit
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
    Month1ReleaseNoWeakeningAudit
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound where
  equivalences := exactFamily_no_weakening_equivalences h
  equations := exactFamily_release_checkpoint_to_equation_endpoints h checkpoint
  target_eq_box_formula :=
    exactFamily_release_checkpoint_target_eq_box_formula h checkpoint
  box_code_roundtrip_to_target :=
    exactFamily_release_checkpoint_box_code_roundtrip_to_target h checkpoint
  carries_iff_pa_finite_consistency :=
    exactFamily_release_checkpoint_carries_iff_pa_finite_consistency h checkpoint
  same_object_closure :=
    exactFamily_release_checkpoint_to_same_object_closure h checkpoint
  public_gap_instantiation :=
    exactFamily_release_checkpoint_to_public_gap h checkpoint
  public_collision_instantiation :=
    exactFamily_release_checkpoint_to_public_collision h checkpoint
  not_main_rationality :=
    exactFamily_release_checkpoint_not_main_rationality h checkpoint

theorem exactConvention_concrete_to_no_weakening_audit
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
    Month1ReleaseNoWeakeningAudit
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  exactConvention_release_checkpoint_to_no_weakening_audit h
    ((exactConvention_concrete_iff_release_checkpoint h).mp concrete)

theorem splitMinChecked_concrete_to_no_weakening_audit
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
    Month1ReleaseNoWeakeningAudit
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  splitMinChecked_release_checkpoint_to_no_weakening_audit h
    ((splitMinChecked_concrete_iff_release_checkpoint h).mp concrete)

theorem exactFamily_concrete_to_no_weakening_audit
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
    Month1ReleaseNoWeakeningAudit
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  exactFamily_release_checkpoint_to_no_weakening_audit h
    ((exactFamily_concrete_iff_release_checkpoint h).mp concrete)

theorem exactConvention_paper_to_no_weakening_audit
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
    Month1ReleaseNoWeakeningAudit
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  exactConvention_release_checkpoint_to_no_weakening_audit h
    ((exactConvention_paper_iff_release_checkpoint h).mp paper)

theorem splitMinChecked_paper_to_no_weakening_audit
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
    Month1ReleaseNoWeakeningAudit
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  splitMinChecked_release_checkpoint_to_no_weakening_audit h
    ((splitMinChecked_paper_iff_release_checkpoint h).mp paper)

theorem exactFamily_paper_to_no_weakening_audit
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
    Month1ReleaseNoWeakeningAudit
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  exactFamily_release_checkpoint_to_no_weakening_audit h
    ((exactFamily_paper_iff_release_checkpoint h).mp paper)

theorem exactConvention_public_origin_to_no_weakening_audit
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
    Month1ReleaseNoWeakeningAudit
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  exactConvention_release_checkpoint_to_no_weakening_audit h ⟨origin⟩

theorem splitMinChecked_public_origin_to_no_weakening_audit
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
    Month1ReleaseNoWeakeningAudit
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  splitMinChecked_release_checkpoint_to_no_weakening_audit h ⟨origin⟩

theorem exactFamily_public_origin_to_no_weakening_audit
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
    Month1ReleaseNoWeakeningAudit
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  exactFamily_release_checkpoint_to_no_weakening_audit h ⟨origin⟩

/-!
Intentional no-weakening audit probes.
-/

#check Month1ReleaseNoWeakeningEquivalences
#check Month1ReleaseNoWeakeningAudit
#check exactConvention_no_weakening_equivalences
#check splitMinChecked_no_weakening_equivalences
#check exactFamily_no_weakening_equivalences
#check exactConvention_release_checkpoint_to_no_weakening_audit
#check splitMinChecked_release_checkpoint_to_no_weakening_audit
#check exactFamily_release_checkpoint_to_no_weakening_audit
#check exactConvention_concrete_to_no_weakening_audit
#check splitMinChecked_concrete_to_no_weakening_audit
#check exactFamily_concrete_to_no_weakening_audit
#check exactConvention_paper_to_no_weakening_audit
#check splitMinChecked_paper_to_no_weakening_audit
#check exactFamily_paper_to_no_weakening_audit
#check exactConvention_public_origin_to_no_weakening_audit
#check splitMinChecked_public_origin_to_no_weakening_audit
#check exactFamily_public_origin_to_no_weakening_audit

end SondowProjectPudlakMonth1NoWeakeningAuditSurface
end SondowMainCheckedCodeBridge
