/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakMonth1PublicOriginEquationReleaseSurface

/-!
# Month 1 release checkpoint surface

This module gives a single project-level checkpoint for the Month 1 public
bridge closure.

The checkpoint is intentionally just the public bundle origin wrapped under a
stable release name.  The value of the file is in the equivalence statements:
the concrete checklist and the paper-ready route are each equivalent to this
checkpoint for all three Pudlak entry surfaces.  From the checkpoint we then
extract the same CnBox equation audit endpoints.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakMonth1ReleaseCheckpointSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakMonth1AuditableClosureSurface
open SondowProjectPudlakMonth1EquationEndpointSurface
open SondowProjectPudlakMonth1PublicOriginEquationReleaseSurface

structure Month1PublicReleaseCheckpoint
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop where
  public_origin :
    Month1AuditablePublicOrigin
      rootSide MainRationality SondowAccepted bounds bound

theorem checkpoint_iff_public_origin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Month1PublicReleaseCheckpoint
      rootSide MainRationality SondowAccepted bounds bound ↔
      Month1AuditablePublicOrigin
        rootSide MainRationality SondowAccepted bounds bound := by
  constructor
  · intro checkpoint
    exact checkpoint.public_origin
  · intro origin
    exact ⟨origin⟩

theorem exactConvention_concrete_iff_release_checkpoint
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
    Month1AuditableConcreteRoute
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound ↔
      Month1PublicReleaseCheckpoint
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactConvention_closure_iff_concrete h).symm.trans
    ((exactConvention_closure_iff_public_origin h).trans
      checkpoint_iff_public_origin.symm)

theorem splitMinChecked_concrete_iff_release_checkpoint
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
    Month1AuditableConcreteRoute
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound ↔
      Month1PublicReleaseCheckpoint
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (splitMinChecked_closure_iff_concrete h).symm.trans
    ((splitMinChecked_closure_iff_public_origin h).trans
      checkpoint_iff_public_origin.symm)

theorem exactFamily_concrete_iff_release_checkpoint
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
    Month1AuditableConcreteRoute
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound ↔
      Month1PublicReleaseCheckpoint
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactFamily_closure_iff_concrete h).symm.trans
    ((exactFamily_closure_iff_public_origin h).trans
      checkpoint_iff_public_origin.symm)

theorem exactConvention_paper_iff_release_checkpoint
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
    Month1AuditablePaperRoute
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound ↔
      Month1PublicReleaseCheckpoint
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactConvention_closure_iff_paper h).symm.trans
    ((exactConvention_closure_iff_public_origin h).trans
      checkpoint_iff_public_origin.symm)

theorem splitMinChecked_paper_iff_release_checkpoint
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
    Month1AuditablePaperRoute
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound ↔
      Month1PublicReleaseCheckpoint
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (splitMinChecked_closure_iff_paper h).symm.trans
    ((splitMinChecked_closure_iff_public_origin h).trans
      checkpoint_iff_public_origin.symm)

theorem exactFamily_paper_iff_release_checkpoint
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
    Month1AuditablePaperRoute
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound ↔
      Month1PublicReleaseCheckpoint
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound :=
  (exactFamily_closure_iff_paper h).symm.trans
    ((exactFamily_closure_iff_public_origin h).trans
      checkpoint_iff_public_origin.symm)

theorem exactConvention_release_checkpoint_to_equation_endpoints
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
    Month1CnBoxEquationEndpoints :=
  exactConvention_public_origin_to_equation_endpoints
    h checkpoint.public_origin

theorem splitMinChecked_release_checkpoint_to_equation_endpoints
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
    Month1CnBoxEquationEndpoints :=
  splitMinChecked_public_origin_to_equation_endpoints
    h checkpoint.public_origin

theorem exactFamily_release_checkpoint_to_equation_endpoints
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
    Month1CnBoxEquationEndpoints :=
  exactFamily_public_origin_to_equation_endpoints
    h checkpoint.public_origin

theorem exactConvention_release_checkpoint_target_eq_box_formula
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula :=
  (exactConvention_release_checkpoint_to_equation_endpoints h checkpoint).target_eq_box_formula m

theorem splitMinChecked_release_checkpoint_target_eq_box_formula
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula :=
  (splitMinChecked_release_checkpoint_to_equation_endpoints h checkpoint).target_eq_box_formula m

theorem exactFamily_release_checkpoint_target_eq_box_formula
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula :=
  (exactFamily_release_checkpoint_to_equation_endpoints h checkpoint).target_eq_box_formula m

theorem exactConvention_release_checkpoint_box_code_roundtrip_to_target
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m) :=
  (exactConvention_release_checkpoint_to_equation_endpoints
    h checkpoint).box_code_roundtrip_to_target m

theorem splitMinChecked_release_checkpoint_box_code_roundtrip_to_target
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m) :=
  (splitMinChecked_release_checkpoint_to_equation_endpoints
    h checkpoint).box_code_roundtrip_to_target m

theorem exactFamily_release_checkpoint_box_code_roundtrip_to_target
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m) :=
  (exactFamily_release_checkpoint_to_equation_endpoints
    h checkpoint).box_code_roundtrip_to_target m

theorem exactConvention_release_checkpoint_carries_iff_pa_finite_consistency
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m :=
  (exactConvention_release_checkpoint_to_equation_endpoints
    h checkpoint).carries_iff_pa_finite_consistency m

theorem splitMinChecked_release_checkpoint_carries_iff_pa_finite_consistency
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m :=
  (splitMinChecked_release_checkpoint_to_equation_endpoints
    h checkpoint).carries_iff_pa_finite_consistency m

theorem exactFamily_release_checkpoint_carries_iff_pa_finite_consistency
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m :=
  (exactFamily_release_checkpoint_to_equation_endpoints
    h checkpoint).carries_iff_pa_finite_consistency m

theorem exactConvention_release_checkpoint_to_equation_audit
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
    Month1PublicOriginEquationAuditEndpoints
      MainRationality SondowAccepted bounds bound :=
  exactConvention_public_origin_to_equation_audit
    h checkpoint.public_origin

theorem splitMinChecked_release_checkpoint_to_equation_audit
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
    Month1PublicOriginEquationAuditEndpoints
      MainRationality SondowAccepted bounds bound :=
  splitMinChecked_public_origin_to_equation_audit
    h checkpoint.public_origin

theorem exactFamily_release_checkpoint_to_equation_audit
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
    Month1PublicOriginEquationAuditEndpoints
      MainRationality SondowAccepted bounds bound :=
  exactFamily_public_origin_to_equation_audit
    h checkpoint.public_origin

theorem exactConvention_release_checkpoint_to_same_object_closure
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
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  (exactConvention_release_checkpoint_to_equation_audit
    h checkpoint).same_object_closure

theorem splitMinChecked_release_checkpoint_to_same_object_closure
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
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_release_checkpoint_to_equation_audit
    h checkpoint).same_object_closure

theorem exactFamily_release_checkpoint_to_same_object_closure
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
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  (exactFamily_release_checkpoint_to_equation_audit
    h checkpoint).same_object_closure

theorem exactConvention_release_checkpoint_to_public_gap
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
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  (exactConvention_release_checkpoint_to_equation_audit
    h checkpoint).public_gap_instantiation

theorem splitMinChecked_release_checkpoint_to_public_gap
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
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  (splitMinChecked_release_checkpoint_to_equation_audit
    h checkpoint).public_gap_instantiation

theorem exactFamily_release_checkpoint_to_public_gap
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
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  (exactFamily_release_checkpoint_to_equation_audit
    h checkpoint).public_gap_instantiation

theorem exactConvention_release_checkpoint_to_public_collision
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
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation
      MainRationality) :=
  (exactConvention_release_checkpoint_to_equation_audit
    h checkpoint).public_collision_instantiation

theorem splitMinChecked_release_checkpoint_to_public_collision
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
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation
      MainRationality) :=
  (splitMinChecked_release_checkpoint_to_equation_audit
    h checkpoint).public_collision_instantiation

theorem exactFamily_release_checkpoint_to_public_collision
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
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation
      MainRationality) :=
  (exactFamily_release_checkpoint_to_equation_audit
    h checkpoint).public_collision_instantiation

theorem exactConvention_release_checkpoint_not_main_rationality
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
    ¬ MainRationality :=
  (exactConvention_release_checkpoint_to_equation_audit
    h checkpoint).not_main_rationality

theorem splitMinChecked_release_checkpoint_not_main_rationality
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
    ¬ MainRationality :=
  (splitMinChecked_release_checkpoint_to_equation_audit
    h checkpoint).not_main_rationality

theorem exactFamily_release_checkpoint_not_main_rationality
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
    ¬ MainRationality :=
  (exactFamily_release_checkpoint_to_equation_audit
    h checkpoint).not_main_rationality

/-!
Intentional release checkpoint probes.
-/

#check Month1PublicReleaseCheckpoint
#check checkpoint_iff_public_origin
#check exactConvention_concrete_iff_release_checkpoint
#check splitMinChecked_concrete_iff_release_checkpoint
#check exactFamily_concrete_iff_release_checkpoint
#check exactConvention_paper_iff_release_checkpoint
#check splitMinChecked_paper_iff_release_checkpoint
#check exactFamily_paper_iff_release_checkpoint
#check exactConvention_release_checkpoint_to_equation_endpoints
#check splitMinChecked_release_checkpoint_to_equation_endpoints
#check exactFamily_release_checkpoint_to_equation_endpoints
#check exactConvention_release_checkpoint_target_eq_box_formula
#check splitMinChecked_release_checkpoint_target_eq_box_formula
#check exactFamily_release_checkpoint_target_eq_box_formula
#check exactConvention_release_checkpoint_box_code_roundtrip_to_target
#check splitMinChecked_release_checkpoint_box_code_roundtrip_to_target
#check exactFamily_release_checkpoint_box_code_roundtrip_to_target
#check exactConvention_release_checkpoint_carries_iff_pa_finite_consistency
#check splitMinChecked_release_checkpoint_carries_iff_pa_finite_consistency
#check exactFamily_release_checkpoint_carries_iff_pa_finite_consistency
#check exactConvention_release_checkpoint_to_equation_audit
#check splitMinChecked_release_checkpoint_to_equation_audit
#check exactFamily_release_checkpoint_to_equation_audit
#check exactConvention_release_checkpoint_to_same_object_closure
#check splitMinChecked_release_checkpoint_to_same_object_closure
#check exactFamily_release_checkpoint_to_same_object_closure
#check exactConvention_release_checkpoint_to_public_gap
#check splitMinChecked_release_checkpoint_to_public_gap
#check exactFamily_release_checkpoint_to_public_gap
#check exactConvention_release_checkpoint_to_public_collision
#check splitMinChecked_release_checkpoint_to_public_collision
#check exactFamily_release_checkpoint_to_public_collision
#check exactConvention_release_checkpoint_not_main_rationality
#check splitMinChecked_release_checkpoint_not_main_rationality
#check exactFamily_release_checkpoint_not_main_rationality

end SondowProjectPudlakMonth1ReleaseCheckpointSurface
end SondowMainCheckedCodeBridge
