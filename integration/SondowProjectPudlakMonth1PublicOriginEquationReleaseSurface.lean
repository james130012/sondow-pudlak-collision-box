/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakMonth1ConcreteEquationReleaseSurface

/-!
# Month 1 public-origin equation release surface

This module exposes the public bundle origin as a direct route to the CnBox
equation endpoints.

The proof path is deliberately thin:

`public bundle origin -> auditable closure -> equation endpoints`.

It gives stable release theorem names for auditors who start from the public
source object rather than from the internal concrete checklist.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakMonth1PublicOriginEquationReleaseSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakMonth1AuditableClosureSurface
open SondowProjectPudlakMonth1ReleaseBoundaryAuditSurface
open SondowProjectPudlakMonth1EquationEndpointSurface
open SondowProjectPudlakMonth1ConcreteEquationReleaseSurface

structure Month1PublicOriginEquationAuditEndpoints
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Prop where
  equations : Month1CnBoxEquationEndpoints
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

theorem exactConvention_public_origin_to_closure
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
    Month1AuditableExactConventionClosure
      h MainRationality SondowAccepted bounds bound :=
  (exactConvention_closure_iff_public_origin h).mpr origin

theorem splitMinChecked_public_origin_to_closure
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
    Month1AuditableSplitMinCheckedClosure
      h MainRationality SondowAccepted bounds bound :=
  (splitMinChecked_closure_iff_public_origin h).mpr origin

theorem exactFamily_public_origin_to_closure
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
    Month1AuditableExactFamilyClosure
      h MainRationality SondowAccepted bounds bound :=
  (exactFamily_closure_iff_public_origin h).mpr origin

theorem exactConvention_public_origin_to_equation_endpoints
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
    Month1CnBoxEquationEndpoints :=
  exactConvention_closure_to_equation_endpoints
    (exactConvention_public_origin_to_closure h origin)

theorem splitMinChecked_public_origin_to_equation_endpoints
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
    Month1CnBoxEquationEndpoints :=
  splitMinChecked_closure_to_equation_endpoints
    (splitMinChecked_public_origin_to_closure h origin)

theorem exactFamily_public_origin_to_equation_endpoints
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
    Month1CnBoxEquationEndpoints :=
  exactFamily_closure_to_equation_endpoints
    (exactFamily_public_origin_to_closure h origin)

theorem exactConvention_public_origin_target_eq_box_formula
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula :=
  (exactConvention_public_origin_to_equation_endpoints h origin).target_eq_box_formula m

theorem exactConvention_public_origin_box_code_roundtrip_to_target
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m) :=
  (exactConvention_public_origin_to_equation_endpoints h origin).box_code_roundtrip_to_target m

theorem exactConvention_public_origin_carries_iff_pa_finite_consistency
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m :=
  (exactConvention_public_origin_to_equation_endpoints h origin).carries_iff_pa_finite_consistency m

theorem splitMinChecked_public_origin_target_eq_box_formula
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula :=
  (splitMinChecked_public_origin_to_equation_endpoints h origin).target_eq_box_formula m

theorem splitMinChecked_public_origin_box_code_roundtrip_to_target
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m) :=
  (splitMinChecked_public_origin_to_equation_endpoints h origin).box_code_roundtrip_to_target m

theorem splitMinChecked_public_origin_carries_iff_pa_finite_consistency
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m :=
  (splitMinChecked_public_origin_to_equation_endpoints h origin).carries_iff_pa_finite_consistency m

theorem exactFamily_public_origin_target_eq_box_formula
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula :=
  (exactFamily_public_origin_to_equation_endpoints h origin).target_eq_box_formula m

theorem exactFamily_public_origin_box_code_roundtrip_to_target
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m) :=
  (exactFamily_public_origin_to_equation_endpoints h origin).box_code_roundtrip_to_target m

theorem exactFamily_public_origin_carries_iff_pa_finite_consistency
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m :=
  (exactFamily_public_origin_to_equation_endpoints h origin).carries_iff_pa_finite_consistency m

theorem exactConvention_public_origin_to_equation_audit
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
    Month1PublicOriginEquationAuditEndpoints
      MainRationality SondowAccepted bounds bound where
  equations := exactConvention_public_origin_to_equation_endpoints h origin
  same_object_closure :=
    exactConvention_closure_to_same_object_closure
      (exactConvention_public_origin_to_closure h origin)
  public_gap_instantiation :=
    exactConvention_closure_to_public_gap
      (exactConvention_public_origin_to_closure h origin)
  public_collision_instantiation :=
    exactConvention_closure_to_public_collision
      (exactConvention_public_origin_to_closure h origin)
  not_main_rationality :=
    exactConvention_closure_not_main_rationality
      (exactConvention_public_origin_to_closure h origin)

theorem splitMinChecked_public_origin_to_equation_audit
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
    Month1PublicOriginEquationAuditEndpoints
      MainRationality SondowAccepted bounds bound where
  equations := splitMinChecked_public_origin_to_equation_endpoints h origin
  same_object_closure :=
    Month1SplitMinCheckedReleaseBoundaryAudit.to_same_object_closure
      (splitMinChecked_public_origin_to_closure h origin)
  public_gap_instantiation :=
    Month1SplitMinCheckedReleaseBoundaryAudit.to_public_gap
      (splitMinChecked_public_origin_to_closure h origin)
  public_collision_instantiation :=
    Month1SplitMinCheckedReleaseBoundaryAudit.to_public_collision
      (splitMinChecked_public_origin_to_closure h origin)
  not_main_rationality :=
    splitMinChecked_closure_not_main_rationality
      (splitMinChecked_public_origin_to_closure h origin)

theorem exactFamily_public_origin_to_equation_audit
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
    Month1PublicOriginEquationAuditEndpoints
      MainRationality SondowAccepted bounds bound where
  equations := exactFamily_public_origin_to_equation_endpoints h origin
  same_object_closure :=
    Month1ExactFamilyReleaseBoundaryAudit.to_same_object_closure
      (exactFamily_public_origin_to_closure h origin)
  public_gap_instantiation :=
    Month1ExactFamilyReleaseBoundaryAudit.to_public_gap
      (exactFamily_public_origin_to_closure h origin)
  public_collision_instantiation :=
    Month1ExactFamilyReleaseBoundaryAudit.to_public_collision
      (exactFamily_public_origin_to_closure h origin)
  not_main_rationality :=
    exactFamily_closure_not_main_rationality
      (exactFamily_public_origin_to_closure h origin)

/-!
Intentional public-origin equation release probes.
-/

#check Month1PublicOriginEquationAuditEndpoints
#check exactConvention_public_origin_to_closure
#check splitMinChecked_public_origin_to_closure
#check exactFamily_public_origin_to_closure
#check exactConvention_public_origin_to_equation_endpoints
#check splitMinChecked_public_origin_to_equation_endpoints
#check exactFamily_public_origin_to_equation_endpoints
#check exactConvention_public_origin_target_eq_box_formula
#check exactConvention_public_origin_box_code_roundtrip_to_target
#check exactConvention_public_origin_carries_iff_pa_finite_consistency
#check splitMinChecked_public_origin_target_eq_box_formula
#check splitMinChecked_public_origin_box_code_roundtrip_to_target
#check splitMinChecked_public_origin_carries_iff_pa_finite_consistency
#check exactFamily_public_origin_target_eq_box_formula
#check exactFamily_public_origin_box_code_roundtrip_to_target
#check exactFamily_public_origin_carries_iff_pa_finite_consistency
#check exactConvention_public_origin_to_equation_audit
#check splitMinChecked_public_origin_to_equation_audit
#check exactFamily_public_origin_to_equation_audit

end SondowProjectPudlakMonth1PublicOriginEquationReleaseSurface
end SondowMainCheckedCodeBridge
