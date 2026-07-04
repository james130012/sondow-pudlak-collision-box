/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakMonth1EquationEndpointSurface

/-!
# Month 1 concrete checklist equation release surface

This module gives direct paper-facing theorem names from the concrete
CnBox/Pudlak checklist to the equation endpoints.  It is a thin composition:

`concrete checklist -> release-boundary audit -> equation endpoints`.

Thus an auditor starting from the concrete checklist can read the CnBox target
equation, code roundtrip, and PA finite-consistency equivalence without first
manually unpacking the intermediate closure object.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakMonth1ConcreteEquationReleaseSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakMonth1AuditableClosureSurface
open SondowProjectPudlakMonth1ReleaseBoundaryAuditSurface
open SondowProjectPudlakMonth1EquationEndpointSurface
open SondowProjectPudlakMonth1PaperReadyTheoremSurface

structure Month1ConcreteEquationAuditEndpoints
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

theorem exactConvention_checklist_to_equation_endpoints
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
    Month1CnBoxEquationEndpoints :=
  exactConvention_closure_to_equation_endpoints
    (Month1ExactConventionReleaseBoundaryAudit.ofConcreteChecklist h checklist)

theorem splitMinChecked_checklist_to_equation_endpoints
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
    Month1CnBoxEquationEndpoints :=
  splitMinChecked_closure_to_equation_endpoints
    (Month1SplitMinCheckedReleaseBoundaryAudit.ofConcreteChecklist h checklist)

theorem exactFamily_checklist_to_equation_endpoints
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
    Month1CnBoxEquationEndpoints :=
  exactFamily_closure_to_equation_endpoints
    (Month1ExactFamilyReleaseBoundaryAudit.ofConcreteChecklist h checklist)

theorem exactConvention_checklist_target_eq_box_formula
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula :=
  (exactConvention_checklist_to_equation_endpoints h checklist).target_eq_box_formula m

theorem exactConvention_checklist_box_code_roundtrip_to_target
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m) :=
  (exactConvention_checklist_to_equation_endpoints h checklist).box_code_roundtrip_to_target m

theorem exactConvention_checklist_carries_iff_pa_finite_consistency
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m :=
  (exactConvention_checklist_to_equation_endpoints h checklist).carries_iff_pa_finite_consistency m

theorem splitMinChecked_checklist_target_eq_box_formula
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula :=
  (splitMinChecked_checklist_to_equation_endpoints h checklist).target_eq_box_formula m

theorem splitMinChecked_checklist_box_code_roundtrip_to_target
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m) :=
  (splitMinChecked_checklist_to_equation_endpoints h checklist).box_code_roundtrip_to_target m

theorem splitMinChecked_checklist_carries_iff_pa_finite_consistency
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m :=
  (splitMinChecked_checklist_to_equation_endpoints h checklist).carries_iff_pa_finite_consistency m

theorem exactFamily_checklist_target_eq_box_formula
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula :=
  (exactFamily_checklist_to_equation_endpoints h checklist).target_eq_box_formula m

theorem exactFamily_checklist_box_code_roundtrip_to_target
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m) :=
  (exactFamily_checklist_to_equation_endpoints h checklist).box_code_roundtrip_to_target m

theorem exactFamily_checklist_carries_iff_pa_finite_consistency
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
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m :=
  (exactFamily_checklist_to_equation_endpoints h checklist).carries_iff_pa_finite_consistency m

theorem exactConvention_checklist_to_concrete_equation_audit
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
    Month1ConcreteEquationAuditEndpoints
      MainRationality SondowAccepted bounds bound where
  equations := exactConvention_checklist_to_equation_endpoints h checklist
  same_object_closure :=
    exactConvention_checklist_to_same_object_closure h checklist
  public_gap_instantiation :=
    exactConvention_checklist_to_public_gap h checklist
  public_collision_instantiation :=
    exactConvention_checklist_to_public_collision h checklist
  not_main_rationality :=
    exactConvention_checklist_not_main_rationality h checklist

theorem splitMinChecked_checklist_to_concrete_equation_audit
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
    Month1ConcreteEquationAuditEndpoints
      MainRationality SondowAccepted bounds bound where
  equations := splitMinChecked_checklist_to_equation_endpoints h checklist
  same_object_closure :=
    splitMinChecked_checklist_to_same_object_closure h checklist
  public_gap_instantiation :=
    splitMinChecked_checklist_to_public_gap h checklist
  public_collision_instantiation :=
    splitMinChecked_checklist_to_public_collision h checklist
  not_main_rationality :=
    splitMinChecked_checklist_not_main_rationality h checklist

theorem exactFamily_checklist_to_concrete_equation_audit
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
    Month1ConcreteEquationAuditEndpoints
      MainRationality SondowAccepted bounds bound where
  equations := exactFamily_checklist_to_equation_endpoints h checklist
  same_object_closure :=
    exactFamily_checklist_to_same_object_closure h checklist
  public_gap_instantiation :=
    exactFamily_checklist_to_public_gap h checklist
  public_collision_instantiation :=
    exactFamily_checklist_to_public_collision h checklist
  not_main_rationality :=
    exactFamily_checklist_not_main_rationality h checklist

/-!
Intentional concrete equation release probes.
-/

#check Month1ConcreteEquationAuditEndpoints
#check exactConvention_checklist_to_equation_endpoints
#check splitMinChecked_checklist_to_equation_endpoints
#check exactFamily_checklist_to_equation_endpoints
#check exactConvention_checklist_target_eq_box_formula
#check exactConvention_checklist_box_code_roundtrip_to_target
#check exactConvention_checklist_carries_iff_pa_finite_consistency
#check splitMinChecked_checklist_target_eq_box_formula
#check splitMinChecked_checklist_box_code_roundtrip_to_target
#check splitMinChecked_checklist_carries_iff_pa_finite_consistency
#check exactFamily_checklist_target_eq_box_formula
#check exactFamily_checklist_box_code_roundtrip_to_target
#check exactFamily_checklist_carries_iff_pa_finite_consistency
#check exactConvention_checklist_to_concrete_equation_audit
#check splitMinChecked_checklist_to_concrete_equation_audit
#check exactFamily_checklist_to_concrete_equation_audit

end SondowProjectPudlakMonth1ConcreteEquationReleaseSurface
end SondowMainCheckedCodeBridge
