/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakMonth1AuditableClosureSurface

/-!
# Month 1 equation endpoint surface

This module flattens the final Month 1 auditable closure into direct CnBox
equation endpoints.  Earlier surfaces already show that the auditable closure
is equivalent to the concrete checklist and public bundle origin.  Here we add
paper-facing theorem names that let an auditor read the actual equations from
the final closure object:

* target equals the CnBox formula;
* decoding the CnBox code returns that target;
* the CnBox carries the PA finite-consistency statement exactly.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakMonth1EquationEndpointSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakMonth1AuditableClosureSurface
open SondowProjectPudlakMonth1ReleaseBoundaryAuditSurface
open SondowProjectPudlakMonth1PublicSyncCandidateSurface

structure Month1CnBoxEquationEndpoints : Prop where
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

namespace Month1CnBoxEquationEndpoints

def ofEncodingProbe
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {gap_cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    {checklist : SondowProjectPudlakConcreteBridgeChecklist
      rootSide gap_cert}
    (probe : Month1PublicSyncEncodingProbe rootSide gap_cert checklist) :
    Month1CnBoxEquationEndpoints where
  target_eq_box_formula := by
    intro m
    exact
      Month1PublicSyncCandidate.encoding_probe_target_eq_box_formula
        probe m
  box_code_roundtrip_to_target := by
    intro m
    exact
      Month1PublicSyncCandidate.encoding_probe_box_code_roundtrip_to_target
        probe m
  carries_iff_pa_finite_consistency := by
    intro m
    exact
      Month1PublicSyncCandidate.encoding_probe_carries_iff_pa_finite_consistency
        probe m

end Month1CnBoxEquationEndpoints

theorem exactConvention_closure_to_equation_endpoints
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
    Month1CnBoxEquationEndpoints := by
  rcases exactConvention_closure_to_encoding_probe audit with
    ⟨⟨_gap_cert, ⟨_checklist, probe⟩⟩⟩
  exact Month1CnBoxEquationEndpoints.ofEncodingProbe probe

theorem splitMinChecked_closure_to_equation_endpoints
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
    Month1CnBoxEquationEndpoints := by
  rcases Month1SplitMinCheckedReleaseBoundaryAudit.to_encoding_probe audit with
    ⟨⟨_gap_cert, ⟨_checklist, probe⟩⟩⟩
  exact Month1CnBoxEquationEndpoints.ofEncodingProbe probe

theorem exactFamily_closure_to_equation_endpoints
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
    Month1CnBoxEquationEndpoints := by
  rcases Month1ExactFamilyReleaseBoundaryAudit.to_encoding_probe audit with
    ⟨⟨_gap_cert, ⟨_checklist, probe⟩⟩⟩
  exact Month1CnBoxEquationEndpoints.ofEncodingProbe probe

theorem exactConvention_closure_target_eq_box_formula
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
        h MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula :=
  (exactConvention_closure_to_equation_endpoints audit).target_eq_box_formula m

theorem exactConvention_closure_box_code_roundtrip_to_target
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
        h MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m) :=
  (exactConvention_closure_to_equation_endpoints audit).box_code_roundtrip_to_target m

theorem exactConvention_closure_carries_iff_pa_finite_consistency
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
        h MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m :=
  (exactConvention_closure_to_equation_endpoints audit).carries_iff_pa_finite_consistency m

theorem splitMinChecked_closure_target_eq_box_formula
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
        h MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula :=
  (splitMinChecked_closure_to_equation_endpoints audit).target_eq_box_formula m

theorem splitMinChecked_closure_box_code_roundtrip_to_target
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
        h MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m) :=
  (splitMinChecked_closure_to_equation_endpoints audit).box_code_roundtrip_to_target m

theorem splitMinChecked_closure_carries_iff_pa_finite_consistency
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
        h MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m :=
  (splitMinChecked_closure_to_equation_endpoints audit).carries_iff_pa_finite_consistency m

theorem exactFamily_closure_target_eq_box_formula
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
        h MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).formula :=
  (exactFamily_closure_to_equation_endpoints audit).target_eq_box_formula m

theorem exactFamily_closure_box_code_roundtrip_to_target
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
        h MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m).code =
        some
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target m) :=
  (exactFamily_closure_to_equation_endpoints audit).box_code_roundtrip_to_target m

theorem exactFamily_closure_carries_iff_pa_finite_consistency
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
        h MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box m) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement m :=
  (exactFamily_closure_to_equation_endpoints audit).carries_iff_pa_finite_consistency m

/-!
Intentional equation endpoint probes.
-/

#check Month1CnBoxEquationEndpoints
#check Month1CnBoxEquationEndpoints.ofEncodingProbe
#check exactConvention_closure_to_equation_endpoints
#check splitMinChecked_closure_to_equation_endpoints
#check exactFamily_closure_to_equation_endpoints
#check exactConvention_closure_target_eq_box_formula
#check exactConvention_closure_box_code_roundtrip_to_target
#check exactConvention_closure_carries_iff_pa_finite_consistency
#check splitMinChecked_closure_target_eq_box_formula
#check splitMinChecked_closure_box_code_roundtrip_to_target
#check splitMinChecked_closure_carries_iff_pa_finite_consistency
#check exactFamily_closure_target_eq_box_formula
#check exactFamily_closure_box_code_roundtrip_to_target
#check exactFamily_closure_carries_iff_pa_finite_consistency

end SondowProjectPudlakMonth1EquationEndpointSurface
end SondowMainCheckedCodeBridge
