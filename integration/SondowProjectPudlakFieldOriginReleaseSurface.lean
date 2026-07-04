/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakExactInputBridgeReleaseSurface
import BoundedArithmeticLab.CnBoxPudlakProjectConcreteFieldIndex

/-!
# Field-origin release surface for the concrete public Pudlak bridge

This module connects the field-level project certificate index to the
root-side lower-source origin required by the public EulerLimit/CnBox bridge.
It keeps the remaining origin claim explicit: the field index must identify
the same scale as the root literature lower-bound source.  Once that audited
origin is supplied, the public bundle origin, concrete checklist, same-object
closure, public gap instantiation, and contradiction endpoint all follow by
definition-preserving transport.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakFieldOriginReleaseSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate

structure ProjectConcreteFieldLowerSourceOrigin
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) : Prop where
  scale_eq :
    index.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale

namespace ProjectConcreteFieldLowerSourceOrigin

theorem bundle_lower_source_scale_eq
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    ((index.toCertificateBundle.toCertificateBackedGapCriterion).lower_source
        ).conditions.scale_data.scale =
      index.lower_source.conditions.scale_data.scale := by
  simp [ProjectConcreteCertificateFieldIndex.toCertificateBundle,
    ProjectConcreteCertificateFieldIndex.lower_source,
    ProjectConcreteCertificateObligation.toCertificateBundle,
    ProjectPublicCollisionCertificateBundle.toCertificateBackedGapCriterion,
    ProjectPublicCollisionCertificateBundle.toProjectPublicCollisionChecklist,
    CnBoxPudlakProjectPublicCollisionChecklist.toCertificateBackedGapCriterion,
    CnBoxPudlakProjectPublicCollisionChecklist.ofAssemblyChecklist,
    ProjectPublicCollisionCertificateBundle.toAssemblyChecklist,
    ProjectLevelCnBoxSondowBudgetedAssemblyChecklist.toCertificateBackedGapCriterion,
    ProjectLevelCnBoxSondowBudgetedAssemblyChecklist.toAssemblyChecklist,
    ProjectLevelCnBoxSondowAssemblyChecklist.toCertificateBackedGapCriterion,
    ProjectLevelCnBoxSondowAssemblyChecklist.toCompiledChecklist,
    ProjectLevelCnBoxSondowCompiledChecklist.toCertificateBackedGapCriterion]

theorem pointwise_scale_eq
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound}
    (origin : ProjectConcreteFieldLowerSourceOrigin rootSide index)
    (n : Nat) :
    index.lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.scale n := by
  rw [origin.scale_eq]

def toPublicBundleLowerSourceOrigin
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound}
    (origin : ProjectConcreteFieldLowerSourceOrigin rootSide index) :
    SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
      rootSide index.toCertificateBundle where
  scale_eq := by
    rw [bundle_lower_source_scale_eq index]
    exact origin.scale_eq

def toScaleOriginBridge
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound}
    (origin : ProjectConcreteFieldLowerSourceOrigin rootSide index) :
    SondowProjectPudlakScaleOriginBridge
      rootSide index.toCertificateBundle.toCertificateBackedGapCriterion.lower_source :=
  origin.toPublicBundleLowerSourceOrigin.toScaleOriginBridge

theorem iff_public_bundle_origin
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound} :
    ProjectConcreteFieldLowerSourceOrigin rootSide index ↔
      SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
        rootSide index.toCertificateBundle := by
  constructor
  · intro origin
    exact origin.toPublicBundleLowerSourceOrigin
  · intro origin
    refine ⟨?_⟩
    rw [← bundle_lower_source_scale_eq index]
    exact origin.scale_eq

theorem root_normalForm_translation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound}
    (origin : ProjectConcreteFieldLowerSourceOrigin rootSide index)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        ((index.toCertificateBundle.toCertificateBackedGapCriterion).lower_source
          ).conditions.scale_data.scale n) :=
  origin.toPublicBundleLowerSourceOrigin.root_normalForm_translation n

end ProjectConcreteFieldLowerSourceOrigin

theorem exactConvention_to_concrete_checklist_of_field_origin
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
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (origin :
      ProjectConcreteFieldLowerSourceOrigin h.toPudlakSideInputs index) :
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  SondowProjectPudlakExactInputBridgeReleaseSurface.exactConvention_to_concrete_checklist_of_lower_source_origin
    h index.toCertificateBundle origin.toPublicBundleLowerSourceOrigin

theorem exactConvention_to_same_object_closure_of_field_origin
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
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (origin :
      ProjectConcreteFieldLowerSourceOrigin h.toPudlakSideInputs index) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  SondowProjectPudlakExactInputBridgeReleaseSurface.exactConvention_to_same_object_closure_of_lower_source_origin
    h index.toCertificateBundle origin.toPublicBundleLowerSourceOrigin

theorem exactConvention_to_public_gap_instantiation_of_field_origin
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
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (origin :
      ProjectConcreteFieldLowerSourceOrigin h.toPudlakSideInputs index) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  SondowProjectPudlakExactInputBridgeReleaseSurface.exactConvention_to_public_gap_instantiation_of_lower_source_origin
    h index.toCertificateBundle origin.toPublicBundleLowerSourceOrigin

theorem exactConvention_not_main_rationality_of_field_origin
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
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (origin :
      ProjectConcreteFieldLowerSourceOrigin h.toPudlakSideInputs index) :
    ¬ MainRationality :=
  SondowProjectPudlakExactInputBridgeReleaseSurface.exactConvention_not_main_rationality_of_lower_source_origin
    h index.toCertificateBundle origin.toPublicBundleLowerSourceOrigin

theorem splitMinChecked_to_concrete_checklist_of_field_origin
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
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (origin :
      ProjectConcreteFieldLowerSourceOrigin h.toPudlakSideInputs index) :
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  SondowProjectPudlakExactInputBridgeReleaseSurface.splitMinChecked_to_concrete_checklist_of_lower_source_origin
    h index.toCertificateBundle origin.toPublicBundleLowerSourceOrigin

theorem splitMinChecked_to_same_object_closure_of_field_origin
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
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (origin :
      ProjectConcreteFieldLowerSourceOrigin h.toPudlakSideInputs index) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  SondowProjectPudlakExactInputBridgeReleaseSurface.splitMinChecked_to_same_object_closure_of_lower_source_origin
    h index.toCertificateBundle origin.toPublicBundleLowerSourceOrigin

theorem splitMinChecked_to_public_gap_instantiation_of_field_origin
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
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (origin :
      ProjectConcreteFieldLowerSourceOrigin h.toPudlakSideInputs index) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  SondowProjectPudlakExactInputBridgeReleaseSurface.splitMinChecked_to_public_gap_instantiation_of_lower_source_origin
    h index.toCertificateBundle origin.toPublicBundleLowerSourceOrigin

theorem splitMinChecked_not_main_rationality_of_field_origin
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
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (origin :
      ProjectConcreteFieldLowerSourceOrigin h.toPudlakSideInputs index) :
    ¬ MainRationality :=
  SondowProjectPudlakExactInputBridgeReleaseSurface.splitMinChecked_not_main_rationality_of_lower_source_origin
    h index.toCertificateBundle origin.toPublicBundleLowerSourceOrigin

theorem exactFamily_to_concrete_checklist_of_field_origin
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
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (origin :
      ProjectConcreteFieldLowerSourceOrigin h.toPudlakSideInputs index) :
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  SondowProjectPudlakExactInputBridgeReleaseSurface.exactFamily_to_concrete_checklist_of_lower_source_origin
    h index.toCertificateBundle origin.toPublicBundleLowerSourceOrigin

theorem exactFamily_to_same_object_closure_of_field_origin
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
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (origin :
      ProjectConcreteFieldLowerSourceOrigin h.toPudlakSideInputs index) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  SondowProjectPudlakExactInputBridgeReleaseSurface.exactFamily_to_same_object_closure_of_lower_source_origin
    h index.toCertificateBundle origin.toPublicBundleLowerSourceOrigin

theorem exactFamily_to_public_gap_instantiation_of_field_origin
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
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (origin :
      ProjectConcreteFieldLowerSourceOrigin h.toPudlakSideInputs index) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  SondowProjectPudlakExactInputBridgeReleaseSurface.exactFamily_to_public_gap_instantiation_of_lower_source_origin
    h index.toCertificateBundle origin.toPublicBundleLowerSourceOrigin

theorem exactFamily_not_main_rationality_of_field_origin
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
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (origin :
      ProjectConcreteFieldLowerSourceOrigin h.toPudlakSideInputs index) :
    ¬ MainRationality :=
  SondowProjectPudlakExactInputBridgeReleaseSurface.exactFamily_not_main_rationality_of_lower_source_origin
    h index.toCertificateBundle origin.toPublicBundleLowerSourceOrigin

end SondowProjectPudlakFieldOriginReleaseSurface
end SondowMainCheckedCodeBridge
