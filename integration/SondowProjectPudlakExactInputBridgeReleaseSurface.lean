/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakConcreteBridgeReleaseSurface

/-!
# Exact-input release surface for the concrete public Pudlak bridge

This module specializes the concrete bridge release surface to the exact
Theorem 5 input fronts used in the project-local Pudlak route.  It does not
assert that the bounded lower source and the EulerLimit literature source are
definitionally the same object; it exposes the precise scale-origin bridge
needed to connect an exact input to the public certificate bundle.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakExactInputBridgeReleaseSurface

universe u v w

structure PublicBundleLowerSourceOrigin
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) : Prop where
  scale_eq :
    bundle.toCertificateBackedGapCriterion.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale

namespace PublicBundleLowerSourceOrigin

def toScaleOriginBridge
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound}
    (origin : PublicBundleLowerSourceOrigin rootSide bundle) :
    SondowProjectPudlakScaleOriginBridge
      rootSide bundle.toCertificateBackedGapCriterion.lower_source where
  scale_aligned := origin.scale_eq

theorem pointwise_scale_eq
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound}
    (origin : PublicBundleLowerSourceOrigin rootSide bundle)
    (n : Nat) :
    bundle.toCertificateBackedGapCriterion.lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.scale n :=
  origin.toScaleOriginBridge.pointwise_scale_aligned n

theorem iff_scale_origin_bridge
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound} :
    PublicBundleLowerSourceOrigin rootSide bundle ↔
      SondowProjectPudlakScaleOriginBridge
        rootSide bundle.toCertificateBackedGapCriterion.lower_source := by
  constructor
  · intro origin
    exact origin.toScaleOriginBridge
  · intro bridge
    exact { scale_eq := bridge.scale_aligned }

theorem root_normalForm_translation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound}
    (origin : PublicBundleLowerSourceOrigin rootSide bundle)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        bundle.toCertificateBackedGapCriterion.lower_source.conditions.scale_data.scale n) :=
  origin.toScaleOriginBridge.root_normalForm_translates_external n

end PublicBundleLowerSourceOrigin

theorem exactConvention_checklist_iff_public_bundle_scale_origin_bridge
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
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) ↔
      Nonempty (Σ' bundle :
        BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakScaleOriginBridge
          h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_iff_public_bundle_scale_origin_bridge

theorem exactConvention_checklist_iff_public_bundle_lower_source_origin
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
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) ↔
      Nonempty (Σ' bundle :
        BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
          MainRationality SondowAccepted bounds bound,
        PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) := by
  exact (exactConvention_checklist_iff_public_bundle_scale_origin_bridge h).trans
    (by
      constructor
      · intro horigin
        rcases horigin with ⟨⟨bundle, origin⟩⟩
        exact ⟨⟨bundle,
          (PublicBundleLowerSourceOrigin.iff_scale_origin_bridge).2 origin⟩⟩
      · intro horigin
        rcases horigin with ⟨⟨bundle, origin⟩⟩
        exact ⟨⟨bundle,
          (PublicBundleLowerSourceOrigin.iff_scale_origin_bridge).1 origin⟩⟩)

theorem splitMinChecked_checklist_iff_public_bundle_scale_origin_bridge
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
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) ↔
      Nonempty (Σ' bundle :
        BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakScaleOriginBridge
          h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_iff_public_bundle_scale_origin_bridge

theorem splitMinChecked_checklist_iff_public_bundle_lower_source_origin
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
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) ↔
      Nonempty (Σ' bundle :
        BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
          MainRationality SondowAccepted bounds bound,
        PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) := by
  exact (splitMinChecked_checklist_iff_public_bundle_scale_origin_bridge h).trans
    (by
      constructor
      · intro horigin
        rcases horigin with ⟨⟨bundle, origin⟩⟩
        exact ⟨⟨bundle,
          (PublicBundleLowerSourceOrigin.iff_scale_origin_bridge).2 origin⟩⟩
      · intro horigin
        rcases horigin with ⟨⟨bundle, origin⟩⟩
        exact ⟨⟨bundle,
          (PublicBundleLowerSourceOrigin.iff_scale_origin_bridge).1 origin⟩⟩)

theorem exactFamily_checklist_iff_public_bundle_scale_origin_bridge
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
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) ↔
      Nonempty (Σ' bundle :
        BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakScaleOriginBridge
          h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_iff_public_bundle_scale_origin_bridge

theorem exactFamily_checklist_iff_public_bundle_lower_source_origin
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
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) ↔
      Nonempty (Σ' bundle :
        BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
          MainRationality SondowAccepted bounds bound,
        PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) := by
  exact (exactFamily_checklist_iff_public_bundle_scale_origin_bridge h).trans
    (by
      constructor
      · intro horigin
        rcases horigin with ⟨⟨bundle, origin⟩⟩
        exact ⟨⟨bundle,
          (PublicBundleLowerSourceOrigin.iff_scale_origin_bridge).2 origin⟩⟩
      · intro horigin
        rcases horigin with ⟨⟨bundle, origin⟩⟩
        exact ⟨⟨bundle,
          (PublicBundleLowerSourceOrigin.iff_scale_origin_bridge).1 origin⟩⟩)

theorem exactConvention_to_concrete_checklist
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin :
      SondowProjectPudlakScaleOriginBridge
        h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  (exactConvention_checklist_iff_public_bundle_scale_origin_bridge h).2
    ⟨⟨bundle, origin⟩⟩

theorem exactConvention_to_concrete_checklist_of_lower_source_origin
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin : PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) :
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  (exactConvention_checklist_iff_public_bundle_lower_source_origin h).2
    ⟨⟨bundle, origin⟩⟩

theorem splitMinChecked_to_concrete_checklist
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin :
      SondowProjectPudlakScaleOriginBridge
        h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  (splitMinChecked_checklist_iff_public_bundle_scale_origin_bridge h).2
    ⟨⟨bundle, origin⟩⟩

theorem splitMinChecked_to_concrete_checklist_of_lower_source_origin
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin : PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) :
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  (splitMinChecked_checklist_iff_public_bundle_lower_source_origin h).2
    ⟨⟨bundle, origin⟩⟩

theorem exactFamily_to_concrete_checklist
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin :
      SondowProjectPudlakScaleOriginBridge
        h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  (exactFamily_checklist_iff_public_bundle_scale_origin_bridge h).2
    ⟨⟨bundle, origin⟩⟩

theorem exactFamily_to_concrete_checklist_of_lower_source_origin
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin : PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) :
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  (exactFamily_checklist_iff_public_bundle_lower_source_origin h).2
    ⟨⟨bundle, origin⟩⟩

theorem exactConvention_to_same_object_closure
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin :
      SondowProjectPudlakScaleOriginBridge
        h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :
    Nonempty (BoundedArithmeticLab.BoundedProofPredicate.ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_to_same_object_closure
    (exactConvention_to_concrete_checklist h bundle origin)

theorem exactConvention_to_same_object_closure_of_lower_source_origin
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin : PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) :
    Nonempty (BoundedArithmeticLab.BoundedProofPredicate.ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_to_same_object_closure
    (exactConvention_to_concrete_checklist_of_lower_source_origin h bundle origin)

theorem exactConvention_to_public_gap_instantiation
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin :
      SondowProjectPudlakScaleOriginBridge
        h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_to_public_gap_instantiation
    (exactConvention_to_concrete_checklist h bundle origin)

theorem exactConvention_to_public_gap_instantiation_of_lower_source_origin
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin : PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_to_public_gap_instantiation
    (exactConvention_to_concrete_checklist_of_lower_source_origin h bundle origin)

theorem exactConvention_not_main_rationality
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin :
      SondowProjectPudlakScaleOriginBridge
        h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :
    ¬ MainRationality :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_not_main_rationality
    (exactConvention_to_concrete_checklist h bundle origin)

theorem exactConvention_not_main_rationality_of_lower_source_origin
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin : PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) :
    ¬ MainRationality :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_not_main_rationality
    (exactConvention_to_concrete_checklist_of_lower_source_origin h bundle origin)

theorem splitMinChecked_to_same_object_closure
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin :
      SondowProjectPudlakScaleOriginBridge
        h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :
    Nonempty (BoundedArithmeticLab.BoundedProofPredicate.ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_to_same_object_closure
    (splitMinChecked_to_concrete_checklist h bundle origin)

theorem splitMinChecked_to_same_object_closure_of_lower_source_origin
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin : PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) :
    Nonempty (BoundedArithmeticLab.BoundedProofPredicate.ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_to_same_object_closure
    (splitMinChecked_to_concrete_checklist_of_lower_source_origin h bundle origin)

theorem splitMinChecked_to_public_gap_instantiation
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin :
      SondowProjectPudlakScaleOriginBridge
        h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_to_public_gap_instantiation
    (splitMinChecked_to_concrete_checklist h bundle origin)

theorem splitMinChecked_to_public_gap_instantiation_of_lower_source_origin
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin : PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_to_public_gap_instantiation
    (splitMinChecked_to_concrete_checklist_of_lower_source_origin h bundle origin)

theorem splitMinChecked_not_main_rationality
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin :
      SondowProjectPudlakScaleOriginBridge
        h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :
    ¬ MainRationality :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_not_main_rationality
    (splitMinChecked_to_concrete_checklist h bundle origin)

theorem splitMinChecked_not_main_rationality_of_lower_source_origin
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin : PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) :
    ¬ MainRationality :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_not_main_rationality
    (splitMinChecked_to_concrete_checklist_of_lower_source_origin h bundle origin)

theorem exactFamily_to_same_object_closure
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin :
      SondowProjectPudlakScaleOriginBridge
        h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :
    Nonempty (BoundedArithmeticLab.BoundedProofPredicate.ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_to_same_object_closure
    (exactFamily_to_concrete_checklist h bundle origin)

theorem exactFamily_to_same_object_closure_of_lower_source_origin
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin : PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) :
    Nonempty (BoundedArithmeticLab.BoundedProofPredicate.ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_to_same_object_closure
    (exactFamily_to_concrete_checklist_of_lower_source_origin h bundle origin)

theorem exactFamily_to_public_gap_instantiation
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin :
      SondowProjectPudlakScaleOriginBridge
        h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_to_public_gap_instantiation
    (exactFamily_to_concrete_checklist h bundle origin)

theorem exactFamily_to_public_gap_instantiation_of_lower_source_origin
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin : PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_to_public_gap_instantiation
    (exactFamily_to_concrete_checklist_of_lower_source_origin h bundle origin)

theorem exactFamily_not_main_rationality
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin :
      SondowProjectPudlakScaleOriginBridge
        h.toPudlakSideInputs bundle.toCertificateBackedGapCriterion.lower_source) :
    ¬ MainRationality :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_not_main_rationality
    (exactFamily_to_concrete_checklist h bundle origin)

theorem exactFamily_not_main_rationality_of_lower_source_origin
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
    (bundle :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound)
    (origin : PublicBundleLowerSourceOrigin h.toPudlakSideInputs bundle) :
    ¬ MainRationality :=
  _root_.SondowMainCheckedCodeBridge.SondowProjectPudlakConcreteBridgeReleaseSurface.checklist_not_main_rationality
    (exactFamily_to_concrete_checklist_of_lower_source_origin h bundle origin)

end SondowProjectPudlakExactInputBridgeReleaseSurface
end SondowMainCheckedCodeBridge
