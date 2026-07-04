/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakFieldOriginReleaseSurface

/-!
# Root-source assembly release surface for the concrete public Pudlak bridge

This module packages the remaining source-origin obligation as an assembly
object.  The field-origin layer proved that a concrete field index plus a
scale-origin witness reaches the public checklist.  Here we give the stronger
audit-facing object: a concrete field index together with a root-to-bounded
lower-source bridge for the same lower source.

The bridge still does not assert definitional equality between the EulerLimit
source and the bounded source.  It records the exact scale agreement needed for
the existing public bridge and proves that this is equivalent to the field
origin consumed downstream.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakRootSourceAssemblyReleaseSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakFieldOriginReleaseSurface

structure RootBoundedLowerSourceBridge
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource) :
    Prop where
  scale_eq :
    lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale

namespace RootBoundedLowerSourceBridge

def toScaleOriginBridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    (bridge : RootBoundedLowerSourceBridge rootSide lower_source) :
    SondowProjectPudlakScaleOriginBridge rootSide lower_source where
  scale_aligned := bridge.scale_eq

theorem pointwise_scale_eq
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    (bridge : RootBoundedLowerSourceBridge rootSide lower_source)
    (n : Nat) :
    lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.scale n :=
  bridge.toScaleOriginBridge.pointwise_scale_aligned n

theorem iff_scale_origin_bridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource} :
    RootBoundedLowerSourceBridge rootSide lower_source ↔
      SondowProjectPudlakScaleOriginBridge rootSide lower_source := by
  constructor
  · intro bridge
    exact bridge.toScaleOriginBridge
  · intro origin
    exact { scale_eq := origin.scale_aligned }

theorem root_normalForm_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    (bridge : RootBoundedLowerSourceBridge rootSide lower_source)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        lower_source.conditions.scale_data.scale n) :=
  bridge.toScaleOriginBridge.root_normalForm_translates_external n

end RootBoundedLowerSourceBridge

structure ProjectConcreteFieldRootSourceAssembly
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) where
  index : ProjectConcreteCertificateFieldIndex
    MainRationality SondowAccepted bounds bound
  source_bridge :
    RootBoundedLowerSourceBridge rootSide index.lower_source

namespace ProjectConcreteFieldRootSourceAssembly

def toFieldOrigin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldRootSourceAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldLowerSourceOrigin rootSide assembly.index where
  scale_eq := assembly.source_bridge.scale_eq

def toPublicBundleLowerSourceOrigin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldRootSourceAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
      rootSide assembly.index.toCertificateBundle :=
  assembly.toFieldOrigin.toPublicBundleLowerSourceOrigin

def ofPublicBundleLowerSourceOrigin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound)
    (origin :
      SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
        rootSide bundle) :
    ProjectConcreteFieldRootSourceAssembly
      rootSide MainRationality SondowAccepted bounds bound := by
  let obligation := ProjectConcreteCertificateObligation.ofCertificateBundle bundle
  let index := ProjectConcreteCertificateFieldIndex.ofConcreteObligation obligation
  refine { index := index, source_bridge := ?_ }
  refine { scale_eq := ?_ }
  simpa [index, obligation,
    ProjectConcreteCertificateFieldIndex.ofConcreteObligation,
    ProjectConcreteCertificateFieldIndex.lower_source,
    ProjectConcreteCertificateObligation.ofCertificateBundle,
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
    ProjectLevelCnBoxSondowCompiledChecklist.toCertificateBackedGapCriterion] using origin.scale_eq

theorem lower_source_scale_eq_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldRootSourceAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale :=
  assembly.source_bridge.scale_eq

theorem bundle_lower_source_scale_eq_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldRootSourceAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ((assembly.index.toCertificateBundle.toCertificateBackedGapCriterion
        ).lower_source).conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale :=
  assembly.toPublicBundleLowerSourceOrigin.scale_eq

theorem root_normalForm_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldRootSourceAssembly
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        ((assembly.index.toCertificateBundle.toCertificateBackedGapCriterion
          ).lower_source).conditions.scale_data.scale n) :=
  assembly.toPublicBundleLowerSourceOrigin.root_normalForm_translation n

end ProjectConcreteFieldRootSourceAssembly

theorem rootSourceAssembly_nonempty_iff_fieldOrigin_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldRootSourceAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Σ' index : ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound,
        ProjectConcreteFieldLowerSourceOrigin rootSide index) := by
  constructor
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨⟨assembly.index, assembly.toFieldOrigin⟩⟩
  · intro h
    rcases h with ⟨⟨index, origin⟩⟩
    exact ⟨{
      index := index
      source_bridge := { scale_eq := origin.scale_eq } }⟩

theorem rootSourceAssembly_nonempty_iff_publicBundleOrigin_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldRootSourceAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Σ' index : ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
          rootSide index.toCertificateBundle) := by
  constructor
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨⟨assembly.index,
      assembly.toPublicBundleLowerSourceOrigin⟩⟩
  · intro h
    rcases h with ⟨⟨index, origin⟩⟩
    have field_origin :
        ProjectConcreteFieldLowerSourceOrigin rootSide index :=
      (ProjectConcreteFieldLowerSourceOrigin.iff_public_bundle_origin).2 origin
    exact (rootSourceAssembly_nonempty_iff_fieldOrigin_nonempty).2
      ⟨⟨index, field_origin⟩⟩

theorem rootSourceAssembly_nonempty_iff_publicBundleLowerSourceOrigin_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldRootSourceAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Σ' bundle : ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
          rootSide bundle) := by
  constructor
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨⟨assembly.index.toCertificateBundle,
      assembly.toPublicBundleLowerSourceOrigin⟩⟩
  · intro h
    rcases h with ⟨⟨bundle, origin⟩⟩
    exact ⟨ProjectConcreteFieldRootSourceAssembly.ofPublicBundleLowerSourceOrigin
      bundle origin⟩

theorem exactConvention_checklist_iff_root_source_assembly
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
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) ↔
      Nonempty (ProjectConcreteFieldRootSourceAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (_root_.SondowMainCheckedCodeBridge.SondowProjectPudlakExactInputBridgeReleaseSurface.exactConvention_checklist_iff_public_bundle_lower_source_origin h).trans
      rootSourceAssembly_nonempty_iff_publicBundleLowerSourceOrigin_nonempty.symm

theorem splitMinChecked_checklist_iff_root_source_assembly
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
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) ↔
      Nonempty (ProjectConcreteFieldRootSourceAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (_root_.SondowMainCheckedCodeBridge.SondowProjectPudlakExactInputBridgeReleaseSurface.splitMinChecked_checklist_iff_public_bundle_lower_source_origin h).trans
      rootSourceAssembly_nonempty_iff_publicBundleLowerSourceOrigin_nonempty.symm

theorem exactFamily_checklist_iff_root_source_assembly
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
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) ↔
      Nonempty (ProjectConcreteFieldRootSourceAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (_root_.SondowMainCheckedCodeBridge.SondowProjectPudlakExactInputBridgeReleaseSurface.exactFamily_checklist_iff_public_bundle_lower_source_origin h).trans
      rootSourceAssembly_nonempty_iff_publicBundleLowerSourceOrigin_nonempty.symm

theorem exactConvention_to_concrete_checklist_of_root_source_assembly
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
    (assembly : ProjectConcreteFieldRootSourceAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  SondowProjectPudlakFieldOriginReleaseSurface.exactConvention_to_concrete_checklist_of_field_origin
    h assembly.index assembly.toFieldOrigin

theorem exactConvention_to_same_object_closure_of_root_source_assembly
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
    (assembly : ProjectConcreteFieldRootSourceAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  SondowProjectPudlakFieldOriginReleaseSurface.exactConvention_to_same_object_closure_of_field_origin
    h assembly.index assembly.toFieldOrigin

theorem exactConvention_to_public_gap_instantiation_of_root_source_assembly
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
    (assembly : ProjectConcreteFieldRootSourceAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  SondowProjectPudlakFieldOriginReleaseSurface.exactConvention_to_public_gap_instantiation_of_field_origin
    h assembly.index assembly.toFieldOrigin

theorem exactConvention_not_main_rationality_of_root_source_assembly
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
    (assembly : ProjectConcreteFieldRootSourceAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  SondowProjectPudlakFieldOriginReleaseSurface.exactConvention_not_main_rationality_of_field_origin
    h assembly.index assembly.toFieldOrigin

theorem splitMinChecked_to_concrete_checklist_of_root_source_assembly
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
    (assembly : ProjectConcreteFieldRootSourceAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  SondowProjectPudlakFieldOriginReleaseSurface.splitMinChecked_to_concrete_checklist_of_field_origin
    h assembly.index assembly.toFieldOrigin

theorem splitMinChecked_to_same_object_closure_of_root_source_assembly
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
    (assembly : ProjectConcreteFieldRootSourceAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  SondowProjectPudlakFieldOriginReleaseSurface.splitMinChecked_to_same_object_closure_of_field_origin
    h assembly.index assembly.toFieldOrigin

theorem splitMinChecked_to_public_gap_instantiation_of_root_source_assembly
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
    (assembly : ProjectConcreteFieldRootSourceAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  SondowProjectPudlakFieldOriginReleaseSurface.splitMinChecked_to_public_gap_instantiation_of_field_origin
    h assembly.index assembly.toFieldOrigin

theorem splitMinChecked_not_main_rationality_of_root_source_assembly
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
    (assembly : ProjectConcreteFieldRootSourceAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  SondowProjectPudlakFieldOriginReleaseSurface.splitMinChecked_not_main_rationality_of_field_origin
    h assembly.index assembly.toFieldOrigin

theorem exactFamily_to_concrete_checklist_of_root_source_assembly
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
    (assembly : ProjectConcreteFieldRootSourceAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  SondowProjectPudlakFieldOriginReleaseSurface.exactFamily_to_concrete_checklist_of_field_origin
    h assembly.index assembly.toFieldOrigin

theorem exactFamily_to_same_object_closure_of_root_source_assembly
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
    (assembly : ProjectConcreteFieldRootSourceAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  SondowProjectPudlakFieldOriginReleaseSurface.exactFamily_to_same_object_closure_of_field_origin
    h assembly.index assembly.toFieldOrigin

theorem exactFamily_to_public_gap_instantiation_of_root_source_assembly
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
    (assembly : ProjectConcreteFieldRootSourceAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  SondowProjectPudlakFieldOriginReleaseSurface.exactFamily_to_public_gap_instantiation_of_field_origin
    h assembly.index assembly.toFieldOrigin

theorem exactFamily_not_main_rationality_of_root_source_assembly
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
    (assembly : ProjectConcreteFieldRootSourceAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  SondowProjectPudlakFieldOriginReleaseSurface.exactFamily_not_main_rationality_of_field_origin
    h assembly.index assembly.toFieldOrigin

end SondowProjectPudlakRootSourceAssemblyReleaseSurface
end SondowMainCheckedCodeBridge
