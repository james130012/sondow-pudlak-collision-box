/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakRootSourceAssemblyReleaseSurface

/-!
# Scale-data bridge release surface for the concrete public Pudlak bridge

This module refines the root-source bridge one level further.  Instead of
recording only the scale equality between a root-side exact input and a bounded
lower source, it exposes that equality as a registration between the root
`LiteraturePudlakTheorem5ScaleData` and the bounded
`TimeConstructibleScale` field carried by the lower source.

This is still an explicit audit obligation, not a proof that the two source
records are definitionally equal.  It makes the required object boundary
narrower and proves it is equivalent to the root-source assembly interface
already consumed by the public checklist.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakScaleDataBridgeReleaseSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakFieldOriginReleaseSurface
open SondowProjectPudlakRootSourceAssemblyReleaseSurface

structure RootBoundedScaleDataBridge
    (root_scale : _root_.LiteraturePudlakTheorem5ScaleData)
    (bounded_scale : BoundedArithmeticLab.TimeConstructibleScale) :
    Prop where
  scale_eq : bounded_scale.scale = root_scale.scale

namespace RootBoundedScaleDataBridge

theorem pointwise_scale_eq
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (bridge : RootBoundedScaleDataBridge root_scale bounded_scale)
    (n : Nat) :
    bounded_scale.scale n = root_scale.scale n := by
  rw [bridge.scale_eq]

def toLowerSourceBridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    (bridge :
      RootBoundedScaleDataBridge
        rootSide.literature_lower_bound.scale_data
        lower_source.conditions.scale_data) :
    RootBoundedLowerSourceBridge rootSide lower_source where
  scale_eq := bridge.scale_eq

theorem iff_lower_source_bridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource} :
    RootBoundedScaleDataBridge
        rootSide.literature_lower_bound.scale_data
        lower_source.conditions.scale_data ↔
      RootBoundedLowerSourceBridge rootSide lower_source := by
  constructor
  · intro bridge
    exact bridge.toLowerSourceBridge
  · intro bridge
    exact { scale_eq := bridge.scale_eq }

theorem root_normalForm_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    (bridge :
      RootBoundedScaleDataBridge
        rootSide.literature_lower_bound.scale_data
        lower_source.conditions.scale_data)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        lower_source.conditions.scale_data.scale n) :=
  bridge.toLowerSourceBridge.root_normalForm_translation n

end RootBoundedScaleDataBridge

structure ProjectConcreteFieldScaleDataAssembly
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) where
  index : ProjectConcreteCertificateFieldIndex
    MainRationality SondowAccepted bounds bound
  scale_bridge :
    RootBoundedScaleDataBridge
      rootSide.literature_lower_bound.scale_data
      index.lower_source.conditions.scale_data

namespace ProjectConcreteFieldScaleDataAssembly

def toRootSourceAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldScaleDataAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldRootSourceAssembly
      rootSide MainRationality SondowAccepted bounds bound where
  index := assembly.index
  source_bridge := assembly.scale_bridge.toLowerSourceBridge

def ofRootSourceAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldRootSourceAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldScaleDataAssembly
      rootSide MainRationality SondowAccepted bounds bound where
  index := assembly.index
  scale_bridge := { scale_eq := assembly.source_bridge.scale_eq }

def toFieldOrigin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldScaleDataAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldLowerSourceOrigin rootSide assembly.index :=
  assembly.toRootSourceAssembly.toFieldOrigin

def toPublicBundleLowerSourceOrigin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldScaleDataAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
      rootSide assembly.index.toCertificateBundle :=
  assembly.toRootSourceAssembly.toPublicBundleLowerSourceOrigin

theorem lower_source_scale_data_scale_eq_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldScaleDataAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale :=
  assembly.scale_bridge.scale_eq

theorem lower_source_pointwise_scale_eq_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldScaleDataAssembly
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    assembly.index.lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.scale n :=
  assembly.scale_bridge.pointwise_scale_eq n

theorem root_normalForm_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldScaleDataAssembly
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        assembly.index.lower_source.conditions.scale_data.scale n) :=
  assembly.scale_bridge.root_normalForm_translation n

end ProjectConcreteFieldScaleDataAssembly

theorem scaleDataAssembly_nonempty_iff_rootSourceAssembly_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldScaleDataAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectConcreteFieldRootSourceAssembly
        rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨assembly.toRootSourceAssembly⟩
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨ProjectConcreteFieldScaleDataAssembly.ofRootSourceAssembly assembly⟩

theorem scaleDataAssembly_nonempty_iff_fieldOrigin_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldScaleDataAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Σ' index : ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound,
        ProjectConcreteFieldLowerSourceOrigin rootSide index) :=
  scaleDataAssembly_nonempty_iff_rootSourceAssembly_nonempty.trans
    rootSourceAssembly_nonempty_iff_fieldOrigin_nonempty

theorem scaleDataAssembly_nonempty_iff_publicBundleLowerSourceOrigin_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldScaleDataAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Σ' bundle : ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
          rootSide bundle) :=
  scaleDataAssembly_nonempty_iff_rootSourceAssembly_nonempty.trans
    rootSourceAssembly_nonempty_iff_publicBundleLowerSourceOrigin_nonempty

theorem exactConvention_checklist_iff_scale_data_assembly
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
      Nonempty (ProjectConcreteFieldScaleDataAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactConvention_checklist_iff_root_source_assembly h).trans
      scaleDataAssembly_nonempty_iff_rootSourceAssembly_nonempty.symm

theorem splitMinChecked_checklist_iff_scale_data_assembly
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
      Nonempty (ProjectConcreteFieldScaleDataAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_checklist_iff_root_source_assembly h).trans
      scaleDataAssembly_nonempty_iff_rootSourceAssembly_nonempty.symm

theorem exactFamily_checklist_iff_scale_data_assembly
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
      Nonempty (ProjectConcreteFieldScaleDataAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactFamily_checklist_iff_root_source_assembly h).trans
      scaleDataAssembly_nonempty_iff_rootSourceAssembly_nonempty.symm

theorem exactConvention_to_concrete_checklist_of_scale_data_assembly
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
    (assembly : ProjectConcreteFieldScaleDataAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  exactConvention_to_concrete_checklist_of_root_source_assembly
    h assembly.toRootSourceAssembly

theorem exactConvention_to_same_object_closure_of_scale_data_assembly
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
    (assembly : ProjectConcreteFieldScaleDataAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  exactConvention_to_same_object_closure_of_root_source_assembly
    h assembly.toRootSourceAssembly

theorem exactConvention_to_public_gap_instantiation_of_scale_data_assembly
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
    (assembly : ProjectConcreteFieldScaleDataAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  exactConvention_to_public_gap_instantiation_of_root_source_assembly
    h assembly.toRootSourceAssembly

theorem exactConvention_not_main_rationality_of_scale_data_assembly
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
    (assembly : ProjectConcreteFieldScaleDataAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  exactConvention_not_main_rationality_of_root_source_assembly
    h assembly.toRootSourceAssembly

theorem splitMinChecked_to_same_object_closure_of_scale_data_assembly
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
    (assembly : ProjectConcreteFieldScaleDataAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  splitMinChecked_to_same_object_closure_of_root_source_assembly
    h assembly.toRootSourceAssembly

theorem splitMinChecked_to_public_gap_instantiation_of_scale_data_assembly
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
    (assembly : ProjectConcreteFieldScaleDataAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  splitMinChecked_to_public_gap_instantiation_of_root_source_assembly
    h assembly.toRootSourceAssembly

theorem splitMinChecked_not_main_rationality_of_scale_data_assembly
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
    (assembly : ProjectConcreteFieldScaleDataAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  splitMinChecked_not_main_rationality_of_root_source_assembly
    h assembly.toRootSourceAssembly

theorem exactFamily_to_same_object_closure_of_scale_data_assembly
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
    (assembly : ProjectConcreteFieldScaleDataAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  exactFamily_to_same_object_closure_of_root_source_assembly
    h assembly.toRootSourceAssembly

theorem exactFamily_to_public_gap_instantiation_of_scale_data_assembly
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
    (assembly : ProjectConcreteFieldScaleDataAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  exactFamily_to_public_gap_instantiation_of_root_source_assembly
    h assembly.toRootSourceAssembly

theorem exactFamily_not_main_rationality_of_scale_data_assembly
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
    (assembly : ProjectConcreteFieldScaleDataAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  exactFamily_not_main_rationality_of_root_source_assembly
    h assembly.toRootSourceAssembly

end SondowProjectPudlakScaleDataBridgeReleaseSurface
end SondowMainCheckedCodeBridge
