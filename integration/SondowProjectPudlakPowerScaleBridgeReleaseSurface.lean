/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakScaleDataBridgeReleaseSurface

/-!
# Power-scale bridge release surface for the concrete public Pudlak bridge

This module refines the scale-data bridge to the exact Theorem 5 power-scale
shape.  The bounded lower source only stores a `TimeConstructibleScale`, while
the root literature source stores the more explicit `time_constructible_bound`
and `exponent`.  The bridge therefore records the auditable pointwise power
registration

`bounded_scale.scale n = root_scale.time_constructible_bound n ^ root_scale.exponent`.

Using the root `scale_eq` field, this is equivalent to the scale-data bridge
already consumed by the public CnBox/Pudlak checklist.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakPowerScaleBridgeReleaseSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectPudlakFieldOriginReleaseSurface
open SondowProjectPudlakRootSourceAssemblyReleaseSurface
open SondowProjectPudlakScaleDataBridgeReleaseSurface

structure RootBoundedPowerScaleRegistration
    (root_scale : _root_.LiteraturePudlakTheorem5ScaleData)
    (bounded_scale : BoundedArithmeticLab.TimeConstructibleScale) :
    Prop where
  bounded_scale_eq_power :
    ∀ n : Nat,
      bounded_scale.scale n =
        root_scale.time_constructible_bound n ^ root_scale.exponent

namespace RootBoundedPowerScaleRegistration

theorem to_scale_eq
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (registration :
      RootBoundedPowerScaleRegistration root_scale bounded_scale) :
    bounded_scale.scale = root_scale.scale := by
  funext n
  rw [registration.bounded_scale_eq_power n]
  exact (root_scale.scale_eq n).symm

def toScaleDataBridge
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (registration :
      RootBoundedPowerScaleRegistration root_scale bounded_scale) :
    RootBoundedScaleDataBridge root_scale bounded_scale where
  scale_eq := registration.to_scale_eq

theorem pointwise_scale_eq
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale}
    (registration :
      RootBoundedPowerScaleRegistration root_scale bounded_scale)
    (n : Nat) :
    bounded_scale.scale n = root_scale.scale n :=
  registration.toScaleDataBridge.pointwise_scale_eq n

theorem iff_scale_data_bridge
    {root_scale : _root_.LiteraturePudlakTheorem5ScaleData}
    {bounded_scale : BoundedArithmeticLab.TimeConstructibleScale} :
    RootBoundedPowerScaleRegistration root_scale bounded_scale ↔
      RootBoundedScaleDataBridge root_scale bounded_scale := by
  constructor
  · intro registration
    exact registration.toScaleDataBridge
  · intro bridge
    refine ⟨?_⟩
    intro n
    rw [bridge.scale_eq]
    exact root_scale.scale_eq n

def toLowerSourceBridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    (registration :
      RootBoundedPowerScaleRegistration
        rootSide.literature_lower_bound.scale_data
        lower_source.conditions.scale_data) :
    RootBoundedLowerSourceBridge rootSide lower_source :=
  registration.toScaleDataBridge.toLowerSourceBridge

theorem iff_lower_source_bridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource} :
    RootBoundedPowerScaleRegistration
        rootSide.literature_lower_bound.scale_data
        lower_source.conditions.scale_data ↔
      RootBoundedLowerSourceBridge rootSide lower_source :=
  iff_scale_data_bridge.trans RootBoundedScaleDataBridge.iff_lower_source_bridge

theorem root_normalForm_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    (registration :
      RootBoundedPowerScaleRegistration
        rootSide.literature_lower_bound.scale_data
        lower_source.conditions.scale_data)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        lower_source.conditions.scale_data.scale n) :=
  registration.toScaleDataBridge.root_normalForm_translation n

end RootBoundedPowerScaleRegistration

structure ProjectConcreteFieldPowerScaleAssembly
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) where
  index : ProjectConcreteCertificateFieldIndex
    MainRationality SondowAccepted bounds bound
  power_registration :
    RootBoundedPowerScaleRegistration
      rootSide.literature_lower_bound.scale_data
      index.lower_source.conditions.scale_data

namespace ProjectConcreteFieldPowerScaleAssembly

def toScaleDataAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldScaleDataAssembly
      rootSide MainRationality SondowAccepted bounds bound where
  index := assembly.index
  scale_bridge := assembly.power_registration.toScaleDataBridge

def ofScaleDataAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldScaleDataAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound where
  index := assembly.index
  power_registration :=
    (RootBoundedPowerScaleRegistration.iff_scale_data_bridge).2
      assembly.scale_bridge

def toRootSourceAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldRootSourceAssembly
      rootSide MainRationality SondowAccepted bounds bound :=
  assembly.toScaleDataAssembly.toRootSourceAssembly

def toFieldOrigin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteFieldLowerSourceOrigin rootSide assembly.index :=
  assembly.toScaleDataAssembly.toFieldOrigin

def toPublicBundleLowerSourceOrigin
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
      rootSide assembly.index.toCertificateBundle :=
  assembly.toScaleDataAssembly.toPublicBundleLowerSourceOrigin

theorem bounded_scale_eq_power
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    assembly.index.lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.time_constructible_bound n ^
        rootSide.literature_lower_bound.scale_data.exponent :=
  assembly.power_registration.bounded_scale_eq_power n

theorem lower_source_scale_eq_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale :=
  assembly.power_registration.to_scale_eq

theorem root_normalForm_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        assembly.index.lower_source.conditions.scale_data.scale n) :=
  assembly.power_registration.root_normalForm_translation n

end ProjectConcreteFieldPowerScaleAssembly

theorem powerScaleAssembly_nonempty_iff_scaleDataAssembly_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectConcreteFieldScaleDataAssembly
        rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨assembly.toScaleDataAssembly⟩
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨ProjectConcreteFieldPowerScaleAssembly.ofScaleDataAssembly assembly⟩

theorem powerScaleAssembly_nonempty_iff_rootSourceAssembly_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectConcreteFieldRootSourceAssembly
        rootSide MainRationality SondowAccepted bounds bound) :=
  powerScaleAssembly_nonempty_iff_scaleDataAssembly_nonempty.trans
    scaleDataAssembly_nonempty_iff_rootSourceAssembly_nonempty

theorem powerScaleAssembly_nonempty_iff_publicBundleLowerSourceOrigin_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty (ProjectConcreteFieldPowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Σ' bundle : ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakExactInputBridgeReleaseSurface.PublicBundleLowerSourceOrigin
          rootSide bundle) :=
  powerScaleAssembly_nonempty_iff_scaleDataAssembly_nonempty.trans
    scaleDataAssembly_nonempty_iff_publicBundleLowerSourceOrigin_nonempty

theorem exactConvention_checklist_iff_power_scale_assembly
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
      Nonempty (ProjectConcreteFieldPowerScaleAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactConvention_checklist_iff_scale_data_assembly h).trans
    powerScaleAssembly_nonempty_iff_scaleDataAssembly_nonempty.symm

theorem splitMinChecked_checklist_iff_power_scale_assembly
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
      Nonempty (ProjectConcreteFieldPowerScaleAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_checklist_iff_scale_data_assembly h).trans
    powerScaleAssembly_nonempty_iff_scaleDataAssembly_nonempty.symm

theorem exactFamily_checklist_iff_power_scale_assembly
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
      Nonempty (ProjectConcreteFieldPowerScaleAssembly
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  (exactFamily_checklist_iff_scale_data_assembly h).trans
    powerScaleAssembly_nonempty_iff_scaleDataAssembly_nonempty.symm

theorem exactConvention_to_concrete_checklist_of_power_scale_assembly
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
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (Σ' cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist h.toPudlakSideInputs cert) :=
  exactConvention_to_concrete_checklist_of_scale_data_assembly
    h assembly.toScaleDataAssembly

theorem exactConvention_to_same_object_closure_of_power_scale_assembly
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
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  exactConvention_to_same_object_closure_of_scale_data_assembly
    h assembly.toScaleDataAssembly

theorem exactConvention_to_public_gap_instantiation_of_power_scale_assembly
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
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  exactConvention_to_public_gap_instantiation_of_scale_data_assembly
    h assembly.toScaleDataAssembly

theorem exactConvention_not_main_rationality_of_power_scale_assembly
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
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  exactConvention_not_main_rationality_of_scale_data_assembly
    h assembly.toScaleDataAssembly

theorem splitMinChecked_to_same_object_closure_of_power_scale_assembly
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
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  splitMinChecked_to_same_object_closure_of_scale_data_assembly
    h assembly.toScaleDataAssembly

theorem splitMinChecked_to_public_gap_instantiation_of_power_scale_assembly
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
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  splitMinChecked_to_public_gap_instantiation_of_scale_data_assembly
    h assembly.toScaleDataAssembly

theorem splitMinChecked_not_main_rationality_of_power_scale_assembly
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
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  splitMinChecked_not_main_rationality_of_scale_data_assembly
    h assembly.toScaleDataAssembly

theorem exactFamily_to_same_object_closure_of_power_scale_assembly
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
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  exactFamily_to_same_object_closure_of_scale_data_assembly
    h assembly.toScaleDataAssembly

theorem exactFamily_to_public_gap_instantiation_of_power_scale_assembly
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
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  exactFamily_to_public_gap_instantiation_of_scale_data_assembly
    h assembly.toScaleDataAssembly

theorem exactFamily_not_main_rationality_of_power_scale_assembly
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
    (assembly : ProjectConcreteFieldPowerScaleAssembly
      h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  exactFamily_not_main_rationality_of_scale_data_assembly
    h assembly.toScaleDataAssembly

end SondowProjectPudlakPowerScaleBridgeReleaseSurface
end SondowMainCheckedCodeBridge
