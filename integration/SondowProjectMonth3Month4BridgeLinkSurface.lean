/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4CollisionReadinessSurface
import integration.SondowProjectPudlakPowerScaleBridgeReleaseSurface

/-!
# Month 3/Month 4 bridge-link surface

This module links the current Month 3/Month 4 readiness checklist to the
existing root-to-bounded Pudlak bridge.  The point is not to identify the root
`FormulaCode` type with the `BoundedArithmeticLab` code type, but to expose the
already-proved `RootToBoundedFormulaCode` translations at the exact assembly
object consumed by the public CnBox/Pudlak bridge.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4BridgeLinkSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4CollisionReadinessSurface
open SondowProjectPudlakPowerScaleBridgeReleaseSurface

abbrev PowerScaleAssembly
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) : Type :=
  ProjectConcreteFieldPowerScaleAssembly
    rootSide MainRationality SondowAccepted bounds bound

def fieldIndex
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound :=
  assembly.index

def readiness
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    CollisionReadinessStatement assembly.index :=
  SondowProjectMonth3Month4CollisionReadinessSurface.statement assembly.index

def scaleOriginBridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    SondowProjectPudlakScaleOriginBridge
      rootSide assembly.index.lower_source :=
  assembly.power_registration.toLowerSourceBridge.toScaleOriginBridge

theorem lower_source_scale_eq_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    assembly.index.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale :=
  assembly.lower_source_scale_eq_root

theorem pointwise_scale_eq_root
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    assembly.index.lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.scale n :=
  (scaleOriginBridge assembly).pointwise_scale_aligned n

theorem bounded_scale_eq_power
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    assembly.index.lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.time_constructible_bound n ^
        rootSide.literature_lower_bound.scale_data.exponent :=
  assembly.bounded_scale_eq_power n

theorem root_normalForm_code_eq_rescaledPudlak
    {rootSide : SondowProjectLocalPudlakSideInputs}
    (n : Nat) :
    (rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n =
      rescaledPudlakStrengthenedFiniteConsistencyCode
        rootSide.literature_lower_bound.scale_data.scale n :=
  rootSide.lowerBoundPackage_normalForm_code_eq_rescaledPudlak n

theorem root_normalForm_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        assembly.index.lower_source.conditions.scale_data.scale n) :=
  assembly.root_normalForm_translation n

theorem root_rescaled_partial_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    RootToBoundedFormulaCode
      (_root_.rescaledPartialConsistencyCode rootSide.lowerBoundPackage.scale n)
      (BoundedArithmeticLab.partialConsistencyCode n) :=
  (scaleOriginBridge assembly).root_rescaled_partial_translates n

structure BridgeLinkStatement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    Prop where
  readiness :
    CollisionReadinessStatement assembly.index
  scale_origin_bridge :
    SondowProjectPudlakScaleOriginBridge
      rootSide assembly.index.lower_source
  lower_source_scale_eq_root :
    assembly.index.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale
  pointwise_scale_eq_root :
    ∀ n : Nat,
      assembly.index.lower_source.conditions.scale_data.scale n =
        rootSide.literature_lower_bound.scale_data.scale n
  bounded_scale_eq_power :
    ∀ n : Nat,
      assembly.index.lower_source.conditions.scale_data.scale n =
        rootSide.literature_lower_bound.scale_data.time_constructible_bound n ^
          rootSide.literature_lower_bound.scale_data.exponent
  root_normalForm_code_eq_rescaledPudlak :
    ∀ n : Nat,
      (rootSide.literature_lower_bound.toNormalForm
          rootSide.strengthened_to_partial).code n =
        rescaledPudlakStrengthenedFiniteConsistencyCode
          rootSide.literature_lower_bound.scale_data.scale n
  root_normalForm_translation :
    ∀ n : Nat,
      RootToBoundedFormulaCode
        ((rootSide.literature_lower_bound.toNormalForm
          rootSide.strengthened_to_partial).code n)
        (BoundedArithmeticLab.rescaledExternalPudlakCode
          assembly.index.lower_source.conditions.scale_data.scale n)
  root_rescaled_partial_translation :
    ∀ n : Nat,
      RootToBoundedFormulaCode
        (_root_.rescaledPartialConsistencyCode
          rootSide.lowerBoundPackage.scale n)
        (BoundedArithmeticLab.partialConsistencyCode n)

def statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    BridgeLinkStatement assembly where
  readiness := readiness assembly
  scale_origin_bridge := scaleOriginBridge assembly
  lower_source_scale_eq_root := lower_source_scale_eq_root assembly
  pointwise_scale_eq_root := pointwise_scale_eq_root assembly
  bounded_scale_eq_power := bounded_scale_eq_power assembly
  root_normalForm_code_eq_rescaledPudlak :=
    root_normalForm_code_eq_rescaledPudlak
  root_normalForm_translation := root_normalForm_translation assembly
  root_rescaled_partial_translation :=
    root_rescaled_partial_translation assembly

theorem statement_iff_readiness_and_scale_origin_bridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    BridgeLinkStatement assembly ↔
      CollisionReadinessStatement assembly.index ∧
        SondowProjectPudlakScaleOriginBridge
          rootSide assembly.index.lower_source := by
  constructor
  · intro h
    exact ⟨h.readiness, h.scale_origin_bridge⟩
  · intro _h
    exact statement assembly

structure Package
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) where
  assembly :
    PowerScaleAssembly
      rootSide MainRationality SondowAccepted bounds bound
  bridge_link_statement : BridgeLinkStatement assembly

def Package.ofAssembly
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    Package rootSide MainRationality SondowAccepted bounds bound where
  assembly := assembly
  bridge_link_statement := statement assembly

theorem package_nonempty_iff_power_scale_assembly_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty
        (Package rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (PowerScaleAssembly
          rootSide MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨pkg⟩
    exact ⟨pkg.assembly⟩
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨Package.ofAssembly assembly⟩

theorem exactConvention_checklist_iff_bridge_link_package
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
      Nonempty
        (Package h.toPudlakSideInputs
          MainRationality SondowAccepted bounds bound) :=
  (exactConvention_checklist_iff_power_scale_assembly h).trans
    package_nonempty_iff_power_scale_assembly_nonempty.symm

theorem splitMinChecked_checklist_iff_bridge_link_package
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
      Nonempty
        (Package h.toPudlakSideInputs
          MainRationality SondowAccepted bounds bound) :=
  (splitMinChecked_checklist_iff_power_scale_assembly h).trans
    package_nonempty_iff_power_scale_assembly_nonempty.symm

theorem exactFamily_checklist_iff_bridge_link_package
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
      Nonempty
        (Package h.toPudlakSideInputs
          MainRationality SondowAccepted bounds bound) :=
  (exactFamily_checklist_iff_power_scale_assembly h).trans
    package_nonempty_iff_power_scale_assembly_nonempty.symm


end SondowProjectMonth3Month4BridgeLinkSurface
end SondowMainCheckedCodeBridge
