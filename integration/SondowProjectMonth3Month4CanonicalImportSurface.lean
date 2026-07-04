/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4BridgeLinkSurface

/-!
# Month 3/Month 4 canonical import surface

This module is the stable single-import surface for the Month 3 bounded PA
proof-predicate assembly and Month 4 Pudlak theorem-5 project-instance route.
It delegates to the bridge-link surface, preserving the exact path from the
public concrete checklist to the common Month 3/Month 4 collision package.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth3Month4CanonicalImportSurface

universe u v w

open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4CollisionReadinessSurface
open SondowProjectMonth3Month4BridgeLinkSurface

abbrev Month3Month4CanonicalReadinessStatement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :=
  CollisionReadinessStatement field_index

abbrev Month3Month4CanonicalBridgeLinkStatement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly
        rootSide MainRationality SondowAccepted bounds bound) :=
  BridgeLinkStatement assembly

abbrev Month3Month4CanonicalPackage
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : BoundedArithmeticLab.SondowComponentBounds)
    (bound : Nat → Real) :=
  Package rootSide MainRationality SondowAccepted bounds bound

theorem readiness_statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    Month3Month4CanonicalReadinessStatement field_index :=
  SondowProjectMonth3Month4CollisionReadinessSurface.statement field_index

theorem statement
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    Month3Month4CanonicalBridgeLinkStatement assembly :=
  SondowProjectMonth3Month4BridgeLinkSurface.statement assembly

theorem statement_iff_readiness_and_scale_origin_bridge
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (assembly :
      PowerScaleAssembly rootSide MainRationality SondowAccepted bounds bound) :
    Month3Month4CanonicalBridgeLinkStatement assembly ↔
      CollisionReadinessStatement assembly.index ∧
        SondowProjectPudlakScaleOriginBridge
          rootSide assembly.index.lower_source :=
  SondowProjectMonth3Month4BridgeLinkSurface.statement_iff_readiness_and_scale_origin_bridge
    assembly

theorem package_nonempty_iff_power_scale_assembly_nonempty
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty
        (Month3Month4CanonicalPackage
          rootSide MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (PowerScaleAssembly
          rootSide MainRationality SondowAccepted bounds bound) :=
  SondowProjectMonth3Month4BridgeLinkSurface.package_nonempty_iff_power_scale_assembly_nonempty

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
  SondowProjectMonth3Month4BridgeLinkSurface.root_normalForm_translation
    assembly n

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
  SondowProjectMonth3Month4BridgeLinkSurface.root_rescaled_partial_translation
    assembly n

theorem exactConvention_checklist_iff_canonical_import
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
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty (Month3Month4CanonicalPackage
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  SondowProjectMonth3Month4BridgeLinkSurface.exactConvention_checklist_iff_bridge_link_package
    h

theorem splitMinChecked_checklist_iff_canonical_import
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
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty (Month3Month4CanonicalPackage
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  SondowProjectMonth3Month4BridgeLinkSurface.splitMinChecked_checklist_iff_bridge_link_package
    h

theorem exactFamily_checklist_iff_canonical_import
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
    Nonempty (Σ' gap_cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist
        h.toPudlakSideInputs gap_cert) ↔
      Nonempty (Month3Month4CanonicalPackage
        h.toPudlakSideInputs MainRationality SondowAccepted bounds bound) :=
  SondowProjectMonth3Month4BridgeLinkSurface.exactFamily_checklist_iff_bridge_link_package
    h


end SondowProjectMonth3Month4CanonicalImportSurface
end SondowMainCheckedCodeBridge
