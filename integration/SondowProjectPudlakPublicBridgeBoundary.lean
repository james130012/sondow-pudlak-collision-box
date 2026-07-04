/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakInstantiation
import BoundedArithmeticLab.CnBoxPudlakExternalGapSameObjectBridge

/-!
# Public bridge boundary between EulerLimit and the CnBox same-object layer

This module is deliberately an integration-layer boundary.  The EulerLimit
side uses the root `FormulaCode`, while the `BoundedArithmeticLab` CnBox side
uses `BoundedArithmeticLab.FormulaCode`; the bridge therefore records an
explicit translation relation rather than pretending the code types are equal.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge

inductive RootToBoundedFormulaCode :
    _root_.FormulaCode → BoundedArithmeticLab.FormulaCode → Prop
  | partialConsistency (n : Nat) :
      RootToBoundedFormulaCode
        (_root_.partialConsistencyCode n)
        (BoundedArithmeticLab.partialConsistencyCode n)
  | pudlakStrengthenedToExternal (n : Nat) :
      RootToBoundedFormulaCode
        (_root_.pudlakStrengthenedFiniteConsistencyCode n)
        (BoundedArithmeticLab.externalPudlakCode n)

structure SondowProjectPudlakPublicBridgeBoundary
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (criterion : BoundedArithmeticLab.BoundedProofPredicate.ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound) : Prop where
  scale_aligned :
    criterion.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale
  root_rescaled_partial_translates :
    ∀ n : Nat,
      RootToBoundedFormulaCode
        (_root_.rescaledPartialConsistencyCode rootSide.lowerBoundPackage.scale n)
        (BoundedArithmeticLab.partialConsistencyCode n)
  root_normalForm_translates_external :
    ∀ n : Nat,
      RootToBoundedFormulaCode
        ((rootSide.literature_lower_bound.toNormalForm
          rootSide.strengthened_to_partial).code n)
        (BoundedArithmeticLab.rescaledExternalPudlakCode
          criterion.lower_source.conditions.scale_data.scale n)
  external_gap_same_object :
    ∀ n : Nat,
      BoundedArithmeticLab.BoundedProofPredicate.ExternalGapSameObjectBridge.Certificate
        criterion n

namespace SondowProjectPudlakPublicBridgeBoundary

theorem mk_root_rescaled_partial_translates
    (rootSide : SondowProjectLocalPudlakSideInputs) (n : Nat) :
    RootToBoundedFormulaCode
      (_root_.rescaledPartialConsistencyCode rootSide.lowerBoundPackage.scale n)
      (BoundedArithmeticLab.partialConsistencyCode n) := by
  rw [rootSide.lowerBoundPackage_rescaledCode_eq_partialConsistencyCode n]
  exact RootToBoundedFormulaCode.partialConsistency n

theorem mk_root_normalForm_translates_external
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (criterion : BoundedArithmeticLab.BoundedProofPredicate.ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)
    (hscale :
      criterion.lower_source.conditions.scale_data.scale =
        rootSide.literature_lower_bound.scale_data.scale)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        criterion.lower_source.conditions.scale_data.scale n) := by
  rw [rootSide.lowerBoundPackage_normalForm_code_eq_rescaledPudlak n]
  rw [hscale]
  exact RootToBoundedFormulaCode.pudlakStrengthenedToExternal
    (rootSide.literature_lower_bound.scale_data.scale n)

theorem of_scaleAligned
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (criterion : BoundedArithmeticLab.BoundedProofPredicate.ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)
    (hscale :
      criterion.lower_source.conditions.scale_data.scale =
        rootSide.literature_lower_bound.scale_data.scale) :
    SondowProjectPudlakPublicBridgeBoundary rootSide criterion where
  scale_aligned := hscale
  root_rescaled_partial_translates :=
    mk_root_rescaled_partial_translates rootSide
  root_normalForm_translates_external :=
    mk_root_normalForm_translates_external rootSide criterion hscale
  external_gap_same_object :=
    BoundedArithmeticLab.BoundedProofPredicate.ExternalGapSameObjectBridge.certificate criterion

theorem target_eq_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {criterion : BoundedArithmeticLab.BoundedProofPredicate.ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound}
    (_boundary : SondowProjectPudlakPublicBridgeBoundary rootSide criterion)
    (n : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target n =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n).formula :=
  BoundedArithmeticLab.BoundedProofPredicate.ExternalGapSameObjectBridge.target_eq_box_formula
    criterion n

theorem lower_length_eq_semantic_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {criterion : BoundedArithmeticLab.BoundedProofPredicate.ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound}
    (_boundary : SondowProjectPudlakPublicBridgeBoundary rootSide criterion)
    (n : Nat) :
    criterion.lower_source.pa_length n =
      BoundedArithmeticLab.semanticBAProofLength
        BoundedArithmeticLab.PAAxiom
        (fun k =>
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box k).formula)
        n :=
  BoundedArithmeticLab.BoundedProofPredicate.ExternalGapSameObjectBridge.lower_length_eq_semantic_box_formula
    criterion n

theorem has_public_gap_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {criterion : BoundedArithmeticLab.BoundedProofPredicate.ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound}
    (_boundary : SondowProjectPudlakPublicBridgeBoundary rootSide criterion) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  BoundedArithmeticLab.BoundedProofPredicate.ExternalGapSameObjectBridge.hasCriterion_to_public_gap_instantiation
    ⟨criterion⟩

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {criterion : BoundedArithmeticLab.BoundedProofPredicate.ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound}
    (_boundary : SondowProjectPudlakPublicBridgeBoundary rootSide criterion) :
    ¬ MainRationality :=
  BoundedArithmeticLab.BoundedProofPredicate.ExternalGapSameObjectBridge.hasCriterion_not_main_rationality
    ⟨criterion⟩

end SondowProjectPudlakPublicBridgeBoundary

end SondowMainCheckedCodeBridge
