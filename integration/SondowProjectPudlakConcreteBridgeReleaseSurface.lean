/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakConcreteBridgeChecklist

/-!
# Release surface for the concrete public Pudlak bridge

This module gives stable paper-facing names for the integration bridge between
the EulerLimit Pudlak-side certificate and the `BoundedArithmeticLab` CnBox
same-object/public-gap layer.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakConcreteBridgeReleaseSurface

theorem checklist_iff_scale_origin_bridge
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs} :
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist rootSide cert) ↔
      Nonempty (Σ' cert :
        BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakScaleOriginBridge
          rootSide cert.toCertificateBackedGapCriterion.lower_source) :=
  SondowProjectPudlakConcreteBridgeChecklist.nonempty_iff_scale_origin_bridge

theorem checklist_iff_pointwise_scaled_certificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs} :
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist rootSide cert) ↔
      Nonempty (Σ' cert :
        BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound,
        ∀ n : Nat,
          cert.toCertificateBackedGapCriterion.lower_source.conditions.scale_data.scale n =
            rootSide.literature_lower_bound.scale_data.scale n) :=
  SondowProjectPudlakConcreteBridgeChecklist.nonempty_iff_pointwise_scaled_computable_certificate

theorem checklist_iff_public_bundle_scale_origin_bridge
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs} :
    Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist rootSide cert) ↔
      Nonempty (Σ' bundle :
        BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
          MainRationality SondowAccepted bounds bound,
        SondowProjectPudlakScaleOriginBridge
          rootSide bundle.toCertificateBackedGapCriterion.lower_source) := by
  constructor
  · intro h
    rcases h with ⟨⟨cert, checklist⟩⟩
    exact ⟨⟨cert.toCertificateBundle,
      { scale_aligned := checklist.scale_aligned }⟩⟩
  · intro h
    rcases h with ⟨⟨bundle, origin⟩⟩
    let cert :
        BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds bound :=
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate.ofCertificateBundle
        bundle
    have horigin :
        SondowProjectPudlakScaleOriginBridge
          rootSide cert.toCertificateBackedGapCriterion.lower_source := by
      simpa [cert,
        BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate.ofCertificateBundle,
        BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate.toCertificateBackedGapCriterion]
        using origin
    exact ⟨⟨cert,
      SondowProjectPudlakConcreteBridgeChecklist.of_scaleOriginBridge
        rootSide cert horigin⟩⟩

theorem scale_origin_pointwise
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    (origin : SondowProjectPudlakScaleOriginBridge rootSide lower_source)
    (n : Nat) :
    lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.scale n :=
  origin.pointwise_scale_aligned n

theorem scale_origin_root_partial_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    (origin : SondowProjectPudlakScaleOriginBridge rootSide lower_source)
    (n : Nat) :
    RootToBoundedFormulaCode
      (_root_.rescaledPartialConsistencyCode rootSide.lowerBoundPackage.scale n)
      (BoundedArithmeticLab.partialConsistencyCode n) :=
  origin.root_rescaled_partial_translates n

theorem scale_origin_root_normalForm_translation
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    (origin : SondowProjectPudlakScaleOriginBridge rootSide lower_source)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        lower_source.conditions.scale_data.scale n) :=
  origin.root_normalForm_translates_external n

theorem checklist_target_eq_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert)
    (n : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target n =
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n).formula :=
  checklist.target_eq_box_formula n

theorem checklist_box_code_roundtrip_to_target
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert)
    (n : Nat) :
    BoundedArithmeticLab.BAFormula.decode
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n).code =
        some (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target n) :=
  checklist.box_code_roundtrip_to_target n

theorem checklist_carries_iff_pa_finite_consistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert)
    (n : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.CnBoxCarriesPAFiniteConsistency
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n) ↔
        BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement n :=
  checklist.carries_iff_pa_finite_consistency n

theorem checklist_to_same_object_closure
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    (h : Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist rootSide cert)) :
    Nonempty (BoundedArithmeticLab.BoundedProofPredicate.ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :=
  SondowProjectPudlakConcreteBridgeChecklist.nonempty_to_project_same_object_closure h

theorem checklist_to_completion_obligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    (h : Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist rootSide cert)) :
    BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound :=
  SondowProjectPudlakConcreteBridgeChecklist.nonempty_to_completion_obligation h

theorem checklist_to_public_gap_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    (h : Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist rootSide cert)) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  SondowProjectPudlakConcreteBridgeChecklist.nonempty_to_public_gap_instantiation h

theorem checklist_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    (h : Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist rootSide cert)) :
    ¬ MainRationality :=
  SondowProjectPudlakConcreteBridgeChecklist.nonempty_not_main_rationality h

end SondowProjectPudlakConcreteBridgeReleaseSurface
end SondowMainCheckedCodeBridge
