/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectPudlakPublicBridgeBoundary
import BoundedArithmeticLab.CnBoxPudlakProjectComputableGapCertificate

/-!
# Concrete public bridge checklist for the project Pudlak route

This integration module packages the concrete project certificate together
with the public EulerLimit/CnBox bridge boundary.  The main equivalence keeps
the obligation honest: a concrete checklist is exactly a computable CnBox gap
certificate plus the scale alignment needed to translate the root EulerLimit
codes into the `BoundedArithmeticLab` code layer.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge

structure SondowProjectPudlakScaleOriginBridge
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource) :
    Prop where
  scale_aligned :
    lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale

namespace SondowProjectPudlakScaleOriginBridge

theorem pointwise_scale_aligned
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    (bridge : SondowProjectPudlakScaleOriginBridge rootSide lower_source)
    (n : Nat) :
    lower_source.conditions.scale_data.scale n =
      rootSide.literature_lower_bound.scale_data.scale n := by
  rw [bridge.scale_aligned]

theorem root_rescaled_partial_translates
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    (_bridge : SondowProjectPudlakScaleOriginBridge rootSide lower_source)
    (n : Nat) :
    RootToBoundedFormulaCode
      (_root_.rescaledPartialConsistencyCode rootSide.lowerBoundPackage.scale n)
      (BoundedArithmeticLab.partialConsistencyCode n) :=
  SondowProjectPudlakPublicBridgeBoundary.mk_root_rescaled_partial_translates
    rootSide n

theorem root_normalForm_translates_external
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {lower_source : BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    (bridge : SondowProjectPudlakScaleOriginBridge rootSide lower_source)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        lower_source.conditions.scale_data.scale n) := by
  rw [rootSide.lowerBoundPackage_normalForm_code_eq_rescaledPudlak n]
  rw [bridge.scale_aligned]
  exact RootToBoundedFormulaCode.pudlakStrengthenedToExternal
    (rootSide.literature_lower_bound.scale_data.scale n)

end SondowProjectPudlakScaleOriginBridge

structure SondowProjectPudlakConcreteBridgeChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) : Prop where
  scale_aligned :
    cert.toCertificateBackedGapCriterion.lower_source.conditions.scale_data.scale =
      rootSide.literature_lower_bound.scale_data.scale
  boundary :
    SondowProjectPudlakPublicBridgeBoundary
      rootSide cert.toCertificateBackedGapCriterion
  external_gap_criterion :
    BoundedArithmeticLab.BoundedProofPredicate.HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound
  public_collision :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation MainRationality)
  public_gap :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality)
  not_main : ¬ MainRationality

namespace SondowProjectPudlakConcreteBridgeChecklist

def of_scaleAligned
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (hscale :
      cert.toCertificateBackedGapCriterion.lower_source.conditions.scale_data.scale =
        rootSide.literature_lower_bound.scale_data.scale) :
    SondowProjectPudlakConcreteBridgeChecklist rootSide cert where
  scale_aligned := hscale
  boundary :=
    SondowProjectPudlakPublicBridgeBoundary.of_scaleAligned
      rootSide cert.toCertificateBackedGapCriterion hscale
  external_gap_criterion := cert.toExternalGapCriterionWitness
  public_collision := ⟨cert.toPublicCollisionInstantiation⟩
  public_gap := ⟨cert.toPublicGapCollisionInstantiation⟩
  not_main := cert.not_main_rationality

theorem nonempty_iff_scaled_computable_certificate
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
        cert.toCertificateBackedGapCriterion.lower_source.conditions.scale_data.scale =
          rootSide.literature_lower_bound.scale_data.scale) := by
  constructor
  · intro h
    rcases h with ⟨⟨cert, checklist⟩⟩
    exact ⟨⟨cert, checklist.scale_aligned⟩⟩
  · intro h
    rcases h with ⟨⟨cert, hscale⟩⟩
    exact ⟨⟨cert, of_scaleAligned rootSide cert hscale⟩⟩

def of_pointwiseScaleAligned
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (hscale :
      ∀ n : Nat,
        cert.toCertificateBackedGapCriterion.lower_source.conditions.scale_data.scale n =
          rootSide.literature_lower_bound.scale_data.scale n) :
    SondowProjectPudlakConcreteBridgeChecklist rootSide cert :=
  of_scaleAligned rootSide cert (funext hscale)

theorem nonempty_iff_pointwise_scaled_computable_certificate
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
            rootSide.literature_lower_bound.scale_data.scale n) := by
  constructor
  · intro h
    rcases h with ⟨⟨cert, checklist⟩⟩
    exact ⟨⟨cert, by
      intro n
      rw [checklist.scale_aligned]⟩⟩
  · intro h
    rcases h with ⟨⟨cert, hscale⟩⟩
    exact ⟨⟨cert, of_pointwiseScaleAligned rootSide cert hscale⟩⟩

def of_scaleOriginBridge
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (origin : SondowProjectPudlakScaleOriginBridge
      rootSide cert.toCertificateBackedGapCriterion.lower_source) :
    SondowProjectPudlakConcreteBridgeChecklist rootSide cert :=
  of_scaleAligned rootSide cert origin.scale_aligned

theorem nonempty_iff_scale_origin_bridge
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
          rootSide cert.toCertificateBackedGapCriterion.lower_source) := by
  constructor
  · intro h
    rcases h with ⟨⟨cert, checklist⟩⟩
    exact ⟨⟨cert, { scale_aligned := checklist.scale_aligned }⟩⟩
  · intro h
    rcases h with ⟨⟨cert, origin⟩⟩
    exact ⟨⟨cert, of_scaleOriginBridge rootSide cert origin⟩⟩

def toBoundary
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert) :
    SondowProjectPudlakPublicBridgeBoundary
      rootSide cert.toCertificateBackedGapCriterion :=
  checklist.boundary

theorem root_rescaled_partial_translates
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert)
    (n : Nat) :
    RootToBoundedFormulaCode
      (_root_.rescaledPartialConsistencyCode rootSide.lowerBoundPackage.scale n)
      (BoundedArithmeticLab.partialConsistencyCode n) :=
  checklist.boundary.root_rescaled_partial_translates n

theorem root_normalForm_translates_external
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert)
    (n : Nat) :
    RootToBoundedFormulaCode
      ((rootSide.literature_lower_bound.toNormalForm
        rootSide.strengthened_to_partial).code n)
      (BoundedArithmeticLab.rescaledExternalPudlakCode
        cert.toCertificateBackedGapCriterion.lower_source.conditions.scale_data.scale n) :=
  checklist.boundary.root_normalForm_translates_external n

theorem external_gap_same_object_certificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert)
    (n : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.ExternalGapSameObjectBridge.Certificate
      cert.toCertificateBackedGapCriterion n :=
  checklist.boundary.external_gap_same_object n

theorem target_eq_box_formula
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
  (checklist.external_gap_same_object_certificate n).target_eq_box_formula

theorem code_eq_box_formulaCode
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert)
    (n : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.code
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target n) =
        (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box n).formulaCode :=
  (checklist.external_gap_same_object_certificate n).code_eq_box_formulaCode

theorem box_code_roundtrip_to_target
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
  (checklist.external_gap_same_object_certificate n).box_code_roundtrip_to_target

theorem carries_iff_pa_finite_consistency
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
  (checklist.external_gap_same_object_certificate n).carries_iff_pa_finite_consistency

theorem lower_length_eq_semantic_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert)
    (n : Nat) :
    cert.toCertificateBackedGapCriterion.lower_source.pa_length n =
      BoundedArithmeticLab.semanticBAProofLength BoundedArithmeticLab.PAAxiom
        (fun k =>
          (BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.box k).formula)
        n :=
  (checklist.external_gap_same_object_certificate n).lower_length_eq_semantic_box_formula

theorem to_external_gap_criterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert) :
    BoundedArithmeticLab.BoundedProofPredicate.HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  checklist.external_gap_criterion

theorem to_public_collision_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert) :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation MainRationality) :=
  checklist.public_collision

theorem to_public_gap_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) :=
  checklist.public_gap

def toProjectSameObjectBridgeClosure
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (_checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert) :
    BoundedArithmeticLab.BoundedProofPredicate.ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound :=
  BoundedArithmeticLab.BoundedProofPredicate.ProjectSameObjectBridgeClosure.ofComputableGapCertificate
    cert

theorem to_completion_obligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (_checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert) :
    BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound :=
  cert.toCompletionObligation

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {cert : BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound}
    (checklist : SondowProjectPudlakConcreteBridgeChecklist rootSide cert) :
    ¬ MainRationality :=
  checklist.not_main

theorem nonempty_to_public_gap_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    (h : Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist rootSide cert)) :
    Nonempty (BoundedArithmeticLab.PublicGapCollisionInstantiation MainRationality) := by
  rcases h with ⟨⟨_cert, checklist⟩⟩
  exact checklist.to_public_gap_instantiation

theorem nonempty_to_public_collision_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    (h : Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist rootSide cert)) :
    Nonempty (BoundedArithmeticLab.PublicCollisionInstantiation MainRationality) := by
  rcases h with ⟨⟨_cert, checklist⟩⟩
  exact checklist.to_public_collision_instantiation

theorem nonempty_to_project_same_object_closure
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    (h : Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist rootSide cert)) :
    Nonempty (BoundedArithmeticLab.BoundedProofPredicate.ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) := by
  rcases h with ⟨⟨_cert, checklist⟩⟩
  exact ⟨checklist.toProjectSameObjectBridgeClosure⟩

theorem nonempty_to_completion_obligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    (h : Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist rootSide cert)) :
    BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound := by
  rcases h with ⟨⟨_cert, checklist⟩⟩
  exact checklist.to_completion_obligation

theorem nonempty_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    (h : Nonempty (Σ' cert :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound,
      SondowProjectPudlakConcreteBridgeChecklist rootSide cert)) :
    ¬ MainRationality := by
  rcases h with ⟨⟨_cert, checklist⟩⟩
  exact checklist.not_main_rationality

end SondowProjectPudlakConcreteBridgeChecklist

end SondowMainCheckedCodeBridge
