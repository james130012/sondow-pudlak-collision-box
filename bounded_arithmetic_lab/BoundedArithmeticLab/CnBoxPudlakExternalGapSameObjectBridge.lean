/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakAcceptedSameObjectBridge

/-!
# External gap same-object bridge

This module exposes the same-object facts at the external gap criterion layer.
The external gap test is thereby tied to the canonical CnBox formula and code,
not merely to a definitionally related finite-consistency predicate.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace ExternalGapSameObjectBridge

structure Certificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion : ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)
    (n : Nat) : Prop where
  target_eq_box_formula :
    canonicalPudlakTargetFamilySpec.target n =
      (canonicalPudlakTargetFamilySpec.box n).formula
  code_eq_box_formulaCode :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        (canonicalPudlakTargetFamilySpec.box n).formulaCode
  box_code_roundtrip_to_target :
    BAFormula.decode (canonicalPudlakTargetFamilySpec.box n).code =
      some (canonicalPudlakTargetFamilySpec.target n)
  carries_iff_pa_finite_consistency :
    CnBoxCarriesPAFiniteConsistency
      (canonicalPudlakTargetFamilySpec.box n) ↔
        PAFiniteConsistencyStatement n
  lower_length_eq_canonical_length :
    criterion.lower_source.pa_length n = canonicalPudlakTargetFamilySpec.length n
  lower_length_eq_semantic_box_formula :
    criterion.lower_source.pa_length n =
      semanticBAProofLength PAAxiom
        (fun k => (canonicalPudlakTargetFamilySpec.box k).formula) n

theorem certificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion : ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)
    (n : Nat) :
    Certificate criterion n where
  target_eq_box_formula := CnBoxPudlakSameObjectBridge.target_eq_box_formula n
  code_eq_box_formulaCode := CnBoxPudlakSameObjectBridge.code_eq_box_formulaCode n
  box_code_roundtrip_to_target :=
    CnBoxPudlakSameObjectBridge.box_code_roundtrip_to_target n
  carries_iff_pa_finite_consistency :=
    CnBoxPudlakSameObjectBridge.carries_iff_pa_finite_consistency n
  lower_length_eq_canonical_length := criterion.lowerLength_eq_canonicalLength n
  lower_length_eq_semantic_box_formula := by
    rw [criterion.length_eq n]
    rfl

theorem target_eq_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (_criterion : ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n =
      (canonicalPudlakTargetFamilySpec.box n).formula :=
  CnBoxPudlakSameObjectBridge.target_eq_box_formula n

theorem code_eq_box_formulaCode
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (_criterion : ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        (canonicalPudlakTargetFamilySpec.box n).formulaCode :=
  CnBoxPudlakSameObjectBridge.code_eq_box_formulaCode n

theorem box_code_roundtrip_to_target
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (_criterion : ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)
    (n : Nat) :
    BAFormula.decode (canonicalPudlakTargetFamilySpec.box n).code =
      some (canonicalPudlakTargetFamilySpec.target n) :=
  CnBoxPudlakSameObjectBridge.box_code_roundtrip_to_target n

theorem carries_iff_pa_finite_consistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (_criterion : ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)
    (n : Nat) :
    CnBoxCarriesPAFiniteConsistency
      (canonicalPudlakTargetFamilySpec.box n) ↔
        PAFiniteConsistencyStatement n :=
  CnBoxPudlakSameObjectBridge.carries_iff_pa_finite_consistency n

theorem lower_length_eq_canonical_length
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion : ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)
    (n : Nat) :
    criterion.lower_source.pa_length n =
      canonicalPudlakTargetFamilySpec.length n :=
  criterion.lowerLength_eq_canonicalLength n

theorem lower_length_eq_semantic_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion : ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)
    (n : Nat) :
    criterion.lower_source.pa_length n =
      semanticBAProofLength PAAxiom
        (fun k => (canonicalPudlakTargetFamilySpec.box k).formula) n := by
  rw [criterion.length_eq n]
  rfl

theorem hasCriterion_certificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (h : HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)
    (n : Nat) :
    Nonempty (Σ' criterion : ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound,
      Certificate criterion n) := by
  rcases h with ⟨criterion⟩
  exact ⟨⟨criterion, certificate criterion n⟩⟩

theorem hasCriterion_to_public_gap_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (h : HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) :=
  externalGapCriterion_to_publicGapInstantiation_nonempty h

theorem hasCriterion_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (h : HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound) :
    ¬ MainRationality :=
  externalGapCriterion_not_main_rationality h

end ExternalGapSameObjectBridge
end BoundedProofPredicate
end BoundedArithmeticLab
