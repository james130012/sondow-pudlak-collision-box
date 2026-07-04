/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectSameObjectClosure

/-!
# Project same-object closure release surface

This module gives stable paper-facing names for the project-level same-object
closure equivalences and for the direct public-gap consequences.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace ProjectSameObjectBridgeReleaseSurface

theorem closure_iff_computable_gap_certificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound) :=
  projectSameObjectBridgeClosure_nonempty_iff_computableGapCertificate

theorem closure_iff_public_certificate_bundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) :=
  projectSameObjectBridgeClosure_nonempty_iff_bundle_nonempty

theorem closure_iff_completion_obligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) ↔
      ProjectPublicCollisionCompletionObligation
        MainRationality SondowAccepted bounds bound :=
  projectSameObjectBridgeClosure_nonempty_iff_completionObligation

theorem closure_iff_public_collision_checklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
        MainRationality SondowAccepted bounds bound) :=
  projectSameObjectBridgeClosure_nonempty_iff_projectChecklist_nonempty

theorem closure_target_eq_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n =
      (canonicalPudlakTargetFamilySpec.box n).formula :=
  closure.target_eq_box_formula n

theorem closure_code_eq_box_formulaCode
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        (canonicalPudlakTargetFamilySpec.box n).formulaCode :=
  closure.code_eq_box_formulaCode n

theorem closure_box_code_roundtrip_to_target
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    BAFormula.decode (canonicalPudlakTargetFamilySpec.box n).code =
      some (canonicalPudlakTargetFamilySpec.target n) :=
  closure.box_code_roundtrip_to_target n

theorem closure_carries_iff_pa_finite_consistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    CnBoxCarriesPAFiniteConsistency
      (canonicalPudlakTargetFamilySpec.box n) ↔
        PAFiniteConsistencyStatement n :=
  closure.carries_iff_pa_finite_consistency n

theorem closure_length_eq_semantic_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.length n =
      semanticBAProofLength PAAxiom
        (fun k => (canonicalPudlakTargetFamilySpec.box k).formula) n :=
  closure.length_eq_semantic_box_formula n

theorem closure_to_external_gap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  projectSameObjectBridgeClosure_nonempty_to_externalGapCriterion h

theorem closure_to_public_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) :=
  projectSameObjectBridgeClosure_nonempty_to_publicInstantiation h

theorem closure_to_public_gap_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) :=
  projectSameObjectBridgeClosure_nonempty_to_publicGapInstantiation h

theorem closure_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)) :
    ¬ MainRationality :=
  projectSameObjectBridgeClosure_nonempty_not_main_rationality h

end ProjectSameObjectBridgeReleaseSurface
end BoundedProofPredicate
end BoundedArithmeticLab
