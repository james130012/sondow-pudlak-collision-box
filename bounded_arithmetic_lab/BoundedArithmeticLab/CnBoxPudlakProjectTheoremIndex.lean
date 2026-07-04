/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectAuditChecklist

/-!
# Project public collision theorem index

This module provides stable theorem aliases for the public kernel, project
certificate bundle, and audit checklist layers.  It is intended as a small
paper-facing index over the already verified project instantiation route.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace ProjectPublicCollisionTheoremIndex

theorem public_instantiation_not_hypothesis
    {Hypothesis : Prop}
    (inst : PublicCollisionInstantiation Hypothesis) :
    ¬ Hypothesis :=
  inst.not_hypothesis

theorem public_gap_instantiation_not_hypothesis
    {Hypothesis : Prop}
    (inst : PublicGapCollisionInstantiation Hypothesis) :
    ¬ Hypothesis :=
  inst.not_hypothesis

theorem public_separated_instantiation_not_hypothesis
    {Hypothesis : Prop}
    (inst : PublicSeparatedCollisionInstantiation Hypothesis) :
    ¬ Hypothesis :=
  inst.not_hypothesis

theorem audit_public_api_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    False :=
  checklist.public_api_collision hmain

theorem audit_public_gap_api_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    False :=
  checklist.public_gap_api_collision hmain

theorem audit_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.not_main_rationality

theorem audit_external_gap_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.external_gap_not_main_rationality

theorem audit_nonempty_iff_bundle_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) :=
  projectPublicCollisionAuditChecklist_nonempty_iff_bundle_nonempty

theorem audit_nonempty_iff_project_checklist_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
        MainRationality SondowAccepted bounds bound) :=
  projectPublicCollisionAuditChecklist_nonempty_iff_projectChecklist_nonempty

theorem audit_nonempty_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound)) :
    ¬ MainRationality :=
  projectPublicCollisionAuditChecklist_nonempty_not_main_rationality h

theorem audit_nonempty_to_public_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) :=
  projectPublicCollisionAuditChecklist_nonempty_to_publicInstantiation h

theorem bundle_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  bundle.not_main_rationality

theorem bundle_nonempty_iff_project_checklist_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
        MainRationality SondowAccepted bounds bound) :=
  projectPublicCollisionCertificateBundle_nonempty_iff_projectChecklist_nonempty

theorem bundle_nonempty_to_external_gap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound)) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  projectPublicCollisionCertificateBundle_nonempty_to_externalGapCriterion h

theorem bundle_nonempty_to_public_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) :=
  projectPublicCollisionCertificateBundle_nonempty_to_publicCollisionInstantiation h

theorem external_gap_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (h : HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound) :
    ¬ MainRationality :=
  BoundedProofPredicate.externalGapCriterion_not_main_rationality h

theorem audit_public_collision_coherent_with_bundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    checklist.toPublicCollisionInstantiation =
      checklist.bundle.toPublicCollisionInstantiation :=
  checklist.public_collision_instantiation_coherent_with_bundle

theorem audit_gap_collision_coherent_with_bundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    checklist.toPublicGapCollisionInstantiation =
      checklist.bundle.toPublicGapCollisionInstantiation :=
  checklist.public_gap_instantiation_coherent_with_bundle

end ProjectPublicCollisionTheoremIndex
end BoundedProofPredicate
end BoundedArithmeticLab
