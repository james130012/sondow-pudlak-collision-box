/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.PublicCollisionExportSurface
import BoundedArithmeticLab.CnBoxPudlakProjectTheoremIndex

/-!
# CnBox/Pudlak project export surface

This module is the project-only export surface over the public kernel
instantiation route.  It names the audit checklist, certificate bundle, and
external gap theorem aliases that should remain in the project layer.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace ProjectPublicCollisionExportSurface

theorem public_kernel_not_hypothesis {Hypothesis : Prop}
    (inst : PublicCollisionInstantiation Hypothesis) :
    ¬ Hypothesis :=
  PublicCollisionExportSurface.not_hypothesis inst

theorem audit_public_api_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    False :=
  ProjectPublicCollisionTheoremIndex.audit_public_api_collision checklist hmain

theorem audit_public_gap_api_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    False :=
  ProjectPublicCollisionTheoremIndex.audit_public_gap_api_collision
    checklist hmain

theorem audit_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  ProjectPublicCollisionTheoremIndex.audit_not_main_rationality checklist

theorem audit_external_gap_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  ProjectPublicCollisionTheoremIndex.audit_external_gap_not_main_rationality
    checklist

theorem audit_nonempty_iff_bundle_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) :=
  ProjectPublicCollisionTheoremIndex.audit_nonempty_iff_bundle_nonempty

theorem audit_nonempty_iff_project_checklist_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
        MainRationality SondowAccepted bounds bound) :=
  ProjectPublicCollisionTheoremIndex.audit_nonempty_iff_project_checklist_nonempty

theorem audit_nonempty_to_public_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) :=
  ProjectPublicCollisionTheoremIndex.audit_nonempty_to_public_instantiation h

theorem bundle_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  ProjectPublicCollisionTheoremIndex.bundle_not_main_rationality bundle

theorem bundle_nonempty_to_external_gap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound)) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  ProjectPublicCollisionTheoremIndex.bundle_nonempty_to_external_gap h

theorem bundle_nonempty_to_public_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) :=
  ProjectPublicCollisionTheoremIndex.bundle_nonempty_to_public_instantiation h

theorem external_gap_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (h : HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound) :
    ¬ MainRationality :=
  ProjectPublicCollisionTheoremIndex.external_gap_not_main_rationality h

theorem audit_public_collision_coherent_with_bundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    checklist.toPublicCollisionInstantiation =
      checklist.bundle.toPublicCollisionInstantiation :=
  ProjectPublicCollisionTheoremIndex.audit_public_collision_coherent_with_bundle
    checklist

theorem audit_gap_collision_coherent_with_bundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    checklist.toPublicGapCollisionInstantiation =
      checklist.bundle.toPublicGapCollisionInstantiation :=
  ProjectPublicCollisionTheoremIndex.audit_gap_collision_coherent_with_bundle
    checklist

end ProjectPublicCollisionExportSurface
end BoundedProofPredicate
end BoundedArithmeticLab
