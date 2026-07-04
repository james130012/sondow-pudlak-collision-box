/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectCertificateBundle

/-!
# Project public collision audit checklist

This module provides the audit-facing final wrapper for the project-level
public collision route.  It exposes direct links to the public collision API,
the project certificate bundle, and the external gap route.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure ProjectPublicCollisionAuditChecklist
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  bundle : ProjectPublicCollisionCertificateBundle
    MainRationality SondowAccepted bounds bound

namespace ProjectPublicCollisionAuditChecklist

def ofCertificateBundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound where
  bundle := bundle

def toCertificateBundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound :=
  checklist.bundle

noncomputable def toProjectPublicCollisionChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound :=
  checklist.bundle.toProjectPublicCollisionChecklist

noncomputable def toExternalGapCriterionWitness
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  checklist.bundle.toExternalGapCriterionWitness

noncomputable def toPublicCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    PublicCollisionInstantiation MainRationality :=
  checklist.bundle.toPublicCollisionInstantiation

noncomputable def toPublicSeparatedCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    PublicSeparatedCollisionInstantiation MainRationality :=
  checklist.bundle.toPublicSeparatedCollisionInstantiation

noncomputable def toPublicGapCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    PublicGapCollisionInstantiation MainRationality :=
  checklist.bundle.toPublicGapCollisionInstantiation

theorem public_api_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    False :=
  checklist.toPublicCollisionInstantiation.collision hmain

theorem public_gap_api_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    False :=
  checklist.toPublicGapCollisionInstantiation.collision hmain

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.bundle.not_main_rationality

theorem public_api_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.toPublicCollisionInstantiation.not_hypothesis

theorem external_gap_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  externalGapCriterion_not_main_rationality
    checklist.toExternalGapCriterionWitness

theorem public_collision_instantiation_coherent_with_bundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    checklist.toPublicCollisionInstantiation =
      checklist.bundle.toPublicCollisionInstantiation :=
  rfl

theorem public_gap_instantiation_coherent_with_bundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    checklist.toPublicGapCollisionInstantiation =
      checklist.bundle.toPublicGapCollisionInstantiation :=
  rfl

end ProjectPublicCollisionAuditChecklist

theorem projectPublicCollisionAuditChecklist_nonempty_iff_bundle_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨checklist.toCertificateBundle⟩
  · intro h
    rcases h with ⟨bundle⟩
    exact ⟨ProjectPublicCollisionAuditChecklist.ofCertificateBundle
      bundle⟩

theorem projectPublicCollisionAuditChecklist_nonempty_iff_projectChecklist_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
        MainRationality SondowAccepted bounds bound) := by
  exact projectPublicCollisionAuditChecklist_nonempty_iff_bundle_nonempty.trans
    projectPublicCollisionCertificateBundle_nonempty_iff_projectChecklist_nonempty

theorem projectPublicCollisionAuditChecklist_nonempty_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound)) :
    ¬ MainRationality := by
  rcases h with ⟨checklist⟩
  exact checklist.not_main_rationality

theorem projectPublicCollisionAuditChecklist_nonempty_to_publicInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) := by
  rcases h with ⟨checklist⟩
  exact ⟨checklist.toPublicCollisionInstantiation⟩

end BoundedProofPredicate
end BoundedArithmeticLab
