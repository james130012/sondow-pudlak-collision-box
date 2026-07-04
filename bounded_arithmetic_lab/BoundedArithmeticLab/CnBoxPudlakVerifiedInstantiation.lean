/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.PublicCollisionInstantiation
import BoundedArithmeticLab.CnBoxPudlakPaperCollision

/-!
# Verified project instantiation of the public collision API

This module is project-specific glue.  It records that the project-level
CnBox/Pudlak/Sondow budgeted assembly checklist instantiates the public
collision API without changing the public theorem statement.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

namespace ProjectLevelCnBoxCertificateBackedGapCriterion

noncomputable def toPublicGapCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    PublicGapCollisionInstantiation MainRationality where
  checklist := fun hmain => criterion.toPublicGapCollisionChecklist hmain

noncomputable def toPublicCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    PublicCollisionInstantiation MainRationality where
  checklist := fun hmain => criterion.toPublicCollisionChecklist hmain

noncomputable def toPublicSeparatedCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    PublicSeparatedCollisionInstantiation MainRationality where
  checklist := fun hmain => criterion.toPublicSeparatedCollisionChecklist hmain

theorem public_gap_instantiation_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    ¬ MainRationality :=
  criterion.toPublicGapCollisionInstantiation.not_hypothesis

theorem public_instantiation_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    ¬ MainRationality :=
  criterion.toPublicCollisionInstantiation.not_hypothesis

theorem public_separated_instantiation_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    ¬ MainRationality :=
  criterion.toPublicSeparatedCollisionInstantiation.not_hypothesis

end ProjectLevelCnBoxCertificateBackedGapCriterion

namespace ProjectLevelCnBoxSondowBudgetedAssemblyChecklist

noncomputable def toPublicCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    PublicCollisionInstantiation MainRationality where
  checklist := fun hmain =>
    checklist.toPaperReadyPublicCollisionChecklist hmain

noncomputable def toPublicSeparatedCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    PublicSeparatedCollisionInstantiation MainRationality where
  checklist := fun hmain =>
    checklist.toPaperReadyPublicSeparatedCollisionChecklist hmain

noncomputable def toPublicGapCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    PublicGapCollisionInstantiation MainRationality :=
  checklist.toCertificateBackedGapCriterion.toPublicGapCollisionInstantiation

theorem public_instantiation_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.toPublicCollisionInstantiation.not_hypothesis

theorem public_separated_instantiation_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.toPublicSeparatedCollisionInstantiation.not_hypothesis

theorem public_gap_instantiation_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.toPublicGapCollisionInstantiation.not_hypothesis

theorem public_collision_instantiation_coherent_with_gap_criterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    checklist.toPublicCollisionInstantiation =
      checklist.toCertificateBackedGapCriterion.toPublicCollisionInstantiation :=
  rfl

theorem public_separated_instantiation_coherent_with_gap_criterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    checklist.toPublicSeparatedCollisionInstantiation =
      (checklist.toCertificateBackedGapCriterion).toPublicSeparatedCollisionInstantiation :=
  rfl

theorem public_gap_instantiation_coherent_with_gap_criterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    checklist.toPublicGapCollisionInstantiation =
      checklist.toCertificateBackedGapCriterion.toPublicGapCollisionInstantiation :=
  rfl

end ProjectLevelCnBoxSondowBudgetedAssemblyChecklist

structure CnBoxPudlakVerifiedProjectInstantiationChecklist
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  assembly : ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
    MainRationality SondowAccepted bounds bound

namespace CnBoxPudlakVerifiedProjectInstantiationChecklist

def ofAssemblyChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
      MainRationality SondowAccepted bounds bound) :
    CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound where
  assembly := checklist

def toAssemblyChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
      MainRationality SondowAccepted bounds bound :=
  checklist.assembly

noncomputable def toPublicCollisionChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    PublicCollisionAPI.Checklist :=
  checklist.assembly.toPaperReadyPublicCollisionChecklist hmain

noncomputable def toPublicSeparatedChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    PublicCollisionAPI.SeparatedChecklist :=
  checklist.assembly.toPaperReadyPublicSeparatedCollisionChecklist hmain

noncomputable def toPublicCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound) :
    PublicCollisionInstantiation MainRationality where
  checklist := fun hmain => checklist.toPublicCollisionChecklist hmain

noncomputable def toPublicSeparatedCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound) :
    PublicSeparatedCollisionInstantiation MainRationality where
  checklist := fun hmain => checklist.toPublicSeparatedChecklist hmain

theorem public_api_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    False :=
  PublicCollisionAPI.collision_from_checklist
    (checklist.toPublicCollisionChecklist hmain)

theorem public_api_separated_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    False :=
  PublicCollisionAPI.collision_from_separated_checklist
    (checklist.toPublicSeparatedChecklist hmain)

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality := by
  intro hmain
  exact checklist.public_api_collision hmain

theorem public_instantiation_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.toPublicCollisionInstantiation.not_hypothesis

theorem public_separated_instantiation_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.toPublicSeparatedCollisionInstantiation.not_hypothesis

end CnBoxPudlakVerifiedProjectInstantiationChecklist

theorem verifiedProjectInstantiation_nonempty_iff_assemblyChecklist_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨checklist.toAssemblyChecklist⟩
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨CnBoxPudlakVerifiedProjectInstantiationChecklist.ofAssemblyChecklist
      checklist⟩

theorem assemblyChecklist_nonempty_to_publicCollisionInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) := by
  rcases h with ⟨checklist⟩
  exact ⟨checklist.toPublicCollisionInstantiation⟩

theorem assemblyChecklist_nonempty_to_publicSeparatedInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicSeparatedCollisionInstantiation MainRationality) := by
  rcases h with ⟨checklist⟩
  exact ⟨checklist.toPublicSeparatedCollisionInstantiation⟩

theorem assemblyChecklist_nonempty_to_publicGapInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) := by
  rcases h with ⟨checklist⟩
  exact ⟨checklist.toPublicGapCollisionInstantiation⟩

theorem verifiedProjectInstantiation_nonempty_to_publicCollisionInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) := by
  rcases h with ⟨checklist⟩
  exact ⟨checklist.toPublicCollisionInstantiation⟩

theorem verifiedProjectInstantiation_nonempty_to_publicSeparatedInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicSeparatedCollisionInstantiation MainRationality) := by
  rcases h with ⟨checklist⟩
  exact ⟨checklist.toPublicSeparatedCollisionInstantiation⟩

theorem verifiedProjectInstantiation_nonempty_to_publicGapInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) := by
  rcases h with ⟨checklist⟩
  exact ⟨checklist.toAssemblyChecklist.toPublicGapCollisionInstantiation⟩

theorem certificateBackedGapCriterion_nonempty_to_publicGapInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (h : Nonempty (ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) := by
  rcases h with ⟨criterion⟩
  exact ⟨criterion.toPublicGapCollisionInstantiation⟩

theorem certificateBackedGapCriterion_nonempty_to_publicCollisionInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (h : Nonempty (ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) := by
  rcases h with ⟨criterion⟩
  exact ⟨criterion.toPublicCollisionInstantiation⟩

theorem certificateBackedGapCriterion_nonempty_to_publicSeparatedInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (h : Nonempty (ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)) :
    Nonempty (PublicSeparatedCollisionInstantiation MainRationality) := by
  rcases h with ⟨criterion⟩
  exact ⟨criterion.toPublicSeparatedCollisionInstantiation⟩

end BoundedProofPredicate
end BoundedArithmeticLab
