/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakVerifiedInstantiation

/-!
# Project-level public collision checklist

This module aggregates the project-level CnBox/Pudlak/Sondow collision routes
behind the public collision instantiation API.  The external gap criterion,
the budgeted assembly checklist, and the verified project instantiation
checklist all feed the same public contradiction schema.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

theorem externalGapCriterion_to_publicGapInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (h : HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) :=
  certificateBackedGapCriterion_nonempty_to_publicGapInstantiation_nonempty h

theorem externalGapCriterion_to_publicCollisionInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (h : HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound) :
    Nonempty (PublicCollisionInstantiation MainRationality) :=
  certificateBackedGapCriterion_nonempty_to_publicCollisionInstantiation_nonempty h

theorem externalGapCriterion_to_publicSeparatedInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (h : HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound) :
    Nonempty (PublicSeparatedCollisionInstantiation MainRationality) :=
  certificateBackedGapCriterion_nonempty_to_publicSeparatedInstantiation_nonempty h

theorem externalGapCriterion_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (h : HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound) :
    ¬ MainRationality := by
  rcases h with ⟨criterion⟩
  exact criterion.public_gap_instantiation_not_main_rationality

structure CnBoxPudlakProjectPublicCollisionChecklist
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  assembly : ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
    MainRationality SondowAccepted bounds bound

namespace CnBoxPudlakProjectPublicCollisionChecklist

def ofAssemblyChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (assembly : ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
      MainRationality SondowAccepted bounds bound) :
    CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound where
  assembly := assembly

def toAssemblyChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
      MainRationality SondowAccepted bounds bound :=
  checklist.assembly

def toVerifiedProjectInstantiationChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound where
  assembly := checklist.assembly

noncomputable def toCertificateBackedGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  checklist.assembly.toCertificateBackedGapCriterion

noncomputable def toPublicCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    PublicCollisionInstantiation MainRationality :=
  checklist.assembly.toPublicCollisionInstantiation

noncomputable def toPublicSeparatedCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    PublicSeparatedCollisionInstantiation MainRationality :=
  checklist.assembly.toPublicSeparatedCollisionInstantiation

noncomputable def toPublicGapCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    PublicGapCollisionInstantiation MainRationality :=
  checklist.assembly.toPublicGapCollisionInstantiation

def toExternalGapCriterionWitness
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  ⟨checklist.toCertificateBackedGapCriterion⟩

theorem assembly_route_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.assembly.public_instantiation_not_main_rationality

theorem gap_route_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.toCertificateBackedGapCriterion
    |>.public_gap_instantiation_not_main_rationality

theorem verified_route_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.toVerifiedProjectInstantiationChecklist
    |>.public_instantiation_not_main_rationality

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.assembly_route_not_main_rationality

theorem public_collision_instantiation_coherent_with_gap_route
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    checklist.toPublicCollisionInstantiation =
      checklist.toCertificateBackedGapCriterion.toPublicCollisionInstantiation :=
  checklist.assembly.public_collision_instantiation_coherent_with_gap_criterion

theorem public_gap_instantiation_coherent_with_gap_route
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    checklist.toPublicGapCollisionInstantiation =
      checklist.toCertificateBackedGapCriterion.toPublicGapCollisionInstantiation :=
  checklist.assembly.public_gap_instantiation_coherent_with_gap_criterion

end CnBoxPudlakProjectPublicCollisionChecklist

theorem projectPublicCollisionChecklist_nonempty_iff_assemblyChecklist_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨checklist.toAssemblyChecklist⟩
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨CnBoxPudlakProjectPublicCollisionChecklist.ofAssemblyChecklist
      assembly⟩

theorem projectPublicCollisionChecklist_nonempty_iff_verifiedInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakVerifiedProjectInstantiationChecklist
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨checklist.toVerifiedProjectInstantiationChecklist⟩
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨CnBoxPudlakProjectPublicCollisionChecklist.ofAssemblyChecklist
      checklist.toAssemblyChecklist⟩

theorem projectPublicCollisionChecklist_nonempty_to_externalGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound)) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound := by
  rcases h with ⟨checklist⟩
  exact checklist.toExternalGapCriterionWitness

theorem projectPublicCollisionChecklist_nonempty_to_publicCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) := by
  rcases h with ⟨checklist⟩
  exact ⟨checklist.toPublicCollisionInstantiation⟩

theorem projectPublicCollisionChecklist_nonempty_to_publicSeparatedInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicSeparatedCollisionInstantiation MainRationality) := by
  rcases h with ⟨checklist⟩
  exact ⟨checklist.toPublicSeparatedCollisionInstantiation⟩

theorem projectPublicCollisionChecklist_nonempty_to_publicGapInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) := by
  rcases h with ⟨checklist⟩
  exact ⟨checklist.toPublicGapCollisionInstantiation⟩

theorem projectPublicCollisionChecklist_nonempty_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound)) :
    ¬ MainRationality := by
  rcases h with ⟨checklist⟩
  exact checklist.not_main_rationality

end BoundedProofPredicate
end BoundedArithmeticLab
