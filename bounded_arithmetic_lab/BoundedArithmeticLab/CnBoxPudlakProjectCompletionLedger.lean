/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectExportSurface

/-!
# CnBox/Pudlak project completion ledger

This module records the project-level completion obligation for the public
collision route.  It separates the verified interface conversions from the
remaining obligation to supply an actual project certificate bundle.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure ProjectPublicCollisionCompletionLedger
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  audit : ProjectPublicCollisionAuditChecklist
    MainRationality SondowAccepted bounds bound

namespace ProjectPublicCollisionCompletionLedger

def ofAuditChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (audit : ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound) :
    ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound where
  audit := audit

def toAuditChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (ledger : ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) :
    ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound :=
  ledger.audit

def toCertificateBundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (ledger : ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) :
    ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound :=
  ledger.audit.toCertificateBundle

noncomputable def toProjectPublicCollisionChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (ledger : ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) :
    CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound :=
  ledger.audit.toProjectPublicCollisionChecklist

noncomputable def toVerifiedProjectInstantiationChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (ledger : ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) :
    CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound :=
  ledger.toCertificateBundle.toVerifiedProjectInstantiationChecklist

noncomputable def toExternalGapCriterionWitness
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (ledger : ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  ledger.audit.toExternalGapCriterionWitness

noncomputable def toPublicCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (ledger : ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) :
    PublicCollisionInstantiation MainRationality :=
  ledger.audit.toPublicCollisionInstantiation

noncomputable def toPublicSeparatedCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (ledger : ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) :
    PublicSeparatedCollisionInstantiation MainRationality :=
  ledger.audit.toPublicSeparatedCollisionInstantiation

noncomputable def toPublicGapCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (ledger : ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) :
    PublicGapCollisionInstantiation MainRationality :=
  ledger.audit.toPublicGapCollisionInstantiation

theorem public_api_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (ledger : ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    False :=
  ledger.audit.public_api_collision hmain

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (ledger : ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  ledger.audit.not_main_rationality

theorem external_gap_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (ledger : ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  ledger.audit.external_gap_not_main_rationality

theorem public_instantiation_coherent_with_audit
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (ledger : ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) :
    ledger.toPublicCollisionInstantiation =
      ledger.audit.toPublicCollisionInstantiation :=
  rfl

theorem gap_instantiation_coherent_with_audit
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (ledger : ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) :
    ledger.toPublicGapCollisionInstantiation =
      ledger.audit.toPublicGapCollisionInstantiation :=
  rfl

end ProjectPublicCollisionCompletionLedger

abbrev ProjectPublicCollisionCompletionObligation
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  Nonempty (ProjectPublicCollisionCompletionLedger
    MainRationality SondowAccepted bounds bound)

theorem projectPublicCollisionCompletionLedger_nonempty_iff_auditChecklist_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectPublicCollisionAuditChecklist
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨ledger⟩
    exact ⟨ledger.toAuditChecklist⟩
  · intro h
    rcases h with ⟨audit⟩
    exact ⟨ProjectPublicCollisionCompletionLedger.ofAuditChecklist
      audit⟩

theorem projectPublicCollisionCompletionLedger_nonempty_iff_bundle_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) := by
  exact projectPublicCollisionCompletionLedger_nonempty_iff_auditChecklist_nonempty.trans
    projectPublicCollisionAuditChecklist_nonempty_iff_bundle_nonempty

theorem projectPublicCollisionCompletionLedger_nonempty_iff_projectChecklist_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
        MainRationality SondowAccepted bounds bound) := by
  exact projectPublicCollisionCompletionLedger_nonempty_iff_bundle_nonempty.trans
    projectPublicCollisionCertificateBundle_nonempty_iff_projectChecklist_nonempty

theorem projectPublicCollisionCompletionLedger_nonempty_iff_verifiedInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakVerifiedProjectInstantiationChecklist
        MainRationality SondowAccepted bounds bound) := by
  exact projectPublicCollisionCompletionLedger_nonempty_iff_bundle_nonempty.trans
    projectPublicCollisionCertificateBundle_nonempty_iff_verifiedInstantiation_nonempty

theorem projectPublicCollisionCompletionLedger_nonempty_to_externalGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound)) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound := by
  rcases h with ⟨ledger⟩
  exact ledger.toExternalGapCriterionWitness

theorem projectPublicCollisionCompletionLedger_nonempty_to_publicInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) := by
  rcases h with ⟨ledger⟩
  exact ⟨ledger.toPublicCollisionInstantiation⟩

theorem projectPublicCollisionCompletionLedger_nonempty_to_publicGapInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) := by
  rcases h with ⟨ledger⟩
  exact ⟨ledger.toPublicGapCollisionInstantiation⟩

theorem projectPublicCollisionCompletionLedger_nonempty_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound)) :
    ¬ MainRationality := by
  rcases h with ⟨ledger⟩
  exact ledger.not_main_rationality

theorem projectPublicCollisionCompletionObligation_iff_bundle_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) :=
  projectPublicCollisionCompletionLedger_nonempty_iff_bundle_nonempty

end BoundedProofPredicate
end BoundedArithmeticLab
