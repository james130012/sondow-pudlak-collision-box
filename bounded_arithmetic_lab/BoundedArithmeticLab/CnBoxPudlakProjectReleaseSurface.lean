/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectCompletionLedger

/-!
# CnBox/Pudlak project release surface

This module exposes the final project-facing theorem names for the public
collision route.  It keeps the completion obligation equivalent to the
certificate bundle and verified project instantiation checklists.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace ProjectPublicCollisionReleaseSurface

theorem completion_obligation_iff_bundle_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) :=
  projectPublicCollisionCompletionObligation_iff_bundle_nonempty

theorem completion_obligation_iff_verified_instantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound ↔
      Nonempty (CnBoxPudlakVerifiedProjectInstantiationChecklist
        MainRationality SondowAccepted bounds bound) :=
  projectPublicCollisionCompletionLedger_nonempty_iff_verifiedInstantiation_nonempty

theorem completion_obligation_iff_project_checklist_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound ↔
      Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
        MainRationality SondowAccepted bounds bound) :=
  projectPublicCollisionCompletionLedger_nonempty_iff_projectChecklist_nonempty

theorem completion_obligation_to_external_gap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  projectPublicCollisionCompletionLedger_nonempty_to_externalGapCriterion h

theorem completion_obligation_to_public_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound) :
    Nonempty (PublicCollisionInstantiation MainRationality) :=
  projectPublicCollisionCompletionLedger_nonempty_to_publicInstantiation h

theorem completion_obligation_to_public_gap_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) :=
  projectPublicCollisionCompletionLedger_nonempty_to_publicGapInstantiation h

theorem completion_obligation_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  projectPublicCollisionCompletionLedger_nonempty_not_main_rationality h

theorem completion_obligation_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    False :=
  completion_obligation_not_main_rationality h hmain

end ProjectPublicCollisionReleaseSurface
end BoundedProofPredicate
end BoundedArithmeticLab
