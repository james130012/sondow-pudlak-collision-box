/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.PublicCollisionCertificates
import BoundedArithmeticLab.CnBoxPudlakPublicKernelAdapter

/-!
# Paper-facing CnBox/Pudlak collision theorem adapters

This module gives stable theorem names for citing the CnBox/Pudlak/Sondow
route through the public collision theorem layer.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

namespace ProjectLevelCnBoxCertificateBackedGapCriterion

noncomputable def toPublicGapCollisionChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    PublicGapCollisionChecklist :=
  (criterion.toGenericGapCriterion hmain).toPublicGapCollisionChecklist

noncomputable def toPublicCollisionChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    PublicCollisionChecklist :=
  (criterion.toPublicGapCollisionChecklist hmain).toPublicCollisionChecklist

noncomputable def toPublicSeparatedCollisionChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    PublicSeparatedCollisionChecklist :=
  (criterion.toPublicCollisionChecklist hmain).toSeparatedCollisionChecklist

theorem paper_ready_public_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    False :=
  public_collision_theorem (criterion.toPublicCollisionChecklist hmain)

theorem paper_ready_public_separated_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    False :=
  public_separated_collision_theorem
    (criterion.toPublicSeparatedCollisionChecklist hmain)

theorem paper_ready_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    ¬ MainRationality := by
  intro hmain
  exact criterion.paper_ready_public_collision hmain

end ProjectLevelCnBoxCertificateBackedGapCriterion

namespace CnBoxPudlakPublicKernelAdapterChecklist

noncomputable def toPublicCollisionChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      CnBoxPudlakPublicKernelAdapterChecklist
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    PublicCollisionChecklist :=
  checklist.criterion.toPublicCollisionChecklist hmain

noncomputable def toPublicSeparatedCollisionChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      CnBoxPudlakPublicKernelAdapterChecklist
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    PublicSeparatedCollisionChecklist :=
  checklist.criterion.toPublicSeparatedCollisionChecklist hmain

theorem paper_ready_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      CnBoxPudlakPublicKernelAdapterChecklist
        MainRationality SondowAccepted bound) :
    ¬ MainRationality :=
  checklist.criterion.paper_ready_not_main_rationality

end CnBoxPudlakPublicKernelAdapterChecklist

namespace ProjectLevelCnBoxSondowBudgetedAssemblyChecklist

noncomputable def toPaperReadyPublicCollisionChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    PublicCollisionChecklist :=
  checklist.toCertificateBackedGapCriterion.toPublicCollisionChecklist hmain

noncomputable def toPaperReadyPublicSeparatedCollisionChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound)
    (hmain : MainRationality) :
    PublicSeparatedCollisionChecklist :=
  checklist.toCertificateBackedGapCriterion
    |>.toPublicSeparatedCollisionChecklist hmain

theorem paper_ready_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.toCertificateBackedGapCriterion.paper_ready_not_main_rationality

end ProjectLevelCnBoxSondowBudgetedAssemblyChecklist

end BoundedProofPredicate
end BoundedArithmeticLab
