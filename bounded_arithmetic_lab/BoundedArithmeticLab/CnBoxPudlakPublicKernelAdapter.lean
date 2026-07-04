/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CertificateBackedCollisionKernel
import BoundedArithmeticLab.CnBoxPudlakAssemblyBudget

/-!
# CnBox/Pudlak adapter for the public collision kernel

This module adapts the CnBox/Pudlak/Sondow project-level checklist to the
project-agnostic certificate-backed collision kernel.  The adapter preserves
the CnBox-specific criterion as a field, so the public kernel projection does
not weaken or erase the relabeling and length-calibration obligations.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

namespace ProjectLevelCnBoxCertificateBackedGapCriterion

noncomputable def toGenericGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    CertificateBackedGapCriterion where
  box := canonicalCnBoxPABox
  accepted := CanonicalProofCertificateAccepted bound
  acceptance :=
    EventualAcceptanceUnderRationality.ofMainAccepted
      hmain criterion.canonicalAcceptance
  short_upper :=
    (canonicalProofCertificateShortUpper criterion.bound_poly).toShortUpper
  lower_gap :=
    (genericProofLengthGap_iff_eventualLowerBound canonicalCnBoxPABox).2
      criterion.lowerBound

noncomputable def toGenericKernel
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    CertificateBackedCollisionKernel :=
  (criterion.toGenericGapCriterion hmain).toKernel

theorem generic_collision
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    False :=
  (criterion.toGenericKernel hmain).collision

theorem not_main_rationality_viaGenericKernel
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    ¬ MainRationality := by
  intro hmain
  exact criterion.generic_collision hmain

end ProjectLevelCnBoxCertificateBackedGapCriterion

structure CnBoxPudlakPublicKernelAdapterChecklist
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bound : Nat → Real) where
  criterion :
    ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound

namespace CnBoxPudlakPublicKernelAdapterChecklist

def ofCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    CnBoxPudlakPublicKernelAdapterChecklist
      MainRationality SondowAccepted bound where
  criterion := criterion

def toCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      CnBoxPudlakPublicKernelAdapterChecklist
        MainRationality SondowAccepted bound) :
    ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  checklist.criterion

noncomputable def toGenericKernel
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      CnBoxPudlakPublicKernelAdapterChecklist
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    CertificateBackedCollisionKernel :=
  checklist.criterion.toGenericKernel hmain

end CnBoxPudlakPublicKernelAdapterChecklist

theorem cnBoxPudlakPublicKernelAdapterChecklist_nonempty_iff_criterion_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real} :
    Nonempty
      (CnBoxPudlakPublicKernelAdapterChecklist
        MainRationality SondowAccepted bound) ↔
      Nonempty
        (ProjectLevelCnBoxCertificateBackedGapCriterion
          MainRationality SondowAccepted bound) := by
  constructor
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨checklist.toCriterion⟩
  · intro h
    rcases h with ⟨criterion⟩
    exact ⟨CnBoxPudlakPublicKernelAdapterChecklist.ofCriterion
      criterion⟩

namespace ProjectLevelCnBoxSondowBudgetedAssemblyChecklist

noncomputable def toPublicKernelAdapterChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    CnBoxPudlakPublicKernelAdapterChecklist
      MainRationality SondowAccepted bound where
  criterion := checklist.toCertificateBackedGapCriterion

end ProjectLevelCnBoxSondowBudgetedAssemblyChecklist

end BoundedProofPredicate
end BoundedArithmeticLab
