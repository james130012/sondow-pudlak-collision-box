/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CertificateBackedCollisionKernel

/-!
# Paper-ready public collision theorem layer

This module provides paper-facing theorem names and checklists over the
project-agnostic certificate-backed collision kernel.  It contains no
CnBox/Sondow/Pudlak-specific assumptions.
-/

namespace BoundedArithmeticLab

structure PublicCollisionChecklist where
  box : AbstractProofLengthBox
  accepted : Nat → Prop
  acceptance : EventualAcceptanceUnderRationality accepted
  short_upper : EventualShortProofUpperBound box accepted
  lower_bound : EventualLowerBound box

def PublicCollisionChecklist.toKernel
    (checklist : PublicCollisionChecklist) :
    CertificateBackedCollisionKernel where
  box := checklist.box
  accepted := checklist.accepted
  acceptance := checklist.acceptance
  short_upper := checklist.short_upper
  lower_bound := checklist.lower_bound

def CertificateBackedCollisionKernel.toPublicCollisionChecklist
    (kernel : CertificateBackedCollisionKernel) :
    PublicCollisionChecklist where
  box := kernel.box
  accepted := kernel.accepted
  acceptance := kernel.acceptance
  short_upper := kernel.short_upper
  lower_bound := kernel.lower_bound

theorem publicCollisionChecklist_nonempty_iff_kernel_nonempty :
    Nonempty PublicCollisionChecklist ↔
      Nonempty CertificateBackedCollisionKernel := by
  constructor
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨checklist.toKernel⟩
  · intro h
    rcases h with ⟨kernel⟩
    exact ⟨kernel.toPublicCollisionChecklist⟩

theorem public_collision_theorem
    (checklist : PublicCollisionChecklist) :
    False :=
  checklist.toKernel.collision

structure PublicGapCollisionChecklist where
  box : AbstractProofLengthBox
  accepted : Nat → Prop
  acceptance : EventualAcceptanceUnderRationality accepted
  short_upper : EventualShortProofUpperBound box accepted
  lower_gap : GenericProofLengthGap box

noncomputable def PublicGapCollisionChecklist.toGapCriterion
    (checklist : PublicGapCollisionChecklist) :
    CertificateBackedGapCriterion where
  box := checklist.box
  accepted := checklist.accepted
  acceptance := checklist.acceptance
  short_upper := checklist.short_upper
  lower_gap := checklist.lower_gap

def CertificateBackedGapCriterion.toPublicGapCollisionChecklist
    (criterion : CertificateBackedGapCriterion) :
    PublicGapCollisionChecklist where
  box := criterion.box
  accepted := criterion.accepted
  acceptance := criterion.acceptance
  short_upper := criterion.short_upper
  lower_gap := criterion.lower_gap

theorem publicGapCollisionChecklist_nonempty_iff_gapCriterion_nonempty :
    Nonempty PublicGapCollisionChecklist ↔
      Nonempty CertificateBackedGapCriterion := by
  constructor
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨checklist.toGapCriterion⟩
  · intro h
    rcases h with ⟨criterion⟩
    exact ⟨criterion.toPublicGapCollisionChecklist⟩

noncomputable def PublicGapCollisionChecklist.toPublicCollisionChecklist
    (checklist : PublicGapCollisionChecklist) :
    PublicCollisionChecklist where
  box := checklist.box
  accepted := checklist.accepted
  acceptance := checklist.acceptance
  short_upper := checklist.short_upper
  lower_bound :=
    (genericProofLengthGap_iff_eventualLowerBound checklist.box).1
      checklist.lower_gap

def PublicCollisionChecklist.toPublicGapCollisionChecklist
    (checklist : PublicCollisionChecklist) :
    PublicGapCollisionChecklist where
  box := checklist.box
  accepted := checklist.accepted
  acceptance := checklist.acceptance
  short_upper := checklist.short_upper
  lower_gap :=
    (genericProofLengthGap_iff_eventualLowerBound checklist.box).2
      checklist.lower_bound

theorem publicGapCollisionChecklist_nonempty_iff_publicCollisionChecklist_nonempty :
    Nonempty PublicGapCollisionChecklist ↔
      Nonempty PublicCollisionChecklist := by
  constructor
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨checklist.toPublicCollisionChecklist⟩
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨checklist.toPublicGapCollisionChecklist⟩

theorem public_gap_collision_theorem
    (checklist : PublicGapCollisionChecklist) :
    False :=
  checklist.toGapCriterion.collision

end BoundedArithmeticLab
