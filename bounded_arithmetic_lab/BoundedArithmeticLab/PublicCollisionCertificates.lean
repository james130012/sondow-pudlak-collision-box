/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.PublicCollisionTheoremLayer

/-!
# Public collision certificates

This module splits the paper-facing collision checklist into separate upper
and lower certificates.  It is project-agnostic and can be used as an
open-source API layer over the public collision theorem.
-/

namespace BoundedArithmeticLab

structure PublicUpperCertificate
    (box : AbstractProofLengthBox) (accepted : Nat → Prop) where
  acceptance : EventualAcceptanceUnderRationality accepted
  short_upper : EventualShortProofUpperBound box accepted

structure PublicLowerCertificate (box : AbstractProofLengthBox) where
  lower_bound : EventualLowerBound box

structure PublicGapLowerCertificate (box : AbstractProofLengthBox) where
  lower_gap : GenericProofLengthGap box

noncomputable def PublicGapLowerCertificate.toLowerCertificate
    {box : AbstractProofLengthBox}
    (cert : PublicGapLowerCertificate box) :
    PublicLowerCertificate box where
  lower_bound :=
    (genericProofLengthGap_iff_eventualLowerBound box).1 cert.lower_gap

def PublicLowerCertificate.toGapLowerCertificate
    {box : AbstractProofLengthBox}
    (cert : PublicLowerCertificate box) :
    PublicGapLowerCertificate box where
  lower_gap :=
    (genericProofLengthGap_iff_eventualLowerBound box).2 cert.lower_bound

theorem publicGapLowerCertificate_nonempty_iff_lowerCertificate_nonempty
    {box : AbstractProofLengthBox} :
    Nonempty (PublicGapLowerCertificate box) ↔
      Nonempty (PublicLowerCertificate box) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toLowerCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toGapLowerCertificate⟩

structure PublicSeparatedCollisionChecklist where
  box : AbstractProofLengthBox
  accepted : Nat → Prop
  upper : PublicUpperCertificate box accepted
  lower : PublicLowerCertificate box

def PublicSeparatedCollisionChecklist.toPublicCollisionChecklist
    (checklist : PublicSeparatedCollisionChecklist) :
    PublicCollisionChecklist where
  box := checklist.box
  accepted := checklist.accepted
  acceptance := checklist.upper.acceptance
  short_upper := checklist.upper.short_upper
  lower_bound := checklist.lower.lower_bound

def PublicCollisionChecklist.toSeparatedCollisionChecklist
    (checklist : PublicCollisionChecklist) :
    PublicSeparatedCollisionChecklist where
  box := checklist.box
  accepted := checklist.accepted
  upper := {
    acceptance := checklist.acceptance
    short_upper := checklist.short_upper }
  lower := {
    lower_bound := checklist.lower_bound }

theorem
    publicSeparatedCollisionChecklist_nonempty_iff_publicCollisionChecklist_nonempty :
    Nonempty PublicSeparatedCollisionChecklist ↔
      Nonempty PublicCollisionChecklist := by
  constructor
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨checklist.toPublicCollisionChecklist⟩
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨checklist.toSeparatedCollisionChecklist⟩

theorem public_separated_collision_theorem
    (checklist : PublicSeparatedCollisionChecklist) :
    False :=
  public_collision_theorem checklist.toPublicCollisionChecklist

end BoundedArithmeticLab
