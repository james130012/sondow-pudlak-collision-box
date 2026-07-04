/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.PublicCollisionCertificates

/-!
# Public collision API

This module is a small facade over the public collision kernel.  It gives
stable paper/open-source names for the generic kernel, checklist, and
certificate layers without adding any CnBox/Sondow/Pudlak-specific data.
-/

namespace BoundedArithmeticLab

namespace PublicCollisionAPI

abbrev Box := AbstractProofLengthBox
abbrev Kernel := CertificateBackedCollisionKernel
abbrev Checklist := PublicCollisionChecklist
abbrev GapChecklist := PublicGapCollisionChecklist
abbrev SeparatedChecklist := PublicSeparatedCollisionChecklist

abbrev UpperCertificate
    (box : AbstractProofLengthBox) (accepted : Nat → Prop) :=
  PublicUpperCertificate box accepted

abbrev LowerCertificate (box : AbstractProofLengthBox) :=
  PublicLowerCertificate box

abbrev GapLowerCertificate (box : AbstractProofLengthBox) :=
  PublicGapLowerCertificate box

theorem collision_from_kernel (kernel : Kernel) : False :=
  kernel.collision

theorem collision_from_checklist (checklist : Checklist) : False :=
  public_collision_theorem checklist

theorem collision_from_gap_checklist (checklist : GapChecklist) : False :=
  public_gap_collision_theorem checklist

theorem collision_from_separated_checklist
    (checklist : SeparatedChecklist) : False :=
  public_separated_collision_theorem checklist

theorem checklist_nonempty_iff_kernel_nonempty :
    Nonempty Checklist ↔ Nonempty Kernel :=
  publicCollisionChecklist_nonempty_iff_kernel_nonempty

theorem gap_checklist_nonempty_iff_checklist_nonempty :
    Nonempty GapChecklist ↔ Nonempty Checklist :=
  publicGapCollisionChecklist_nonempty_iff_publicCollisionChecklist_nonempty

theorem separated_checklist_nonempty_iff_checklist_nonempty :
    Nonempty SeparatedChecklist ↔ Nonempty Checklist :=
  publicSeparatedCollisionChecklist_nonempty_iff_publicCollisionChecklist_nonempty

theorem gap_lower_certificate_nonempty_iff_lower_certificate_nonempty
    {box : Box} :
    Nonempty (GapLowerCertificate box) ↔
      Nonempty (LowerCertificate box) :=
  publicGapLowerCertificate_nonempty_iff_lowerCertificate_nonempty

end PublicCollisionAPI

end BoundedArithmeticLab
