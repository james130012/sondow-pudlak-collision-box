/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.PudlakInterface

/-!
# Certificate-backed collision kernel

This module is the project-agnostic collision kernel.  It packages an eventual
acceptance certificate, a short-proof upper certificate, and a lower-bound gap
certificate over the same `AbstractProofLengthBox`.
-/

namespace BoundedArithmeticLab

structure CertificateBackedCollisionKernel where
  box : AbstractProofLengthBox
  accepted : Nat → Prop
  acceptance : EventualAcceptanceUnderRationality accepted
  short_upper : EventualShortProofUpperBound box accepted
  lower_bound : EventualLowerBound box

theorem CertificateBackedCollisionKernel.collision
    (kernel : CertificateBackedCollisionKernel) :
    False :=
  eventualCollision kernel.acceptance kernel.short_upper kernel.lower_bound

structure GenericProofLengthGapWitness
    (box : AbstractProofLengthBox) (f : Nat → Real) (N : Nat) where
  n : Nat
  n_ge : N ≤ n
  gap_pos : box.length n > f n

def GenericHasProofLengthGapWitness
    (box : AbstractProofLengthBox) (f : Nat → Real) (N : Nat) : Prop :=
  Nonempty (GenericProofLengthGapWitness box f N)

def GenericProofLengthGap (box : AbstractProofLengthBox) : Prop :=
  ∀ f : Nat → Real, IsPolynomialBound f →
    ∀ N : Nat, GenericHasProofLengthGapWitness box f N

theorem genericProofLengthGap_iff_eventualLowerBound
    (box : AbstractProofLengthBox) :
    GenericProofLengthGap box ↔ EventualLowerBound box := by
  constructor
  · intro hgap
    exact {
      lower_bound := by
        intro f hf N
        rcases hgap f hf N with ⟨witness⟩
        exact ⟨witness.n, witness.n_ge, witness.gap_pos⟩ }
  · intro hlower f hf N
    rcases hlower.lower_bound f hf N with ⟨n, hn, hgt⟩
    exact ⟨{ n := n, n_ge := hn, gap_pos := hgt }⟩

structure CertificateBackedGapCriterion where
  box : AbstractProofLengthBox
  accepted : Nat → Prop
  acceptance : EventualAcceptanceUnderRationality accepted
  short_upper : EventualShortProofUpperBound box accepted
  lower_gap : GenericProofLengthGap box

theorem CertificateBackedGapCriterion.same_formula
    (criterion : CertificateBackedGapCriterion) :
    criterion.box.formula = criterion.box.formula :=
  rfl

theorem CertificateBackedGapCriterion.same_length
    (criterion : CertificateBackedGapCriterion) :
    criterion.box.length = criterion.box.length :=
  rfl

noncomputable def CertificateBackedGapCriterion.lowerBound
    (criterion : CertificateBackedGapCriterion) :
    EventualLowerBound criterion.box :=
  (genericProofLengthGap_iff_eventualLowerBound criterion.box).1
    criterion.lower_gap

noncomputable def CertificateBackedGapCriterion.toKernel
    (criterion : CertificateBackedGapCriterion) :
    CertificateBackedCollisionKernel where
  box := criterion.box
  accepted := criterion.accepted
  acceptance := criterion.acceptance
  short_upper := criterion.short_upper
  lower_bound := criterion.lowerBound

def CertificateBackedCollisionKernel.toGapCriterion
    (kernel : CertificateBackedCollisionKernel) :
    CertificateBackedGapCriterion where
  box := kernel.box
  accepted := kernel.accepted
  acceptance := kernel.acceptance
  short_upper := kernel.short_upper
  lower_gap :=
    (genericProofLengthGap_iff_eventualLowerBound kernel.box).2
      kernel.lower_bound

theorem certificateBackedGapCriterion_nonempty_iff_kernel_nonempty :
    Nonempty CertificateBackedGapCriterion ↔
      Nonempty CertificateBackedCollisionKernel := by
  constructor
  · intro h
    rcases h with ⟨criterion⟩
    exact ⟨criterion.toKernel⟩
  · intro h
    rcases h with ⟨kernel⟩
    exact ⟨kernel.toGapCriterion⟩

theorem CertificateBackedGapCriterion.collision
    (criterion : CertificateBackedGapCriterion) :
    False :=
  criterion.toKernel.collision

end BoundedArithmeticLab
