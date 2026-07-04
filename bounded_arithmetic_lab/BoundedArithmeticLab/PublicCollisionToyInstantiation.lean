/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.PublicCollisionAPI

/-!
# Toy instantiation of the public collision API

This module checks that the public collision API is not tied to the project
CnBox objects.  It instantiates the API over arbitrary formula and length
functions.  It does not assert that the upper and lower certificates are
inhabited; a complete checklist is intentionally contradictory.
-/

namespace BoundedArithmeticLab

namespace PublicCollisionToyInstantiation

def toyBox (formula : Nat → FormulaCode) (length : Nat → Real) :
    AbstractProofLengthBox where
  system := ProofSystem.PA
  measure := ProofLengthMeasure.symbolSize
  formula := formula
  length := length

def allAccepted : Nat → Prop := fun _ => True

structure ToyUpperCertificate
    (formula : Nat → FormulaCode) (length bound : Nat → Real) where
  bound_poly : IsPolynomialBound bound
  length_le_bound : ∀ n : Nat, length n ≤ bound n

def ToyUpperCertificate.toPublicUpperCertificate
    {formula : Nat → FormulaCode} {length bound : Nat → Real}
    (cert : ToyUpperCertificate formula length bound) :
    PublicCollisionAPI.UpperCertificate (toyBox formula length) allAccepted where
  acceptance := {
    accepts_eventually := by
      exact ⟨0, by intro n hn; trivial⟩ }
  short_upper := {
    bound := bound
    bound_poly := cert.bound_poly
    short_of_accepted := by
      intro n hn
      exact cert.length_le_bound n }

structure ToyLowerCertificate
    (formula : Nat → FormulaCode) (length : Nat → Real) where
  lower_bound : EventualLowerBound (toyBox formula length)

def ToyLowerCertificate.toPublicLowerCertificate
    {formula : Nat → FormulaCode} {length : Nat → Real}
    (cert : ToyLowerCertificate formula length) :
    PublicCollisionAPI.LowerCertificate (toyBox formula length) where
  lower_bound := cert.lower_bound

structure ToySeparatedCollisionChecklist where
  formula : Nat → FormulaCode
  length : Nat → Real
  bound : Nat → Real
  upper : ToyUpperCertificate formula length bound
  lower : ToyLowerCertificate formula length

def ToySeparatedCollisionChecklist.toPublicSeparatedChecklist
    (checklist : ToySeparatedCollisionChecklist) :
    PublicCollisionAPI.SeparatedChecklist where
  box := toyBox checklist.formula checklist.length
  accepted := allAccepted
  upper := checklist.upper.toPublicUpperCertificate
  lower := checklist.lower.toPublicLowerCertificate

theorem toy_public_collision
    (checklist : ToySeparatedCollisionChecklist) : False :=
  PublicCollisionAPI.collision_from_separated_checklist
    checklist.toPublicSeparatedChecklist

end PublicCollisionToyInstantiation

end BoundedArithmeticLab
