/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakRelabeledCalibration

/-!
# Proof-length gap interface for canonical Cn boxes

This module makes the proof-complexity gap explicit.  A gap witness is the
particular index where the PA proof length beats a proposed polynomial bound.
The gap formula is proved equivalent to the existing `EventualLowerBound`
interface, and the canonical relabeled Pudlak route is connected to the final
short-proof/lower-bound collision.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure ProofLengthGapWitness
    (box : AbstractProofLengthBox) (f : Nat → Real) (N : Nat) where
  n : Nat
  n_ge : N ≤ n
  gap_pos : box.length n > f n

def HasProofLengthGapWitness
    (box : AbstractProofLengthBox) (f : Nat → Real) (N : Nat) : Prop :=
  Nonempty (ProofLengthGapWitness box f N)

def ProofLengthGap (box : AbstractProofLengthBox) : Prop :=
  ∀ f : Nat → Real, IsPolynomialBound f →
    ∀ N : Nat, HasProofLengthGapWitness box f N

theorem proofLengthGap_iff_eventualLowerBound
    (box : AbstractProofLengthBox) :
    ProofLengthGap box ↔ EventualLowerBound box := by
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

noncomputable def canonicalCnBoxPABox : AbstractProofLengthBox :=
  (concretePAFormalization
    canonicalPudlakTargetFamilySpec.target
    canonicalPudlakTargetFamilySpec.code).box

noncomputable def CanonicalCnBoxProofLengthGap : Prop :=
  ProofLengthGap canonicalCnBoxPABox

theorem CanonicalRelabeledPudlakCalibration.toProofLengthGap
    {lower_source : BussPudlakTheorem5PALowerBoundSource}
    (calibration : CanonicalRelabeledPudlakCalibration lower_source) :
    CanonicalCnBoxProofLengthGap := by
  exact (proofLengthGap_iff_eventualLowerBound canonicalCnBoxPABox).2
    (by
      simpa [canonicalCnBoxPABox]
        using calibration.toConcretePALowerBound)

structure CanonicalCnBoxGapCollisionInputs
    (accepted : Nat → Prop) where
  acceptance : EventualAcceptanceUnderRationality accepted
  short_upper : EventualShortProofUpperBound canonicalCnBoxPABox accepted
  lower_source : BussPudlakTheorem5PALowerBoundSource
  lower_calibration : CanonicalRelabeledPudlakCalibration lower_source

noncomputable def CanonicalCnBoxGapCollisionInputs.lowerBound
    {accepted : Nat → Prop}
    (inputs : CanonicalCnBoxGapCollisionInputs accepted) :
    EventualLowerBound canonicalCnBoxPABox := by
  simpa [canonicalCnBoxPABox]
    using inputs.lower_calibration.toConcretePALowerBound

noncomputable def CanonicalCnBoxGapCollisionInputs.gap
    {accepted : Nat → Prop}
    (inputs : CanonicalCnBoxGapCollisionInputs accepted) :
    CanonicalCnBoxProofLengthGap :=
  inputs.lower_calibration.toProofLengthGap

noncomputable def
    CanonicalCnBoxGapCollisionInputs.witnessAgainstShortBound
    {accepted : Nat → Prop}
    (inputs : CanonicalCnBoxGapCollisionInputs accepted)
    (N : Nat) :
    HasProofLengthGapWitness
      canonicalCnBoxPABox inputs.short_upper.bound N :=
  inputs.gap inputs.short_upper.bound inputs.short_upper.bound_poly N

theorem canonicalCnBox_gap_collision
    {accepted : Nat → Prop}
    (inputs : CanonicalCnBoxGapCollisionInputs accepted) :
    False := by
  rcases inputs.acceptance.accepts_eventually with ⟨N, hN⟩
  rcases inputs.witnessAgainstShortBound N with ⟨witness⟩
  have hle := inputs.short_upper.short_of_accepted
    witness.n (hN witness.n witness.n_ge)
  exact (not_le_of_gt witness.gap_pos) hle

end BoundedProofPredicate
end BoundedArithmeticLab
