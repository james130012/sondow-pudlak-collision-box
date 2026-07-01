/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.ShortProof

/-!
# Pudlak lower-bound and collision interfaces

The lower-bound theorem itself is not proved here.  This file fixes the exact
shape that a Pudlak-style lower bound must have in order to collide with a
short-proof construction.
-/

namespace BoundedArithmeticLab

structure AbstractProofLengthBox where
  system : ProofSystem
  measure : ProofLengthMeasure
  formula : ℕ → FormulaCode
  length : ℕ → ℝ

structure EventualShortProofUpperBound
    (box : AbstractProofLengthBox) (accepted : ℕ → Prop) where
  bound : ℕ → ℝ
  bound_poly : IsPolynomialBound bound
  short_of_accepted : ∀ n : ℕ, accepted n → box.length n ≤ bound n

structure EventualLowerBound (box : AbstractProofLengthBox) where
  lower_bound :
    ∀ f : ℕ → ℝ, IsPolynomialBound f →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ box.length n > f n

structure EventualAcceptanceUnderRationality
    (accepted : ℕ → Prop) where
  accepts_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → accepted n

theorem eventualCollision
    {box : AbstractProofLengthBox} {accepted : ℕ → Prop}
    (haccept : EventualAcceptanceUnderRationality accepted)
    (hshort : EventualShortProofUpperBound box accepted)
    (hlower : EventualLowerBound box) :
    False := by
  rcases haccept.accepts_eventually with ⟨N, hN⟩
  rcases hlower.lower_bound hshort.bound hshort.bound_poly N with
    ⟨n, hn_ge, hn_gt⟩
  have hn_le := hshort.short_of_accepted n (hN n hn_ge)
  linarith

structure LowerBoundTransfer
    (source target : AbstractProofLengthBox) where
  transfer :
    ∀ f : ℕ → ℝ, IsPolynomialBound f →
      EventualLowerBound source → EventualLowerBound target

def LowerBoundTransfer.refl (box : AbstractProofLengthBox) :
    LowerBoundTransfer box box where
  transfer := by
    intro f hf hlower
    exact hlower

def reflectionGraftBox (length : ℕ → ℝ) : AbstractProofLengthBox where
  system := ProofSystem.PA
  measure := ProofLengthMeasure.symbolSize
  formula := sondowReflectionGraftCode
  length := length

def partialConsistencyBox (length : ℕ → ℝ) : AbstractProofLengthBox where
  system := ProofSystem.PA
  measure := ProofLengthMeasure.symbolSize
  formula := partialConsistencyCode
  length := length

end BoundedArithmeticLab
