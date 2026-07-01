/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.PudlakInterface

/-!
# S21 proof-system skeleton

This module is the sidecar landing zone for the short-proof side.  It does not
yet define the full Buss `S21` syntax.  Instead, it fixes the proof-object and
length interface that a concrete `S21` formalization must instantiate.
-/

namespace BoundedArithmeticLab

universe u

structure ProofSystemBoxModel (box : AbstractProofLengthBox) where
  Proof : Type u
  proves : Proof → ℕ → Prop
  size : Proof → ℕ
  proof_length_le_size :
    ∀ n : ℕ, ∀ p : Proof, proves p n → box.length n ≤ (size p : ℝ)

structure AcceptedProofFamily
    {box : AbstractProofLengthBox} (model : ProofSystemBoxModel box)
    (accepted : ℕ → Prop) where
  bound : ℕ → ℝ
  bound_poly : IsPolynomialBound bound
  proof_of_accepted :
    ∀ n : ℕ, accepted n →
      ∃ p : model.Proof, model.proves p n ∧ (model.size p : ℝ) ≤ bound n

def AcceptedProofFamily.toShortProofUpperBound
    {box : AbstractProofLengthBox} {model : ProofSystemBoxModel box}
    {accepted : ℕ → Prop}
    (h : AcceptedProofFamily model accepted) :
    EventualShortProofUpperBound box accepted where
  bound := h.bound
  bound_poly := h.bound_poly
  short_of_accepted := by
    intro n hn
    rcases h.proof_of_accepted n hn with ⟨p, hp, hsize⟩
    exact (model.proof_length_le_size n p hp).trans hsize

def S21ProofSystemBoxModel
    (formula : ℕ → FormulaCode) (length : ℕ → ℝ) : Type (u + 1) :=
  ProofSystemBoxModel.{u}
    { system := ProofSystem.S21
      measure := ProofLengthMeasure.symbolSize
      formula := formula
      length := length }

end BoundedArithmeticLab
