/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import Mathlib

/-!
# Sondow kernel moment targets

Definitions for the kernel-moment route to the Sondow decomposition formula.
This file intentionally contains target statements only; it does not assert
any unproved analytic theorem as a Lean theorem.
-/

namespace EulerLimit.SondowKernel

open BigOperators

noncomputable section

/-- Harmonic numbers in `ℝ`, indexed by the upper endpoint. -/
def harmonicReal (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹

/-- The diagonal closed form for the truncated kernel moment. -/
def diagonalClosed (a N : ℕ) : ℝ :=
  harmonicReal (a + N) - harmonicReal a

/--
The off-diagonal closed form with lower endpoint `m`, positive gap `delta`,
and truncation `N`.
-/
def offDiagonalClosed (m delta N : ℕ) : ℝ :=
  (∑ r ∈ Finset.Icc 1 delta,
      Real.log (((N + m + r : ℕ) : ℝ) / ((m + r : ℕ) : ℝ))) /
    (delta : ℝ)

/-- Closed form for the truncated kernel moment, split by diagonal/off-diagonal cases. -/
def kernelMomentClosed (a b N : ℕ) : ℝ :=
  if a = b then
    diagonalClosed a N
  else if a < b then
    offDiagonalClosed a (b - a) N
  else
    offDiagonalClosed b (a - b) N

/--
Lean-facing target for the basic kernel moment identity. The analytic integral
side will be added once its exact API is chosen.
-/
def kernelMomentClosedFormsTarget : Prop :=
  ∀ a b N : ℕ,
    kernelMomentClosed a b N =
      if a = b then
        harmonicReal (a + N) - harmonicReal a
      else if a < b then
        (∑ r ∈ Finset.Icc 1 (b - a),
            Real.log (((N + a + r : ℕ) : ℝ) / ((a + r : ℕ) : ℝ))) /
          ((b - a : ℕ) : ℝ)
      else
        (∑ r ∈ Finset.Icc 1 (a - b),
            Real.log (((N + b + r : ℕ) : ℝ) / ((b + r : ℕ) : ℝ))) /
          ((a - b : ℕ) : ℝ)

theorem kernelMomentClosedFormsTarget_holds : kernelMomentClosedFormsTarget := by
  intro a b N
  unfold kernelMomentClosed diagonalClosed offDiagonalClosed
  by_cases hab : a = b
  · simp [hab]
  · by_cases hlt : a < b
    · simp [hab, hlt]
    · simp [hab, hlt]

end

end EulerLimit.SondowKernel
