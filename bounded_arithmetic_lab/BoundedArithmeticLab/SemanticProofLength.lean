/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import BoundedArithmeticLab.BoundedSyntax

/-!
# Semantic proof length

For a concrete proof-object system, the semantic proof length is the infimum of
all code sizes of proofs of the target formula.  This avoids setting the length
field by hand and gives the exact inequality needed by `FormalProofSystem`.
-/

namespace BoundedArithmeticLab

noncomputable def semanticBAProofLength
    (Ax : BAFormula → Prop) (target : ℕ → BAFormula) (n : ℕ) : ℝ :=
  sInf ({r : ℝ | ∃ p : BAProofObject Ax,
    p.conclusion = target n ∧ (p.size : ℝ) = r} : Set ℝ)

theorem semanticBAProofLength_le_size
    (Ax : BAFormula → Prop) (target : ℕ → BAFormula)
    {n : ℕ} (p : BAProofObject Ax)
    (hp : p.conclusion = target n) :
    semanticBAProofLength Ax target n ≤ (p.size : ℝ) := by
  dsimp [semanticBAProofLength]
  refine csInf_le ?_ ?_
  · refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨q, _hq, rfl⟩
    exact Nat.cast_nonneg q.size
  · exact ⟨p, hp, rfl⟩

end BoundedArithmeticLab
