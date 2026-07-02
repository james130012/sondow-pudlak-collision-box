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

theorem semanticBAProofLength_pa_le_bussS21
    (target : ℕ → BAFormula) {n : ℕ}
    (hnonempty :
      ∃ p : BAProofObject BussS21Axiom, p.conclusion = target n) :
    semanticBAProofLength PAAxiom target n ≤
      semanticBAProofLength BussS21Axiom target n := by
  dsimp [semanticBAProofLength]
  refine le_csInf ?_ ?_
  · rcases hnonempty with ⟨p, hp⟩
    exact ⟨(p.size : ℝ), ⟨p, hp, rfl⟩⟩
  · intro r hr
    rcases hr with ⟨p, hp, rfl⟩
    have hle :
        semanticBAProofLength PAAxiom target n ≤
          ((p.mapAxioms bussS21Axiom_subset_pa).size : ℝ) :=
      semanticBAProofLength_le_size PAAxiom target
        (p.mapAxioms bussS21Axiom_subset_pa) hp
    change semanticBAProofLength PAAxiom target n ≤ (p.size : ℝ)
    simpa [BAProofObject.size_mapAxioms] using hle

end BoundedArithmeticLab
