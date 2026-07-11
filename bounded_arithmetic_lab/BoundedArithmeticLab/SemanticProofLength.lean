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

/-- A bounded-arithmetic proof of `target n` whose object size is at most `k`. -/
def BAHasProofOfSize
    (Ax : BAFormula → Prop) (target : ℕ → BAFormula)
    (n k : ℕ) : Prop :=
  ∃ p : BAProofObject Ax, p.conclusion = target n ∧ p.size ≤ k

/-- Having a proof object is equivalent to having a proof object below some
finite size bound. -/
theorem exists_BAHasProofOfSize_iff_exists_proof
    (Ax : BAFormula → Prop) (target : ℕ → BAFormula) (n : ℕ) :
    (∃ k : ℕ, BAHasProofOfSize Ax target n k) ↔
      ∃ p : BAProofObject Ax, p.conclusion = target n := by
  constructor
  · intro h
    rcases h with ⟨_k, p, hp, _hsize⟩
    exact ⟨p, hp⟩
  · intro h
    rcases h with ⟨p, hp⟩
    exact ⟨p.size, p, hp, le_rfl⟩

/--
Option-valued semantic minimum proof size.  Unlike `semanticBAProofLength`,
this records the no-proof case as `none` instead of using the real-valued
empty-infimum convention.
-/
noncomputable def semanticBAMinProofSizeOption
    (Ax : BAFormula → Prop) (target : ℕ → BAFormula) (n : ℕ) :
    Option ℕ := by
  classical
  exact
    if h : ∃ k : ℕ, BAHasProofOfSize Ax target n k then
      some (Nat.find h)
    else
      none

theorem semanticBAMinProofSizeOption_none_of_no_proof
    {Ax : BAFormula → Prop} {target : ℕ → BAFormula} {n : ℕ}
    (hno : ¬ ∃ p : BAProofObject Ax, p.conclusion = target n) :
    semanticBAMinProofSizeOption Ax target n = none := by
  classical
  have hno_size : ¬ ∃ k : ℕ, BAHasProofOfSize Ax target n k := by
    intro h
    exact hno ((exists_BAHasProofOfSize_iff_exists_proof Ax target n).1 h)
  simp [semanticBAMinProofSizeOption, hno_size]

theorem semanticBAMinProofSizeOption_some_of_exists_proof
    {Ax : BAFormula → Prop} {target : ℕ → BAFormula} {n : ℕ}
    (hproof : ∃ p : BAProofObject Ax, p.conclusion = target n) :
    ∃ k : ℕ, semanticBAMinProofSizeOption Ax target n = some k := by
  classical
  have hsize : ∃ k : ℕ, BAHasProofOfSize Ax target n k :=
    (exists_BAHasProofOfSize_iff_exists_proof Ax target n).2 hproof
  exact ⟨Nat.find hsize, by simp [semanticBAMinProofSizeOption, hsize]⟩

theorem semanticBAMinProofSizeOption_min_le_of_proof
    {Ax : BAFormula → Prop} {target : ℕ → BAFormula} {n m : ℕ}
    (hmin : semanticBAMinProofSizeOption Ax target n = some m)
    (p : BAProofObject Ax) (hp : p.conclusion = target n) :
    m ≤ p.size := by
  classical
  have hsize : ∃ k : ℕ, BAHasProofOfSize Ax target n k :=
    ⟨p.size, p, hp, le_rfl⟩
  have hfind : semanticBAMinProofSizeOption Ax target n = some (Nat.find hsize) := by
    simp [semanticBAMinProofSizeOption, hsize]
  have hm : m = Nat.find hsize := by
    rw [hfind] at hmin
    cases hmin
    rfl
  subst hm
  exact Nat.find_min' hsize ⟨p, hp, le_rfl⟩

theorem semanticBAMinProofSizeOption_some_to_hasProofOfSize
    {Ax : BAFormula → Prop} {target : ℕ → BAFormula} {n m : ℕ}
    (hmin : semanticBAMinProofSizeOption Ax target n = some m) :
    BAHasProofOfSize Ax target n m := by
  classical
  by_cases hsize : ∃ k : ℕ, BAHasProofOfSize Ax target n k
  · have hfind :
        semanticBAMinProofSizeOption Ax target n = some (Nat.find hsize) := by
      simp [semanticBAMinProofSizeOption, hsize]
    have hm : m = Nat.find hsize := by
      rw [hfind] at hmin
      cases hmin
      rfl
    subst hm
    exact Nat.find_spec hsize
  · have hnone :
        semanticBAMinProofSizeOption Ax target n = none := by
      simp [semanticBAMinProofSizeOption, hsize]
    rw [hnone] at hmin
    cases hmin

theorem semanticBAMinProofSizeOption_some_to_exists_proof
    {Ax : BAFormula → Prop} {target : ℕ → BAFormula} {n m : ℕ}
    (hmin : semanticBAMinProofSizeOption Ax target n = some m) :
    ∃ p : BAProofObject Ax, p.conclusion = target n := by
  rcases semanticBAMinProofSizeOption_some_to_hasProofOfSize hmin with
    ⟨p, hp, _hsize⟩
  exact ⟨p, hp⟩

theorem semanticBAMinProofSizeOption_some_iff_exists_proof
    {Ax : BAFormula → Prop} {target : ℕ → BAFormula} {n : ℕ} :
    (∃ m : ℕ, semanticBAMinProofSizeOption Ax target n = some m) ↔
      ∃ p : BAProofObject Ax, p.conclusion = target n := by
  constructor
  · intro hmin
    rcases hmin with ⟨m, hm⟩
    exact semanticBAMinProofSizeOption_some_to_exists_proof hm
  · intro hproof
    exact semanticBAMinProofSizeOption_some_of_exists_proof hproof

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
