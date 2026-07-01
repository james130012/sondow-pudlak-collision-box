/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import Mathlib.ModelTheory.Syntax
import EulerLimit.ProofComplexityCore

/-!
# MiniHilbert proof calculus

This module contains the local Hilbert-style proof-calculus model used by the
projection bridge.
-/

namespace MiniHilbert

open FirstOrder
open FirstOrder.Language

universe u v w

variable {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}

-- Minimal Hilbert-style proof objects for the single proof-calculus operation
-- needed here.  This is not a full PA formalization; it isolates the standard
-- right-conjunction-elimination derivation over mathlib first-order formulas.
inductive Proof : L.BoundedFormula α n → Type (max u v w) where
  | input {φ : L.BoundedFormula α n} : Proof φ
  | conjIntro {A B : L.BoundedFormula α n} : Proof A → Proof B → Proof (A ⊓ B)
  | rightConjAxiom (A B : L.BoundedFormula α n) : Proof ((A ⊓ B).imp B)
  | mp {A B : L.BoundedFormula α n} : Proof (A.imp B) → Proof A → Proof B

def Proof.length : {φ : L.BoundedFormula α n} → Proof φ → ℕ
  | _, Proof.input => 1
  | _, Proof.conjIntro hp hq => hp.length + hq.length + 1
  | _, Proof.rightConjAxiom _ _ => 1
  | _, Proof.mp hp hq => hp.length + hq.length + 1

-- A concrete proof-code size for this local Hilbert calculus.  The code-size
-- model intentionally mirrors `Proof.length`: leaves encode as one symbol and
-- modus ponens stores both subproofs plus the rule marker.
def Proof.codeSize : {φ : L.BoundedFormula α n} → Proof φ → ℕ
  | _, Proof.input => 1
  | _, Proof.conjIntro hp hq => hp.codeSize + hq.codeSize + 1
  | _, Proof.rightConjAxiom _ _ => 1
  | _, Proof.mp hp hq => hp.codeSize + hq.codeSize + 1

theorem Proof.codeSize_eq_length
    {φ : L.BoundedFormula α n} (p : Proof φ) :
    p.codeSize = p.length := by
  induction p with
  | input =>
      rfl
  | conjIntro hp hq ihp ihq =>
      simp [Proof.codeSize, Proof.length, ihp, ihq]
  | rightConjAxiom A B =>
      rfl
  | mp hp hq ihp ihq =>
      simp [Proof.codeSize, Proof.length, ihp, ihq]

def conjIntro {A B : L.BoundedFormula α n}
    (p : Proof A) (q : Proof B) : Proof (A ⊓ B) :=
  Proof.conjIntro p q

theorem length_conjIntro {A B : L.BoundedFormula α n}
    (p : Proof A) (q : Proof B) :
    (conjIntro p q).length = p.length + q.length + 1 := by
  rfl

theorem length_conjIntro_linear {A B : L.BoundedFormula α n}
    (p : Proof A) (q : Proof B) :
    (conjIntro p q).length ≤ p.length + q.length + 1 := by
  rw [length_conjIntro]

theorem codeSize_conjIntro {A B : L.BoundedFormula α n}
    (p : Proof A) (q : Proof B) :
    (conjIntro p q).codeSize = p.codeSize + q.codeSize + 1 := by
  rw [Proof.codeSize_eq_length, length_conjIntro,
    Proof.codeSize_eq_length, Proof.codeSize_eq_length]

def rightConjElim (A B : L.BoundedFormula α n) (p : Proof (A ⊓ B)) : Proof B :=
  Proof.mp (Proof.rightConjAxiom A B) p

theorem length_rightConjElim (A B : L.BoundedFormula α n) (p : Proof (A ⊓ B)) :
    (rightConjElim A B p).length = p.length + 2 := by
  simp [rightConjElim, Proof.length]
  omega

theorem length_rightConjElim_linear (A B : L.BoundedFormula α n) (p : Proof (A ⊓ B)) :
    (rightConjElim A B p).length ≤ p.length + 2 := by
  rw [length_rightConjElim]

theorem codeSize_rightConjElim
    (A B : L.BoundedFormula α n) (p : Proof (A ⊓ B)) :
    (rightConjElim A B p).codeSize = p.codeSize + 2 := by
  rw [Proof.codeSize_eq_length, length_rightConjElim, Proof.codeSize_eq_length]

theorem codeSize_rightConjElim_linear
    (A B : L.BoundedFormula α n) (p : Proof (A ⊓ B)) :
    (rightConjElim A B p).codeSize ≤ p.codeSize + 2 := by
  rw [codeSize_rightConjElim]

structure RightConjElimClosed
    (ProofObj : L.BoundedFormula α n → Type (max u v w))
    (length : {φ : L.BoundedFormula α n} → ProofObj φ → ℕ)
    (rightElim :
      (A B : L.BoundedFormula α n) → ProofObj (A ⊓ B) → ProofObj B) :
    Prop where
  length_right_elim :
    ∀ (A B : L.BoundedFormula α n) (p : ProofObj (A ⊓ B)),
      length (rightElim A B p) = length p + 2
  length_right_elim_linear :
    ∀ (A B : L.BoundedFormula α n) (p : ProofObj (A ⊓ B)),
      length (rightElim A B p) ≤ length p + 2

theorem proof_right_conj_elim_closed :
    RightConjElimClosed
      (L := L) (α := α) (n := n)
      Proof Proof.length rightConjElim where
  length_right_elim := length_rightConjElim
  length_right_elim_linear := length_rightConjElim_linear

-- A minimal Hilbert theory proof object.  `Ax` is the axiom predicate of the
-- object theory.  This is the proof-calculus core needed to model that PA can
-- simulate S_2^1 when every S_2^1 axiom is available in PA.
inductive TheoryProof
    (Ax : L.BoundedFormula α n → Prop) : L.BoundedFormula α n → Type (max u v w) where
  | ax {φ : L.BoundedFormula α n} : Ax φ → TheoryProof Ax φ
  | conjIntro {A B : L.BoundedFormula α n} :
      TheoryProof Ax A → TheoryProof Ax B → TheoryProof Ax (A ⊓ B)
  | rightConjAxiom (A B : L.BoundedFormula α n) : TheoryProof Ax ((A ⊓ B).imp B)
  | mp {A B : L.BoundedFormula α n} :
      TheoryProof Ax (A.imp B) → TheoryProof Ax A → TheoryProof Ax B

def TheoryProof.length
    {Ax : L.BoundedFormula α n → Prop} :
    {φ : L.BoundedFormula α n} → TheoryProof Ax φ → ℕ
  | _, TheoryProof.ax _ => 1
  | _, TheoryProof.conjIntro hp hq => hp.length + hq.length + 1
  | _, TheoryProof.rightConjAxiom _ _ => 1
  | _, TheoryProof.mp hp hq => hp.length + hq.length + 1

def TheoryProof.codeSize
    {Ax : L.BoundedFormula α n → Prop} :
    {φ : L.BoundedFormula α n} → TheoryProof Ax φ → ℕ
  | _, TheoryProof.ax _ => 1
  | _, TheoryProof.conjIntro hp hq => hp.codeSize + hq.codeSize + 1
  | _, TheoryProof.rightConjAxiom _ _ => 1
  | _, TheoryProof.mp hp hq => hp.codeSize + hq.codeSize + 1

theorem TheoryProof.codeSize_eq_length
    {Ax : L.BoundedFormula α n → Prop}
    {φ : L.BoundedFormula α n} (p : TheoryProof Ax φ) :
    p.codeSize = p.length := by
  induction p with
  | ax h =>
      rfl
  | conjIntro hp hq ihp ihq =>
      simp [TheoryProof.codeSize, TheoryProof.length, ihp, ihq]
  | rightConjAxiom A B =>
      rfl
  | mp hp hq ihp ihq =>
      simp [TheoryProof.codeSize, TheoryProof.length, ihp, ihq]

def TheoryProof.andIntro
    {Ax : L.BoundedFormula α n → Prop} {A B : L.BoundedFormula α n}
    (p : TheoryProof Ax A) (q : TheoryProof Ax B) :
    TheoryProof Ax (A ⊓ B) :=
  TheoryProof.conjIntro p q

theorem TheoryProof.length_conjIntro
    {Ax : L.BoundedFormula α n → Prop} {A B : L.BoundedFormula α n}
    (p : TheoryProof Ax A) (q : TheoryProof Ax B) :
    (TheoryProof.andIntro p q).length = p.length + q.length + 1 := by
  rfl

theorem TheoryProof.length_conjIntro_linear
    {Ax : L.BoundedFormula α n → Prop} {A B : L.BoundedFormula α n}
    (p : TheoryProof Ax A) (q : TheoryProof Ax B) :
    (TheoryProof.andIntro p q).length ≤ p.length + q.length + 1 := by
  rw [TheoryProof.length_conjIntro]

theorem TheoryProof.codeSize_conjIntro
    {Ax : L.BoundedFormula α n → Prop} {A B : L.BoundedFormula α n}
    (p : TheoryProof Ax A) (q : TheoryProof Ax B) :
    (TheoryProof.andIntro p q).codeSize = p.codeSize + q.codeSize + 1 := by
  rw [TheoryProof.codeSize_eq_length, TheoryProof.length_conjIntro,
    TheoryProof.codeSize_eq_length, TheoryProof.codeSize_eq_length]

def TheoryProof.rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    (A B : L.BoundedFormula α n) (p : TheoryProof Ax (A ⊓ B)) :
    TheoryProof Ax B :=
  TheoryProof.mp (TheoryProof.rightConjAxiom A B) p

theorem TheoryProof.length_rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    (A B : L.BoundedFormula α n) (p : TheoryProof Ax (A ⊓ B)) :
    (TheoryProof.rightConjElim A B p).length = p.length + 2 := by
  simp [TheoryProof.rightConjElim, TheoryProof.length]
  omega

theorem TheoryProof.length_rightConjElim_linear
    {Ax : L.BoundedFormula α n → Prop}
    (A B : L.BoundedFormula α n) (p : TheoryProof Ax (A ⊓ B)) :
    (TheoryProof.rightConjElim A B p).length ≤ p.length + 2 := by
  rw [TheoryProof.length_rightConjElim]

theorem TheoryProof.codeSize_rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    (A B : L.BoundedFormula α n) (p : TheoryProof Ax (A ⊓ B)) :
    (TheoryProof.rightConjElim A B p).codeSize = p.codeSize + 2 := by
  rw [TheoryProof.codeSize_eq_length, TheoryProof.length_rightConjElim,
    TheoryProof.codeSize_eq_length]

theorem TheoryProof.codeSize_rightConjElim_linear
    {Ax : L.BoundedFormula α n → Prop}
    (A B : L.BoundedFormula α n) (p : TheoryProof Ax (A ⊓ B)) :
    (TheoryProof.rightConjElim A B p).codeSize ≤ p.codeSize + 2 := by
  rw [TheoryProof.codeSize_rightConjElim]

theorem theory_proof_right_conj_elim_closed
    (Ax : L.BoundedFormula α n → Prop) :
    RightConjElimClosed
      (L := L) (α := α) (n := n)
      (TheoryProof Ax) TheoryProof.length TheoryProof.rightConjElim where
  length_right_elim := TheoryProof.length_rightConjElim
  length_right_elim_linear := TheoryProof.length_rightConjElim_linear

def TheoryProof.mapAxioms
    {Ax₁ Ax₂ : L.BoundedFormula α n → Prop}
    (hAx : ∀ {φ : L.BoundedFormula α n}, Ax₁ φ → Ax₂ φ) :
    {φ : L.BoundedFormula α n} → TheoryProof Ax₁ φ → TheoryProof Ax₂ φ
  | _, TheoryProof.ax h => TheoryProof.ax (hAx h)
  | _, TheoryProof.conjIntro hp hq =>
      TheoryProof.conjIntro
        (TheoryProof.mapAxioms hAx hp) (TheoryProof.mapAxioms hAx hq)
  | _, TheoryProof.rightConjAxiom A B => TheoryProof.rightConjAxiom A B
  | _, TheoryProof.mp hp hq =>
      TheoryProof.mp (TheoryProof.mapAxioms hAx hp) (TheoryProof.mapAxioms hAx hq)

theorem TheoryProof.length_mapAxioms
    {Ax₁ Ax₂ : L.BoundedFormula α n → Prop}
    (hAx : ∀ {φ : L.BoundedFormula α n}, Ax₁ φ → Ax₂ φ)
    {φ : L.BoundedFormula α n} (p : TheoryProof Ax₁ φ) :
    (TheoryProof.mapAxioms hAx p).length = p.length := by
  induction p with
  | ax h =>
      simp [TheoryProof.mapAxioms, TheoryProof.length]
  | conjIntro hp hq ihp ihq =>
      simp [TheoryProof.mapAxioms, TheoryProof.length, ihp, ihq]
  | rightConjAxiom A B =>
      simp [TheoryProof.mapAxioms, TheoryProof.length]
  | mp hp hq ihp ihq =>
      simp [TheoryProof.mapAxioms, TheoryProof.length, ihp, ihq]

theorem TheoryProof.length_mapAxioms_linear
    {Ax₁ Ax₂ : L.BoundedFormula α n → Prop}
    (hAx : ∀ {φ : L.BoundedFormula α n}, Ax₁ φ → Ax₂ φ)
    {φ : L.BoundedFormula α n} (p : TheoryProof Ax₁ φ) :
    (TheoryProof.mapAxioms hAx p).length ≤ p.length := by
  rw [TheoryProof.length_mapAxioms hAx p]

def TheoryProof.HasProofOfLength
    (Ax : L.BoundedFormula α n → Prop) (φ : L.BoundedFormula α n) (k : ℕ) : Prop :=
  ∃ p : TheoryProof Ax φ, p.length ≤ k

def TheoryProof.Provable
    (Ax : L.BoundedFormula α n → Prop) (φ : L.BoundedFormula α n) : Prop :=
  Nonempty (TheoryProof Ax φ)

theorem TheoryProof.exists_hasProofOfLength_of_provable
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) :
    ∃ k : ℕ, TheoryProof.HasProofOfLength Ax φ k := by
  rcases h with ⟨p⟩
  exact ⟨p.length, p, le_rfl⟩

noncomputable def TheoryProof.minLength
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) : ℕ :=
  by
    classical
    exact Nat.find (TheoryProof.exists_hasProofOfLength_of_provable h)

theorem TheoryProof.hasProofOfLength_minLength
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) :
    TheoryProof.HasProofOfLength Ax φ (TheoryProof.minLength h) := by
  classical
  exact Nat.find_spec (TheoryProof.exists_hasProofOfLength_of_provable h)

theorem TheoryProof.minLength_le_of_hasProofOfLength
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) {k : ℕ}
    (hk : TheoryProof.HasProofOfLength Ax φ k) :
    TheoryProof.minLength h ≤ k := by
  classical
  exact Nat.find_min' (TheoryProof.exists_hasProofOfLength_of_provable h) hk

def TheoryProof.HasCodeOfSize
    (Ax : L.BoundedFormula α n → Prop) (φ : L.BoundedFormula α n) (k : ℕ) : Prop :=
  ∃ p : TheoryProof Ax φ, p.codeSize ≤ k

theorem TheoryProof.exists_hasCodeOfSize_of_provable
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) :
    ∃ k : ℕ, TheoryProof.HasCodeOfSize Ax φ k := by
  rcases h with ⟨p⟩
  exact ⟨p.codeSize, p, le_rfl⟩

noncomputable def TheoryProof.minCodeSize
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) : ℕ :=
  by
    classical
    exact Nat.find (TheoryProof.exists_hasCodeOfSize_of_provable h)

theorem TheoryProof.hasCodeOfSize_minCodeSize
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) :
    TheoryProof.HasCodeOfSize Ax φ (TheoryProof.minCodeSize h) := by
  classical
  exact Nat.find_spec (TheoryProof.exists_hasCodeOfSize_of_provable h)

theorem TheoryProof.minCodeSize_le_of_hasCodeOfSize
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) {k : ℕ}
    (hk : TheoryProof.HasCodeOfSize Ax φ k) :
    TheoryProof.minCodeSize h ≤ k := by
  classical
  exact Nat.find_min' (TheoryProof.exists_hasCodeOfSize_of_provable h) hk

theorem TheoryProof.hasProofOfLength_of_hasCodeOfSize
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n} {k : ℕ}
    (h : TheoryProof.HasCodeOfSize Ax φ k) :
    TheoryProof.HasProofOfLength Ax φ k := by
  rcases h with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  rw [← TheoryProof.codeSize_eq_length p]
  exact hp

theorem TheoryProof.hasCodeOfSize_of_hasProofOfLength
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n} {k : ℕ}
    (h : TheoryProof.HasProofOfLength Ax φ k) :
    TheoryProof.HasCodeOfSize Ax φ k := by
  rcases h with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  rw [TheoryProof.codeSize_eq_length p]
  exact hp

theorem TheoryProof.minCodeSize_eq_minLength
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) :
    TheoryProof.minCodeSize h = TheoryProof.minLength h := by
  apply Nat.le_antisymm
  · exact TheoryProof.minCodeSize_le_of_hasCodeOfSize h
      (TheoryProof.hasCodeOfSize_of_hasProofOfLength
        (TheoryProof.hasProofOfLength_minLength h))
  · exact TheoryProof.minLength_le_of_hasProofOfLength h
      (TheoryProof.hasProofOfLength_of_hasCodeOfSize
        (TheoryProof.hasCodeOfSize_minCodeSize h))

structure TheoryProof.Code
    (Ax : L.BoundedFormula α n → Prop) (φ : L.BoundedFormula α n) where
  proof : TheoryProof Ax φ
  size : ℕ
  size_eq_codeSize : size = proof.codeSize

def TheoryProof.Code.ofProof
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (p : TheoryProof Ax φ) : TheoryProof.Code Ax φ where
  proof := p
  size := p.codeSize
  size_eq_codeSize := rfl

def TheoryProof.HasCheckedCodeOfSize
    (Ax : L.BoundedFormula α n → Prop) (φ : L.BoundedFormula α n) (k : ℕ) : Prop :=
  ∃ c : TheoryProof.Code Ax φ, c.size ≤ k

theorem TheoryProof.hasCheckedCodeOfSize_of_hasCodeOfSize
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n} {k : ℕ}
    (h : TheoryProof.HasCodeOfSize Ax φ k) :
    TheoryProof.HasCheckedCodeOfSize Ax φ k := by
  rcases h with ⟨p, hp⟩
  exact ⟨TheoryProof.Code.ofProof p, hp⟩

theorem TheoryProof.hasCodeOfSize_of_hasCheckedCodeOfSize
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n} {k : ℕ}
    (h : TheoryProof.HasCheckedCodeOfSize Ax φ k) :
    TheoryProof.HasCodeOfSize Ax φ k := by
  rcases h with ⟨c, hc⟩
  refine ⟨c.proof, ?_⟩
  rwa [← c.size_eq_codeSize]

theorem TheoryProof.exists_hasCheckedCodeOfSize_of_provable
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) :
    ∃ k : ℕ, TheoryProof.HasCheckedCodeOfSize Ax φ k := by
  rcases h with ⟨p⟩
  exact ⟨p.codeSize, TheoryProof.hasCheckedCodeOfSize_of_hasCodeOfSize
    ⟨p, le_rfl⟩⟩

noncomputable def TheoryProof.minCheckedCodeSize
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) : ℕ :=
  by
    classical
    exact Nat.find (TheoryProof.exists_hasCheckedCodeOfSize_of_provable h)

theorem TheoryProof.hasCheckedCodeOfSize_minCheckedCodeSize
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) :
    TheoryProof.HasCheckedCodeOfSize Ax φ (TheoryProof.minCheckedCodeSize h) := by
  classical
  exact Nat.find_spec (TheoryProof.exists_hasCheckedCodeOfSize_of_provable h)

theorem TheoryProof.minCheckedCodeSize_le_of_hasCheckedCodeOfSize
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) {k : ℕ}
    (hk : TheoryProof.HasCheckedCodeOfSize Ax φ k) :
    TheoryProof.minCheckedCodeSize h ≤ k := by
  classical
  exact Nat.find_min'
    (TheoryProof.exists_hasCheckedCodeOfSize_of_provable h) hk

theorem TheoryProof.minCheckedCodeSize_eq_of_provable
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h₁ h₂ : TheoryProof.Provable Ax φ) :
    TheoryProof.minCheckedCodeSize h₁ = TheoryProof.minCheckedCodeSize h₂ := by
  apply le_antisymm
  · exact TheoryProof.minCheckedCodeSize_le_of_hasCheckedCodeOfSize h₁
      (TheoryProof.hasCheckedCodeOfSize_minCheckedCodeSize h₂)
  · exact TheoryProof.minCheckedCodeSize_le_of_hasCheckedCodeOfSize h₂
      (TheoryProof.hasCheckedCodeOfSize_minCheckedCodeSize h₁)

theorem TheoryProof.minCheckedCodeSize_eq_minCodeSize
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) :
    TheoryProof.minCheckedCodeSize h = TheoryProof.minCodeSize h := by
  apply Nat.le_antisymm
  · exact TheoryProof.minCheckedCodeSize_le_of_hasCheckedCodeOfSize h
      (TheoryProof.hasCheckedCodeOfSize_of_hasCodeOfSize
        (TheoryProof.hasCodeOfSize_minCodeSize h))
  · exact TheoryProof.minCodeSize_le_of_hasCodeOfSize h
      (TheoryProof.hasCodeOfSize_of_hasCheckedCodeOfSize
        (TheoryProof.hasCheckedCodeOfSize_minCheckedCodeSize h))

theorem TheoryProof.minCheckedCodeSize_eq_minLength
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n}
    (h : TheoryProof.Provable Ax φ) :
    TheoryProof.minCheckedCodeSize h = TheoryProof.minLength h := by
  rw [TheoryProof.minCheckedCodeSize_eq_minCodeSize,
    TheoryProof.minCodeSize_eq_minLength]

theorem TheoryProof.provable_of_hasProofOfLength
    {Ax : L.BoundedFormula α n → Prop} {φ : L.BoundedFormula α n} {k : ℕ}
    (h : TheoryProof.HasProofOfLength Ax φ k) :
    TheoryProof.Provable Ax φ := by
  rcases h with ⟨p, _hp⟩
  exact ⟨p⟩

theorem TheoryProof.hasProofOfLength_mapAxioms
    {Ax₁ Ax₂ : L.BoundedFormula α n → Prop}
    (hAx : ∀ {φ : L.BoundedFormula α n}, Ax₁ φ → Ax₂ φ)
    {φ : L.BoundedFormula α n} {k : ℕ}
    (h : TheoryProof.HasProofOfLength Ax₁ φ k) :
    TheoryProof.HasProofOfLength Ax₂ φ k := by
  rcases h with ⟨p, hp⟩
  refine ⟨TheoryProof.mapAxioms hAx p, ?_⟩
  rw [TheoryProof.length_mapAxioms hAx p]
  exact hp

theorem TheoryProof.hasProofOfLength_rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    (A B : L.BoundedFormula α n) {k : ℕ}
    (h : TheoryProof.HasProofOfLength Ax (A ⊓ B) k) :
    TheoryProof.HasProofOfLength Ax B (k + 2) := by
  rcases h with ⟨p, hp⟩
  refine ⟨TheoryProof.rightConjElim A B p, ?_⟩
  rw [TheoryProof.length_rightConjElim]
  omega

theorem TheoryProof.hasProofOfLength_conjIntro
    {Ax : L.BoundedFormula α n → Prop}
    {A B : L.BoundedFormula α n} {kA kB : ℕ}
    (hA : TheoryProof.HasProofOfLength Ax A kA)
    (hB : TheoryProof.HasProofOfLength Ax B kB) :
    TheoryProof.HasProofOfLength Ax (A ⊓ B) (kA + kB + 1) := by
  rcases hA with ⟨pA, hpA⟩
  rcases hB with ⟨pB, hpB⟩
  refine ⟨TheoryProof.andIntro pA pB, ?_⟩
  rw [TheoryProof.length_conjIntro]
  omega

theorem TheoryProof.provable_rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    (A B : L.BoundedFormula α n)
    (h : TheoryProof.Provable Ax (A ⊓ B)) :
    TheoryProof.Provable Ax B := by
  exact TheoryProof.provable_of_hasProofOfLength
    (TheoryProof.hasProofOfLength_rightConjElim A B
      (TheoryProof.hasProofOfLength_minLength h))

theorem TheoryProof.minLength_rightConjElim_le
    {Ax : L.BoundedFormula α n → Prop}
    (A B : L.BoundedFormula α n)
    (h : TheoryProof.Provable Ax (A ⊓ B)) :
    TheoryProof.minLength (TheoryProof.provable_rightConjElim A B h) ≤
      TheoryProof.minLength h + 2 := by
  exact TheoryProof.minLength_le_of_hasProofOfLength
    (TheoryProof.provable_rightConjElim A B h)
    (TheoryProof.hasProofOfLength_rightConjElim A B
      (TheoryProof.hasProofOfLength_minLength h))

theorem TheoryProof.hasProofOfLength_mapAxioms_rightConjElim
    {Ax₁ Ax₂ : L.BoundedFormula α n → Prop}
    (hAx : ∀ {φ : L.BoundedFormula α n}, Ax₁ φ → Ax₂ φ)
    (A B : L.BoundedFormula α n) {k : ℕ}
    (h : TheoryProof.HasProofOfLength Ax₁ (A ⊓ B) k) :
    TheoryProof.HasProofOfLength Ax₂ B (k + 2) :=
  TheoryProof.hasProofOfLength_rightConjElim A B
    (TheoryProof.hasProofOfLength_mapAxioms hAx h)

theorem TheoryProof.hasProofOfLength_rightConjElim_mapAxioms
    {Ax₁ Ax₂ : L.BoundedFormula α n → Prop}
    (hAx : ∀ {φ : L.BoundedFormula α n}, Ax₁ φ → Ax₂ φ)
    (A B : L.BoundedFormula α n) {k : ℕ}
    (h : TheoryProof.HasProofOfLength Ax₁ (A ⊓ B) k) :
    TheoryProof.HasProofOfLength Ax₂ B (k + 2) :=
  TheoryProof.hasProofOfLength_mapAxioms hAx
    (TheoryProof.hasProofOfLength_rightConjElim A B h)

structure ConcreteShortProofFamily
    (Ax : L.BoundedFormula α n → Prop) (code : ℕ → L.BoundedFormula α n)
    (accepted : ℕ → Prop) (bound : ℕ → ℕ) : Prop where
  short_proof :
    ∀ m : ℕ, accepted m → TheoryProof.HasProofOfLength Ax (code m) (bound m)

theorem ConcreteShortProofFamily.minCheckedCodeSize_le_bound
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    {accepted : ℕ → Prop} {bound : ℕ → ℕ}
    (hshort : ConcreteShortProofFamily Ax code accepted bound)
    (hprov : ∀ m : ℕ, TheoryProof.Provable Ax (code m)) :
    ∀ m : ℕ, accepted m →
      TheoryProof.minCheckedCodeSize (hprov m) ≤ bound m := by
  intro m hm
  have hproof := hshort.short_proof m hm
  have hchecked :
      TheoryProof.HasCheckedCodeOfSize Ax (code m) (bound m) :=
    TheoryProof.hasCheckedCodeOfSize_of_hasCodeOfSize
      (TheoryProof.hasCodeOfSize_of_hasProofOfLength hproof)
  exact TheoryProof.minCheckedCodeSize_le_of_hasCheckedCodeOfSize
    (hprov m) hchecked

structure ConcreteProofFamily
    (Ax : L.BoundedFormula α n → Prop) (code : ℕ → L.BoundedFormula α n) where
  proof : ∀ m : ℕ, TheoryProof Ax (code m)

def ConcreteProofFamily.provable
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code) (m : ℕ) :
    TheoryProof.Provable Ax (code m) :=
  ⟨h.proof m⟩

def ConcreteProofFamily.length
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code) (m : ℕ) : ℕ :=
  (h.proof m).length

noncomputable def ConcreteProofFamily.minLength
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code) (m : ℕ) : ℕ :=
  TheoryProof.minLength (h.provable m)

noncomputable def ConcreteProofFamily.minCodeSize
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code) (m : ℕ) : ℕ :=
  TheoryProof.minCodeSize (h.provable m)

noncomputable def ConcreteProofFamily.minCheckedCodeSize
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code) (m : ℕ) : ℕ :=
  TheoryProof.minCheckedCodeSize (h.provable m)

theorem ConcreteProofFamily.minLength_le_length
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code) (m : ℕ) :
    h.minLength m ≤ h.length m := by
  exact TheoryProof.minLength_le_of_hasProofOfLength (h.provable m)
    ⟨h.proof m, le_rfl⟩

theorem ConcreteProofFamily.minCodeSize_eq_minLength
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code) (m : ℕ) :
    h.minCodeSize m = h.minLength m :=
  TheoryProof.minCodeSize_eq_minLength (h.provable m)

theorem ConcreteProofFamily.minCheckedCodeSize_eq_minCodeSize
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code) (m : ℕ) :
    h.minCheckedCodeSize m = h.minCodeSize m :=
  TheoryProof.minCheckedCodeSize_eq_minCodeSize (h.provable m)

theorem ConcreteProofFamily.minCheckedCodeSize_eq_minLength
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code) (m : ℕ) :
    h.minCheckedCodeSize m = h.minLength m :=
  TheoryProof.minCheckedCodeSize_eq_minLength (h.provable m)

def ConcreteProofFamily.codeSize
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code) (m : ℕ) : ℕ :=
  (h.proof m).codeSize

theorem ConcreteProofFamily.codeSize_eq_length
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code) (m : ℕ) :
    h.codeSize m = h.length m :=
  TheoryProof.codeSize_eq_length (h.proof m)

def ConcreteProofFamily.conjIntro
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (hA : ConcreteProofFamily Ax A) (hB : ConcreteProofFamily Ax B) :
    ConcreteProofFamily Ax (fun m => A m ⊓ B m) where
  proof := fun m => TheoryProof.andIntro (hA.proof m) (hB.proof m)

theorem ConcreteProofFamily.length_conjIntro
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (hA : ConcreteProofFamily Ax A) (hB : ConcreteProofFamily Ax B) (m : ℕ) :
    (hA.conjIntro hB).length m = hA.length m + hB.length m + 1 := by
  exact TheoryProof.length_conjIntro (hA.proof m) (hB.proof m)

theorem ConcreteProofFamily.length_conjIntro_linear
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (hA : ConcreteProofFamily Ax A) (hB : ConcreteProofFamily Ax B) (m : ℕ) :
    (hA.conjIntro hB).length m ≤ hA.length m + hB.length m + 1 := by
  rw [hA.length_conjIntro hB m]

theorem ConcreteProofFamily.codeSize_conjIntro
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (hA : ConcreteProofFamily Ax A) (hB : ConcreteProofFamily Ax B) (m : ℕ) :
    (hA.conjIntro hB).codeSize m = hA.codeSize m + hB.codeSize m + 1 := by
  exact TheoryProof.codeSize_conjIntro (hA.proof m) (hB.proof m)

theorem ConcreteProofFamily.minLength_conjIntro_le
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (hA : ConcreteProofFamily Ax A) (hB : ConcreteProofFamily Ax B) (m : ℕ) :
    (hA.conjIntro hB).minLength m ≤ hA.length m + hB.length m + 1 := by
  exact TheoryProof.minLength_le_of_hasProofOfLength
    ((hA.conjIntro hB).provable m)
    ⟨(hA.conjIntro hB).proof m, by
      change (hA.conjIntro hB).length m ≤ hA.length m + hB.length m + 1
      rw [hA.length_conjIntro hB m]⟩

def ConcreteProofFamily.rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) :
    ConcreteProofFamily Ax B where
  proof := fun m => TheoryProof.rightConjElim (A m) (B m) (h.proof m)

theorem ConcreteProofFamily.length_rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) (m : ℕ) :
    h.rightConjElim.length m = h.length m + 2 := by
  exact TheoryProof.length_rightConjElim (A m) (B m) (h.proof m)

theorem ConcreteProofFamily.length_rightConjElim_linear
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) (m : ℕ) :
    h.rightConjElim.length m ≤ h.length m + 2 := by
  rw [h.length_rightConjElim m]

theorem ConcreteProofFamily.minLength_rightConjElim_le
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) (m : ℕ) :
    h.rightConjElim.minLength m ≤ h.minLength m + 2 := by
  exact TheoryProof.minLength_rightConjElim_le (A m) (B m) (h.provable m)

theorem ConcreteProofFamily.minCodeSize_rightConjElim_le
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) (m : ℕ) :
    h.rightConjElim.minCodeSize m ≤ h.minCodeSize m + 2 := by
  rw [h.rightConjElim.minCodeSize_eq_minLength m,
    h.minCodeSize_eq_minLength m]
  exact h.minLength_rightConjElim_le m

theorem ConcreteProofFamily.minCheckedCodeSize_rightConjElim_le
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) (m : ℕ) :
    h.rightConjElim.minCheckedCodeSize m ≤ h.minCheckedCodeSize m + 2 := by
  rw [h.rightConjElim.minCheckedCodeSize_eq_minCodeSize m,
    h.minCheckedCodeSize_eq_minCodeSize m]
  exact h.minCodeSize_rightConjElim_le m

theorem ConcreteProofFamily.codeSize_rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) (m : ℕ) :
    h.rightConjElim.codeSize m = h.codeSize m + 2 := by
  exact TheoryProof.codeSize_rightConjElim (A m) (B m) (h.proof m)

theorem ConcreteProofFamily.codeSize_rightConjElim_linear
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) (m : ℕ) :
    h.rightConjElim.codeSize m ≤ h.codeSize m + 2 := by
  rw [h.codeSize_rightConjElim m]

def ConcreteProofFamily.toShortProofFamily
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code) :
    ConcreteShortProofFamily Ax code (fun _ => True) h.length where
  short_proof := by
    intro m _hm
    exact ⟨h.proof m, le_rfl⟩

def ConcreteProofFamily.rightConjElimShortProofFamily
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) :
    ConcreteShortProofFamily Ax B (fun _ => True) (fun m => h.length m + 2) where
  short_proof := by
    intro m _hm
    refine ⟨h.rightConjElim.proof m, ?_⟩
    change h.rightConjElim.length m ≤ h.length m + 2
    rw [h.length_rightConjElim m]

def nat_bound_as_real (bound : ℕ → ℕ) (m : ℕ) : ℝ :=
  bound m

theorem is_polynomial_bound_nat_add_const
    {bound : ℕ → ℕ} (hbound : is_polynomial_bound (nat_bound_as_real bound))
    (c : ℕ) :
    is_polynomial_bound (nat_bound_as_real (fun m => bound m + c)) := by
  have hrescale :
      is_polynomial_bound (fun m : ℕ => (1 : ℝ) * nat_bound_as_real bound m + c) :=
    hbound.linear_rescale (by norm_num) (by exact_mod_cast Nat.zero_le c)
  rcases hrescale with ⟨C, k, hCk⟩
  refine ⟨C, k, ?_⟩
  intro m
  have hrewrite :
      nat_bound_as_real (fun m => bound m + c) m =
        (1 : ℝ) * nat_bound_as_real bound m + c := by
    simp [nat_bound_as_real, Nat.cast_add]
  rw [hrewrite]
  exact hCk m

theorem is_polynomial_bound_nat_add
    {left right : ℕ → ℕ}
    (hleft : is_polynomial_bound (nat_bound_as_real left))
    (hright : is_polynomial_bound (nat_bound_as_real right)) :
    is_polynomial_bound (nat_bound_as_real (fun m => left m + right m)) := by
  rcases hleft.nonneg_coefficient with ⟨C₁, k₁, hC₁, hleft_bound⟩
  rcases hright.nonneg_coefficient with ⟨C₂, k₂, hC₂, hright_bound⟩
  refine ⟨C₁ + C₂, max k₁ k₂, ?_⟩
  intro m
  have hbase_nonneg : 0 ≤ (m : ℝ) + 1 := by
    nlinarith [show (0 : ℝ) ≤ (m : ℝ) by exact Nat.cast_nonneg m]
  have hbase_one : 1 ≤ (m : ℝ) + 1 := by
    nlinarith [show (0 : ℝ) ≤ (m : ℝ) by exact Nat.cast_nonneg m]
  have hpow₁ :
      ((m : ℝ) + 1) ^ k₁ ≤ ((m : ℝ) + 1) ^ max k₁ k₂ :=
    pow_le_pow_right₀ hbase_one (Nat.le_max_left k₁ k₂)
  have hpow₂ :
      ((m : ℝ) + 1) ^ k₂ ≤ ((m : ℝ) + 1) ^ max k₁ k₂ :=
    pow_le_pow_right₀ hbase_one (Nat.le_max_right k₁ k₂)
  have hleft_le :
      nat_bound_as_real left m ≤
        C₁ * ((m : ℝ) + 1) ^ max k₁ k₂ := by
    exact le_trans (hleft_bound m)
      (mul_le_mul_of_nonneg_left hpow₁ hC₁)
  have hright_le :
      nat_bound_as_real right m ≤
        C₂ * ((m : ℝ) + 1) ^ max k₁ k₂ := by
    exact le_trans (hright_bound m)
      (mul_le_mul_of_nonneg_left hpow₂ hC₂)
  have hpow_nonneg : 0 ≤ ((m : ℝ) + 1) ^ max k₁ k₂ :=
    pow_nonneg hbase_nonneg _
  calc
    nat_bound_as_real (fun m => left m + right m) m
        = (left m : ℝ) + (right m : ℝ) := by
          simp [nat_bound_as_real]
    _ ≤ C₁ * ((m : ℝ) + 1) ^ max k₁ k₂ +
        C₂ * ((m : ℝ) + 1) ^ max k₁ k₂ := by
          simpa [nat_bound_as_real] using add_le_add hleft_le hright_le
    _ = (C₁ + C₂) * ((m : ℝ) + 1) ^ max k₁ k₂ := by
          ring

theorem is_polynomial_bound_nat_add_add_const
    {left right : ℕ → ℕ}
    (hleft : is_polynomial_bound (nat_bound_as_real left))
    (hright : is_polynomial_bound (nat_bound_as_real right))
    (c : ℕ) :
    is_polynomial_bound
      (nat_bound_as_real (fun m => left m + right m + c)) :=
  is_polynomial_bound_nat_add_const
    (is_polynomial_bound_nat_add hleft hright) c

theorem ConcreteProofFamily.rightConjElim_length_polynomial
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m))
    (hpoly : is_polynomial_bound (nat_bound_as_real h.length)) :
    is_polynomial_bound (nat_bound_as_real h.rightConjElim.length) := by
  have hpoly_add :
      is_polynomial_bound (nat_bound_as_real (fun m => h.length m + 2)) :=
    is_polynomial_bound_nat_add_const hpoly 2
  rcases hpoly_add with ⟨C, k, hCk⟩
  refine ⟨C, k, ?_⟩
  intro m
  have hlen : h.rightConjElim.length m = h.length m + 2 :=
    h.length_rightConjElim m
  simpa [nat_bound_as_real, hlen] using hCk m

theorem ConcreteProofFamily.minLength_polynomial_of_length_polynomial
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code)
    (hpoly : is_polynomial_bound (nat_bound_as_real h.length)) :
    is_polynomial_bound (nat_bound_as_real h.minLength) := by
  exact is_polynomial_bound_of_le (g := nat_bound_as_real h.length) (by
    intro m
    have hle : (h.minLength m : ℝ) ≤ h.length m := by
      exact_mod_cast h.minLength_le_length m
    simpa [nat_bound_as_real] using hle) hpoly

theorem ConcreteProofFamily.conjIntro_length_polynomial
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (hA : ConcreteProofFamily Ax A) (hB : ConcreteProofFamily Ax B)
    (hApoly : is_polynomial_bound (nat_bound_as_real hA.length))
    (hBpoly : is_polynomial_bound (nat_bound_as_real hB.length)) :
    is_polynomial_bound (nat_bound_as_real (hA.conjIntro hB).length) := by
  have hpoly_add :
      is_polynomial_bound
        (nat_bound_as_real (fun m => hA.length m + hB.length m + 1)) :=
    is_polynomial_bound_nat_add_add_const hApoly hBpoly 1
  rcases hpoly_add with ⟨C, k, hCk⟩
  refine ⟨C, k, ?_⟩
  intro m
  have hlen :
      (hA.conjIntro hB).length m = hA.length m + hB.length m + 1 :=
    hA.length_conjIntro hB m
  simpa [nat_bound_as_real, hlen] using hCk m

theorem ConcreteProofFamily.conjIntro_minLength_polynomial
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (hA : ConcreteProofFamily Ax A) (hB : ConcreteProofFamily Ax B)
    (hApoly : is_polynomial_bound (nat_bound_as_real hA.length))
    (hBpoly : is_polynomial_bound (nat_bound_as_real hB.length)) :
    is_polynomial_bound (nat_bound_as_real (hA.conjIntro hB).minLength) :=
  (hA.conjIntro hB).minLength_polynomial_of_length_polynomial
    (hA.conjIntro_length_polynomial hB hApoly hBpoly)

theorem ConcreteProofFamily.rightConjElim_minLength_polynomial
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m))
    (hpoly : is_polynomial_bound (nat_bound_as_real h.minLength)) :
    is_polynomial_bound (nat_bound_as_real h.rightConjElim.minLength) := by
  have hpoly_add :
      is_polynomial_bound (nat_bound_as_real (fun m => h.minLength m + 2)) :=
    is_polynomial_bound_nat_add_const hpoly 2
  exact is_polynomial_bound_of_le
    (g := nat_bound_as_real (fun m => h.minLength m + 2)) (by
      intro m
      have hle : (h.rightConjElim.minLength m : ℝ) ≤ h.minLength m + 2 := by
        exact_mod_cast h.minLength_rightConjElim_le m
      simpa [nat_bound_as_real] using hle) hpoly_add

theorem ConcreteProofFamily.rightConjElim_codeSize_polynomial
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m))
    (hpoly : is_polynomial_bound (nat_bound_as_real h.codeSize)) :
    is_polynomial_bound (nat_bound_as_real h.rightConjElim.codeSize) := by
  have hpoly_add :
      is_polynomial_bound (nat_bound_as_real (fun m => h.codeSize m + 2)) :=
    is_polynomial_bound_nat_add_const hpoly 2
  rcases hpoly_add with ⟨C, k, hCk⟩
  refine ⟨C, k, ?_⟩
  intro m
  have hsize : h.rightConjElim.codeSize m = h.codeSize m + 2 :=
    h.codeSize_rightConjElim m
  simpa [nat_bound_as_real, hsize] using hCk m

structure ConcretePolynomialShortProofFamily
    (Ax : L.BoundedFormula α n → Prop) (code : ℕ → L.BoundedFormula α n)
    (accepted : ℕ → Prop) : Type (max u v w) where
  bound : ℕ → ℕ
  bound_polynomial : is_polynomial_bound (nat_bound_as_real bound)
  short_proofs : ConcreteShortProofFamily Ax code accepted bound

def ConcreteProofFamily.toPolynomialShortProofFamily
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code)
    (hpoly : is_polynomial_bound (nat_bound_as_real h.length)) :
    ConcretePolynomialShortProofFamily Ax code (fun _ => True) where
  bound := h.length
  bound_polynomial := hpoly
  short_proofs := h.toShortProofFamily

def ConcreteProofFamily.rightConjElimPolynomialShortProofFamily
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m))
    (hpoly : is_polynomial_bound (nat_bound_as_real h.length)) :
    ConcretePolynomialShortProofFamily Ax B (fun _ => True) where
  bound := h.rightConjElim.length
  bound_polynomial := h.rightConjElim_length_polynomial hpoly
  short_proofs := by
    refine {
      short_proof := ?_ }
    intro m _hm
    refine ⟨h.rightConjElim.proof m, ?_⟩
    exact le_rfl

def ConcreteProofFamily.toCodeSizePolynomialShortProofFamily
    {Ax : L.BoundedFormula α n → Prop} {code : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax code)
    (hpoly : is_polynomial_bound (nat_bound_as_real h.codeSize)) :
    ConcretePolynomialShortProofFamily Ax code (fun _ => True) where
  bound := h.codeSize
  bound_polynomial := hpoly
  short_proofs := by
    refine {
      short_proof := ?_ }
    intro m _hm
    refine ⟨h.proof m, ?_⟩
    rw [h.codeSize_eq_length m]
    exact Nat.le_refl _

def ConcreteProofFamily.rightConjElimCodeSizePolynomialShortProofFamily
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m))
    (hpoly : is_polynomial_bound (nat_bound_as_real h.codeSize)) :
    ConcretePolynomialShortProofFamily Ax B (fun _ => True) where
  bound := h.rightConjElim.codeSize
  bound_polynomial := h.rightConjElim_codeSize_polynomial hpoly
  short_proofs := by
    refine {
      short_proof := ?_ }
    intro m _hm
    refine ⟨h.rightConjElim.proof m, ?_⟩
    rw [h.rightConjElim.codeSize_eq_length m]
    exact Nat.le_refl _

theorem ConcreteProofFamily.rightConjElimPolynomialShortProofFamily_bound
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m))
    (hpoly : is_polynomial_bound (nat_bound_as_real h.length)) :
    (h.rightConjElimPolynomialShortProofFamily hpoly).bound =
      h.rightConjElim.length :=
  rfl

structure ConcreteRightConjElimPolynomialClosure
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) where
  length_closure :
    is_polynomial_bound (nat_bound_as_real h.length) →
      ConcretePolynomialShortProofFamily Ax B (fun _ => True)
  code_size_closure :
    is_polynomial_bound (nat_bound_as_real h.codeSize) →
      ConcretePolynomialShortProofFamily Ax B (fun _ => True)

def ConcreteProofFamily.rightConjElimPolynomialClosure
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) :
    ConcreteRightConjElimPolynomialClosure Ax A B h where
  length_closure := h.rightConjElimPolynomialShortProofFamily
  code_size_closure := h.rightConjElimCodeSizePolynomialShortProofFamily

structure HilbertConcreteLocalClosure
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) : Prop where
  length_exact :
    ∀ m : ℕ, h.rightConjElim.length m = h.length m + 2
  code_size_exact :
    ∀ m : ℕ, h.rightConjElim.codeSize m = h.codeSize m + 2
  length_polynomial_preserved :
    is_polynomial_bound (nat_bound_as_real h.length) →
      is_polynomial_bound (nat_bound_as_real h.rightConjElim.length)
  code_size_polynomial_preserved :
    is_polynomial_bound (nat_bound_as_real h.codeSize) →
      is_polynomial_bound (nat_bound_as_real h.rightConjElim.codeSize)

theorem ConcreteProofFamily.hilbertConcreteLocalClosure
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : ConcreteProofFamily Ax (fun m => A m ⊓ B m)) :
    HilbertConcreteLocalClosure Ax A B h where
  length_exact := h.length_rightConjElim
  code_size_exact := h.codeSize_rightConjElim
  length_polynomial_preserved := h.rightConjElim_length_polynomial
  code_size_polynomial_preserved := h.rightConjElim_codeSize_polynomial

theorem ConcreteShortProofFamily.mapAxioms
    {Ax₁ Ax₂ : L.BoundedFormula α n → Prop}
    {code : ℕ → L.BoundedFormula α n} {accepted : ℕ → Prop}
    {bound : ℕ → ℕ}
    (hAx : ∀ {φ : L.BoundedFormula α n}, Ax₁ φ → Ax₂ φ)
    (hshort : ConcreteShortProofFamily Ax₁ code accepted bound) :
    ConcreteShortProofFamily Ax₂ code accepted bound where
  short_proof := by
    intro m hm
    exact TheoryProof.hasProofOfLength_mapAxioms hAx
      (hshort.short_proof m hm)

theorem ConcreteShortProofFamily.rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n} {accepted : ℕ → Prop}
    {bound : ℕ → ℕ}
    (hshort : ConcreteShortProofFamily Ax (fun m => A m ⊓ B m) accepted bound) :
    ConcreteShortProofFamily Ax B accepted (fun m => bound m + 2) where
  short_proof := by
    intro m hm
    exact TheoryProof.hasProofOfLength_rightConjElim (A m) (B m)
      (hshort.short_proof m hm)

theorem ConcreteShortProofFamily.conjIntro
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {acceptedA acceptedB : ℕ → Prop}
    {boundA boundB : ℕ → ℕ}
    (hA : ConcreteShortProofFamily Ax A acceptedA boundA)
    (hB : ConcreteShortProofFamily Ax B acceptedB boundB) :
    ConcreteShortProofFamily Ax (fun m => A m ⊓ B m)
      (fun m => acceptedA m ∧ acceptedB m)
      (fun m => boundA m + boundB m + 1) where
  short_proof := by
    intro m hm
    exact TheoryProof.hasProofOfLength_conjIntro
      (hA.short_proof m hm.1) (hB.short_proof m hm.2)

theorem ConcreteShortProofFamily.mapAxioms_rightConjElim
    {Ax₁ Ax₂ : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n} {accepted : ℕ → Prop}
    {bound : ℕ → ℕ}
    (hAx : ∀ {φ : L.BoundedFormula α n}, Ax₁ φ → Ax₂ φ)
    (hshort :
      ConcreteShortProofFamily Ax₁ (fun m => A m ⊓ B m) accepted bound) :
    ConcreteShortProofFamily Ax₂ B accepted (fun m => bound m + 2) :=
  (hshort.mapAxioms hAx).rightConjElim

def ConcretePolynomialShortProofFamily.mapAxioms
    {Ax₁ Ax₂ : L.BoundedFormula α n → Prop}
    {code : ℕ → L.BoundedFormula α n} {accepted : ℕ → Prop}
    (hAx : ∀ {φ : L.BoundedFormula α n}, Ax₁ φ → Ax₂ φ)
    (hshort : ConcretePolynomialShortProofFamily Ax₁ code accepted) :
    ConcretePolynomialShortProofFamily Ax₂ code accepted where
  bound := hshort.bound
  bound_polynomial := hshort.bound_polynomial
  short_proofs := hshort.short_proofs.mapAxioms hAx

def ConcretePolynomialShortProofFamily.rightConjElim
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n} {accepted : ℕ → Prop}
    (hshort :
      ConcretePolynomialShortProofFamily Ax (fun m => A m ⊓ B m) accepted) :
    ConcretePolynomialShortProofFamily Ax B accepted where
  bound := fun m => hshort.bound m + 2
  bound_polynomial :=
    is_polynomial_bound_nat_add_const hshort.bound_polynomial 2
  short_proofs := hshort.short_proofs.rightConjElim

def ConcretePolynomialShortProofFamily.conjIntro
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {acceptedA acceptedB : ℕ → Prop}
    (hA : ConcretePolynomialShortProofFamily Ax A acceptedA)
    (hB : ConcretePolynomialShortProofFamily Ax B acceptedB) :
    ConcretePolynomialShortProofFamily Ax (fun m => A m ⊓ B m)
      (fun m => acceptedA m ∧ acceptedB m) where
  bound := fun m => hA.bound m + hB.bound m + 1
  bound_polynomial :=
    is_polynomial_bound_nat_add_add_const
      hA.bound_polynomial hB.bound_polynomial 1
  short_proofs := hA.short_proofs.conjIntro hB.short_proofs

def ConcretePolynomialShortProofFamily.mapAxioms_rightConjElim
    {Ax₁ Ax₂ : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n} {accepted : ℕ → Prop}
    (hAx : ∀ {φ : L.BoundedFormula α n}, Ax₁ φ → Ax₂ φ)
    (hshort :
      ConcretePolynomialShortProofFamily Ax₁ (fun m => A m ⊓ B m) accepted) :
    ConcretePolynomialShortProofFamily Ax₂ B accepted :=
  (hshort.mapAxioms hAx).rightConjElim

end MiniHilbert
