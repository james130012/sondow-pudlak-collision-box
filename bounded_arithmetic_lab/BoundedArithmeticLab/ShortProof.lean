/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.Interfaces

/-!
# Local short-proof construction

This file proves the short-proof side in a local proof-code semantics.  It does
not identify that local semantics with PA or S²₁; that later identification is a
separate simulation/calibration theorem.
-/

namespace BoundedArithmeticLab

universe u

structure ProofCodeSemantics (relevant : FormulaCode → Prop) where
  Code : Type u
  checks : Code → FormulaCode → Prop
  size : Code → ℕ
  complete : ∀ code : FormulaCode, relevant code → ∃ c : Code, checks c code

structure AcceptedFamily (φ : ℕ → FormulaCode) where
  accepted : ℕ → Prop

structure AcceptedProofCodeRealization
    {φ : ℕ → FormulaCode} (accepted : ℕ → Prop)
    (sem : ProofCodeSemantics (fun code => ∃ n : ℕ, φ n = code)) where
  codeOfAccepted :
    ∀ n : ℕ, accepted n → ∃ c : sem.Code, sem.checks c (φ n)

structure LocalShortProofBridge
    (φ : ℕ → FormulaCode) (accepted : ℕ → Prop) where
  sem : ProofCodeSemantics (fun code => ∃ n : ℕ, φ n = code)
  bound : ℕ → ℝ
  bound_poly : IsPolynomialBound bound
  short_of_accepted :
    ∀ n : ℕ, accepted n →
      ∃ c : sem.Code, sem.checks c (φ n) ∧ (sem.size c : ℝ) ≤ bound n

structure SizedAcceptedProofCodeRealization
    {φ : ℕ → FormulaCode} (accepted : ℕ → Prop)
    (sem : ProofCodeSemantics (fun code => ∃ n : ℕ, φ n = code))
    (bound : ℕ → ℝ) where
  bound_poly : IsPolynomialBound bound
  codeOfAccepted :
    ∀ n : ℕ, accepted n →
      ∃ c : sem.Code, sem.checks c (φ n) ∧ (sem.size c : ℝ) ≤ bound n

def SizedAcceptedProofCodeRealization.toLocalShortProofBridge
    {φ : ℕ → FormulaCode} {accepted : ℕ → Prop}
    {sem : ProofCodeSemantics (fun code => ∃ n : ℕ, φ n = code)}
    {bound : ℕ → ℝ}
    (h : SizedAcceptedProofCodeRealization accepted sem bound) :
    LocalShortProofBridge φ accepted where
  sem := sem
  bound := bound
  bound_poly := h.bound_poly
  short_of_accepted := h.codeOfAccepted

def canonicalSelfCheckingSemantics
    (φ : ℕ → FormulaCode) :
    ProofCodeSemantics (fun code => ∃ n : ℕ, φ n = code) where
  Code := ℕ
  checks := fun n code => φ n = code
  size := fun n => n + 1
  complete := by
    intro code hcode
    rcases hcode with ⟨n, rfl⟩
    exact ⟨n, rfl⟩

def canonicalSelfCheckingSemantics_realizes_accepted
    (φ : ℕ → FormulaCode) (accepted : ℕ → Prop) :
    AcceptedProofCodeRealization accepted (canonicalSelfCheckingSemantics φ) where
  codeOfAccepted := by
    intro n _hn
    exact ⟨n, rfl⟩

def canonicalSelfCheckingSemantics_sized_realizes_accepted
    (φ : ℕ → FormulaCode) (accepted : ℕ → Prop) :
    SizedAcceptedProofCodeRealization accepted
      (canonicalSelfCheckingSemantics φ)
      (fun n : ℕ => (n : ℝ) + 1) where
  bound_poly := by
    refine ⟨1, 1, ?_⟩
    intro n
    simp
  codeOfAccepted := by
    intro n _hn
    refine ⟨n, rfl, ?_⟩
    change ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1
    rw [Nat.cast_add, Nat.cast_one]

def canonicalSelfCheckingSemantics_localShortProofBridge
    (φ : ℕ → FormulaCode) (accepted : ℕ → Prop) :
    LocalShortProofBridge φ accepted :=
  (canonicalSelfCheckingSemantics_sized_realizes_accepted φ accepted)
    |>.toLocalShortProofBridge

end BoundedArithmeticLab
