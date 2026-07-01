/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.S21ProofSystem
import BoundedArithmeticLab.SystemComparison

/-!
# Verifier traces as S21 short proofs

This module mirrors the main repository's `S21VerifierTraceSoundness` and
`S21ToPALinearEmbedding` interfaces in a lightweight, repository-independent
form.
-/

namespace BoundedArithmeticLab

structure FixedVerifierEncoding
    (formula : ℕ → FormulaCode) (accepted : ℕ → Prop) where
  verifier_polytime_statement : Prop
  verifier_polytime : verifier_polytime_statement
  accepted_formula_represents_verifier_statement : Prop
  accepted_formula_represents_verifier :
    accepted_formula_represents_verifier_statement
  trace_bound : ℕ → ℝ
  trace_bound_poly : IsPolynomialBound trace_bound
  binary_numeral_encoding_statement : Prop
  binary_numeral_encoding : binary_numeral_encoding_statement
  symbol_size_encoding_statement : Prop
  symbol_size_encoding : symbol_size_encoding_statement

structure S21VerifierTraceSoundness
    (s21Box : AbstractProofLengthBox) (accepted : ℕ → Prop) where
  trace_bound : ℕ → ℝ
  trace_bound_poly : IsPolynomialBound trace_bound
  short_proof_from_accepting_trace :
    ∀ n : ℕ, accepted n → s21Box.length n ≤ trace_bound n

def S21VerifierTraceSoundness.toShortProofUpperBound
    {s21Box : AbstractProofLengthBox} {accepted : ℕ → Prop}
    (h : S21VerifierTraceSoundness s21Box accepted) :
    EventualShortProofUpperBound s21Box accepted where
  bound := h.trace_bound
  bound_poly := h.trace_bound_poly
  short_of_accepted := h.short_proof_from_accepting_trace

structure S21VerifierTraceRealization
    {s21Box : AbstractProofLengthBox} (accepted : ℕ → Prop)
    (model : ProofSystemBoxModel s21Box) where
  trace_bound : ℕ → ℝ
  trace_bound_poly : IsPolynomialBound trace_bound
  proof_of_accepted :
    ∀ n : ℕ, accepted n →
      ∃ p : model.Proof, model.proves p n ∧ (model.size p : ℝ) ≤ trace_bound n

def S21VerifierTraceRealization.toAcceptedProofFamily
    {s21Box : AbstractProofLengthBox} {accepted : ℕ → Prop}
    {model : ProofSystemBoxModel s21Box}
    (h : S21VerifierTraceRealization accepted model) :
    AcceptedProofFamily model accepted where
  bound := h.trace_bound
  bound_poly := h.trace_bound_poly
  proof_of_accepted := h.proof_of_accepted

def S21VerifierTraceRealization.toTraceSoundness
    {s21Box : AbstractProofLengthBox} {accepted : ℕ → Prop}
    {model : ProofSystemBoxModel s21Box}
    (h : S21VerifierTraceRealization accepted model) :
    S21VerifierTraceSoundness s21Box accepted where
  trace_bound := h.trace_bound
  trace_bound_poly := h.trace_bound_poly
  short_proof_from_accepting_trace := by
    intro n hn
    rcases h.proof_of_accepted n hn with ⟨p, hp, hsize⟩
    exact (model.proof_length_le_size n p hp).trans hsize

def paShortProofsOfS21TraceAndTransport
    {s21Box paBox : AbstractProofLengthBox} {accepted : ℕ → Prop}
    (htrace : S21VerifierTraceSoundness s21Box accepted)
    (htransport : ShortProofSystemTransport s21Box paBox) :
    EventualShortProofUpperBound paBox accepted :=
  htrace.toShortProofUpperBound.transport htransport

end BoundedArithmeticLab
