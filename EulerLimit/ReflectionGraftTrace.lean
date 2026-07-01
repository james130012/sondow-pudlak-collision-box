/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.Certificate

/-!
# Reflection-graft trace bridge

This module isolates the remaining metatheoretic trace-soundness input behind
the reflection-graft route.

It does not claim that PA has short proofs for accepted reflection-graft
certificates unconditionally.  Instead, it proves the exact local bridge from
S21 trace soundness plus a PA simulation bound to the already used short-proof
package.  This keeps the hard bounded-arithmetic metatheorem visible as a
small, auditable interface.
-/

theorem is_polynomial_bound_add
    {f g : ℕ → ℝ}
    (hf : is_polynomial_bound f) (hg : is_polynomial_bound g) :
    is_polynomial_bound (fun n : ℕ => f n + g n) := by
  rcases hf.nonneg_coefficient with ⟨Cf, kf, hCf, hf_bound⟩
  rcases hg.nonneg_coefficient with ⟨Cg, kg, hCg, hg_bound⟩
  refine ⟨Cf + Cg, max kf kg, ?_⟩
  intro n
  have hbase_nonneg : 0 ≤ (n : ℝ) + 1 := by
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]
  have hbase_one : 1 ≤ (n : ℝ) + 1 := by
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]
  have hpowf :
      ((n : ℝ) + 1) ^ kf ≤ ((n : ℝ) + 1) ^ max kf kg :=
    pow_le_pow_right₀ hbase_one (Nat.le_max_left kf kg)
  have hpowg :
      ((n : ℝ) + 1) ^ kg ≤ ((n : ℝ) + 1) ^ max kf kg :=
    pow_le_pow_right₀ hbase_one (Nat.le_max_right kf kg)
  have hf_le :
      f n ≤ Cf * ((n : ℝ) + 1) ^ max kf kg :=
    le_trans (hf_bound n) (mul_le_mul_of_nonneg_left hpowf hCf)
  have hg_le :
      g n ≤ Cg * ((n : ℝ) + 1) ^ max kf kg :=
    le_trans (hg_bound n) (mul_le_mul_of_nonneg_left hpowg hCg)
  calc
    f n + g n ≤
        Cf * ((n : ℝ) + 1) ^ max kf kg +
          Cg * ((n : ℝ) + 1) ^ max kf kg := by
      exact add_le_add hf_le hg_le
    _ = (Cf + Cg) * ((n : ℝ) + 1) ^ max kf kg := by
      ring

theorem is_polynomial_bound_add_const
    {f : ℕ → ℝ} (hf : is_polynomial_bound f) {C : ℝ} (hC : 0 ≤ C) :
    is_polynomial_bound (fun n : ℕ => f n + C) := by
  have hrescale :
      is_polynomial_bound (fun n : ℕ => (1 : ℝ) * f n + C) :=
    hf.linear_rescale (by norm_num) hC
  simpa using hrescale

structure ReflectionGraftTraceInputs where
  trace_soundness : S21VerifierTraceSoundness sondowReflectionGraftCode
  pa_embedding : S21ToPALinearEmbeddingOn sondowReflectionGraftCode

/-!
## Local trace-composition interface

The reflection-graft verifier accepts exactly a Sondow certificate together
with the partial-consistency payload.  The next structure isolates the proof
calculus step needed to turn those two accepted components into a short S21
proof of the grafted formula.  This is intentionally narrower than a global
bounded-arithmetic verification theorem.
-/

structure ReflectionGraftS21TraceComposition : Prop where
  compose_short_proof :
    ∀ n : ℕ,
      accepted_certificate (sondowCertificateValidCode n) →
        accepted_certificate (partialConsistencyCode n) →
          proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤
              proof_predicate_formula_size sondowReflectionGraftCode n

/-!
The following package is a concrete sufficient condition for the composition
interface above.  It separates the proof-calculus operation (S21 can introduce
the fixed graft conjunction with constant overhead) from the syntactic size
bookkeeping (the graft proof predicate is large enough to absorb both component
predicate bounds and the overhead).
-/

structure ReflectionGraftS21ConjunctionIntroduction where
  C : ℝ
  C_nonneg : 0 ≤ C
  introduce_graft :
    ∀ n : ℕ,
      accepted_certificate (sondowCertificateValidCode n) →
        accepted_certificate (partialConsistencyCode n) →
          proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
              (sondowReflectionGraftCode n) ≤
            proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
              (sondowCertificateValidCode n) +
            proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
              (partialConsistencyCode n) + C
  graft_predicate_absorbs_components :
    ∀ n : ℕ,
      proof_predicate_formula_size sondowCertificateValidCode n +
        proof_predicate_formula_size partialConsistencyCode n + C ≤
          proof_predicate_formula_size sondowReflectionGraftCode n

structure S21GraftConjunctionIntroductionCost where
  C : ℝ
  C_nonneg : 0 ≤ C
  introduce_graft :
    ∀ n : ℕ,
      accepted_certificate (sondowCertificateValidCode n) →
        accepted_certificate (partialConsistencyCode n) →
          proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
              (sondowReflectionGraftCode n) ≤
            proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
              (sondowCertificateValidCode n) +
            proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
              (partialConsistencyCode n) + C

structure S21GraftConjunctionLengthCalibration where
  C : ℝ
  C_nonneg : 0 ≤ C
  sondowLength : ℕ → ℕ
  partialLength : ℕ → ℕ
  graftLength : ℕ → ℕ
  sondow_exact :
    ∀ n : ℕ,
      proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
        (sondowCertificateValidCode n) = sondowLength n
  partial_exact :
    ∀ n : ℕ,
      proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
        (partialConsistencyCode n) = partialLength n
  graft_upper :
    ∀ n : ℕ,
      proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode n) ≤ graftLength n
  local_conj_intro :
    ∀ n : ℕ,
      (graftLength n : ℝ) ≤
        sondowLength n + partialLength n + C

def S21GraftConjunctionLengthCalibration.toCost
    (h : S21GraftConjunctionLengthCalibration) :
    S21GraftConjunctionIntroductionCost where
  C := h.C
  C_nonneg := h.C_nonneg
  introduce_graft := by
    intro n _hsondow_acc _hpartial_acc
    calc
      proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ h.graftLength n :=
        h.graft_upper n
      _ ≤ h.sondowLength n + h.partialLength n + h.C :=
        h.local_conj_intro n
      _ =
          proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
              (sondowCertificateValidCode n) +
            proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
              (partialConsistencyCode n) + h.C := by
        rw [h.sondow_exact n, h.partial_exact n]

structure S21GraftConjunctionExactLengthCalibration where
  C : ℝ
  C_nonneg : 0 ≤ C
  sondowLength : ℕ → ℕ
  partialLength : ℕ → ℕ
  graftLength : ℕ → ℕ
  sondow_exact :
    ∀ n : ℕ,
      proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
        (sondowCertificateValidCode n) = sondowLength n
  partial_exact :
    ∀ n : ℕ,
      proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
        (partialConsistencyCode n) = partialLength n
  graft_exact :
    ∀ n : ℕ,
      proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode n) = graftLength n
  local_conj_intro :
    ∀ n : ℕ,
      (graftLength n : ℝ) ≤
        sondowLength n + partialLength n + C

def S21GraftConjunctionExactLengthCalibration.toCalibration
    (h : S21GraftConjunctionExactLengthCalibration) :
    S21GraftConjunctionLengthCalibration where
  C := h.C
  C_nonneg := h.C_nonneg
  sondowLength := h.sondowLength
  partialLength := h.partialLength
  graftLength := h.graftLength
  sondow_exact := h.sondow_exact
  partial_exact := h.partial_exact
  graft_upper := by
    intro n
    rw [h.graft_exact n]
  local_conj_intro := h.local_conj_intro

def S21GraftConjunctionExactLengthCalibration.toCost
    (h : S21GraftConjunctionExactLengthCalibration) :
    S21GraftConjunctionIntroductionCost :=
  h.toCalibration.toCost

def S21GraftConjunctionLengthCalibration.ofOneStepLocalIntro
    (sondowLength partialLength graftLength : ℕ → ℕ)
    (hsondow :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = sondowLength n)
    (hpartial :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = partialLength n)
    (hgraft :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ graftLength n)
    (hlocal :
      ∀ n : ℕ,
        graftLength n ≤ sondowLength n + partialLength n + 1) :
    S21GraftConjunctionLengthCalibration where
  C := 1
  C_nonneg := by norm_num
  sondowLength := sondowLength
  partialLength := partialLength
  graftLength := graftLength
  sondow_exact := hsondow
  partial_exact := hpartial
  graft_upper := hgraft
  local_conj_intro := by
    intro n
    exact_mod_cast hlocal n

def S21GraftConjunctionExactLengthCalibration.ofOneStepLocalIntro
    (sondowLength partialLength graftLength : ℕ → ℕ)
    (hsondow :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = sondowLength n)
    (hpartial :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = partialLength n)
    (hgraft :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) = graftLength n)
    (hlocal :
      ∀ n : ℕ,
        graftLength n ≤ sondowLength n + partialLength n + 1) :
    S21GraftConjunctionExactLengthCalibration where
  C := 1
  C_nonneg := by norm_num
  sondowLength := sondowLength
  partialLength := partialLength
  graftLength := graftLength
  sondow_exact := hsondow
  partial_exact := hpartial
  graft_exact := hgraft
  local_conj_intro := by
    intro n
    exact_mod_cast hlocal n

universe s21_u s21_v s21_w

def S21GraftRelevantCode (code : FormulaCode) : Prop :=
  (∃ n : ℕ, code = sondowCertificateValidCode n) ∨
    (∃ n : ℕ, code = partialConsistencyCode n) ∨
      (∃ n : ℕ, code = sondowReflectionGraftCode n)

def s21GraftMiniHilbertLength
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (code : FormulaCode) : ℕ :=
  match code.family with
  | FormulaFamily.sondowCertificateValid => hsondow.length code.index
  | FormulaFamily.partialConsistency => hpartial.length code.index
  | FormulaFamily.sondowReflectionGraft =>
      (hsondow.conjIntro hpartial).length code.index
  | _ => 0

def s21GraftMiniHilbertProofCodeSemantics
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B) :
    ProofCodeSemantics S21GraftRelevantCode where
  Code := FormulaCode
  checks := fun c code => c = code
  size := s21GraftMiniHilbertLength hsondow hpartial
  complete := by
    intro code _hcode
    exact ⟨code, rfl⟩

theorem s21GraftMiniHilbertProofCodeSemantics_minProofCodeSize
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (code : FormulaCode) (hcode : S21GraftRelevantCode code) :
    (s21GraftMiniHilbertProofCodeSemantics hsondow hpartial).minProofCodeSize
        code hcode =
      s21GraftMiniHilbertLength hsondow hpartial code := by
  let sem := s21GraftMiniHilbertProofCodeSemantics hsondow hpartial
  apply Nat.le_antisymm
  · exact sem.minProofCodeSize_le_of_hasProofCodeOfSize hcode
      ⟨code, rfl, le_rfl⟩
  · rcases sem.hasProofCodeOfSize_minProofCodeSize hcode with
      ⟨c, hc, hc_size⟩
    subst hc
    exact hc_size

def s21GraftMiniHilbertProofLengthCodeSemantics
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B) :
    ProofLengthCodeSemantics
      ProofSystem.S21 ProofLengthMeasure.symbolSize S21GraftRelevantCode where
  proof_code_semantics :=
    s21GraftMiniHilbertProofCodeSemantics hsondow hpartial
  fallback_length := s21GraftMiniHilbertLength hsondow hpartial

theorem s21GraftMiniHilbertProofLengthCodeSemantics_length_eq
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B) :
    (s21GraftMiniHilbertProofLengthCodeSemantics hsondow hpartial).length =
      s21GraftMiniHilbertLength hsondow hpartial := by
  funext code
  by_cases hcode : S21GraftRelevantCode code
  · rw [ProofLengthCodeSemantics.length]
    rw [ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize]
    exact s21GraftMiniHilbertProofCodeSemantics_minProofCodeSize
      hsondow hpartial code hcode
  · simp [ProofLengthCodeSemantics.length,
      s21GraftMiniHilbertProofLengthCodeSemantics,
      ProofCodeSemantics.semanticProofLength, hcode]

theorem s21GraftMiniHilbertCalibration_iff_family_lengths
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B) :
    (s21GraftMiniHilbertProofLengthCodeSemantics hsondow hpartial).Calibration ↔
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (hsondow.conjIntro hpartial).length n) := by
  constructor
  · intro hcal
    refine ⟨?_, ?_, ?_⟩
    · intro n
      rw [hcal.proof_length_eq_length (sondowCertificateValidCode n)
        (Or.inl ⟨n, rfl⟩)]
      rw [s21GraftMiniHilbertProofLengthCodeSemantics_length_eq]
      rfl
    · intro n
      rw [hcal.proof_length_eq_length (partialConsistencyCode n)
        (Or.inr (Or.inl ⟨n, rfl⟩))]
      rw [s21GraftMiniHilbertProofLengthCodeSemantics_length_eq]
      rfl
    · intro n
      rw [hcal.proof_length_eq_length (sondowReflectionGraftCode n)
        (Or.inr (Or.inr ⟨n, rfl⟩))]
      rw [s21GraftMiniHilbertProofLengthCodeSemantics_length_eq]
      rfl
  · rintro ⟨hsondow_len, hpartial_len, hgraft_len⟩
    refine ⟨?_⟩
    intro code hcode
    rw [s21GraftMiniHilbertProofLengthCodeSemantics_length_eq]
    rcases hcode with ⟨n, hcode_eq⟩ | ⟨n, hcode_eq⟩ | ⟨n, hcode_eq⟩
    · subst hcode_eq
      exact hsondow_len n
    · subst hcode_eq
      exact hpartial_len n
    · subst hcode_eq
      exact hgraft_len n

theorem s21GraftMiniHilbertCalibration_of_family_lengths
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsondow_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n)
    (hpartial_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n)
    (hgraft_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (hsondow.conjIntro hpartial).length n) :
    (s21GraftMiniHilbertProofLengthCodeSemantics
      hsondow hpartial).Calibration :=
  (s21GraftMiniHilbertCalibration_iff_family_lengths
    hsondow hpartial).2 ⟨hsondow_len, hpartial_len, hgraft_len⟩

theorem s21GraftMiniHilbertProjectSemantics_iff_family_lengths
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B) :
    ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength hsondow hpartial)
        S21GraftRelevantCode ↔
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (hsondow.conjIntro hpartial).length n) := by
  constructor
  · intro hsem
    refine ⟨?_, ?_, ?_⟩
    · intro n
      rw [hsem.proof_length_eq (sondowCertificateValidCode n)
        (Or.inl ⟨n, rfl⟩)]
      rfl
    · intro n
      rw [hsem.proof_length_eq (partialConsistencyCode n)
        (Or.inr (Or.inl ⟨n, rfl⟩))]
      rfl
    · intro n
      rw [hsem.proof_length_eq (sondowReflectionGraftCode n)
        (Or.inr (Or.inr ⟨n, rfl⟩))]
      rfl
  · rintro ⟨hsondow_len, hpartial_len, hgraft_len⟩
    refine ⟨?_⟩
    intro code hcode
    rcases hcode with ⟨n, hcode_eq⟩ | ⟨n, hcode_eq⟩ | ⟨n, hcode_eq⟩
    · subst hcode_eq
      exact hsondow_len n
    · subst hcode_eq
      exact hpartial_len n
    · subst hcode_eq
      exact hgraft_len n

theorem s21GraftMiniHilbertProjectSemantics_of_family_lengths
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsondow_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n)
    (hpartial_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n)
    (hgraft_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (hsondow.conjIntro hpartial).length n) :
    ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength hsondow hpartial)
        S21GraftRelevantCode :=
  (s21GraftMiniHilbertProjectSemantics_iff_family_lengths
    hsondow hpartial).2 ⟨hsondow_len, hpartial_len, hgraft_len⟩

theorem s21GraftMiniHilbertProjectSemantics_of_minProofCodeSize
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hproof_length :
      ∀ code : FormulaCode, ∀ hcode : S21GraftRelevantCode code,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize code =
          (s21GraftMiniHilbertProofCodeSemantics hsondow hpartial).minProofCodeSize
            code hcode) :
    ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength hsondow hpartial)
        S21GraftRelevantCode :=
  ProofCodeSemantics.toProjectProofLengthSemantics
      (s21GraftMiniHilbertProofCodeSemantics hsondow hpartial)
      ProofSystem.S21 ProofLengthMeasure.symbolSize
      (s21GraftMiniHilbertLength hsondow hpartial)
      (by
        intro code hcode
        exact (s21GraftMiniHilbertProofCodeSemantics_minProofCodeSize
          hsondow hpartial code hcode).symm)
      hproof_length

theorem s21GraftMiniHilbertFamilyLengths_of_minProofCodeSize
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hproof_length :
      ∀ code : FormulaCode, ∀ hcode : S21GraftRelevantCode code,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize code =
          (s21GraftMiniHilbertProofCodeSemantics hsondow hpartial).minProofCodeSize
            code hcode) :
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (hsondow.conjIntro hpartial).length n) :=
  (s21GraftMiniHilbertProjectSemantics_iff_family_lengths
    hsondow hpartial).1
    (s21GraftMiniHilbertProjectSemantics_of_minProofCodeSize
      hsondow hpartial hproof_length)

theorem s21GraftMiniHilbert_minProofCodeSize_iff_projectSemantics
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B) :
    (∀ code : FormulaCode, ∀ hcode : S21GraftRelevantCode code,
      proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize code =
        (s21GraftMiniHilbertProofCodeSemantics hsondow hpartial).minProofCodeSize
          code hcode) ↔
    ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength hsondow hpartial)
        S21GraftRelevantCode := by
  constructor
  · exact s21GraftMiniHilbertProjectSemantics_of_minProofCodeSize
      hsondow hpartial
  · intro hsem code hcode
    rw [hsem.proof_length_eq code hcode]
    exact_mod_cast
      (s21GraftMiniHilbertProofCodeSemantics_minProofCodeSize
        hsondow hpartial code hcode).symm

theorem s21GraftMiniHilbert_minProofCodeSize_iff_family_lengths
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B) :
    (∀ code : FormulaCode, ∀ hcode : S21GraftRelevantCode code,
      proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize code =
        (s21GraftMiniHilbertProofCodeSemantics hsondow hpartial).minProofCodeSize
          code hcode) ↔
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (hsondow.conjIntro hpartial).length n) :=
  (s21GraftMiniHilbert_minProofCodeSize_iff_projectSemantics
    hsondow hpartial).trans
    (s21GraftMiniHilbertProjectSemantics_iff_family_lengths
      hsondow hpartial)

structure S21GraftProofLengthRecognitionTheorem where
  {L : FirstOrder.Language.{s21_u, s21_v}}
  {α : Type s21_w}
  {arity : ℕ}
  {Ax : L.BoundedFormula α arity → Prop}
  {A B : ℕ → L.BoundedFormula α arity}
  sondow_proofs : MiniHilbert.ConcreteProofFamily Ax A
  partial_proofs : MiniHilbert.ConcreteProofFamily Ax B
  recognizes_minProofCodeSize :
    ∀ code : FormulaCode, ∀ hcode : S21GraftRelevantCode code,
      proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize code =
        (s21GraftMiniHilbertProofCodeSemantics
          sondow_proofs partial_proofs).minProofCodeSize code hcode

theorem S21GraftProofLengthRecognitionTheorem.iff_projectSemantics
    (h : S21GraftProofLengthRecognitionTheorem) :
    ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength h.sondow_proofs h.partial_proofs)
        S21GraftRelevantCode :=
  (s21GraftMiniHilbert_minProofCodeSize_iff_projectSemantics
    h.sondow_proofs h.partial_proofs).1 h.recognizes_minProofCodeSize

theorem S21GraftProofLengthRecognitionTheorem.family_lengths
    (h : S21GraftProofLengthRecognitionTheorem) :
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = h.sondow_proofs.length n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = h.partial_proofs.length n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (h.sondow_proofs.conjIntro h.partial_proofs).length n) :=
  (s21GraftMiniHilbert_minProofCodeSize_iff_family_lengths
    h.sondow_proofs h.partial_proofs).1 h.recognizes_minProofCodeSize

def S21GraftProofLengthRecognitionTheorem.ofFamilyLengths
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hfamilies :
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (hsondow.conjIntro hpartial).length n)) :
    S21GraftProofLengthRecognitionTheorem where
  sondow_proofs := hsondow
  partial_proofs := hpartial
  recognizes_minProofCodeSize :=
    (s21GraftMiniHilbert_minProofCodeSize_iff_family_lengths
      hsondow hpartial).2 hfamilies

structure S21GraftLocalProofCodeSemanticsPackage where
  {L : FirstOrder.Language.{s21_u, s21_v}}
  {α : Type s21_w}
  {arity : ℕ}
  {Ax : L.BoundedFormula α arity → Prop}
  {A B : ℕ → L.BoundedFormula α arity}
  sondow_proofs : MiniHilbert.ConcreteProofFamily Ax A
  partial_proofs : MiniHilbert.ConcreteProofFamily Ax B
  proof_length_eq_minProofCodeSize :
    ∀ code : FormulaCode, ∀ hcode : S21GraftRelevantCode code,
      proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize code =
        (s21GraftMiniHilbertProofCodeSemantics
          sondow_proofs partial_proofs).minProofCodeSize code hcode

def S21GraftLocalProofCodeSemanticsPackage.toProjectSemantics
    (h : S21GraftLocalProofCodeSemanticsPackage) :
    ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength h.sondow_proofs h.partial_proofs)
        S21GraftRelevantCode :=
  s21GraftMiniHilbertProjectSemantics_of_minProofCodeSize
    h.sondow_proofs h.partial_proofs h.proof_length_eq_minProofCodeSize

def S21GraftConjunctionLengthCalibration.ofMiniHilbertConjIntro
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsondow_exact :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n)
    (hpartial_exact :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n)
    (hgraft_upper :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤
            (hsondow.conjIntro hpartial).length n) :
    S21GraftConjunctionLengthCalibration :=
  S21GraftConjunctionLengthCalibration.ofOneStepLocalIntro
    hsondow.length hpartial.length (hsondow.conjIntro hpartial).length
    hsondow_exact hpartial_exact hgraft_upper
    (by
      intro n
      rw [hsondow.length_conjIntro hpartial n])

def S21GraftConjunctionLengthCalibration.ofMiniHilbertProjectSemantics
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength hsondow hpartial)
        S21GraftRelevantCode) :
    S21GraftConjunctionLengthCalibration :=
  S21GraftConjunctionLengthCalibration.ofMiniHilbertConjIntro
    hsondow hpartial
    (by
      intro n
      rw [hsem.proof_length_eq (sondowCertificateValidCode n)
        (Or.inl ⟨n, rfl⟩)]
      rfl)
    (by
      intro n
      rw [hsem.proof_length_eq (partialConsistencyCode n)
        (Or.inr (Or.inl ⟨n, rfl⟩))]
      rfl)
    (by
      intro n
      rw [hsem.proof_length_eq (sondowReflectionGraftCode n)
        (Or.inr (Or.inr ⟨n, rfl⟩))]
      exact le_rfl)

def S21GraftConjunctionExactLengthCalibration.ofMiniHilbertConjIntro
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsondow_exact :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n)
    (hpartial_exact :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n)
    (hgraft_exact :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (hsondow.conjIntro hpartial).length n) :
    S21GraftConjunctionExactLengthCalibration :=
  S21GraftConjunctionExactLengthCalibration.ofOneStepLocalIntro
    hsondow.length hpartial.length (hsondow.conjIntro hpartial).length
    hsondow_exact hpartial_exact hgraft_exact
    (by
      intro n
      rw [hsondow.length_conjIntro hpartial n])

def S21GraftConjunctionExactLengthCalibration.ofMiniHilbertProjectSemantics
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength hsondow hpartial)
        S21GraftRelevantCode) :
    S21GraftConjunctionExactLengthCalibration :=
  S21GraftConjunctionExactLengthCalibration.ofMiniHilbertConjIntro
    hsondow hpartial
    (by
      intro n
      rw [hsem.proof_length_eq (sondowCertificateValidCode n)
        (Or.inl ⟨n, rfl⟩)]
      rfl)
    (by
      intro n
      rw [hsem.proof_length_eq (partialConsistencyCode n)
        (Or.inr (Or.inl ⟨n, rfl⟩))]
      rfl)
    (by
      intro n
      rw [hsem.proof_length_eq (sondowReflectionGraftCode n)
        (Or.inr (Or.inr ⟨n, rfl⟩))]
      rfl)

structure ReflectionGraftPredicateAbsorption (C : ℝ) : Prop where
  absorbs_components :
    ∀ n : ℕ,
      proof_predicate_formula_size sondowCertificateValidCode n +
        proof_predicate_formula_size partialConsistencyCode n + C ≤
          proof_predicate_formula_size sondowReflectionGraftCode n

def ReflectionGraftS21ConjunctionIntroduction.ofCostAndAbsorption
    (hcost : S21GraftConjunctionIntroductionCost)
    (habsorb : ReflectionGraftPredicateAbsorption hcost.C) :
    ReflectionGraftS21ConjunctionIntroduction where
  C := hcost.C
  C_nonneg := hcost.C_nonneg
  introduce_graft := hcost.introduce_graft
  graft_predicate_absorbs_components := habsorb.absorbs_components

theorem ReflectionGraftS21ConjunctionIntroduction.toTraceComposition
    (hgraft : ReflectionGraftS21ConjunctionIntroduction)
    (hsondow : S21VerifierTraceSoundness sondowCertificateValidCode)
    (hpartial : S21VerifierTraceSoundness partialConsistencyCode) :
    ReflectionGraftS21TraceComposition where
  compose_short_proof := by
    intro n hsondow_acc hpartial_acc
    have hintro := hgraft.introduce_graft n hsondow_acc hpartial_acc
    have hsondow_len :=
      hsondow.short_proof_from_accepting_trace n hsondow_acc
    have hpartial_len :=
      hpartial.short_proof_from_accepting_trace n hpartial_acc
    have hsum :
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
            (sondowCertificateValidCode n) +
          proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
            (partialConsistencyCode n) + hgraft.C ≤
        proof_predicate_formula_size sondowCertificateValidCode n +
          proof_predicate_formula_size partialConsistencyCode n + hgraft.C := by
      linarith
    exact le_trans hintro
      (le_trans hsum (hgraft.graft_predicate_absorbs_components n))

theorem ReflectionGraftS21TraceComposition.toTraceSoundness
    (h : ReflectionGraftS21TraceComposition) :
    S21VerifierTraceSoundness sondowReflectionGraftCode where
  short_proof_from_accepting_trace := by
    intro n hacc
    exact h.compose_short_proof n
      (accepted_sondow_certificate_of_reflection_graft hacc)
      (accepted_partial_consistency_of_reflection_graft hacc)

def ReflectionGraftTraceInputs.ofComposition
    (hcompose : ReflectionGraftS21TraceComposition)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftTraceInputs where
  trace_soundness := hcompose.toTraceSoundness
  pa_embedding := hembed

theorem ReflectionGraftS21TraceComposition.accepted_certificates_have_short_proofs
    (hcompose : ReflectionGraftS21TraceComposition)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n :=
  reflection_graft_short_proof_bridge_of_trace_soundness_and_linear_embedding
    hcompose.toTraceSoundness hembed
    |>.accepted_certificates_have_short_proofs

def AcceptedCertificateS21TraceRealization.ofReflectionGraftComposition
    (hsem : AcceptedCertificateCodeSemantics sondowReflectionGraftCode)
    (hcompose : ReflectionGraftS21TraceComposition) :
    AcceptedCertificateS21TraceRealization sondowReflectionGraftCode :=
  AcceptedCertificateS21TraceRealization.ofTraceSoundness
    hsem hcompose.toTraceSoundness

theorem reflection_graft_collapse_package_of_forward_inputs_trace_composition_and_embedding
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hcompose : ReflectionGraftS21TraceComposition)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftCollapsePackage :=
  reflection_graft_collapse_package_of_forward_inputs_trace_soundness_and_embedding
    hfwd hpayload hcompose.toTraceSoundness hembed

structure ReflectionGraftComponentTraceInputs where
  sondow_trace : S21VerifierTraceSoundness sondowCertificateValidCode
  partial_consistency_trace : S21VerifierTraceSoundness partialConsistencyCode
  graft_intro : ReflectionGraftS21ConjunctionIntroduction
  pa_embedding : S21ToPALinearEmbeddingOn sondowReflectionGraftCode

structure ReflectionGraftDirectTraceInputs where
  sondow_trace : S21VerifierTraceSoundness sondowCertificateValidCode
  partial_consistency_trace : S21VerifierTraceSoundness partialConsistencyCode
  graft_cost : S21GraftConjunctionIntroductionCost
  pa_embedding : S21ToPALinearEmbeddingOn sondowReflectionGraftCode

def ReflectionGraftDirectTraceInputs.ofGlobalTraceAndCost
    (htrace : S21VerifierTracePackage)
    (hcost : S21GraftConjunctionIntroductionCost)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftDirectTraceInputs where
  sondow_trace :=
    htrace.trace_soundness
      sondowCertificateValidCode fixed_verifier_encoding_sondowCertificateValidCode
  partial_consistency_trace :=
    htrace.trace_soundness
      partialConsistencyCode fixed_verifier_encoding_partialConsistencyCode
  graft_cost := hcost
  pa_embedding := hembed

def ReflectionGraftComponentTraceInputs.graftComposition
    (h : ReflectionGraftComponentTraceInputs) :
    ReflectionGraftS21TraceComposition :=
  h.graft_intro.toTraceComposition h.sondow_trace h.partial_consistency_trace

def ReflectionGraftComponentTraceInputs.toDirectTraceInputs
    (h : ReflectionGraftComponentTraceInputs) :
    ReflectionGraftDirectTraceInputs where
  sondow_trace := h.sondow_trace
  partial_consistency_trace := h.partial_consistency_trace
  graft_cost := {
    C := h.graft_intro.C
    C_nonneg := h.graft_intro.C_nonneg
    introduce_graft := h.graft_intro.introduce_graft }
  pa_embedding := h.pa_embedding

def ReflectionGraftComponentTraceInputs.ofCostAndAbsorption
    (hsondow : S21VerifierTraceSoundness sondowCertificateValidCode)
    (hpartial : S21VerifierTraceSoundness partialConsistencyCode)
    (hcost : S21GraftConjunctionIntroductionCost)
    (habsorb : ReflectionGraftPredicateAbsorption hcost.C)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftComponentTraceInputs where
  sondow_trace := hsondow
  partial_consistency_trace := hpartial
  graft_intro :=
    ReflectionGraftS21ConjunctionIntroduction.ofCostAndAbsorption
      hcost habsorb
  pa_embedding := hembed

def ReflectionGraftComponentTraceInputs.ofGlobalTraceCostAndAbsorption
    (htrace : S21VerifierTracePackage)
    (hcost : S21GraftConjunctionIntroductionCost)
    (habsorb : ReflectionGraftPredicateAbsorption hcost.C)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftComponentTraceInputs :=
  ReflectionGraftComponentTraceInputs.ofCostAndAbsorption
    (htrace.trace_soundness
      sondowCertificateValidCode fixed_verifier_encoding_sondowCertificateValidCode)
    (htrace.trace_soundness
      partialConsistencyCode fixed_verifier_encoding_partialConsistencyCode)
    hcost habsorb hembed

theorem ReflectionGraftDirectTraceInputs.s21_short_proofs_direct
    (h : ReflectionGraftDirectTraceInputs) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n := by
  let f : ℕ → ℝ := fun n =>
    proof_predicate_formula_size sondowCertificateValidCode n +
      proof_predicate_formula_size partialConsistencyCode n +
        h.graft_cost.C
  have hf_poly : is_polynomial_bound f := by
    have hsondow_poly :
        is_polynomial_bound
          (proof_predicate_formula_size sondowCertificateValidCode) :=
      fixed_verifier_encoding_sondowCertificateValidCode
        |>.proof_predicate_polynomial.predicate_polynomial
    have hpartial_poly :
        is_polynomial_bound
          (proof_predicate_formula_size partialConsistencyCode) :=
      fixed_verifier_encoding_partialConsistencyCode
        |>.proof_predicate_polynomial.predicate_polynomial
    have hsum :
        is_polynomial_bound (fun n : ℕ =>
          proof_predicate_formula_size sondowCertificateValidCode n +
            proof_predicate_formula_size partialConsistencyCode n) :=
      is_polynomial_bound_add hsondow_poly hpartial_poly
    exact is_polynomial_bound_add_const hsum h.graft_cost.C_nonneg
  refine ⟨f, hf_poly, ?_⟩
  intro n hacc
  have hsondow_acc := accepted_sondow_certificate_of_reflection_graft hacc
  have hpartial_acc := accepted_partial_consistency_of_reflection_graft hacc
  have hintro :=
    h.graft_cost.introduce_graft n hsondow_acc hpartial_acc
  have hsondow_len :=
    h.sondow_trace.short_proof_from_accepting_trace n hsondow_acc
  have hpartial_len :=
    h.partial_consistency_trace.short_proof_from_accepting_trace n hpartial_acc
  have hsum :
      proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) +
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) + h.graft_cost.C ≤ f n := by
    dsimp [f]
    linarith
  exact le_trans hintro hsum

theorem ReflectionGraftDirectTraceInputs.toShortProofBridge
    (h : ReflectionGraftDirectTraceInputs) :
    ReflectionGraftShortProofBridge where
  accepted_certificates_have_short_proofs :=
    pa_short_proofs_of_s21_short_proofs_and_embedding_on
      h.pa_embedding h.s21_short_proofs_direct

theorem ReflectionGraftDirectTraceInputs.eventual_accepted_reflection_graft_of_rationality
    (_h : ReflectionGraftDirectTraceInputs)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      accepted_certificate (sondowReflectionGraftCode n) := by
  rcases h_rat with ⟨q, hq⟩
  rcases (reflection_graft_certificate_inputs hfwd hpayload hq).accepted_eventual with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact ⟨q, hN n hn⟩

theorem ReflectionGraftDirectTraceInputs.eventual_short_proofs_of_rationality
    (h : ReflectionGraftDirectTraceInputs)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n := by
  rcases h.toShortProofBridge.accepted_certificates_have_short_proofs with
    ⟨f, hf_poly, hf_bound⟩
  rcases h.eventual_accepted_reflection_graft_of_rationality
      hfwd hpayload h_rat with ⟨N, hN⟩
  refine ⟨f, hf_poly, N, ?_⟩
  intro n hn
  have hacc := hN n hn
  exact ⟨hacc, hf_bound n hacc⟩

theorem reflection_graft_eventual_short_proofs_of_global_trace_cost_and_rationality
    (htrace : S21VerifierTracePackage)
    (hcost : S21GraftConjunctionIntroductionCost)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n :=
  (ReflectionGraftDirectTraceInputs.ofGlobalTraceAndCost
    htrace hcost hembed).eventual_short_proofs_of_rationality
      hfwd hpayload h_rat

theorem reflection_graft_eventual_short_proofs_of_global_trace_calibration_and_rationality
    (htrace : S21VerifierTracePackage)
    (hcal : S21GraftConjunctionLengthCalibration)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n :=
  reflection_graft_eventual_short_proofs_of_global_trace_cost_and_rationality
    htrace hcal.toCost hembed hfwd hpayload h_rat

theorem reflection_graft_eventual_short_proofs_of_global_trace_exact_calibration_and_rationality
    (htrace : S21VerifierTracePackage)
    (hcal : S21GraftConjunctionExactLengthCalibration)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n :=
  reflection_graft_eventual_short_proofs_of_global_trace_calibration_and_rationality
    htrace hcal.toCalibration hembed hfwd hpayload h_rat

theorem reflection_graft_eventual_short_proofs_of_minihilbert_project_semantics_and_rationality
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength hsondow hpartial)
        S21GraftRelevantCode)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n :=
  reflection_graft_eventual_short_proofs_of_global_trace_calibration_and_rationality
    htrace
    (S21GraftConjunctionLengthCalibration.ofMiniHilbertProjectSemantics
      hsondow hpartial hsem)
    hembed hfwd hpayload h_rat

theorem reflection_graft_eventual_short_proofs_of_minihilbert_code_semantics_and_rationality
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (model :
      ProofLengthCodeSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize S21GraftRelevantCode)
    (hmodel_length :
      model.length = s21GraftMiniHilbertLength hsondow hpartial)
    (hcal : model.Calibration)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n := by
  apply reflection_graft_eventual_short_proofs_of_minihilbert_project_semantics_and_rationality
    hsondow hpartial
  · rw [← hmodel_length]
    exact hcal.toProjectProofLengthSemantics
  · exact htrace
  · exact hembed
  · exact hfwd
  · exact hpayload
  · exact h_rat

theorem reflection_graft_short_proofs_of_minihilbert_canonical_code_semantics
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hcal :
      (s21GraftMiniHilbertProofLengthCodeSemantics hsondow hpartial).Calibration)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n :=
  reflection_graft_eventual_short_proofs_of_minihilbert_code_semantics_and_rationality
    hsondow hpartial
    (s21GraftMiniHilbertProofLengthCodeSemantics hsondow hpartial)
    (s21GraftMiniHilbertProofLengthCodeSemantics_length_eq hsondow hpartial)
    hcal htrace hembed hfwd hpayload h_rat

structure S21GraftCanonicalCalibrationPackage where
  {L : FirstOrder.Language.{s21_u, s21_v}}
  {α : Type s21_w}
  {arity : ℕ}
  {Ax : L.BoundedFormula α arity → Prop}
  {A B : ℕ → L.BoundedFormula α arity}
  sondow_proofs : MiniHilbert.ConcreteProofFamily Ax A
  partial_proofs : MiniHilbert.ConcreteProofFamily Ax B
  calibration :
    (s21GraftMiniHilbertProofLengthCodeSemantics
      sondow_proofs partial_proofs).Calibration

def S21GraftCanonicalCalibrationPackage.ofFamilyLengths
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsondow_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n)
    (hpartial_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n)
    (hgraft_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (hsondow.conjIntro hpartial).length n) :
    S21GraftCanonicalCalibrationPackage where
  sondow_proofs := hsondow
  partial_proofs := hpartial
  calibration :=
    s21GraftMiniHilbertCalibration_of_family_lengths
      hsondow hpartial hsondow_len hpartial_len hgraft_len

def S21GraftLocalProofCodeSemanticsPackage.toCanonicalCalibrationPackage
    (h : S21GraftLocalProofCodeSemanticsPackage) :
    S21GraftCanonicalCalibrationPackage where
  sondow_proofs := h.sondow_proofs
  partial_proofs := h.partial_proofs
  calibration :=
    (s21GraftMiniHilbertCalibration_iff_family_lengths
      h.sondow_proofs h.partial_proofs).2
      (s21GraftMiniHilbertFamilyLengths_of_minProofCodeSize
        h.sondow_proofs h.partial_proofs h.proof_length_eq_minProofCodeSize)

theorem S21GraftCanonicalCalibrationPackage.toShortProofs
    (h : S21GraftCanonicalCalibrationPackage)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n :=
  reflection_graft_short_proofs_of_minihilbert_canonical_code_semantics
    h.sondow_proofs h.partial_proofs h.calibration
    htrace hembed hfwd hpayload h_rat

theorem S21GraftCanonicalCalibrationPackage.toShortProofBridge
    (h : S21GraftCanonicalCalibrationPackage)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftShortProofBridge := by
  have hsem :
      ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength h.sondow_proofs h.partial_proofs)
        S21GraftRelevantCode := by
    rw [← s21GraftMiniHilbertProofLengthCodeSemantics_length_eq
      h.sondow_proofs h.partial_proofs]
    exact h.calibration.toProjectProofLengthSemantics
  exact
    (ReflectionGraftDirectTraceInputs.ofGlobalTraceAndCost
      htrace
      (S21GraftConjunctionLengthCalibration.ofMiniHilbertProjectSemantics
        h.sondow_proofs h.partial_proofs hsem).toCost
      hembed).toShortProofBridge

theorem S21GraftCanonicalCalibrationPackage.accepted_certificates_have_short_proofs
    (h : S21GraftCanonicalCalibrationPackage)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n :=
  (h.toShortProofBridge htrace hembed).accepted_certificates_have_short_proofs

theorem S21GraftLocalProofCodeSemanticsPackage.toShortProofBridge
    (h : S21GraftLocalProofCodeSemanticsPackage)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftShortProofBridge :=
  h.toCanonicalCalibrationPackage.toShortProofBridge htrace hembed

theorem S21GraftLocalProofCodeSemanticsPackage.s21_short_proofs
    (h : S21GraftLocalProofCodeSemanticsPackage)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n :=
  (ReflectionGraftDirectTraceInputs.ofGlobalTraceAndCost
    htrace
    (S21GraftConjunctionLengthCalibration.ofMiniHilbertProjectSemantics
      h.sondow_proofs h.partial_proofs h.toProjectSemantics).toCost
    hembed).s21_short_proofs_direct

theorem S21GraftLocalProofCodeSemanticsPackage.accepted_certificates_have_short_proofs
    (h : S21GraftLocalProofCodeSemanticsPackage)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n :=
  (h.toShortProofBridge htrace hembed).accepted_certificates_have_short_proofs

theorem S21GraftLocalProofCodeSemanticsPackage.eventual_short_proofs_of_rationality
    (h : S21GraftLocalProofCodeSemanticsPackage)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n :=
  h.toCanonicalCalibrationPackage.toShortProofs
    htrace hembed hfwd hpayload h_rat

def S21GraftProofLengthRecognitionTheorem.toLocalProofCodeSemanticsPackage
    (h : S21GraftProofLengthRecognitionTheorem) :
    S21GraftLocalProofCodeSemanticsPackage where
  sondow_proofs := h.sondow_proofs
  partial_proofs := h.partial_proofs
  proof_length_eq_minProofCodeSize := h.recognizes_minProofCodeSize

theorem S21GraftProofLengthRecognitionTheorem.toShortProofBridge
    (h : S21GraftProofLengthRecognitionTheorem)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftShortProofBridge :=
  h.toLocalProofCodeSemanticsPackage.toShortProofBridge htrace hembed

theorem S21GraftProofLengthRecognitionTheorem.s21_short_proofs
    (h : S21GraftProofLengthRecognitionTheorem)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n :=
  h.toLocalProofCodeSemanticsPackage.s21_short_proofs htrace hembed

theorem S21GraftProofLengthRecognitionTheorem.accepted_certificates_have_short_proofs
    (h : S21GraftProofLengthRecognitionTheorem)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n :=
  h.toLocalProofCodeSemanticsPackage.accepted_certificates_have_short_proofs
    htrace hembed

theorem S21GraftProofLengthRecognitionTheorem.eventual_short_proofs_of_rationality
    (h : S21GraftProofLengthRecognitionTheorem)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n :=
  h.toLocalProofCodeSemanticsPackage.eventual_short_proofs_of_rationality
    htrace hembed hfwd hpayload h_rat

theorem reflection_graft_short_proof_bridge_of_family_lengths
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsondow_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n)
    (hpartial_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n)
    (hgraft_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (hsondow.conjIntro hpartial).length n)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftShortProofBridge :=
  (S21GraftCanonicalCalibrationPackage.ofFamilyLengths
    hsondow hpartial hsondow_len hpartial_len hgraft_len).toShortProofBridge
      htrace hembed

theorem reflection_graft_short_proof_bridge_of_project_semantics
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength hsondow hpartial)
        S21GraftRelevantCode)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftShortProofBridge :=
  (ReflectionGraftDirectTraceInputs.ofGlobalTraceAndCost
    htrace
    (S21GraftConjunctionLengthCalibration.ofMiniHilbertProjectSemantics
      hsondow hpartial hsem).toCost
    hembed).toShortProofBridge

theorem reflection_graft_s21_short_proofs_of_family_lengths
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsondow_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n)
    (hpartial_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n)
    (hgraft_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (hsondow.conjIntro hpartial).length n)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n := by
  have hsem :
      ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength hsondow hpartial)
        S21GraftRelevantCode :=
    s21GraftMiniHilbertProjectSemantics_of_family_lengths
      hsondow hpartial hsondow_len hpartial_len hgraft_len
  exact
    (ReflectionGraftDirectTraceInputs.ofGlobalTraceAndCost
      htrace
      (S21GraftConjunctionLengthCalibration.ofMiniHilbertProjectSemantics
        hsondow hpartial hsem).toCost
      hembed).s21_short_proofs_direct

theorem reflection_graft_s21_short_proofs_of_project_semantics
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength hsondow hpartial)
        S21GraftRelevantCode)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n :=
  (ReflectionGraftDirectTraceInputs.ofGlobalTraceAndCost
    htrace
    (S21GraftConjunctionLengthCalibration.ofMiniHilbertProjectSemantics
      hsondow hpartial hsem).toCost
    hembed).s21_short_proofs_direct

theorem reflection_graft_accepted_short_proofs_of_family_lengths
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsondow_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n)
    (hpartial_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n)
    (hgraft_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (hsondow.conjIntro hpartial).length n)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n :=
  (reflection_graft_short_proof_bridge_of_family_lengths
    hsondow hpartial hsondow_len hpartial_len hgraft_len htrace hembed)
      |>.accepted_certificates_have_short_proofs

theorem reflection_graft_accepted_short_proofs_of_project_semantics
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength hsondow hpartial)
        S21GraftRelevantCode)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n :=
  (reflection_graft_short_proof_bridge_of_project_semantics
    hsondow hpartial hsem htrace hembed)
      |>.accepted_certificates_have_short_proofs

theorem reflection_graft_eventual_short_proofs_of_family_lengths_and_rationality
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsondow_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) = hsondow.length n)
    (hpartial_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = hpartial.length n)
    (hgraft_len :
      ∀ n : ℕ,
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) =
            (hsondow.conjIntro hpartial).length n)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n :=
  (S21GraftCanonicalCalibrationPackage.ofFamilyLengths
    hsondow hpartial hsondow_len hpartial_len hgraft_len).toShortProofs
      htrace hembed hfwd hpayload h_rat

theorem reflection_graft_eventual_short_proofs_of_project_semantics_and_rationality
    {L : FirstOrder.Language.{s21_u, s21_v}} {α : Type s21_w} {arity : ℕ}
    {Ax : L.BoundedFormula α arity → Prop}
    {A B : ℕ → L.BoundedFormula α arity}
    (hsondow : MiniHilbert.ConcreteProofFamily Ax A)
    (hpartial : MiniHilbert.ConcreteProofFamily Ax B)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.S21 ProofLengthMeasure.symbolSize
        (s21GraftMiniHilbertLength hsondow hpartial)
        S21GraftRelevantCode)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n := by
  rcases reflection_graft_accepted_short_proofs_of_project_semantics
      hsondow hpartial hsem htrace hembed with
    ⟨f, hf_poly, hf_bound⟩
  rcases ReflectionGraftDirectTraceInputs.eventual_accepted_reflection_graft_of_rationality
      (ReflectionGraftDirectTraceInputs.ofGlobalTraceAndCost
        htrace
        (S21GraftConjunctionLengthCalibration.ofMiniHilbertProjectSemantics
          hsondow hpartial hsem).toCost
        hembed)
      hfwd hpayload h_rat with
    ⟨N, hN⟩
  refine ⟨f, hf_poly, N, ?_⟩
  intro n hn
  have hacc := hN n hn
  exact ⟨hacc, hf_bound n hacc⟩

def ReflectionGraftComponentTraceInputs.toTraceInputs
    (h : ReflectionGraftComponentTraceInputs) :
    ReflectionGraftTraceInputs :=
  ReflectionGraftTraceInputs.ofComposition h.graftComposition h.pa_embedding

theorem ReflectionGraftComponentTraceInputs.toShortProofBridge
    (h : ReflectionGraftComponentTraceInputs) :
    ReflectionGraftShortProofBridge :=
  reflection_graft_short_proof_bridge_of_trace_soundness_and_linear_embedding
    h.graftComposition.toTraceSoundness h.pa_embedding

theorem ReflectionGraftComponentTraceInputs.s21_short_proofs_direct
    (h : ReflectionGraftComponentTraceInputs) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n :=
  h.toDirectTraceInputs.s21_short_proofs_direct

theorem ReflectionGraftComponentTraceInputs.toShortProofBridgeDirect
    (h : ReflectionGraftComponentTraceInputs) :
    ReflectionGraftShortProofBridge :=
  h.toDirectTraceInputs.toShortProofBridge

theorem ReflectionGraftComponentTraceInputs.toCollapsePackage
    (h : ReflectionGraftComponentTraceInputs)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs) :
    ReflectionGraftCollapsePackage :=
  reflection_graft_collapse_package_of_forward_inputs_trace_composition_and_embedding
    hfwd hpayload h.graftComposition h.pa_embedding

theorem ReflectionGraftComponentTraceInputs.eventual_accepted_reflection_graft_of_rationality
    (_h : ReflectionGraftComponentTraceInputs)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      accepted_certificate (sondowReflectionGraftCode n) := by
  rcases h_rat with ⟨q, hq⟩
  rcases (reflection_graft_certificate_inputs hfwd hpayload hq).accepted_eventual with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact ⟨q, hN n hn⟩

theorem ReflectionGraftComponentTraceInputs.eventual_short_proofs_of_rationality
    (h : ReflectionGraftComponentTraceInputs)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n := by
  rcases h.toShortProofBridgeDirect.accepted_certificates_have_short_proofs with
    ⟨f, hf_poly, hf_bound⟩
  rcases h.eventual_accepted_reflection_graft_of_rationality
      hfwd hpayload h_rat with ⟨N, hN⟩
  refine ⟨f, hf_poly, N, ?_⟩
  intro n hn
  have hacc := hN n hn
  exact ⟨hacc, hf_bound n hacc⟩

def ReflectionGraftTraceInputs.toConcreteVerification
    (h : ReflectionGraftTraceInputs) :
    ReflectionGraftConcreteVerificationPackage where
  trace_soundness := h.trace_soundness
  pa_embedding := h.pa_embedding

theorem ReflectionGraftTraceInputs.toShortProofBridge
    (h : ReflectionGraftTraceInputs) :
    ReflectionGraftShortProofBridge :=
  h.toConcreteVerification.toShortProofBridge

theorem ReflectionGraftTraceInputs.accepted_certificates_have_short_proofs
    (h : ReflectionGraftTraceInputs) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n :=
  h.toShortProofBridge.accepted_certificates_have_short_proofs

theorem ReflectionGraftTraceInputs.eventual_accepted_reflection_graft_of_rationality
    (_h : ReflectionGraftTraceInputs)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      accepted_certificate (sondowReflectionGraftCode n) := by
  rcases h_rat with ⟨q, hq⟩
  rcases (reflection_graft_certificate_inputs hfwd hpayload hq).accepted_eventual with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact ⟨q, hN n hn⟩

theorem ReflectionGraftTraceInputs.eventual_short_proofs_of_rationality
    (h : ReflectionGraftTraceInputs)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n := by
  rcases h.accepted_certificates_have_short_proofs with ⟨f, hf_poly, hf_bound⟩
  rcases h.eventual_accepted_reflection_graft_of_rationality
      hfwd hpayload h_rat with ⟨N, hN⟩
  refine ⟨f, hf_poly, N, ?_⟩
  intro n hn
  have hacc := hN n hn
  exact ⟨hacc, hf_bound n hacc⟩

theorem ReflectionGraftTraceInputs.toCollapsePackage
    (h : ReflectionGraftTraceInputs)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs) :
    ReflectionGraftCollapsePackage :=
  reflection_graft_collapse_package_of_forward_inputs_trace_soundness_and_embedding
    hfwd hpayload h.trace_soundness h.pa_embedding

def ReflectionGraftTraceInputs.ofGlobal
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbedding) :
    ReflectionGraftTraceInputs where
  trace_soundness :=
    htrace.trace_soundness
      sondowReflectionGraftCode fixed_verifier_encoding_sondowReflectionGraftCode
  pa_embedding := hembed.on sondowReflectionGraftCode

def ReflectionGraftTraceInputs.ofTraceRealization
    (hrealize : AcceptedCertificateS21TraceRealization sondowReflectionGraftCode)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftTraceInputs where
  trace_soundness := hrealize.toS21VerifierTraceSoundness
  pa_embedding := hembed

theorem ReflectionGraftTraceInputs.short_proofs_of_trace_realization
    (hrealize : AcceptedCertificateS21TraceRealization sondowReflectionGraftCode)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n :=
  (ReflectionGraftTraceInputs.ofTraceRealization hrealize hembed)
    |>.accepted_certificates_have_short_proofs

structure ReflectionGraftTraceMetatheorem where
  trace_inputs : ReflectionGraftTraceInputs

def ReflectionGraftTraceMetatheorem.ofGlobal
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbedding) :
    ReflectionGraftTraceMetatheorem where
  trace_inputs := ReflectionGraftTraceInputs.ofGlobal htrace hembed

def ReflectionGraftTraceMetatheorem.ofTraceRealization
    (hrealize : AcceptedCertificateS21TraceRealization sondowReflectionGraftCode)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftTraceMetatheorem where
  trace_inputs := ReflectionGraftTraceInputs.ofTraceRealization hrealize hembed

theorem ReflectionGraftTraceMetatheorem.toShortProofBridge
    (h : ReflectionGraftTraceMetatheorem) :
    ReflectionGraftShortProofBridge :=
  h.trace_inputs.toShortProofBridge

theorem ReflectionGraftTraceMetatheorem.eventual_short_proofs_of_rationality
    (h : ReflectionGraftTraceMetatheorem)
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n :=
  h.trace_inputs.eventual_short_proofs_of_rationality
    hfwd hpayload h_rat

def ReflectionGraftTraceMetatheorem.toConcreteVerification
    (h : ReflectionGraftTraceMetatheorem) :
    ReflectionGraftConcreteVerificationPackage :=
  h.trace_inputs.toConcreteVerification
