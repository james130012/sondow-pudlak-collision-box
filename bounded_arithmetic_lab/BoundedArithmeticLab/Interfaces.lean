/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lightweight bounded-arithmetic interfaces

This sidecar library is intentionally independent of the main EulerLimit
repository.  It fixes the audit-facing vocabulary for proof systems, formula
codes, proof lengths, and polynomial bounds without importing the heavy
analysis development.
-/

namespace BoundedArithmeticLab

inductive ProofSystem
  | S21
  | PA
  deriving DecidableEq, Repr

inductive ProofLengthMeasure
  | symbolSize
  | lineCount
  | bitSize
  deriving DecidableEq, Repr

inductive FormulaFamily
  | partialConsistency
  | sondowCertificateValid
  | sondowReflectionGraft
  | externalPudlak
  | sondowProduct
  | sondowLogRelation
  | sondowDecomposition
  | sondowThreePow
  | sondowPayload
  | tailOneLe
  | tailLcmDoubleLeNinePow
  | tailGeometricTailLtOne
  | tailAnalyticTailBound
  deriving DecidableEq, Repr

structure FormulaCode where
  family : FormulaFamily
  index : ℕ
  deriving DecidableEq, Repr

def partialConsistencyCode (n : ℕ) : FormulaCode :=
  { family := FormulaFamily.partialConsistency, index := n }

def sondowCertificateValidCode (n : ℕ) : FormulaCode :=
  { family := FormulaFamily.sondowCertificateValid, index := n }

def sondowReflectionGraftCode (n : ℕ) : FormulaCode :=
  { family := FormulaFamily.sondowReflectionGraft, index := n }

def externalPudlakCode (n : ℕ) : FormulaCode :=
  { family := FormulaFamily.externalPudlak, index := n }

def sondowProductCode (n : ℕ) : FormulaCode :=
  { family := FormulaFamily.sondowProduct, index := n }

def sondowLogRelationCode (n : ℕ) : FormulaCode :=
  { family := FormulaFamily.sondowLogRelation, index := n }

def sondowDecompositionCode (n : ℕ) : FormulaCode :=
  { family := FormulaFamily.sondowDecomposition, index := n }

def sondowThreePowCode (n : ℕ) : FormulaCode :=
  { family := FormulaFamily.sondowThreePow, index := n }

def sondowPayloadCode (n : ℕ) : FormulaCode :=
  { family := FormulaFamily.sondowPayload, index := n }

def tailOneLeCode (n : ℕ) : FormulaCode :=
  { family := FormulaFamily.tailOneLe, index := n }

def tailLcmDoubleLeNinePowCode (n : ℕ) : FormulaCode :=
  { family := FormulaFamily.tailLcmDoubleLeNinePow, index := n }

def tailGeometricTailLtOneCode (n : ℕ) : FormulaCode :=
  { family := FormulaFamily.tailGeometricTailLtOne, index := n }

def tailAnalyticTailBoundCode (n : ℕ) : FormulaCode :=
  { family := FormulaFamily.tailAnalyticTailBound, index := n }

theorem sondowCertificateValidCode_injective :
    Function.Injective sondowCertificateValidCode := by
  intro m n h
  have hindex := congrArg FormulaCode.index h
  simpa [sondowCertificateValidCode] using hindex

def IsPolynomialBound (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, ∃ k : ℕ, ∀ n : ℕ, f n ≤ c * ((n : ℝ) + 1) ^ k

theorem IsPolynomialBound.of_le
    {f g : ℕ → ℝ} (hfg : ∀ n : ℕ, f n ≤ g n)
    (hg : IsPolynomialBound g) :
    IsPolynomialBound f := by
  rcases hg with ⟨c, k, hg⟩
  exact ⟨c, k, fun n => (hfg n).trans (hg n)⟩

theorem IsPolynomialBound.const (C : ℝ) :
    IsPolynomialBound (fun _ : ℕ => C) := by
  refine ⟨C, 0, ?_⟩
  intro n
  simp

theorem IsPolynomialBound.natCast_id :
    IsPolynomialBound (fun n : ℕ => (n : ℝ)) := by
  refine ⟨1, 1, ?_⟩
  intro n
  have hn : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  simp [hn]

theorem IsPolynomialBound.linear_rescale
    {f : ℕ → ℝ} (hf : IsPolynomialBound f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) :
    IsPolynomialBound (fun n : ℕ => C * f n + D) := by
  rcases hf with ⟨c, k, hc⟩
  refine ⟨C * c + D, k, ?_⟩
  intro n
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    linarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]
  have hpow : (1 : ℝ) ≤ ((n : ℝ) + 1)^k :=
    one_le_pow₀ hbase
  have hmul : C * f n ≤ C * (c * ((n : ℝ) + 1)^k) :=
    mul_le_mul_of_nonneg_left (hc n) hC
  have hDpow : D ≤ D * ((n : ℝ) + 1)^k := by
    simpa using mul_le_mul_of_nonneg_left hpow hD
  calc
    C * f n + D
        ≤ C * (c * ((n : ℝ) + 1)^k) + D * ((n : ℝ) + 1)^k :=
          add_le_add hmul hDpow
    _ = (C * c + D) * ((n : ℝ) + 1)^k := by ring

theorem IsPolynomialBound.with_nonneg_coefficient
    {f : ℕ → ℝ} (hf : IsPolynomialBound f) :
    ∃ c : ℝ, ∃ k : ℕ, 0 ≤ c ∧
      ∀ n : ℕ, f n ≤ c * ((n : ℝ) + 1) ^ k := by
  rcases hf with ⟨c, k, hc⟩
  refine ⟨max c 0, k, le_max_right c 0, ?_⟩
  intro n
  have hbase_nonneg : 0 ≤ (n : ℝ) + 1 := by
    linarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]
  have hpow_nonneg : 0 ≤ ((n : ℝ) + 1) ^ k :=
    pow_nonneg hbase_nonneg k
  have hcoeff : c * ((n : ℝ) + 1) ^ k ≤
      max c 0 * ((n : ℝ) + 1) ^ k :=
    mul_le_mul_of_nonneg_right (le_max_left c 0) hpow_nonneg
  exact (hc n).trans hcoeff

theorem IsPolynomialBound.add
    {f g : ℕ → ℝ} (hf : IsPolynomialBound f) (hg : IsPolynomialBound g) :
    IsPolynomialBound (fun n : ℕ => f n + g n) := by
  rcases hf.with_nonneg_coefficient with ⟨c, k, hc_nonneg, hc⟩
  rcases hg.with_nonneg_coefficient with ⟨d, l, hd_nonneg, hd⟩
  refine ⟨c + d, max k l, ?_⟩
  intro n
  let x : ℝ := (n : ℝ) + 1
  have hx_one : (1 : ℝ) ≤ x := by
    dsimp [x]
    linarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]
  have hk_le : x ^ k ≤ x ^ max k l :=
    pow_le_pow_right₀ hx_one (Nat.le_max_left k l)
  have hl_le : x ^ l ≤ x ^ max k l :=
    pow_le_pow_right₀ hx_one (Nat.le_max_right k l)
  have hc' : c * x ^ k ≤ c * x ^ max k l :=
    mul_le_mul_of_nonneg_left hk_le hc_nonneg
  have hd' : d * x ^ l ≤ d * x ^ max k l :=
    mul_le_mul_of_nonneg_left hl_le hd_nonneg
  have hf_le : f n ≤ c * x ^ k := by
    simpa [x] using hc n
  have hg_le : g n ≤ d * x ^ l := by
    simpa [x] using hd n
  calc
    f n + g n ≤ c * x ^ k + d * x ^ l := add_le_add hf_le hg_le
    _ ≤ c * x ^ max k l + d * x ^ max k l := add_le_add hc' hd'
    _ = (c + d) * x ^ max k l := by ring

theorem IsPolynomialBound.add_const
    {f : ℕ → ℝ} (hf : IsPolynomialBound f) (C : ℝ) :
    IsPolynomialBound (fun n : ℕ => f n + C) :=
  hf.add (IsPolynomialBound.const C)

end BoundedArithmeticLab
