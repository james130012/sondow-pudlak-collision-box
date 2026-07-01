/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.Analytic
import EulerLimit.LCMAsymptoticBridge
import EulerLimit.SondowDecomposition

/-!
# Sondow forward-input reproof adapters

This module connects the Lean-closed sidecar-shaped Sondow product-log and
decomposition reproofs back to the exact main-library `SondowForwardInputs`
interface.
-/

open BigOperators

noncomputable section

theorem nestedSondowProductNormalized_d_eq_sondow_S_explicit (n : ℕ) :
    EulerLimit.SondowProductLog.nestedSondowProductNormalized (d (2 * n)) n =
      sondow_S_explicit n := by
  rfl

theorem rawLLogSum_eq_sondow_L (n : ℕ) :
    EulerLimit.SondowProductLog.rawLLogSum n = sondow_L n := by
  unfold EulerLimit.SondowProductLog.rawLLogSum sondow_L
    EulerLimit.SondowProductLog.alternatingTermReal
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i < j := (Finset.mem_filter.mp hj).2
  apply Finset.sum_congr rfl
  intro k _hk
  have hsub : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by
    exact Nat.cast_sub (Nat.le_of_lt hij)
  have hlog :
      (((n + i + k : ℕ) : ℝ)) = (n : ℝ) + (i : ℝ) + (k : ℝ) := by
    norm_num [Nat.cast_add]
  rw [hsub, hlog]

theorem originalSondowIntegral_eq_I (n : ℕ) :
    EulerLimit.SondowDecomposition.originalSondowIntegral n = I n := by
  rfl

theorem diagonalARat_eq_A_rat (n : ℕ) :
    EulerLimit.SondowDecomposition.diagonalARat n = A_rat n := by
  unfold EulerLimit.SondowDecomposition.diagonalARat A_rat harmonic_rat
  apply Finset.sum_congr rfl
  intro i _hi
  rw [EulerLimit.SondowCoefficient.harmonicRat_eq_harmonic]

theorem diagonalAReal_eq_A_rat_cast (n : ℕ) :
    EulerLimit.SondowDecomposition.diagonalAReal n = (A_rat n : ℝ) := by
  rw [EulerLimit.SondowDecomposition.diagonalAReal_eq_diagonalARat_cast]
  rw [diagonalARat_eq_A_rat]

theorem denominatorCancelsFor_d_two_mul (n : ℕ) :
    EulerLimit.SondowProductLog.denominatorCancelsFor (d (2 * n)) n := by
  intro i j hj
  exact sondow_S_explicit_exponent_denominator_cancel hj

theorem sondow_explicit_product_log_relation_prop_reproof
    (n : ℕ) :
    sondow_explicit_product_log_relation_prop n := by
  have h :=
    EulerLimit.SondowProductLog.log_nestedSondowProductNormalized_eq_scale_rawLLogSum
      (scale := d (2 * n)) (n := n) (denominatorCancelsFor_d_two_mul n)
  simpa [sondow_explicit_product_log_relation_prop,
    nestedSondowProductNormalized_d_eq_sondow_S_explicit,
    rawLLogSum_eq_sondow_L] using h

theorem sondow_explicit_decomposition_prop_reproof
    {n : ℕ} (hn : 1 ≤ n) :
    sondow_explicit_decomposition_prop n := by
  have h := EulerLimit.SondowDecomposition.rawSondowDecompositionTarget_holds hn
  simpa [sondow_explicit_decomposition_prop,
    EulerLimit.SondowDecomposition.rawSondowDecompositionTarget,
    originalSondowIntegral_eq_I, rawLLogSum_eq_sondow_L,
    diagonalAReal_eq_A_rat_cast, euler_mascheroni] using h

/-- Lean-closed replacement for the three external Sondow forward inputs. -/
def SondowForwardInputs.of_reproof : SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_unconditional
  product_log := fun n _hn => sondow_explicit_product_log_relation_prop_reproof n
  decomposition := fun _n hn => sondow_explicit_decomposition_prop_reproof hn

/-- The reproved three-input package gives the explicit Sondow forward identity. -/
theorem sondow_identity_explicit_eventual_of_rational_reproof
    (h_rat : is_rational euler_mascheroni) :
    sondow_identity_explicit_eventual :=
  sondow_identity_explicit_eventual_of_rational_forward_inputs
    SondowForwardInputs.of_reproof h_rat

/-- The reproved three-input package gives the main Sondow forward identity. -/
theorem sondow_identity_eventual_of_rational_reproof
    (h_rat : is_rational euler_mascheroni) :
    sondow_identity_eventual :=
  sondow_identity_eventual_of_rational_forward_inputs
    SondowForwardInputs.of_reproof h_rat

end
