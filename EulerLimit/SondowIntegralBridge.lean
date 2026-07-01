/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import Mathlib

/-!
# Sondow integral bridge

This module isolates the analytic kernel identity needed to connect the
original Sondow double integral with the closed kernel-moment expansion in
`SondowDecomposition`.
-/

namespace EulerLimit.SondowIntegralBridge

open Filter MeasureTheory Set

open scoped Topology

noncomputable section

/--
Laplace-log kernel in exponential form. For `0 < z < 1`, the exponential tail
on the positive half-line integrates to `-1 / log z`.
-/
theorem laplace_exp_log_mul_integral {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (Real.log z * t)) =
      - (Real.log z)⁻¹ := by
  have hlog_neg : Real.log z < 0 := (Real.log_neg_iff hz0).2 hz1
  have hlog_ne : Real.log z ≠ 0 := ne_of_lt hlog_neg
  have hlim_exp :
      Filter.Tendsto (fun t : ℝ => Real.exp (Real.log z * t)) Filter.atTop
        (𝓝 0) := by
    exact (Real.tendsto_exp_comp_nhds_zero).2
      (Filter.Tendsto.const_mul_atTop_of_neg hlog_neg
        (tendsto_id : Filter.Tendsto (fun t : ℝ => t) Filter.atTop Filter.atTop))
  have hlim :
      Filter.Tendsto (fun t : ℝ => Real.exp (Real.log z * t) / Real.log z)
        Filter.atTop (𝓝 0) := by
    simpa using hlim_exp.div_const (Real.log z)
  have hint := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ))
    (g := fun t : ℝ => Real.exp (Real.log z * t) / Real.log z)
    (g' := fun t : ℝ => Real.exp (Real.log z * t))
    (l := (0 : ℝ))
    (hderiv := by
      intro x _hx
      have hlin : HasDerivAt (fun u : ℝ => Real.log z * u) (Real.log z) x := by
        simpa using (hasDerivAt_id x).const_mul (Real.log z)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (Real.log z * u))
          (Real.exp (Real.log z * x) * Real.log z) x := by
        simpa using hlin.exp
      have hdiv := hexp.div_const (Real.log z)
      simpa [hlog_ne] using hdiv)
    (g'pos := by
      intro x _hx
      positivity)
    (hg := hlim)
  simpa [hlog_ne] using hint

/--
Laplace-log kernel in the power form used by Sondow. This is the bridge from
`z ^ t` to `-1 / log z`, with the `rpow` definition discharged explicitly.
-/
theorem laplace_rpow_integral {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), z ^ t) = - (Real.log z)⁻¹ := by
  have hpoint : (fun t : ℝ => z ^ t) =
      fun t : ℝ => Real.exp (Real.log z * t) := by
    funext t
    exact Real.rpow_def_of_pos hz0 t
  rw [hpoint]
  exact laplace_exp_log_mul_integral hz0 hz1

/--
Denominator adapter for the Sondow kernel. It rewrites the logarithmic factor
as a scaled Laplace kernel without changing the statement strength.
-/
theorem one_div_neg_one_sub_mul_log_eq_laplace_scaled {z : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1) :
    1 / (-(1 - z) * Real.log z) =
      (1 / (1 - z)) * (∫ t : ℝ in Set.Ioi (0 : ℝ), z ^ t) := by
  have hlog_neg : Real.log z < 0 := (Real.log_neg_iff hz0).2 hz1
  have hlog_ne : Real.log z ≠ 0 := ne_of_lt hlog_neg
  have hone_sub : 1 - z ≠ 0 := by linarith
  rw [laplace_rpow_integral hz0 hz1]
  field_simp [hlog_ne, hone_sub]

/--
Pointwise weighted version of the denominator adapter. This is the local form
needed before expanding the numerator and the geometric denominator.
-/
theorem div_neg_one_sub_mul_log_eq_mul_laplace_scaled (a : ℝ) {z : ℝ}
    (hz0 : 0 < z) (hz1 : z < 1) :
    a / (-(1 - z) * Real.log z) =
      a * ((1 / (1 - z)) * (∫ t : ℝ in Set.Ioi (0 : ℝ), z ^ t)) := by
  rw [div_eq_mul_one_div]
  rw [one_div_neg_one_sub_mul_log_eq_laplace_scaled hz0 hz1]

/-- Product of two open-unit variables remains in the open unit interval. -/
theorem mul_mem_open_unit {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy1 : y < 1) :
    0 < x * y ∧ x * y < 1 := by
  refine ⟨mul_pos hx0 hy0, ?_⟩
  have hxle : x ≤ 1 := le_of_lt hx1
  have hyle : 0 ≤ y := le_of_lt hy0
  have hxy_le_y : x * y ≤ 1 * y := mul_le_mul_of_nonneg_right hxle hyle
  have hxy_le_y' : x * y ≤ y := by simpa using hxy_le_y
  exact lt_of_le_of_lt hxy_le_y' hy1

/--
The exact `xy` kernel adapter that matches the denominator in Sondow's double
integral.
-/
theorem one_div_neg_one_sub_xy_mul_log_eq_laplace_scaled {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    1 / (-(1 - x * y) * Real.log (x * y)) =
      (1 / (1 - x * y)) * (∫ t : ℝ in Set.Ioi (0 : ℝ), (x * y) ^ t) := by
  rcases mul_mem_open_unit hx0 hx1 hy0 hy1 with ⟨hxy0, hxy1⟩
  exact one_div_neg_one_sub_mul_log_eq_laplace_scaled hxy0 hxy1

/--
Weighted `xy` form of the bridge. This is the pointwise local statement for the
original Sondow integrand numerator divided by its logarithmic denominator.
-/
theorem div_neg_one_sub_xy_mul_log_eq_mul_laplace_scaled (a : ℝ) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    a / (-(1 - x * y) * Real.log (x * y)) =
      a * ((1 / (1 - x * y)) *
        (∫ t : ℝ in Set.Ioi (0 : ℝ), (x * y) ^ t)) := by
  rcases mul_mem_open_unit hx0 hx1 hy0 hy1 with ⟨hxy0, hxy1⟩
  exact div_neg_one_sub_mul_log_eq_mul_laplace_scaled a hxy0 hxy1

/-- Unit-interval integral of a positive shifted real power. -/
theorem unit_interval_rpow_sub_one_integral {A : ℝ} (hA : 0 < A) :
    (∫ x in (0 : ℝ)..1, x ^ (A - 1)) = A⁻¹ := by
  have hgt : -1 < A - 1 := by linarith
  have h := integral_rpow (a := (0 : ℝ)) (b := (1 : ℝ)) (r := A - 1) (Or.inl hgt)
  rw [h]
  have hAexpr : A - 1 + 1 = A := by ring
  rw [hAexpr]
  have hAne : A ≠ 0 := ne_of_gt hA
  have hpow0 : (0 : ℝ) ^ A = 0 := by
    exact Real.zero_rpow hA.ne'
  have hpow1 : (1 : ℝ) ^ A = 1 := by simp
  rw [hpow0, hpow1]
  field_simp [hAne]
  norm_num

/--
Unit-interval monomial integral in the shifted natural-index form needed by
the Sondow kernel moments.
-/
theorem unit_interval_nat_shift_rpow_integral (a k : ℕ) {t : ℝ}
    (hk : 1 ≤ k) (ht : 0 ≤ t) :
    (∫ x in (0 : ℝ)..1, x ^ (((a + k : ℕ) : ℝ) + t - 1)) =
      (((a + k : ℕ) : ℝ) + t)⁻¹ := by
  have hA : 0 < ((a + k : ℕ) : ℝ) + t := by
    have hnat : 0 < ((a + k : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < a + k)
    linarith
  exact unit_interval_rpow_sub_one_integral hA

/-- Constant-left form of `unit_interval_nat_shift_rpow_integral`. -/
theorem unit_interval_nat_shift_rpow_integral_const_mul (a k : ℕ) {t c : ℝ}
    (hk : 1 ≤ k) (ht : 0 ≤ t) :
    (∫ x in (0 : ℝ)..1, c * x ^ (((a + k : ℕ) : ℝ) + t - 1)) =
      c * (((a + k : ℕ) : ℝ) + t)⁻¹ := by
  rw [intervalIntegral.integral_const_mul]
  rw [unit_interval_nat_shift_rpow_integral a k hk ht]

/-- Constant-right form of `unit_interval_nat_shift_rpow_integral`. -/
theorem unit_interval_nat_shift_rpow_integral_mul_const (a k : ℕ) {t c : ℝ}
    (hk : 1 ≤ k) (ht : 0 ≤ t) :
    (∫ x in (0 : ℝ)..1, x ^ (((a + k : ℕ) : ℝ) + t - 1) * c) =
      (((a + k : ℕ) : ℝ) + t)⁻¹ * c := by
  rw [intervalIntegral.integral_mul_const]
  rw [unit_interval_nat_shift_rpow_integral a k hk ht]

end

end EulerLimit.SondowIntegralBridge
