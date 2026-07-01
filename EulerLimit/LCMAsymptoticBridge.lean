/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.LCMBoundBridge

/-!
# Asymptotic Hanson bridge

This module continues the `Nat.lcmUpto n ≤ 3^n` internalization after the
finite Hanson certificate range.  The slow finite `decide` certificates stay in
`LCMBoundBridge`; this file is for the reusable real-inequality tail.
-/

open Chebyshev

theorem one_sub_div_pos_of_lt
    {a n : ℕ} (h : a < n) :
    0 < (1 : ℝ) - (a : ℝ) / (n : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlt : (a : ℝ) / (n : ℝ) < 1 := by
    rw [div_lt_one hn]
    exact_mod_cast h
  linarith

theorem log_div_sub_one_eq
    {a n : ℕ} (ha : 0 < a) (h : a < n) :
    Real.log ((n : ℝ) / (a : ℝ) - 1) =
      Real.log n - Real.log a +
        Real.log ((1 : ℝ) - (a : ℝ) / (n : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpos : 0 < (1 : ℝ) - (a : ℝ) / (n : ℝ) :=
    one_sub_div_pos_of_lt h
  have hne1 : ((n : ℝ) / (a : ℝ)) ≠ 0 := by positivity
  have hne2 : ((1 : ℝ) - (a : ℝ) / (n : ℝ)) ≠ 0 := by positivity
  have hrewrite :
      (n : ℝ) / (a : ℝ) - 1 =
        ((n : ℝ) / (a : ℝ)) * ((1 : ℝ) - (a : ℝ) / (n : ℝ)) := by
    field_simp [haR.ne', hnR.ne']
  rw [hrewrite, Real.log_mul hne1 hne2, Real.log_div hnR.ne' haR.ne']

theorem hansonA_le_43_of_lt_four {i : ℕ} (hi : i < 4) :
    hansonA i ≤ 43 := by
  interval_cases i <;> norm_num [hansonA]

theorem shifted_log_penalty_ge_neg_two_of_ge_86
    {n i : ℕ} (hn : 86 ≤ n) (hi : i < 4) :
    -2 ≤
      ((n : ℝ) / (hansonA i : ℝ) - 1) *
        Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
  let a := hansonA i
  have ha_pos_nat : 0 < a := by
    dsimp [a]
    exact hansonA_pos i
  have ha_le_nat : a ≤ 43 := by
    dsimp [a]
    exact hansonA_le_43_of_lt_four hi
  have haR : (0 : ℝ) < a := by exact_mod_cast ha_pos_nat
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h2a : 2 * a ≤ n := by omega
  have ht_nonneg : 0 ≤ (a : ℝ) / (n : ℝ) := by positivity
  have ht_half : (a : ℝ) / (n : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hnR]
    have h2aR : (2 : ℝ) * a ≤ n := by exact_mod_cast h2a
    nlinarith
  have hlog :
      -2 * ((a : ℝ) / (n : ℝ)) ≤
        Real.log ((1 : ℝ) - (a : ℝ) / (n : ℝ)) :=
    neg_two_mul_le_log_one_sub ht_nonneg ht_half
  have hfactor_nonneg : 0 ≤ (n : ℝ) / (a : ℝ) - 1 := by
    rw [sub_nonneg]
    rw [one_le_div haR]
    exact_mod_cast (by omega : a ≤ n)
  have hmul :
      ((n : ℝ) / (a : ℝ) - 1) * (-2 * ((a : ℝ) / (n : ℝ))) ≤
        ((n : ℝ) / (a : ℝ) - 1) *
          Real.log ((1 : ℝ) - (a : ℝ) / (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog hfactor_nonneg
  have hleft :
      -2 ≤ ((n : ℝ) / (a : ℝ) - 1) * (-2 * ((a : ℝ) / (n : ℝ))) := by
    have hrewrite :
        ((n : ℝ) / (a : ℝ) - 1) * (-2 * ((a : ℝ) / (n : ℝ))) =
          -2 + 2 * ((a : ℝ) / (n : ℝ)) := by
      field_simp [haR.ne', hnR.ne']
      ring
    rw [hrewrite]
    have hnonneg : 0 ≤ 2 * ((a : ℝ) / (n : ℝ)) := by positivity
    nlinarith
  exact hleft.trans hmul

theorem shifted_log_penalty_ge_neg_one_of_lt
    {a n : ℕ} (ha : 0 < a) (han : a < n) :
    -1 ≤
      ((n : ℝ) / (a : ℝ) - 1) *
        Real.log ((1 : ℝ) - (a : ℝ) / (n : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpos : 0 < (1 : ℝ) - (a : ℝ) / (n : ℝ) :=
    one_sub_div_pos_of_lt han
  have hbase :
      1 - ((1 : ℝ) - (a : ℝ) / (n : ℝ))⁻¹ ≤
        Real.log ((1 : ℝ) - (a : ℝ) / (n : ℝ)) :=
    Real.one_sub_inv_le_log_of_pos hpos
  have hfactor_nonneg : 0 ≤ (n : ℝ) / (a : ℝ) - 1 := by
    rw [sub_nonneg]
    rw [one_le_div haR]
    exact_mod_cast (Nat.le_of_lt han)
  have hmul :
      ((n : ℝ) / (a : ℝ) - 1) *
          (1 - ((1 : ℝ) - (a : ℝ) / (n : ℝ))⁻¹) ≤
        ((n : ℝ) / (a : ℝ) - 1) *
          Real.log ((1 : ℝ) - (a : ℝ) / (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hbase hfactor_nonneg
  have hleft :
      ((n : ℝ) / (a : ℝ) - 1) *
          (1 - ((1 : ℝ) - (a : ℝ) / (n : ℝ))⁻¹) = -1 := by
    have hanR : (a : ℝ) < n := by exact_mod_cast han
    have hdiff : (n : ℝ) - (a : ℝ) ≠ 0 := by linarith
    field_simp [haR.ne', hnR.ne', hdiff]
    ring
  rw [← hleft]
  exact hmul

theorem hansonA_lt_of_mem_range {i k : ℕ} (hi : i ∈ Finset.range k) :
    hansonA i < hansonA k :=
  hansonA_strictMono (Finset.mem_range.mp hi)

theorem hansonA_lt_of_mem_range_of_le
    {n i k : ℕ} (hk : hansonA k ≤ n) (hi : i ∈ Finset.range k) :
    hansonA i < n :=
  (hansonA_lt_of_mem_range hi).trans_le hk

theorem two_mul_hansonA_le_hansonA_succ_of_one_le
    {i : ℕ} (hi : 1 ≤ i) :
    2 * hansonA i ≤ hansonA (i + 1) := by
  dsimp [hansonA]
  have h3 : 3 ≤ hansonA i := by
    have hA1 : hansonA 1 ≤ hansonA i :=
      hansonA_strictMono.monotone hi
    norm_num [hansonA] at hA1 ⊢
    exact hA1
  have hmul : 3 * hansonA i ≤ hansonA i * hansonA i :=
    Nat.mul_le_mul_right (hansonA i) h3
  rw [pow_two]
  have hle : 2 * hansonA i + hansonA i ≤ hansonA i * hansonA i := by
    simpa [two_mul, Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hmul
  exact (Nat.le_sub_of_add_le hle).trans (Nat.le_add_right _ _)

theorem two_mul_hansonA_le_hansonA_of_lt
    {i k : ℕ} (hk : 2 ≤ k) (hi : i < k) :
    2 * hansonA i ≤ hansonA k := by
  rcases i with _ | i
  · have hA2k : hansonA 2 ≤ hansonA k :=
      hansonA_strictMono.monotone hk
    norm_num [hansonA] at hA2k ⊢
    omega
  · have hstep : 2 * hansonA (i + 1) ≤ hansonA (i + 2) :=
      two_mul_hansonA_le_hansonA_succ_of_one_le (by omega : 1 ≤ i + 1)
    have hsuccle : i + 2 ≤ k := by omega
    have hmon : hansonA (i + 2) ≤ hansonA k :=
      hansonA_strictMono.monotone hsuccle
    exact hstep.trans hmon

theorem two_mul_hansonA_le_of_mem_range_of_hansonA_le
    {n i k : ℕ} (hk2 : 2 ≤ k) (hkn : hansonA k ≤ n)
    (hi : i ∈ Finset.range k) :
    2 * hansonA i ≤ n :=
  (two_mul_hansonA_le_hansonA_of_lt hk2 (Finset.mem_range.mp hi)).trans hkn

theorem shifted_log_penalty_sum_ge_neg
    {n k : ℕ} (hk : hansonA k ≤ n) :
    -(k : ℝ) ≤
      ∑ i ∈ Finset.range k,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
  have hsum :
      ∑ i ∈ Finset.range k, (-1 : ℝ) ≤
        ∑ i ∈ Finset.range k,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
    exact Finset.sum_le_sum fun i hi =>
      shifted_log_penalty_ge_neg_one_of_lt
        (hansonA_pos i) (hansonA_lt_of_mem_range_of_le hk hi)
  have hconst : (∑ i ∈ Finset.range k, (-1 : ℝ)) = -(k : ℝ) := by
    simp
  rwa [hconst] at hsum

theorem shifted_log_sum_eq_base_add_penalty
    {n k : ℕ} (hk : hansonA k ≤ n) :
    (∑ i ∈ Finset.range k,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) =
      (∑ i ∈ Finset.range k,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          (Real.log n - Real.log (hansonA i))) +
      ∑ i ∈ Finset.range k,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hlt : hansonA i < n := hansonA_lt_of_mem_range_of_le hk hi
  have hlog := log_div_sub_one_eq (hansonA_pos i) hlt
  rw [hlog]
  ring

theorem shifted_log_sum_lower_of_base_lower
    {n k : ℕ} (hk : hansonA k ≤ n)
    (hbase :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        (∑ i ∈ Finset.range k,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            (Real.log n - Real.log (hansonA i))) - (k : ℝ)) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range k,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) := by
  have hpen := shifted_log_penalty_sum_ge_neg hk
  rw [shifted_log_sum_eq_base_add_penalty hk]
  linarith

theorem hanson_base_sum_eq_sum_form (n k : ℕ) :
    (∑ i ∈ Finset.range k,
      ((n : ℝ) / (hansonA i : ℝ) - 1) *
        (Real.log n - Real.log (hansonA i))) =
      (((n : ℝ) *
          (∑ i ∈ Finset.range k, (1 : ℝ) / (hansonA i : ℝ)) - (k : ℝ)) *
        Real.log n) -
        (n : ℝ) *
          (∑ i ∈ Finset.range k,
            ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i)) +
        ∑ i ∈ Finset.range k, Real.log (hansonA i) := by
  rw [show
      (∑ i ∈ Finset.range k,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          (Real.log n - Real.log (hansonA i))) =
        ∑ i ∈ Finset.range k,
          (((n : ℝ) / (hansonA i : ℝ) - 1) * Real.log n -
            ((n : ℝ) / (hansonA i : ℝ) - 1) * Real.log (hansonA i)) by
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  have hsum_left :
      (∑ x ∈ Finset.range k, ((n : ℝ) / (hansonA x : ℝ) - 1)) =
        (n : ℝ) * (∑ x ∈ Finset.range k, (1 : ℝ) / (hansonA x : ℝ)) -
          (k : ℝ) := by
    rw [Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    simp [Finset.sum_const, nsmul_eq_mul]
    ring_nf
  have hsum_right :
      (∑ x ∈ Finset.range k,
          ((n : ℝ) / (hansonA x : ℝ) - 1) * Real.log (hansonA x)) =
        (n : ℝ) *
          (∑ x ∈ Finset.range k,
            ((1 : ℝ) / (hansonA x : ℝ)) * Real.log (hansonA x)) -
          ∑ x ∈ Finset.range k, Real.log (hansonA x) := by
    rw [show
        (∑ x ∈ Finset.range k,
            ((n : ℝ) / (hansonA x : ℝ) - 1) * Real.log (hansonA x)) =
          ∑ x ∈ Finset.range k,
            ((n : ℝ) / (hansonA x : ℝ) * Real.log (hansonA x) -
              Real.log (hansonA x)) by
      apply Finset.sum_congr rfl
      intro x _
      ring]
    rw [Finset.sum_sub_distrib]
    have hfirst :
        (∑ x ∈ Finset.range k,
            (n : ℝ) / (hansonA x : ℝ) * Real.log (hansonA x)) =
          (n : ℝ) *
            (∑ x ∈ Finset.range k,
              ((1 : ℝ) / (hansonA x : ℝ)) * Real.log (hansonA x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hfirst]
  rw [hsum_left, hsum_right]
  ring

theorem hansonA_reciprocal_sum_real_eq (k : ℕ) :
    (∑ i ∈ Finset.range k, (1 : ℝ) / hansonA i) =
      1 - (1 : ℝ) / ((hansonA k : ℝ) - 1) := by
  have hq := congrArg (fun q : ℚ => (q : ℝ)) (hansonA_reciprocal_sum_eq k)
  norm_num at hq
  simpa using hq

theorem hanson_log_product_sum_eq_log_pred (k : ℕ) :
    (∑ i ∈ Finset.range k, Real.log (hansonA i : ℝ)) =
      Real.log ((hansonA k - 1 : ℕ) : ℝ) := by
  rw [← Real.log_prod]
  · have hprod :
        (∏ i ∈ Finset.range k, (hansonA i : ℝ)) =
          ((hansonA k - 1 : ℕ) : ℝ) := by
      exact_mod_cast prod_range_hansonA_eq_pred k
    rw [hprod]
  · intro i _
    exact_mod_cast Nat.ne_of_gt (hansonA_pos i)

theorem hanson_base_lower_of_margin
    {n k : ℕ}
    (hmargin :
      (n : ℝ) * Real.log n / ((hansonA k : ℝ) - 1) +
            (k : ℝ) * Real.log n + (k : ℝ) -
          (∑ i ∈ Finset.range k, Real.log (hansonA i : ℝ)) ≤
        (n : ℝ) *
          (Real.log 3 -
            ∑ i ∈ Finset.range k,
              ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i))) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      (∑ i ∈ Finset.range k,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          (Real.log n - Real.log (hansonA i))) - (k : ℝ) := by
  rw [hanson_base_sum_eq_sum_form]
  rw [hansonA_reciprocal_sum_real_eq]
  have hden : ((hansonA k : ℝ) - 1) ≠ 0 := by
    have hgt : (1 : ℝ) < hansonA k := by
      exact_mod_cast (by
        have := two_le_hansonA k
        omega : 1 < hansonA k)
    linarith
  have halg :
      (((n : ℝ) * (1 - 1 / ((hansonA k : ℝ) - 1)) - (k : ℝ)) *
              Real.log n -
            (n : ℝ) *
              (∑ i ∈ Finset.range k,
                1 / (hansonA i : ℝ) * Real.log (hansonA i)) +
          ∑ i ∈ Finset.range k, Real.log (hansonA i : ℝ) -
        (k : ℝ)) =
        (n : ℝ) * Real.log n -
          ((n : ℝ) * Real.log n / ((hansonA k : ℝ) - 1) +
              (k : ℝ) * Real.log n + (k : ℝ) -
            ∑ i ∈ Finset.range k, Real.log (hansonA i : ℝ)) -
          (n : ℝ) *
            (∑ i ∈ Finset.range k,
              1 / (hansonA i : ℝ) * Real.log (hansonA i)) := by
    field_simp [hden]
    ring
  rw [halg]
  nlinarith

theorem shifted_log_sum_lower_of_hanson_margin
    {n k : ℕ} (hk : hansonA k ≤ n)
    (hmargin :
      (n : ℝ) * Real.log n / ((hansonA k : ℝ) - 1) +
            (k : ℝ) * Real.log n + (k : ℝ) -
          (∑ i ∈ Finset.range k, Real.log (hansonA i : ℝ)) ≤
        (n : ℝ) *
          (Real.log 3 -
            ∑ i ∈ Finset.range k,
              ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i))) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range k,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) :=
  shifted_log_sum_lower_of_base_lower hk
    (hanson_base_lower_of_margin hmargin)

theorem shifted_log_sum_lower_of_hanson_closed_margin
    {n k : ℕ} (hk : hansonA k ≤ n)
    (hmargin :
      (n : ℝ) * Real.log n / ((hansonA k : ℝ) - 1) +
            (k : ℝ) * Real.log n + (k : ℝ) -
          Real.log ((hansonA k - 1 : ℕ) : ℝ) ≤
        (n : ℝ) *
          (Real.log 3 -
            ∑ i ∈ Finset.range k,
              ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i))) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range k,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) := by
  refine shifted_log_sum_lower_of_hanson_margin hk ?_
  rwa [hanson_log_product_sum_eq_log_pred]

theorem hanson_log_pred_nonneg (k : ℕ) :
    0 ≤ Real.log ((hansonA k - 1 : ℕ) : ℝ) := by
  exact Real.log_nonneg (by
    have hnat : 1 ≤ hansonA k - 1 := by
      have := two_le_hansonA k
      omega
    exact_mod_cast hnat)

theorem hanson_closed_margin_of_log_le
    {n k : ℕ} {L gap : ℝ}
    (hlog : Real.log (n : ℝ) ≤ L)
    (hgap : gap ≤
      Real.log 3 -
        ∑ i ∈ Finset.range k,
          ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i))
    (hband :
      (n : ℝ) * L / ((hansonA k : ℝ) - 1) +
          (k : ℝ) * L + (k : ℝ) ≤
        (n : ℝ) * gap) :
    (n : ℝ) * Real.log n / ((hansonA k : ℝ) - 1) +
          (k : ℝ) * Real.log n + (k : ℝ) -
        Real.log ((hansonA k - 1 : ℕ) : ℝ) ≤
      (n : ℝ) *
        (Real.log 3 -
          ∑ i ∈ Finset.range k,
            ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i)) := by
  have hden_nonneg : 0 ≤ ((hansonA k : ℝ) - 1) := by
    have hgt : (1 : ℝ) ≤ hansonA k := by
      exact_mod_cast (by
        have := two_le_hansonA k
        omega : 1 ≤ hansonA k)
    linarith
  have hlogpred : 0 ≤ Real.log ((hansonA k - 1 : ℕ) : ℝ) :=
    hanson_log_pred_nonneg k
  have hterm :
      (n : ℝ) * Real.log n / ((hansonA k : ℝ) - 1) ≤
        (n : ℝ) * L / ((hansonA k : ℝ) - 1) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n)) hden_nonneg
  have hklog : (k : ℝ) * Real.log n ≤ (k : ℝ) * L := by
    exact mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
  have hleft :
      (n : ℝ) * Real.log n / ((hansonA k : ℝ) - 1) +
            (k : ℝ) * Real.log n + (k : ℝ) -
          Real.log ((hansonA k - 1 : ℕ) : ℝ) ≤
        (n : ℝ) * L / ((hansonA k : ℝ) - 1) +
          (k : ℝ) * L + (k : ℝ) := by
    nlinarith
  have hgapmul :
      (n : ℝ) * gap ≤
        (n : ℝ) *
          (Real.log 3 -
            ∑ i ∈ Finset.range k,
              ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i)) := by
    exact mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg n)
  exact hleft.trans (hband.trans hgapmul)

theorem hanson_band_linear_margin
    {n lo k : ℕ} {L gap : ℝ}
    (hlo : lo ≤ n)
    (hcoef : 0 ≤ gap - L / ((hansonA k : ℝ) - 1))
    (hend :
      (k : ℝ) * L + (k : ℝ) ≤
        (gap - L / ((hansonA k : ℝ) - 1)) * (lo : ℝ)) :
    (n : ℝ) * L / ((hansonA k : ℝ) - 1) +
        (k : ℝ) * L + (k : ℝ) ≤
      (n : ℝ) * gap := by
  have hloR : (lo : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
  have hmono :
      (gap - L / ((hansonA k : ℝ) - 1)) * (lo : ℝ) ≤
        (gap - L / ((hansonA k : ℝ) - 1)) * (n : ℝ) := by
    exact mul_le_mul_of_nonneg_left hloR hcoef
  have hsplit :
      (n : ℝ) * gap =
        (n : ℝ) * L / ((hansonA k : ℝ) - 1) +
          (gap - L / ((hansonA k : ℝ) - 1)) * (n : ℝ) := by
    ring
  rw [hsplit]
  nlinarith

theorem hanson_closed_margin_of_endpoint_log_le
    {n lo k : ℕ} {L gap : ℝ}
    (hlo : lo ≤ n)
    (hlog : Real.log (n : ℝ) ≤ L)
    (hgap : gap ≤
      Real.log 3 -
        ∑ i ∈ Finset.range k,
          ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i))
    (hcoef : 0 ≤ gap - L / ((hansonA k : ℝ) - 1))
    (hend :
      (k : ℝ) * L + (k : ℝ) ≤
        (gap - L / ((hansonA k : ℝ) - 1)) * (lo : ℝ)) :
    (n : ℝ) * Real.log n / ((hansonA k : ℝ) - 1) +
          (k : ℝ) * Real.log n + (k : ℝ) -
        Real.log ((hansonA k - 1 : ℕ) : ℝ) ≤
      (n : ℝ) *
        (Real.log 3 -
          ∑ i ∈ Finset.range k,
            ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i)) :=
  hanson_closed_margin_of_log_le hlog hgap
    (hanson_band_linear_margin hlo hcoef hend)

theorem two_mul_add_one_le_two_pow_of_ge_four
    {a : ℕ} (ha : 4 ≤ a) :
    2 * a + 1 ≤ 2 ^ a := by
  exact Nat.le_induction (m := 4)
    (P := fun a _ => 2 * a + 1 ≤ 2 ^ a)
    (by norm_num)
    (by
      intro a ha ih
      calc
        2 * (a + 1) + 1 = (2 * a + 1) + 2 := by ring
        _ ≤ 2 ^ a + 2 := Nat.add_le_add_right ih 2
        _ ≤ 2 ^ a + 2 ^ a := by
          apply Nat.add_le_add_left
          have hpow : 2 ^ 2 ≤ 2 ^ a :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        _ = 2 ^ (a + 1) := by rw [pow_succ']; ring)
    a ha

theorem sq_lt_two_pow_of_ge_five
    {a : ℕ} (ha : 5 ≤ a) :
    a ^ 2 < 2 ^ a := by
  exact Nat.le_induction (m := 5)
    (P := fun a _ => a ^ 2 < 2 ^ a)
    (by norm_num)
    (by
      intro a ha ih
      have hlin : 2 * a + 1 ≤ 2 ^ a :=
        two_mul_add_one_le_two_pow_of_ge_four (by omega)
      calc
        (a + 1) ^ 2 = a ^ 2 + (2 * a + 1) := by ring
        _ < 2 ^ a + 2 ^ a := Nat.add_lt_add_of_lt_of_le ih hlin
        _ = 2 ^ (a + 1) := by rw [pow_succ']; ring)
    a ha

theorem hansonA_succ_le_sq (j : ℕ) :
    hansonA (j + 1) ≤ hansonA j ^ 2 := by
  dsimp [hansonA]
  let a := hansonA j
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact (by norm_num : 1 ≤ 2).trans (two_le_hansonA j)
  have ha_le_sq : a ≤ a ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left a (by omega)
  calc
    a ^ 2 - a + 1 ≤ a ^ 2 - a + a := Nat.add_le_add_left ha1 _
    _ = a ^ 2 := Nat.sub_add_cancel ha_le_sq

theorem hansonA_succ_lt_two_pow_hansonA
    {j : ℕ} (hj : 2 ≤ j) :
    hansonA (j + 1) < 2 ^ hansonA j := by
  have hle : hansonA (j + 1) ≤ hansonA j ^ 2 :=
    hansonA_succ_le_sq j
  have hsq : hansonA j ^ 2 < 2 ^ hansonA j :=
    sq_lt_two_pow_of_ge_five (by
      have hA2 : hansonA 2 ≤ hansonA j :=
        hansonA_strictMono.monotone hj
      norm_num [hansonA] at hA2 ⊢
      omega)
  exact hle.trans_lt hsq

theorem log_hansonA_succ_le_hansonA
    {j : ℕ} (hj : 2 ≤ j) :
    Real.log (hansonA (j + 1) : ℝ) ≤ (hansonA j : ℝ) := by
  have hlt : hansonA (j + 1) < 2 ^ hansonA j :=
    hansonA_succ_lt_two_pow_hansonA hj
  have hpos : (0 : ℝ) < hansonA (j + 1) := by
    exact_mod_cast hansonA_pos (j + 1)
  have hltR :
      ((hansonA (j + 1) : ℕ) : ℝ) ≤ ((2 ^ hansonA j : ℕ) : ℝ) := by
    exact_mod_cast (le_of_lt hlt)
  have hlog_le :
      Real.log (hansonA (j + 1) : ℝ) ≤
        Real.log (((2 ^ hansonA j : ℕ) : ℝ)) :=
    Real.log_le_log hpos hltR
  have hpowlog :
      Real.log (((2 ^ hansonA j : ℕ) : ℝ)) =
        (hansonA j : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    ring_nf
  rw [hpowlog] at hlog_le
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  exact hlog_le.trans <| by
    calc
      (hansonA j : ℝ) * Real.log 2 ≤ (hansonA j : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
      _ = (hansonA j : ℝ) := by ring

theorem hansonA_reciprocal_sum_Ico_eq
    {m k : ℕ} (hmk : m ≤ k) :
    (∑ i ∈ Finset.Ico m k, (1 : ℝ) / hansonA i) =
      (1 : ℝ) / ((hansonA m : ℝ) - 1) -
        (1 : ℝ) / ((hansonA k : ℝ) - 1) := by
  rw [Finset.sum_Ico_eq_sub _ hmk]
  rw [hansonA_reciprocal_sum_real_eq k]
  rw [hansonA_reciprocal_sum_real_eq m]
  ring

theorem hansonA_reciprocal_sum_Ico_le_left
    {m k : ℕ} (hmk : m ≤ k) :
    (∑ i ∈ Finset.Ico m k, (1 : ℝ) / hansonA i) ≤
      (1 : ℝ) / ((hansonA m : ℝ) - 1) := by
  rw [hansonA_reciprocal_sum_Ico_eq hmk]
  have hdenpos : 0 < ((hansonA k : ℝ) - 1) := by
    have hgt : (1 : ℝ) < hansonA k := by
      exact_mod_cast (by
        have := two_le_hansonA k
        omega : 1 < hansonA k)
    linarith
  have hnonneg : 0 ≤ (1 : ℝ) / ((hansonA k : ℝ) - 1) := by
    positivity
  linarith

theorem hanson_weighted_log_div_le_two_recip_pred
    {i : ℕ} (hi : 3 ≤ i) :
    ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i : ℝ) ≤
      2 * ((1 : ℝ) / (hansonA (i - 1) : ℝ)) := by
  have hi1 : 2 ≤ i - 1 := by omega
  have hs : i - 1 + 1 = i := by omega
  have hlog := log_hansonA_succ_le_hansonA (j := i - 1) hi1
  rw [hs] at hlog
  have hden_nonneg : 0 ≤ (1 : ℝ) / (hansonA i : ℝ) := by positivity
  have hfirst :
      ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i : ℝ) ≤
        ((1 : ℝ) / (hansonA i : ℝ)) * (hansonA (i - 1) : ℝ) := by
    exact mul_le_mul_of_nonneg_left hlog hden_nonneg
  have hsecond :
      ((1 : ℝ) / (hansonA i : ℝ)) * (hansonA (i - 1) : ℝ) ≤
        2 * ((1 : ℝ) / (hansonA (i - 1) : ℝ)) := by
    let a := hansonA (i - 1)
    have ha_pos_nat : 0 < a := by
      dsimp [a]
      exact hansonA_pos (i - 1)
    have ha_le_sq_nat : a ≤ a ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_left a ha_pos_nat
    have hAi_nat : hansonA i = a ^ 2 - a + 1 := by
      dsimp [a]
      rw [← hs]
      rfl
    have hAiR : (hansonA i : ℝ) = (a : ℝ) ^ 2 - (a : ℝ) + 1 := by
      rw [hAi_nat]
      rw [Nat.cast_add, Nat.cast_sub ha_le_sq_nat, Nat.cast_pow]
      norm_num
    have ha_pos : (0 : ℝ) < a := by exact_mod_cast ha_pos_nat
    have hden_pos : 0 < (a : ℝ) ^ 2 - (a : ℝ) + 1 := by
      nlinarith [sq_nonneg ((a : ℝ) - 1)]
    have hden_pos' : 0 < (a : ℝ) * ((a : ℝ) - 1) + 1 := by
      nlinarith [sq_nonneg ((a : ℝ) - 1)]
    rw [hAiR]
    change ((1 : ℝ) / ((a : ℝ) ^ 2 - (a : ℝ) + 1)) * (a : ℝ) ≤
      2 * ((1 : ℝ) / (a : ℝ))
    field_simp [ha_pos.ne', hden_pos.ne', hden_pos'.ne']
    nlinarith [sq_nonneg ((a : ℝ) - 1)]
  exact hfirst.trans hsecond

theorem sum_Ico_pred_eq
    {m k : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k) (g : ℕ → ℝ) :
    (∑ i ∈ Finset.Ico m k, g (i - 1)) =
      ∑ j ∈ Finset.Ico (m - 1) (k - 1), g j := by
  rw [Finset.sum_Ico_eq_sum_range]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : k - m = k - 1 - (m - 1) := by omega
  rw [← hlen]
  refine Finset.sum_congr rfl ?_
  intro x _
  have hidx : m + x - 1 = (m - 1) + x := by omega
  rw [hidx]

theorem hanson_weighted_log_sum_Ico_le_two_recip_pred
    {m k : ℕ} (hm : 3 ≤ m) (hmk : m ≤ k) :
    (∑ i ∈ Finset.Ico m k,
      ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i : ℝ)) ≤
      2 * (∑ j ∈ Finset.Ico (m - 1) (k - 1),
        (1 : ℝ) / (hansonA j : ℝ)) := by
  calc
    (∑ i ∈ Finset.Ico m k,
      ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i : ℝ))
        ≤ ∑ i ∈ Finset.Ico m k,
            2 * ((1 : ℝ) / (hansonA (i - 1) : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact hanson_weighted_log_div_le_two_recip_pred (by
            have hmem := Finset.mem_Ico.mp hi
            omega)
    _ = 2 * (∑ i ∈ Finset.Ico m k,
            ((1 : ℝ) / (hansonA (i - 1) : ℝ))) := by
          rw [Finset.mul_sum]
    _ = 2 * (∑ j ∈ Finset.Ico (m - 1) (k - 1),
        (1 : ℝ) / (hansonA j : ℝ)) := by
          have hsum := sum_Ico_pred_eq (m := m) (k := k)
            (by omega : 1 ≤ m) hmk
            (fun j => (1 : ℝ) / (hansonA j : ℝ))
          exact congrArg (fun x : ℝ => 2 * x) hsum

theorem hanson_weighted_log_sum_Ico_le_two_recip_closed
    {m k : ℕ} (hm : 3 ≤ m) (hmk : m ≤ k) :
    (∑ i ∈ Finset.Ico m k,
      ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i : ℝ)) ≤
      2 * ((1 : ℝ) / ((hansonA (m - 1) : ℝ) - 1)) := by
  have htail := hanson_weighted_log_sum_Ico_le_two_recip_pred hm hmk
  have hrecip :
      (∑ j ∈ Finset.Ico (m - 1) (k - 1),
        (1 : ℝ) / (hansonA j : ℝ)) ≤
        (1 : ℝ) / ((hansonA (m - 1) : ℝ) - 1) :=
    hansonA_reciprocal_sum_Ico_le_left (by omega : m - 1 ≤ k - 1)
  exact htail.trans (mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 2))

theorem hanson_weighted_log_sum_range_le_range_add_tail
    {m k : ℕ} (hm : 3 ≤ m) (hmk : m ≤ k) :
    (∑ i ∈ Finset.range k,
      ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i : ℝ)) ≤
      (∑ i ∈ Finset.range m,
        ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i : ℝ)) +
        2 * ((1 : ℝ) / ((hansonA (m - 1) : ℝ) - 1)) := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun i => ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i : ℝ))
    hmk
  have htail := hanson_weighted_log_sum_Ico_le_two_recip_closed hm hmk
  linarith

theorem hanson_log_weight_gap_ge_of_range_tail
    {m k : ℕ} {gap eps : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k)
    (hgap :
      gap ≤
        Real.log 3 -
          ∑ i ∈ Finset.range m,
            ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i))
    (htail :
      2 * ((1 : ℝ) / ((hansonA (m - 1) : ℝ) - 1)) ≤ eps) :
    gap - eps ≤
      Real.log 3 -
        ∑ i ∈ Finset.range k,
          ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i) := by
  have hsum := hanson_weighted_log_sum_range_le_range_add_tail
    (m := m) (k := k) hm hmk
  nlinarith

theorem floor_log_sum_lower_of_shifted_log_lower
    {n k : ℕ}
    (hfloor : ∀ i : ℕ, i ∈ Finset.range k → 2 * hansonA i ≤ n)
    (hlower :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ∑ i ∈ Finset.range k,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ j ∈ Finset.range k,
        ((n / hansonA j : ℕ) : ℝ) *
          Real.log ((n / hansonA j : ℕ) : ℝ) :=
  hlower.trans <| Finset.sum_le_sum fun i hi =>
    div_sub_one_mul_log_le_floor_mul_log_of_two_mul_le
      (hansonA_pos i) (hfloor i hi)

theorem hansonC_le_three_pow_of_shifted_log_lower
    {n k : ℕ} (hn : 1 ≤ n)
    (hfloor : ∀ i : ℕ, i ∈ Finset.range k → 2 * hansonA i ≤ n)
    (hlower :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ∑ i ∈ Finset.range k,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) :
    hansonC n k ≤ 3 ^ n :=
  hansonC_le_three_pow_of_log_le n k
    (log_hansonC_le_log_three_of_floor_pow_log_lower
      (n := n) (k := k) hn
      (floor_log_sum_lower_of_shifted_log_lower hfloor hlower))

theorem lcmUpto_le_three_pow_nat_of_hanson_prefix_shifted_log_lower_ge
    (N : ℕ)
    (hN : 1 ≤ N)
    (hfinite : ∀ n : ℕ, n < N → Nat.lcmUpto n ≤ 3 ^ n)
    (k : ℕ → ℕ)
    (hfloor : ∀ n : ℕ, N ≤ n →
      ∀ i : ℕ, i ∈ Finset.range (k n) → 2 * hansonA i ≤ n)
    (hlower : ∀ n : ℕ, N ≤ n →
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ∑ i ∈ Finset.range (k n),
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
    N hfinite k ?_
  intro n hn
  exact hansonC_le_three_pow_of_shifted_log_lower
    (hN.trans hn) (hfloor n hn) (hlower n hn)

theorem lcmUpto_le_three_pow_nat_of_hanson_prefix_margin_ge
    (N : ℕ)
    (hN : 1 ≤ N)
    (hfinite : ∀ n : ℕ, n < N → Nat.lcmUpto n ≤ 3 ^ n)
    (k : ℕ → ℕ)
    (hk : ∀ n : ℕ, N ≤ n → hansonA (k n) ≤ n)
    (hfloor : ∀ n : ℕ, N ≤ n →
      ∀ i : ℕ, i ∈ Finset.range (k n) → 2 * hansonA i ≤ n)
    (hmargin : ∀ n : ℕ, N ≤ n →
      (n : ℝ) * Real.log n / ((hansonA (k n) : ℝ) - 1) +
            (k n : ℝ) * Real.log n + (k n : ℝ) -
          (∑ i ∈ Finset.range (k n), Real.log (hansonA i : ℝ)) ≤
        (n : ℝ) *
          (Real.log 3 -
            ∑ i ∈ Finset.range (k n),
              ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i))) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hanson_prefix_shifted_log_lower_ge
    N hN hfinite k hfloor ?_
  intro n hn
  exact shifted_log_sum_lower_of_hanson_margin
    (hk n hn) (hmargin n hn)

theorem lcmUpto_le_three_pow_nat_of_hanson_prefix_closed_margin_ge
    (N : ℕ)
    (hN : 1 ≤ N)
    (hfinite : ∀ n : ℕ, n < N → Nat.lcmUpto n ≤ 3 ^ n)
    (k : ℕ → ℕ)
    (hk : ∀ n : ℕ, N ≤ n → hansonA (k n) ≤ n)
    (hfloor : ∀ n : ℕ, N ≤ n →
      ∀ i : ℕ, i ∈ Finset.range (k n) → 2 * hansonA i ≤ n)
    (hmargin : ∀ n : ℕ, N ≤ n →
      (n : ℝ) * Real.log n / ((hansonA (k n) : ℝ) - 1) +
            (k n : ℝ) * Real.log n + (k n : ℝ) -
          Real.log ((hansonA (k n) - 1 : ℕ) : ℝ) ≤
        (n : ℝ) *
          (Real.log 3 -
            ∑ i ∈ Finset.range (k n),
              ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i))) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hanson_prefix_shifted_log_lower_ge
    N hN hfinite k hfloor ?_
  intro n hn
  exact shifted_log_sum_lower_of_hanson_closed_margin
    (hk n hn) (hmargin n hn)

theorem lcmUpto_le_three_pow_nat_of_hanson_prefix_margin_ge_of_two_le
    (N : ℕ)
    (hN : 1 ≤ N)
    (hfinite : ∀ n : ℕ, n < N → Nat.lcmUpto n ≤ 3 ^ n)
    (k : ℕ → ℕ)
    (hk2 : ∀ n : ℕ, N ≤ n → 2 ≤ k n)
    (hk : ∀ n : ℕ, N ≤ n → hansonA (k n) ≤ n)
    (hmargin : ∀ n : ℕ, N ≤ n →
      (n : ℝ) * Real.log n / ((hansonA (k n) : ℝ) - 1) +
            (k n : ℝ) * Real.log n + (k n : ℝ) -
          (∑ i ∈ Finset.range (k n), Real.log (hansonA i : ℝ)) ≤
        (n : ℝ) *
          (Real.log 3 -
            ∑ i ∈ Finset.range (k n),
              ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i))) :
    lcmUpto_le_three_pow_nat_statement :=
  lcmUpto_le_three_pow_nat_of_hanson_prefix_margin_ge
    N hN hfinite k hk
    (fun n hn _i hi =>
      two_mul_hansonA_le_of_mem_range_of_hansonA_le (hk2 n hn) (hk n hn) hi)
    hmargin

theorem lcmUpto_le_three_pow_nat_of_hanson_prefix_closed_margin_ge_of_two_le
    (N : ℕ)
    (hN : 1 ≤ N)
    (hfinite : ∀ n : ℕ, n < N → Nat.lcmUpto n ≤ 3 ^ n)
    (k : ℕ → ℕ)
    (hk2 : ∀ n : ℕ, N ≤ n → 2 ≤ k n)
    (hk : ∀ n : ℕ, N ≤ n → hansonA (k n) ≤ n)
    (hmargin : ∀ n : ℕ, N ≤ n →
      (n : ℝ) * Real.log n / ((hansonA (k n) : ℝ) - 1) +
            (k n : ℝ) * Real.log n + (k n : ℝ) -
          Real.log ((hansonA (k n) - 1 : ℕ) : ℝ) ≤
        (n : ℝ) *
          (Real.log 3 -
            ∑ i ∈ Finset.range (k n),
              ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i))) :
    lcmUpto_le_three_pow_nat_statement :=
  lcmUpto_le_three_pow_nat_of_hanson_prefix_closed_margin_ge
    N hN hfinite k hk
    (fun n hn _i hi =>
      two_mul_hansonA_le_of_mem_range_of_hansonA_le (hk2 n hn) (hk n hn) hi)
    hmargin

theorem shifted_log_penalty_ge_neg_one_of_ge_86
    {n i : ℕ} (hn : 86 ≤ n) (hi : i < 4) :
    -1 ≤
      ((n : ℝ) / (hansonA i : ℝ) - 1) *
        Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
  exact shifted_log_penalty_ge_neg_one_of_lt
    (hansonA_pos i)
    (by
      have hle := hansonA_le_43_of_lt_four hi
      omega)

theorem shifted_log_penalty_sum_four_ge_neg_eight
    {n : ℕ} (hn : 86 ≤ n) :
    -8 ≤
      ∑ i ∈ Finset.range 4,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
  have hsum :
      ∑ i ∈ Finset.range 4, (-2 : ℝ) ≤
        ∑ i ∈ Finset.range 4,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
    exact Finset.sum_le_sum fun i hi =>
      shifted_log_penalty_ge_neg_two_of_ge_86 hn (Finset.mem_range.mp hi)
  have hconst : (∑ i ∈ Finset.range 4, (-2 : ℝ)) = -8 := by
    norm_num
  rwa [hconst] at hsum

theorem shifted_log_penalty_sum_four_ge_neg_four
    {n : ℕ} (hn : 86 ≤ n) :
    -4 ≤
      ∑ i ∈ Finset.range 4,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
  have hsum :
      ∑ i ∈ Finset.range 4, (-1 : ℝ) ≤
        ∑ i ∈ Finset.range 4,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
    exact Finset.sum_le_sum fun i hi =>
      shifted_log_penalty_ge_neg_one_of_ge_86 hn (Finset.mem_range.mp hi)
  have hconst : (∑ i ∈ Finset.range 4, (-1 : ℝ)) = -4 := by
    norm_num
  rwa [hconst] at hsum

theorem shifted_log_sum_four_eq_base_add_penalty
    {n : ℕ} (hn : 86 ≤ n) :
    (∑ i ∈ Finset.range 4,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) =
      (∑ i ∈ Finset.range 4,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          (Real.log n - Real.log (hansonA i))) +
      ∑ i ∈ Finset.range 4,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hlt : hansonA i < n := by
    have hle := hansonA_le_43_of_lt_four (Finset.mem_range.mp hi)
    omega
  have hlog := log_div_sub_one_eq (hansonA_pos i) hlt
  rw [hlog]
  ring

theorem shifted_log_sum_four_lower_of_base_lower
    {n : ℕ} (hn : 86 ≤ n)
    (hbase :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        (∑ i ∈ Finset.range 4,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            (Real.log n - Real.log (hansonA i))) - 4) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range 4,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) := by
  have hpen := shifted_log_penalty_sum_four_ge_neg_four hn
  rw [shifted_log_sum_four_eq_base_add_penalty hn]
  linarith

theorem hanson_base_sum_four_eq_explicit (n : ℕ) :
    (∑ i ∈ Finset.range 4,
      ((n : ℝ) / (hansonA i : ℝ) - 1) *
        (Real.log n - Real.log (hansonA i))) =
      (((n : ℝ) * (1805 / 1806 : ℝ) - 4) * Real.log n) -
        (n : ℝ) *
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43) +
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43) := by
  norm_num [Finset.sum_range_succ, hansonA]
  ring

theorem hanson_log_product_four_eq_log_1806 :
    Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 =
      Real.log (1806 : ℝ) := by
  rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
  rw [← Real.log_mul (by norm_num : ((2 : ℝ) * 3) ≠ 0) (by norm_num : (7 : ℝ) ≠ 0)]
  rw [← Real.log_mul (by norm_num : ((2 : ℝ) * 3 * 7) ≠ 0) (by norm_num : (43 : ℝ) ≠ 0)]
  norm_num

theorem shifted_log_sum_four_lower_of_explicit_base_lower
    {n : ℕ} (hn : 86 ≤ n)
    (hbase :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ((((n : ℝ) * (1805 / 1806 : ℝ) - 4) * Real.log n) -
          (n : ℝ) *
            ((1 / 2 : ℝ) * Real.log 2 +
              (1 / 3 : ℝ) * Real.log 3 +
              (1 / 7 : ℝ) * Real.log 7 +
              (1 / 43 : ℝ) * Real.log 43) +
          (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43)) - 4) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range 4,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) := by
  refine shifted_log_sum_four_lower_of_base_lower hn ?_
  rw [hanson_base_sum_four_eq_explicit]
  exact hbase

theorem explicit_base_lower_of_margin
    {n : ℕ}
    (hmargin :
      (n : ℝ) * Real.log n / 1806 + 4 * Real.log n + 4 -
          (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43) ≤
        (n : ℝ) *
          (Real.log 3 -
            ((1 / 2 : ℝ) * Real.log 2 +
              (1 / 3 : ℝ) * Real.log 3 +
              (1 / 7 : ℝ) * Real.log 7 +
              (1 / 43 : ℝ) * Real.log 43))) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ((((n : ℝ) * (1805 / 1806 : ℝ) - 4) * Real.log n) -
        (n : ℝ) *
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43) +
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43)) - 4 := by
  nlinarith

theorem shifted_log_sum_four_lower_of_margin
    {n : ℕ} (hn : 86 ≤ n)
    (hmargin :
      (n : ℝ) * Real.log n / 1806 + 4 * Real.log n + 4 -
          (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43) ≤
        (n : ℝ) *
          (Real.log 3 -
            ((1 / 2 : ℝ) * Real.log 2 +
              (1 / 3 : ℝ) * Real.log 3 +
              (1 / 7 : ℝ) * Real.log 7 +
              (1 / 43 : ℝ) * Real.log 43))) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range 4,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) :=
  shifted_log_sum_four_lower_of_explicit_base_lower hn
    (explicit_base_lower_of_margin hmargin)

theorem log_nat_lt_of_lt_two_pow
    {n m : ℕ} (hm : 0 < m) (hn : 0 < n) (h : n < 2 ^ m) :
    Real.log (n : ℝ) < (m : ℝ) * (0.6931471808 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpowR : (n : ℝ) < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h
  have hlog : Real.log (n : ℝ) < Real.log (((2 ^ m : ℕ) : ℝ)) :=
    Real.log_lt_log hnR hpowR
  have hpowlog : Real.log (((2 ^ m : ℕ) : ℝ)) = (m : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hpowlog] at hlog
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmul : (m : ℝ) * Real.log 2 < (m : ℝ) * (0.6931471808 : ℝ) :=
    mul_lt_mul_of_pos_left Real.log_two_lt_d9 hmR
  exact hlog.trans hmul

theorem log_seven_lt_1_946 :
    Real.log (7 : ℝ) < (1.946 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 7)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 10)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

theorem log_forty_three_over_forty_two_le :
    Real.log ((43 : ℝ) / 42) ≤ (1 / 42 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (43 : ℝ) / 42)
  norm_num at h ⊢
  exact h

theorem log_forty_three_decomp :
    Real.log (43 : ℝ) =
      Real.log 2 + Real.log 3 + Real.log 7 + Real.log ((43 : ℝ) / 42) := by
  have h :
      Real.log 2 + Real.log 3 + Real.log 7 + Real.log ((43 : ℝ) / 42) =
        Real.log (43 : ℝ) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((2 : ℝ) * 3) ≠ 0) (by norm_num : (7 : ℝ) ≠ 0)]
    rw [← Real.log_mul
      (by norm_num : ((2 : ℝ) * 3 * 7) ≠ 0)
      (by norm_num : ((43 : ℝ) / 42) ≠ 0)]
    norm_num
  exact h.symm

theorem log_forty_three_lt_3_762 :
    Real.log (43 : ℝ) < (3.762 : ℝ) := by
  rw [log_forty_three_decomp]
  have h2 : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have h3 : Real.log 3 < (1.0986122888 : ℝ) := Real.log_three_lt_d9
  have h7 : Real.log 7 < (1.946 : ℝ) := log_seven_lt_1_946
  have h42 : Real.log ((43 : ℝ) / 42) ≤ (1 / 42 : ℝ) :=
    log_forty_three_over_forty_two_le
  nlinarith

theorem hanson_log_weight_four_gap_ge_0_02034 :
    (0.02034 : ℝ) ≤
      Real.log 3 -
        ((1 / 2 : ℝ) * Real.log 2 +
          (1 / 3 : ℝ) * Real.log 3 +
          (1 / 7 : ℝ) * Real.log 7 +
          (1 / 43 : ℝ) * Real.log 43) := by
  have h2 : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have h3lo : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
  have h3hi : Real.log 3 < (1.0986122888 : ℝ) := Real.log_three_lt_d9
  have h7 : Real.log 7 < (1.946 : ℝ) := log_seven_lt_1_946
  have h43 : Real.log 43 < (3.762 : ℝ) := log_forty_three_lt_3_762
  nlinarith

theorem log_seven_over_four_lower :
    (6 / 11 : ℝ) < Real.log ((7 : ℝ) / 4) := by
  have h := Real.lt_log_one_add_of_pos (show (0 : ℝ) < 3 / 4 by norm_num)
  norm_num at h ⊢
  exact h

theorem log_seven_lower :
    (2 : ℝ) * (0.6931471803 : ℝ) + (6 / 11 : ℝ) <
      Real.log (7 : ℝ) := by
  have hdecomp :
      Real.log (7 : ℝ) = 2 * Real.log 2 + Real.log ((7 : ℝ) / 4) := by
    have h :
        Real.log (4 : ℝ) + Real.log ((7 : ℝ) / 4) =
          Real.log (7 : ℝ) := by
      rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (by norm_num : ((7 : ℝ) / 4) ≠ 0)]
      norm_num
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [← h, hlog4]
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h74 : (6 / 11 : ℝ) < Real.log ((7 : ℝ) / 4) :=
    log_seven_over_four_lower
  nlinarith

theorem log_forty_three_over_thirty_two_lower :
    (22 / 75 : ℝ) < Real.log ((43 : ℝ) / 32) := by
  have h := Real.lt_log_one_add_of_pos (show (0 : ℝ) < 11 / 32 by norm_num)
  norm_num at h ⊢
  exact h

theorem log_forty_three_lower :
    (5 : ℝ) * (0.6931471803 : ℝ) + (22 / 75 : ℝ) <
      Real.log (43 : ℝ) := by
  have hdecomp :
      Real.log (43 : ℝ) = 5 * Real.log 2 + Real.log ((43 : ℝ) / 32) := by
    have h :
        Real.log (32 : ℝ) + Real.log ((43 : ℝ) / 32) =
          Real.log (43 : ℝ) := by
      rw [← Real.log_mul (by norm_num : (32 : ℝ) ≠ 0)
        (by norm_num : ((43 : ℝ) / 32) ≠ 0)]
      norm_num
    have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
      norm_num
    rw [← h, hlog32]
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h4332 : (22 / 75 : ℝ) < Real.log ((43 : ℝ) / 32) :=
    log_forty_three_over_thirty_two_lower
  nlinarith

theorem hanson_log_product_four_gt_7_48 :
    (7.48 : ℝ) < Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h3 : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
  have h7 : (2 : ℝ) * (0.6931471803 : ℝ) + (6 / 11 : ℝ) <
      Real.log 7 := log_seven_lower
  have h43 : (5 : ℝ) * (0.6931471803 : ℝ) + (22 / 75 : ℝ) <
      Real.log 43 := log_forty_three_lower
  nlinarith

theorem hanson_margin_of_dyadic_band
    {n m lo : ℕ}
    (hm : 0 < m) (hlo_pos : 0 < lo) (hnlo : lo ≤ n) (hhi : n < 2 ^ m)
    (hnum :
      4 * ((m : ℝ) * (0.6931471808 : ℝ)) + 4 - (7.48 : ℝ) ≤
        ((0.02034 : ℝ) - ((m : ℝ) * (0.6931471808 : ℝ)) / 1806) * (lo : ℝ))
    (hcoef :
      0 ≤ (0.02034 : ℝ) - ((m : ℝ) * (0.6931471808 : ℝ)) / 1806) :
    (n : ℝ) * Real.log n / 1806 + 4 * Real.log n + 4 -
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43) ≤
      (n : ℝ) *
        (Real.log 3 -
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43)) := by
  have hn_pos : 0 < n := by omega
  have hlog_lt :
      Real.log (n : ℝ) < (m : ℝ) * (0.6931471808 : ℝ) :=
    log_nat_lt_of_lt_two_pow hm hn_pos hhi
  have hlog_le :
      Real.log (n : ℝ) ≤ (m : ℝ) * (0.6931471808 : ℝ) :=
    le_of_lt hlog_lt
  have hprod_le :
      (7.48 : ℝ) ≤ Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 :=
    le_of_lt hanson_log_product_four_gt_7_48
  have hgap := hanson_log_weight_four_gap_ge_0_02034
  have hnloR : (lo : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlo
  have hmul :
      ((0.02034 : ℝ) - ((m : ℝ) * (0.6931471808 : ℝ)) / 1806) * (lo : ℝ) ≤
        ((0.02034 : ℝ) - ((m : ℝ) * (0.6931471808 : ℝ)) / 1806) * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hnloR hcoef
  have hband :
      (n : ℝ) * ((m : ℝ) * (0.6931471808 : ℝ)) / 1806 +
          4 * ((m : ℝ) * (0.6931471808 : ℝ)) + 4 - (7.48 : ℝ) ≤
        (n : ℝ) * (0.02034 : ℝ) := by
    nlinarith
  have hlog_mul :
      (n : ℝ) * Real.log n / 1806 ≤
        (n : ℝ) * ((m : ℝ) * (0.6931471808 : ℝ)) / 1806 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog_le (Nat.cast_nonneg n))
      (by norm_num : (0 : ℝ) ≤ 1806)
  have hlog_four :
      4 * Real.log n ≤ 4 * ((m : ℝ) * (0.6931471808 : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hlog_le (by norm_num : (0 : ℝ) ≤ 4)
  have hgap_mul :
      (n : ℝ) * (0.02034 : ℝ) ≤
        (n : ℝ) *
          (Real.log 3 -
            ((1 / 2 : ℝ) * Real.log 2 +
              (1 / 3 : ℝ) * Real.log 3 +
              (1 / 7 : ℝ) * Real.log 7 +
              (1 / 43 : ℝ) * Real.log 43)) :=
    mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg n)
  calc
    (n : ℝ) * Real.log n / 1806 + 4 * Real.log n + 4 -
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43)
        ≤ (n : ℝ) * ((m : ℝ) * (0.6931471808 : ℝ)) / 1806 +
            4 * ((m : ℝ) * (0.6931471808 : ℝ)) + 4 - (7.48 : ℝ) := by
          nlinarith
    _ ≤ (n : ℝ) * (0.02034 : ℝ) := hband
    _ ≤ (n : ℝ) *
        (Real.log 3 -
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43)) := by
          exact hgap_mul

theorem hanson_margin_ge_2048_lt_hansonA_five
    {n : ℕ} (hn : 2048 ≤ n) (hN : n < hansonA 5) :
    (n : ℝ) * Real.log n / 1806 + 4 * Real.log n + 4 -
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43) ≤
      (n : ℝ) *
        (Real.log 3 -
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43)) := by
  by_cases h4096 : n < 4096
  · exact hanson_margin_of_dyadic_band
      (n := n) (m := 12) (lo := 2048)
      (by norm_num) (by norm_num) hn
      (by norm_num; exact h4096)
      (by norm_num) (by norm_num)
  · by_cases h8192 : n < 8192
    · exact hanson_margin_of_dyadic_band
        (n := n) (m := 13) (lo := 4096)
        (by norm_num) (by norm_num) (by omega)
        (by norm_num; exact h8192)
        (by norm_num) (by norm_num)
    · by_cases h16384 : n < 16384
      · exact hanson_margin_of_dyadic_band
          (n := n) (m := 14) (lo := 8192)
          (by norm_num) (by norm_num) (by omega)
          (by norm_num; exact h16384)
          (by norm_num) (by norm_num)
      · by_cases h32768 : n < 32768
        · exact hanson_margin_of_dyadic_band
            (n := n) (m := 15) (lo := 16384)
            (by norm_num) (by norm_num) (by omega)
            (by norm_num; exact h32768)
            (by norm_num) (by norm_num)
        · by_cases h65536 : n < 65536
          · exact hanson_margin_of_dyadic_band
              (n := n) (m := 16) (lo := 32768)
              (by norm_num) (by norm_num) (by omega)
              (by norm_num; exact h65536)
              (by norm_num) (by norm_num)
          · by_cases h131072 : n < 131072
            · exact hanson_margin_of_dyadic_band
                (n := n) (m := 17) (lo := 65536)
                (by norm_num) (by norm_num) (by omega)
                (by norm_num; exact h131072)
                (by norm_num) (by norm_num)
            · by_cases h262144 : n < 262144
              · exact hanson_margin_of_dyadic_band
                  (n := n) (m := 18) (lo := 131072)
                  (by norm_num) (by norm_num) (by omega)
                  (by norm_num; exact h262144)
                  (by norm_num) (by norm_num)
              · by_cases h524288 : n < 524288
                · exact hanson_margin_of_dyadic_band
                    (n := n) (m := 19) (lo := 262144)
                    (by norm_num) (by norm_num) (by omega)
                    (by norm_num; exact h524288)
                    (by norm_num) (by norm_num)
                · by_cases h1048576 : n < 1048576
                  · exact hanson_margin_of_dyadic_band
                      (n := n) (m := 20) (lo := 524288)
                      (by norm_num) (by norm_num) (by omega)
                      (by norm_num; exact h1048576)
                      (by norm_num) (by norm_num)
                  · by_cases h2097152 : n < 2097152
                    · exact hanson_margin_of_dyadic_band
                        (n := n) (m := 21) (lo := 1048576)
                        (by norm_num) (by norm_num) (by omega)
                        (by norm_num; exact h2097152)
                        (by norm_num) (by norm_num)
                    · exact hanson_margin_of_dyadic_band
                        (n := n) (m := 22) (lo := 2097152)
                        (by norm_num) (by norm_num) (by omega)
                        (by
                          norm_num [hansonA] at hN ⊢
                          omega)
                        (by norm_num) (by norm_num)

theorem shifted_log_sum_four_lower_ge_2048_lt_hansonA_five
    {n : ℕ} (hn : 2048 ≤ n) (hN : n < hansonA 5) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range 4,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) :=
  shifted_log_sum_four_lower_of_margin
    (by omega : 86 ≤ n)
    (hanson_margin_ge_2048_lt_hansonA_five hn hN)

theorem lcmUpto_le_three_pow_nat_of_hanson_tail_ge_hansonA_five
    (htail : ∀ n : ℕ, hansonA 5 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (n + 1),
            (n / hansonA j) ^ (n / hansonA j)) :
    lcmUpto_le_three_pow_nat_statement :=
  lcmUpto_le_three_pow_nat_of_hansonC_four_shifted_log_lower_ge_2048_lt_hansonA_five
    (fun _ hn hN => shifted_log_sum_four_lower_ge_2048_lt_hansonA_five hn hN)
    htail

theorem hansonA_le_1807_of_lt_five {i : ℕ} (hi : i < 5) :
    hansonA i ≤ 1807 := by
  interval_cases i <;> norm_num [hansonA]

theorem shifted_log_penalty_sum_five_ge_neg_five
    {n : ℕ} (hn : hansonA 5 ≤ n) :
    -5 ≤
      ∑ i ∈ Finset.range 5,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
  have hsum :
      ∑ i ∈ Finset.range 5, (-1 : ℝ) ≤
        ∑ i ∈ Finset.range 5,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
    exact Finset.sum_le_sum fun i hi =>
      shifted_log_penalty_ge_neg_one_of_lt
        (hansonA_pos i)
        (by
          have hle := hansonA_le_1807_of_lt_five (Finset.mem_range.mp hi)
          norm_num [hansonA] at hn
          omega)
  have hconst : (∑ i ∈ Finset.range 5, (-1 : ℝ)) = -5 := by
    norm_num
  rwa [hconst] at hsum

theorem shifted_log_sum_five_eq_base_add_penalty
    {n : ℕ} (hn : hansonA 5 ≤ n) :
    (∑ i ∈ Finset.range 5,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) =
      (∑ i ∈ Finset.range 5,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          (Real.log n - Real.log (hansonA i))) +
      ∑ i ∈ Finset.range 5,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hlt : hansonA i < n := by
    have hle := hansonA_le_1807_of_lt_five (Finset.mem_range.mp hi)
    norm_num [hansonA] at hn
    omega
  have hlog := log_div_sub_one_eq (hansonA_pos i) hlt
  rw [hlog]
  ring

theorem shifted_log_sum_five_lower_of_base_lower
    {n : ℕ} (hn : hansonA 5 ≤ n)
    (hbase :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        (∑ i ∈ Finset.range 5,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            (Real.log n - Real.log (hansonA i))) - 5) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range 5,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) := by
  have hpen := shifted_log_penalty_sum_five_ge_neg_five hn
  rw [shifted_log_sum_five_eq_base_add_penalty hn]
  linarith

theorem hanson_base_sum_five_eq_explicit (n : ℕ) :
    (∑ i ∈ Finset.range 5,
      ((n : ℝ) / (hansonA i : ℝ) - 1) *
        (Real.log n - Real.log (hansonA i))) =
      (((n : ℝ) * (3263441 / 3263442 : ℝ) - 5) * Real.log n) -
        (n : ℝ) *
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43 +
            (1 / 1807 : ℝ) * Real.log 1807) +
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 + Real.log 1807) := by
  norm_num [Finset.sum_range_succ, hansonA]
  ring

theorem explicit_base_five_lower_of_margin
    {n : ℕ}
    (hmargin :
      (n : ℝ) * Real.log n / 3263442 + 5 * Real.log n + 5 -
          (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 + Real.log 1807) ≤
        (n : ℝ) *
          (Real.log 3 -
            ((1 / 2 : ℝ) * Real.log 2 +
              (1 / 3 : ℝ) * Real.log 3 +
              (1 / 7 : ℝ) * Real.log 7 +
              (1 / 43 : ℝ) * Real.log 43 +
              (1 / 1807 : ℝ) * Real.log 1807))) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ((((n : ℝ) * (3263441 / 3263442 : ℝ) - 5) * Real.log n) -
        (n : ℝ) *
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43 +
            (1 / 1807 : ℝ) * Real.log 1807) +
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 + Real.log 1807)) - 5 := by
  nlinarith

theorem shifted_log_sum_five_lower_of_margin
    {n : ℕ} (hn : hansonA 5 ≤ n)
    (hmargin :
      (n : ℝ) * Real.log n / 3263442 + 5 * Real.log n + 5 -
          (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 + Real.log 1807) ≤
        (n : ℝ) *
          (Real.log 3 -
            ((1 / 2 : ℝ) * Real.log 2 +
              (1 / 3 : ℝ) * Real.log 3 +
              (1 / 7 : ℝ) * Real.log 7 +
              (1 / 43 : ℝ) * Real.log 43 +
              (1 / 1807 : ℝ) * Real.log 1807))) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range 5,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) := by
  refine shifted_log_sum_five_lower_of_base_lower hn ?_
  rw [hanson_base_sum_five_eq_explicit]
  exact explicit_base_five_lower_of_margin hmargin

theorem log_1807_over_1806_le :
    Real.log ((1807 : ℝ) / 1806) ≤ (1 / 1806 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (1807 : ℝ) / 1806)
  norm_num at h ⊢
  exact h

theorem log_1807_decomp :
    Real.log (1807 : ℝ) =
      Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
        Real.log ((1807 : ℝ) / 1806) := by
  have h :
      Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
          Real.log ((1807 : ℝ) / 1806) =
        Real.log (1807 : ℝ) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    rw [← Real.log_mul (by norm_num : ((2 : ℝ) * 3) ≠ 0) (by norm_num : (7 : ℝ) ≠ 0)]
    rw [← Real.log_mul
      (by norm_num : ((2 : ℝ) * 3 * 7) ≠ 0)
      (by norm_num : (43 : ℝ) ≠ 0)]
    rw [← Real.log_mul
      (by norm_num : ((2 : ℝ) * 3 * 7 * 43) ≠ 0)
      (by norm_num : ((1807 : ℝ) / 1806) ≠ 0)]
    norm_num
  exact h.symm

theorem log_1807_lt_7_501 :
    Real.log (1807 : ℝ) < (7.501 : ℝ) := by
  rw [log_1807_decomp]
  have h2 : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have h3 : Real.log 3 < (1.0986122888 : ℝ) := Real.log_three_lt_d9
  have h7 : Real.log 7 < (1.946 : ℝ) := log_seven_lt_1_946
  have h43 : Real.log 43 < (3.762 : ℝ) := log_forty_three_lt_3_762
  have hratio : Real.log ((1807 : ℝ) / 1806) ≤ (1 / 1806 : ℝ) :=
    log_1807_over_1806_le
  nlinarith

theorem hanson_log_weight_five_gap_ge_0_01618 :
    (0.01618 : ℝ) ≤
      Real.log 3 -
        ((1 / 2 : ℝ) * Real.log 2 +
          (1 / 3 : ℝ) * Real.log 3 +
          (1 / 7 : ℝ) * Real.log 7 +
          (1 / 43 : ℝ) * Real.log 43 +
          (1 / 1807 : ℝ) * Real.log 1807) := by
  have hgap4 := hanson_log_weight_four_gap_ge_0_02034
  have h1807 : Real.log 1807 < (7.501 : ℝ) := log_1807_lt_7_501
  nlinarith

theorem log_1807_gt_6_9 :
    (6.9 : ℝ) < Real.log (1807 : ℝ) := by
  have hlt : Real.log (1024 : ℝ) < Real.log (1807 : ℝ) :=
    Real.log_lt_log (by norm_num : (0 : ℝ) < 1024)
      (by norm_num : (1024 : ℝ) < 1807)
  have hlog1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [hlog1024] at hlt
  nlinarith

theorem hanson_log_product_five_gt_14 :
    (14 : ℝ) < Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 + Real.log 1807 := by
  have h4 : (7.48 : ℝ) < Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 :=
    hanson_log_product_four_gt_7_48
  have h1807 : (6.9 : ℝ) < Real.log (1807 : ℝ) := log_1807_gt_6_9
  nlinarith

theorem hanson_margin_five_ge_hansonA_five_lt_hansonA_six
    {n : ℕ} (hlo : hansonA 5 ≤ n) (hhi : n < hansonA 6) :
    (n : ℝ) * Real.log n / 3263442 + 5 * Real.log n + 5 -
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 + Real.log 1807) ≤
      (n : ℝ) *
        (Real.log 3 -
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43 +
            (1 / 1807 : ℝ) * Real.log 1807)) := by
  have hn_pos : 0 < n := by
    norm_num [hansonA] at hlo
    omega
  have hhi44 : n < 2 ^ 44 := by
    norm_num [hansonA] at hhi ⊢
    omega
  have hlog_lt :
      Real.log (n : ℝ) < (44 : ℝ) * (0.6931471808 : ℝ) :=
    log_nat_lt_of_lt_two_pow (by norm_num) hn_pos hhi44
  have hlog_le :
      Real.log (n : ℝ) ≤ (44 : ℝ) * (0.6931471808 : ℝ) :=
    le_of_lt hlog_lt
  have hprod_le :
      (14 : ℝ) ≤ Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 + Real.log 1807 :=
    le_of_lt hanson_log_product_five_gt_14
  have hgap := hanson_log_weight_five_gap_ge_0_01618
  have hnloR : (3263443 : ℝ) ≤ (n : ℝ) := by
    norm_num [hansonA] at hlo
    exact_mod_cast hlo
  have hband :
      (n : ℝ) * ((44 : ℝ) * (0.6931471808 : ℝ)) / 3263442 +
          5 * ((44 : ℝ) * (0.6931471808 : ℝ)) + 5 - (14 : ℝ) ≤
        (n : ℝ) * (0.01618 : ℝ) := by
    nlinarith
  have hlog_mul :
      (n : ℝ) * Real.log n / 3263442 ≤
        (n : ℝ) * ((44 : ℝ) * (0.6931471808 : ℝ)) / 3263442 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog_le (Nat.cast_nonneg n))
      (by norm_num : (0 : ℝ) ≤ 3263442)
  have hlog_five :
      5 * Real.log n ≤ 5 * ((44 : ℝ) * (0.6931471808 : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hlog_le (by norm_num : (0 : ℝ) ≤ 5)
  have hgap_mul :
      (n : ℝ) * (0.01618 : ℝ) ≤
        (n : ℝ) *
          (Real.log 3 -
            ((1 / 2 : ℝ) * Real.log 2 +
              (1 / 3 : ℝ) * Real.log 3 +
              (1 / 7 : ℝ) * Real.log 7 +
              (1 / 43 : ℝ) * Real.log 43 +
              (1 / 1807 : ℝ) * Real.log 1807)) :=
    mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg n)
  calc
    (n : ℝ) * Real.log n / 3263442 + 5 * Real.log n + 5 -
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 + Real.log 1807)
        ≤ (n : ℝ) * ((44 : ℝ) * (0.6931471808 : ℝ)) / 3263442 +
            5 * ((44 : ℝ) * (0.6931471808 : ℝ)) + 5 - (14 : ℝ) := by
          nlinarith
    _ ≤ (n : ℝ) * (0.01618 : ℝ) := hband
    _ ≤ (n : ℝ) *
        (Real.log 3 -
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43 +
            (1 / 1807 : ℝ) * Real.log 1807)) := by
          exact hgap_mul

theorem shifted_log_sum_five_lower_ge_hansonA_five_lt_hansonA_six
    {n : ℕ} (hlo : hansonA 5 ≤ n) (hhi : n < hansonA 6) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range 5,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) :=
  shifted_log_sum_five_lower_of_margin hlo
    (hanson_margin_five_ge_hansonA_five_lt_hansonA_six hlo hhi)

theorem two_mul_hansonA_le_3614_of_lt_five {i : ℕ} (hi : i < 5) :
    2 * hansonA i ≤ 3614 := by
  interval_cases i <;> norm_num [hansonA]

theorem floor_log_sum_five_lower_of_ge_3614
    {n : ℕ} (hn : 3614 ≤ n) :
    (∑ i ∈ Finset.range 5,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) ≤
      ∑ i ∈ Finset.range 5,
        ((n / hansonA i : ℕ) : ℝ) *
          Real.log ((n / hansonA i : ℕ) : ℝ) := by
  exact Finset.sum_le_sum fun i hi =>
    div_sub_one_mul_log_le_floor_mul_log_of_two_mul_le
      (hansonA_pos i)
      ((two_mul_hansonA_le_3614_of_lt_five (Finset.mem_range.mp hi)).trans hn)

theorem floor_pow_log_lower_five_of_shifted_log_lower
    {n : ℕ} (hn : 3614 ≤ n)
    (hlower :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ∑ i ∈ Finset.range 5,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ j ∈ Finset.range 5,
        ((n / hansonA j : ℕ) : ℝ) *
          Real.log ((n / hansonA j : ℕ) : ℝ) :=
  hlower.trans (floor_log_sum_five_lower_of_ge_3614 hn)

theorem hansonC_five_le_three_pow_of_shifted_log_lower
    {n : ℕ} (hn : 3614 ≤ n)
    (hlower :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ∑ i ∈ Finset.range 5,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) :
    hansonC n 5 ≤ 3 ^ n :=
  hansonC_le_three_pow_of_log_le n 5
    (log_hansonC_le_log_three_of_floor_pow_log_lower
      (n := n) (k := 5) (by omega)
      (floor_pow_log_lower_five_of_shifted_log_lower hn hlower))

theorem lcmUpto_le_three_pow_nat_of_hanson_tail_ge_hansonA_six
    (htail : ∀ n : ℕ, hansonA 6 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (n + 1),
            (n / hansonA j) ^ (n / hansonA j)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
    2048 ?_ (fun n => if n < hansonA 5 then 4 else if n < hansonA 6 then 5 else n + 1) ?_
  · intro n hn
    by_cases h882 : n < 882
    · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
        (hansonC_succ_index_le_three_pow_of_lt_882 h882)).bound
    · by_cases h1807 : n < 1807
      · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
          (hansonC_succ_index_le_three_pow_of_ge_882_lt_1807
            (Nat.le_of_not_gt h882) h1807)).bound
      · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
          (hansonC_succ_index_le_three_pow_of_ge_1807_lt_2048
            (Nat.le_of_not_gt h1807) hn)).bound
  · intro n hn
    by_cases h5 : n < hansonA 5
    · simpa only [h5, ↓reduceIte] using
        hansonC_four_le_three_pow_of_shifted_log_lower
        (by omega : 86 ≤ n)
        (shifted_log_sum_four_lower_ge_2048_lt_hansonA_five hn h5)
    · by_cases h6 : n < hansonA 6
      · simpa only [h5, h6, ↓reduceIte] using
          hansonC_five_le_three_pow_of_shifted_log_lower
          (by
            have hn5 : hansonA 5 ≤ n := Nat.le_of_not_gt h5
            norm_num [hansonA] at hn5
            omega : 3614 ≤ n)
          (shifted_log_sum_five_lower_ge_hansonA_five_lt_hansonA_six
            (Nat.le_of_not_gt h5) h6)
      · simpa only [h5, h6, ↓reduceIte] using
          hansonC_le_three_pow_of_floor_pow_prod_lower
          n (n + 1) (htail n (Nat.le_of_not_gt h6))

theorem hansonA_le_3263443_of_lt_six {i : ℕ} (hi : i < 6) :
    hansonA i ≤ 3263443 := by
  interval_cases i <;> norm_num [hansonA]

theorem shifted_log_penalty_sum_six_ge_neg_six
    {n : ℕ} (hn : hansonA 6 ≤ n) :
    -6 ≤
      ∑ i ∈ Finset.range 6,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
  have hsum :
      ∑ i ∈ Finset.range 6, (-1 : ℝ) ≤
        ∑ i ∈ Finset.range 6,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
    exact Finset.sum_le_sum fun i hi =>
      shifted_log_penalty_ge_neg_one_of_lt
        (hansonA_pos i)
        (by
          have hle := hansonA_le_3263443_of_lt_six (Finset.mem_range.mp hi)
          norm_num [hansonA] at hn
          omega)
  have hconst : (∑ i ∈ Finset.range 6, (-1 : ℝ)) = -6 := by
    norm_num
  rwa [hconst] at hsum

theorem shifted_log_sum_six_eq_base_add_penalty
    {n : ℕ} (hn : hansonA 6 ≤ n) :
    (∑ i ∈ Finset.range 6,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) =
      (∑ i ∈ Finset.range 6,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          (Real.log n - Real.log (hansonA i))) +
      ∑ i ∈ Finset.range 6,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((1 : ℝ) - (hansonA i : ℝ) / (n : ℝ)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hlt : hansonA i < n := by
    have hle := hansonA_le_3263443_of_lt_six (Finset.mem_range.mp hi)
    norm_num [hansonA] at hn
    omega
  have hlog := log_div_sub_one_eq (hansonA_pos i) hlt
  rw [hlog]
  ring

theorem shifted_log_sum_six_lower_of_base_lower
    {n : ℕ} (hn : hansonA 6 ≤ n)
    (hbase :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        (∑ i ∈ Finset.range 6,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            (Real.log n - Real.log (hansonA i))) - 6) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range 6,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) := by
  have hpen := shifted_log_penalty_sum_six_ge_neg_six hn
  rw [shifted_log_sum_six_eq_base_add_penalty hn]
  linarith

theorem hanson_base_sum_six_eq_explicit (n : ℕ) :
    (∑ i ∈ Finset.range 6,
      ((n : ℝ) / (hansonA i : ℝ) - 1) *
        (Real.log n - Real.log (hansonA i))) =
      (((n : ℝ) * (10650056950805 / 10650056950806 : ℝ) - 6) *
          Real.log n) -
        (n : ℝ) *
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43 +
            (1 / 1807 : ℝ) * Real.log 1807 +
            (1 / 3263443 : ℝ) * Real.log 3263443) +
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
          Real.log 1807 + Real.log 3263443) := by
  norm_num [Finset.sum_range_succ, hansonA]
  ring

theorem explicit_base_six_lower_of_margin
    {n : ℕ}
    (hmargin :
      (n : ℝ) * Real.log n / 10650056950806 + 6 * Real.log n + 6 -
          (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
            Real.log 1807 + Real.log 3263443) ≤
        (n : ℝ) *
          (Real.log 3 -
            ((1 / 2 : ℝ) * Real.log 2 +
              (1 / 3 : ℝ) * Real.log 3 +
              (1 / 7 : ℝ) * Real.log 7 +
              (1 / 43 : ℝ) * Real.log 43 +
              (1 / 1807 : ℝ) * Real.log 1807 +
              (1 / 3263443 : ℝ) * Real.log 3263443))) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ((((n : ℝ) * (10650056950805 / 10650056950806 : ℝ) - 6) *
          Real.log n) -
        (n : ℝ) *
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43 +
            (1 / 1807 : ℝ) * Real.log 1807 +
            (1 / 3263443 : ℝ) * Real.log 3263443) +
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
          Real.log 1807 + Real.log 3263443)) - 6 := by
  nlinarith

theorem shifted_log_sum_six_lower_of_margin
    {n : ℕ} (hn : hansonA 6 ≤ n)
    (hmargin :
      (n : ℝ) * Real.log n / 10650056950806 + 6 * Real.log n + 6 -
          (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
            Real.log 1807 + Real.log 3263443) ≤
        (n : ℝ) *
          (Real.log 3 -
            ((1 / 2 : ℝ) * Real.log 2 +
              (1 / 3 : ℝ) * Real.log 3 +
              (1 / 7 : ℝ) * Real.log 7 +
              (1 / 43 : ℝ) * Real.log 43 +
              (1 / 1807 : ℝ) * Real.log 1807 +
              (1 / 3263443 : ℝ) * Real.log 3263443))) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range 6,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) := by
  refine shifted_log_sum_six_lower_of_base_lower hn ?_
  rw [hanson_base_sum_six_eq_explicit]
  exact explicit_base_six_lower_of_margin hmargin

theorem log_3263443_lt_15_25 :
    Real.log (3263443 : ℝ) < (15.25 : ℝ) := by
  have h := log_nat_lt_of_lt_two_pow
    (n := 3263443) (m := 22)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  nlinarith

theorem hanson_log_weight_six_gap_ge_0_01617 :
    (0.01617 : ℝ) ≤
      Real.log 3 -
        ((1 / 2 : ℝ) * Real.log 2 +
          (1 / 3 : ℝ) * Real.log 3 +
          (1 / 7 : ℝ) * Real.log 7 +
          (1 / 43 : ℝ) * Real.log 43 +
          (1 / 1807 : ℝ) * Real.log 1807 +
          (1 / 3263443 : ℝ) * Real.log 3263443) := by
  have hgap5 := hanson_log_weight_five_gap_ge_0_01618
  have h3263443 : Real.log 3263443 < (15.25 : ℝ) := log_3263443_lt_15_25
  nlinarith

theorem hanson_log_weight_six_sum_eq_explicit :
    (∑ i ∈ Finset.range 6,
      ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i)) =
      ((1 / 2 : ℝ) * Real.log 2 +
        (1 / 3 : ℝ) * Real.log 3 +
        (1 / 7 : ℝ) * Real.log 7 +
        (1 / 43 : ℝ) * Real.log 43 +
        (1 / 1807 : ℝ) * Real.log 1807 +
        (1 / 3263443 : ℝ) * Real.log 3263443) := by
  norm_num [Finset.sum_range_succ, hansonA]

theorem hanson_log_weight_six_gap_range_ge_0_01617 :
    (0.01617 : ℝ) ≤
      Real.log 3 -
        ∑ i ∈ Finset.range 6,
          ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i) := by
  rw [hanson_log_weight_six_sum_eq_explicit]
  exact hanson_log_weight_six_gap_ge_0_01617

theorem hanson_log_weight_gap_ge_0_01616_of_six_le
    {k : ℕ} (hk : 6 ≤ k) :
    (0.01616 : ℝ) ≤
      Real.log 3 -
        ∑ i ∈ Finset.range k,
          ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i) := by
  have htail :
      2 * ((1 : ℝ) / ((hansonA (6 - 1) : ℝ) - 1)) ≤
        (0.00001 : ℝ) := by
    norm_num [hansonA]
  have h := hanson_log_weight_gap_ge_of_range_tail
    (m := 6) (k := k) (gap := (0.01617 : ℝ)) (eps := (0.00001 : ℝ))
    (by norm_num) hk hanson_log_weight_six_gap_range_ge_0_01617 htail
  norm_num at h ⊢
  exact h

theorem log_le_two_log_hansonA_of_lt_succ
    {n k : ℕ} (hn : 1 ≤ n) (hhi : n < hansonA (k + 1)) :
    Real.log (n : ℝ) ≤ 2 * Real.log (hansonA k : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hle_nat : n ≤ hansonA k ^ 2 :=
    (le_of_lt hhi).trans (hansonA_succ_le_sq k)
  have hleR : (n : ℝ) ≤ ((hansonA k ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hle_nat
  have hlog := Real.log_le_log hn_pos hleR
  have hpowlog :
      Real.log (((hansonA k ^ 2 : ℕ) : ℝ)) =
        2 * Real.log (hansonA k : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rwa [hpowlog] at hlog

theorem hansonA_pred_sub_one_mul_cast
    {k : ℕ} (hk : 1 ≤ k) :
    ((hansonA k : ℝ) - 1) =
      ((hansonA (k - 1) : ℝ) - 1) * (hansonA (k - 1) : ℝ) := by
  have hs : k - 1 + 1 = k := by omega
  rw [← hs]
  have hnat := hansonA_succ_sub_one (k - 1)
  have hleft : ((hansonA (k - 1 + 1) : ℝ) - 1) =
      ((hansonA (k - 1 + 1) - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub]
    · norm_num
    · exact (by norm_num : 1 ≤ 2).trans (two_le_hansonA (k - 1 + 1))
  rw [hleft]
  rw [hnat]
  rw [Nat.cast_mul, Nat.cast_sub]
  · have hidx : k - 1 + 1 - 1 = k - 1 := by omega
    rw [hidx]
    ring
  · exact (by norm_num : 1 ≤ 2).trans (two_le_hansonA (k - 1))

theorem two_thousand_mul_index_le_hansonA_pred
    {k : ℕ} (hk : 6 ≤ k) :
    2000 * k ≤ hansonA (k - 1) := by
  exact Nat.le_induction (m := 6)
    (P := fun k _ => 2000 * k ≤ hansonA (k - 1))
    (by norm_num [hansonA])
    (by
      intro k hk ih
      have hkpred : (k + 1) - 1 = k := by omega
      rw [hkpred]
      have hkm1 : k - 1 + 1 = k := by omega
      have hincr : hansonA (k - 1) + 2000 ≤ hansonA k := by
        rw [← hkm1]
        dsimp [hansonA]
        let a := hansonA (k - 1)
        have ha46 : 46 ≤ a := by
          dsimp [a]
          have h5 : 5 ≤ k - 1 := by omega
          have hmono : hansonA 5 ≤ hansonA (k - 1) :=
            hansonA_strictMono.monotone h5
          norm_num [hansonA] at hmono ⊢
          omega
        have ha_le_sq : a ≤ a ^ 2 := by
          rw [pow_two]
          exact Nat.le_mul_of_pos_left a (by omega)
        have hEq : a ^ 2 - a + 1 = a ^ 2 + 1 - a := by omega
        rw [hEq]
        rw [Nat.le_sub_iff_add_le (by omega : a ≤ a ^ 2 + 1)]
        nlinarith
      have hstep : 2000 * (k + 1) ≤ hansonA (k - 1) + 2000 := by
        nlinarith
      exact hstep.trans hincr)
    k hk

theorem hanson_log_div_pred_le_0_00001
    {k : ℕ} (hk : 6 ≤ k) :
    (2 * Real.log (hansonA k : ℝ)) / ((hansonA k : ℝ) - 1) ≤
      (0.00001 : ℝ) := by
  have hk1 : 2 ≤ k - 1 := by omega
  have hs : k - 1 + 1 = k := by omega
  have hlog := log_hansonA_succ_le_hansonA (j := k - 1) hk1
  rw [hs] at hlog
  let b := hansonA (k - 1)
  have hb_large_nat : 3263443 ≤ b := by
    dsimp [b]
    have h5 : 5 ≤ k - 1 := by omega
    have hmono : hansonA 5 ≤ hansonA (k - 1) :=
      hansonA_strictMono.monotone h5
    norm_num [hansonA] at hmono ⊢
    omega
  have hb_pos : (0 : ℝ) < b := by
    dsimp [b]
    exact_mod_cast hansonA_pos (k - 1)
  have hb_minus_pos : (0 : ℝ) < (b : ℝ) - 1 := by
    have hb_large : (3263443 : ℝ) ≤ b := by exact_mod_cast hb_large_nat
    linarith
  have hden_eq : ((hansonA k : ℝ) - 1) = ((b : ℝ) - 1) * (b : ℝ) := by
    dsimp [b]
    exact hansonA_pred_sub_one_mul_cast (by omega : 1 ≤ k)
  rw [hden_eq]
  have hden_pos : 0 < ((b : ℝ) - 1) * (b : ℝ) :=
    mul_pos hb_minus_pos hb_pos
  have hnum_le : 2 * Real.log (hansonA k : ℝ) ≤ 2 * (b : ℝ) := by
    dsimp [b]
    exact mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 2)
  have hmain :
      (2 * (b : ℝ)) / (((b : ℝ) - 1) * (b : ℝ)) ≤ (0.00001 : ℝ) := by
    have hb_large : (3263443 : ℝ) ≤ b := by exact_mod_cast hb_large_nat
    field_simp [hb_pos.ne', hb_minus_pos.ne']
    nlinarith
  exact (div_le_div_of_nonneg_right hnum_le (le_of_lt hden_pos)).trans hmain

theorem hanson_endpoint_linear_margin_of_six_le
    {k : ℕ} (hk : 6 ≤ k) :
    (k : ℝ) * (2 * Real.log (hansonA k : ℝ)) + (k : ℝ) ≤
      ((0.01616 : ℝ) -
          (2 * Real.log (hansonA k : ℝ)) / ((hansonA k : ℝ) - 1)) *
        (hansonA k : ℝ) := by
  have hk1 : 2 ≤ k - 1 := by omega
  have hs : k - 1 + 1 = k := by omega
  let b := hansonA (k - 1)
  have hb_large_nat : 3263443 ≤ b := by
    dsimp [b]
    have h5 : 5 ≤ k - 1 := by omega
    have hmono : hansonA 5 ≤ hansonA (k - 1) :=
      hansonA_strictMono.monotone h5
    norm_num [hansonA] at hmono ⊢
    omega
  have hb_large : (3263443 : ℝ) ≤ b := by exact_mod_cast hb_large_nat
  have hlog := log_hansonA_succ_le_hansonA (j := k - 1) hk1
  rw [hs] at hlog
  have hk_small_nat := two_thousand_mul_index_le_hansonA_pred hk
  have hk_small_cast :
      (2000 : ℝ) * (k : ℝ) ≤ (hansonA (k - 1) : ℝ) := by
    exact_mod_cast hk_small_nat
  have hk_small : (k : ℝ) ≤ (b : ℝ) / 2000 := by
    dsimp [b] at hk_small_nat ⊢
    nlinarith
  have hAk_eq : (hansonA k : ℝ) = (b : ℝ) ^ 2 - (b : ℝ) + 1 := by
    dsimp [b]
    rw [← hs]
    dsimp [hansonA]
    have hb_pos_nat : 0 < hansonA (k - 1) := hansonA_pos (k - 1)
    have hb_le_sq_nat : hansonA (k - 1) ≤ hansonA (k - 1) ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_left _ hb_pos_nat
    rw [Nat.cast_add, Nat.cast_sub hb_le_sq_nat, Nat.cast_pow]
    norm_num
  have hfrac := hanson_log_div_pred_le_0_00001 hk
  have hcoef_lower : (0.01615 : ℝ) ≤
      (0.01616 : ℝ) -
        (2 * Real.log (hansonA k : ℝ)) / ((hansonA k : ℝ) - 1) := by
    nlinarith
  have hleft :
      (k : ℝ) * (2 * Real.log (hansonA k : ℝ)) + (k : ℝ) ≤
        (0.01615 : ℝ) * (hansonA k : ℝ) := by
    calc
      (k : ℝ) * (2 * Real.log (hansonA k : ℝ)) + (k : ℝ)
          ≤ ((b : ℝ) / 2000) * (2 * (b : ℝ)) + (b : ℝ) / 2000 := by
            nlinarith
      _ ≤ (0.01615 : ℝ) * ((b : ℝ) ^ 2 - (b : ℝ) + 1) := by
            nlinarith
      _ = (0.01615 : ℝ) * (hansonA k : ℝ) := by rw [hAk_eq]
  have hrhs :
      (0.01615 : ℝ) * (hansonA k : ℝ) ≤
        ((0.01616 : ℝ) -
            (2 * Real.log (hansonA k : ℝ)) / ((hansonA k : ℝ) - 1)) *
          (hansonA k : ℝ) := by
    exact mul_le_mul_of_nonneg_right hcoef_lower (Nat.cast_nonneg _)
  exact hleft.trans hrhs

theorem hanson_closed_margin_of_hanson_band_ge_six
    {n k : ℕ} (hk : 6 ≤ k)
    (hlo : hansonA k ≤ n) (hhi : n < hansonA (k + 1)) :
    (n : ℝ) * Real.log n / ((hansonA k : ℝ) - 1) +
          (k : ℝ) * Real.log n + (k : ℝ) -
        Real.log ((hansonA k - 1 : ℕ) : ℝ) ≤
      (n : ℝ) *
        (Real.log 3 -
          ∑ i ∈ Finset.range k,
            ((1 : ℝ) / (hansonA i : ℝ)) * Real.log (hansonA i)) := by
  have hn : 1 ≤ n := by
    have hpos := hansonA_pos k
    omega
  exact hanson_closed_margin_of_endpoint_log_le
    (lo := hansonA k) (L := 2 * Real.log (hansonA k : ℝ))
    (gap := (0.01616 : ℝ))
    hlo
    (log_le_two_log_hansonA_of_lt_succ hn hhi)
    (hanson_log_weight_gap_ge_0_01616_of_six_le hk)
    (by
      have hfrac := hanson_log_div_pred_le_0_00001 hk
      nlinarith)
    (hanson_endpoint_linear_margin_of_six_le hk)

theorem hansonA_index_add_two_le (k : ℕ) :
    k + 2 ≤ hansonA k := by
  induction k with
  | zero =>
      norm_num [hansonA]
  | succ k ih =>
      have hsucc : hansonA k + 1 ≤ hansonA (k + 1) :=
        Nat.succ_le_of_lt (hansonA_lt_succ k)
      omega

theorem exists_hansonA_succ_gt (n : ℕ) :
    ∃ k : ℕ, n < hansonA (k + 1) := by
  refine ⟨n, ?_⟩
  have h := hansonA_index_add_two_le (n + 1)
  omega

def hansonBandIndex (n : ℕ) : ℕ :=
  Nat.find (exists_hansonA_succ_gt n)

theorem hansonBandIndex_upper (n : ℕ) :
    n < hansonA (hansonBandIndex n + 1) := by
  exact Nat.find_spec (exists_hansonA_succ_gt n)

theorem hansonBandIndex_ge_six
    {n : ℕ} (hn : hansonA 6 ≤ n) :
    6 ≤ hansonBandIndex n := by
  by_contra hnot
  have hlt : hansonBandIndex n < 6 := Nat.lt_of_not_ge hnot
  have hupper := hansonBandIndex_upper n
  have hmono : hansonA (hansonBandIndex n + 1) ≤ hansonA 6 :=
    hansonA_strictMono.monotone (by omega : hansonBandIndex n + 1 ≤ 6)
  omega

theorem hansonBandIndex_lower
    {n : ℕ} (hn : hansonA 6 ≤ n) :
    hansonA (hansonBandIndex n) ≤ n := by
  have hk6 := hansonBandIndex_ge_six hn
  have hpred_lt : hansonBandIndex n - 1 < hansonBandIndex n := by omega
  have hnot := Nat.find_min (exists_hansonA_succ_gt n) hpred_lt
  have hidx : hansonBandIndex n - 1 + 1 = hansonBandIndex n := by omega
  rw [hidx] at hnot
  exact Nat.le_of_not_gt hnot

theorem hansonC_bandIndex_le_three_pow_of_ge_hansonA_six
    {n : ℕ} (hn : hansonA 6 ≤ n) :
    hansonC n (hansonBandIndex n) ≤ 3 ^ n := by
  have hk6 := hansonBandIndex_ge_six hn
  have hlo := hansonBandIndex_lower hn
  have hhi := hansonBandIndex_upper n
  have hfloor :
      ∀ i : ℕ, i ∈ Finset.range (hansonBandIndex n) →
        2 * hansonA i ≤ n := by
    intro i hi
    exact two_mul_hansonA_le_of_mem_range_of_hansonA_le
      (by omega : 2 ≤ hansonBandIndex n) hlo hi
  have hclosed :=
    hanson_closed_margin_of_hanson_band_ge_six hk6 hlo hhi
  have hshift :=
    shifted_log_sum_lower_of_hanson_closed_margin hlo hclosed
  exact hansonC_le_three_pow_of_shifted_log_lower
    (by
      have hpos := hansonA_pos 6
      omega : 1 ≤ n)
    hfloor hshift

theorem lcmUpto_le_three_pow_nat_unconditional :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
    2048 ?_
    (fun n => if n < hansonA 5 then 4 else if n < hansonA 6 then 5 else hansonBandIndex n)
    ?_
  · intro n hn
    by_cases h882 : n < 882
    · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
        (hansonC_succ_index_le_three_pow_of_lt_882 h882)).bound
    · by_cases h1807 : n < 1807
      · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
          (hansonC_succ_index_le_three_pow_of_ge_882_lt_1807
            (Nat.le_of_not_gt h882) h1807)).bound
      · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
          (hansonC_succ_index_le_three_pow_of_ge_1807_lt_2048
            (Nat.le_of_not_gt h1807) hn)).bound
  · intro n hn
    by_cases h5 : n < hansonA 5
    · simpa only [h5, ↓reduceIte] using
        hansonC_four_le_three_pow_of_shifted_log_lower
        (by omega : 86 ≤ n)
        (shifted_log_sum_four_lower_ge_2048_lt_hansonA_five hn h5)
    · by_cases h6 : n < hansonA 6
      · simpa only [h5, h6, ↓reduceIte] using
          hansonC_five_le_three_pow_of_shifted_log_lower
          (by
            have hn5 : hansonA 5 ≤ n := Nat.le_of_not_gt h5
            norm_num [hansonA] at hn5
            omega : 3614 ≤ n)
          (shifted_log_sum_five_lower_ge_hansonA_five_lt_hansonA_six
            (Nat.le_of_not_gt h5) h6)
      · simpa only [h5, h6, ↓reduceIte] using
          hansonC_bandIndex_le_three_pow_of_ge_hansonA_six
            (Nat.le_of_not_gt h6)

theorem hanson_log_product_six_nonneg :
    0 ≤ Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
      Real.log 1807 + Real.log 3263443 := by
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have h7 : 0 ≤ Real.log (7 : ℝ) := Real.log_nonneg (by norm_num)
  have h43 : 0 ≤ Real.log (43 : ℝ) := Real.log_nonneg (by norm_num)
  have h1807 : 0 ≤ Real.log (1807 : ℝ) := Real.log_nonneg (by norm_num)
  have h3263443 : 0 ≤ Real.log (3263443 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith

theorem hanson_margin_six_ge_hansonA_six_lt_hansonA_seven
    {n : ℕ} (hlo : hansonA 6 ≤ n) (hhi : n < hansonA 7) :
    (n : ℝ) * Real.log n / 10650056950806 + 6 * Real.log n + 6 -
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
          Real.log 1807 + Real.log 3263443) ≤
      (n : ℝ) *
        (Real.log 3 -
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43 +
            (1 / 1807 : ℝ) * Real.log 1807 +
            (1 / 3263443 : ℝ) * Real.log 3263443)) := by
  have hn_pos : 0 < n := by
    norm_num [hansonA] at hlo
    omega
  have hhi87 : n < 2 ^ 87 := by
    norm_num [hansonA] at hhi ⊢
    omega
  have hlog_lt :
      Real.log (n : ℝ) < (87 : ℝ) * (0.6931471808 : ℝ) :=
    log_nat_lt_of_lt_two_pow (by norm_num) hn_pos hhi87
  have hlog_le :
      Real.log (n : ℝ) ≤ (87 : ℝ) * (0.6931471808 : ℝ) :=
    le_of_lt hlog_lt
  have hprod_nonneg := hanson_log_product_six_nonneg
  have hgap := hanson_log_weight_six_gap_ge_0_01617
  have hnloR : (10650056950807 : ℝ) ≤ (n : ℝ) := by
    norm_num [hansonA] at hlo
    exact_mod_cast hlo
  have hband :
      (n : ℝ) * ((87 : ℝ) * (0.6931471808 : ℝ)) / 10650056950806 +
          6 * ((87 : ℝ) * (0.6931471808 : ℝ)) + 6 ≤
        (n : ℝ) * (0.01617 : ℝ) := by
    nlinarith
  have hlog_mul :
      (n : ℝ) * Real.log n / 10650056950806 ≤
        (n : ℝ) * ((87 : ℝ) * (0.6931471808 : ℝ)) / 10650056950806 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog_le (Nat.cast_nonneg n))
      (by norm_num : (0 : ℝ) ≤ 10650056950806)
  have hlog_six :
      6 * Real.log n ≤ 6 * ((87 : ℝ) * (0.6931471808 : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hlog_le (by norm_num : (0 : ℝ) ≤ 6)
  have hgap_mul :
      (n : ℝ) * (0.01617 : ℝ) ≤
        (n : ℝ) *
          (Real.log 3 -
            ((1 / 2 : ℝ) * Real.log 2 +
              (1 / 3 : ℝ) * Real.log 3 +
              (1 / 7 : ℝ) * Real.log 7 +
              (1 / 43 : ℝ) * Real.log 43 +
              (1 / 1807 : ℝ) * Real.log 1807 +
              (1 / 3263443 : ℝ) * Real.log 3263443)) :=
    mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg n)
  calc
    (n : ℝ) * Real.log n / 10650056950806 + 6 * Real.log n + 6 -
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
          Real.log 1807 + Real.log 3263443)
        ≤ (n : ℝ) * ((87 : ℝ) * (0.6931471808 : ℝ)) / 10650056950806 +
            6 * ((87 : ℝ) * (0.6931471808 : ℝ)) + 6 := by
          nlinarith
    _ ≤ (n : ℝ) * (0.01617 : ℝ) := hband
    _ ≤ (n : ℝ) *
        (Real.log 3 -
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43 +
            (1 / 1807 : ℝ) * Real.log 1807 +
            (1 / 3263443 : ℝ) * Real.log 3263443)) := by
          exact hgap_mul

theorem shifted_log_sum_six_lower_ge_hansonA_six_lt_hansonA_seven
    {n : ℕ} (hlo : hansonA 6 ≤ n) (hhi : n < hansonA 7) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range 6,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) :=
  shifted_log_sum_six_lower_of_margin hlo
    (hanson_margin_six_ge_hansonA_six_lt_hansonA_seven hlo hhi)

theorem hanson_margin_six_ge_hansonA_seven_lt_hansonA_eight
    {n : ℕ} (hlo : hansonA 7 ≤ n) (hhi : n < hansonA 8) :
    (n : ℝ) * Real.log n / 10650056950806 + 6 * Real.log n + 6 -
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
          Real.log 1807 + Real.log 3263443) ≤
      (n : ℝ) *
        (Real.log 3 -
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43 +
            (1 / 1807 : ℝ) * Real.log 1807 +
            (1 / 3263443 : ℝ) * Real.log 3263443)) := by
  have hn_pos : 0 < n := by
    norm_num [hansonA] at hlo
    omega
  have hhi174 : n < 2 ^ 174 := by
    norm_num [hansonA] at hhi ⊢
    omega
  have hlog_lt :
      Real.log (n : ℝ) < (174 : ℝ) * (0.6931471808 : ℝ) :=
    log_nat_lt_of_lt_two_pow (by norm_num) hn_pos hhi174
  have hlog_le :
      Real.log (n : ℝ) ≤ (174 : ℝ) * (0.6931471808 : ℝ) :=
    le_of_lt hlog_lt
  have hprod_nonneg := hanson_log_product_six_nonneg
  have hgap := hanson_log_weight_six_gap_ge_0_01617
  have hnloR : (113423713055421844361000443 : ℝ) ≤ (n : ℝ) := by
    norm_num [hansonA] at hlo
    exact_mod_cast hlo
  have hband :
      (n : ℝ) * ((174 : ℝ) * (0.6931471808 : ℝ)) / 10650056950806 +
          6 * ((174 : ℝ) * (0.6931471808 : ℝ)) + 6 ≤
        (n : ℝ) * (0.01617 : ℝ) := by
    nlinarith
  have hlog_mul :
      (n : ℝ) * Real.log n / 10650056950806 ≤
        (n : ℝ) * ((174 : ℝ) * (0.6931471808 : ℝ)) / 10650056950806 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog_le (Nat.cast_nonneg n))
      (by norm_num : (0 : ℝ) ≤ 10650056950806)
  have hlog_six :
      6 * Real.log n ≤ 6 * ((174 : ℝ) * (0.6931471808 : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hlog_le (by norm_num : (0 : ℝ) ≤ 6)
  have hgap_mul :
      (n : ℝ) * (0.01617 : ℝ) ≤
        (n : ℝ) *
          (Real.log 3 -
            ((1 / 2 : ℝ) * Real.log 2 +
              (1 / 3 : ℝ) * Real.log 3 +
              (1 / 7 : ℝ) * Real.log 7 +
              (1 / 43 : ℝ) * Real.log 43 +
              (1 / 1807 : ℝ) * Real.log 1807 +
              (1 / 3263443 : ℝ) * Real.log 3263443)) :=
    mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg n)
  calc
    (n : ℝ) * Real.log n / 10650056950806 + 6 * Real.log n + 6 -
        (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
          Real.log 1807 + Real.log 3263443)
        ≤ (n : ℝ) * ((174 : ℝ) * (0.6931471808 : ℝ)) / 10650056950806 +
            6 * ((174 : ℝ) * (0.6931471808 : ℝ)) + 6 := by
          nlinarith
    _ ≤ (n : ℝ) * (0.01617 : ℝ) := hband
    _ ≤ (n : ℝ) *
        (Real.log 3 -
          ((1 / 2 : ℝ) * Real.log 2 +
            (1 / 3 : ℝ) * Real.log 3 +
            (1 / 7 : ℝ) * Real.log 7 +
            (1 / 43 : ℝ) * Real.log 43 +
            (1 / 1807 : ℝ) * Real.log 1807 +
            (1 / 3263443 : ℝ) * Real.log 3263443)) := by
          exact hgap_mul

theorem shifted_log_sum_six_lower_ge_hansonA_seven_lt_hansonA_eight
    {n : ℕ} (hlo : hansonA 7 ≤ n) (hhi : n < hansonA 8) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ i ∈ Finset.range 6,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1) :=
  shifted_log_sum_six_lower_of_margin
    (by
      norm_num [hansonA] at hlo ⊢
      omega)
    (hanson_margin_six_ge_hansonA_seven_lt_hansonA_eight hlo hhi)

theorem two_mul_hansonA_le_6526886_of_lt_six {i : ℕ} (hi : i < 6) :
    2 * hansonA i ≤ 6526886 := by
  interval_cases i <;> norm_num [hansonA]

theorem floor_log_sum_six_lower_of_ge_6526886
    {n : ℕ} (hn : 6526886 ≤ n) :
    (∑ i ∈ Finset.range 6,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) ≤
      ∑ i ∈ Finset.range 6,
        ((n / hansonA i : ℕ) : ℝ) *
          Real.log ((n / hansonA i : ℕ) : ℝ) := by
  exact Finset.sum_le_sum fun i hi =>
    div_sub_one_mul_log_le_floor_mul_log_of_two_mul_le
      (hansonA_pos i)
      ((two_mul_hansonA_le_6526886_of_lt_six (Finset.mem_range.mp hi)).trans hn)

theorem floor_pow_log_lower_six_of_shifted_log_lower
    {n : ℕ} (hn : 6526886 ≤ n)
    (hlower :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ∑ i ∈ Finset.range 6,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ j ∈ Finset.range 6,
        ((n / hansonA j : ℕ) : ℝ) *
          Real.log ((n / hansonA j : ℕ) : ℝ) :=
  hlower.trans (floor_log_sum_six_lower_of_ge_6526886 hn)

theorem hansonC_six_le_three_pow_of_shifted_log_lower
    {n : ℕ} (hn : 6526886 ≤ n)
    (hlower :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ∑ i ∈ Finset.range 6,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) :
    hansonC n 6 ≤ 3 ^ n :=
  hansonC_le_three_pow_of_log_le n 6
    (log_hansonC_le_log_three_of_floor_pow_log_lower
      (n := n) (k := 6) (by omega)
      (floor_pow_log_lower_six_of_shifted_log_lower hn hlower))

theorem lcmUpto_le_three_pow_nat_of_hanson_tail_ge_hansonA_seven
    (htail : ∀ n : ℕ, hansonA 7 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (n + 1),
            (n / hansonA j) ^ (n / hansonA j)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
    2048 ?_
    (fun n =>
      if n < hansonA 5 then 4
      else if n < hansonA 6 then 5
      else if n < hansonA 7 then 6
      else n + 1)
    ?_
  · intro n hn
    by_cases h882 : n < 882
    · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
        (hansonC_succ_index_le_three_pow_of_lt_882 h882)).bound
    · by_cases h1807 : n < 1807
      · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
          (hansonC_succ_index_le_three_pow_of_ge_882_lt_1807
            (Nat.le_of_not_gt h882) h1807)).bound
      · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
          (hansonC_succ_index_le_three_pow_of_ge_1807_lt_2048
            (Nat.le_of_not_gt h1807) hn)).bound
  · intro n hn
    by_cases h5 : n < hansonA 5
    · simpa only [h5, ↓reduceIte] using
        hansonC_four_le_three_pow_of_shifted_log_lower
        (by omega : 86 ≤ n)
        (shifted_log_sum_four_lower_ge_2048_lt_hansonA_five hn h5)
    · by_cases h6 : n < hansonA 6
      · simpa only [h5, h6, ↓reduceIte] using
          hansonC_five_le_three_pow_of_shifted_log_lower
          (by
            have hn5 : hansonA 5 ≤ n := Nat.le_of_not_gt h5
            norm_num [hansonA] at hn5
            omega : 3614 ≤ n)
          (shifted_log_sum_five_lower_ge_hansonA_five_lt_hansonA_six
            (Nat.le_of_not_gt h5) h6)
      · by_cases h7 : n < hansonA 7
        · simpa only [h5, h6, h7, ↓reduceIte] using
            hansonC_six_le_three_pow_of_shifted_log_lower
            (by
              have hn6 : hansonA 6 ≤ n := Nat.le_of_not_gt h6
              norm_num [hansonA] at hn6
              omega : 6526886 ≤ n)
            (shifted_log_sum_six_lower_ge_hansonA_six_lt_hansonA_seven
              (Nat.le_of_not_gt h6) h7)
        · simpa only [h5, h6, h7, ↓reduceIte] using
            hansonC_le_three_pow_of_floor_pow_prod_lower
            n (n + 1) (htail n (Nat.le_of_not_gt h7))

theorem lcmUpto_le_three_pow_nat_of_hanson_tail_ge_hansonA_eight
    (htail : ∀ n : ℕ, hansonA 8 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (n + 1),
            (n / hansonA j) ^ (n / hansonA j)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
    2048 ?_
    (fun n =>
      if n < hansonA 5 then 4
      else if n < hansonA 6 then 5
      else if n < hansonA 8 then 6
      else n + 1)
    ?_
  · intro n hn
    by_cases h882 : n < 882
    · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
        (hansonC_succ_index_le_three_pow_of_lt_882 h882)).bound
    · by_cases h1807 : n < 1807
      · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
          (hansonC_succ_index_le_three_pow_of_ge_882_lt_1807
            (Nat.le_of_not_gt h882) h1807)).bound
      · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
          (hansonC_succ_index_le_three_pow_of_ge_1807_lt_2048
            (Nat.le_of_not_gt h1807) hn)).bound
  · intro n hn
    by_cases h5 : n < hansonA 5
    · simpa only [h5, ↓reduceIte] using
        hansonC_four_le_three_pow_of_shifted_log_lower
        (by omega : 86 ≤ n)
        (shifted_log_sum_four_lower_ge_2048_lt_hansonA_five hn h5)
    · by_cases h6 : n < hansonA 6
      · simpa only [h5, h6, ↓reduceIte] using
          hansonC_five_le_three_pow_of_shifted_log_lower
          (by
            have hn5 : hansonA 5 ≤ n := Nat.le_of_not_gt h5
            norm_num [hansonA] at hn5
            omega : 3614 ≤ n)
          (shifted_log_sum_five_lower_ge_hansonA_five_lt_hansonA_six
            (Nat.le_of_not_gt h5) h6)
      · by_cases h8 : n < hansonA 8
        · by_cases h7 : n < hansonA 7
          · simpa only [h5, h6, h8, ↓reduceIte] using
              hansonC_six_le_three_pow_of_shifted_log_lower
              (by
                have hn6 : hansonA 6 ≤ n := Nat.le_of_not_gt h6
                norm_num [hansonA] at hn6
                omega : 6526886 ≤ n)
              (shifted_log_sum_six_lower_ge_hansonA_six_lt_hansonA_seven
                (Nat.le_of_not_gt h6) h7)
          · simpa only [h5, h6, h8, ↓reduceIte] using
              hansonC_six_le_three_pow_of_shifted_log_lower
              (by
                have hn6 : hansonA 6 ≤ n := Nat.le_of_not_gt h6
                norm_num [hansonA] at hn6
                omega : 6526886 ≤ n)
              (shifted_log_sum_six_lower_ge_hansonA_seven_lt_hansonA_eight
                (Nat.le_of_not_gt h7) h8)
        · simpa only [h5, h6, h8, ↓reduceIte] using
            hansonC_le_three_pow_of_floor_pow_prod_lower
            n (n + 1) (htail n (Nat.le_of_not_gt h8))
