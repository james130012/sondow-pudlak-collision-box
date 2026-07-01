/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.ModelTheory.Syntax

/-!
# Analytic Sondow layer

This module contains the Euler-Mascheroni, Sondow integral, LCM, and explicit
Sondow criterion layer.
-/


open BigOperators
open Filter
open MeasureTheory
open Topology

-- ==========================================================================
-- 1. LIMIT DEFINITION OF EULER'S CONSTANT γ (EULER-MASCHERONI CONSTANT)
-- ==========================================================================

-- The nth harmonic sum: H_n = sum_{i=0}^{n-1} 1/(i+1)
noncomputable def harmonic_sum (n : ℕ) : ℝ :=
  (harmonic n : ℝ)

-- The Euler sequence: euler_seq(n) = H_n - log(n)
noncomputable def euler_seq (n : ℕ) : ℝ :=
  harmonic_sum n - Real.log (n : ℝ)

-- Declare the Euler-Mascheroni constant as a real number
noncomputable def euler_mascheroni : ℝ := Real.eulerMascheroniConstant

-- Theorem proving that the limit of the Euler sequence is the Euler-Mascheroni constant
theorem euler_mascheroni_limit :
  Tendsto (fun n : ℕ => euler_seq n) atTop (nhds euler_mascheroni) :=
  Real.tendsto_harmonic_sub_log


-- ==========================================================================
-- 2. DEFINITIONS OF SONDOW DOUBLE INTEGRAL I_n AND LCM SEQUENCE d(2n)
-- ==========================================================================

-- The integrand function for Sondow's double integral:
-- f_n(x, y) = (x(1-x)y(1-y))^n / (-(1 - xy) * log(xy))
noncomputable def sondow_integrand (n : ℕ) (x y : ℝ) : ℝ :=
  (x^n * (1 - x)^n * y^n * (1 - y)^n) / (-(1 - x * y) * Real.log (x * y))

noncomputable def inner_I (n : ℕ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, sondow_integrand n x y

-- The Sondow double integral I_n over [0,1]^2
noncomputable def I (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, inner_I n x

-- The LCM sequence d(k) = lcm(1, 2, ..., k)
def d : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (d n) (n + 1)

theorem d_pos : ∀ n : ℕ, 0 < d n := by
  intro n
  induction n with
  | zero =>
      simp [d]
  | succ n ih =>
      have hne : Nat.lcm (d n) (n + 1) ≠ 0 :=
        Nat.lcm_ne_zero (m := d n) (n := n + 1) (hm := Nat.ne_of_gt ih) (hn := Nat.succ_ne_zero _)
      simpa [d] using Nat.pos_of_ne_zero hne

theorem d_dvd_succ : ∀ n : ℕ, d n ∣ d (n + 1) := by
  intro n
  simpa [d] using (Nat.dvd_lcm_left (d n) (n + 1))

theorem d_le_succ : ∀ n : ℕ, d n ≤ d (n + 1) := by
  intro n
  exact Nat.le_of_dvd (d_pos (n + 1)) (d_dvd_succ n)

theorem d_mono : ∀ {m n : ℕ}, m ≤ n → d m ∣ d n := by
  intro m n hmn
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.le_zero.mp hmn
      simp [hm]
  | succ n ih =>
      cases Nat.lt_or_eq_of_le hmn with
      | inl hlt =>
          have hle : m ≤ n := Nat.le_of_lt_succ hlt
          exact dvd_trans (ih hle) (d_dvd_succ n)
      | inr heq =>
          subst heq
          simp

theorem d_dvd_of_le {m n : ℕ} (h : m ≤ n) : d m ∣ d n := by
  exact d_mono h

theorem d_self_dvd (n : ℕ) : d n ∣ d n := by
  exact d_mono (Nat.le_refl n)

theorem d_ne_zero (n : ℕ) : d n ≠ 0 := by
  exact Nat.ne_of_gt (d_pos n)

theorem d_eq_lcmUpto (n : ℕ) : d n = Nat.lcmUpto n := by
  induction n with
  | zero =>
      simp [d, Nat.lcmUpto]
  | succ n ih =>
      rw [d, ih]
      unfold Nat.lcmUpto
      have hIcc :
          insert (n + 1) (Finset.Icc 1 n) = Finset.Icc 1 (n + 1) := by
        simpa using
          (Finset.insert_Icc_right_eq_Icc_succ (a := 1) (b := n)
            (by simp : (1 : ℕ) ≤ Order.succ n))
      rw [← hIcc, Finset.lcm_insert]
      exact Nat.lcm_comm _ _

theorem d_double_eq_lcmUpto (n : ℕ) : d (2 * n) = Nat.lcmUpto (2 * n) := by
  exact d_eq_lcmUpto (2 * n)

theorem log_d_eq_chebyshev_psi (n : ℕ) :
    Real.log (d n : ℝ) = Chebyshev.psi n := by
  rw [d_eq_lcmUpto, Chebyshev.psi_eq_log_lcmUpto]

theorem log_d_double_eq_chebyshev_psi (n : ℕ) :
    Real.log (d (2 * n) : ℝ) = Chebyshev.psi (2 * n) := by
  simpa using log_d_eq_chebyshev_psi (2 * n)

theorem dvd_d_nonzero {n : ℕ} (hn : n ≠ 0) : n ∣ d n := by
  cases n with
  | zero =>
      cases hn rfl
  | succ n =>
      simpa [d] using (Nat.dvd_lcm_right (d n) (n + 1))

theorem dvd_d_of_le {m n : ℕ} (hm : 0 < m) (h : m ≤ n) : m ∣ d n := by
  exact Nat.dvd_trans (dvd_d_nonzero (Nat.ne_of_gt hm)) (d_dvd_of_le h)

theorem d_dvd_factorial : ∀ n : ℕ, d n ∣ n.factorial := by
  intro n
  induction n with
  | zero =>
      simp [d]
  | succ n ih =>
      have h1 : d n ∣ (n + 1).factorial := by
        exact Nat.dvd_trans ih (Nat.factorial_dvd_factorial (Nat.le_succ n))
      have h2 : n + 1 ∣ (n + 1).factorial := by
        exact Nat.dvd_factorial (Nat.succ_pos n) le_rfl
      simpa [d] using Nat.lcm_dvd h1 h2

theorem d_le_factorial (n : ℕ) : d n ≤ n.factorial := by
  exact Nat.le_of_dvd (Nat.factorial_pos n) (d_dvd_factorial n)

theorem d_dvd_double (n : ℕ) : d n ∣ d (2 * n) := by
  have hle : n ≤ 2 * n := by
    simp [two_mul]
  exact d_dvd_of_le hle

theorem n_dvd_d_double {n : ℕ} (hn : 0 < n) : n ∣ d (2 * n) := by
  have hle : n ≤ 2 * n := by
    simp [two_mul]
  exact dvd_d_of_le hn hle

-- The rational harmonic sum used in Sondow's rational term A_n.
noncomputable def harmonic_rat (m : ℕ) : ℚ :=
  harmonic m

-- Sondow's rational term A_n = sum_j binom(n,j)^2 H_{n+j}.
noncomputable def A_rat (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1), ((Nat.choose n j : ℕ) : ℚ)^2 * harmonic_rat (n + j)

-- Sondow's logarithmic term:
-- L_n = 2 * sum_{0 ≤ i < j ≤ n} sum_{k=1}^{j-i}
--   (-1)^(i+j-1)/(j-i) * binom(n,i) * binom(n,j) * log(n+i+k).
noncomputable def sondow_L (n : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range (n + 1),
    ∑ j ∈ (Finset.range (n + 1)).filter (fun j => i < j),
      ∑ k ∈ Finset.Icc 1 (j - i),
        (((-1 : ℝ) ^ (i + j - 1)) / (j - i : ℝ)) *
          (Nat.choose n i : ℝ) * (Nat.choose n j : ℝ) *
            Real.log (n + i + k : ℝ)

-- Sondow's explicit positive-integer product. This is the product form used to
-- turn the logarithmic linear form into the logarithm of an integer.
def sondow_S_explicit (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 1 n,
    ∏ i ∈ Finset.range (Nat.min (k - 1) (n - k) + 1),
      ∏ j ∈ Finset.Icc (i + 1) (n - i),
        (n + k) ^ (((2 * d (2 * n)) / j) * (Nat.choose n i)^2)

theorem sondow_S_explicit_pos (n : ℕ) : 0 < sondow_S_explicit n := by
  unfold sondow_S_explicit
  refine Finset.prod_pos ?_
  intro k hk
  refine Finset.prod_pos ?_
  intro i _hi
  refine Finset.prod_pos ?_
  intro j _hj
  exact pow_pos (Nat.add_pos_right n (Finset.mem_Icc.mp hk).1) _

theorem sondow_S_explicit_exponent_denominator_dvd {n i j : ℕ}
    (hj : j ∈ Finset.Icc (i + 1) (n - i)) :
    j ∣ 2 * d (2 * n) := by
  have hj_bounds := Finset.mem_Icc.mp hj
  have hj_pos : 0 < j := by omega
  have hj_le_n : j ≤ n := by omega
  have hj_le_2n : j ≤ 2 * n := by omega
  exact dvd_mul_of_dvd_right (dvd_d_of_le hj_pos hj_le_2n) 2

theorem sondow_S_explicit_exponent_denominator_cancel {n i j : ℕ}
    (hj : j ∈ Finset.Icc (i + 1) (n - i)) :
    j * ((2 * d (2 * n)) / j) = 2 * d (2 * n) := by
  exact Nat.mul_div_cancel' (sondow_S_explicit_exponent_denominator_dvd hj)

def Rat.is_integer (x : ℚ) : Prop :=
  ∃ z : ℤ, (z : ℚ) = x

theorem Rat.is_integer_of_den_eq_one {x : ℚ} (h : x.den = 1) : Rat.is_integer x := by
  exact ⟨x.num, Rat.coe_int_num_of_den_eq_one h⟩

theorem Rat.is_integer_add {x y : ℚ}
    (hx : Rat.is_integer x) (hy : Rat.is_integer y) : Rat.is_integer (x + y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a + b, by norm_num⟩

theorem Rat.is_integer_mul {x y : ℚ}
    (hx : Rat.is_integer x) (hy : Rat.is_integer y) : Rat.is_integer (x * y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a * b, by norm_num⟩

theorem Rat.is_integer_natCast (a : ℕ) : Rat.is_integer (a : ℚ) := by
  exact ⟨a, by norm_num⟩

theorem Rat.is_integer_sum {ι : Type} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, Rat.is_integer (f i)) : Rat.is_integer (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f Rat.is_integer
    (fun _ _ => Rat.is_integer_add) (by exact ⟨0, by norm_num⟩) h

theorem rat_nat_div_is_integer {a m : ℕ} (hm : m ≠ 0) (hdvd : m ∣ a) :
    Rat.is_integer ((a : ℚ) / (m : ℕ)) := by
  exact Rat.is_integer_of_den_eq_one ((Rat.den_div_natCast_eq_one_iff a m hm).2 hdvd)

theorem rat_nat_mul_is_integer_of_den_dvd (a : ℕ) (q : ℚ) (hden : q.den ∣ a) :
    Rat.is_integer ((a : ℚ) * q) := by
  rcases hden with ⟨k, hk⟩
  rw [hk]
  refine ⟨(k : ℤ) * q.num, ?_⟩
  rw [Nat.cast_mul]
  calc
    (((k : ℤ) * q.num : ℤ) : ℚ) = (k : ℚ) * q.num := by simp
    _ = (k : ℚ) * ((q.den : ℚ) * q) := by rw [Rat.den_mul_eq_num]
    _ = ((q.den : ℚ) * (k : ℚ)) * q := by ring

theorem d_mul_harmonic_rat_is_integer {n m : ℕ} (hmn : m ≤ 2 * n) :
    Rat.is_integer ((d (2 * n) : ℚ) * harmonic_rat m) := by
  unfold harmonic_rat
  rw [harmonic]
  rw [Finset.mul_sum]
  apply Rat.is_integer_sum
  intro i hi
  rw [Finset.mem_range] at hi
  have hi_pos : 0 < i + 1 := Nat.succ_pos i
  have hi_le : i + 1 ≤ 2 * n := by omega
  have hdvd : i + 1 ∣ d (2 * n) := dvd_d_of_le hi_pos hi_le
  convert rat_nat_div_is_integer (Nat.ne_of_gt hi_pos) hdvd using 1
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hi_pos)]

theorem d_mul_A_rat_is_integer (n : ℕ) :
    Rat.is_integer ((d (2 * n) : ℚ) * A_rat n) := by
  unfold A_rat
  rw [Finset.mul_sum]
  apply Rat.is_integer_sum
  intro j hj
  rw [Finset.mem_range] at hj
  have hnj : n + j ≤ 2 * n := by omega
  have hH : Rat.is_integer ((d (2 * n) : ℚ) * harmonic_rat (n + j)) :=
    d_mul_harmonic_rat_is_integer hnj
  have hchoose : Rat.is_integer (((Nat.choose n j : ℕ) : ℚ)^2) := by
    simpa [pow_two] using Rat.is_integer_mul
      (Rat.is_integer_natCast (Nat.choose n j)) (Rat.is_integer_natCast (Nat.choose n j))
  convert Rat.is_integer_mul hchoose hH using 1
  ring

theorem d_mul_choose_mul_rat_is_integer_of_den_le (n : ℕ) (q : ℚ)
    (hden : q.den ≤ 2 * n) :
    Rat.is_integer (((d (2 * n) * Nat.choose (2 * n) n : ℕ) : ℚ) * q) := by
  have hpos : 0 < q.den := Rat.den_pos q
  have hdvd_d : q.den ∣ d (2 * n) := dvd_d_of_le hpos hden
  have hdvd : q.den ∣ d (2 * n) * Nat.choose (2 * n) n := dvd_mul_of_dvd_left hdvd_d _
  exact rat_nat_mul_is_integer_of_den_dvd _ q hdvd

theorem real_int_of_rat_is_integer {x : ℚ} (hx : Rat.is_integer x) :
    ∃ z : ℤ, (x : ℝ) = (z : ℝ) := by
  rcases hx with ⟨z, hz⟩
  exact ⟨z, by rw [← hz]; norm_num⟩

theorem real_int_sub {x y : ℝ}
    (hx : ∃ z : ℤ, x = (z : ℝ)) (hy : ∃ z : ℤ, y = (z : ℝ)) :
    ∃ z : ℤ, x - y = (z : ℝ) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  exact ⟨a - b, by norm_num⟩


-- ==========================================================================
-- 3. AXIOMATIC SETUP FOR SEQUENCE S(n) AND ITS LOG RELATION
-- ==========================================================================

-- L_n is Sondow's explicit finite logarithmic sum.
noncomputable def L : ℕ → ℝ := sondow_L

-- S(n) is Sondow's explicit positive-integer product.
def S : ℕ → ℕ := sondow_S_explicit

def S_matches_sondow_explicit : Prop :=
  ∀ n : ℕ, S n = sondow_S_explicit n

theorem S_matches_sondow_explicit_true : S_matches_sondow_explicit := by
  intro n
  rfl

theorem S_pos (n : ℕ) : 0 < S n := by
  exact sondow_S_explicit_pos n

theorem S_pos_of_matches_sondow_explicit
    (hS : S_matches_sondow_explicit) (n : ℕ) : 0 < S n := by
  rw [hS n]
  exact sondow_S_explicit_pos n

theorem S_pos_real (n : ℕ) : 0 < (S n : ℝ) := by
  exact_mod_cast S_pos n

theorem S_ge_one (n : ℕ) : 1 ≤ S n := by
  exact Nat.succ_le_of_lt (S_pos n)

theorem S_ge_one_real (n : ℕ) : (1 : ℝ) ≤ S n := by
  exact_mod_cast S_ge_one n

theorem log_S_nonneg (n : ℕ) : 0 ≤ Real.log (S n : ℝ) := by
  apply Real.log_nonneg
  exact S_ge_one_real n

-- The exact Sondow decomposition, isolated as the remaining analytic expansion target.
def sondow_decomposition_prop (n : ℕ) : Prop :=
  I n = (Nat.choose (2 * n) n : ℝ) * euler_mascheroni + L n - (A_rat n : ℝ)

-- The same decomposition with Sondow's explicit logarithmic finite sum.
def sondow_explicit_decomposition_prop (n : ℕ) : Prop :=
  I n = (Nat.choose (2 * n) n : ℝ) * euler_mascheroni + sondow_L n - (A_rat n : ℝ)

-- The log relation stated directly with Sondow's explicit logarithmic finite sum.
def sondow_explicit_log_relation_prop (n : ℕ) : Prop :=
  Real.log (S n : ℝ) = (d (2 * n) : ℝ) * sondow_L n

-- The log relation with both `S` and `L` expanded to the explicit Sondow forms.
def sondow_explicit_product_log_relation_prop (n : ℕ) : Prop :=
  Real.log (sondow_S_explicit n : ℝ) = (d (2 * n) : ℝ) * sondow_L n

-- Log relation: log S(n) = d(2n) * L_n.
-- The standard product-log identity is required explicitly as a hypothesis.
theorem log_S_relation_of_product_log
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (n : ℕ) : Real.log (S n : ℝ) = (d (2 * n) : ℝ) * L n := by
  simpa [S, L, sondow_explicit_product_log_relation_prop] using h_product_log n

theorem L_eq_sondow_L (n : ℕ) : L n = sondow_L n := by
  rfl

theorem sondow_explicit_log_relation_prop_iff_product {n : ℕ}
    (hS : S n = sondow_S_explicit n) :
    sondow_explicit_log_relation_prop n ↔ sondow_explicit_product_log_relation_prop n := by
  unfold sondow_explicit_log_relation_prop sondow_explicit_product_log_relation_prop
  rw [hS]

theorem sondow_explicit_log_relation_prop_iff_product_true {n : ℕ} :
    sondow_explicit_log_relation_prop n ↔ sondow_explicit_product_log_relation_prop n := by
  exact sondow_explicit_log_relation_prop_iff_product (S_matches_sondow_explicit_true n)

theorem sondow_explicit_log_relation_prop_of_product_log_and_L_alignment
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n) {n : ℕ}
    (hL : L n = sondow_L n) :
    sondow_explicit_log_relation_prop n := by
  unfold sondow_explicit_log_relation_prop
  rw [log_S_relation_of_product_log h_product_log n, hL]

theorem sondow_explicit_log_relation_of_product_log
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (n : ℕ) :
    sondow_explicit_log_relation_prop n := by
  exact sondow_explicit_log_relation_prop_of_product_log_and_L_alignment
    h_product_log (L_eq_sondow_L n)

theorem sondow_explicit_log_relation_all_of_L_alignment
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (hL : ∀ n : ℕ, L n = sondow_L n) :
    ∀ n : ℕ, sondow_explicit_log_relation_prop n := by
  intro n
  exact sondow_explicit_log_relation_prop_of_product_log_and_L_alignment h_product_log (hL n)

theorem sondow_explicit_log_relation_all_of_product_log
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n) :
    ∀ n : ℕ, sondow_explicit_log_relation_prop n := by
  intro n
  exact sondow_explicit_log_relation_of_product_log h_product_log n

theorem sondow_decomposition_prop_of_explicit {n : ℕ}
    (hL : L n = sondow_L n)
    (h : sondow_explicit_decomposition_prop n) :
    sondow_decomposition_prop n := by
  unfold sondow_decomposition_prop sondow_explicit_decomposition_prop at *
  rwa [hL]

theorem sondow_decomposition_prop_of_explicit_true {n : ℕ}
    (h : sondow_explicit_decomposition_prop n) :
    sondow_decomposition_prop n := by
  exact sondow_decomposition_prop_of_explicit (L_eq_sondow_L n) h

theorem sondow_decomposition_all_of_explicit
    (hL : ∀ n : ℕ, L n = sondow_L n)
    (h : ∀ n : ℕ, sondow_explicit_decomposition_prop n) :
    ∀ n : ℕ, sondow_decomposition_prop n := by
  intro n
  exact sondow_decomposition_prop_of_explicit (hL n) (h n)

theorem sondow_decomposition_all_of_explicit_true
    (h : ∀ n : ℕ, sondow_explicit_decomposition_prop n) :
    ∀ n : ℕ, sondow_decomposition_prop n := by
  intro n
  exact sondow_decomposition_prop_of_explicit_true (h n)



-- ==========================================================================
-- 4. SONDOW'S RATIONAL EQUIVALENCE THEOREM STATEMENT
-- ==========================================================================

-- Definition of rational numbers in the real field
def is_rational (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

theorem is_rational_of_rat (q : ℚ) : is_rational (q : ℝ) := by
  exact ⟨q, rfl⟩

theorem is_rational_of_int (z : ℤ) : is_rational (z : ℝ) := by
  refine ⟨(z : ℚ), ?_⟩
  simp

theorem is_rational_of_nat (n : ℕ) : is_rational (n : ℝ) := by
  exact is_rational_of_rat n

theorem is_rational_iff_exists_rat (x : ℝ) : is_rational x ↔ ∃ q : ℚ, (q : ℝ) = x := by
  rfl

-- Definition of the fractional part of a real number: {x} = x - floor(x)
noncomputable def fractional_part (x : ℝ) : ℝ := x - (Int.floor x : ℝ)

theorem fractional_part_eq_fract (x : ℝ) : fractional_part x = Int.fract x := by
  simp [fractional_part]

theorem fractional_part_nonneg (x : ℝ) : 0 ≤ fractional_part x := by
  rw [fractional_part_eq_fract]
  exact Int.fract_nonneg x

theorem fractional_part_lt_one (x : ℝ) : fractional_part x < 1 := by
  rw [fractional_part_eq_fract]
  exact Int.fract_lt_one x

theorem fractional_part_range (x : ℝ) : 0 ≤ fractional_part x ∧ fractional_part x < 1 := by
  exact ⟨fractional_part_nonneg x, fractional_part_lt_one x⟩

theorem fractional_part_eq_of_sub_int {x y : ℝ}
    (h_range : 0 ≤ y ∧ y < 1) (h_int : ∃ z : ℤ, x - y = (z : ℝ)) :
    fractional_part x = y := by
  rw [fractional_part_eq_fract]
  exact Int.fract_eq_iff.2 ⟨h_range.1, h_range.2, h_int⟩

theorem fractional_part_int_cast (z : ℤ) : fractional_part (z : ℝ) = 0 := by
  rw [fractional_part_eq_fract]
  simp

theorem fractional_part_nat_cast (n : ℕ) : fractional_part (n : ℝ) = 0 := by
  rw [fractional_part_eq_fract]
  simp

-- Sondow-style identity at an index n.
def sondow_identity_prop (n : ℕ) : Prop :=
  fractional_part (Real.log (S n : ℝ)) = (d (2 * n) : ℝ) * I n

-- The same identity using the explicit Sondow product instead of the abstract `S`.
def sondow_identity_explicit_prop (n : ℕ) : Prop :=
  fractional_part (Real.log (sondow_S_explicit n : ℝ)) = (d (2 * n) : ℝ) * I n

theorem sondow_identity_prop_iff_explicit {n : ℕ}
    (hS : S n = sondow_S_explicit n) :
    sondow_identity_prop n ↔ sondow_identity_explicit_prop n := by
  unfold sondow_identity_prop sondow_identity_explicit_prop
  rw [hS]

-- The integer-gap condition used to turn the Sondow decomposition into a fractional-part identity.
def sondow_integer_gap_prop (n : ℕ) : Prop :=
  ∃ z : ℤ, Real.log (S n : ℝ) - (d (2 * n) : ℝ) * I n = (z : ℝ)

def sondow_integer_gap_explicit_prop (n : ℕ) : Prop :=
  ∃ z : ℤ, Real.log (sondow_S_explicit n : ℝ) - (d (2 * n) : ℝ) * I n = (z : ℝ)

theorem sondow_integer_gap_prop_iff_explicit {n : ℕ}
    (hS : S n = sondow_S_explicit n) :
    sondow_integer_gap_prop n ↔ sondow_integer_gap_explicit_prop n := by
  unfold sondow_integer_gap_prop sondow_integer_gap_explicit_prop
  rw [hS]

-- The range condition needed for the right side to be the fractional part.
def sondow_term_range_prop (n : ℕ) : Prop :=
  0 ≤ (d (2 * n) : ℝ) * I n ∧ (d (2 * n) : ℝ) * I n < 1

def sondow_term_nonneg_prop (n : ℕ) : Prop :=
  0 ≤ (d (2 * n) : ℝ) * I n

def sondow_term_lt_one_prop (n : ℕ) : Prop :=
  (d (2 * n) : ℝ) * I n < 1

def I_nonneg_prop (n : ℕ) : Prop :=
  0 ≤ I n

def sondow_integrand_nonneg_on_unit_square_prop (n : ℕ) : Prop :=
  ∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
    0 ≤ sondow_integrand n x y

def inner_I_nonneg_on_unit_interval_prop (n : ℕ) : Prop :=
  ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ inner_I n x

-- Eventual form of the Sondow identity: the equality holds beyond some cutoff.
def sondow_identity_eventual : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → sondow_identity_prop n

def sondow_identity_explicit_eventual : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → sondow_identity_explicit_prop n

def sondow_integer_gap_eventual : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → sondow_integer_gap_prop n

def sondow_integer_gap_explicit_eventual : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → sondow_integer_gap_explicit_prop n

def sondow_term_range_eventual : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → sondow_term_range_prop n

def sondow_term_nonneg_eventual : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → sondow_term_nonneg_prop n

def sondow_term_lt_one_eventual : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → sondow_term_lt_one_prop n

def I_nonneg_eventual : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → I_nonneg_prop n

def sondow_integrand_nonneg_eventual_on_unit_square : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → sondow_integrand_nonneg_on_unit_square_prop n

-- Pointwise form used in the original Sondow criterion.
def sondow_identity_some : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ sondow_identity_prop n

theorem sondow_integer_gap_eventual_of_rational_and_decomposition
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_rat : is_rational euler_mascheroni)
    (h_decomp : ∀ n : ℕ, sondow_decomposition_prop n) :
    sondow_integer_gap_eventual := by
  rcases h_rat with ⟨q, hq⟩
  refine ⟨q.den, ?_⟩
  intro n hn
  let c : ℕ := d (2 * n) * Nat.choose (2 * n) n
  have hden_le : q.den ≤ 2 * n := by omega
  have hAq : Rat.is_integer ((d (2 * n) : ℚ) * A_rat n) := d_mul_A_rat_is_integer n
  have hA : ∃ z : ℤ, (((d (2 * n) : ℚ) * A_rat n : ℚ) : ℝ) = (z : ℝ) :=
    real_int_of_rat_is_integer hAq
  have hGq : Rat.is_integer ((c : ℚ) * q) := by
    dsimp [c]
    exact d_mul_choose_mul_rat_is_integer_of_den_le n q hden_le
  have hG : ∃ z : ℤ, (((c : ℚ) * q : ℚ) : ℝ) = (z : ℝ) :=
    real_int_of_rat_is_integer hGq
  rcases real_int_sub hA hG with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hdec := h_decomp n
  unfold sondow_decomposition_prop at hdec
  have hlog := log_S_relation_of_product_log h_product_log n
  calc
    Real.log (S n : ℝ) - (d (2 * n) : ℝ) * I n
        = (d (2 * n) : ℝ) * (A_rat n : ℝ) -
            (d (2 * n) : ℝ) * (Nat.choose (2 * n) n : ℝ) * euler_mascheroni := by
          rw [hlog, hdec]
          ring
    _ = (d (2 * n) : ℝ) * (A_rat n : ℝ) -
          (d (2 * n) : ℝ) * (Nat.choose (2 * n) n : ℝ) * (q : ℝ) := by
          rw [hq]
    _ = (((d (2 * n) : ℚ) * A_rat n : ℚ) : ℝ) - (((c : ℚ) * q : ℚ) : ℝ) := by
          dsimp [c]
          norm_num
    _ = (z : ℝ) := hz

theorem sondow_integer_gap_eventual_of_rational_explicit_log_and_decomposition
    (h_rat : is_rational euler_mascheroni)
    (h_log : ∀ n : ℕ, sondow_explicit_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n) :
    sondow_integer_gap_eventual := by
  rcases h_rat with ⟨q, hq⟩
  refine ⟨q.den, ?_⟩
  intro n hn
  let c : ℕ := d (2 * n) * Nat.choose (2 * n) n
  have hden_le : q.den ≤ 2 * n := by omega
  have hAq : Rat.is_integer ((d (2 * n) : ℚ) * A_rat n) := d_mul_A_rat_is_integer n
  have hA : ∃ z : ℤ, (((d (2 * n) : ℚ) * A_rat n : ℚ) : ℝ) = (z : ℝ) :=
    real_int_of_rat_is_integer hAq
  have hGq : Rat.is_integer ((c : ℚ) * q) := by
    dsimp [c]
    exact d_mul_choose_mul_rat_is_integer_of_den_le n q hden_le
  have hG : ∃ z : ℤ, (((c : ℚ) * q : ℚ) : ℝ) = (z : ℝ) :=
    real_int_of_rat_is_integer hGq
  rcases real_int_sub hA hG with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hdec := h_decomp n
  unfold sondow_explicit_decomposition_prop at hdec
  have hlog := h_log n
  unfold sondow_explicit_log_relation_prop at hlog
  calc
    Real.log (S n : ℝ) - (d (2 * n) : ℝ) * I n
        = (d (2 * n) : ℝ) * (A_rat n : ℝ) -
            (d (2 * n) : ℝ) * (Nat.choose (2 * n) n : ℝ) * euler_mascheroni := by
          rw [hlog, hdec]
          ring
    _ = (d (2 * n) : ℝ) * (A_rat n : ℝ) -
          (d (2 * n) : ℝ) * (Nat.choose (2 * n) n : ℝ) * (q : ℝ) := by
          rw [hq]
    _ = (((d (2 * n) : ℚ) * A_rat n : ℚ) : ℝ) - (((c : ℚ) * q : ℚ) : ℝ) := by
          dsimp [c]
          norm_num
    _ = (z : ℝ) := hz

theorem sondow_integer_gap_explicit_eventual_of_rational_product_log_and_decomposition
    (h_rat : is_rational euler_mascheroni)
    (h_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n) :
    sondow_integer_gap_explicit_eventual := by
  rcases h_rat with ⟨q, hq⟩
  refine ⟨q.den, ?_⟩
  intro n hn
  let c : ℕ := d (2 * n) * Nat.choose (2 * n) n
  have hden_le : q.den ≤ 2 * n := by omega
  have hAq : Rat.is_integer ((d (2 * n) : ℚ) * A_rat n) := d_mul_A_rat_is_integer n
  have hA : ∃ z : ℤ, (((d (2 * n) : ℚ) * A_rat n : ℚ) : ℝ) = (z : ℝ) :=
    real_int_of_rat_is_integer hAq
  have hGq : Rat.is_integer ((c : ℚ) * q) := by
    dsimp [c]
    exact d_mul_choose_mul_rat_is_integer_of_den_le n q hden_le
  have hG : ∃ z : ℤ, (((c : ℚ) * q : ℚ) : ℝ) = (z : ℝ) :=
    real_int_of_rat_is_integer hGq
  rcases real_int_sub hA hG with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hdec := h_decomp n
  unfold sondow_explicit_decomposition_prop at hdec
  have hlog := h_log n
  unfold sondow_explicit_product_log_relation_prop at hlog
  calc
    Real.log (sondow_S_explicit n : ℝ) - (d (2 * n) : ℝ) * I n
        = (d (2 * n) : ℝ) * (A_rat n : ℝ) -
            (d (2 * n) : ℝ) * (Nat.choose (2 * n) n : ℝ) * euler_mascheroni := by
          rw [hlog, hdec]
          ring
    _ = (d (2 * n) : ℝ) * (A_rat n : ℝ) -
          (d (2 * n) : ℝ) * (Nat.choose (2 * n) n : ℝ) * (q : ℝ) := by
          rw [hq]
    _ = (((d (2 * n) : ℚ) * A_rat n : ℚ) : ℝ) - (((c : ℚ) * q : ℚ) : ℝ) := by
          dsimp [c]
          norm_num
    _ = (z : ℝ) := hz

theorem sondow_integer_gap_explicit_eventual_of_rational_product_log_and_decomposition_pos
    (h_rat : is_rational euler_mascheroni)
    (h_log : ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    sondow_integer_gap_explicit_eventual := by
  rcases h_rat with ⟨q, hq⟩
  refine ⟨q.den, ?_⟩
  intro n hn
  have hn_pos : 1 ≤ n := by
    exact le_trans (Nat.succ_le_of_lt (Rat.den_pos q)) hn
  let c : ℕ := d (2 * n) * Nat.choose (2 * n) n
  have hden_le : q.den ≤ 2 * n := by omega
  have hAq : Rat.is_integer ((d (2 * n) : ℚ) * A_rat n) := d_mul_A_rat_is_integer n
  have hA : ∃ z : ℤ, (((d (2 * n) : ℚ) * A_rat n : ℚ) : ℝ) = (z : ℝ) :=
    real_int_of_rat_is_integer hAq
  have hGq : Rat.is_integer ((c : ℚ) * q) := by
    dsimp [c]
    exact d_mul_choose_mul_rat_is_integer_of_den_le n q hden_le
  have hG : ∃ z : ℤ, (((c : ℚ) * q : ℚ) : ℝ) = (z : ℝ) :=
    real_int_of_rat_is_integer hGq
  rcases real_int_sub hA hG with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hdec := h_decomp n hn_pos
  unfold sondow_explicit_decomposition_prop at hdec
  have hlog := h_log n hn_pos
  unfold sondow_explicit_product_log_relation_prop at hlog
  calc
    Real.log (sondow_S_explicit n : ℝ) - (d (2 * n) : ℝ) * I n
        = (d (2 * n) : ℝ) * (A_rat n : ℝ) -
            (d (2 * n) : ℝ) * (Nat.choose (2 * n) n : ℝ) * euler_mascheroni := by
          rw [hlog, hdec]
          ring
    _ = (d (2 * n) : ℝ) * (A_rat n : ℝ) -
          (d (2 * n) : ℝ) * (Nat.choose (2 * n) n : ℝ) * (q : ℝ) := by
          rw [hq]
    _ = (((d (2 * n) : ℚ) * A_rat n : ℚ) : ℝ) - (((c : ℚ) * q : ℚ) : ℝ) := by
          dsimp [c]
          norm_num
    _ = (z : ℝ) := hz

theorem sondow_identity_prop_of_integer_gap_and_range {n : ℕ}
    (h_gap : sondow_integer_gap_prop n) (h_range : sondow_term_range_prop n) :
    sondow_identity_prop n := by
  exact fractional_part_eq_of_sub_int h_range h_gap

theorem sondow_identity_explicit_prop_of_integer_gap_and_range {n : ℕ}
    (h_gap : sondow_integer_gap_explicit_prop n) (h_range : sondow_term_range_prop n) :
    sondow_identity_explicit_prop n := by
  exact fractional_part_eq_of_sub_int h_range h_gap

theorem sondow_identity_prop_nonneg {n : ℕ} (h : sondow_identity_prop n) :
    0 ≤ (d (2 * n) : ℝ) * I n := by
  rw [sondow_identity_prop] at h
  rw [← h]
  exact fractional_part_nonneg _

theorem sondow_identity_prop_lt_one {n : ℕ} (h : sondow_identity_prop n) :
    (d (2 * n) : ℝ) * I n < 1 := by
  rw [sondow_identity_prop] at h
  rw [← h]
  exact fractional_part_lt_one _

theorem sondow_identity_prop_range {n : ℕ} (h : sondow_identity_prop n) :
    0 ≤ (d (2 * n) : ℝ) * I n ∧ (d (2 * n) : ℝ) * I n < 1 := by
  exact ⟨sondow_identity_prop_nonneg h, sondow_identity_prop_lt_one h⟩

theorem sondow_term_range_prop_of_identity {n : ℕ} (h : sondow_identity_prop n) :
    sondow_term_range_prop n := by
  exact sondow_identity_prop_range h

theorem sondow_term_nonneg_prop_of_I_nonneg {n : ℕ} (hI : I_nonneg_prop n) :
    sondow_term_nonneg_prop n := by
  exact mul_nonneg (Nat.cast_nonneg _) hI

theorem sondow_term_nonneg_eventual_of_I_nonneg_eventual
    (hI : I_nonneg_eventual) : sondow_term_nonneg_eventual := by
  rcases hI with ⟨N, hN⟩
  exact ⟨N, fun n hn => sondow_term_nonneg_prop_of_I_nonneg (hN n hn)⟩

theorem inner_I_nonneg_on_unit_interval_of_integrand_nonneg_on_unit_square {n : ℕ}
    (h : sondow_integrand_nonneg_on_unit_square_prop n) :
    inner_I_nonneg_on_unit_interval_prop n := by
  intro x hx
  exact intervalIntegral.integral_nonneg zero_le_one (fun y hy => h x y hx hy)

theorem I_nonneg_prop_of_inner_I_nonneg_on_unit_interval {n : ℕ}
    (h : inner_I_nonneg_on_unit_interval_prop n) : I_nonneg_prop n := by
  exact intervalIntegral.integral_nonneg zero_le_one (fun x hx => h x hx)

theorem I_nonneg_prop_of_integrand_nonneg_on_unit_square {n : ℕ}
    (h : sondow_integrand_nonneg_on_unit_square_prop n) : I_nonneg_prop n := by
  exact I_nonneg_prop_of_inner_I_nonneg_on_unit_interval
    (inner_I_nonneg_on_unit_interval_of_integrand_nonneg_on_unit_square h)

theorem I_nonneg_eventual_of_integrand_nonneg_eventual_on_unit_square
    (h : sondow_integrand_nonneg_eventual_on_unit_square) : I_nonneg_eventual := by
  rcases h with ⟨N, hN⟩
  exact ⟨N, fun n hn => I_nonneg_prop_of_integrand_nonneg_on_unit_square (hN n hn)⟩

theorem sondow_integrand_nonneg_on_unit_square (n : ℕ) :
    sondow_integrand_nonneg_on_unit_square_prop n := by
  intro x y hx hy
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hy0 : 0 ≤ y := hy.1
  have hy1 : y ≤ 1 := hy.2
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hxy1 : x * y ≤ 1 := by
    have hxy_le_x : x * y ≤ x * 1 := mul_le_mul_of_nonneg_left hy1 hx0
    exact hxy_le_x.trans (by simpa using hx1)
  have hxsub : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hysub : 0 ≤ 1 - y := sub_nonneg.mpr hy1
  have hnum : 0 ≤ x^n * (1 - x)^n * y^n * (1 - y)^n := by
    positivity
  have hden_left : -(1 - x * y) ≤ 0 := by
    exact neg_nonpos.mpr (sub_nonneg.mpr hxy1)
  have hden_right : Real.log (x * y) ≤ 0 := Real.log_nonpos hxy0 hxy1
  have hden : 0 ≤ -(1 - x * y) * Real.log (x * y) :=
    mul_nonneg_of_nonpos_of_nonpos hden_left hden_right
  exact div_nonneg hnum hden

theorem mul_mem_Ioo_unit {x y : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) : x * y ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · exact mul_pos hx.1 hy.1
  · have hxy_le_x : x * y < x * 1 := mul_lt_mul_of_pos_left hy.2 hx.1
    have hxy_lt_x : x * y < x := by simpa using hxy_le_x
    exact hxy_lt_x.trans hx.2

theorem sondow_denominator_pos_on_open_unit_square {x y : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    0 < -(1 - x * y) * Real.log (x * y) := by
  have hxy : x * y ∈ Set.Ioo (0 : ℝ) 1 := mul_mem_Ioo_unit hx hy
  have hleft : -(1 - x * y) < 0 := by
    exact neg_lt_zero.mpr (sub_pos.mpr hxy.2)
  have hright : Real.log (x * y) < 0 := Real.log_neg hxy.1 hxy.2
  exact mul_pos_of_neg_of_neg hleft hright

theorem one_sub_mul_sq_le_sondow_denominator {x y : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    (1 - x * y)^2 ≤ -(1 - x * y) * Real.log (x * y) := by
  have hxy : x * y ∈ Set.Ioo (0 : ℝ) 1 := mul_mem_Ioo_unit hx hy
  have hone_sub_nonneg : 0 ≤ 1 - x * y := sub_nonneg.mpr hxy.2.le
  have hlog : 1 - x * y ≤ -Real.log (x * y) := by
    have h := Real.log_le_sub_one_of_pos hxy.1
    linarith
  calc
    (1 - x * y)^2 = (1 - x * y) * (1 - x * y) := by ring
    _ ≤ (1 - x * y) * (-Real.log (x * y)) :=
        mul_le_mul_of_nonneg_left hlog hone_sub_nonneg
    _ = -(1 - x * y) * Real.log (x * y) := by ring

theorem corner_product_le_one_sub_mul_sq {x y : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    (1 - x) * (1 - y) ≤ (1 - x * y)^2 := by
  have hxsub_nonneg : 0 ≤ 1 - x := sub_nonneg.mpr hx.2.le
  have hysub_nonneg : 0 ≤ 1 - y := sub_nonneg.mpr hy.2.le
  have hxsub_le : 1 - x ≤ 1 - x * y := by
    nlinarith [hx.1, hy.2]
  have hysub_le : 1 - y ≤ 1 - x * y := by
    nlinarith [hy.1, hx.2]
  calc
    (1 - x) * (1 - y) ≤ (1 - x * y) * (1 - x * y) := by
      exact mul_le_mul hxsub_le hysub_le hysub_nonneg
        (sub_nonneg.mpr (mul_mem_Ioo_unit hx hy).2.le)
    _ = (1 - x * y)^2 := by ring

theorem four_mul_le_add_sq (a b : ℝ) :
    4 * (a * b) ≤ (a + b)^2 := by
  nlinarith [sq_nonneg (a - b)]

theorem four_mul_sondow_numerator_one_le_one_sub_mul_sq {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    4 * (x * (1 - x) * (y * (1 - y))) ≤ (1 - x * y)^2 := by
  let a : ℝ := 1 - x
  let b : ℝ := x * (1 - y)
  have ha : 0 ≤ a := by dsimp [a]; exact sub_nonneg.mpr hx.2
  have hb : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg hx.1 (sub_nonneg.mpr hy.2)
  have hnum_le_ab : x * (1 - x) * (y * (1 - y)) ≤ a * b := by
    dsimp [a, b]
    have hbase_nonneg : 0 ≤ x * (1 - x) * (1 - y) := by
      exact mul_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) (sub_nonneg.mpr hy.2)
    calc
      x * (1 - x) * (y * (1 - y)) = y * (x * (1 - x) * (1 - y)) := by ring
      _ ≤ 1 * (x * (1 - x) * (1 - y)) :=
        mul_le_mul_of_nonneg_right hy.2 hbase_nonneg
      _ = (1 - x) * (x * (1 - y)) := by ring
  have hfour : 4 * (a * b) ≤ (a + b)^2 := four_mul_le_add_sq a b
  calc
    4 * (x * (1 - x) * (y * (1 - y))) ≤ 4 * (a * b) := by
      exact mul_le_mul_of_nonneg_left hnum_le_ab (by norm_num)
    _ ≤ (a + b)^2 := hfour
    _ = (1 - x * y)^2 := by
      dsimp [a, b]
      ring

theorem sondow_integrand_pos_on_open_unit_square (n : ℕ) {x y : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    0 < sondow_integrand n x y := by
  have hxsub : 0 < 1 - x := sub_pos.mpr hx.2
  have hysub : 0 < 1 - y := sub_pos.mpr hy.2
  have hnum : 0 < x^n * (1 - x)^n * y^n * (1 - y)^n := by
    exact mul_pos (mul_pos (mul_pos (pow_pos hx.1 n) (pow_pos hxsub n))
      (pow_pos hy.1 n)) (pow_pos hysub n)
  have hden : 0 < -(1 - x * y) * Real.log (x * y) :=
    sondow_denominator_pos_on_open_unit_square hx hy
  exact div_pos hnum hden

theorem sondow_integrand_one_le_one_on_open_unit_square {x y : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    sondow_integrand 1 x y ≤ 1 := by
  have hxy : x * y ∈ Set.Ioo (0 : ℝ) 1 := mul_mem_Ioo_unit hx hy
  have hcorner_nonneg : 0 ≤ (1 - x) * (1 - y) :=
    mul_nonneg (sub_nonneg.mpr hx.2.le) (sub_nonneg.mpr hy.2.le)
  have hnum_corner :
      x^1 * (1 - x)^1 * y^1 * (1 - y)^1 ≤ (1 - x) * (1 - y) := by
    calc
      x^1 * (1 - x)^1 * y^1 * (1 - y)^1
          = (x * y) * ((1 - x) * (1 - y)) := by ring
      _ ≤ 1 * ((1 - x) * (1 - y)) :=
          mul_le_mul_of_nonneg_right hxy.2.le hcorner_nonneg
      _ = (1 - x) * (1 - y) := by ring
  have hnum_den :
      x^1 * (1 - x)^1 * y^1 * (1 - y)^1 ≤
        -(1 - x * y) * Real.log (x * y) := by
    exact hnum_corner.trans
      ((corner_product_le_one_sub_mul_sq hx hy).trans
        (one_sub_mul_sq_le_sondow_denominator hx hy))
  have hden_pos : 0 < -(1 - x * y) * Real.log (x * y) :=
    sondow_denominator_pos_on_open_unit_square hx hy
  unfold sondow_integrand
  exact (div_le_one hden_pos).2 hnum_den

theorem sondow_integrand_one_le_quarter_on_open_unit_square {x y : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    sondow_integrand 1 x y ≤ (1 : ℝ) / 4 := by
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
  have hnum_sq :
      x^1 * (1 - x)^1 * y^1 * (1 - y)^1 ≤ ((1 - x * y)^2) / 4 := by
    have h :=
      four_mul_sondow_numerator_one_le_one_sub_mul_sq hxIcc hyIcc
    nlinarith
  have hnum_den :
      x^1 * (1 - x)^1 * y^1 * (1 - y)^1 ≤
        (-(1 - x * y) * Real.log (x * y)) / 4 := by
    exact hnum_sq.trans
      (div_le_div_of_nonneg_right
        (one_sub_mul_sq_le_sondow_denominator hx hy) (by norm_num))
  have hden_pos : 0 < -(1 - x * y) * Real.log (x * y) :=
    sondow_denominator_pos_on_open_unit_square hx hy
  unfold sondow_integrand
  rw [div_le_iff₀ hden_pos]
  nlinarith

theorem sondow_integrand_zero_of_left_zero (n : ℕ) (y : ℝ) :
    sondow_integrand n 0 y = 0 := by
  simp [sondow_integrand]

theorem sondow_integrand_zero_of_right_zero (n : ℕ) (x : ℝ) :
    sondow_integrand n x 0 = 0 := by
  simp [sondow_integrand]

theorem sondow_integrand_zero_of_left_one {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :
    sondow_integrand n 1 y = 0 := by
  have hn_ne : n ≠ 0 := Nat.ne_zero_of_lt hn
  simp [sondow_integrand, hn_ne]

theorem sondow_integrand_zero_of_right_one {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    sondow_integrand n x 1 = 0 := by
  have hn_ne : n ≠ 0 := Nat.ne_zero_of_lt hn
  simp [sondow_integrand, hn_ne]

theorem sondow_integrand_continuousOn_y_open_unit (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousOn (fun y : ℝ => sondow_integrand n x y) (Set.Ioo (0 : ℝ) 1) := by
  intro y hy
  have hden_ne : -(1 - x * y) * Real.log (x * y) ≠ 0 :=
    (sondow_denominator_pos_on_open_unit_square hx hy).ne'
  unfold sondow_integrand
  have hnum_cont :
      ContinuousWithinAt
        (fun y : ℝ => x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n)
        (Set.Ioo (0 : ℝ) 1) y := by
    fun_prop
  have hden_cont :
      ContinuousWithinAt (fun y : ℝ => -(1 - x * y) * Real.log (x * y))
        (Set.Ioo (0 : ℝ) 1) y := by
    have hxy_ne : x * y ≠ 0 := mul_ne_zero hx.1.ne' hy.1.ne'
    fun_prop
  exact hnum_cont.div hden_cont hden_ne

theorem sondow_integrand_continuousOn_x_open_unit (n : ℕ) {y : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x : ℝ => sondow_integrand n x y) (Set.Ioo (0 : ℝ) 1) := by
  intro x hx
  have hden_ne : -(1 - x * y) * Real.log (x * y) ≠ 0 :=
    (sondow_denominator_pos_on_open_unit_square hx hy).ne'
  unfold sondow_integrand
  have hnum_cont :
      ContinuousWithinAt
        (fun x : ℝ => x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n)
        (Set.Ioo (0 : ℝ) 1) x := by
    fun_prop
  have hden_cont :
      ContinuousWithinAt (fun x : ℝ => -(1 - x * y) * Real.log (x * y))
        (Set.Ioo (0 : ℝ) 1) x := by
    have hxy_ne : x * y ≠ 0 := mul_ne_zero hx.1.ne' hy.1.ne'
    fun_prop
  exact hnum_cont.div hden_cont hden_ne

theorem sondow_integrand_intervalIntegrable_y_of_uIcc_subset_open (n : ℕ) {x a b : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hsub : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun y : ℝ => sondow_integrand n x y) volume a b := by
  exact ((sondow_integrand_continuousOn_y_open_unit n hx).mono hsub).intervalIntegrable

theorem sondow_integrand_intervalIntegrable_x_of_uIcc_subset_open (n : ℕ) {y a b : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    (hsub : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x : ℝ => sondow_integrand n x y) volume a b := by
  exact ((sondow_integrand_continuousOn_x_open_unit n hy).mono hsub).intervalIntegrable

theorem uIcc_eps_one_sub_subset_open_unit {ε : ℝ} (hε_pos : 0 < ε)
    (hε_half : ε ≤ (1 : ℝ) / 2) :
    Set.uIcc ε (1 - ε) ⊆ Set.Ioo (0 : ℝ) 1 := by
  have hε_le : ε ≤ 1 - ε := by linarith
  rw [Set.uIcc_of_le hε_le]
  intro z hz
  exact ⟨hε_pos.trans_le hz.1, hz.2.trans_lt (by linarith)⟩

theorem sondow_integrand_intervalIntegrable_y_eps (n : ℕ) {x ε : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hε_pos : 0 < ε)
    (hε_half : ε ≤ (1 : ℝ) / 2) :
    IntervalIntegrable (fun y : ℝ => sondow_integrand n x y) volume ε (1 - ε) := by
  exact sondow_integrand_intervalIntegrable_y_of_uIcc_subset_open n hx
    (uIcc_eps_one_sub_subset_open_unit hε_pos hε_half)

theorem sondow_integrand_intervalIntegrable_x_eps (n : ℕ) {y ε : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) (hε_pos : 0 < ε)
    (hε_half : ε ≤ (1 : ℝ) / 2) :
    IntervalIntegrable (fun x : ℝ => sondow_integrand n x y) volume ε (1 - ε) := by
  exact sondow_integrand_intervalIntegrable_x_of_uIcc_subset_open n hy
    (uIcc_eps_one_sub_subset_open_unit hε_pos hε_half)

theorem unit_interval_mul_sub_le_quarter (x : ℝ) :
    x * (1 - x) ≤ (1 : ℝ) / 4 := by
  nlinarith [sq_nonneg (x - 1 / 2)]

theorem unit_square_mul_sub_mul_sub_le_sixteenth {x y : ℝ}
    (_hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    x * (1 - x) * (y * (1 - y)) ≤ (1 : ℝ) / 16 := by
  have hx' : x * (1 - x) ≤ (1 : ℝ) / 4 := unit_interval_mul_sub_le_quarter x
  have hy' : y * (1 - y) ≤ (1 : ℝ) / 4 := unit_interval_mul_sub_le_quarter y
  have hmul := mul_le_mul hx' hy' (mul_nonneg hy.1 (sub_nonneg.mpr hy.2))
    (by positivity : 0 ≤ (1 : ℝ) / 4)
  have hq : ((1 : ℝ) / 4) * ((1 : ℝ) / 4) = (1 : ℝ) / 16 := by
    norm_num
  exact hmul.trans_eq hq

theorem sondow_integrand_succ_le_div_sixteen (n : ℕ) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    sondow_integrand (n + 1) x y ≤ sondow_integrand n x y / 16 := by
  have hfac : x * (1 - x) * (y * (1 - y)) ≤ (1 : ℝ) / 16 :=
    unit_square_mul_sub_mul_sub_le_sixteenth hx hy
  have hnonneg : 0 ≤ sondow_integrand n x y := sondow_integrand_nonneg_on_unit_square n x y hx hy
  have hmulmono :
      sondow_integrand n x y * (x * (1 - x) * (y * (1 - y))) ≤
        sondow_integrand n x y * ((1 : ℝ) / 16) := by
    exact mul_le_mul_of_nonneg_left hfac hnonneg
  rw [show sondow_integrand n x y / 16 = sondow_integrand n x y * ((1 : ℝ) / 16) by ring]
  calc
    sondow_integrand (n + 1) x y =
        sondow_integrand n x y * (x * (1 - x) * (y * (1 - y))) := by
          unfold sondow_integrand
          ring_nf
    _ ≤ sondow_integrand n x y * ((1 : ℝ) / 16) := hmulmono

theorem sondow_integrand_le_one_on_open_unit_square_of_one_le (n : ℕ) (hn : 1 ≤ n)
    {x y : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    sondow_integrand n x y ≤ 1 := by
  induction n with
  | zero =>
      omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst hk0
        exact sondow_integrand_one_le_one_on_open_unit_square hx hy
      · have hk_ge_one : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
        have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
        calc
          sondow_integrand (k + 1) x y ≤ sondow_integrand k x y / 16 :=
            sondow_integrand_succ_le_div_sixteen k hxIcc hyIcc
          _ ≤ 1 / 16 := by
            exact div_le_div_of_nonneg_right (ih hk_ge_one) (by norm_num)
          _ ≤ 1 := by norm_num

theorem sondow_integrand_intervalIntegrable_y_unit_of_one_le (n : ℕ) (hn : 1 ≤ n)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun y : ℝ => sondow_integrand n x y) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  refine IntegrableOn.of_bound (μ := volume) (s := Set.Ioo (0 : ℝ) 1)
    (f := fun y : ℝ => sondow_integrand n x y) ?_ ?_ 1 ?_
  · exact measure_Ioo_lt_top
  · exact ContinuousOn.aestronglyMeasurable
      (sondow_integrand_continuousOn_y_open_unit n hx) measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hnonneg : 0 ≤ sondow_integrand n x y :=
      le_of_lt (sondow_integrand_pos_on_open_unit_square n hx hy)
    have hle : sondow_integrand n x y ≤ 1 :=
      sondow_integrand_le_one_on_open_unit_square_of_one_le n hn hx hy
    rw [Real.norm_of_nonneg hnonneg]
    exact hle

theorem sondow_integrand_intervalIntegrable_x_unit_of_one_le (n : ℕ) (hn : 1 ≤ n)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x : ℝ => sondow_integrand n x y) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  refine IntegrableOn.of_bound (μ := volume) (s := Set.Ioo (0 : ℝ) 1)
    (f := fun x : ℝ => sondow_integrand n x y) ?_ ?_ 1 ?_
  · exact measure_Ioo_lt_top
  · exact ContinuousOn.aestronglyMeasurable
      (sondow_integrand_continuousOn_x_open_unit n hy) measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hnonneg : 0 ≤ sondow_integrand n x y :=
      le_of_lt (sondow_integrand_pos_on_open_unit_square n hx hy)
    have hle : sondow_integrand n x y ≤ 1 :=
      sondow_integrand_le_one_on_open_unit_square_of_one_le n hn hx hy
    rw [Real.norm_of_nonneg hnonneg]
    exact hle

theorem inner_I_succ_le_div_sixteen_of_mem_Ioo (n : ℕ) (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    inner_I (n + 1) x ≤ inner_I n x / 16 := by
  unfold inner_I
  have hmono :
      (∫ y in (0 : ℝ)..1, sondow_integrand (n + 1) x y) ≤
        ∫ y in (0 : ℝ)..1, sondow_integrand n x y / 16 := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
      (f := fun y : ℝ => sondow_integrand (n + 1) x y)
      (g := fun y : ℝ => sondow_integrand n x y / 16) zero_le_one
      (sondow_integrand_intervalIntegrable_y_unit_of_one_le (n + 1) (Nat.succ_pos n) hx)
      (IntervalIntegrable.div_const
        (sondow_integrand_intervalIntegrable_y_unit_of_one_le n hn hx) 16)
      ?_
    intro y hy
    exact sondow_integrand_succ_le_div_sixteen n ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩
  have hdiv :
      (∫ y in (0 : ℝ)..1, sondow_integrand n x y / 16) =
        (∫ y in (0 : ℝ)..1, sondow_integrand n x y) / 16 := by
    rw [intervalIntegral.integral_div]
  exact hmono.trans_eq hdiv

theorem inner_I_zero_of_left_zero (n : ℕ) : inner_I n 0 = 0 := by
  simp [inner_I, sondow_integrand_zero_of_left_zero]

theorem inner_I_zero_of_left_one {n : ℕ} (hn : 1 ≤ n) : inner_I n 1 = 0 := by
  simp [inner_I, sondow_integrand_zero_of_left_one hn]

theorem inner_I_succ_le_div_sixteen_of_mem_Icc (n : ℕ) (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    inner_I (n + 1) x ≤ inner_I n x / 16 := by
  rcases lt_or_eq_of_le hx.1 with hx_pos | rfl
  · rcases lt_or_eq_of_le hx.2 with hx_lt | rfl
    · exact inner_I_succ_le_div_sixteen_of_mem_Ioo n hn ⟨hx_pos, hx_lt⟩
    · simp [inner_I_zero_of_left_one hn, inner_I_zero_of_left_one (Nat.succ_pos n)]
  · simp [inner_I_zero_of_left_zero]

theorem inner_I_le_one_of_mem_Ioo (n : ℕ) (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    inner_I n x ≤ 1 := by
  unfold inner_I
  have hmono :
      (∫ y in (0 : ℝ)..1, sondow_integrand n x y) ≤ ∫ _y in (0 : ℝ)..1, (1 : ℝ) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
      (f := fun y : ℝ => sondow_integrand n x y)
      (g := fun _y : ℝ => (1 : ℝ)) zero_le_one
      (sondow_integrand_intervalIntegrable_y_unit_of_one_le n hn hx)
      intervalIntegrable_const
      ?_
    intro y hy
    exact sondow_integrand_le_one_on_open_unit_square_of_one_le n hn hx hy
  simpa using hmono

theorem inner_I_le_one_of_mem_Icc (n : ℕ) (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    inner_I n x ≤ 1 := by
  rcases lt_or_eq_of_le hx.1 with hx_pos | rfl
  · rcases lt_or_eq_of_le hx.2 with hx_lt | rfl
    · exact inner_I_le_one_of_mem_Ioo n hn ⟨hx_pos, hx_lt⟩
    · simp [inner_I_zero_of_left_one hn]
  · simp [inner_I_zero_of_left_zero]

theorem inner_I_continuousOn_open_unit (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (inner_I n) (Set.Ioo (0 : ℝ) 1) := by
  intro x hx
  unfold inner_I
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (μ := volume) (F := fun x y : ℝ => sondow_integrand n x y)
    (bound := fun _ : ℝ => (1 : ℝ)) (a := 0) (b := 1)
    (s := Set.Ioo (0 : ℝ) 1) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (intervalIntegrable_iff.mp
      (sondow_integrand_intervalIntegrable_y_unit_of_one_le n hn hx)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have h_ae_one : ∀ᵐ y : ℝ ∂volume, y ∈ ({1} : Set ℝ)ᶜ :=
      compl_mem_ae_iff.mpr (by simp : volume ({1} : Set ℝ) = 0)
    filter_upwards [h_ae_one] with y hy_ne hy_interval
    have hy_open : y ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at hy_interval
      exact ⟨hy_interval.1, lt_of_le_of_ne hy_interval.2 (by simpa using hy_ne)⟩
    have hnonneg : 0 ≤ sondow_integrand n x y :=
      le_of_lt (sondow_integrand_pos_on_open_unit_square n hx hy_open)
    have hle : sondow_integrand n x y ≤ 1 :=
      sondow_integrand_le_one_on_open_unit_square_of_one_le n hn hx hy_open
    rw [Real.norm_of_nonneg hnonneg]
    exact hle
  · have h_ae_one : ∀ᵐ y : ℝ ∂volume, y ∈ ({1} : Set ℝ)ᶜ :=
      compl_mem_ae_iff.mpr (by simp : volume ({1} : Set ℝ) = 0)
    filter_upwards [h_ae_one] with y hy_ne hy_interval
    have hy_open : y ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at hy_interval
      exact ⟨hy_interval.1, lt_of_le_of_ne hy_interval.2 (by simpa using hy_ne)⟩
    exact sondow_integrand_continuousOn_x_open_unit n hy_open x hx

theorem inner_I_intervalIntegrable_unit_of_one_le (n : ℕ) (hn : 1 ≤ n) :
    IntervalIntegrable (inner_I n) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  refine IntegrableOn.of_bound (μ := volume) (s := Set.Ioo (0 : ℝ) 1)
    (f := inner_I n) ?_ ?_ 1 ?_
  · exact measure_Ioo_lt_top
  · exact ContinuousOn.aestronglyMeasurable
      (inner_I_continuousOn_open_unit n hn) measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hnonneg : 0 ≤ inner_I n x :=
      inner_I_nonneg_on_unit_interval_of_integrand_nonneg_on_unit_square
        (sondow_integrand_nonneg_on_unit_square n) x hxIcc
    have hle : inner_I n x ≤ 1 := inner_I_le_one_of_mem_Ioo n hn hx
    rw [Real.norm_of_nonneg hnonneg]
    exact hle

theorem I_succ_le_div_sixteen_of_one_le (n : ℕ) (hn : 1 ≤ n) :
    I (n + 1) ≤ I n / 16 := by
  unfold I
  have hmono :
      (∫ x in (0 : ℝ)..1, inner_I (n + 1) x) ≤
        ∫ x in (0 : ℝ)..1, inner_I n x / 16 := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
      (f := inner_I (n + 1)) (g := fun x : ℝ => inner_I n x / 16) zero_le_one
      (inner_I_intervalIntegrable_unit_of_one_le (n + 1) (Nat.succ_pos n))
      (IntervalIntegrable.div_const (inner_I_intervalIntegrable_unit_of_one_le n hn) 16)
      ?_
    intro x hx
    exact inner_I_succ_le_div_sixteen_of_mem_Ioo n hn hx
  have hdiv :
      (∫ x in (0 : ℝ)..1, inner_I n x / 16) =
        (∫ x in (0 : ℝ)..1, inner_I n x) / 16 := by
    rw [intervalIntegral.integral_div]
  exact hmono.trans_eq hdiv

theorem inner_I_one_le_quarter_of_mem_Ioo {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    inner_I 1 x ≤ (1 : ℝ) / 4 := by
  unfold inner_I
  have hmono :
      (∫ y in (0 : ℝ)..1, sondow_integrand 1 x y) ≤
        ∫ _y in (0 : ℝ)..1, (1 : ℝ) / 4 := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
      (f := fun y : ℝ => sondow_integrand 1 x y)
      (g := fun _y : ℝ => (1 : ℝ) / 4) zero_le_one
      (sondow_integrand_intervalIntegrable_y_unit_of_one_le 1 le_rfl hx)
      intervalIntegrable_const
      ?_
    intro y hy
    exact sondow_integrand_one_le_quarter_on_open_unit_square hx hy
  simpa using hmono

theorem inner_I_one_le_quarter_of_mem_Icc {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    inner_I 1 x ≤ (1 : ℝ) / 4 := by
  rcases lt_or_eq_of_le hx.1 with hx_pos | rfl
  · rcases lt_or_eq_of_le hx.2 with hx_lt | rfl
    · exact inner_I_one_le_quarter_of_mem_Ioo ⟨hx_pos, hx_lt⟩
    · simp [inner_I_zero_of_left_one le_rfl]
  · simp [inner_I_zero_of_left_zero]

theorem I_one_le_quarter : I 1 ≤ (1 : ℝ) / 4 := by
  unfold I
  have hmono :
      (∫ x in (0 : ℝ)..1, inner_I 1 x) ≤ ∫ _x in (0 : ℝ)..1, (1 : ℝ) / 4 := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
      (f := inner_I 1) (g := fun _x : ℝ => (1 : ℝ) / 4) zero_le_one
      (inner_I_intervalIntegrable_unit_of_one_le 1 le_rfl)
      intervalIntegrable_const
      ?_
    intro x hx
    exact inner_I_one_le_quarter_of_mem_Ioo hx
  simpa using hmono

-- Closed-form bound: I(n) ≤ 16^{-n} for all n ≥ 1, obtained by iterating the
-- recursion I(k+1) ≤ I(k)/16 from the base case I(1) ≤ 1/16.
-- The base case is kept as an explicit hypothesis because the weaker theorem
-- `I_one_le_quarter` already suffices for the main Nair convergence chain.
theorem I_le_sixteenth_pow_of_I_one_le_sixteenth
    (hI1 : I 1 ≤ (1 : ℝ) / 16) (n : ℕ) (hn : 1 ≤ n) :
    I n ≤ ((1 : ℝ) / 16) ^ n := by
  induction n with
  | zero => exact absurd hn (by decide)
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst hk0
        have hpow : ((1 : ℝ) / 16) ^ (0 + 1) = (1 : ℝ) / 16 := by simp [pow_one]
        rw [hpow]
        exact hI1
      · have hk_ge1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hrec : I (k + 1) ≤ I k / 16 := I_succ_le_div_sixteen_of_one_le k hk_ge1
        have hih : I k ≤ ((1 : ℝ) / 16) ^ k := ih hk_ge1
        have hge0 : 0 ≤ I k :=
          I_nonneg_prop_of_integrand_nonneg_on_unit_square
            (sondow_integrand_nonneg_on_unit_square k)
        calc I (k + 1) ≤ I k / 16 := hrec
          _ ≤ ((1 : ℝ) / 16) ^ k / 16 := by
              exact div_le_div_of_nonneg_right hih (by norm_num)
          _ = ((1 : ℝ) / 16) ^ (k + 1) := by
              rw [pow_succ]
              ring

-- Weaker but theorem-backed tail bound. The proved estimate `I 1 ≤ 1/4` is enough
-- for convergence once paired with the 1/16 recursion from n ≥ 1.
theorem I_le_four_mul_sixteenth_pow (n : ℕ) (hn : 1 ≤ n) :
    I n ≤ 4 * ((1 : ℝ) / 16) ^ n := by
  induction n with
  | zero => exact absurd hn (by decide)
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst hk0
        have hpow : 4 * ((1 : ℝ) / 16) ^ (0 + 1) = (1 : ℝ) / 4 := by
          norm_num
        rw [hpow]
        exact I_one_le_quarter
      · have hk_ge1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hrec : I (k + 1) ≤ I k / 16 := I_succ_le_div_sixteen_of_one_le k hk_ge1
        have hih : I k ≤ 4 * ((1 : ℝ) / 16) ^ k := ih hk_ge1
        calc
          I (k + 1) ≤ I k / 16 := hrec
          _ ≤ (4 * ((1 : ℝ) / 16) ^ k) / 16 := by
              exact div_le_div_of_nonneg_right hih (by norm_num)
          _ = 4 * ((1 : ℝ) / 16) ^ (k + 1) := by
              rw [pow_succ]
              ring

-- Hanson-style LCM exponential upper bound in Mathlib's standard `Nat.lcmUpto` language:
-- lcm(1,...,n) ≤ 3^n. It is stated over `ℕ`, matching the literature.
-- The real-valued forms below are derived wrappers used by the analytic estimates.
def lcmUpto_le_three_pow_nat_statement : Prop :=
  ∀ n : ℕ, Nat.lcmUpto n ≤ 3 ^ n

theorem lcmUpto_le_three_pow
    (hlcm : lcmUpto_le_three_pow_nat_statement) (n : ℕ) :
    (Nat.lcmUpto n : ℝ) ≤ (3 : ℝ) ^ n := by
  exact_mod_cast hlcm n

theorem lcmUpto_double_le_nine_pow_nat
    (hlcm : lcmUpto_le_three_pow_nat_statement) (n : ℕ) :
    Nat.lcmUpto (2 * n) ≤ 9 ^ n := by
  calc
    Nat.lcmUpto (2 * n) ≤ 3 ^ (2 * n) := hlcm (2 * n)
    _ = 9 ^ n := by
      rw [show 2 * n = n * 2 by omega, pow_mul]
      rw [pow_two]
      rw [← mul_pow]
      norm_num

theorem lcmUpto_double_le_nine_pow
    (hlcm : lcmUpto_le_three_pow_nat_statement) (n : ℕ) :
    (Nat.lcmUpto (2 * n) : ℝ) ≤ (9 : ℝ) ^ n := by
  exact_mod_cast lcmUpto_double_le_nine_pow_nat hlcm n

theorem d_double_le_nine_pow
    (hlcm : lcmUpto_le_three_pow_nat_statement) (n : ℕ) :
    (d (2 * n) : ℝ) ≤ (9 : ℝ) ^ n := by
  rw [d_double_eq_lcmUpto]
  exact lcmUpto_double_le_nine_pow hlcm n

theorem sondow_product_le_four_mul_nine_sixteenth_pow
    (hlcm : lcmUpto_le_three_pow_nat_statement) (n : ℕ) (hn : 1 ≤ n) :
    (d (2 * n) : ℝ) * I n ≤ 4 * ((9 : ℝ) / 16) ^ n := by
  calc
    (d (2 * n) : ℝ) * I n
        ≤ (9 : ℝ) ^ n * I n := mul_le_mul_of_nonneg_right
          (d_double_le_nine_pow hlcm n) (I_nonneg_prop_of_integrand_nonneg_on_unit_square
          (sondow_integrand_nonneg_on_unit_square n))
    _ ≤ (9 : ℝ) ^ n * (4 * ((1 : ℝ) / 16) ^ n) := mul_le_mul_of_nonneg_left
          (I_le_four_mul_sixteenth_pow n hn) (pow_nonneg (by norm_num) n)
    _ = 4 * ((9 : ℝ) / 16) ^ n := by
        rw [show (9 : ℝ) ^ n * (4 * ((1 : ℝ) / 16) ^ n) =
          4 * ((9 : ℝ) ^ n * ((1 : ℝ) / 16) ^ n) by ring]
        rw [← mul_pow]
        ring

-- The product d(2n) * I(n) → 0.
-- For n ≥ 1: d(2n) * I(n) ≤ 9^n * 16^{-n} = (9/16)^n → 0.
-- The n = 0 case is excluded via Tendsto.congr', since atTop only cares about
-- the tail of the sequence.
theorem sondow_product_tendsto_zero_of_lcm_bound
    (hlcm : lcmUpto_le_three_pow_nat_statement) :
    Tendsto (fun n : ℕ => (d (2 * n) : ℝ) * I n) atTop (nhds 0) := by
  have hkey : ∀ᶠ n in atTop,
      (d (2 * n) : ℝ) * I n ≤ 4 * ((9 : ℝ) / 16) ^ n := by
    refine Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    exact sondow_product_le_four_mul_nine_sixteenth_pow hlcm n hn
  have hnonneg : ∀ᶠ n in atTop, 0 ≤ (d (2 * n) : ℝ) * I n := by
    refine Filter.eventually_atTop.2 ⟨0, fun n _ => ?_⟩
    exact mul_nonneg (Nat.cast_nonneg _)
      (I_nonneg_prop_of_integrand_nonneg_on_unit_square
        (sondow_integrand_nonneg_on_unit_square n))
  have htendsto_base : Tendsto (fun n : ℕ => ((9 : ℝ) / 16) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have htendsto : Tendsto (fun n : ℕ => 4 * ((9 : ℝ) / 16) ^ n) atTop (nhds 0) := by
    simpa using htendsto_base.const_mul (4 : ℝ)
  exact squeeze_zero' hnonneg hkey htendsto

theorem sondow_integrand_nonneg_eventual_on_unit_square_of_forall :
    sondow_integrand_nonneg_eventual_on_unit_square := by
  exact ⟨0, fun n _ => sondow_integrand_nonneg_on_unit_square n⟩

theorem I_nonneg_eventual_of_sondow_integrand :
    I_nonneg_eventual := by
  exact I_nonneg_eventual_of_integrand_nonneg_eventual_on_unit_square
    sondow_integrand_nonneg_eventual_on_unit_square_of_forall

theorem sondow_term_range_prop_of_nonneg_and_lt_one {n : ℕ}
    (h_nonneg : sondow_term_nonneg_prop n) (h_lt : sondow_term_lt_one_prop n) :
    sondow_term_range_prop n := by
  exact ⟨h_nonneg, h_lt⟩

theorem sondow_term_range_eventual_of_nonneg_and_lt_one
    (h_nonneg : sondow_term_nonneg_eventual) (h_lt : sondow_term_lt_one_eventual) :
    sondow_term_range_eventual := by
  rcases h_nonneg with ⟨Nnonneg, hNnonneg⟩
  rcases h_lt with ⟨Nlt, hNlt⟩
  refine ⟨max Nnonneg Nlt, ?_⟩
  intro n hn
  exact sondow_term_range_prop_of_nonneg_and_lt_one
    (hNnonneg n (le_trans (Nat.le_max_left Nnonneg Nlt) hn))
    (hNlt n (le_trans (Nat.le_max_right Nnonneg Nlt) hn))

theorem sondow_term_lt_one_eventual_of_tendsto_zero
    (h : Tendsto (fun n : ℕ => (d (2 * n) : ℝ) * I n) atTop (nhds 0)) :
    sondow_term_lt_one_eventual := by
  have h_eventual : ∀ᶠ n in atTop, (d (2 * n) : ℝ) * I n < 1 := by
    exact h.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  rcases Filter.eventually_atTop.mp h_eventual with ⟨N, hN⟩
  exact ⟨N, fun n hn => hN n hn⟩

theorem four_mul_nine_sixteenth_pow_lt_one_eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 4 * ((9 : ℝ) / 16) ^ n < 1 := by
  have htendsto_base : Tendsto (fun n : ℕ => ((9 : ℝ) / 16) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have htendsto : Tendsto (fun n : ℕ => 4 * ((9 : ℝ) / 16) ^ n) atTop (nhds 0) := by
    simpa using htendsto_base.const_mul (4 : ℝ)
  have h_eventual : ∀ᶠ n in atTop, 4 * ((9 : ℝ) / 16) ^ n < 1 := by
    exact htendsto.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  exact Filter.eventually_atTop.mp h_eventual

theorem sondow_term_lt_one_eventual_of_lcm_bound
    (hlcm : lcmUpto_le_three_pow_nat_statement) :
    sondow_term_lt_one_eventual := by
  rcases four_mul_nine_sixteenth_pow_lt_one_eventual with ⟨N, hN⟩
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hn_one : 1 ≤ n := le_trans (Nat.le_max_left 1 N) hn
  have hn_N : N ≤ n := le_trans (Nat.le_max_right 1 N) hn
  exact lt_of_le_of_lt
    (sondow_product_le_four_mul_nine_sixteenth_pow hlcm n hn_one)
    (hN n hn_N)

theorem tendsto_zero_of_geometric_half_bound {f : ℕ → ℝ}
    (hf_nonneg : ∀ n : ℕ, 0 ≤ f n)
    (hf_le : ∀ n : ℕ, f n ≤ ((1 : ℝ) / 2) ^ n) :
    Tendsto f atTop (nhds 0) := by
  exact squeeze_zero hf_nonneg hf_le
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

theorem sondow_product_le_geometric_half_of_bounds {n : ℕ}
    (hd : (d (2 * n) : ℝ) ≤ (8 : ℝ) ^ n)
    (hI_nonneg : 0 ≤ I n)
    (hI : I n ≤ (16 : ℝ)⁻¹ ^ n) :
    (d (2 * n) : ℝ) * I n ≤ ((1 : ℝ) / 2) ^ n := by
  have hmul : (d (2 * n) : ℝ) * I n ≤ (8 : ℝ) ^ n * ((16 : ℝ)⁻¹ ^ n) := by
    exact mul_le_mul hd hI hI_nonneg (pow_nonneg (by norm_num) n)
  have hpow : (8 : ℝ) ^ n * ((16 : ℝ)⁻¹ ^ n) = ((1 : ℝ) / 2) ^ n := by
    rw [← mul_pow]
    norm_num
  exact hmul.trans_eq hpow

theorem sondow_product_tendsto_zero_of_geometric_bounds
    (hd : ∀ n : ℕ, (d (2 * n) : ℝ) ≤ (8 : ℝ)^n)
    (hI_nonneg : ∀ n : ℕ, 0 ≤ I n)
    (hI : ∀ n : ℕ, I n ≤ (16 : ℝ)⁻¹ ^ n) :
    Tendsto (fun n : ℕ => (d (2 * n) : ℝ) * I n) atTop (nhds 0) := by
  apply tendsto_zero_of_geometric_half_bound
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) (hI_nonneg n)
  · intro n
    exact sondow_product_le_geometric_half_of_bounds (hd n) (hI_nonneg n) (hI n)

theorem sondow_term_range_eventual_of_tendsto_zero
    (h : Tendsto (fun n : ℕ => (d (2 * n) : ℝ) * I n) atTop (nhds 0)) :
    sondow_term_range_eventual := by
  exact sondow_term_range_eventual_of_nonneg_and_lt_one
    (sondow_term_nonneg_eventual_of_I_nonneg_eventual I_nonneg_eventual_of_sondow_integrand)
    (sondow_term_lt_one_eventual_of_tendsto_zero h)

theorem sondow_identity_eventual_implies_some :
    sondow_identity_eventual → sondow_identity_some := by
  intro h
  rcases h with ⟨N, hN⟩
  refine ⟨N + 1, by simp, ?_⟩
  exact hN (N + 1) (Nat.le_succ N)

theorem sondow_identity_eventual_intro {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → sondow_identity_prop n) : sondow_identity_eventual := by
  exact ⟨N, h⟩

theorem sondow_identity_explicit_eventual_intro {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → sondow_identity_explicit_prop n) :
    sondow_identity_explicit_eventual := by
  exact ⟨N, h⟩

theorem sondow_identity_eventual_iff_exists_cutoff :
    sondow_identity_eventual ↔ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → sondow_identity_prop n := by
  rfl

theorem sondow_identity_explicit_eventual_iff_exists_cutoff :
    sondow_identity_explicit_eventual ↔
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → sondow_identity_explicit_prop n := by
  rfl

theorem sondow_identity_eventual_of_explicit_eventual
    (hS : S_matches_sondow_explicit)
    (h : sondow_identity_explicit_eventual) :
    sondow_identity_eventual := by
  rcases h with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact (sondow_identity_prop_iff_explicit (hS n)).2 (hN n hn)

theorem sondow_identity_eventual_of_explicit_eventual_true
    (h : sondow_identity_explicit_eventual) :
    sondow_identity_eventual := by
  exact sondow_identity_eventual_of_explicit_eventual S_matches_sondow_explicit_true h

theorem sondow_identity_explicit_eventual_of_eventual
    (hS : S_matches_sondow_explicit)
    (h : sondow_identity_eventual) :
    sondow_identity_explicit_eventual := by
  rcases h with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact (sondow_identity_prop_iff_explicit (hS n)).1 (hN n hn)

theorem sondow_identity_explicit_eventual_of_eventual_true
    (h : sondow_identity_eventual) :
    sondow_identity_explicit_eventual := by
  exact sondow_identity_explicit_eventual_of_eventual S_matches_sondow_explicit_true h

theorem sondow_identity_eventual_iff_explicit_eventual
    (hS : S_matches_sondow_explicit) :
    sondow_identity_eventual ↔ sondow_identity_explicit_eventual := by
  constructor
  · exact sondow_identity_explicit_eventual_of_eventual hS
  · exact sondow_identity_eventual_of_explicit_eventual hS

theorem sondow_identity_eventual_iff_explicit_eventual_true :
    sondow_identity_eventual ↔ sondow_identity_explicit_eventual := by
  exact sondow_identity_eventual_iff_explicit_eventual S_matches_sondow_explicit_true

theorem sondow_integer_gap_eventual_of_explicit_eventual
    (hS : S_matches_sondow_explicit)
    (h : sondow_integer_gap_explicit_eventual) :
    sondow_integer_gap_eventual := by
  rcases h with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact (sondow_integer_gap_prop_iff_explicit (hS n)).2 (hN n hn)

theorem sondow_integer_gap_eventual_of_explicit_eventual_true
    (h : sondow_integer_gap_explicit_eventual) :
    sondow_integer_gap_eventual := by
  exact sondow_integer_gap_eventual_of_explicit_eventual S_matches_sondow_explicit_true h

theorem sondow_integer_gap_explicit_eventual_of_eventual
    (hS : S_matches_sondow_explicit)
    (h : sondow_integer_gap_eventual) :
    sondow_integer_gap_explicit_eventual := by
  rcases h with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact (sondow_integer_gap_prop_iff_explicit (hS n)).1 (hN n hn)

theorem sondow_integer_gap_explicit_eventual_of_eventual_true
    (h : sondow_integer_gap_eventual) :
    sondow_integer_gap_explicit_eventual := by
  exact sondow_integer_gap_explicit_eventual_of_eventual S_matches_sondow_explicit_true h

theorem sondow_integer_gap_eventual_iff_explicit_eventual
    (hS : S_matches_sondow_explicit) :
    sondow_integer_gap_eventual ↔ sondow_integer_gap_explicit_eventual := by
  constructor
  · exact sondow_integer_gap_explicit_eventual_of_eventual hS
  · exact sondow_integer_gap_eventual_of_explicit_eventual hS

theorem sondow_integer_gap_eventual_iff_explicit_eventual_true :
    sondow_integer_gap_eventual ↔ sondow_integer_gap_explicit_eventual := by
  exact sondow_integer_gap_eventual_iff_explicit_eventual S_matches_sondow_explicit_true

theorem sondow_identity_eventual_of_integer_gap_and_range
    (h_gap : sondow_integer_gap_eventual) (h_range : sondow_term_range_eventual) :
    sondow_identity_eventual := by
  rcases h_gap with ⟨Ngap, hNgap⟩
  rcases h_range with ⟨Nrange, hNrange⟩
  refine ⟨max Ngap Nrange, ?_⟩
  intro n hn
  exact sondow_identity_prop_of_integer_gap_and_range
    (hNgap n (le_trans (Nat.le_max_left Ngap Nrange) hn))
    (hNrange n (le_trans (Nat.le_max_right Ngap Nrange) hn))

theorem sondow_identity_explicit_eventual_of_integer_gap_and_range
    (h_gap : sondow_integer_gap_explicit_eventual) (h_range : sondow_term_range_eventual) :
    sondow_identity_explicit_eventual := by
  rcases h_gap with ⟨Ngap, hNgap⟩
  rcases h_range with ⟨Nrange, hNrange⟩
  refine ⟨max Ngap Nrange, ?_⟩
  intro n hn
  exact sondow_identity_explicit_prop_of_integer_gap_and_range
    (hNgap n (le_trans (Nat.le_max_left Ngap Nrange) hn))
    (hNrange n (le_trans (Nat.le_max_right Ngap Nrange) hn))

theorem sondow_identity_eventual_of_integer_gap_and_tendsto_zero
    (h_gap : sondow_integer_gap_eventual)
    (h_tendsto : Tendsto (fun n : ℕ => (d (2 * n) : ℝ) * I n) atTop (nhds 0)) :
    sondow_identity_eventual := by
  exact sondow_identity_eventual_of_integer_gap_and_range h_gap
    (sondow_term_range_eventual_of_tendsto_zero h_tendsto)

theorem sondow_identity_explicit_eventual_of_integer_gap_and_tendsto_zero
    (h_gap : sondow_integer_gap_explicit_eventual)
    (h_tendsto : Tendsto (fun n : ℕ => (d (2 * n) : ℝ) * I n) atTop (nhds 0)) :
    sondow_identity_explicit_eventual := by
  exact sondow_identity_explicit_eventual_of_integer_gap_and_range h_gap
    (sondow_term_range_eventual_of_tendsto_zero h_tendsto)

theorem sondow_identity_eventual_of_rational_decomposition_and_lcm_bound
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_rat : is_rational euler_mascheroni)
    (h_decomp : ∀ n : ℕ, sondow_decomposition_prop n) :
    sondow_identity_eventual := by
  exact sondow_identity_eventual_of_integer_gap_and_tendsto_zero
    (sondow_integer_gap_eventual_of_rational_and_decomposition h_product_log h_rat h_decomp)
    (sondow_product_tendsto_zero_of_lcm_bound hlcm)

theorem sondow_identity_eventual_of_rational_explicit_decomposition_and_lcm_bound
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_rat : is_rational euler_mascheroni)
    (hL : ∀ n : ℕ, L n = sondow_L n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n) :
    sondow_identity_eventual := by
  exact sondow_identity_eventual_of_rational_decomposition_and_lcm_bound h_product_log hlcm h_rat
    (sondow_decomposition_all_of_explicit hL h_decomp)

theorem sondow_identity_eventual_of_rational_explicit_decomposition_and_lcm_bound_true
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_rat : is_rational euler_mascheroni)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n) :
    sondow_identity_eventual := by
  exact sondow_identity_eventual_of_rational_decomposition_and_lcm_bound h_product_log hlcm h_rat
    (sondow_decomposition_all_of_explicit_true h_decomp)

theorem sondow_identity_eventual_of_rational_explicit_log_decomposition_and_lcm_bound
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_rat : is_rational euler_mascheroni)
    (h_log : ∀ n : ℕ, sondow_explicit_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n) :
    sondow_identity_eventual := by
  exact sondow_identity_eventual_of_integer_gap_and_tendsto_zero
    (sondow_integer_gap_eventual_of_rational_explicit_log_and_decomposition
      h_rat h_log h_decomp)
    (sondow_product_tendsto_zero_of_lcm_bound hlcm)

theorem sondow_identity_explicit_eventual_of_rational_explicit_log_decomposition_and_lcm_bound
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (hS : S_matches_sondow_explicit)
    (h_rat : is_rational euler_mascheroni)
    (h_log : ∀ n : ℕ, sondow_explicit_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n) :
    sondow_identity_explicit_eventual := by
  exact sondow_identity_explicit_eventual_of_eventual hS
    (sondow_identity_eventual_of_rational_explicit_log_decomposition_and_lcm_bound
      hlcm h_rat h_log h_decomp)

theorem sondow_identity_explicit_eventual_of_rational_explicit_log_decomposition_and_lcm_bound_true
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_rat : is_rational euler_mascheroni)
    (h_log : ∀ n : ℕ, sondow_explicit_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n) :
    sondow_identity_explicit_eventual := by
  exact sondow_identity_explicit_eventual_of_rational_explicit_log_decomposition_and_lcm_bound
    hlcm S_matches_sondow_explicit_true h_rat h_log h_decomp

theorem sondow_identity_explicit_eventual_of_rational_product_log_decomposition_and_lcm_bound
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_rat : is_rational euler_mascheroni)
    (h_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n) :
    sondow_identity_explicit_eventual := by
  exact sondow_identity_explicit_eventual_of_integer_gap_and_tendsto_zero
    (sondow_integer_gap_explicit_eventual_of_rational_product_log_and_decomposition
      h_rat h_log h_decomp)
    (sondow_product_tendsto_zero_of_lcm_bound hlcm)

theorem sondow_identity_explicit_eventual_of_rational_product_log_decomposition_pos_and_lcm_bound
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_rat : is_rational euler_mascheroni)
    (h_log : ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    sondow_identity_explicit_eventual := by
  exact sondow_identity_explicit_eventual_of_integer_gap_and_tendsto_zero
    (sondow_integer_gap_explicit_eventual_of_rational_product_log_and_decomposition_pos
      h_rat h_log h_decomp)
    (sondow_product_tendsto_zero_of_lcm_bound hlcm)

theorem sondow_identity_explicit_eventual_of_rational_standard_sondow_decomposition_and_lcm_bound
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_rat : is_rational euler_mascheroni)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n) :
    sondow_identity_explicit_eventual := by
  exact sondow_identity_explicit_eventual_of_rational_product_log_decomposition_and_lcm_bound
    hlcm h_rat h_product_log h_decomp

theorem sondow_identity_explicit_eventual_of_rational_pos_standard_inputs
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_product_log : ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (h_rat : is_rational euler_mascheroni)
    (h_decomp : ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    sondow_identity_explicit_eventual := by
  exact sondow_identity_explicit_eventual_of_rational_product_log_decomposition_pos_and_lcm_bound
    hlcm h_rat h_product_log h_decomp

theorem sondow_identity_explicit_eventual_of_rational_standard_inputs
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n)
    (h_rat : is_rational euler_mascheroni) :
    sondow_identity_explicit_eventual := by
  exact
    sondow_identity_explicit_eventual_of_rational_standard_sondow_decomposition_and_lcm_bound
      hlcm h_product_log h_rat h_decomp

theorem sondow_identity_eventual_of_rational_standard_inputs
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n)
    (hS : S_matches_sondow_explicit)
    (h_rat : is_rational euler_mascheroni) :
    sondow_identity_eventual := by
  exact sondow_identity_eventual_of_explicit_eventual hS
    (sondow_identity_explicit_eventual_of_rational_standard_inputs
      hlcm h_product_log h_decomp h_rat)

theorem sondow_identity_eventual_of_rational_standard_inputs_true
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n)
    (h_rat : is_rational euler_mascheroni) :
    sondow_identity_eventual := by
  exact sondow_identity_eventual_of_rational_standard_inputs
    hlcm h_product_log h_decomp S_matches_sondow_explicit_true h_rat

theorem sondow_identity_eventual_of_rational_positive_standard_inputs_true
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_product_log : ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n)
    (h_rat : is_rational euler_mascheroni) :
    sondow_identity_eventual := by
  exact sondow_identity_eventual_of_explicit_eventual_true
    (sondow_identity_explicit_eventual_of_rational_product_log_decomposition_pos_and_lcm_bound
      hlcm h_rat h_product_log h_decomp)

theorem sondow_identity_eventual_of_rational_L_alignment_explicit_decomposition_and_lcm_bound
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_rat : is_rational euler_mascheroni)
    (hL : ∀ n : ℕ, L n = sondow_L n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n) :
    sondow_identity_eventual := by
  exact sondow_identity_eventual_of_rational_explicit_log_decomposition_and_lcm_bound hlcm h_rat
    (sondow_explicit_log_relation_all_of_L_alignment h_product_log hL) h_decomp

theorem sondow_identity_eventual_of_rational_explicit_sondow_and_lcm_bound
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n)
    (h_rat : is_rational euler_mascheroni) :
    sondow_identity_eventual := by
  exact sondow_identity_eventual_of_rational_explicit_log_decomposition_and_lcm_bound hlcm h_rat
    (sondow_explicit_log_relation_all_of_product_log h_product_log) h_decomp

theorem sondow_identity_eventual_iff_eventually :
    sondow_identity_eventual ↔ ∀ᶠ n in atTop, sondow_identity_prop n := by
  constructor
  · intro h
    rcases h with ⟨N, hN⟩
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  · intro h
    rcases Filter.eventually_atTop.mp h with ⟨N, hN⟩
    exact ⟨N, hN⟩

theorem sondow_identity_explicit_eventual_iff_eventually :
    sondow_identity_explicit_eventual ↔
      ∀ᶠ n in atTop, sondow_identity_explicit_prop n := by
  constructor
  · intro h
    rcases h with ⟨N, hN⟩
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  · intro h
    rcases Filter.eventually_atTop.mp h with ⟨N, hN⟩
    exact ⟨N, hN⟩

def sondow_reverse_criterion : Prop :=
  sondow_identity_eventual → is_rational euler_mascheroni

-- A compact interface for the external, literature-proved Sondow/LCM forward inputs.
-- These are exactly the ingredients used for the rationality-to-eventual-identity
-- direction; the reverse Sondow criterion is intentionally kept separate below.
structure SondowForwardInputs : Prop where
  lcm_bound : lcmUpto_le_three_pow_nat_statement
  product_log : ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n
  decomposition : ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n

theorem sondow_identity_explicit_eventual_of_rational_forward_inputs
    (hfwd : SondowForwardInputs)
    (h_rat : is_rational euler_mascheroni) :
    sondow_identity_explicit_eventual := by
  exact sondow_identity_explicit_eventual_of_rational_product_log_decomposition_pos_and_lcm_bound
    hfwd.lcm_bound h_rat hfwd.product_log hfwd.decomposition

theorem sondow_identity_eventual_of_rational_forward_inputs
    (hfwd : SondowForwardInputs)
    (h_rat : is_rational euler_mascheroni) :
    sondow_identity_eventual := by
  exact sondow_identity_eventual_of_explicit_eventual_true
    (sondow_identity_explicit_eventual_of_rational_forward_inputs hfwd h_rat)

-- A compact interface for the external, literature-proved Sondow/LCM inputs.
-- The development below proves the internal consequences of this package; it
-- does not pretend to reprove the analytic Sondow identities, the LCM bound, or
-- the reverse Sondow criterion.
structure SondowStandardInputs : Prop where
  lcm_bound : lcmUpto_le_three_pow_nat_statement
  product_log : ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n
  decomposition : ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n
  reverse : sondow_reverse_criterion

def SondowStandardInputs.toForward (hstd : SondowStandardInputs) :
    SondowForwardInputs where
  lcm_bound := hstd.lcm_bound
  product_log := hstd.product_log
  decomposition := hstd.decomposition

theorem rational_of_sondow_identity_explicit_eventual_of_matches
    (h_reverse : sondow_reverse_criterion)
    (hS : S_matches_sondow_explicit) :
    sondow_identity_explicit_eventual → is_rational euler_mascheroni := by
  intro h
  exact h_reverse
    (sondow_identity_eventual_of_explicit_eventual hS h)

theorem rational_of_sondow_identity_explicit_eventual :
    sondow_reverse_criterion →
    sondow_identity_explicit_eventual → is_rational euler_mascheroni := by
  intro h_reverse
  exact rational_of_sondow_identity_explicit_eventual_of_matches
    h_reverse S_matches_sondow_explicit_true

theorem sondow_rational_equivalence_of_forward_reverse
    (h_forward : is_rational euler_mascheroni → sondow_identity_eventual)
    (h_reverse : sondow_reverse_criterion) :
    is_rational euler_mascheroni ↔ sondow_identity_eventual := by
  constructor
  · exact h_forward
  · exact h_reverse

theorem sondow_rational_equivalence_eventually_of_forward_reverse
    (h_forward : is_rational euler_mascheroni → sondow_identity_eventual)
    (h_reverse : sondow_reverse_criterion) :
    is_rational euler_mascheroni ↔ ∀ᶠ n in atTop, sondow_identity_prop n := by
  simpa [sondow_identity_eventual_iff_eventually] using
    sondow_rational_equivalence_of_forward_reverse h_forward h_reverse

theorem sondow_rational_equivalence_standard_inputs
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n)
    (h_reverse : sondow_reverse_criterion) :
    is_rational euler_mascheroni ↔ sondow_identity_eventual := by
  exact sondow_rational_equivalence_of_forward_reverse
    (sondow_identity_eventual_of_rational_standard_inputs_true hlcm h_product_log h_decomp)
    h_reverse

theorem sondow_rational_equivalence_of_standard_package
    (hstd : SondowStandardInputs) :
    is_rational euler_mascheroni ↔ sondow_identity_eventual := by
  exact sondow_rational_equivalence_of_forward_reverse
    (sondow_identity_eventual_of_rational_forward_inputs hstd.toForward)
    hstd.reverse

theorem sondow_rational_equivalence_of_all_n_standard_package
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n)
    (h_reverse : sondow_reverse_criterion) :
    is_rational euler_mascheroni ↔ sondow_identity_eventual := by
  exact sondow_rational_equivalence_standard_inputs
    hlcm h_product_log h_decomp h_reverse

theorem sondow_rational_equivalence_standard_inputs_eventually
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n)
    (h_reverse : sondow_reverse_criterion) :
    is_rational euler_mascheroni ↔ ∀ᶠ n in atTop, sondow_identity_prop n := by
  simpa [sondow_identity_eventual_iff_eventually] using
    sondow_rational_equivalence_standard_inputs hlcm h_product_log h_decomp h_reverse

theorem sondow_rational_equivalence_eventually_of_standard_package
    (hstd : SondowStandardInputs) :
    is_rational euler_mascheroni ↔ ∀ᶠ n in atTop, sondow_identity_prop n := by
  simpa [sondow_identity_eventual_iff_eventually] using
    sondow_rational_equivalence_of_standard_package hstd

theorem sondow_explicit_rational_equivalence_of_matches
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n)
    (h_reverse : sondow_reverse_criterion)
    (hS : S_matches_sondow_explicit) :
    is_rational euler_mascheroni ↔ sondow_identity_explicit_eventual := by
  constructor
  · exact sondow_identity_explicit_eventual_of_rational_standard_inputs
      hlcm h_product_log h_decomp
  · exact rational_of_sondow_identity_explicit_eventual_of_matches h_reverse hS

theorem sondow_explicit_rational_equivalence
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n)
    (h_reverse : sondow_reverse_criterion) :
    is_rational euler_mascheroni ↔ sondow_identity_explicit_eventual := by
  exact sondow_explicit_rational_equivalence_of_matches
    hlcm h_product_log h_decomp h_reverse S_matches_sondow_explicit_true

theorem sondow_explicit_rational_equivalence_of_standard_package
    (hstd : SondowStandardInputs) :
    is_rational euler_mascheroni ↔ sondow_identity_explicit_eventual := by
  constructor
  · intro h_rat
    exact sondow_identity_explicit_eventual_of_rational_forward_inputs hstd.toForward h_rat
  · exact rational_of_sondow_identity_explicit_eventual hstd.reverse

theorem sondow_explicit_rational_equivalence_eventually_of_matches
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n)
    (h_reverse : sondow_reverse_criterion)
    (hS : S_matches_sondow_explicit) :
    is_rational euler_mascheroni ↔
      ∀ᶠ n in atTop, sondow_identity_explicit_prop n := by
  simpa [sondow_identity_explicit_eventual_iff_eventually] using
    sondow_explicit_rational_equivalence_of_matches hlcm h_product_log h_decomp h_reverse hS

theorem sondow_explicit_rational_equivalence_eventually
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_product_log : ∀ n : ℕ, sondow_explicit_product_log_relation_prop n)
    (h_decomp : ∀ n : ℕ, sondow_explicit_decomposition_prop n)
    (h_reverse : sondow_reverse_criterion) :
    is_rational euler_mascheroni ↔
      ∀ᶠ n in atTop, sondow_identity_explicit_prop n := by
  simpa [sondow_identity_explicit_eventual_iff_eventually] using
    sondow_explicit_rational_equivalence hlcm h_product_log h_decomp h_reverse

theorem sondow_explicit_rational_equivalence_eventually_of_standard_package
    (hstd : SondowStandardInputs) :
    is_rational euler_mascheroni ↔
      ∀ᶠ n in atTop, sondow_identity_explicit_prop n := by
  simpa [sondow_identity_explicit_eventual_iff_eventually] using
    sondow_explicit_rational_equivalence_of_standard_package hstd
