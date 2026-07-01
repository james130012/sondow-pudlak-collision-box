/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.SondowKernel
import EulerLimit.SondowIntegralBridge
import EulerLimit.SondowProductLog

/-!
# Sondow decomposition finite-algebra targets

This module starts the decomposition track with audited finite-algebra
building blocks. It intentionally does not assert the analytic integral
identity or the full decomposition theorem.
-/

namespace EulerLimit.SondowDecomposition

open BigOperators

open scoped Topology

noncomputable section

open EulerLimit.SondowKernel
open EulerLimit.SondowCoefficient
open EulerLimit.SondowIntegralBridge
open EulerLimit.SondowProductLog

/-- Diagonal binomial coefficient in the Sondow decomposition. -/
theorem diagonalChooseSquareSum (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), ((Nat.choose n i : ℝ) ^ 2) =
      (Nat.choose (2 * n) n : ℝ) := by
  exact_mod_cast Nat.sum_range_choose_sq n

/-- The alternating binomial sum vanishes for positive `n`. -/
theorem alternatingChooseSum_eq_zero {n : ℕ} (hn : n ≠ 0) :
    ∑ i ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ i * (Nat.choose n i : ℝ) = 0 := by
  have hZ := Int.alternating_sum_range_choose_of_ne (n := n) hn
  exact_mod_cast hZ

/-- The signed binomial coefficient used in the decomposition cancellation. -/
def alternatingBinomial (n i : ℕ) : ℝ :=
  (-1 : ℝ) ^ i * (Nat.choose n i : ℝ)

/--
Diagonal coefficient of the `log N` term after the kernel-moment expansion.
The signs disappear on the diagonal.
-/
def diagonalLogNCoefficient (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (alternatingBinomial n i) ^ 2

/--
Full square coefficient of the `log N` term before diagonal/off-diagonal
splitting.
-/
def fullSquareLogNCoefficient (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (n + 1), alternatingBinomial n i) ^ 2

/--
The off-diagonal `log N` coefficient in normalized square-defect form.
This certificate deliberately avoids a triangular-index choice; the later
adapter will identify it with the `2 * ∑_{i<j}` form.
-/
def offDiagonalLogNCoefficient (n : ℕ) : ℝ :=
  fullSquareLogNCoefficient n - diagonalLogNCoefficient n

theorem alternatingBinomial_sq (n i : ℕ) :
    (alternatingBinomial n i) ^ 2 = ((Nat.choose n i : ℝ) ^ 2) := by
  unfold alternatingBinomial
  rw [mul_pow]
  have hsign : ((-1 : ℝ) ^ i) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  rw [hsign]
  ring

/-- The diagonal `log N` coefficient is the central binomial coefficient. -/
theorem diagonalLogNCoefficient_eq_choose (n : ℕ) :
    diagonalLogNCoefficient n = (Nat.choose (2 * n) n : ℝ) := by
  unfold diagonalLogNCoefficient
  calc
    ∑ i ∈ Finset.range (n + 1), (alternatingBinomial n i) ^ 2
        = ∑ i ∈ Finset.range (n + 1), ((Nat.choose n i : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [alternatingBinomial_sq]
    _ = (Nat.choose (2 * n) n : ℝ) := diagonalChooseSquareSum n

/-- For positive `n`, the full signed square coefficient is zero. -/
theorem fullSquareLogNCoefficient_eq_zero {n : ℕ} (hn : n ≠ 0) :
    fullSquareLogNCoefficient n = 0 := by
  unfold fullSquareLogNCoefficient alternatingBinomial
  rw [alternatingChooseSum_eq_zero hn]
  norm_num

/--
The off-diagonal `log N` coefficient cancels the diagonal coefficient. This is
the finite-algebra core of the decomposition limit: the divergent `log N` part
is killed by an exact signed-binomial identity, not by an asymptotic shortcut.
-/
theorem offDiagonalLogNCoefficient_eq_neg_choose {n : ℕ} (hn : n ≠ 0) :
    offDiagonalLogNCoefficient n = - (Nat.choose (2 * n) n : ℝ) := by
  unfold offDiagonalLogNCoefficient
  rw [fullSquareLogNCoefficient_eq_zero hn]
  rw [diagonalLogNCoefficient_eq_choose]
  ring

/-- Upper-triangular pair sum `∑_{i<j} f_i f_j` over `range m`. -/
def upperPairSum (m : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range m,
    ∑ j ∈ (Finset.range m).filter (fun j => i < j), f i * f j

theorem upperPairSum_succ (m : ℕ) (f : ℕ → ℝ) :
    upperPairSum (m + 1) f =
      upperPairSum m f + ∑ i ∈ Finset.range m, f i * f m := by
  unfold upperPairSum
  rw [Finset.sum_range_succ]
  have hlast :
      (∑ j ∈ (Finset.range (m + 1)).filter (fun j => m < j), f m * f j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hjrange := Finset.mem_range.mp hj'.1
    omega
  rw [hlast, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have him : i < m := Finset.mem_range.mp hi
  have hinner :
      (∑ j ∈ (Finset.range (m + 1)).filter (fun j => i < j), f i * f j) =
        (∑ j ∈ (Finset.range m).filter (fun j => i < j), f i * f j) +
          f i * f m := by
    rw [Finset.range_add_one]
    rw [Finset.filter_insert]
    simp [him, add_comm]
  rw [hinner]

theorem sum_sq_eq_diag_add_two_upper (m : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range m, f i) ^ 2 =
      (∑ i ∈ Finset.range m, (f i) ^ 2) + 2 * upperPairSum m f := by
  induction m with
  | zero =>
      simp [upperPairSum]
  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [upperPairSum_succ]
      have hT :
          (∑ i ∈ Finset.range m, f i * f m) =
            (∑ i ∈ Finset.range m, f i) * f m := by
        rw [Finset.sum_mul]
      rw [hT]
      nlinarith [ih]

/--
The off-diagonal `log N` coefficient in the original triangular form
`2 * ∑_{i<j}`.
-/
def triangularLogNCoefficient (n : ℕ) : ℝ :=
  2 * upperPairSum (n + 1) (alternatingBinomial n)

theorem fullSquareLogNCoefficient_eq_diagonal_add_triangular (n : ℕ) :
    fullSquareLogNCoefficient n =
      diagonalLogNCoefficient n + triangularLogNCoefficient n := by
  unfold fullSquareLogNCoefficient diagonalLogNCoefficient triangularLogNCoefficient
  exact sum_sq_eq_diag_add_two_upper (n + 1) (alternatingBinomial n)

theorem triangularLogNCoefficient_eq_offDiagonalLogNCoefficient (n : ℕ) :
    triangularLogNCoefficient n = offDiagonalLogNCoefficient n := by
  have h := fullSquareLogNCoefficient_eq_diagonal_add_triangular n
  unfold offDiagonalLogNCoefficient
  nlinarith

/--
Original-form off-diagonal cancellation: for positive `n`, the triangular
coefficient `2 * ∑_{i<j}` is exactly `-choose(2n,n)`.
-/
theorem triangularLogNCoefficient_eq_neg_choose {n : ℕ} (hn : n ≠ 0) :
    triangularLogNCoefficient n = - (Nat.choose (2 * n) n : ℝ) := by
  rw [triangularLogNCoefficient_eq_offDiagonalLogNCoefficient]
  exact offDiagonalLogNCoefficient_eq_neg_choose hn

/--
The exact cancellation of the divergent `log N` coefficient in the Sondow
decomposition finite algebra.
-/
theorem decompositionLogNCoefficient_cancel {n : ℕ} (hn : n ≠ 0) :
    diagonalLogNCoefficient n + triangularLogNCoefficient n = 0 := by
  rw [diagonalLogNCoefficient_eq_choose]
  rw [triangularLogNCoefficient_eq_neg_choose hn]
  ring

/-- Signed-binomial expansion of `(1 - x)^n` in the decomposition normalization. -/
theorem one_sub_pow_eq_alternating_sum (n : ℕ) (x : ℝ) :
    (1 - x) ^ n =
      ∑ i ∈ Finset.range (n + 1), alternatingBinomial n i * x ^ i := by
  have h := add_pow (-x) 1 n
  have h' : (1 - x) ^ n =
      ∑ i ∈ Finset.range (n + 1),
        (-x) ^ i * 1 ^ (n - i) * (Nat.choose n i : ℝ) := by
    simpa [sub_eq_add_neg, add_comm] using h
  rw [h']
  apply Finset.sum_congr rfl
  intro i _hi
  unfold alternatingBinomial
  rw [neg_eq_neg_one_mul, mul_pow]
  ring

/--
Weighted one-variable expansion used before inserting the kernel moments.
The index is already shifted to the moment exponent `n + i`.
-/
theorem pow_mul_one_sub_pow_eq_weighted_sum (n : ℕ) (x : ℝ) :
    x ^ n * (1 - x) ^ n =
      ∑ i ∈ Finset.range (n + 1), alternatingBinomial n i * x ^ (n + i) := by
  rw [one_sub_pow_eq_alternating_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [pow_add]
  ring

/--
Finite numerator expansion for the two-variable Sondow kernel integrand.
This closes the purely polynomial part of the finite-expansion layer; the
denominator/geometric-series adapter is closed by the lemmas below.
-/
theorem numeratorExpansion (n : ℕ) (x y : ℝ) :
    x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          alternatingBinomial n i * alternatingBinomial n j * x ^ (n + i) * y ^ (n + j) := by
  rw [pow_mul_one_sub_pow_eq_weighted_sum n x]
  rw [mul_assoc]
  rw [pow_mul_one_sub_pow_eq_weighted_sum n y]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/--
Division form of the finite geometric-series certificate. This is the algebraic
adapter for replacing the truncated denominator factor by a finite sum away
from the pole.
-/
theorem one_sub_pow_div_one_sub_eq_geometric_sum
    (N : ℕ) {z : ℝ} (hz : 1 - z ≠ 0) :
    (1 - z ^ N) / (1 - z) = ∑ q ∈ Finset.range N, z ^ q := by
  have hgeom : (∑ q ∈ Finset.range N, z ^ q) * (1 - z) = 1 - z ^ N := by
    exact geom_sum_mul_neg z N
  rw [← hgeom]
  field_simp [hz]

/-- The same finite geometric-series certificate in the `xy` denominator shape. -/
theorem one_sub_xy_pow_div_one_sub_xy_eq_geometric_sum
    (N : ℕ) {x y : ℝ} (hxy : 1 - x * y ≠ 0) :
    (1 - (x * y) ^ N) / (1 - x * y) =
      ∑ q ∈ Finset.range N, (x * y) ^ q := by
  exact one_sub_pow_div_one_sub_eq_geometric_sum N hxy

/--
Finite expansion of the numerator times the truncated geometric denominator
adapter. This is the polynomial input shape for the truncated kernel moments.
-/
theorem numerator_mul_geometric_sum_expansion (n N : ℕ) (x y : ℝ) :
    (x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n) *
        (∑ q ∈ Finset.range N, (x * y) ^ q) =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          ∑ q ∈ Finset.range N,
            alternatingBinomial n i * alternatingBinomial n j *
              x ^ (n + i + q) * y ^ (n + j + q) := by
  rw [numeratorExpansion]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [mul_pow]
  rw [pow_add, pow_add]
  ring

/--
Finite expansion after replacing the truncated denominator factor by its
geometric-series certificate.
-/
theorem numerator_mul_truncated_denominator_expansion
    (n N : ℕ) {x y : ℝ} (hxy : 1 - x * y ≠ 0) :
    (x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n) *
        ((1 - (x * y) ^ N) / (1 - x * y)) =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          ∑ q ∈ Finset.range N,
            alternatingBinomial n i * alternatingBinomial n j *
              x ^ (n + i + q) * y ^ (n + j + q) := by
  rw [one_sub_xy_pow_div_one_sub_xy_eq_geometric_sum N hxy]
  exact numerator_mul_geometric_sum_expansion n N x y

/--
Same adapter with the full truncated numerator-over-denominator shape on the
left. This is the closest purely algebraic bridge to the original integrand.
-/
theorem numerator_times_one_sub_pow_div_denominator_expansion
    (n N : ℕ) {x y : ℝ} (hxy : 1 - x * y ≠ 0) :
    (x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n * (1 - (x * y) ^ N)) /
        (1 - x * y) =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          ∑ q ∈ Finset.range N,
            alternatingBinomial n i * alternatingBinomial n j *
              x ^ (n + i + q) * y ^ (n + j + q) := by
  have hshape :
      (x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n * (1 - (x * y) ^ N)) /
          (1 - x * y) =
        (x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n) *
          ((1 - (x * y) ^ N) / (1 - x * y)) := by
    field_simp [hxy]
  rw [hshape]
  exact numerator_mul_truncated_denominator_expansion n N hxy

/--
The monomial shape that feeds the `k = 1, ..., N` truncated kernel moment.
The exponent `a + k - 1` matches the integral denominator `a + k + t` after
the Laplace-kernel step.
-/
def kernelMomentMonomial (a b k : ℕ) (x y : ℝ) : ℝ :=
  x ^ (a + k - 1) * y ^ (b + k - 1)

theorem kernelMomentMonomial_succ (a b q : ℕ) (x y : ℝ) :
    kernelMomentMonomial a b (q + 1) x y = x ^ (a + q) * y ^ (b + q) := by
  unfold kernelMomentMonomial
  rw [show a + (q + 1) - 1 = a + q by omega]
  rw [show b + (q + 1) - 1 = b + q by omega]

/--
Reindex the geometric `q = 0, ..., N-1` monomial sum as the kernel-moment
index `k = 1, ..., N`.
-/
theorem range_monomial_sum_eq_kernel_index_sum
    (n N i j : ℕ) (x y : ℝ) :
    (∑ q ∈ Finset.range N,
      alternatingBinomial n i * alternatingBinomial n j *
        x ^ (n + i + q) * y ^ (n + j + q)) =
      ∑ k ∈ Finset.Icc 1 N,
        alternatingBinomial n i * alternatingBinomial n j *
          kernelMomentMonomial (n + i) (n + j) k x y := by
  rw [sum_Icc_one_eq_sum_range_succ]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [kernelMomentMonomial_succ]
  ring

/--
The full finite expansion in the kernel-moment `k = 1, ..., N` index.
This is still purely algebraic; the analytic integral/Laplace bridge is the
next separate target.
-/
theorem monomial_triple_sum_eq_kernel_index_triple_sum
    (n N : ℕ) (x y : ℝ) :
    (∑ i ∈ Finset.range (n + 1),
      ∑ j ∈ Finset.range (n + 1),
        ∑ q ∈ Finset.range N,
          alternatingBinomial n i * alternatingBinomial n j *
            x ^ (n + i + q) * y ^ (n + j + q)) =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.Icc 1 N,
            alternatingBinomial n i * alternatingBinomial n j *
              kernelMomentMonomial (n + i) (n + j) k x y := by
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  exact range_monomial_sum_eq_kernel_index_sum n N i j x y

/--
The original truncated denominator algebra, now in the same `k = 1, ..., N`
index used by the truncated kernel-moment certificate.
-/
theorem truncated_denominator_expansion_kernel_index
    (n N : ℕ) {x y : ℝ} (hxy : 1 - x * y ≠ 0) :
    (x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n * (1 - (x * y) ^ N)) /
        (1 - x * y) =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.Icc 1 N,
            alternatingBinomial n i * alternatingBinomial n j *
              kernelMomentMonomial (n + i) (n + j) k x y := by
  rw [numerator_times_one_sub_pow_div_denominator_expansion n N hxy]
  exact monomial_triple_sum_eq_kernel_index_triple_sum n N x y

/--
Kernel monomial divided by the logarithmic factor from the original Sondow
integrand. This is the pointwise object whose double integral later becomes
`laplaceMoment`.
-/
def logKernelMonomial (a b k : ℕ) (x y : ℝ) : ℝ :=
  kernelMomentMonomial a b k x y / (-Real.log (x * y))

theorem kernelMomentMonomial_nonneg
    (a b k : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ kernelMomentMonomial a b k x y := by
  unfold kernelMomentMonomial
  positivity

theorem kernelMomentMonomial_mul_rpow_nonneg
    (a b k : ℕ) {t x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ kernelMomentMonomial a b k x y * (x * y) ^ t := by
  have hmono := kernelMomentMonomial_nonneg a b k hx hy
  have hrpow : 0 ≤ (x * y) ^ t := Real.rpow_nonneg (mul_nonneg hx hy) t
  exact mul_nonneg hmono hrpow

theorem continuous_kernelMomentMonomial (a b k : ℕ) :
    Continuous (fun p : ℝ × ℝ => kernelMomentMonomial a b k p.1 p.2) := by
  unfold kernelMomentMonomial
  continuity

theorem continuous_kernelMomentMonomial_mul_rpow
    (a b k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Continuous
      (fun p : ℝ × ℝ =>
        kernelMomentMonomial a b k p.1 p.2 * (p.1 * p.2) ^ t) := by
  have hmono :
      Continuous (fun p : ℝ × ℝ => kernelMomentMonomial a b k p.1 p.2) :=
    continuous_kernelMomentMonomial a b k
  have hbase : Continuous (fun p : ℝ × ℝ => p.1 * p.2) :=
    continuous_fst.mul continuous_snd
  have hrpow : Continuous (fun p : ℝ × ℝ => (p.1 * p.2) ^ t) :=
    (Real.continuous_rpow_const ht).comp hbase
  exact hmono.mul hrpow

theorem aestronglyMeasurable_kernelMomentMonomial_mul_rpow
    (a b k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        kernelMomentMonomial a b k p.1 p.2 * (p.1 * p.2) ^ t)
      (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (ℝ × ℝ)) :=
  (continuous_kernelMomentMonomial_mul_rpow a b k ht).aestronglyMeasurable

theorem logKernelMonomial_nonneg
    (a b k : ℕ) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    0 ≤ logKernelMonomial a b k x y := by
  unfold logKernelMonomial
  have hnum : 0 ≤ kernelMomentMonomial a b k x y :=
    kernelMomentMonomial_nonneg a b k hx0.le hy0.le
  rcases mul_mem_open_unit hx0 hx1 hy0 hy1 with ⟨hxy0, hxy1⟩
  have hlog_neg : Real.log (x * y) < 0 := (Real.log_neg_iff hxy0).2 hxy1
  have hden_pos : 0 < -Real.log (x * y) := by linarith
  exact div_nonneg hnum hden_pos.le

/-- One-dimensional endpoint majorant used for the log-kernel integrability proof. -/
def endpointSqrtBound (m : ℕ) (x : ℝ) : ℝ :=
  x ^ m * (1 - x) ^ (-(1 / 2 : ℝ))

theorem endpointSqrtBound_integrableOn_Ioo (m : ℕ) :
    MeasureTheory.IntegrableOn (endpointSqrtBound m) (Set.Ioo (0 : ℝ) 1) := by
  have hs : -1 < (-(1 / 2 : ℝ)) := by norm_num
  have hsing :
      IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegral.intervalIntegrable_rpow' hs
  have hbaseInterval :
      IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-(1 / 2 : ℝ)))
        MeasureTheory.volume (0 : ℝ) 1 := by
    simpa using (hsing.comp_sub_left (1 : ℝ)).symm
  have hbase :
      MeasureTheory.IntegrableOn
        (fun x : ℝ => (1 - x) ^ (-(1 / 2 : ℝ)))
        (Set.Ioo (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact hbaseInterval
  rw [MeasureTheory.IntegrableOn] at hbase ⊢
  refine MeasureTheory.Integrable.mono' hbase ?_ ?_
  · unfold endpointSqrtBound
    measurability
  · have hmem : ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1),
        x ∈ Set.Ioo (0 : ℝ) 1 := by
      exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
    filter_upwards [hmem] with x hx
    have hx0 : 0 ≤ x := le_of_lt hx.1
    have hx1 : x ≤ 1 := le_of_lt hx.2
    have hpow_nonneg : 0 ≤ x ^ m := pow_nonneg hx0 m
    have hpow_le_one : x ^ m ≤ 1 := pow_le_one₀ hx0 hx1
    have hbase_nonneg : 0 ≤ (1 - x) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (by linarith : 0 ≤ 1 - x) _
    unfold endpointSqrtBound
    rw [Real.norm_of_nonneg (mul_nonneg hpow_nonneg hbase_nonneg)]
    exact mul_le_of_le_one_left hbase_nonneg hpow_le_one

/-- Two-dimensional product majorant for a single logarithmic kernel monomial. -/
def logKernelDominatingProduct (a b k : ℕ) (p : ℝ × ℝ) : ℝ :=
  endpointSqrtBound (a + k - 1) p.1 * endpointSqrtBound (b + k - 1) p.2

theorem logKernelDominatingProduct_integrableOn_openSquare (a b k : ℕ) :
    MeasureTheory.IntegrableOn (logKernelDominatingProduct a b k)
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
  have hx := endpointSqrtBound_integrableOn_Ioo (a + k - 1)
  have hy := endpointSqrtBound_integrableOn_Ioo (b + k - 1)
  rw [MeasureTheory.IntegrableOn] at hx hy ⊢
  unfold logKernelDominatingProduct
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [← MeasureTheory.Measure.prod_restrict]
  exact hx.mul_prod hy

theorem sqrt_one_sub_mul_le_neg_log_mul
    {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    Real.sqrt ((1 - x) * (1 - y)) ≤ -Real.log (x * y) := by
  have hux : 0 ≤ 1 - x := by linarith
  have huy : 0 ≤ 1 - y := by linarith
  have hsum_nonneg : 0 ≤ (1 - x) + (1 - y) := add_nonneg hux huy
  have hsqrt_le_sum :
      Real.sqrt ((1 - x) * (1 - y)) ≤ (1 - x) + (1 - y) := by
    rw [Real.sqrt_le_left hsum_nonneg]
    nlinarith [mul_nonneg hux huy, sq_nonneg (1 - x), sq_nonneg (1 - y)]
  have hlog_mul : Real.log (x * y) = Real.log x + Real.log y :=
    Real.log_mul (ne_of_gt hx0) (ne_of_gt hy0)
  have hxlog : 1 - x ≤ -Real.log x := by
    have h := Real.log_le_sub_one_of_pos hx0
    linarith
  have hylog : 1 - y ≤ -Real.log y := by
    have h := Real.log_le_sub_one_of_pos hy0
    linarith
  have hsum_le_log : (1 - x) + (1 - y) ≤ -Real.log (x * y) := by
    rw [hlog_mul]
    linarith
  exact hsqrt_le_sum.trans hsum_le_log

theorem one_div_neg_log_mul_le_endpoint_rpow
    {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    1 / (-Real.log (x * y)) ≤
      (1 - x) ^ (-(1 / 2 : ℝ)) * (1 - y) ^ (-(1 / 2 : ℝ)) := by
  have hux_pos : 0 < 1 - x := by linarith
  have huy_pos : 0 < 1 - y := by linarith
  have hsqrt_le_log := sqrt_one_sub_mul_le_neg_log_mul hx0 hx1 hy0 hy1
  have hsqrt_eq :
      Real.sqrt ((1 - x) * (1 - y)) =
        (1 - x) ^ (1 / 2 : ℝ) * (1 - y) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul hux_pos.le (1 - y)]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hprod_pos :
      0 < (1 - x) ^ (1 / 2 : ℝ) * (1 - y) ^ (1 / 2 : ℝ) := by
    exact mul_pos (Real.rpow_pos_of_pos hux_pos _) (Real.rpow_pos_of_pos huy_pos _)
  have hprod_le_log :
      (1 - x) ^ (1 / 2 : ℝ) * (1 - y) ^ (1 / 2 : ℝ) ≤
        -Real.log (x * y) := by
    simpa [hsqrt_eq] using hsqrt_le_log
  have hrecip := one_div_le_one_div_of_le hprod_pos hprod_le_log
  have hprod_inv :
      1 / ((1 - x) ^ (1 / 2 : ℝ) * (1 - y) ^ (1 / 2 : ℝ)) =
        (1 - x) ^ (-(1 / 2 : ℝ)) * (1 - y) ^ (-(1 / 2 : ℝ)) := by
    rw [one_div, mul_inv_rev]
    rw [Real.rpow_neg hux_pos.le, Real.rpow_neg huy_pos.le]
    ring
  calc
    1 / (-Real.log (x * y))
        ≤ 1 / ((1 - x) ^ (1 / 2 : ℝ) * (1 - y) ^ (1 / 2 : ℝ)) := hrecip
    _ = (1 - x) ^ (-(1 / 2 : ℝ)) * (1 - y) ^ (-(1 / 2 : ℝ)) := hprod_inv

theorem logKernelMonomial_le_dominatingProduct
    (a b k : ℕ) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    logKernelMonomial a b k x y ≤ logKernelDominatingProduct a b k (x, y) := by
  have hmono_nonneg : 0 ≤ kernelMomentMonomial a b k x y :=
    kernelMomentMonomial_nonneg a b k hx0.le hy0.le
  have hinv := one_div_neg_log_mul_le_endpoint_rpow hx0 hx1 hy0 hy1
  unfold logKernelMonomial
  calc
    kernelMomentMonomial a b k x y / (-Real.log (x * y))
        = kernelMomentMonomial a b k x y * (1 / (-Real.log (x * y))) := by
          ring
    _ ≤ kernelMomentMonomial a b k x y *
          ((1 - x) ^ (-(1 / 2 : ℝ)) * (1 - y) ^ (-(1 / 2 : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hinv hmono_nonneg
    _ = logKernelDominatingProduct a b k (x, y) := by
          unfold logKernelDominatingProduct endpointSqrtBound kernelMomentMonomial
          ring

theorem logKernelMonomial_integrableOn_openSquare (a b k : ℕ) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => logKernelMonomial a b k p.1 p.2)
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
  have hdom := logKernelDominatingProduct_integrableOn_openSquare a b k
  rw [MeasureTheory.IntegrableOn] at hdom ⊢
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · have hnum :
        Measurable (fun p : ℝ × ℝ => kernelMomentMonomial a b k p.1 p.2) :=
      (continuous_kernelMomentMonomial a b k).measurable
    have hprod : Measurable (fun p : ℝ × ℝ => p.1 * p.2) :=
      measurable_fst.mul measurable_snd
    have hden : Measurable (fun p : ℝ × ℝ => -Real.log (p.1 * p.2)) :=
      (Real.measurable_log.comp hprod).neg
    exact (hnum.div hden).aestronglyMeasurable
  · have hmem :
        ∀ᵐ p ∂MeasureTheory.volume.restrict
          (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1),
          p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 := by
      exact MeasureTheory.ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
    filter_upwards [hmem] with p hp
    rcases hp with ⟨hx, hy⟩
    have hnonneg := logKernelMonomial_nonneg a b k hx.1 hx.2 hy.1 hy.2
    have hle := logKernelMonomial_le_dominatingProduct a b k hx.1 hx.2 hy.1 hy.2
    simpa [Real.norm_of_nonneg hnonneg] using hle

theorem nat_shift_cast_sub_one (a k : ℕ) (hk : 1 ≤ k) :
    ((a + k - 1 : ℕ) : ℝ) = ((a + k : ℕ) : ℝ) - 1 := by
  have hle : 1 ≤ a + k := by omega
  rw [Nat.cast_sub hle]
  norm_num

/--
On the open unit square, the Laplace kernel monomial separates into an
`x`-factor and a `y`-factor. Endpoints are handled later by a.e. interval
congruence.
-/
theorem kernelMomentMonomial_mul_rpow_eq_shifted_rpow
    (a b k : ℕ) {t x y : ℝ} (hk : 1 ≤ k) (hx : 0 < x) (hy : 0 < y) :
    kernelMomentMonomial a b k x y * (x * y) ^ t =
      x ^ (((a + k : ℕ) : ℝ) + t - 1) *
        y ^ (((b + k : ℕ) : ℝ) + t - 1) := by
  unfold kernelMomentMonomial
  rw [Real.mul_rpow hx.le hy.le]
  calc
    x ^ (a + k - 1) * y ^ (b + k - 1) * (x ^ t * y ^ t)
        = (x ^ (a + k - 1) * x ^ t) * (y ^ (b + k - 1) * y ^ t) := by
          ring
    _ = x ^ (((a + k : ℕ) : ℝ) + t - 1) *
        y ^ (((b + k : ℕ) : ℝ) + t - 1) := by
          have hxpow :
              x ^ (a + k - 1) * x ^ t =
                x ^ (((a + k : ℕ) : ℝ) + t - 1) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_add hx]
            congr 1
            rw [nat_shift_cast_sub_one a k hk]
            ring
          have hypow :
              y ^ (b + k - 1) * y ^ t =
                y ^ (((b + k : ℕ) : ℝ) + t - 1) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_add hy]
            congr 1
            rw [nat_shift_cast_sub_one b k hk]
            ring
          rw [hxpow, hypow]

/--
For fixed `t ≥ 0` and `x ∈ (0,1]`, the inner `y`-integral of the separated
kernel monomial is the expected reciprocal factor.
-/
theorem inner_kernelMomentMonomial_mul_rpow_integral
    (a b k : ℕ) {t x : ℝ} (hk : 1 ≤ k) (ht : 0 ≤ t) (hx : 0 < x) :
    (∫ y in (0 : ℝ)..1, kernelMomentMonomial a b k x y * (x * y) ^ t) =
      x ^ (((a + k : ℕ) : ℝ) + t - 1) *
        (((b + k : ℕ) : ℝ) + t)⁻¹ := by
  have hcongr :
      (∫ y in (0 : ℝ)..1, kernelMomentMonomial a b k x y * (x * y) ^ t) =
        ∫ y in (0 : ℝ)..1,
          x ^ (((a + k : ℕ) : ℝ) + t - 1) *
            y ^ (((b + k : ℕ) : ℝ) + t - 1) := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun y hy => by
      have hyIoc : y ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using hy
      rw [kernelMomentMonomial_mul_rpow_eq_shifted_rpow a b k hk hx hyIoc.1])
  rw [hcongr]
  rw [unit_interval_nat_shift_rpow_integral_const_mul b k hk ht]

/--
For fixed `t ≥ 0`, the iterated `x/y` integral of the Laplace kernel monomial
is exactly the integrand defining `laplaceMoment`.
-/
theorem iterated_kernelMomentMonomial_mul_rpow_integral
    (a b k : ℕ) {t : ℝ} (hk : 1 ≤ k) (ht : 0 ≤ t) :
    (∫ x in (0 : ℝ)..1,
      ∫ y in (0 : ℝ)..1, kernelMomentMonomial a b k x y * (x * y) ^ t) =
      (((a + k : ℕ) : ℝ) + t)⁻¹ *
        (((b + k : ℕ) : ℝ) + t)⁻¹ := by
  have hcongr :
      (∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1, kernelMomentMonomial a b k x y * (x * y) ^ t) =
        ∫ x in (0 : ℝ)..1,
          x ^ (((a + k : ℕ) : ℝ) + t - 1) *
            (((b + k : ℕ) : ℝ) + t)⁻¹ := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun x hxmem => by
      have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le zero_le_one] using hxmem
      rw [inner_kernelMomentMonomial_mul_rpow_integral a b k hk ht hxIoc.1])
  rw [hcongr]
  rw [unit_interval_nat_shift_rpow_integral_mul_const a k hk ht]

/--
The logarithmic kernel monomial is a monomial times the Laplace kernel
`∫_0^∞ (xy)^t dt` on the open unit square.
-/
theorem logKernelMonomial_eq_mul_laplace_integral (a b k : ℕ) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    logKernelMonomial a b k x y =
      kernelMomentMonomial a b k x y *
        (∫ t : ℝ in Set.Ioi (0 : ℝ), (x * y) ^ t) := by
  unfold logKernelMonomial
  rcases mul_mem_open_unit hx0 hx1 hy0 hy1 with ⟨hxy0, hxy1⟩
  have hlog_neg : Real.log (x * y) < 0 := (Real.log_neg_iff hxy0).2 hxy1
  have hlog_ne : Real.log (x * y) ≠ 0 := ne_of_lt hlog_neg
  rw [laplace_rpow_integral hxy0 hxy1]
  field_simp [hlog_ne]

/--
Integral-valued form of `logKernelMonomial_eq_mul_laplace_integral`. This is
the local statement needed before Fubini/Tonelli and the unit-interval monomial
integrals are applied.
-/
theorem logKernelMonomial_eq_laplace_integral (a b k : ℕ) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    logKernelMonomial a b k x y =
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
        kernelMomentMonomial a b k x y * (x * y) ^ t := by
  rw [logKernelMonomial_eq_mul_laplace_integral a b k hx0 hx1 hy0 hy1]
  rw [MeasureTheory.integral_const_mul]

theorem integrableOn_const_rpow_Ioi {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    MeasureTheory.IntegrableOn (fun t : ℝ => z ^ t) (Set.Ioi (0 : ℝ)) := by
  have hlog_neg : Real.log z < 0 := (Real.log_neg_iff hz0).2 hz1
  have h := integrableOn_exp_mul_Ioi (a := Real.log z) hlog_neg (0 : ℝ)
  refine h.congr_fun (fun t _ht => ?_)
    (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))
  exact (Real.rpow_def_of_pos hz0 t).symm

/--
The truncated denominator expansion after inserting the logarithmic kernel.
This is still pointwise algebra; the following analytic layer will integrate
these monomial-log terms.
-/
theorem truncated_log_denominator_expansion_kernel_index
    (n N : ℕ) {x y : ℝ} (hxy : 1 - x * y ≠ 0) :
    ((x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n * (1 - (x * y) ^ N)) /
        (1 - x * y)) / (-Real.log (x * y)) =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.Icc 1 N,
            alternatingBinomial n i * alternatingBinomial n j *
              logKernelMonomial (n + i) (n + j) k x y := by
  rw [truncated_denominator_expansion_kernel_index n N hxy]
  unfold logKernelMonomial
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/--
Pointwise split of the original Sondow logarithmic integrand into the truncated
kernel sum and an explicit remainder. This is the precise local bridge before
the remaining integration and remainder-limit certificates.
-/
theorem original_log_denominator_split_kernel_index
    (n N : ℕ) {x y : ℝ} (hxy : 1 - x * y ≠ 0)
    (hlog : Real.log (x * y) ≠ 0) :
    (x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n) /
        (-(1 - x * y) * Real.log (x * y)) =
      (∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.Icc 1 N,
            alternatingBinomial n i * alternatingBinomial n j *
              logKernelMonomial (n + i) (n + j) k x y) +
        ((x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n * (x * y) ^ N) /
          (1 - x * y)) / (-Real.log (x * y)) := by
  let P : ℝ := x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n
  let z : ℝ := x * y
  have hsplit : P / (-(1 - z) * Real.log z) =
      (P * (1 - z ^ N) / (1 - z)) / (-Real.log z) +
        (P * z ^ N / (1 - z)) / (-Real.log z) := by
    field_simp [hxy, hlog, z]
    ring
  change P / (-(1 - z) * Real.log z) = _
  rw [hsplit]
  rw [truncated_log_denominator_expansion_kernel_index n N hxy]

/--
The remaining analytic certificate for the kernel-moment route, after the
finite expansion has been reduced to the `k = 1, ..., N` monomial index.
The intended `moment a b k` is the analytic value attached to
`kernelMomentMonomial a b k`.
-/
def kernelMomentSumCertificate (moment : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ a b N : ℕ,
    ∑ k ∈ Finset.Icc 1 N, moment a b k = kernelMomentClosed a b N

theorem sum_range_sub_telescope (F : ℕ → ℝ) (N : ℕ) :
    (∑ r ∈ Finset.range N, (F (r + 1) - F r)) = F N - F 0 := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      ring

theorem sum_Icc_sub_telescope (F : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (F k - F (k - 1))) = F N - F 0 := by
  rw [sum_Icc_one_eq_sum_range_succ]
  simpa using sum_range_sub_telescope F N

theorem offDiagonalClosed_zero (m delta : ℕ) :
    offDiagonalClosed m delta 0 = 0 := by
  unfold offDiagonalClosed
  have hsum :
      (∑ r ∈ Finset.Icc 1 delta,
          Real.log (((0 + m + r : ℕ) : ℝ) / ((m + r : ℕ) : ℝ))) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hden_nat : 0 < m + r := by omega
    have hden : ((m + r : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hden_nat
    have hratio : (((0 + m + r : ℕ) : ℝ) / ((m + r : ℕ) : ℝ)) = 1 := by
      field_simp [hden]
      simp
    rw [hratio, Real.log_one]
  rw [hsum]
  simp

theorem kernelMomentClosed_zero (a b : ℕ) :
    kernelMomentClosed a b 0 = 0 := by
  unfold kernelMomentClosed diagonalClosed
  by_cases hab : a = b
  · simp [hab]
  · by_cases hlt : a < b
    · simp [hab, hlt, offDiagonalClosed_zero]
    · simp [hab, hlt, offDiagonalClosed_zero]

/--
The closed-form pointwise increment of the kernel moment. The analytic task can
be reduced to proving that the chosen integral moment equals this increment.
-/
def kernelMomentIncrement (a b k : ℕ) : ℝ :=
  kernelMomentClosed a b k - kernelMomentClosed a b (k - 1)

theorem kernelMomentIncrement_sum_certificate :
    kernelMomentSumCertificate kernelMomentIncrement := by
  intro a b N
  unfold kernelMomentIncrement
  rw [sum_Icc_sub_telescope]
  rw [kernelMomentClosed_zero]
  ring

/--
Pointwise analytic certificate: a moment functional agrees with the closed-form
increment at every positive kernel index.
-/
def kernelMomentPointwiseCertificate (moment : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ a b k : ℕ, 1 ≤ k → moment a b k = kernelMomentIncrement a b k

theorem kernelMomentSumCertificate_of_pointwise_increment
    {moment : ℕ → ℕ → ℕ → ℝ}
    (hpoint : kernelMomentPointwiseCertificate moment) :
    kernelMomentSumCertificate moment := by
  intro a b N
  calc
    ∑ k ∈ Finset.Icc 1 N, moment a b k
        = ∑ k ∈ Finset.Icc 1 N, kernelMomentIncrement a b k := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hpoint a b k (Finset.mem_Icc.mp hk).1
    _ = kernelMomentClosed a b N := kernelMomentIncrement_sum_certificate a b N

/--
Laplace-normalized analytic moment for the next proof layer. No theorem here
asserts its value; the remaining analytic target is the pointwise certificate
below.
-/
def laplaceMoment (a b k : ℕ) : ℝ :=
  ∫ t : ℝ in Set.Ioi (0 : ℝ),
    (((a + k : ℕ) : ℝ) + t)⁻¹ * (((b + k : ℕ) : ℝ) + t)⁻¹

/--
The original double-integral moment attached to a single logarithmic kernel
monomial.
-/
def logKernelMoment (a b k : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ∫ y in (0 : ℝ)..1, logKernelMonomial a b k x y

theorem logKernelMoment_intervalIntegral_eq_iterated_Ioo (a b k : ℕ) :
    logKernelMoment a b k =
      ∫ x : ℝ in Set.Ioo (0 : ℝ) 1,
        ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
          logKernelMonomial a b k x y := by
  unfold logKernelMoment
  have hinner :
      (fun x : ℝ =>
        ∫ y in (0 : ℝ)..1, logKernelMonomial a b k x y) =
        fun x : ℝ =>
          ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
            logKernelMonomial a b k x y := by
    funext x
    rw [intervalIntegral.integral_of_le zero_le_one]
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hinner]
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem kernelMomentMonomial_mul_rpow_intervalIntegral_eq_iterated_Ioo
    (a b k : ℕ) (t : ℝ) :
    (∫ x in (0 : ℝ)..1,
      ∫ y in (0 : ℝ)..1,
        kernelMomentMonomial a b k x y * (x * y) ^ t) =
      ∫ x : ℝ in Set.Ioo (0 : ℝ) 1,
        ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
          kernelMomentMonomial a b k x y * (x * y) ^ t := by
  have hinner :
      (fun x : ℝ =>
        ∫ y in (0 : ℝ)..1,
          kernelMomentMonomial a b k x y * (x * y) ^ t) =
        fun x : ℝ =>
          ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
            kernelMomentMonomial a b k x y * (x * y) ^ t := by
    funext x
    rw [intervalIntegral.integral_of_le zero_le_one]
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hinner]
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]

/--
The precise remaining Fubini/Tonelli certificate for replacing the original
double integral by the Laplace-parameter integral. This keeps the remaining
analytic exchange step named and auditable.
-/
def logKernelFubiniCertificate (a b k : ℕ) : Prop :=
  logKernelMoment a b k =
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
      (∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1,
          kernelMomentMonomial a b k x y * (x * y) ^ t)

/--
Once the Fubini/Tonelli exchange is supplied, the original log-kernel moment is
exactly the already closed Laplace moment.
-/
theorem logKernelMoment_eq_laplaceMoment_of_fubiniCertificate
    (a b k : ℕ) (hk : 1 ≤ k)
    (hF : logKernelFubiniCertificate a b k) :
    logKernelMoment a b k = laplaceMoment a b k := by
  rw [hF]
  unfold laplaceMoment
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact iterated_kernelMomentMonomial_mul_rpow_integral a b k hk
    (le_of_lt (Set.mem_Ioi.mp ht))

/-- Remaining pointwise analytic target for the Laplace route. -/
def laplaceMomentPointwiseTarget : Prop :=
  kernelMomentPointwiseCertificate laplaceMoment

theorem kernelMomentSumCertificate_of_laplaceMomentPointwise
    (h : laplaceMomentPointwiseTarget) :
    kernelMomentSumCertificate laplaceMoment :=
  kernelMomentSumCertificate_of_pointwise_increment h

/-- Sondow's finite expansion after replacing monomials by a moment functional. -/
def kernelIndexedMomentExpansion
    (n N : ℕ) (moment : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ∑ j ∈ Finset.range (n + 1),
      ∑ k ∈ Finset.Icc 1 N,
        alternatingBinomial n i * alternatingBinomial n j * moment (n + i) (n + j) k

/-- The closed kernel-moment expansion used before the diagonal/off-diagonal split. -/
def closedKernelMomentExpansion (n N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ∑ j ∈ Finset.range (n + 1),
      alternatingBinomial n i * alternatingBinomial n j * kernelMomentClosed (n + i) (n + j) N

/--
Once the analytic moment certificate is supplied, the whole finite Sondow
expansion reduces to the closed kernel-moment expansion by finite linearity.
-/
theorem kernelIndexedMomentExpansion_eq_closed_of_certificate
    {moment : ℕ → ℕ → ℕ → ℝ}
    (hcert : kernelMomentSumCertificate moment) (n N : ℕ) :
    kernelIndexedMomentExpansion n N moment = closedKernelMomentExpansion n N := by
  unfold kernelIndexedMomentExpansion closedKernelMomentExpansion
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← Finset.mul_sum]
  rw [hcert]

theorem kernelMomentClosed_comm (a b N : ℕ) :
    kernelMomentClosed a b N = kernelMomentClosed b a N := by
  by_cases hab : a = b
  · subst b
    rfl
  · by_cases hlt : a < b
    · have hne : b ≠ a := by omega
      have hnot : ¬ b < a := by omega
      simp [kernelMomentClosed, hab, hlt, hne, hnot]
    · have hgt : b < a := by omega
      have hne : b ≠ a := by omega
      simp [kernelMomentClosed, hab, hlt, hne, hgt]

theorem kernelMomentClosed_diag (a N : ℕ) :
    kernelMomentClosed a a N = diagonalClosed a N := by
  simp [kernelMomentClosed]

theorem kernelMomentClosed_of_lt {a b N : ℕ} (hab : a < b) :
    kernelMomentClosed a b N = offDiagonalClosed a (b - a) N := by
  have hne : a ≠ b := by omega
  simp [kernelMomentClosed, hne, hab]

theorem kernelMomentClosed_of_gt {a b N : ℕ} (hba : b < a) :
    kernelMomentClosed a b N = offDiagonalClosed b (a - b) N := by
  have hne : a ≠ b := by omega
  have hnot : ¬ a < b := by omega
  simp [kernelMomentClosed, hne, hnot]

theorem harmonicReal_succ (n : ℕ) :
    harmonicReal (n + 1) = harmonicReal n + (((n + 1 : ℕ) : ℝ)⁻¹) := by
  unfold harmonicReal
  rw [Finset.sum_Icc_succ_top]
  omega

theorem harmonicReal_sub_prev {n : ℕ} (hn : 1 ≤ n) :
    harmonicReal n - harmonicReal (n - 1) = ((n : ℕ) : ℝ)⁻¹ := by
  have hsucc := harmonicReal_succ (n - 1)
  have hn_eq : n - 1 + 1 = n := by omega
  rw [hn_eq] at hsucc
  linarith

theorem kernelMomentIncrement_diag (a k : ℕ) (hk : 1 ≤ k) :
    kernelMomentIncrement a a k = (((a + k : ℕ) : ℝ)⁻¹) := by
  unfold kernelMomentIncrement
  rw [kernelMomentClosed_diag]
  rw [kernelMomentClosed_diag]
  unfold diagonalClosed
  have hprev : a + (k - 1) = a + k - 1 := by omega
  rw [hprev]
  have hdiff := harmonicReal_sub_prev (n := a + k) (by omega)
  linarith

theorem log_ratio_telescope (base d : ℕ) (hbase : 0 < base) :
    (∑ r ∈ Finset.Icc 1 d,
      Real.log (((base + r : ℕ) : ℝ) / ((base + r - 1 : ℕ) : ℝ))) =
      Real.log (((base + d : ℕ) : ℝ) / (base : ℝ)) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Finset.sum_Icc_succ_top]
      · rw [ih]
        have hb : (base : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hbase
        have hbd : ((base + d : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt (by omega : 0 < base + d)
        have hden_succ :
            ((base + (d + 1) - 1 : ℕ) : ℝ) = ((base + d : ℕ) : ℝ) := by
          exact_mod_cast (by omega : base + (d + 1) - 1 = base + d)
        rw [hden_succ]
        have hpos1 : 0 < (((base + d : ℕ) : ℝ) / (base : ℝ)) := by positivity
        have hpos2 :
            0 < (((base + (d + 1) : ℕ) : ℝ) / ((base + d : ℕ) : ℝ)) := by
          positivity
        rw [← Real.log_mul hpos1.ne' hpos2.ne']
        congr 1
        field_simp [hb, hbd]
      · omega

theorem offDiagonalClosed_increment (m delta k : ℕ) (hdelta : 0 < delta) (hk : 1 ≤ k) :
    offDiagonalClosed m delta k - offDiagonalClosed m delta (k - 1) =
      Real.log (((m + delta + k : ℕ) : ℝ) / ((m + k : ℕ) : ℝ)) / (delta : ℝ) := by
  have _hdelta_pos : 0 < delta := hdelta
  unfold offDiagonalClosed
  rw [← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ r ∈ Finset.Icc 1 delta,
        (Real.log (((k + m + r : ℕ) : ℝ) / ((m + r : ℕ) : ℝ)) -
          Real.log ((((k - 1) + m + r : ℕ) : ℝ) / ((m + r : ℕ) : ℝ))))
        = ∑ r ∈ Finset.Icc 1 delta,
            Real.log (((m + k + r : ℕ) : ℝ) / ((m + k + r - 1 : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
          have hAcast :
              ((k + m + r : ℕ) : ℝ) = ((m + k + r : ℕ) : ℝ) := by
            exact_mod_cast (by omega : k + m + r = m + k + r)
          have hBcast :
              (((k - 1) + m + r : ℕ) : ℝ) = ((m + k + r - 1 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : (k - 1) + m + r = m + k + r - 1)
          rw [hAcast, hBcast]
          have hA0 : ((m + k + r : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt (by omega : 0 < m + k + r)
          have hB0 : ((m + k + r - 1 : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt (by omega : 0 < m + k + r - 1)
          have hC0 : ((m + r : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt (by omega : 0 < m + r)
          rw [Real.log_div hA0 hC0, Real.log_div hB0 hC0, Real.log_div hA0 hB0]
          ring
    _ = Real.log (((m + k + delta : ℕ) : ℝ) / ((m + k : ℕ) : ℝ)) := by
          exact log_ratio_telescope (m + k) delta (by omega)
    _ = Real.log (((m + delta + k : ℕ) : ℝ) / ((m + k : ℕ) : ℝ)) := by
          have hnum :
              ((m + k + delta : ℕ) : ℝ) = ((m + delta + k : ℕ) : ℝ) := by
            exact_mod_cast (by omega : m + k + delta = m + delta + k)
          rw [hnum]

theorem kernelMomentIncrement_of_lt {a b k : ℕ} (hab : a < b) (hk : 1 ≤ k) :
    kernelMomentIncrement a b k =
      Real.log (((b + k : ℕ) : ℝ) / ((a + k : ℕ) : ℝ)) / ((b - a : ℕ) : ℝ) := by
  unfold kernelMomentIncrement
  rw [kernelMomentClosed_of_lt hab]
  rw [kernelMomentClosed_of_lt (N := k - 1) hab]
  have hdelta : 0 < b - a := by omega
  rw [offDiagonalClosed_increment a (b - a) k hdelta hk]
  have hnum : ((a + (b - a) + k : ℕ) : ℝ) = ((b + k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : a + (b - a) + k = b + k)
  rw [hnum]

theorem kernelMomentIncrement_of_gt {a b k : ℕ} (hba : b < a) (hk : 1 ≤ k) :
    kernelMomentIncrement a b k =
      Real.log (((a + k : ℕ) : ℝ) / ((b + k : ℕ) : ℝ)) / ((a - b : ℕ) : ℝ) := by
  unfold kernelMomentIncrement
  rw [kernelMomentClosed_of_gt hba]
  rw [kernelMomentClosed_of_gt (N := k - 1) hba]
  have hdelta : 0 < a - b := by omega
  rw [offDiagonalClosed_increment b (a - b) k hdelta hk]
  have hnum : ((b + (a - b) + k : ℕ) : ℝ) = ((a + k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : b + (a - b) + k = a + k)
  rw [hnum]

theorem kernelMomentIncrement_eq_closed_form (a b k : ℕ) (hk : 1 ≤ k) :
    kernelMomentIncrement a b k =
      if a = b then
        (((a + k : ℕ) : ℝ)⁻¹)
      else if a < b then
        Real.log (((b + k : ℕ) : ℝ) / ((a + k : ℕ) : ℝ)) / ((b - a : ℕ) : ℝ)
      else
        Real.log (((a + k : ℕ) : ℝ) / ((b + k : ℕ) : ℝ)) / ((a - b : ℕ) : ℝ) := by
  by_cases hab : a = b
  · subst b
    simp [kernelMomentIncrement_diag, hk]
  · by_cases hlt : a < b
    · simp [hab, hlt, kernelMomentIncrement_of_lt hlt hk]
    · have hgt : b < a := by omega
      simp [hab, hlt, kernelMomentIncrement_of_gt hgt hk]

theorem inv_mul_inv_eq_rpow_neg_two {x : ℝ} (hx : 0 < x) :
    x⁻¹ * x⁻¹ = x ^ (-2 : ℝ) := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num]
  rw [Real.rpow_neg hx.le]
  field_simp [hx.ne']
  norm_num [Real.rpow_natCast]

theorem diagonal_laplace_integral {A : ℝ} (hA : 0 < A) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), (A + t)⁻¹ * (A + t)⁻¹) = A⁻¹ := by
  let F : ℝ → ℝ := fun t => -((A + t)⁻¹)
  have hderiv :
      ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt F ((A + x)⁻¹ * (A + x)⁻¹) x := by
    intro x hx
    have hx0 : 0 ≤ x := Set.mem_Ici.mp hx
    have hpos : 0 < A + x := by linarith
    have hne : A + x ≠ 0 := hpos.ne'
    have hbase : HasDerivAt (fun y : ℝ => A + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add A
    have hneg := (hbase.inv hne).neg
    have hnegF : HasDerivAt F (-(-1 / (A + x) ^ 2)) x := by
      refine hneg.congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall (fun _ => by rfl)
    have hval : -(-1 / (A + x) ^ 2) = (A + x)⁻¹ * (A + x)⁻¹ := by
      field_simp [hne]
    exact hnegF.congr_deriv hval
  have hint_rpow :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => (t + A) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) := by
    exact integrableOn_add_rpow_Ioi_of_lt
      (a := (-2 : ℝ)) (c := 0) (m := A) (by norm_num) (by linarith)
  have hint :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => (A + t)⁻¹ * (A + t)⁻¹) (Set.Ioi (0 : ℝ)) := by
    refine hint_rpow.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have hpos : 0 < A + t := by linarith [hA, Set.mem_Ioi.mp ht]
    change (t + A) ^ (-2 : ℝ) = (A + t)⁻¹ * (A + t)⁻¹
    rw [add_comm t A]
    exact (inv_mul_inv_eq_rpow_neg_two hpos).symm
  have htend : Filter.Tendsto F Filter.atTop (𝓝 (0 : ℝ)) := by
    unfold F
    simpa using (tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_left Filter.atTop A Filter.tendsto_id)).neg
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := (0 : ℝ)) (m := (0 : ℝ)) hderiv hint htend
  simpa [F, sub_eq_add_neg] using h

theorem laplaceMoment_diag (a k : ℕ) (hk : 1 ≤ k) :
    laplaceMoment a a k = kernelMomentIncrement a a k := by
  unfold laplaceMoment
  have hA : 0 < ((a + k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < a + k)
  rw [diagonal_laplace_integral hA]
  rw [kernelMomentIncrement_diag a k hk]

theorem offdiag_laplace_integral {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), (A + t)⁻¹ * (B + t)⁻¹) =
      Real.log (B / A) / (B - A) := by
  let G : ℝ → ℝ := fun t => (Real.log (A + t) - Real.log (B + t)) / (B - A)
  have hdelta : B - A ≠ 0 := by linarith
  have hderiv :
      ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt G ((A + x)⁻¹ * (B + x)⁻¹) x := by
    intro x hx
    have hx0 : 0 ≤ x := Set.mem_Ici.mp hx
    have hApos : 0 < A + x := by linarith
    have hBpos : 0 < B + x := by linarith
    have hAne : A + x ≠ 0 := hApos.ne'
    have hBne : B + x ≠ 0 := hBpos.ne'
    have hAderiv : HasDerivAt (fun y : ℝ => Real.log (A + y)) ((A + x)⁻¹) x := by
      have hbase : HasDerivAt (fun y : ℝ => A + y) 1 x := by
        simpa using (hasDerivAt_id x).const_add A
      simpa using hbase.log hAne
    have hBderiv : HasDerivAt (fun y : ℝ => Real.log (B + y)) ((B + x)⁻¹) x := by
      have hbase : HasDerivAt (fun y : ℝ => B + y) 1 x := by
        simpa using (hasDerivAt_id x).const_add B
      simpa using hbase.log hBne
    have hmain := (hAderiv.sub hBderiv).div_const (B - A)
    have hval :
        ((A + x)⁻¹ - (B + x)⁻¹) / (B - A) = (A + x)⁻¹ * (B + x)⁻¹ := by
      field_simp [hAne, hBne, hdelta]
      ring_nf
    simpa [G, hval] using hmain
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ (A + x)⁻¹ * (B + x)⁻¹ := by
    intro x hx
    have hApos : 0 < A + x := by linarith [Set.mem_Ioi.mp hx]
    have hBpos : 0 < B + x := by linarith [Set.mem_Ioi.mp hx, hAB]
    positivity
  have htend_log :
      Filter.Tendsto
        (fun t : ℝ => Real.log (A + t) - Real.log (B + t)) Filter.atTop (𝓝 (0 : ℝ)) := by
    have htop : Filter.Tendsto (fun t : ℝ => B + t) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_left Filter.atTop B Filter.tendsto_id
    have hlog := (Real.tendsto_log_comp_add_sub_log (A - B)).comp htop
    refine hlog.congr' ?_
    exact Filter.Eventually.of_forall (fun t => by
      change Real.log ((B + t) + (A - B)) - Real.log (B + t) =
        Real.log (A + t) - Real.log (B + t)
      have harg : (B + t) + (A - B) = A + t := by ring
      rw [harg])
  have htend : Filter.Tendsto G Filter.atTop (𝓝 (0 : ℝ)) := by
    unfold G
    simpa using htend_log.div_const (B - A)
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
      (a := (0 : ℝ)) (l := (0 : ℝ)) hderiv hpos htend
  have hB : 0 < B := hA.trans hAB
  have hlogBA : Real.log (B / A) = Real.log B - Real.log A := by
    rw [Real.log_div hB.ne' hA.ne']
  rw [h]
  unfold G
  rw [hlogBA]
  field_simp [hdelta]
  ring_nf

theorem offdiag_laplace_integral_symm {A B : ℝ} (hB : 0 < B) (hBA : B < A) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), (A + t)⁻¹ * (B + t)⁻¹) =
      Real.log (A / B) / (A - B) := by
  simpa [mul_comm] using offdiag_laplace_integral (A := B) (B := A) hB hBA

theorem laplaceMoment_of_lt {a b k : ℕ} (hab : a < b) (hk : 1 ≤ k) :
    laplaceMoment a b k = kernelMomentIncrement a b k := by
  unfold laplaceMoment
  have hA : 0 < ((a + k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < a + k)
  have hAB : ((a + k : ℕ) : ℝ) < ((b + k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : a + k < b + k)
  rw [offdiag_laplace_integral hA hAB]
  rw [kernelMomentIncrement_of_lt hab hk]
  have hden :
      ((b + k : ℕ) : ℝ) - ((a + k : ℕ) : ℝ) = ((b - a : ℕ) : ℝ) := by
    rw [← Nat.cast_sub (by omega : a + k ≤ b + k)]
    congr 1
    omega
  rw [hden]

theorem laplaceMoment_of_gt {a b k : ℕ} (hba : b < a) (hk : 1 ≤ k) :
    laplaceMoment a b k = kernelMomentIncrement a b k := by
  unfold laplaceMoment
  have hB : 0 < ((b + k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < b + k)
  have hBA : ((b + k : ℕ) : ℝ) < ((a + k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : b + k < a + k)
  rw [offdiag_laplace_integral_symm hB hBA]
  rw [kernelMomentIncrement_of_gt hba hk]
  have hden :
      ((a + k : ℕ) : ℝ) - ((b + k : ℕ) : ℝ) = ((a - b : ℕ) : ℝ) := by
    rw [← Nat.cast_sub (by omega : b + k ≤ a + k)]
    congr 1
    omega
  rw [hden]

theorem laplaceMoment_eq_kernelMomentIncrement (a b k : ℕ) (hk : 1 ≤ k) :
    laplaceMoment a b k = kernelMomentIncrement a b k := by
  by_cases hab : a = b
  · subst b
    exact laplaceMoment_diag a k hk
  · by_cases hlt : a < b
    · exact laplaceMoment_of_lt hlt hk
    · have hgt : b < a := by omega
      exact laplaceMoment_of_gt hgt hk

/--
The original log-kernel moment has the closed pointwise value once the precise
Fubini/Tonelli exchange certificate is available.
-/
theorem logKernelMoment_eq_kernelMomentIncrement_of_fubiniCertificate
    (a b k : ℕ) (hk : 1 ≤ k)
    (hF : logKernelFubiniCertificate a b k) :
    logKernelMoment a b k = kernelMomentIncrement a b k := by
  rw [logKernelMoment_eq_laplaceMoment_of_fubiniCertificate a b k hk hF]
  exact laplaceMoment_eq_kernelMomentIncrement a b k hk

theorem laplaceMomentPointwiseTarget_holds : laplaceMomentPointwiseTarget := by
  intro a b k hk
  exact laplaceMoment_eq_kernelMomentIncrement a b k hk

theorem laplaceMomentSumCertificate :
    kernelMomentSumCertificate laplaceMoment :=
  kernelMomentSumCertificate_of_laplaceMomentPointwise laplaceMomentPointwiseTarget_holds

/--
Family form of the Fubini/Tonelli certificate, strong enough to make the
original log-kernel moment a valid kernel-moment sum certificate.
-/
theorem logKernelMomentSumCertificate_of_fubiniCertificate
    (hF : ∀ a b k : ℕ, 1 ≤ k → logKernelFubiniCertificate a b k) :
    kernelMomentSumCertificate logKernelMoment := by
  apply kernelMomentSumCertificate_of_pointwise_increment
  intro a b k hk
  exact logKernelMoment_eq_kernelMomentIncrement_of_fubiniCertificate
    a b k hk (hF a b k hk)

theorem kernelIndexedMomentExpansion_laplace_eq_closed (n N : ℕ) :
    kernelIndexedMomentExpansion n N laplaceMoment = closedKernelMomentExpansion n N :=
  kernelIndexedMomentExpansion_eq_closed_of_certificate laplaceMomentSumCertificate n N

/--
Finite-expansion bridge for the original log-kernel moment. After the single
remaining Fubini/Tonelli family certificate, the expansion is already the
closed kernel-moment expansion.
-/
theorem kernelIndexedMomentExpansion_logKernel_eq_closed_of_fubiniCertificate
    (hF : ∀ a b k : ℕ, 1 ≤ k → logKernelFubiniCertificate a b k)
    (n N : ℕ) :
    kernelIndexedMomentExpansion n N logKernelMoment =
      closedKernelMomentExpansion n N :=
  kernelIndexedMomentExpansion_eq_closed_of_certificate
    (logKernelMomentSumCertificate_of_fubiniCertificate hF) n N

theorem alternatingBinomial_mul_self (n i : ℕ) :
    alternatingBinomial n i * alternatingBinomial n i = ((Nat.choose n i : ℝ) ^ 2) := by
  rw [← pow_two]
  exact alternatingBinomial_sq n i

/-- Upper-triangular pair sum for a general two-variable weight. -/
def upperPairWeightedSum (m : ℕ) (G : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range m,
    ∑ j ∈ (Finset.range m).filter (fun j => i < j), G i j

theorem upperPairWeightedSum_succ (m : ℕ) (G : ℕ → ℕ → ℝ) :
    upperPairWeightedSum (m + 1) G =
      upperPairWeightedSum m G + ∑ i ∈ Finset.range m, G i m := by
  unfold upperPairWeightedSum
  rw [Finset.sum_range_succ]
  have hlast :
      (∑ j ∈ (Finset.range (m + 1)).filter (fun j => m < j), G m j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hjrange := Finset.mem_range.mp hj'.1
    omega
  rw [hlast, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have him : i < m := Finset.mem_range.mp hi
  have hinner :
      (∑ j ∈ (Finset.range (m + 1)).filter (fun j => i < j), G i j) =
        (∑ j ∈ (Finset.range m).filter (fun j => i < j), G i j) + G i m := by
    rw [Finset.range_add_one]
    rw [Finset.filter_insert]
    simp [him, add_comm]
  rw [hinner]

/--
Split a symmetric finite square sum into its diagonal and twice its upper
triangle. This is the weighted version needed for `kernelMomentClosed`.
-/
theorem square_sum_eq_diag_add_two_upper_weighted
    (m : ℕ) (G : ℕ → ℕ → ℝ)
    (hsym : ∀ i j, i < m → j < m → G i j = G j i) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, G i j) =
      (∑ i ∈ Finset.range m, G i i) + 2 * upperPairWeightedSum m G := by
  induction m with
  | zero =>
      simp [upperPairWeightedSum]
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hrows :
          (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range (m + 1), G i j) =
            (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, G i j) +
              ∑ i ∈ Finset.range m, G i m := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.sum_range_succ]
      have hlastrow_succ :
          (∑ j ∈ Finset.range (m + 1), G m j) =
            (∑ j ∈ Finset.range m, G m j) + G m m := by
        rw [Finset.sum_range_succ]
      have hlastrow :
          (∑ j ∈ Finset.range m, G m j) = ∑ i ∈ Finset.range m, G i m := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjm : j < m := Finset.mem_range.mp hj
        exact hsym m j (by omega) (by omega)
      have hdiag :
          (∑ i ∈ Finset.range (m + 1), G i i) =
            (∑ i ∈ Finset.range m, G i i) + G m m := by
        rw [Finset.sum_range_succ]
      rw [hrows, hlastrow_succ, hlastrow, hdiag, upperPairWeightedSum_succ]
      have ih' := ih (fun i j hi hj => hsym i j (by omega) (by omega))
      rw [ih']
      ring

/-- Diagonal part of the closed kernel expansion before simplifying signs. -/
def diagonalClosedKernelContribution (n N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    alternatingBinomial n i * alternatingBinomial n i * kernelMomentClosed (n + i) (n + i) N

/-- Upper-triangular off-diagonal part of the closed kernel expansion. -/
def upperClosedKernelContribution (n N : ℕ) : ℝ :=
  2 * upperPairWeightedSum (n + 1)
    (fun i j => alternatingBinomial n i * alternatingBinomial n j *
      kernelMomentClosed (n + i) (n + j) N)

/-- Diagonal part after using the diagonal closed form. -/
def diagonalHarmonicKernelContribution (n N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ((Nat.choose n i : ℝ) ^ 2) * (harmonicReal (n + i + N) - harmonicReal (n + i))

/-- Upper-triangular part after using the off-diagonal closed form. -/
def upperOffDiagonalKernelContribution (n N : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range (n + 1),
    ∑ j ∈ (Finset.range (n + 1)).filter (fun j => i < j),
      alternatingBinomial n i * alternatingBinomial n j * offDiagonalClosed (n + i) (j - i) N

theorem closedKernelMomentExpansion_eq_diagonal_add_upper (n N : ℕ) :
    closedKernelMomentExpansion n N =
      diagonalClosedKernelContribution n N + upperClosedKernelContribution n N := by
  unfold closedKernelMomentExpansion diagonalClosedKernelContribution upperClosedKernelContribution
  let G : ℕ → ℕ → ℝ := fun i j =>
    alternatingBinomial n i * alternatingBinomial n j * kernelMomentClosed (n + i) (n + j) N
  change (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), G i j) =
    (∑ i ∈ Finset.range (n + 1), G i i) + 2 * upperPairWeightedSum (n + 1) G
  apply square_sum_eq_diag_add_two_upper_weighted
  intro i j _hi _hj
  unfold G
  rw [kernelMomentClosed_comm (n + i) (n + j) N]
  ring

theorem diagonalClosedKernelContribution_eq_harmonic (n N : ℕ) :
    diagonalClosedKernelContribution n N = diagonalHarmonicKernelContribution n N := by
  unfold diagonalClosedKernelContribution diagonalHarmonicKernelContribution
  apply Finset.sum_congr rfl
  intro i _hi
  rw [kernelMomentClosed_diag]
  unfold diagonalClosed
  rw [alternatingBinomial_mul_self]

theorem upperClosedKernelContribution_eq_offDiagonal (n N : ℕ) :
    upperClosedKernelContribution n N = upperOffDiagonalKernelContribution n N := by
  unfold upperClosedKernelContribution upperOffDiagonalKernelContribution upperPairWeightedSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i < j := (Finset.mem_filter.mp hj).2
  have hlt : n + i < n + j := by omega
  change alternatingBinomial n i * alternatingBinomial n j * kernelMomentClosed (n + i) (n + j) N =
    alternatingBinomial n i * alternatingBinomial n j * offDiagonalClosed (n + i) (j - i) N
  rw [kernelMomentClosed_of_lt hlt]
  rw [Nat.add_sub_add_left]

theorem closedKernelMomentExpansion_eq_harmonic_add_offDiagonal (n N : ℕ) :
    closedKernelMomentExpansion n N =
      diagonalHarmonicKernelContribution n N + upperOffDiagonalKernelContribution n N := by
  rw [closedKernelMomentExpansion_eq_diagonal_add_upper]
  rw [diagonalClosedKernelContribution_eq_harmonic]
  rw [upperClosedKernelContribution_eq_offDiagonal]

/--
Split the off-diagonal kernel moment closed form into numerator-log and
denominator-log sums. This is the finite algebra interface needed before the
asymptotic estimate for the numerator logs.
-/
theorem offDiagonalClosed_eq_log_sums (m delta N : ℕ) :
    offDiagonalClosed m delta N =
      ((∑ r ∈ Finset.Icc 1 delta, Real.log ((N + m + r : ℕ) : ℝ)) -
        (∑ r ∈ Finset.Icc 1 delta, Real.log ((m + r : ℕ) : ℝ))) /
        (delta : ℝ) := by
  unfold offDiagonalClosed
  have hsum :
      (∑ r ∈ Finset.Icc 1 delta,
          Real.log (((N + m + r : ℕ) : ℝ) / ((m + r : ℕ) : ℝ))) =
        (∑ r ∈ Finset.Icc 1 delta, Real.log ((N + m + r : ℕ) : ℝ)) -
          (∑ r ∈ Finset.Icc 1 delta, Real.log ((m + r : ℕ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hnum_nat : 0 < N + m + r := by omega
    have hden_nat : 0 < m + r := by omega
    have hnum : ((N + m + r : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hnum_nat
    have hden : ((m + r : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hden_nat
    rw [Real.log_div hnum hden]
  rw [hsum]

/-- Real version of Sondow's rational diagonal term `A_n`. -/
def diagonalAReal (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ((Nat.choose n i : ℝ) ^ 2) * harmonicReal (n + i)

/-- Rational version of the diagonal `A_n` term, matching the main-library shape. -/
def diagonalARat (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1),
    ((Nat.choose n i : ℚ) ^ 2) * harmonicRat (n + i)

theorem harmonicReal_eq_harmonicRat_cast (n : ℕ) :
    harmonicReal n = (harmonicRat n : ℝ) := by
  unfold harmonicReal harmonicRat
  norm_num

theorem diagonalAReal_eq_diagonalARat_cast (n : ℕ) :
    diagonalAReal n = (diagonalARat n : ℝ) := by
  unfold diagonalAReal diagonalARat
  push_cast
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← harmonicReal_eq_harmonicRat_cast]

/-- The diagonal limit contribution after replacing `H_(N+n+i) - log N` by `gamma`. -/
def diagonalLimitContribution (gamma : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ((Nat.choose n i : ℝ) ^ 2) * (gamma - harmonicReal (n + i))

theorem diagonalLimitContribution_eq_choose_mul_sub_A (gamma : ℝ) (n : ℕ) :
    diagonalLimitContribution gamma n =
      (Nat.choose (2 * n) n : ℝ) * gamma - diagonalAReal n := by
  unfold diagonalLimitContribution diagonalAReal
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hleft :
      (∑ x ∈ Finset.range (n + 1), (Nat.choose n x : ℝ) ^ 2 * gamma) =
        (Nat.choose (2 * n) n : ℝ) * gamma := by
    rw [← Finset.sum_mul]
    rw [diagonalChooseSquareSum]
  rw [hleft]

/--
Certificate form of the shifted Euler-Mascheroni limit needed by the diagonal
part. The separate certificate keeps the finite-sum argument independent of
the chosen mathlib theorem used to prove the shifted limit.
-/
def shiftedHarmonicLimitCertificate (gamma : ℝ) : Prop :=
  ∀ c : ℕ,
    Filter.Tendsto
      (fun N : ℕ => harmonicReal (c + N) - Real.log (N : ℝ))
      Filter.atTop (𝓝 gamma)

theorem harmonicReal_eq_harmonic_cast (n : ℕ) :
    harmonicReal n = (harmonic n : ℝ) := by
  calc
    harmonicReal n = (harmonicRat n : ℝ) := harmonicReal_eq_harmonicRat_cast n
    _ = (harmonic n : ℝ) := by rw [harmonicRat_eq_harmonic]

theorem shiftedLog_sub_log_tendsto_zero (c : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => Real.log ((c + N : ℕ) : ℝ) - Real.log (N : ℝ))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have hlog0 :
      Filter.Tendsto
        (fun N : ℕ => Real.log ((N : ℝ) + (c : ℝ)) - Real.log (N : ℝ))
        Filter.atTop (𝓝 (0 : ℝ)) := by
    exact (Real.tendsto_log_comp_add_sub_log (c : ℝ)).comp tendsto_natCast_atTop_atTop
  refine hlog0.congr' ?_
  exact Filter.Eventually.of_forall (fun N => by
    simp [Nat.cast_add, add_comm])

theorem shiftedHarmonicLimitCertificate_eulerMascheroni :
    shiftedHarmonicLimitCertificate Real.eulerMascheroniConstant := by
  intro c
  have hshift : Filter.Tendsto (fun N : ℕ => N + c) Filter.atTop Filter.atTop :=
    Filter.tendsto_add_atTop_nat c
  have hh0 := Real.tendsto_harmonic_sub_log.comp hshift
  have hh :
      Filter.Tendsto
        (fun N : ℕ => harmonicReal (c + N) - Real.log ((c + N : ℕ) : ℝ))
        Filter.atTop (𝓝 Real.eulerMascheroniConstant) := by
    refine hh0.congr' ?_
    exact Filter.Eventually.of_forall (fun N => by
      change ((harmonic (N + c) : ℝ) - Real.log ((N + c : ℕ) : ℝ)) =
        harmonicReal (c + N) - Real.log ((c + N : ℕ) : ℝ)
      rw [show N + c = c + N by omega]
      rw [harmonicReal_eq_harmonic_cast])
  have hlog := shiftedLog_sub_log_tendsto_zero c
  have hmain := hh.add hlog
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain

theorem diagonalHarmonicKernelContribution_sub_log_eq_sum (n N : ℕ) :
    diagonalHarmonicKernelContribution n N -
        diagonalLogNCoefficient n * Real.log (N : ℝ) =
      ∑ i ∈ Finset.range (n + 1),
        ((Nat.choose n i : ℝ) ^ 2) *
          ((harmonicReal (n + i + N) - Real.log (N : ℝ)) -
            harmonicReal (n + i)) := by
  unfold diagonalHarmonicKernelContribution diagonalLogNCoefficient
  rw [Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [alternatingBinomial_sq]
  ring

theorem diagonalHarmonicKernelContribution_sub_log_tendsto_of_certificate
    {gamma : ℝ} (hgamma : shiftedHarmonicLimitCertificate gamma) (n : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        diagonalHarmonicKernelContribution n N -
          diagonalLogNCoefficient n * Real.log (N : ℝ))
      Filter.atTop (𝓝 (diagonalLimitContribution gamma n)) := by
  have hsum :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ i ∈ Finset.range (n + 1),
            ((Nat.choose n i : ℝ) ^ 2) *
              ((harmonicReal (n + i + N) - Real.log (N : ℝ)) -
                harmonicReal (n + i)))
        Filter.atTop (𝓝 (diagonalLimitContribution gamma n)) := by
    unfold diagonalLimitContribution
    refine tendsto_finsetSum (Finset.range (n + 1)) ?_
    intro i _hi
    exact ((hgamma (n + i)).sub tendsto_const_nhds).const_mul
      ((Nat.choose n i : ℝ) ^ 2)
  refine hsum.congr' ?_
  exact Filter.Eventually.of_forall
    (fun N => (diagonalHarmonicKernelContribution_sub_log_eq_sum n N).symm)

theorem diagonalHarmonicKernelContribution_sub_log_tendsto_eulerMascheroni
    (n : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        diagonalHarmonicKernelContribution n N -
          diagonalLogNCoefficient n * Real.log (N : ℝ))
      Filter.atTop
        (𝓝 (diagonalLimitContribution Real.eulerMascheroniConstant n)) :=
  diagonalHarmonicKernelContribution_sub_log_tendsto_of_certificate
    shiftedHarmonicLimitCertificate_eulerMascheroni n

theorem offDiagonalClosed_sub_log_eq_shifted_log_sum
    (m delta N : ℕ) (hdelta : 0 < delta) :
    offDiagonalClosed m delta N - Real.log (N : ℝ) =
      ((∑ r ∈ Finset.Icc 1 delta,
          (Real.log ((N + m + r : ℕ) : ℝ) - Real.log (N : ℝ))) -
        (∑ r ∈ Finset.Icc 1 delta, Real.log ((m + r : ℕ) : ℝ))) /
        (delta : ℝ) := by
  rw [offDiagonalClosed_eq_log_sums]
  have hcard : ((Finset.Icc 1 delta).card : ℝ) = (delta : ℝ) := by
    norm_num [Nat.card_Icc]
  have hsum_const :
      (∑ _r ∈ Finset.Icc 1 delta, Real.log (N : ℝ)) =
        (delta : ℝ) * Real.log (N : ℝ) := by
    rw [Finset.sum_const]
    rw [nsmul_eq_mul, hcard]
  have hdiff :
      (∑ r ∈ Finset.Icc 1 delta,
          (Real.log ((N + m + r : ℕ) : ℝ) - Real.log (N : ℝ))) =
        (∑ r ∈ Finset.Icc 1 delta, Real.log ((N + m + r : ℕ) : ℝ)) -
          (delta : ℝ) * Real.log (N : ℝ) := by
    rw [Finset.sum_sub_distrib]
    rw [hsum_const]
  rw [hdiff]
  have hdelta_ne : (delta : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hdelta
  field_simp [hdelta_ne]
  ring

theorem offDiagonalClosed_sub_log_tendsto_constant
    (m delta : ℕ) (hdelta : 0 < delta) :
    Filter.Tendsto
      (fun N : ℕ => offDiagonalClosed m delta N - Real.log (N : ℝ))
      Filter.atTop
      (𝓝 (- (∑ r ∈ Finset.Icc 1 delta, Real.log ((m + r : ℕ) : ℝ)) /
          (delta : ℝ))) := by
  have hnum :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ r ∈ Finset.Icc 1 delta,
            (Real.log ((N + m + r : ℕ) : ℝ) - Real.log (N : ℝ)))
        Filter.atTop (𝓝 (0 : ℝ)) := by
    have hsum :
        Filter.Tendsto
          (fun N : ℕ =>
            ∑ r ∈ Finset.Icc 1 delta,
              (Real.log ((N + m + r : ℕ) : ℝ) - Real.log (N : ℝ)))
          Filter.atTop
          (𝓝 (∑ _r ∈ Finset.Icc 1 delta, (0 : ℝ))) := by
      refine tendsto_finsetSum (α := ℕ) (M := ℝ) (Finset.Icc 1 delta) ?_
      intro r _hr
      have h := shiftedLog_sub_log_tendsto_zero (m + r)
      refine h.congr' ?_
      exact Filter.Eventually.of_forall (fun N => by
        change Real.log ((m + r + N : ℕ) : ℝ) - Real.log (N : ℝ) =
          Real.log ((N + m + r : ℕ) : ℝ) - Real.log (N : ℝ)
        rw [show m + r + N = N + m + r by omega])
    simpa using hsum
  have hmain :
      Filter.Tendsto
        (fun N : ℕ =>
          ((∑ r ∈ Finset.Icc 1 delta,
              (Real.log ((N + m + r : ℕ) : ℝ) - Real.log (N : ℝ))) -
            (∑ r ∈ Finset.Icc 1 delta, Real.log ((m + r : ℕ) : ℝ))) /
            (delta : ℝ))
        Filter.atTop
        (𝓝 (- (∑ r ∈ Finset.Icc 1 delta, Real.log ((m + r : ℕ) : ℝ)) /
          (delta : ℝ))) := by
    simpa using (hnum.sub tendsto_const_nhds).div_const (delta : ℝ)
  refine hmain.congr' ?_
  exact Filter.Eventually.of_forall (fun N =>
    (offDiagonalClosed_sub_log_eq_shifted_log_sum m delta N hdelta).symm)

/--
The finite denominator-log term obtained from the off-diagonal kernel moments.
The sign convention is the one produced by
`log ((N+m+r)/(m+r)) = log (N+m+r) - log (m+r)`.
-/
def offDiagonalConstantFromKernel (n : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range (n + 1),
    ∑ j ∈ (Finset.range (n + 1)).filter (fun j => i < j),
      ∑ r ∈ Finset.Icc 1 (j - i),
        (- (alternatingBinomial n i * alternatingBinomial n j) *
            (((j - i : ℕ) : ℝ)⁻¹)) *
          Real.log ((n + i + r : ℕ) : ℝ)

theorem offDiagonalConstantTerm_eq_alternatingTermReal
    {n i j : ℕ} (hij : i < j) :
    - (alternatingBinomial n i * alternatingBinomial n j) *
        (((j - i : ℕ) : ℝ)⁻¹) =
      alternatingTermReal n i j := by
  unfold alternatingBinomial alternatingTermReal
  have hsign :
      - (((-1 : ℝ) ^ i) * ((-1 : ℝ) ^ j)) =
        (-1 : ℝ) ^ (i + j - 1) := by
    rw [← pow_add]
    have hpow :
        (-1 : ℝ) ^ (i + j) = (-1 : ℝ) ^ ((i + j - 1) + 1) := by
      congr 1
      omega
    rw [hpow, pow_succ]
    ring
  rw [← hsign]
  field_simp

/--
The off-diagonal constant term from the kernel route is exactly the same raw
`L_n` triple sum used by the product-log certificate.
-/
theorem offDiagonalConstantFromKernel_eq_rawLLogSum (n : ℕ) :
    offDiagonalConstantFromKernel n = rawLLogSum n := by
  unfold offDiagonalConstantFromKernel rawLLogSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i < j := (Finset.mem_filter.mp hj).2
  apply Finset.sum_congr rfl
  intro r _hr
  rw [offDiagonalConstantTerm_eq_alternatingTermReal hij]

def upperOffDiagonalLimitConstant (n : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range (n + 1),
    ∑ j ∈ (Finset.range (n + 1)).filter (fun j => i < j),
      alternatingBinomial n i * alternatingBinomial n j *
        (- (∑ r ∈ Finset.Icc 1 (j - i), Real.log ((n + i + r : ℕ) : ℝ)) /
          ((j - i : ℕ) : ℝ))

theorem upperOffDiagonalKernelContribution_sub_log_eq_sum (n N : ℕ) :
    upperOffDiagonalKernelContribution n N -
        triangularLogNCoefficient n * Real.log (N : ℝ) =
      2 * ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ (Finset.range (n + 1)).filter (fun j => i < j),
          alternatingBinomial n i * alternatingBinomial n j *
            (offDiagonalClosed (n + i) (j - i) N - Real.log (N : ℝ)) := by
  unfold upperOffDiagonalKernelContribution triangularLogNCoefficient upperPairSum
  rw [show (2 * ∑ i ∈ Finset.range (n + 1),
      ∑ j ∈ (Finset.range (n + 1)).filter (fun j => i < j),
        alternatingBinomial n i * alternatingBinomial n j) * Real.log (N : ℝ) =
      2 * ((∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ (Finset.range (n + 1)).filter (fun j => i < j),
          alternatingBinomial n i * alternatingBinomial n j) * Real.log (N : ℝ)) by ring]
  rw [← mul_sub]
  congr 1
  rw [Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

theorem upperOffDiagonalLimitConstant_eq_offDiagonalConstantFromKernel (n : ℕ) :
    upperOffDiagonalLimitConstant n = offDiagonalConstantFromKernel n := by
  unfold upperOffDiagonalLimitConstant offDiagonalConstantFromKernel
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i < j := (Finset.mem_filter.mp hj).2
  have hdelta_ne : ((j - i : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by omega : 0 < j - i)
  rw [div_eq_mul_inv]
  rw [show alternatingBinomial n i * alternatingBinomial n j *
      ((-∑ r ∈ Finset.Icc 1 (j - i), Real.log ((n + i + r : ℕ) : ℝ)) *
        (((j - i : ℕ) : ℝ)⁻¹)) =
      (-(alternatingBinomial n i * alternatingBinomial n j) *
        (((j - i : ℕ) : ℝ)⁻¹)) *
        (∑ r ∈ Finset.Icc 1 (j - i), Real.log ((n + i + r : ℕ) : ℝ)) by ring]
  rw [Finset.mul_sum]

theorem upperOffDiagonalKernelContribution_sub_log_tendsto_constant (n : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => upperOffDiagonalKernelContribution n N -
        triangularLogNCoefficient n * Real.log (N : ℝ))
      Filter.atTop (𝓝 (offDiagonalConstantFromKernel n)) := by
  have hsum :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ i ∈ Finset.range (n + 1),
            ∑ j ∈ (Finset.range (n + 1)).filter (fun j => i < j),
              alternatingBinomial n i * alternatingBinomial n j *
                (offDiagonalClosed (n + i) (j - i) N - Real.log (N : ℝ)))
        Filter.atTop
        (𝓝 (∑ i ∈ Finset.range (n + 1),
          ∑ j ∈ (Finset.range (n + 1)).filter (fun j => i < j),
            alternatingBinomial n i * alternatingBinomial n j *
              (- (∑ r ∈ Finset.Icc 1 (j - i), Real.log ((n + i + r : ℕ) : ℝ)) /
                ((j - i : ℕ) : ℝ)))) := by
    refine tendsto_finsetSum (α := ℕ) (M := ℝ) (Finset.range (n + 1)) ?_
    intro i _hi
    refine tendsto_finsetSum (α := ℕ) (M := ℝ)
      ((Finset.range (n + 1)).filter (fun j => i < j)) ?_
    intro j hj
    have hij : i < j := (Finset.mem_filter.mp hj).2
    exact (offDiagonalClosed_sub_log_tendsto_constant (n + i) (j - i) (by omega)).const_mul
      (alternatingBinomial n i * alternatingBinomial n j)
  have htwo :
      Filter.Tendsto
        (fun N : ℕ =>
          2 * ∑ i ∈ Finset.range (n + 1),
            ∑ j ∈ (Finset.range (n + 1)).filter (fun j => i < j),
              alternatingBinomial n i * alternatingBinomial n j *
                (offDiagonalClosed (n + i) (j - i) N - Real.log (N : ℝ)))
        Filter.atTop (𝓝 (upperOffDiagonalLimitConstant n)) := by
    unfold upperOffDiagonalLimitConstant
    simpa [mul_assoc] using hsum.const_mul (2 : ℝ)
  have htarget :
      Filter.Tendsto
        (fun N : ℕ =>
          2 * ∑ i ∈ Finset.range (n + 1),
            ∑ j ∈ (Finset.range (n + 1)).filter (fun j => i < j),
              alternatingBinomial n i * alternatingBinomial n j *
                (offDiagonalClosed (n + i) (j - i) N - Real.log (N : ℝ)))
        Filter.atTop (𝓝 (offDiagonalConstantFromKernel n)) := by
    simpa [upperOffDiagonalLimitConstant_eq_offDiagonalConstantFromKernel n] using htwo
  refine htarget.congr' ?_
  exact Filter.Eventually.of_forall (fun N =>
    (upperOffDiagonalKernelContribution_sub_log_eq_sum n N).symm)

theorem closedKernelMomentExpansion_eq_centered_sum {n : ℕ} (hn : n ≠ 0) (N : ℕ) :
    closedKernelMomentExpansion n N =
      (diagonalHarmonicKernelContribution n N -
          diagonalLogNCoefficient n * Real.log (N : ℝ)) +
        (upperOffDiagonalKernelContribution n N -
          triangularLogNCoefficient n * Real.log (N : ℝ)) := by
  rw [closedKernelMomentExpansion_eq_harmonic_add_offDiagonal]
  have hcancel := decompositionLogNCoefficient_cancel hn
  calc
    diagonalHarmonicKernelContribution n N + upperOffDiagonalKernelContribution n N
        = diagonalHarmonicKernelContribution n N + upperOffDiagonalKernelContribution n N -
            (diagonalLogNCoefficient n + triangularLogNCoefficient n) *
              Real.log (N : ℝ) := by
          rw [hcancel]
          ring
    _ = (diagonalHarmonicKernelContribution n N -
          diagonalLogNCoefficient n * Real.log (N : ℝ)) +
        (upperOffDiagonalKernelContribution n N -
          triangularLogNCoefficient n * Real.log (N : ℝ)) := by
          ring

theorem closedKernelMomentExpansion_tendsto_decompositionConstant {n : ℕ} (hn : n ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => closedKernelMomentExpansion n N)
      Filter.atTop
      (𝓝 (diagonalLimitContribution Real.eulerMascheroniConstant n +
        offDiagonalConstantFromKernel n)) := by
  have hdiag := diagonalHarmonicKernelContribution_sub_log_tendsto_eulerMascheroni n
  have hoff := upperOffDiagonalKernelContribution_sub_log_tendsto_constant n
  have hsum := hdiag.add hoff
  refine hsum.congr' ?_
  exact Filter.Eventually.of_forall (fun N =>
    (closedKernelMomentExpansion_eq_centered_sum hn N).symm)

theorem closedKernelMomentExpansion_tendsto_rawSondowConstant {n : ℕ} (hn : n ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => closedKernelMomentExpansion n N)
      Filter.atTop
      (𝓝 ((Nat.choose (2 * n) n : ℝ) * Real.eulerMascheroniConstant +
        rawLLogSum n - diagonalAReal n)) := by
  have h := closedKernelMomentExpansion_tendsto_decompositionConstant hn
  convert h using 1
  rw [diagonalLimitContribution_eq_choose_mul_sub_A]
  rw [offDiagonalConstantFromKernel_eq_rawLLogSum]
  ring_nf

/-- Pointwise sidecar normalization of Sondow's original integrand. -/
def originalSondowIntegrand (n : ℕ) (x y : ℝ) : ℝ :=
  (x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n) /
    (-(1 - x * y) * Real.log (x * y))

/-- Pointwise explicit remainder left by the truncated denominator split. -/
def originalLogKernelRemainderIntegrand (n N : ℕ) (x y : ℝ) : ℝ :=
  ((x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n * (x * y) ^ N) /
    (1 - x * y)) / (-Real.log (x * y))

/-- The finite logarithmic-kernel part of the truncated Sondow split. -/
def logKernelFiniteSum (n N : ℕ) (x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ∑ j ∈ Finset.range (n + 1),
      ∑ k ∈ Finset.Icc 1 N,
        alternatingBinomial n i * alternatingBinomial n j *
          logKernelMonomial (n + i) (n + j) k x y

theorem originalSondowIntegrand_eq_logKernelFiniteSum_add_remainder
    (n N : ℕ) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    originalSondowIntegrand n x y =
      logKernelFiniteSum n N x y + originalLogKernelRemainderIntegrand n N x y := by
  rcases mul_mem_open_unit hx0 hx1 hy0 hy1 with ⟨hxy0, hxy1⟩
  have hden : 1 - x * y ≠ 0 := by
    exact ne_of_gt (by linarith : 0 < 1 - x * y)
  have hlog_neg : Real.log (x * y) < 0 := (Real.log_neg_iff hxy0).2 hxy1
  have hlog : Real.log (x * y) ≠ 0 := ne_of_lt hlog_neg
  unfold originalSondowIntegrand originalLogKernelRemainderIntegrand logKernelFiniteSum
  exact original_log_denominator_split_kernel_index n N hden hlog

theorem originalSondowIntegrand_nonneg
    (n : ℕ) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    0 ≤ originalSondowIntegrand n x y := by
  unfold originalSondowIntegrand
  rcases mul_mem_open_unit hx0 hx1 hy0 hy1 with ⟨hxy0, hxy1⟩
  have hnum : 0 ≤ x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n := by positivity
  have hlog_neg : Real.log (x * y) < 0 := (Real.log_neg_iff hxy0).2 hxy1
  have hden_pos : 0 < -(1 - x * y) * Real.log (x * y) := by
    have hone : 0 < 1 - x * y := by linarith
    nlinarith [mul_pos hone (neg_pos.mpr hlog_neg)]
  exact div_nonneg hnum hden_pos.le

theorem originalLogKernelRemainderIntegrand_nonneg
    (n N : ℕ) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    0 ≤ originalLogKernelRemainderIntegrand n N x y := by
  unfold originalLogKernelRemainderIntegrand
  rcases mul_mem_open_unit hx0 hx1 hy0 hy1 with ⟨hxy0, hxy1⟩
  have hnum :
      0 ≤ x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n * (x * y) ^ N := by
    positivity
  have hone_pos : 0 < 1 - x * y := by linarith
  have hlog_neg : Real.log (x * y) < 0 := (Real.log_neg_iff hxy0).2 hxy1
  have hlog_pos : 0 < -Real.log (x * y) := by linarith
  exact div_nonneg (div_nonneg hnum hone_pos.le) hlog_pos.le

/--
On the open unit square, the truncated remainder is exactly the original
integrand multiplied by the geometric tail `(xy)^N`.
-/
theorem originalLogKernelRemainderIntegrand_eq_original_mul_pow
    (n N : ℕ) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    originalLogKernelRemainderIntegrand n N x y =
      originalSondowIntegrand n x y * (x * y) ^ N := by
  rcases mul_mem_open_unit hx0 hx1 hy0 hy1 with ⟨hxy0, hxy1⟩
  have hone_pos : 0 < 1 - x * y := by linarith
  have hlog_neg : Real.log (x * y) < 0 := (Real.log_neg_iff hxy0).2 hxy1
  have hone_ne : 1 - x * y ≠ 0 := ne_of_gt hone_pos
  have hlog_ne : Real.log (x * y) ≠ 0 := ne_of_lt hlog_neg
  unfold originalLogKernelRemainderIntegrand originalSondowIntegrand
  field_simp [hone_ne, hlog_ne]

theorem originalLogKernelRemainderIntegrand_le_originalSondowIntegrand
    (n N : ℕ) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    originalLogKernelRemainderIntegrand n N x y ≤ originalSondowIntegrand n x y := by
  rw [originalLogKernelRemainderIntegrand_eq_original_mul_pow n N hx0 hx1 hy0 hy1]
  have hxy := mul_mem_open_unit hx0 hx1 hy0 hy1
  have hpow : (x * y) ^ N ≤ 1 :=
    pow_le_one₀ (n := N) (le_of_lt hxy.1) (le_of_lt hxy.2)
  exact mul_le_of_le_one_right (originalSondowIntegrand_nonneg n hx0 hx1 hy0 hy1) hpow

theorem originalLogKernelRemainderIntegrand_tendsto_zero
    (n : ℕ) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    Filter.Tendsto (fun N : ℕ => originalLogKernelRemainderIntegrand n N x y)
      Filter.atTop (𝓝 (0 : ℝ)) := by
  have hxy := mul_mem_open_unit hx0 hx1 hy0 hy1
  have hpow :
      Filter.Tendsto (fun N : ℕ => (x * y) ^ N) Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hxy.1) hxy.2
  have hmain :
      Filter.Tendsto
        (fun N : ℕ => originalSondowIntegrand n x y * (x * y) ^ N)
        Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa using hpow.const_mul (originalSondowIntegrand n x y)
  refine hmain.congr' ?_
  exact Filter.Eventually.of_forall (fun N =>
    (originalLogKernelRemainderIntegrand_eq_original_mul_pow n N hx0 hx1 hy0 hy1).symm)

/-- Open-square version of the unit square, avoiding endpoint bookkeeping. -/
def openUnitSquare : Set (ℝ × ℝ) :=
  Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1

theorem measurableSet_openUnitSquare : MeasurableSet openUnitSquare := by
  unfold openUnitSquare
  exact measurableSet_Ioo.prod measurableSet_Ioo

theorem logKernelMonomial_integrableOn_openUnitSquare (a b k : ℕ) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => logKernelMonomial a b k p.1 p.2)
      openUnitSquare := by
  simpa [openUnitSquare] using logKernelMonomial_integrableOn_openSquare a b k

/-- Lebesgue measure restricted to the open unit square. -/
def openUnitSquareMeasure : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
    openUnitSquare

/-- The original Sondow integrand is globally measurable. -/
theorem measurable_originalSondowIntegrand (n : ℕ) :
    Measurable (fun p : ℝ × ℝ => originalSondowIntegrand n p.1 p.2) := by
  unfold originalSondowIntegrand
  measurability

/-- On `[0,1]`, every positive natural power is bounded by the base. -/
theorem pow_le_self_on_unit_of_one_le {x : ℝ} {n : ℕ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hn : 1 ≤ n) :
    x ^ n ≤ x := by
  have htail : x ^ (n - 1) ≤ 1 := pow_le_one₀ hx0 hx1
  have hpow : x ^ n = x * x ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow]
  exact mul_le_of_le_one_right hx0 htail

/--
For `n ≥ 1`, the polynomial numerator in Sondow's integrand is bounded by the
square of the geometric denominator on the closed unit square.
-/
theorem sondowNumerator_le_one_sub_mul_sq
    {n : ℕ} (hn : 1 ≤ n) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n ≤ (1 - x * y) ^ 2 := by
  have h1x0 : 0 ≤ 1 - x := by linarith
  have h1x1 : 1 - x ≤ 1 := by linarith
  have h1y0 : 0 ≤ 1 - y := by linarith
  have h1y1 : 1 - y ≤ 1 := by linarith
  have hxpow := pow_le_self_on_unit_of_one_le hx0 hx1 hn
  have h1xpow := pow_le_self_on_unit_of_one_le h1x0 h1x1 hn
  have hypow := pow_le_self_on_unit_of_one_le hy0 hy1 hn
  have h1ypow := pow_le_self_on_unit_of_one_le h1y0 h1y1 hn
  have hxpart : x ^ n * (1 - x) ^ n ≤ x * (1 - x) := by
    exact mul_le_mul hxpow h1xpow (pow_nonneg h1x0 n) hx0
  have hypart : y ^ n * (1 - y) ^ n ≤ y * (1 - y) := by
    exact mul_le_mul hypow h1ypow (pow_nonneg h1y0 n) hy0
  have hpart_nonneg : 0 ≤ y ^ n * (1 - y) ^ n := by positivity
  have htarget_nonneg : 0 ≤ x * (1 - x) := by positivity
  have hmul :
      (x ^ n * (1 - x) ^ n) * (y ^ n * (1 - y) ^ n) ≤
        (x * (1 - x)) * (y * (1 - y)) := by
    exact mul_le_mul hxpart hypart hpart_nonneg htarget_nonneg
  have hxy_le_one : x * y ≤ 1 := by
    exact (mul_le_mul hx1 hy1 hy0 zero_le_one).trans (by norm_num)
  have hboundary_nonneg : 0 ≤ (1 - x) * (1 - y) := by positivity
  have hdrop_xy : x * (1 - x) * y * (1 - y) ≤ (1 - x) * (1 - y) := by
    have h := mul_le_mul_of_nonneg_right hxy_le_one hboundary_nonneg
    nlinarith
  have hxy_le_x : x * y ≤ x := by
    simpa using mul_le_mul_of_nonneg_left hy1 hx0
  have hxy_le_y : x * y ≤ y := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hx1 hy0
  have ha_le : 1 - x ≤ 1 - x * y := by linarith
  have hb_le : 1 - y ≤ 1 - x * y := by linarith
  have hc_nonneg : 0 ≤ 1 - x * y := by linarith
  have hsquare : (1 - x) * (1 - y) ≤ (1 - x * y) * (1 - x * y) := by
    exact mul_le_mul ha_le hb_le h1y0 hc_nonneg
  calc
    x ^ n * (1 - x) ^ n * y ^ n * (1 - y) ^ n
        = (x ^ n * (1 - x) ^ n) * (y ^ n * (1 - y) ^ n) := by ring
    _ ≤ (x * (1 - x)) * (y * (1 - y)) := hmul
    _ = x * (1 - x) * y * (1 - y) := by ring
    _ ≤ (1 - x) * (1 - y) := hdrop_xy
    _ ≤ (1 - x * y) * (1 - x * y) := hsquare
    _ = (1 - x * y) ^ 2 := by ring

/--
For `n ≥ 1`, the original Sondow integrand is bounded by `1` on the open unit
square. The logarithmic denominator is controlled by
`log u ≤ u - 1`, i.e. `1 - u ≤ -log u`.
-/
theorem originalSondowIntegrand_le_one
    {n : ℕ} (hn : 1 ≤ n) {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    originalSondowIntegrand n x y ≤ 1 := by
  unfold originalSondowIntegrand
  rcases mul_mem_open_unit hx0 hx1 hy0 hy1 with ⟨hxy0, hxy1⟩
  have hnum_le := sondowNumerator_le_one_sub_mul_sq hn hx0.le hx1.le hy0.le hy1.le
  have hlog_bound : 1 - x * y ≤ -Real.log (x * y) := by
    have h := Real.log_le_sub_one_of_pos hxy0
    linarith
  have hone_nonneg : 0 ≤ 1 - x * y := by linarith
  have hden_ge : (1 - x * y) ^ 2 ≤ -(1 - x * y) * Real.log (x * y) := by
    have hmul := mul_le_mul_of_nonneg_left hlog_bound hone_nonneg
    nlinarith
  have hden_pos : 0 < -(1 - x * y) * Real.log (x * y) := by
    have hone : 0 < 1 - x * y := by linarith
    have hlog_neg : Real.log (x * y) < 0 := (Real.log_neg_iff hxy0).2 hxy1
    nlinarith [mul_pos hone (neg_pos.mpr hlog_neg)]
  rw [div_le_iff₀ hden_pos]
  simpa [one_mul] using hnum_le.trans hden_ge

theorem openUnitSquareMeasure_isFinite :
    MeasureTheory.IsFiniteMeasure openUnitSquareMeasure := by
  change MeasureTheory.IsFiniteMeasure
    ((MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
      openUnitSquare)
  rw [MeasureTheory.isFiniteMeasure_restrict]
  exact ne_of_lt (Bornology.IsBounded.measure_lt_top
    ((Metric.isBounded_Ioo (0 : ℝ) 1).prod (Metric.isBounded_Ioo (0 : ℝ) 1)))

theorem logKernelLaplaceIntegrand_integrable_prod (a b k : ℕ) :
    MeasureTheory.Integrable
      (fun q : (ℝ × ℝ) × ℝ =>
        kernelMomentMonomial a b k q.1.1 q.1.2 * (q.1.1 * q.1.2) ^ q.2)
      (openUnitSquareMeasure.prod
        ((MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Ioi (0 : ℝ)))) := by
  letI : MeasureTheory.IsFiniteMeasure openUnitSquareMeasure :=
    openUnitSquareMeasure_isFinite
  let μt : MeasureTheory.Measure ℝ :=
    (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Ioi (0 : ℝ))
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun q : (ℝ × ℝ) × ℝ =>
        kernelMomentMonomial a b k q.1.1 q.1.2 * (q.1.1 * q.1.2) ^ q.2)
      (openUnitSquareMeasure.prod μt) := by
    apply Measurable.aestronglyMeasurable
    unfold kernelMomentMonomial
    measurability
  rw [MeasureTheory.integrable_prod_iff hmeas]
  constructor
  · have hmem : ∀ᵐ p ∂openUnitSquareMeasure, p ∈ openUnitSquare := by
      simpa [openUnitSquareMeasure] using
        MeasureTheory.ae_restrict_mem measurableSet_openUnitSquare
    filter_upwards [hmem] with p hp
    rcases hp with ⟨hx, hy⟩
    rcases mul_mem_open_unit hx.1 hx.2 hy.1 hy.2 with ⟨hxy0, hxy1⟩
    have htint := integrableOn_const_rpow_Ioi hxy0 hxy1
    have hmul := htint.const_mul (kernelMomentMonomial a b k p.1 p.2)
    simpa [μt] using hmul
  · have hlog : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => logKernelMonomial a b k p.1 p.2)
        openUnitSquareMeasure := by
      simpa [MeasureTheory.IntegrableOn, openUnitSquareMeasure] using
        logKernelMonomial_integrableOn_openUnitSquare a b k
    refine (MeasureTheory.integrable_congr ?_).mpr hlog
    have hmem : ∀ᵐ p ∂openUnitSquareMeasure, p ∈ openUnitSquare := by
      simpa [openUnitSquareMeasure] using
        MeasureTheory.ae_restrict_mem measurableSet_openUnitSquare
    filter_upwards [hmem] with p hp
    rcases hp with ⟨hx, hy⟩
    calc
      (∫ t,
        ‖kernelMomentMonomial a b k p.1 p.2 * (p.1 * p.2) ^ t‖ ∂μt)
          = ∫ t,
              kernelMomentMonomial a b k p.1 p.2 * (p.1 * p.2) ^ t ∂μt := by
            apply MeasureTheory.integral_congr_ae
            have htmem : ∀ᵐ t ∂μt, t ∈ Set.Ioi (0 : ℝ) := by
              simpa [μt] using MeasureTheory.ae_restrict_mem
                (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))
            filter_upwards [htmem] with t _ht
            have hnonneg :=
              kernelMomentMonomial_mul_rpow_nonneg a b k hx.1.le hy.1.le (t := t)
            exact Real.norm_of_nonneg hnonneg
      _ = logKernelMonomial a b k p.1 p.2 := by
            simpa [μt] using
              (logKernelMonomial_eq_laplace_integral a b k hx.1 hx.2 hy.1 hy.2).symm

/--
Certificate that the original Sondow integrand is integrable on the open unit
square. This is the domination hypothesis needed by the standard dominated
convergence theorem.
-/
def openSquareOriginalIntegrandIntegrableCertificate (n : ℕ) : Prop :=
  MeasureTheory.Integrable
    (fun p : ℝ × ℝ => originalSondowIntegrand n p.1 p.2)
    openUnitSquareMeasure

theorem openSquareOriginalIntegrandIntegrableCertificate_holds
    {n : ℕ} (hn : 1 ≤ n) :
    openSquareOriginalIntegrandIntegrableCertificate n := by
  letI : MeasureTheory.IsFiniteMeasure openUnitSquareMeasure :=
    openUnitSquareMeasure_isFinite
  have hnorm : ∀ᵐ p ∂openUnitSquareMeasure,
      ‖originalSondowIntegrand n p.1 p.2‖ ≤ (1 : ℝ) := by
    have hmem : ∀ᵐ p ∂openUnitSquareMeasure, p ∈ openUnitSquare := by
      simpa [openUnitSquareMeasure] using
        MeasureTheory.ae_restrict_mem measurableSet_openUnitSquare
    filter_upwards [hmem] with p hp
    rcases hp with ⟨hx, hy⟩
    have hnonneg := originalSondowIntegrand_nonneg n hx.1 hx.2 hy.1 hy.2
    have hle := originalSondowIntegrand_le_one hn hx.1 hx.2 hy.1 hy.2
    simpa [Real.norm_of_nonneg hnonneg] using hle
  exact MeasureTheory.Integrable.of_bound
    ((measurable_originalSondowIntegrand n).aestronglyMeasurable) 1 hnorm

theorem measurable_originalLogKernelRemainderIntegrand (n N : ℕ) :
    Measurable (fun p : ℝ × ℝ => originalLogKernelRemainderIntegrand n N p.1 p.2) := by
  unfold originalLogKernelRemainderIntegrand
  measurability

theorem aestronglyMeasurable_originalLogKernelRemainderIntegrand_restrict_openUnitSquare
    (n N : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => originalLogKernelRemainderIntegrand n N p.1 p.2)
      openUnitSquareMeasure :=
  (measurable_originalLogKernelRemainderIntegrand n N).aestronglyMeasurable

theorem openSquareOriginalLogKernelRemainderIntegrable
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => originalLogKernelRemainderIntegrand n N p.1 p.2)
      openUnitSquare := by
  rw [MeasureTheory.IntegrableOn]
  exact MeasureTheory.Integrable.mono'
    (openSquareOriginalIntegrandIntegrableCertificate_holds hn)
    (aestronglyMeasurable_originalLogKernelRemainderIntegrand_restrict_openUnitSquare n N)
    (by
      have hmem : ∀ᵐ p ∂openUnitSquareMeasure, p ∈ openUnitSquare := by
        simpa [openUnitSquareMeasure] using
          MeasureTheory.ae_restrict_mem measurableSet_openUnitSquare
      filter_upwards [hmem] with p hp
      rcases hp with ⟨hx, hy⟩
      have hnonneg := originalLogKernelRemainderIntegrand_nonneg n N hx.1 hx.2 hy.1 hy.2
      have hle := originalLogKernelRemainderIntegrand_le_originalSondowIntegrand
        n N hx.1 hx.2 hy.1 hy.2
      simpa [Real.norm_of_nonneg hnonneg] using hle)

theorem openSquareLogKernelFiniteSumIntegrable
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => logKernelFiniteSum n N p.1 p.2)
      openUnitSquare := by
  have hOriginal :
      MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => originalSondowIntegrand n p.1 p.2)
        openUnitSquare := by
    simpa [openSquareOriginalIntegrandIntegrableCertificate,
      MeasureTheory.IntegrableOn, openUnitSquareMeasure] using
      (openSquareOriginalIntegrandIntegrableCertificate_holds hn)
  have hRemainder :=
    openSquareOriginalLogKernelRemainderIntegrable (n := n) hn N
  refine (hOriginal.sub hRemainder).congr_fun ?_ measurableSet_openUnitSquare
  intro p hp
  rcases hp with ⟨hx, hy⟩
  have hsplit :=
    originalSondowIntegrand_eq_logKernelFiniteSum_add_remainder
      n N hx.1 hx.2 hy.1 hy.2
  change originalSondowIntegrand n p.1 p.2 -
      originalLogKernelRemainderIntegrand n N p.1 p.2 =
    logKernelFiniteSum n N p.1 p.2
  rw [hsplit]
  ring

/--
On the open square, the explicit remainder integral tends to zero from the
standard dominated-convergence theorem: pointwise convergence is supplied by
the geometric tail `(xy)^N`, and domination is by the original nonnegative
Sondow integrand.
-/
theorem openSquare_originalLogKernelRemainder_setIntegral_tendsto_zero_of_dominated
    (n : ℕ)
    (hbound : openSquareOriginalIntegrandIntegrableCertificate n) :
    Filter.Tendsto
      (fun N : ℕ => ∫ p : ℝ × ℝ in openUnitSquare,
        originalLogKernelRemainderIntegrand n N p.1 p.2)
      Filter.atTop (𝓝 (0 : ℝ)) := by
  let μ : MeasureTheory.Measure (ℝ × ℝ) :=
    openUnitSquareMeasure
  let F : ℕ → (ℝ × ℝ) → ℝ :=
    fun N p => originalLogKernelRemainderIntegrand n N p.1 p.2
  let bound : (ℝ × ℝ) → ℝ :=
    fun p => originalSondowIntegrand n p.1 p.2
  have hdom : ∀ N : ℕ, ∀ᵐ p ∂μ, ‖F N p‖ ≤ bound p := by
    intro N
    have hmem : ∀ᵐ p ∂μ, p ∈ openUnitSquare := by
      simpa [μ, openUnitSquareMeasure] using
        MeasureTheory.ae_restrict_mem measurableSet_openUnitSquare
    filter_upwards [hmem] with p hp
    rcases hp with ⟨hx, hy⟩
    have hnonneg := originalLogKernelRemainderIntegrand_nonneg n N hx.1 hx.2 hy.1 hy.2
    have hle := originalLogKernelRemainderIntegrand_le_originalSondowIntegrand
      n N hx.1 hx.2 hy.1 hy.2
    simpa [F, bound, Real.norm_of_nonneg hnonneg] using hle
  have hlim : ∀ᵐ p ∂μ,
      Filter.Tendsto (fun N : ℕ => F N p) Filter.atTop (𝓝 (0 : ℝ)) := by
    have hmem : ∀ᵐ p ∂μ, p ∈ openUnitSquare := by
      simpa [μ, openUnitSquareMeasure] using
        MeasureTheory.ae_restrict_mem measurableSet_openUnitSquare
    filter_upwards [hmem] with p hp
    rcases hp with ⟨hx, hy⟩
    simpa [F] using originalLogKernelRemainderIntegrand_tendsto_zero
      n hx.1 hx.2 hy.1 hy.2
  have h := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := μ) (F := F) (f := fun _p : ℝ × ℝ => (0 : ℝ)) (bound := bound)
    (fun N =>
      aestronglyMeasurable_originalLogKernelRemainderIntegrand_restrict_openUnitSquare n N)
    hbound hdom hlim
  simpa [μ, F, bound, openUnitSquareMeasure] using h

/--
Unconditional open-square remainder estimate for the Sondow range `n ≥ 1`.
The only inputs are now the already proved pointwise tail estimate, the
measurability lemmas, and the boundedness of the original integrand.
-/
theorem openSquare_originalLogKernelRemainder_setIntegral_tendsto_zero
    {n : ℕ} (hn : 1 ≤ n) :
    Filter.Tendsto
      (fun N : ℕ => ∫ p : ℝ × ℝ in openUnitSquare,
        originalLogKernelRemainderIntegrand n N p.1 p.2)
      Filter.atTop (𝓝 (0 : ℝ)) :=
  openSquare_originalLogKernelRemainder_setIntegral_tendsto_zero_of_dominated
    n (openSquareOriginalIntegrandIntegrableCertificate_holds hn)

/--
Fubini bridge from the open-square product set integral to the iterated
`Ioo × Ioo` set integral for the explicit remainder.
-/
theorem openSquare_originalLogKernelRemainder_setIntegral_eq_iterated_Ioo
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    (∫ p : ℝ × ℝ in openUnitSquare,
        originalLogKernelRemainderIntegrand n N p.1 p.2) =
      ∫ x : ℝ in Set.Ioo (0 : ℝ) 1,
        ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
          originalLogKernelRemainderIntegrand n N x y := by
  unfold openUnitSquare
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  exact MeasureTheory.setIntegral_prod
    (fun p : ℝ × ℝ => originalLogKernelRemainderIntegrand n N p.1 p.2)
    (openSquareOriginalLogKernelRemainderIntegrable hn N)

/-- Sidecar normalization of Sondow's original double integral. -/
def originalSondowIntegral (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ∫ y in (0 : ℝ)..1, originalSondowIntegrand n x y

/--
The explicit remainder left by the truncated denominator split after the finite
kernel-moment part is removed.
-/
def originalLogKernelRemainder (n N : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ∫ y in (0 : ℝ)..1, originalLogKernelRemainderIntegrand n N x y

theorem originalLogKernelRemainder_intervalIntegral_eq_iterated_Ioo
    (n N : ℕ) :
    originalLogKernelRemainder n N =
      ∫ x : ℝ in Set.Ioo (0 : ℝ) 1,
        ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
          originalLogKernelRemainderIntegrand n N x y := by
  unfold originalLogKernelRemainder
  have hinner :
      (fun x : ℝ =>
        ∫ y in (0 : ℝ)..1, originalLogKernelRemainderIntegrand n N x y) =
        fun x : ℝ =>
          ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
            originalLogKernelRemainderIntegrand n N x y := by
    funext x
    rw [intervalIntegral.integral_of_le zero_le_one]
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hinner]
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem originalLogKernelRemainder_eq_openSquare_setIntegral
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    originalLogKernelRemainder n N =
      ∫ p : ℝ × ℝ in openUnitSquare,
        originalLogKernelRemainderIntegrand n N p.1 p.2 := by
  rw [originalLogKernelRemainder_intervalIntegral_eq_iterated_Ioo n N]
  rw [openSquare_originalLogKernelRemainder_setIntegral_eq_iterated_Ioo hn N]

theorem openSquare_originalSondow_setIntegral_eq_iterated_Ioo
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ p : ℝ × ℝ in openUnitSquare,
        originalSondowIntegrand n p.1 p.2) =
      ∫ x : ℝ in Set.Ioo (0 : ℝ) 1,
        ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
          originalSondowIntegrand n x y := by
  unfold openUnitSquare
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact MeasureTheory.setIntegral_prod
    (fun p : ℝ × ℝ => originalSondowIntegrand n p.1 p.2)
    (by
      simpa [openSquareOriginalIntegrandIntegrableCertificate,
        MeasureTheory.IntegrableOn, openUnitSquareMeasure, openUnitSquare,
        MeasureTheory.Measure.volume_eq_prod] using
        (openSquareOriginalIntegrandIntegrableCertificate_holds hn))

theorem originalSondowIntegral_intervalIntegral_eq_iterated_Ioo (n : ℕ) :
    originalSondowIntegral n =
      ∫ x : ℝ in Set.Ioo (0 : ℝ) 1,
        ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
          originalSondowIntegrand n x y := by
  unfold originalSondowIntegral
  have hinner :
      (fun x : ℝ =>
        ∫ y in (0 : ℝ)..1, originalSondowIntegrand n x y) =
        fun x : ℝ =>
          ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
            originalSondowIntegrand n x y := by
    funext x
    rw [intervalIntegral.integral_of_le zero_le_one]
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hinner]
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem originalSondowIntegral_eq_openSquare_setIntegral
    {n : ℕ} (hn : 1 ≤ n) :
    originalSondowIntegral n =
      ∫ p : ℝ × ℝ in openUnitSquare,
        originalSondowIntegrand n p.1 p.2 := by
  rw [originalSondowIntegral_intervalIntegral_eq_iterated_Ioo n]
  rw [openSquare_originalSondow_setIntegral_eq_iterated_Ioo hn]

theorem openSquare_originalSondow_setIntegral_eq_logKernelFiniteSum_add_remainder
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    (∫ p : ℝ × ℝ in openUnitSquare,
        originalSondowIntegrand n p.1 p.2) =
      (∫ p : ℝ × ℝ in openUnitSquare,
        logKernelFiniteSum n N p.1 p.2) +
        ∫ p : ℝ × ℝ in openUnitSquare,
          originalLogKernelRemainderIntegrand n N p.1 p.2 := by
  calc
    (∫ p : ℝ × ℝ in openUnitSquare,
        originalSondowIntegrand n p.1 p.2)
        = ∫ p : ℝ × ℝ in openUnitSquare,
            logKernelFiniteSum n N p.1 p.2 +
              originalLogKernelRemainderIntegrand n N p.1 p.2 := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_openUnitSquare ?_
          intro p hp
          rcases hp with ⟨hx, hy⟩
          exact originalSondowIntegrand_eq_logKernelFiniteSum_add_remainder
            n N hx.1 hx.2 hy.1 hy.2
    _ = (∫ p : ℝ × ℝ in openUnitSquare,
          logKernelFiniteSum n N p.1 p.2) +
          ∫ p : ℝ × ℝ in openUnitSquare,
            originalLogKernelRemainderIntegrand n N p.1 p.2 := by
          rw [MeasureTheory.integral_add]
          · simpa [MeasureTheory.IntegrableOn] using
              openSquareLogKernelFiniteSumIntegrable (n := n) hn N
          · simpa [MeasureTheory.IntegrableOn] using
              openSquareOriginalLogKernelRemainderIntegrable (n := n) hn N

theorem originalSondowIntegral_eq_openSquare_logKernelFiniteSum_add_remainder
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    originalSondowIntegral n =
      (∫ p : ℝ × ℝ in openUnitSquare,
        logKernelFiniteSum n N p.1 p.2) +
        originalLogKernelRemainder n N := by
  calc
    originalSondowIntegral n
        = ∫ p : ℝ × ℝ in openUnitSquare,
            originalSondowIntegrand n p.1 p.2 := by
          rw [originalSondowIntegral_eq_openSquare_setIntegral hn]
    _ = (∫ p : ℝ × ℝ in openUnitSquare,
          logKernelFiniteSum n N p.1 p.2) +
          ∫ p : ℝ × ℝ in openUnitSquare,
            originalLogKernelRemainderIntegrand n N p.1 p.2 := by
          rw [openSquare_originalSondow_setIntegral_eq_logKernelFiniteSum_add_remainder hn N]
    _ = (∫ p : ℝ × ℝ in openUnitSquare,
          logKernelFiniteSum n N p.1 p.2) +
          originalLogKernelRemainder n N := by
          rw [originalLogKernelRemainder_eq_openSquare_setIntegral hn N]

/--
The remaining part of the integrated split after the open-square integral
linearity layer has been closed: identify the integral of the finite kernel
sum with the indexed moment expansion.
-/
def openSquareLogKernelFiniteSumMomentCertificate (n N : ℕ) : Prop :=
  (∫ p : ℝ × ℝ in openUnitSquare,
    logKernelFiniteSum n N p.1 p.2) =
    kernelIndexedMomentExpansion n N logKernelMoment

/--
Single-log-kernel open-square moment certificate: this is the local integrable
monomial statement needed to turn the finite kernel sum into the indexed moment
expansion.
-/
def openSquareLogKernelMomentCertificate (a b k : ℕ) : Prop :=
  MeasureTheory.IntegrableOn
    (fun p : ℝ × ℝ => logKernelMonomial a b k p.1 p.2)
    openUnitSquare ∧
  (∫ p : ℝ × ℝ in openUnitSquare,
    logKernelMonomial a b k p.1 p.2) =
    logKernelMoment a b k

theorem openSquareLogKernelMomentCertificate_of_integrable
    (a b k : ℕ)
    (hInt : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => logKernelMonomial a b k p.1 p.2)
      openUnitSquare) :
    openSquareLogKernelMomentCertificate a b k := by
  refine ⟨hInt, ?_⟩
  calc
    (∫ p : ℝ × ℝ in openUnitSquare,
      logKernelMonomial a b k p.1 p.2)
        = ∫ x : ℝ in Set.Ioo (0 : ℝ) 1,
            ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
              logKernelMonomial a b k x y := by
          unfold openUnitSquare
          rw [MeasureTheory.Measure.volume_eq_prod]
          exact MeasureTheory.setIntegral_prod
            (fun p : ℝ × ℝ => logKernelMonomial a b k p.1 p.2)
            (by
              simpa [openUnitSquare, MeasureTheory.Measure.volume_eq_prod] using hInt)
    _ = logKernelMoment a b k := by
          rw [logKernelMoment_intervalIntegral_eq_iterated_Ioo a b k]

theorem openSquareLogKernelMomentCertificate_holds (a b k : ℕ) :
    openSquareLogKernelMomentCertificate a b k :=
  openSquareLogKernelMomentCertificate_of_integrable a b k
    (logKernelMonomial_integrableOn_openUnitSquare a b k)

theorem openSquareLogKernelFiniteSumMomentCertificate_of_monomial
    (n N : ℕ)
    (hmono : ∀ a b k : ℕ, 1 ≤ k → openSquareLogKernelMomentCertificate a b k) :
    openSquareLogKernelFiniteSumMomentCertificate n N := by
  unfold openSquareLogKernelFiniteSumMomentCertificate
  unfold logKernelFiniteSum kernelIndexedMomentExpansion
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _hj
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hcert := hmono (n + i) (n + j) k hk1
        rw [MeasureTheory.integral_const_mul]
        rw [hcert.2]
      · intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hcert := hmono (n + i) (n + j) k hk1
        simpa [MeasureTheory.IntegrableOn] using
          hcert.1.const_mul (alternatingBinomial n i * alternatingBinomial n j)
    · intro j _hj
      apply MeasureTheory.integrable_finsetSum
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hcert := hmono (n + i) (n + j) k hk1
      simpa [MeasureTheory.IntegrableOn] using
        hcert.1.const_mul (alternatingBinomial n i * alternatingBinomial n j)
  · intro i _hi
    apply MeasureTheory.integrable_finsetSum
    intro j _hj
    apply MeasureTheory.integrable_finsetSum
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hcert := hmono (n + i) (n + j) k hk1
    simpa [MeasureTheory.IntegrableOn] using
      hcert.1.const_mul (alternatingBinomial n i * alternatingBinomial n j)

theorem openSquareLogKernelFiniteSumMomentCertificate_holds (n N : ℕ) :
    openSquareLogKernelFiniteSumMomentCertificate n N :=
  openSquareLogKernelFiniteSumMomentCertificate_of_monomial n N
    (fun a b k _hk => openSquareLogKernelMomentCertificate_holds a b k)

/--
Integrated form of `original_log_denominator_split_kernel_index`. This is kept
as a named certificate because it requires the remaining interval-integral
linearity/congruence and endpoint-null bookkeeping.
-/
def integratedOriginalSplitCertificate (n N : ℕ) : Prop :=
  originalSondowIntegral n =
    kernelIndexedMomentExpansion n N logKernelMoment +
      originalLogKernelRemainder n N

theorem integratedOriginalSplitCertificate_of_finiteSumMoment
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ)
    (hmoment : openSquareLogKernelFiniteSumMomentCertificate n N) :
    integratedOriginalSplitCertificate n N := by
  unfold integratedOriginalSplitCertificate
  rw [originalSondowIntegral_eq_openSquare_logKernelFiniteSum_add_remainder hn N]
  rw [hmoment]

theorem integratedOriginalSplitCertificate_holds
    {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    integratedOriginalSplitCertificate n N :=
  integratedOriginalSplitCertificate_of_finiteSumMoment hn N
    (openSquareLogKernelFiniteSumMomentCertificate_holds n N)

/-- The remaining analytic estimate: the original split remainder tends to zero. -/
def originalLogKernelRemainderVanishes (n : ℕ) : Prop :=
  Filter.Tendsto (fun N : ℕ => originalLogKernelRemainder n N)
    Filter.atTop (𝓝 (0 : ℝ))

theorem originalLogKernelRemainderVanishes_holds
    {n : ℕ} (hn : 1 ≤ n) :
    originalLogKernelRemainderVanishes n := by
  unfold originalLogKernelRemainderVanishes
  have h := openSquare_originalLogKernelRemainder_setIntegral_tendsto_zero hn
  refine h.congr' ?_
  exact Filter.Eventually.of_forall (fun N =>
    (originalLogKernelRemainder_eq_openSquare_setIntegral hn N).symm)

theorem logKernelFubiniCertificate_holds (a b k : ℕ) :
    logKernelFubiniCertificate a b k := by
  unfold logKernelFubiniCertificate
  letI : MeasureTheory.IsFiniteMeasure openUnitSquareMeasure :=
    openUnitSquareMeasure_isFinite
  let μt : MeasureTheory.Measure ℝ :=
    (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Ioi (0 : ℝ))
  let f : (ℝ × ℝ) × ℝ → ℝ :=
    fun q => kernelMomentMonomial a b k q.1.1 q.1.2 *
      (q.1.1 * q.1.2) ^ q.2
  have htriple : MeasureTheory.Integrable f (openUnitSquareMeasure.prod μt) := by
    simpa [f, μt] using logKernelLaplaceIntegrand_integrable_prod a b k
  have hlogSet :
      (∫ p : ℝ × ℝ in openUnitSquare,
        logKernelMonomial a b k p.1 p.2) =
        ∫ x : ℝ in Set.Ioo (0 : ℝ) 1,
          ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
            logKernelMonomial a b k x y := by
    unfold openUnitSquare
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact MeasureTheory.setIntegral_prod
      (fun p : ℝ × ℝ => logKernelMonomial a b k p.1 p.2)
      (by
        simpa [openUnitSquare, MeasureTheory.Measure.volume_eq_prod] using
          logKernelMonomial_integrableOn_openUnitSquare a b k)
  calc
    logKernelMoment a b k
        = ∫ p : ℝ × ℝ,
            logKernelMonomial a b k p.1 p.2 ∂openUnitSquareMeasure := by
          rw [logKernelMoment_intervalIntegral_eq_iterated_Ioo a b k]
          rw [← hlogSet]
          rfl
    _ = ∫ p : ℝ × ℝ,
          ∫ t : ℝ, f (p, t) ∂μt ∂openUnitSquareMeasure := by
          apply MeasureTheory.integral_congr_ae
          have hmem : ∀ᵐ p ∂openUnitSquareMeasure, p ∈ openUnitSquare := by
            simpa [openUnitSquareMeasure] using
              MeasureTheory.ae_restrict_mem measurableSet_openUnitSquare
          filter_upwards [hmem] with p hp
          rcases hp with ⟨hx, hy⟩
          simpa [f, μt] using
            logKernelMonomial_eq_laplace_integral a b k hx.1 hx.2 hy.1 hy.2
    _ = ∫ t : ℝ,
          ∫ p : ℝ × ℝ, f (p, t) ∂openUnitSquareMeasure ∂μt := by
          calc
            (∫ p : ℝ × ℝ,
              ∫ t : ℝ, f (p, t) ∂μt ∂openUnitSquareMeasure)
                = ∫ q : (ℝ × ℝ) × ℝ,
                    f q ∂openUnitSquareMeasure.prod μt := by
                  exact (MeasureTheory.integral_prod f htriple).symm
            _ = ∫ t : ℝ,
                  ∫ p : ℝ × ℝ,
                    f (p, t) ∂openUnitSquareMeasure ∂μt := by
                  exact MeasureTheory.integral_prod_symm f htriple
    _ = ∫ t : ℝ in Set.Ioi (0 : ℝ),
          (∫ x in (0 : ℝ)..1,
            ∫ y in (0 : ℝ)..1,
              kernelMomentMonomial a b k x y * (x * y) ^ t) := by
          apply MeasureTheory.integral_congr_ae
          have hslice := htriple.prod_left_ae
          filter_upwards [hslice] with t htint
          have htintOn : MeasureTheory.IntegrableOn
              (fun p : ℝ × ℝ => f (p, t)) openUnitSquare := by
            simpa [MeasureTheory.IntegrableOn, openUnitSquareMeasure] using htint
          have hprod :
              (∫ p : ℝ × ℝ in openUnitSquare, f (p, t)) =
                ∫ x : ℝ in Set.Ioo (0 : ℝ) 1,
                  ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
                    f ((x, y), t) := by
            unfold openUnitSquare
            rw [MeasureTheory.Measure.volume_eq_prod]
            exact MeasureTheory.setIntegral_prod
              (fun p : ℝ × ℝ => f (p, t))
              (by
                simpa [openUnitSquare, MeasureTheory.Measure.volume_eq_prod] using
                  htintOn)
          calc
            (∫ p : ℝ × ℝ, f (p, t) ∂openUnitSquareMeasure)
                = ∫ p : ℝ × ℝ in openUnitSquare, f (p, t) := by rfl
            _ = ∫ x : ℝ in Set.Ioo (0 : ℝ) 1,
                  ∫ y : ℝ in Set.Ioo (0 : ℝ) 1,
                    f ((x, y), t) := hprod
            _ = ∫ x in (0 : ℝ)..1,
                  ∫ y in (0 : ℝ)..1,
                    kernelMomentMonomial a b k x y * (x * y) ^ t := by
                  rw [← kernelMomentMonomial_mul_rpow_intervalIntegral_eq_iterated_Ioo
                    a b k t]

/--
Raw sidecar form of Sondow's explicit decomposition statement, before the main
library adapter identifies `rawLLogSum` and `diagonalAReal` with the published
`sondow_L` and rational `A_n` names.
-/
def rawSondowDecompositionTarget (n : ℕ) : Prop :=
  originalSondowIntegral n =
    (Nat.choose (2 * n) n : ℝ) * Real.eulerMascheroniConstant +
      rawLLogSum n - diagonalAReal n

/--
Final decomposition closure from the two remaining analytic certificates. This
shows that, after the Fubini/Tonelli family certificate and the integrated
split/remainder certificates, the original double integral has exactly the
raw Sondow decomposition constant already computed by the closed kernel-moment
chain.
-/
theorem rawSondowDecompositionTarget_of_certificates
    {n : ℕ} (hn : n ≠ 0)
    (hF : ∀ a b k : ℕ, 1 ≤ k → logKernelFubiniCertificate a b k)
    (hsplit : ∀ N : ℕ, integratedOriginalSplitCertificate n N)
    (hrem : originalLogKernelRemainderVanishes n) :
    rawSondowDecompositionTarget n := by
  let C : ℝ := (Nat.choose (2 * n) n : ℝ) * Real.eulerMascheroniConstant +
    rawLLogSum n - diagonalAReal n
  have hclosed :
      Filter.Tendsto (fun N : ℕ => closedKernelMomentExpansion n N)
        Filter.atTop (𝓝 C) := by
    simpa [C] using closedKernelMomentExpansion_tendsto_rawSondowConstant hn
  have hexp :
      Filter.Tendsto (fun N : ℕ => kernelIndexedMomentExpansion n N logKernelMoment)
        Filter.atTop (𝓝 C) := by
    refine hclosed.congr' ?_
    exact Filter.Eventually.of_forall (fun N =>
      (kernelIndexedMomentExpansion_logKernel_eq_closed_of_fubiniCertificate hF n N).symm)
  have hsum :
      Filter.Tendsto
        (fun N : ℕ => kernelIndexedMomentExpansion n N logKernelMoment +
          originalLogKernelRemainder n N)
        Filter.atTop (𝓝 (C + 0)) := by
    exact hexp.add hrem
  have hsumC :
      Filter.Tendsto
        (fun N : ℕ => kernelIndexedMomentExpansion n N logKernelMoment +
          originalLogKernelRemainder n N)
        Filter.atTop (𝓝 C) := by
    simpa using hsum
  have hI_to_C :
      Filter.Tendsto (fun _N : ℕ => originalSondowIntegral n)
        Filter.atTop (𝓝 C) := by
    refine hsumC.congr' ?_
    exact Filter.Eventually.of_forall (fun N => (hsplit N).symm)
  have hI_to_I :
      Filter.Tendsto (fun _N : ℕ => originalSondowIntegral n)
        Filter.atTop (𝓝 (originalSondowIntegral n)) :=
    tendsto_const_nhds
  have huniq := tendsto_nhds_unique hI_to_I hI_to_C
  simpa [rawSondowDecompositionTarget, C] using huniq

/--
Raw decomposition closure after internalizing the remainder-vanishing
certificate. The remaining external surface is exactly the Fubini/Tonelli
family certificate and the integrated finite-split certificate.
-/
theorem rawSondowDecompositionTarget_of_split_and_fubini
    {n : ℕ} (hn : 1 ≤ n)
    (hF : ∀ a b k : ℕ, 1 ≤ k → logKernelFubiniCertificate a b k)
    (hsplit : ∀ N : ℕ, integratedOriginalSplitCertificate n N) :
    rawSondowDecompositionTarget n := by
  exact rawSondowDecompositionTarget_of_certificates
    (n := n) (Nat.ne_of_gt hn) hF hsplit
    (originalLogKernelRemainderVanishes_holds hn)

/--
Raw decomposition closure after internalizing both the integrated finite split
and the remainder-vanishing certificate. The remaining analytic surface is
now exactly the Fubini/Tonelli family certificate for single log-kernel
moments.
-/
theorem rawSondowDecompositionTarget_of_fubini
    {n : ℕ} (hn : 1 ≤ n)
    (hF : ∀ a b k : ℕ, 1 ≤ k → logKernelFubiniCertificate a b k) :
    rawSondowDecompositionTarget n :=
  rawSondowDecompositionTarget_of_split_and_fubini hn hF
    (fun N => integratedOriginalSplitCertificate_holds hn N)

theorem rawSondowDecompositionTarget_holds
    {n : ℕ} (hn : 1 ≤ n) :
    rawSondowDecompositionTarget n :=
  rawSondowDecompositionTarget_of_fubini hn
    (fun a b k _hk => logKernelFubiniCertificate_holds a b k)

end

end EulerLimit.SondowDecomposition
