/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.SondowCoefficient

/-!
# Sondow product-log adapter targets

This module starts the final adapter from the finite coefficient certificate to
the product-log relation. It does not yet assert the main-library
`sondow_explicit_product_log_relation_prop`; it closes the coefficient-sum
layer that both the logarithm of the product and `d(2*n) * L_n` must reduce to.
-/

namespace EulerLimit.SondowProductLog

open BigOperators

noncomputable section

open EulerLimit.SondowCoefficient

/-- The real logarithmic sum read from the explicit product coefficients. -/
def productCoefficientLogSum (scale n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n,
    (scale : ℝ) * (coeffFromProduct n k : ℝ) *
      Real.log ((n + k : ℕ) : ℝ)

/-- The real logarithmic sum read from Sondow's alternating `L_n` coefficients. -/
def alternatingCoefficientLogSum (scale n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n,
    (scale : ℝ) * (coeffFromAlternating n k : ℝ) *
      Real.log ((n + k : ℕ) : ℝ)

/-- The real form of the alternating coefficient term in Sondow's `L_n`. -/
def alternatingTermReal (n i j : ℕ) : ℝ :=
  (((-1 : ℝ) ^ (i + j - 1)) / (((j - i : ℕ) : ℝ))) *
    (Nat.choose n i : ℝ) * (Nat.choose n j : ℝ)

/--
The `L_n` logarithmic sum after grouping all terms by the logarithmic basis
`Real.log (n+k)`.
-/
def groupedLLogSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n,
    (2 * ∑ i ∈ Finset.range k,
      ∑ j ∈ Finset.Icc k n, alternatingTermReal n i j) *
        Real.log ((n + k : ℕ) : ℝ)

/-- The explicit triple-sum shape of Sondow's `L_n`, copied into the sidecar. -/
def rawLLogSum (n : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range (n + 1),
    ∑ j ∈ (Finset.range (n + 1)).filter (fun j => i < j),
      ∑ r ∈ Finset.Icc 1 (j - i),
        alternatingTermReal n i j * Real.log ((n + i + r : ℕ) : ℝ)

/--
The same raw `L_n` sum after the inner change of variables `k = i + r`, but
before exchanging the outer finite sums.
-/
def reindexedLLogSum (n : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range (n + 1),
    ∑ j ∈ Finset.Icc (i + 1) n,
      ∑ k ∈ Finset.Icc (i + 1) j,
        alternatingTermReal n i j * Real.log ((n + k : ℕ) : ℝ)

/-- A generic finite product of powers over the logarithmic basis `n+k`. -/
def finitePowerProduct (n : ℕ) (exponent : ℕ → ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 1 n, (n + k) ^ exponent k

theorem range_filter_lt_eq_Icc_succ (i n : ℕ) :
    (Finset.range (n + 1)).filter (fun j => i < j) =
      Finset.Icc (i + 1) n := by
  ext j
  constructor
  · intro hj
    have hj' := Finset.mem_filter.mp hj
    have hj_range : j < n + 1 := Finset.mem_range.mp hj'.1
    have hij : i < j := hj'.2
    exact Finset.mem_Icc.mpr (by omega)
  · intro hj
    have hjI : i + 1 ≤ j ∧ j ≤ n := Finset.mem_Icc.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩

theorem sum_Icc_one_sub_eq_sum_Icc_succ
    {M : Type} [AddCommMonoid M] (f : ℕ → M) {i j : ℕ}
    (hij : i ≤ j) :
    ∑ r ∈ Finset.Icc 1 (j - i), f (i + r) =
      ∑ k ∈ Finset.Icc (i + 1) j, f k := by
  refine Finset.sum_bij'
    (s := Finset.Icc 1 (j - i)) (t := Finset.Icc (i + 1) j)
    (f := fun r => f (i + r)) (g := fun k => f k)
    (fun r _hr => i + r) (fun k _hk => k - i) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    have hmem : 1 ≤ r ∧ r ≤ j - i := Finset.mem_Icc.mp hr
    exact Finset.mem_Icc.mpr (by omega)
  · intro k hk
    have hmem : i + 1 ≤ k ∧ k ≤ j := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr (by omega)
  · intro r hr
    have hmem : 1 ≤ r ∧ r ≤ j - i := Finset.mem_Icc.mp hr
    omega
  · intro k hk
    have hmem : i + 1 ≤ k ∧ k ≤ j := Finset.mem_Icc.mp hk
    omega
  · intro r _hr
    rfl

/--
The local divisibility hypothesis needed to read Sondow's product exponents as
the common scale times rational reciprocal coefficients.
-/
def denominatorCancelsFor (scale n : ℕ) : Prop :=
  ∀ ⦃i j : ℕ⦄, j ∈ Finset.Icc (i + 1) (n - i) →
    j * ((2 * scale) / j) = 2 * scale

/-- The exponent of the basis factor `n+k` in the normalized Sondow product. -/
def productExponent (scale n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (Nat.min (k - 1) (n - k) + 1),
    ∑ j ∈ Finset.Icc (i + 1) (n - i),
      ((2 * scale) / j) * (Nat.choose n i) ^ 2

/--
The normalized product side of Sondow's product-log identity. In the main
library this specializes to `sondow_S_explicit n` with `scale = d (2*n)`.
-/
def sondowProductNormalized (scale n : ℕ) : ℕ :=
  finitePowerProduct n (productExponent scale n)

/--
The nested product shape used by the main-library `sondow_S_explicit`, with the
common scale kept abstract.
-/
def nestedSondowProductNormalized (scale n : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 1 n,
    ∏ i ∈ Finset.range (Nat.min (k - 1) (n - k) + 1),
      ∏ j ∈ Finset.Icc (i + 1) (n - i),
        (n + k) ^ (((2 * scale) / j) * (Nat.choose n i) ^ 2)

theorem finitePowerProduct_pos (n : ℕ) (exponent : ℕ → ℕ) :
    0 < finitePowerProduct n exponent := by
  unfold finitePowerProduct
  refine Finset.prod_pos ?_
  intro k hk
  exact pow_pos (Nat.add_pos_right n (Finset.mem_Icc.mp hk).1) _

/--
Logarithm expansion for a finite product of natural powers. This is the generic
`Real.log_prod`/`Real.log_pow` brick needed by the Sondow product-log adapter.
-/
theorem log_finitePowerProduct (n : ℕ) (exponent : ℕ → ℕ) :
    Real.log (finitePowerProduct n exponent : ℝ) =
      ∑ k ∈ Finset.Icc 1 n,
        (exponent k : ℝ) * Real.log ((n + k : ℕ) : ℝ) := by
  unfold finitePowerProduct
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro k _hk
    rw [Nat.cast_pow, Real.log_pow]
  · intro k hk
    exact_mod_cast
      Nat.ne_of_gt (pow_pos (Nat.add_pos_right n (Finset.mem_Icc.mp hk).1) (exponent k))

theorem nestedSondowProductNormalized_eq_sondowProductNormalized
    (scale n : ℕ) :
    nestedSondowProductNormalized scale n =
      sondowProductNormalized scale n := by
  unfold nestedSondowProductNormalized sondowProductNormalized finitePowerProduct productExponent
  apply Finset.prod_congr rfl
  intro k _hk
  calc
    (∏ i ∈ Finset.range (Nat.min (k - 1) (n - k) + 1),
        ∏ j ∈ Finset.Icc (i + 1) (n - i),
          (n + k) ^ (((2 * scale) / j) * (Nat.choose n i) ^ 2))
        =
          ∏ i ∈ Finset.range (Nat.min (k - 1) (n - k) + 1),
            (n + k) ^
              ∑ j ∈ Finset.Icc (i + 1) (n - i),
                ((2 * scale) / j) * (Nat.choose n i) ^ 2 := by
            apply Finset.prod_congr rfl
            intro i _hi
            rw [Finset.prod_pow_eq_pow_sum]
    _ = (n + k) ^
          ∑ i ∈ Finset.range (Nat.min (k - 1) (n - k) + 1),
            ∑ j ∈ Finset.Icc (i + 1) (n - i),
              ((2 * scale) / j) * (Nat.choose n i) ^ 2 := by
        rw [Finset.prod_pow_eq_pow_sum]

theorem denominatorCancel_cast_inv {scale n i j : ℕ}
    (hcancel : denominatorCancelsFor scale n)
    (hj : j ∈ Finset.Icc (i + 1) (n - i)) :
    (((2 * scale) / j : ℕ) : ℝ) =
      (2 : ℝ) * (scale : ℝ) * ((j : ℝ)⁻¹) := by
  have hj_pos : 0 < j := by
    have hj_low := (Finset.mem_Icc.mp hj).1
    omega
  have hj_ne : (j : ℝ) ≠ 0 := by positivity
  have hmul : (j : ℝ) * (((2 * scale) / j : ℕ) : ℝ) =
      ((2 * scale : ℕ) : ℝ) := by
    exact_mod_cast hcancel hj
  calc
    (((2 * scale) / j : ℕ) : ℝ)
        = ((j : ℝ) * (((2 * scale) / j : ℕ) : ℝ)) * ((j : ℝ)⁻¹) := by
            field_simp [hj_ne]
    _ = ((2 * scale : ℕ) : ℝ) * ((j : ℝ)⁻¹) := by rw [hmul]
    _ = (2 : ℝ) * (scale : ℝ) * ((j : ℝ)⁻¹) := by
        norm_num [Nat.cast_mul, mul_assoc]

theorem productExponent_cast_eq {scale n k : ℕ}
    (hcancel : denominatorCancelsFor scale n) :
    (productExponent scale n k : ℝ) =
      (scale : ℝ) * (coeffFromProduct n k : ℝ) := by
  unfold productExponent coeffFromProduct
  push_cast
  rw [← mul_assoc, mul_comm (scale : ℝ) (2 : ℝ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← mul_assoc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [denominatorCancel_cast_inv hcancel hj]
  ring

theorem log_sondowProductNormalized_eq_productCoefficientLogSum
    {scale n : ℕ} (hcancel : denominatorCancelsFor scale n) :
    Real.log (sondowProductNormalized scale n : ℝ) =
      productCoefficientLogSum scale n := by
  unfold sondowProductNormalized productCoefficientLogSum
  rw [log_finitePowerProduct]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [productExponent_cast_eq hcancel]

theorem coeffFromProduct_eq_coeffFromAlternating_real
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (coeffFromProduct n k : ℝ) = (coeffFromAlternating n k : ℝ) := by
  have hcert := coefficientCertificateTarget_holds n k hk hkn
  have hq : coeffFromAlternating n k = coeffFromProduct n k :=
    hcert.1.trans hcert.2
  exact_mod_cast hq.symm

theorem alternatingTerm_cast_real (n i j : ℕ) :
    (alternatingTerm n i j : ℝ) = alternatingTermReal n i j := by
  unfold alternatingTerm alternatingTermReal
  norm_num [Rat.cast_div]
  ring

theorem coeffFromAlternating_cast_real (n k : ℕ) :
    (coeffFromAlternating n k : ℝ) =
      2 * ∑ i ∈ Finset.range k,
        ∑ j ∈ Finset.Icc k n, alternatingTermReal n i j := by
  unfold coeffFromAlternating
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  exact alternatingTerm_cast_real n i j

theorem rawInnerLLogSum_eq_reindexedInner
    (n i j : ℕ) (hij : i ≤ j) :
    ∑ r ∈ Finset.Icc 1 (j - i),
      alternatingTermReal n i j * Real.log ((n + i + r : ℕ) : ℝ) =
    ∑ k ∈ Finset.Icc (i + 1) j,
      alternatingTermReal n i j * Real.log ((n + k : ℕ) : ℝ) := by
  simpa [Nat.add_assoc] using
    (sum_Icc_one_sub_eq_sum_Icc_succ
      (f := fun k => alternatingTermReal n i j * Real.log ((n + k : ℕ) : ℝ))
      (i := i) (j := j) hij)

theorem rawLLogSum_eq_reindexedLLogSum (n : ℕ) :
    rawLLogSum n = reindexedLLogSum n := by
  unfold rawLLogSum reindexedLLogSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  rw [range_filter_lt_eq_Icc_succ]
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i ≤ j := by
    have hjI := Finset.mem_Icc.mp hj
    omega
  rw [rawInnerLLogSum_eq_reindexedInner n i j hij]

theorem triple_sum_reindex_i_j_k_to_k_i_j
    (n : ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1),
      ∑ j ∈ Finset.Icc (i + 1) n,
        ∑ k ∈ Finset.Icc (i + 1) j, F i j k) =
    ∑ k ∈ Finset.Icc 1 n,
      ∑ i ∈ Finset.range k,
        ∑ j ∈ Finset.Icc k n, F i j k := by
  let A : Finset (Sigma fun _i : ℕ => Sigma fun _j : ℕ => ℕ) :=
    (Finset.range (n + 1)).sigma (fun i =>
      (Finset.Icc (i + 1) n).sigma (fun j => Finset.Icc (i + 1) j))
  let B : Finset (Sigma fun _k : ℕ => Sigma fun _i : ℕ => ℕ) :=
    (Finset.Icc 1 n).sigma (fun k =>
      (Finset.range k).sigma (fun i => Finset.Icc k n))
  have hA :
      (∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.Icc (i + 1) n,
          ∑ k ∈ Finset.Icc (i + 1) j, F i j k) =
      ∑ x ∈ A, F x.1 x.2.1 x.2.2 := by
    simp [A, Finset.sum_sigma]
  have hB :
      (∑ k ∈ Finset.Icc 1 n,
        ∑ i ∈ Finset.range k,
          ∑ j ∈ Finset.Icc k n, F i j k) =
      ∑ x ∈ B, F x.2.1 x.2.2 x.1 := by
    simp [B, Finset.sum_sigma]
  rw [hA, hB]
  refine Finset.sum_bij'
    (s := A) (t := B)
    (f := fun x => F x.1 x.2.1 x.2.2)
    (g := fun x => F x.2.1 x.2.2 x.1)
    (fun x _hx => ⟨x.2.2, ⟨x.1, x.2.1⟩⟩)
    (fun x _hx => ⟨x.2.1, ⟨x.2.2, x.1⟩⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    have hxA := Finset.mem_sigma.mp hx
    rcases hxA with ⟨hi, hx2⟩
    have hx2' := Finset.mem_sigma.mp hx2
    rcases hx2' with ⟨hj, hk⟩
    have hi_range : x.1 < n + 1 := Finset.mem_range.mp hi
    have hjI : x.1 + 1 ≤ x.2.1 ∧ x.2.1 ≤ n := Finset.mem_Icc.mp hj
    have hkI : x.1 + 1 ≤ x.2.2 ∧ x.2.2 ≤ x.2.1 := Finset.mem_Icc.mp hk
    have h1 : x.2.2 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr (by omega)
    have h2 : x.1 ∈ Finset.range x.2.2 := Finset.mem_range.mpr (by omega)
    have h3 : x.2.1 ∈ Finset.Icc x.2.2 n := Finset.mem_Icc.mpr (by omega)
    simp [B, h1, h2, h3]
  · intro x hx
    have hxB := Finset.mem_sigma.mp hx
    rcases hxB with ⟨hk, hx2⟩
    have hx2' := Finset.mem_sigma.mp hx2
    rcases hx2' with ⟨hi, hj⟩
    have hkI : 1 ≤ x.1 ∧ x.1 ≤ n := Finset.mem_Icc.mp hk
    have hi_range : x.2.1 < x.1 := Finset.mem_range.mp hi
    have hjI : x.1 ≤ x.2.2 ∧ x.2.2 ≤ n := Finset.mem_Icc.mp hj
    have h1 : x.2.1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have h2 : x.2.2 ∈ Finset.Icc (x.2.1 + 1) n := Finset.mem_Icc.mpr (by omega)
    have h3 : x.1 ∈ Finset.Icc (x.2.1 + 1) x.2.2 :=
      Finset.mem_Icc.mpr (by omega)
    simp [A, h1, h2, h3]
  · intro x _hx
    rfl
  · intro x _hx
    rfl
  · intro x _hx
    rfl

theorem reindexedLLogSum_eq_groupedLLogSum (n : ℕ) :
    reindexedLLogSum n = groupedLLogSum n := by
  unfold reindexedLLogSum groupedLLogSum
  rw [triple_sum_reindex_i_j_k_to_k_i_j]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  have hfactor :
      (∑ i ∈ Finset.range k,
        ∑ j ∈ Finset.Icc k n,
          alternatingTermReal n i j * Real.log ((n + k : ℕ) : ℝ)) =
      (∑ i ∈ Finset.range k,
        ∑ j ∈ Finset.Icc k n,
          alternatingTermReal n i j) * Real.log ((n + k : ℕ) : ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_mul]
  rw [hfactor]
  ring

theorem rawLLogSum_eq_groupedLLogSum (n : ℕ) :
    rawLLogSum n = groupedLLogSum n := by
  rw [rawLLogSum_eq_reindexedLLogSum, reindexedLLogSum_eq_groupedLLogSum]

/--
The finite coefficient certificate after embedding in the real logarithmic
basis. This is the coefficient-equality core of the final product-log adapter.
-/
theorem productCoefficientLogSum_eq_alternatingCoefficientLogSum
    (scale n : ℕ) :
    productCoefficientLogSum scale n =
      alternatingCoefficientLogSum scale n := by
  unfold productCoefficientLogSum alternatingCoefficientLogSum
  apply Finset.sum_congr rfl
  intro k hk_mem
  have hk : 1 ≤ k := (Finset.mem_Icc.mp hk_mem).1
  have hkn : k ≤ n := (Finset.mem_Icc.mp hk_mem).2
  rw [coeffFromProduct_eq_coeffFromAlternating_real hk hkn]

theorem scale_groupedLLogSum_eq_alternatingCoefficientLogSum
    (scale n : ℕ) :
    (scale : ℝ) * groupedLLogSum n =
      alternatingCoefficientLogSum scale n := by
  unfold groupedLLogSum alternatingCoefficientLogSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [coeffFromAlternating_cast_real]
  ring

theorem scale_rawLLogSum_eq_alternatingCoefficientLogSum
    (scale n : ℕ) :
    (scale : ℝ) * rawLLogSum n =
      alternatingCoefficientLogSum scale n := by
  rw [rawLLogSum_eq_groupedLLogSum]
  exact scale_groupedLLogSum_eq_alternatingCoefficientLogSum scale n

/--
Product-side expansion plus the finite coefficient certificate, stated for the
summed-exponent normalized product.
-/
theorem log_sondowProductNormalized_eq_alternatingCoefficientLogSum
    {scale n : ℕ} (hcancel : denominatorCancelsFor scale n) :
    Real.log (sondowProductNormalized scale n : ℝ) =
      alternatingCoefficientLogSum scale n := by
  rw [log_sondowProductNormalized_eq_productCoefficientLogSum hcancel]
  rw [productCoefficientLogSum_eq_alternatingCoefficientLogSum]

/--
The same product-log result, stated for the nested product shape matching
`sondow_S_explicit`.
-/
theorem log_nestedSondowProductNormalized_eq_alternatingCoefficientLogSum
    {scale n : ℕ} (hcancel : denominatorCancelsFor scale n) :
    Real.log (nestedSondowProductNormalized scale n : ℝ) =
      alternatingCoefficientLogSum scale n := by
  rw [nestedSondowProductNormalized_eq_sondowProductNormalized]
  exact log_sondowProductNormalized_eq_alternatingCoefficientLogSum hcancel

/--
The sidecar product-log theorem with both sides in Sondow's concrete shapes:
the nested product and the raw triple-sum `L_n`.
-/
theorem log_nestedSondowProductNormalized_eq_scale_rawLLogSum
    {scale n : ℕ} (hcancel : denominatorCancelsFor scale n) :
    Real.log (nestedSondowProductNormalized scale n : ℝ) =
      (scale : ℝ) * rawLLogSum n := by
  rw [log_nestedSondowProductNormalized_eq_alternatingCoefficientLogSum hcancel]
  rw [← scale_rawLLogSum_eq_alternatingCoefficientLogSum]

end

end EulerLimit.SondowProductLog
