/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import Mathlib

/-!
# Sondow product-log coefficient targets

Definitions for the finite coefficient certificate used to prove the
Sondow product-log relation without directly formalizing the prose of the
appendix.
-/

namespace EulerLimit.SondowCoefficient

open BigOperators

noncomputable section

/-- Harmonic numbers in `ℚ`, indexed by the upper endpoint. -/
def harmonicRat (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, (k : ℚ)⁻¹

theorem harmonicRat_eq_harmonic (n : ℕ) : harmonicRat n = harmonic n := by
  simp [harmonicRat, harmonic_eq_sum_Icc]

theorem harmonicRat_succ (n : ℕ) :
    harmonicRat (n + 1) = harmonicRat n + (((n + 1 : ℕ) : ℚ)⁻¹) := by
  rw [harmonicRat_eq_harmonic, harmonicRat_eq_harmonic, harmonic_succ]

theorem harmonicRat_sub_eq_sum_Icc {i m : ℕ} (h : i ≤ m) :
    harmonicRat m - harmonicRat i = ∑ j ∈ Finset.Icc (i + 1) m, (j : ℚ)⁻¹ := by
  rw [harmonicRat_eq_harmonic, harmonicRat_eq_harmonic]
  induction m with
  | zero =>
      have hi : i = 0 := Nat.le_zero.mp h
      simp [hi]
  | succ m ih =>
      by_cases hi : i ≤ m
      · have hsum := Finset.sum_Icc_succ_top (a := i + 1) (b := m)
          (by omega : i + 1 ≤ m + 1) (fun j : ℕ => (j : ℚ)⁻¹)
        rw [hsum]
        rw [harmonic_succ]
        calc
          harmonic m + ((m + 1 : ℕ) : ℚ)⁻¹ - harmonic i
              = (harmonic m - harmonic i) + ((m + 1 : ℕ) : ℚ)⁻¹ := by ring
          _ = (∑ j ∈ Finset.Icc (i + 1) m, (j : ℚ)⁻¹) +
                ((m + 1 : ℕ) : ℚ)⁻¹ := by
              rw [ih hi]
      · have him : i = m + 1 := by omega
        simp [him]

theorem harmonicRat_sub_eq_reciprocal_sum {n i : ℕ} (h : i ≤ n - i) :
    harmonicRat (n - i) - harmonicRat i =
      ∑ j ∈ Finset.Icc (i + 1) (n - i), (j : ℚ)⁻¹ := by
  exact harmonicRat_sub_eq_sum_Icc h

theorem sum_Icc_succ_left {M : Type} [AddCommMonoid M] (f : ℕ → M)
    {k n : ℕ} (hkn : k ≤ n) :
    ∑ j ∈ Finset.Icc k n, f j = f k + ∑ j ∈ Finset.Icc (k + 1) n, f j := by
  have hinsert : insert k (Finset.Icc (k + 1) n) = Finset.Icc k n := by
    simpa using (Finset.insert_Icc_succ_left_eq_Icc (a := k) (b := n) hkn)
  rw [← hinsert]
  exact Finset.sum_insert (by simp)

noncomputable def alternatingTerm (n i j : ℕ) : ℚ :=
  ((-1 : ℚ) ^ (i + j - 1) *
    (Nat.choose n i : ℚ) * (Nat.choose n j : ℚ)) /
      (((j - i : ℕ) : ℚ))

noncomputable def alternatingBoundary (n k : ℕ) : ℚ :=
  (∑ j ∈ Finset.Icc (k + 1) n, alternatingTerm n k j) -
    (∑ i ∈ Finset.range k, alternatingTerm n i k)

theorem sum_Icc_one_eq_sum_range_succ {M : Type} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, f j = ∑ r ∈ Finset.range n, f (r + 1) := by
  refine Finset.sum_bij'
    (s := Finset.Icc 1 n) (t := Finset.range n)
    (f := f) (g := fun r => f (r + 1))
    (fun j _hj => j - 1) (fun r _hr => r + 1) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    have hmem : 1 ≤ j ∧ j ≤ n := Finset.mem_Icc.mp hj
    exact Finset.mem_range.mpr (by omega)
  · intro r hr
    have hlt : r < n := Finset.mem_range.mp hr
    exact Finset.mem_Icc.mpr (by omega)
  · intro j hj
    have hmem : 1 ≤ j ∧ j ≤ n := Finset.mem_Icc.mp hj
    omega
  · intro r hr
    have hlt : r < n := Finset.mem_range.mp hr
    omega
  · intro j hj
    have hmem : 1 ≤ j ∧ j ≤ n := Finset.mem_Icc.mp hj
    congr 1
    omega

theorem choose_div_succ_eq_choose_succ_div (n r : ℕ) :
    ((Nat.choose n r : ℚ) / ((r + 1 : ℕ) : ℚ)) =
      ((Nat.choose (n + 1) (r + 1) : ℚ) / ((n + 1 : ℕ) : ℚ)) := by
  have hnat := Nat.add_one_mul_choose_eq n r
  have hq : ((n + 1 : ℕ) : ℚ) * (Nat.choose n r : ℚ) =
      (Nat.choose (n + 1) (r + 1) : ℚ) * ((r + 1 : ℕ) : ℚ) := by
    exact_mod_cast hnat
  have hnz : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hrz : ((r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp [hnz, hrz]
  linarith

theorem alternating_choose_shift_sum (n : ℕ) :
    ∑ r ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ r * (Nat.choose (n + 1) (r + 1) : ℚ) = 1 := by
  have hfullZ := Int.alternating_sum_range_choose_of_ne (n := n + 1) (by omega)
  have hfullQ :
      (∑ m ∈ Finset.range (n + 1 + 1),
        (-1 : ℚ) ^ m * (Nat.choose (n + 1) m : ℚ)) = 0 := by
    exact_mod_cast hfullZ
  rw [Finset.sum_range_succ'] at hfullQ
  have hfullQ' :
      (∑ r ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (r + 1) * (Nat.choose (n + 1) (r + 1) : ℚ)) + 1 = 0 := by
    simpa using hfullQ
  have hneg :
      (∑ r ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (r + 1) * (Nat.choose (n + 1) (r + 1) : ℚ)) = -1 := by
    linarith
  have hsign :
      (∑ r ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (r + 1) * (Nat.choose (n + 1) (r + 1) : ℚ)) =
      - (∑ r ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ r * (Nat.choose (n + 1) (r + 1) : ℚ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [pow_succ]
    ring
  rw [hsign] at hneg
  linarith

theorem alternating_choose_div_succ_sum (n : ℕ) :
    ∑ r ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ r * ((Nat.choose n r : ℚ) / ((r + 1 : ℕ) : ℚ)) =
        1 / ((n + 1 : ℕ) : ℚ) := by
  have hconv :
      ∑ r ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ r * ((Nat.choose n r : ℚ) / ((r + 1 : ℕ) : ℚ)) =
      (1 / ((n + 1 : ℕ) : ℚ)) *
        ∑ r ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ r * (Nat.choose (n + 1) (r + 1) : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [choose_div_succ_eq_choose_succ_div]
    ring
  rw [hconv, alternating_choose_shift_sum]
  ring

theorem alternating_choose_succ_div_sum_eq_harmonic (n : ℕ) :
    ∑ r ∈ Finset.range n,
      (-1 : ℚ) ^ r * ((Nat.choose n (r + 1) : ℚ) / ((r + 1 : ℕ) : ℚ)) =
        harmonicRat n := by
  induction n with
  | zero =>
      simp [harmonicRat]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hsplit : ∀ r : ℕ,
          (-1 : ℚ) ^ r *
              ((Nat.choose (n + 1) (r + 1) : ℚ) / ((r + 1 : ℕ) : ℚ)) =
            (-1 : ℚ) ^ r *
                ((Nat.choose n (r + 1) : ℚ) / ((r + 1 : ℕ) : ℚ)) +
              (-1 : ℚ) ^ r *
                ((Nat.choose n r : ℚ) / ((r + 1 : ℕ) : ℚ)) := by
        intro r
        rw [Nat.choose_succ_succ]
        norm_num [Nat.cast_add]
        ring
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
      rw [ih]
      have hzero :
          (-1 : ℚ) ^ n * ((Nat.choose n (n + 1) : ℚ) / ((n + 1 : ℕ) : ℚ)) = 0 := by
        simp
      rw [hzero]
      simp only [zero_add]
      have htail :
          (∑ x ∈ Finset.range n,
              (-1 : ℚ) ^ x * ((Nat.choose n x : ℚ) / ((x + 1 : ℕ) : ℚ))) +
            (-1 : ℚ) ^ n * ((Nat.choose n n : ℚ) / ((n + 1 : ℕ) : ℚ)) =
          ∑ x ∈ Finset.range (n + 1),
              (-1 : ℚ) ^ x * ((Nat.choose n x : ℚ) / ((x + 1 : ℕ) : ℚ)) := by
        rw [Finset.sum_range_succ]
      rw [add_assoc]
      rw [htail]
      rw [alternating_choose_div_succ_sum n]
      rw [harmonicRat_eq_harmonic (n + 1)]
      rw [harmonic_succ]
      rw [harmonicRat_eq_harmonic n]
      ring

/--
Coefficient of `log (n + k)` coming from the alternating double-sum form of
Sondow's logarithmic term.
-/
def coeffFromAlternating (n k : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range k,
    ∑ j ∈ Finset.Icc k n,
      alternatingTerm n i j

/--
Coefficient of `log (n + k)` after applying Sondow's square-binomial harmonic
coefficient identity.
-/
def coeffFromSquareHarmonic (n k : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range k,
    (Nat.choose n i : ℚ) ^ 2 * (harmonicRat (n - i) - harmonicRat i)

/--
Coefficient of `log (n + k)` read from the explicit product after dividing out
the common factor `d(2*n)`.
-/
def coeffFromProduct (n k : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range (Nat.min (k - 1) (n - k) + 1),
    (Nat.choose n i : ℚ) ^ 2 *
      ∑ j ∈ Finset.Icc (i + 1) (n - i), (j : ℚ)⁻¹

noncomputable def squareHarmonicTerm (n i : ℕ) : ℚ :=
  (Nat.choose n i : ℚ) ^ 2 * (harmonicRat (n - i) - harmonicRat i)

theorem squareHarmonicTerm_reflect {n i : ℕ} (hi : i ≤ n) :
    squareHarmonicTerm n (n - i) = -squareHarmonicTerm n i := by
  unfold squareHarmonicTerm
  have hchoose : Nat.choose n (n - i) = Nat.choose n i := Nat.choose_symm hi
  have hsub : n - (n - i) = i := Nat.sub_sub_self hi
  rw [hchoose, hsub]
  ring

theorem squareHarmonicTerm_tail_sum_zero {n k : ℕ} (hk : k ≤ n) :
    ∑ i ∈ Finset.Icc (n - k + 1) (k - 1), squareHarmonicTerm n i = 0 := by
  classical
  let s := Finset.Icc (n - k + 1) (k - 1)
  let f := squareHarmonicTerm n
  change ∑ i ∈ s, f i = 0
  apply Finset.sum_involution (s := s) (f := f) (g := fun a _ha => n - a)
  · intro a ha
    have haI : a ∈ Finset.Icc (n - k + 1) (k - 1) := ha
    have ha_le_n : a ≤ n := by
      have hau := (Finset.mem_Icc.mp haI).2
      omega
    have href := squareHarmonicTerm_reflect (n := n) (i := a) ha_le_n
    change squareHarmonicTerm n a + squareHarmonicTerm n (n - a) = 0
    rw [href]
    ring
  · intro a ha hnonzero hfix
    have haI : a ∈ Finset.Icc (n - k + 1) (k - 1) := ha
    have ha_le_n : a ≤ n := by
      have hau := (Finset.mem_Icc.mp haI).2
      omega
    have href := squareHarmonicTerm_reflect (n := n) (i := a) ha_le_n
    have hz : squareHarmonicTerm n a = 0 := by
      rw [hfix] at href
      linarith
    exact hnonzero hz
  · intro a ha
    have haI : a ∈ Finset.Icc (n - k + 1) (k - 1) := ha
    have hal := (Finset.mem_Icc.mp haI).1
    have hau := (Finset.mem_Icc.mp haI).2
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro a ha
    have haI : a ∈ Finset.Icc (n - k + 1) (k - 1) := ha
    have hau := (Finset.mem_Icc.mp haI).2
    have ha_le_n : a ≤ n := by omega
    exact Nat.sub_sub_self ha_le_n

theorem coeffFromAlternating_succ {n k : ℕ} (hkn : k < n) :
    coeffFromAlternating n (k + 1) =
      coeffFromAlternating n k + 2 * alternatingBoundary n k := by
  have hkn_le : k ≤ n := Nat.le_of_lt hkn
  unfold coeffFromAlternating alternatingTerm alternatingBoundary
  rw [Finset.sum_range_succ]
  have hsplit : ∀ i : ℕ,
      ∑ j ∈ Finset.Icc k n,
        ((-1 : ℚ) ^ (i + j - 1) *
          (Nat.choose n i : ℚ) * (Nat.choose n j : ℚ)) / ((j - i : ℕ) : ℚ)
      =
        ((-1 : ℚ) ^ (i + k - 1) *
          (Nat.choose n i : ℚ) * (Nat.choose n k : ℚ)) / ((k - i : ℕ) : ℚ)
        + ∑ j ∈ Finset.Icc (k + 1) n,
          ((-1 : ℚ) ^ (i + j - 1) *
            (Nat.choose n i : ℚ) * (Nat.choose n j : ℚ)) / ((j - i : ℕ) : ℚ) := by
    intro i
    exact sum_Icc_succ_left
      (fun j : ℕ =>
        ((-1 : ℚ) ^ (i + j - 1) *
          (Nat.choose n i : ℚ) * (Nat.choose n j : ℚ)) / ((j - i : ℕ) : ℚ))
      hkn_le
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp [alternatingTerm]
  ring_nf

theorem coeffFromSquareHarmonic_succ (n k : ℕ) :
    coeffFromSquareHarmonic n (k + 1) =
      coeffFromSquareHarmonic n k + 2 * squareHarmonicTerm n k := by
  unfold coeffFromSquareHarmonic squareHarmonicTerm
  rw [Finset.sum_range_succ]
  ring

theorem coeffFromSquareHarmonic_eq_coeffFromProduct_left {n k : ℕ}
    (hk : 1 ≤ k) (hleft : k - 1 ≤ n - k) :
    coeffFromSquareHarmonic n k = coeffFromProduct n k := by
  unfold coeffFromSquareHarmonic coeffFromProduct
  have hmin : Nat.min (k - 1) (n - k) = k - 1 := Nat.min_eq_left hleft
  rw [hmin]
  have hksub : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hksub]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi_lt : i < k := Finset.mem_range.mp hi
  have hi_le : i ≤ n - i := by omega
  rw [harmonicRat_sub_eq_reciprocal_sum hi_le]

theorem coeffFromSquareHarmonic_eq_coeffFromProduct {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    coeffFromSquareHarmonic n k = coeffFromProduct n k := by
  by_cases hleft : k - 1 ≤ n - k
  · exact coeffFromSquareHarmonic_eq_coeffFromProduct_left hk hleft
  · unfold coeffFromSquareHarmonic coeffFromProduct
    have hright : n - k ≤ k - 1 := by omega
    have hmin : Nat.min (k - 1) (n - k) = n - k := Nat.min_eq_right hright
    rw [hmin]
    have hmle : n - k + 1 ≤ k := by omega
    let f : ℕ → ℚ := fun i =>
      (Nat.choose n i : ℚ) ^ 2 * (harmonicRat (n - i) - harmonicRat i)
    let g : ℕ → ℚ := fun i =>
      (Nat.choose n i : ℚ) ^ 2 *
        ∑ j ∈ Finset.Icc (i + 1) (n - i), (j : ℚ)⁻¹
    have hsplit := Finset.sum_range_add_sum_Ico (f := f) (h := hmle)
    have htail : ∑ i ∈ Finset.Ico (n - k + 1) k, f i = 0 := by
      have hsucc : Order.succ (k - 1) = k := by
        simpa using Nat.sub_add_cancel hk
      have hIco : Finset.Ico (n - k + 1) k = Finset.Icc (n - k + 1) (k - 1) := by
        exact ((congrArg (Finset.Ico (n - k + 1)) hsucc).symm).trans
          (Finset.Ico_succ_right_eq_Icc (n - k + 1) (k - 1))
      rw [hIco]
      simpa [f, squareHarmonicTerm] using
        squareHarmonicTerm_tail_sum_zero (n := n) (k := k) hkn
    have hmain : ∑ i ∈ Finset.range (n - k + 1), f i =
        ∑ i ∈ Finset.range (n - k + 1), g i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi_lt_m : i < n - k + 1 := Finset.mem_range.mp hi
      have hi_le_nk : i ≤ n - k := by omega
      have hi_lt_k : i < k := by omega
      have hi_le_ni : i ≤ n - i := by omega
      simp [f, g, harmonicRat_sub_eq_reciprocal_sum hi_le_ni]
    have hsumk : ∑ i ∈ Finset.range k, f i =
        ∑ i ∈ Finset.range (n - k + 1), f i := by
      rw [← hsplit, htail, add_zero]
    calc
      2 * ∑ i ∈ Finset.range k, f i
          = 2 * ∑ i ∈ Finset.range (n - k + 1), f i := by rw [hsumk]
      _ = 2 * ∑ i ∈ Finset.range (n - k + 1), g i := by rw [hmain]

/-- The finite coefficient certificate needed for the product-log identity. -/
def coefficientCertificateTarget : Prop :=
  ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    coeffFromAlternating n k = coeffFromSquareHarmonic n k ∧
    coeffFromSquareHarmonic n k = coeffFromProduct n k

/--
The remaining nontrivial combinatorial identity in the product-log coefficient
certificate. This isolates the Sondow appendix identity from the already closed
square-harmonic-to-product step.
-/
def alternatingToSquareTarget : Prop :=
  ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    coeffFromAlternating n k = coeffFromSquareHarmonic n k

/--
One-step form of the remaining Sondow appendix identity. It says that the
boundary change in the alternating double sum equals the next
square-harmonic term.
-/
def alternatingStepTarget : Prop :=
  ∀ n k : ℕ, k < n → alternatingBoundary n k = squareHarmonicTerm n k

noncomputable def signedBinomialRightBoundary (n k : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc (k + 1) n,
    ((-1 : ℚ) ^ (k + j - 1) * (Nat.choose n j : ℚ)) / ((j - k : ℕ) : ℚ)

noncomputable def signedBinomialLeftBoundary (n k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range k,
    ((-1 : ℚ) ^ (i + k - 1) * (Nat.choose n i : ℚ)) / ((k - i : ℕ) : ℚ)

noncomputable def signedBinomialPoleBoundary (n k : ℕ) : ℚ :=
  signedBinomialRightBoundary n k - signedBinomialLeftBoundary n k

/--
Right-hand one-sided closed form for the signed binomial pole boundary.
This is stronger than the part needed by `signedBinomialPoleTarget`, but it
isolates the forward recurrence proof obligation.
-/
def signedBinomialRightBoundaryTarget : Prop :=
  ∀ n k : ℕ, k ≤ n →
    signedBinomialRightBoundary n k =
      (Nat.choose n k : ℚ) * (harmonicRat n - harmonicRat k)

/--
Left-hand one-sided closed form for the signed binomial pole boundary.
It should follow from the right-hand target by `i ↔ n-i` symmetry.
-/
def signedBinomialLeftBoundaryTarget : Prop :=
  ∀ n k : ℕ, k ≤ n →
    signedBinomialLeftBoundary n k =
      (Nat.choose n k : ℚ) * (harmonicRat n - harmonicRat (n - k))

def signedBinomialRightBoundaryRecurrenceTarget : Prop :=
  ∀ n k : ℕ, 1 ≤ k → k < n →
    (k : ℚ) * signedBinomialRightBoundary n k -
      ((n - k + 1 : ℕ) : ℚ) * signedBinomialRightBoundary n (k - 1) =
        - (Nat.choose n k : ℚ)

theorem signedBinomial_alternating_tail_Ico_int (n k : ℕ) (hk : k ≤ n) :
    (∑ m ∈ Finset.Ico (k + 1) (n + 2),
      ((-1 : ℤ) ^ m * ((n + 1).choose m : ℤ))) =
      (-1 : ℤ) ^ (k + 1) * (n.choose k : ℤ) := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (f := fun m : ℕ => ((-1 : ℤ) ^ m * ((n + 1).choose m : ℤ)))
    (m := k + 1) (n := n + 2) (by omega : k + 1 ≤ n + 2)
  have hfull := Int.alternating_sum_range_choose_of_ne (n := n + 1) (by omega)
  have hprefix := Int.alternating_sum_range_choose_eq_choose (n := n) (m := k)
  rw [← hsplit, hprefix] at hfull
  have hsign : (-1 : ℤ) ^ (k + 1) * (n.choose k : ℤ) =
      - ((-1 : ℤ) ^ k * (n.choose k : ℤ)) := by
    rw [pow_succ]
    ring
  linarith

theorem signedBinomial_alternating_tail_sum_int (n k : ℕ) (hk : k ≤ n) :
    (∑ r ∈ Finset.range (n - k + 1),
      ((-1 : ℤ) ^ r * ((n + 1).choose (k + 1 + r) : ℤ))) =
      (n.choose k : ℤ) := by
  have htail := signedBinomial_alternating_tail_Ico_int n k hk
  have hreindex :
      (∑ r ∈ Finset.range (n - k + 1),
        ((-1 : ℤ) ^ r * ((n + 1).choose (k + 1 + r) : ℤ))) =
      (∑ m ∈ Finset.Ico (k + 1) (n + 2),
        ((-1 : ℤ) ^ (k + 1) *
          ((-1 : ℤ) ^ m * ((n + 1).choose m : ℤ)))) := by
    refine Finset.sum_bij
      (fun r _hr => k + 1 + r) ?_ ?_ ?_ ?_
    · intro r hr
      have hlt : r < n - k + 1 := Finset.mem_range.mp hr
      exact Finset.mem_Ico.mpr (by omega)
    · intro a _ha b _hb hab
      omega
    · intro m hm
      have hmem := Finset.mem_Ico.mp hm
      refine ⟨m - (k + 1), ?_, ?_⟩
      · exact Finset.mem_range.mpr (by omega)
      · omega
    · intro r _hr
      have hsign : (-1 : ℤ) ^ r =
          (-1 : ℤ) ^ (k + 1) * (-1 : ℤ) ^ (k + 1 + r) := by
        rw [← pow_add]
        apply neg_one_pow_congr
        simp [Nat.even_add]
        tauto
      rw [hsign]
      ring
  rw [hreindex]
  rw [← Finset.mul_sum]
  rw [htail]
  rw [← mul_assoc]
  rw [← pow_add]
  have hsign : (-1 : ℤ) ^ (k + 1 + (k + 1)) = 1 := by
    apply Even.neg_one_pow
    exact Even.add_self (k + 1)
  rw [hsign]
  ring

theorem signedBinomial_alternating_tail_sum (n k : ℕ) (hk : k ≤ n) :
    (∑ r ∈ Finset.range (n - k + 1),
      ((-1 : ℚ) ^ r * ((n + 1).choose (k + 1 + r) : ℚ))) =
      (n.choose k : ℚ) := by
  exact_mod_cast signedBinomial_alternating_tail_sum_int n k hk

theorem signedBinomialRightBoundary_eq_sum_range {n k : ℕ} (hk : k ≤ n) :
    signedBinomialRightBoundary n k =
      ∑ r ∈ Finset.range (n - k),
        (-1 : ℚ) ^ r *
          ((Nat.choose n (k + 1 + r) : ℚ) / ((r + 1 : ℕ) : ℚ)) := by
  unfold signedBinomialRightBoundary
  refine Finset.sum_bij
    (fun j _hj => j - (k + 1)) ?_ ?_ ?_ ?_
  · intro j hj
    have hmem := Finset.mem_Icc.mp hj
    exact Finset.mem_range.mpr (by omega)
  · intro a ha b hb hab
    have haI := Finset.mem_Icc.mp ha
    have hbI := Finset.mem_Icc.mp hb
    omega
  · intro r hr
    have hlt : r < n - k := Finset.mem_range.mp hr
    refine ⟨k + 1 + r, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr (by omega)
    · omega
  · intro j hj
    have hmem := Finset.mem_Icc.mp hj
    have hpow : k + j - 1 = 2 * k + (j - (k + 1)) := by omega
    have heven : Even (2 * k) := by
      rw [two_mul]
      exact Even.add_self k
    have hsign : (-1 : ℚ) ^ (k + j - 1) =
        (-1 : ℚ) ^ (j - (k + 1)) := by
      rw [hpow, pow_add, heven.neg_one_pow]
      ring
    have hidx : k + 1 + (j - (k + 1)) = j := by omega
    have hden : j - (k + 1) + 1 = j - k := by omega
    simp [hsign, hidx, hden, div_eq_mul_inv]
    ring

theorem signedBinomialRightBoundary_recurrence_term {n k r : ℕ}
    (hkn : k < n) (hr : r < n - k) :
    (k : ℚ) * ((Nat.choose n (k + 1 + r) : ℚ) / ((r + 1 : ℕ) : ℚ)) -
      ((n - k + 1 : ℕ) : ℚ) *
        ((Nat.choose n (k + r) : ℚ) / ((r + 1 : ℕ) : ℚ)) =
        - (Nat.choose (n + 1) (k + 1 + r) : ℚ) := by
  have hkrle : k + r ≤ n := by omega
  have hkle : k ≤ n := Nat.le_of_lt hkn
  have hkrsucc : k + r + 1 = k + 1 + r := by omega
  have hchoose1 :
      (Nat.choose n (k + 1 + r) : ℚ) * (((k + 1 + r : ℕ) : ℚ)) =
        (Nat.choose n (k + r) : ℚ) * (((n - (k + r) : ℕ) : ℚ)) := by
    simpa [hkrsucc] using (show
      (Nat.choose n (k + r + 1) : ℚ) * (((k + r + 1 : ℕ) : ℚ)) =
        (Nat.choose n (k + r) : ℚ) * (((n - (k + r) : ℕ) : ℚ)) from by
      exact_mod_cast Nat.choose_succ_right_eq n (k + r))
  have hchoose2 :
      (((n + 1 : ℕ) : ℚ)) * (Nat.choose n (k + r) : ℚ) =
        (Nat.choose (n + 1) (k + 1 + r) : ℚ) *
          (((k + 1 + r : ℕ) : ℚ)) := by
    simpa [hkrsucc] using (show
      (((n + 1 : ℕ) : ℚ)) * (Nat.choose n (k + r) : ℚ) =
        (Nat.choose (n + 1) (k + r + 1) : ℚ) *
          (((k + r + 1 : ℕ) : ℚ)) from by
      exact_mod_cast Nat.add_one_mul_choose_eq n (k + r))
  have hcast1 :
      (((n - (k + r) : ℕ) : ℚ)) = (n : ℚ) - (k : ℚ) - (r : ℚ) := by
    rw [Nat.cast_sub hkrle, Nat.cast_add]
    ring
  have hcast2 :
      (((n - k + 1 : ℕ) : ℚ)) = (n : ℚ) - (k : ℚ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hkle]
  have hcast3 : (((n + 1 : ℕ) : ℚ)) = (n : ℚ) + 1 := by norm_num
  have hchoose1n :
      (Nat.choose n (1 + k + r) : ℚ) * (((1 + k + r : ℕ) : ℚ)) =
        (Nat.choose n (k + r) : ℚ) * ((n : ℚ) - (k : ℚ) - (r : ℚ)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hcast1] using hchoose1
  have hchoose2n :
      ((n : ℚ) + 1) * (Nat.choose n (k + r) : ℚ) =
        (Nat.choose (1 + n) (1 + k + r) : ℚ) *
          (((1 + k + r : ℕ) : ℚ)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hcast3] using hchoose2
  have hden : (((r + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  have hq1 : (((1 + k + r : ℕ) : ℚ)) ≠ 0 := by positivity
  field_simp [hden]
  apply mul_left_cancel₀ hq1
  rw [hcast2]
  ring_nf at hchoose1n hchoose2n ⊢
  linear_combination (norm := ring_nf)
    (k : ℚ) * hchoose1n - ((1 + r : ℕ) : ℚ) * hchoose2n
  norm_num [Nat.cast_add, Nat.cast_one] at *
  ring

theorem signedBinomialRightBoundaryRecurrenceTarget_holds :
    signedBinomialRightBoundaryRecurrenceTarget := by
  intro n k hk hkn
  have hRk := signedBinomialRightBoundary_eq_sum_range
    (n := n) (k := k) (Nat.le_of_lt hkn)
  have hRprev := signedBinomialRightBoundary_eq_sum_range
    (n := n) (k := k - 1) (by omega : k - 1 ≤ n)
  rw [hRk, hRprev]
  have hsubprev : n - (k - 1) = n - k + 1 := by omega
  have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hsubprev, hkpred]
  let f : ℕ → ℚ := fun r =>
    (-1 : ℚ) ^ r *
      ((Nat.choose n (k + 1 + r) : ℚ) / ((r + 1 : ℕ) : ℚ))
  let g : ℕ → ℚ := fun r =>
    (-1 : ℚ) ^ r *
      ((Nat.choose n (k + r) : ℚ) / ((r + 1 : ℕ) : ℚ))
  let h : ℕ → ℚ := fun r =>
    (-1 : ℚ) ^ r * (Nat.choose (n + 1) (k + 1 + r) : ℚ)
  change (k : ℚ) * (∑ r ∈ Finset.range (n - k), f r) -
      ((n - k + 1 : ℕ) : ℚ) * (∑ r ∈ Finset.range (n - k + 1), g r) =
        - (Nat.choose n k : ℚ)
  have hsplit :
      (k : ℚ) * (∑ r ∈ Finset.range (n - k), f r) -
        ((n - k + 1 : ℕ) : ℚ) *
          (∑ r ∈ Finset.range (n - k + 1), g r) =
      (∑ r ∈ Finset.range (n - k),
        ((k : ℚ) * f r - ((n - k + 1 : ℕ) : ℚ) * g r)) -
        ((n - k + 1 : ℕ) : ℚ) * g (n - k) := by
    rw [Finset.sum_range_succ]
    rw [mul_add]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  have hterm : ∀ r ∈ Finset.range (n - k),
      (k : ℚ) * f r - ((n - k + 1 : ℕ) : ℚ) * g r = - h r := by
    intro r hr
    have hlt : r < n - k := Finset.mem_range.mp hr
    unfold f g h
    have ht := signedBinomialRightBoundary_recurrence_term
      (n := n) (k := k) (r := r) hkn hlt
    calc
      (k : ℚ) *
            ((-1 : ℚ) ^ r *
              ((Nat.choose n (k + 1 + r) : ℚ) / ((r + 1 : ℕ) : ℚ))) -
          ((n - k + 1 : ℕ) : ℚ) *
            ((-1 : ℚ) ^ r *
              ((Nat.choose n (k + r) : ℚ) / ((r + 1 : ℕ) : ℚ)))
          = (-1 : ℚ) ^ r *
              ((k : ℚ) *
                  ((Nat.choose n (k + 1 + r) : ℚ) / ((r + 1 : ℕ) : ℚ)) -
                ((n - k + 1 : ℕ) : ℚ) *
                  ((Nat.choose n (k + r) : ℚ) / ((r + 1 : ℕ) : ℚ))) := by
              ring
      _ = (-1 : ℚ) ^ r *
            (-(Nat.choose (n + 1) (k + 1 + r) : ℚ)) := by
          rw [ht]
      _ = - ((-1 : ℚ) ^ r *
            (Nat.choose (n + 1) (k + 1 + r) : ℚ)) := by
          ring
  have hsum :
      (∑ r ∈ Finset.range (n - k),
        ((k : ℚ) * f r - ((n - k + 1 : ℕ) : ℚ) * g r)) =
      - ∑ r ∈ Finset.range (n - k), h r := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    exact hterm
  rw [hsum]
  have htail :
      ((n - k + 1 : ℕ) : ℚ) * g (n - k) = h (n - k) := by
    unfold g h
    have hidx1 : k + (n - k) = n :=
      Nat.add_sub_of_le (Nat.le_of_lt hkn)
    have hidx2 : k + 1 + (n - k) = n + 1 := by omega
    have hden : (((n - k + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
    field_simp [hden]
    simp [hidx1, hidx2]
  rw [htail]
  have hrange :
      (∑ r ∈ Finset.range (n - k), h r) + h (n - k) =
        ∑ r ∈ Finset.range (n - k + 1), h r := by
    rw [Finset.sum_range_succ]
  have hcombine :
      -∑ r ∈ Finset.range (n - k), h r - h (n - k) =
        -∑ r ∈ Finset.range (n - k + 1), h r := by
    rw [← hrange]
    ring
  rw [hcombine]
  unfold h
  rw [signedBinomial_alternating_tail_sum n k (Nat.le_of_lt hkn)]

theorem signedBinomialRightClosedForm_recurrence {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n) :
    (k : ℚ) * ((Nat.choose n k : ℚ) * (harmonicRat n - harmonicRat k)) -
      ((n - k + 1 : ℕ) : ℚ) *
        ((Nat.choose n (k - 1) : ℚ) * (harmonicRat n - harmonicRat (k - 1))) =
        - (Nat.choose n k : ℚ) := by
  cases k with
  | zero => omega
  | succ k =>
      have hsub : n - (k + 1) + 1 = n - k := by omega
      have hpred : k + 1 - 1 = k := by omega
      have hchoose :
          (Nat.choose n (k + 1) : ℚ) * (((k + 1 : ℕ) : ℚ)) =
            (Nat.choose n k : ℚ) * (((n - k : ℕ) : ℚ)) := by
        exact_mod_cast Nat.choose_succ_right_eq n k
      have hchoose_rev :
          (((n - k : ℕ) : ℚ)) * (Nat.choose n k : ℚ) =
            (Nat.choose n (k + 1) : ℚ) * (((k + 1 : ℕ) : ℚ)) := by
        rw [mul_comm]
        exact hchoose.symm
      have hnonzero : (((k + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
      rw [hsub, hpred, harmonicRat_succ]
      field_simp [hnonzero]
      rw [hchoose_rev]
      ring

theorem signedBinomialPoleBoundary_zero (n : ℕ) :
    signedBinomialPoleBoundary n 0 =
      (Nat.choose n 0 : ℚ) * (harmonicRat (n - 0) - harmonicRat 0) := by
  unfold signedBinomialPoleBoundary signedBinomialRightBoundary signedBinomialLeftBoundary
  rw [sum_Icc_one_eq_sum_range_succ]
  simpa [harmonicRat, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_assoc] using
    alternating_choose_succ_div_sum_eq_harmonic n

theorem signedBinomialRightBoundary_zero (n : ℕ) :
    signedBinomialRightBoundary n 0 =
      (Nat.choose n 0 : ℚ) * (harmonicRat n - harmonicRat 0) := by
  unfold signedBinomialRightBoundary
  rw [sum_Icc_one_eq_sum_range_succ]
  simpa [harmonicRat, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_assoc] using
    alternating_choose_succ_div_sum_eq_harmonic n

theorem signedBinomialLeftBoundary_zero (n : ℕ) :
    signedBinomialLeftBoundary n 0 = 0 := by
  simp [signedBinomialLeftBoundary]

theorem signedBinomialLeftBoundary_eq_right_reflect {n k : ℕ} (hk : k ≤ n) :
    signedBinomialLeftBoundary n k = signedBinomialRightBoundary n (n - k) := by
  unfold signedBinomialLeftBoundary signedBinomialRightBoundary
  refine Finset.sum_bij
    (fun i _hi => n - i) ?_ ?_ ?_ ?_
  · intro i hi
    have hlt : i < k := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr (by omega)
  · intro a ha b hb hab
    have ha_lt : a < k := Finset.mem_range.mp ha
    have hb_lt : b < k := Finset.mem_range.mp hb
    omega
  · intro j hj
    have hmem := Finset.mem_Icc.mp hj
    refine ⟨n - j, ?_, ?_⟩
    · exact Finset.mem_range.mpr (by omega)
    · omega
  · intro i hi
    have hlt : i < k := Finset.mem_range.mp hi
    have hi_le_n : i ≤ n := by omega
    have hchoose : Nat.choose n (n - i) = Nat.choose n i :=
      Nat.choose_symm hi_le_n
    have hden : n - i - (n - k) = k - i := by omega
    have hpow_sum :
        (i + k - 1) + ((n - k) + (n - i) - 1) = 2 * (n - 1) := by
      omega
    have hsign : (-1 : ℚ) ^ (i + k - 1) =
        (-1 : ℚ) ^ ((n - k) + (n - i) - 1) := by
      apply neg_one_pow_congr
      have heven :
          Even ((i + k - 1) + ((n - k) + (n - i) - 1)) := by
        rw [hpow_sum]
        exact ⟨n - 1, by ring⟩
      exact Nat.even_add.mp heven
    simp [hchoose, hden, hsign, div_eq_mul_inv]

theorem signedBinomialRightBoundaryTarget_of_recurrence
    (hrec : signedBinomialRightBoundaryRecurrenceTarget) :
    signedBinomialRightBoundaryTarget := by
  intro n k hk
  induction k with
  | zero =>
      simpa using signedBinomialRightBoundary_zero n
  | succ k ih =>
      by_cases htop : k + 1 = n
      · subst n
        simp [signedBinomialRightBoundary]
      · have hlt : k + 1 < n := Nat.lt_of_le_of_ne hk htop
        have hprev_le : k ≤ n := by omega
        have ihprev := ih hprev_le
        have hrec_step := hrec n (k + 1) (by omega) hlt
        have hclosed :=
          signedBinomialRightClosedForm_recurrence
            (n := n) (k := k + 1) (by omega) hlt
        have hpred : k + 1 - 1 = k := by omega
        rw [hpred, ihprev] at hrec_step
        rw [hpred] at hclosed
        have hmul :
            (((k + 1 : ℕ) : ℚ)) * signedBinomialRightBoundary n (k + 1) =
              (((k + 1 : ℕ) : ℚ)) *
                ((Nat.choose n (k + 1) : ℚ) *
                  (harmonicRat n - harmonicRat (k + 1))) := by
          nlinarith [hrec_step, hclosed]
        exact mul_left_cancel₀ (by positivity : (((k + 1 : ℕ) : ℚ)) ≠ 0) hmul

theorem signedBinomialRightBoundaryTarget_holds :
    signedBinomialRightBoundaryTarget :=
  signedBinomialRightBoundaryTarget_of_recurrence
    signedBinomialRightBoundaryRecurrenceTarget_holds

theorem signedBinomialLeftBoundaryTarget_holds :
    signedBinomialLeftBoundaryTarget := by
  intro n k hk
  rw [signedBinomialLeftBoundary_eq_right_reflect hk]
  rw [signedBinomialRightBoundaryTarget_holds n (n - k) (Nat.sub_le n k)]
  have hchoose : Nat.choose n (n - k) = Nat.choose n k := Nat.choose_symm hk
  rw [hchoose]

/--
The one-dimensional signed binomial pole identity remaining after factoring
the common `choose n k` from `alternatingStepTarget`.
-/
def signedBinomialPoleTarget : Prop :=
  ∀ n k : ℕ, k < n →
    signedBinomialPoleBoundary n k =
      (Nat.choose n k : ℚ) * (harmonicRat (n - k) - harmonicRat k)

theorem signedBinomialPoleTarget_of_oneSided
    (hright : signedBinomialRightBoundaryTarget)
    (hleft : signedBinomialLeftBoundaryTarget) :
    signedBinomialPoleTarget := by
  intro n k hkn
  have hle : k ≤ n := Nat.le_of_lt hkn
  unfold signedBinomialPoleBoundary
  rw [hright n k hle, hleft n k hle]
  ring

theorem signedBinomialPoleTarget_holds : signedBinomialPoleTarget :=
  signedBinomialPoleTarget_of_oneSided
    signedBinomialRightBoundaryTarget_holds
    signedBinomialLeftBoundaryTarget_holds

theorem alternatingStepTarget_of_signedBinomialPoleTarget
    (h : signedBinomialPoleTarget) : alternatingStepTarget := by
  intro n k hkn
  have hk := h n k hkn
  unfold alternatingBoundary alternatingTerm squareHarmonicTerm
  unfold signedBinomialPoleBoundary signedBinomialRightBoundary signedBinomialLeftBoundary at hk
  have hfactor1 :
      (∑ j ∈ Finset.Icc (k + 1) n,
        (-1 : ℚ) ^ (k + j - 1) * (Nat.choose n k : ℚ) *
          (Nat.choose n j : ℚ) / ((j - k : ℕ) : ℚ)) =
      (Nat.choose n k : ℚ) *
        (∑ j ∈ Finset.Icc (k + 1) n,
          ((-1 : ℚ) ^ (k + j - 1) * (Nat.choose n j : ℚ)) /
            ((j - k : ℕ) : ℚ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hfactor2 :
      (∑ i ∈ Finset.range k,
        (-1 : ℚ) ^ (i + k - 1) * (Nat.choose n i : ℚ) *
          (Nat.choose n k : ℚ) / ((k - i : ℕ) : ℚ)) =
      (Nat.choose n k : ℚ) *
        (∑ i ∈ Finset.range k,
          ((-1 : ℚ) ^ (i + k - 1) * (Nat.choose n i : ℚ)) /
            ((k - i : ℕ) : ℚ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hfactor1, hfactor2]
  rw [← mul_sub]
  rw [hk]
  ring

theorem alternatingToSquareTarget_of_step
    (hstep : alternatingStepTarget) : alternatingToSquareTarget := by
  intro n k _hk hkn
  have hstrong : ∀ m : ℕ, m ≤ n →
      coeffFromAlternating n m = coeffFromSquareHarmonic n m := by
    intro m hm
    induction m with
    | zero =>
        simp [coeffFromAlternating, coeffFromSquareHarmonic]
    | succ m ih =>
        have hmn : m < n := Nat.lt_of_succ_le hm
        rw [coeffFromAlternating_succ hmn, coeffFromSquareHarmonic_succ]
        rw [ih (Nat.le_of_lt hmn), hstep n m hmn]
  exact hstrong k hkn

theorem alternatingToSquareTarget_of_signedBinomialPoleTarget
    (h : signedBinomialPoleTarget) : alternatingToSquareTarget :=
  alternatingToSquareTarget_of_step
    (alternatingStepTarget_of_signedBinomialPoleTarget h)

theorem coefficientCertificateTarget_of_alternatingToSquare
    (h : alternatingToSquareTarget) : coefficientCertificateTarget := by
  intro n k hk hkn
  exact ⟨h n k hk hkn, coeffFromSquareHarmonic_eq_coeffFromProduct hk hkn⟩

theorem coefficientCertificateTarget_of_signedBinomialPoleTarget
    (h : signedBinomialPoleTarget) : coefficientCertificateTarget :=
  coefficientCertificateTarget_of_alternatingToSquare
    (alternatingToSquareTarget_of_signedBinomialPoleTarget h)

theorem coefficientCertificateTarget_holds : coefficientCertificateTarget :=
  coefficientCertificateTarget_of_signedBinomialPoleTarget
    signedBinomialPoleTarget_holds

end

end EulerLimit.SondowCoefficient
