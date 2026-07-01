/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.Analytic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Bertrand

/-!
# LCM bound bridge

This module isolates the rigorous bridge from a Chebyshev-psi linear upper
bound to the Sondow forward-input LCM bound.

It does not assert a new prime-number estimate.  Instead, it proves that any
verified estimate `Chebyshev.psi n ≤ c*n` with `c ≤ log 3` immediately yields
`Nat.lcmUpto n ≤ 3^n`.
-/

open Chebyshev

theorem Nat.lcmUpto_dvd_lcmUpto {m n : ℕ} (hmn : m ≤ n) :
    Nat.lcmUpto m ∣ Nat.lcmUpto n := by
  rw [Nat.lcmUpto, Nat.lcmUpto]
  exact Finset.lcm_dvd fun k hk =>
    Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
      (Finset.mem_Icc.mp hk).2.trans hmn⟩)

theorem Nat.lcmUpto_le_lcmUpto {m n : ℕ} (hmn : m ≤ n) :
    Nat.lcmUpto m ≤ Nat.lcmUpto n :=
  Nat.le_of_dvd (Nat.lcmUpto_pos n) (Nat.lcmUpto_dvd_lcmUpto hmn)

theorem Nat.lcmUpto_succ_dvd_succ_mul_lcmUpto (n : ℕ) :
    Nat.lcmUpto (n + 1) ∣ (n + 1) * Nat.lcmUpto n := by
  rw [Nat.lcmUpto]
  refine Finset.lcm_dvd ?_
  intro k hk
  rw [Nat.lcmUpto]
  have hkI := Finset.mem_Icc.mp hk
  rcases lt_or_eq_of_le hkI.2 with hklt | hkeq
  · have hkn : k ≤ n := Nat.lt_succ_iff.mp hklt
    exact (Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hkI.1, hkn⟩)).trans
      (Nat.dvd_mul_left _ _)
  · subst hkeq
    exact Nat.dvd_mul_right _ _

theorem Nat.lcmUpto_succ_le_succ_mul_lcmUpto (n : ℕ) :
    Nat.lcmUpto (n + 1) ≤ (n + 1) * Nat.lcmUpto n :=
  Nat.le_of_dvd
    (Nat.mul_pos (Nat.succ_pos n) (Nat.lcmUpto_pos n))
    (Nat.lcmUpto_succ_dvd_succ_mul_lcmUpto n)

theorem Nat.log_two_mul_le_log_add_factorization_centralBinom
    (n : ℕ) {p : ℕ} (hp : p.Prime) :
    p.log (2 * n) ≤ p.log n + (Nat.centralBinom n).factorization p := by
  by_cases hn0 : n = 0
  · subst hn0
    simp
  let a := p.log n
  let b := p.log (2 * n)
  have hb : p.log (n + n) < b + 1 := by
    simp [b, two_mul]
  have hfac := Nat.factorization_choose' (p := p) (n := n) (k := n) (b := b + 1) hp hb
  have hfac_cb : (Nat.centralBinom n).factorization p =
      ((Finset.Ico 1 (b + 1)).filter
        (fun i => p ^ i ≤ n % p ^ i + n % p ^ i)).card := by
    simpa [Nat.centralBinom, two_mul] using hfac
  have hsubset : Finset.Ico (a + 1) (b + 1) ⊆
      (Finset.Ico 1 (b + 1)).filter (fun i => p ^ i ≤ n % p ^ i + n % p ^ i) := by
    intro i hi
    rw [Finset.mem_filter]
    have hiab := Finset.mem_Ico.mp hi
    have hia : a < i := Nat.lt_of_succ_le hiab.1
    have hib : i ≤ b := Nat.lt_succ_iff.mp hiab.2
    have hpi_le : p ^ i ≤ 2 * n := Nat.pow_le_of_le_log (by omega) hib
    have hn_lt_pi : n < p ^ i := Nat.lt_pow_of_log_lt hp.one_lt hia
    have hmod : n % p ^ i = n := Nat.mod_eq_of_lt hn_lt_pi
    constructor
    · exact Finset.mem_Ico.mpr ⟨by omega, hiab.2⟩
    · rw [hmod]
      simpa [two_mul] using hpi_le
  have hcard : (Finset.Ico (a + 1) (b + 1)).card ≤
      (Nat.centralBinom n).factorization p := by
    rw [hfac_cb]
    exact Finset.card_le_card hsubset
  have hcard_eq : (Finset.Ico (a + 1) (b + 1)).card = b - a := by
    simp [a, b]
  have hba : a ≤ b := Nat.log_mono_right (by omega)
  omega

theorem Nat.lcmUpto_two_mul_dvd_lcmUpto_mul_centralBinom (n : ℕ) :
    Nat.lcmUpto (2 * n) ∣ Nat.lcmUpto n * Nat.centralBinom n := by
  rw [← Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero (2 * n))
    (Nat.mul_ne_zero (Nat.lcmUpto_ne_zero n) (Nat.centralBinom_ne_zero n))]
  intro p hp
  rw [Nat.factorization_lcmUpto (2 * n) hp]
  rw [Nat.factorization_mul (Nat.lcmUpto_ne_zero n) (Nat.centralBinom_ne_zero n)]
  have hlog_central := Nat.log_two_mul_le_log_add_factorization_centralBinom n hp
  simpa [Nat.factorization_lcmUpto n hp, Pi.add_apply] using hlog_central

theorem Nat.lcmUpto_two_mul_le_lcmUpto_mul_centralBinom (n : ℕ) :
    Nat.lcmUpto (2 * n) ≤ Nat.lcmUpto n * Nat.centralBinom n :=
  Nat.le_of_dvd
    (Nat.mul_pos (Nat.lcmUpto_pos n) (Nat.centralBinom_pos n))
    (Nat.lcmUpto_two_mul_dvd_lcmUpto_mul_centralBinom n)

theorem Nat.lcmUpto_two_mul_le_of_no_bertrand_prime
    (n : ℕ) (hn : 2 < n)
    (no_prime : ∀ p : ℕ, p.Prime → n < p → 2 * n < p) :
    Nat.lcmUpto (2 * n) ≤
      Nat.lcmUpto n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) := by
  calc
    Nat.lcmUpto (2 * n) ≤ Nat.lcmUpto n * Nat.centralBinom n :=
      Nat.lcmUpto_two_mul_le_lcmUpto_mul_centralBinom n
    _ ≤ Nat.lcmUpto n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) := by
      exact Nat.mul_le_mul_left _
        (centralBinom_le_of_no_bertrand_prime n hn no_prime)

theorem Nat.lcmUpto_two_mul_add_one_dvd_mul_lcmUpto_two_mul (n : ℕ) :
    Nat.lcmUpto (2 * n + 1) ∣ (2 * n + 1) * Nat.lcmUpto (2 * n) := by
  simpa using Nat.lcmUpto_succ_dvd_succ_mul_lcmUpto (2 * n)

theorem Nat.lcmUpto_two_mul_add_one_dvd_mul_lcmUpto_mul_centralBinom (n : ℕ) :
    Nat.lcmUpto (2 * n + 1) ∣
      (2 * n + 1) * (Nat.lcmUpto n * Nat.centralBinom n) := by
  exact (Nat.lcmUpto_two_mul_add_one_dvd_mul_lcmUpto_two_mul n).trans
    (Nat.mul_dvd_mul_left _ (Nat.lcmUpto_two_mul_dvd_lcmUpto_mul_centralBinom n))

theorem Nat.lcmUpto_two_mul_add_one_le_mul_lcmUpto_mul_centralBinom (n : ℕ) :
    Nat.lcmUpto (2 * n + 1) ≤
      (2 * n + 1) * (Nat.lcmUpto n * Nat.centralBinom n) :=
  Nat.le_of_dvd
    (Nat.mul_pos (Nat.succ_pos (2 * n))
      (Nat.mul_pos (Nat.lcmUpto_pos n) (Nat.centralBinom_pos n)))
    (Nat.lcmUpto_two_mul_add_one_dvd_mul_lcmUpto_mul_centralBinom n)

theorem Nat.factorization_centralBinom_eq_zero_of_two_mul_div_three_lt
    {n p : ℕ} (hn : 2 < n) (hp_le : p ≤ n) (hp_gt : 2 * n / 3 < p) :
    (Nat.centralBinom n).factorization p = 0 := by
  exact Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hp_le (by
    have h := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).mp hp_gt
    rwa [mul_comm p 3] at h)

theorem Nat.le_two_mul_div_three_of_factorization_centralBinom_pos
    {n p : ℕ} (hn : 2 < n) (hp_le : p ≤ n)
    (hpos : 0 < (Nat.centralBinom n).factorization p) :
    p ≤ 2 * n / 3 := by
  by_contra hnot
  have hp_gt : 2 * n / 3 < p := Nat.lt_of_not_ge hnot
  have hz := Nat.factorization_centralBinom_eq_zero_of_two_mul_div_three_lt hn hp_le hp_gt
  omega

theorem lcmUpto_le_three_pow_nat_of_log_lcmUpto_le_at
    (n : ℕ)
    (hlog :
      Real.log (Nat.lcmUpto n : ℝ) ≤ Real.log 3 * (n : ℝ)) :
    Nat.lcmUpto n ≤ 3 ^ n := by
  have hlog' :
      Real.log (Nat.lcmUpto n : ℝ) ≤ Real.log ((3 ^ n : ℕ) : ℝ) := by
    calc
      Real.log (Nat.lcmUpto n : ℝ) ≤ Real.log 3 * (n : ℝ) := hlog
      _ = Real.log ((3 ^ n : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
        ring_nf
  have hpow_pos : (0 : ℝ) < ((3 ^ n : ℕ) : ℝ) := by positivity
  exact_mod_cast
    ((Real.log_le_log_iff
      (by exact_mod_cast Nat.lcmUpto_pos n) hpow_pos).1 hlog')

theorem lcmUpto_le_three_pow_nat_of_log_lcmUpto_le
    (hlog : ∀ n : ℕ,
      Real.log (Nat.lcmUpto n : ℝ) ≤ Real.log 3 * (n : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  intro n
  exact lcmUpto_le_three_pow_nat_of_log_lcmUpto_le_at n (hlog n)

theorem lcmUpto_le_three_pow_nat_of_le_256
    {n : ℕ} (hn : n ≤ 256) :
    Nat.lcmUpto n ≤ 3 ^ n := by
  set_option maxRecDepth 8192 in
  set_option exponentiation.threshold 512 in
  revert n
  decide

theorem nat_mul_two_pow_le_three_pow (n : ℕ) :
    n * 2 ^ n ≤ 3 ^ n := by
  rcases n with _ | n
  · norm_num
  rcases n with _ | n
  · norm_num
  rcases n with _ | n
  · norm_num
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      have hfactor : 2 * (n + 4) ≤ 3 * (n + 3) := by omega
      calc
        (n + 4) * 2 ^ (n + 4)
            = (2 * (n + 4)) * 2 ^ (n + 3) := by ring
        _ ≤ (3 * (n + 3)) * 2 ^ (n + 3) :=
          Nat.mul_le_mul_right _ hfactor
        _ = 3 * ((n + 3) * 2 ^ (n + 3)) := by ring
        _ ≤ 3 * (3 ^ (n + 3)) := Nat.mul_le_mul_left _ ih
        _ = 3 ^ (n + 4) := by
          rw [pow_succ]
          ring

theorem lcmUpto_le_three_pow_nat_of_lcmUpto_le_nat_mul_two_pow
    (h : ∀ n : ℕ, 1 ≤ n → Nat.lcmUpto n ≤ n * 2 ^ n) :
    lcmUpto_le_three_pow_nat_statement := by
  intro n
  rcases n with _ | n
  · simp [Nat.lcmUpto]
  exact (h (n + 1) (by omega)).trans (nat_mul_two_pow_le_three_pow (n + 1))

theorem lcmUpto_le_three_pow_nat_at_of_dvd_certificate
    (n m : ℕ)
    (hdvd : Nat.lcmUpto n ∣ m)
    (hmpos : 0 < m)
    (hm : m ≤ 3 ^ n) :
    Nat.lcmUpto n ≤ 3 ^ n :=
  (Nat.le_of_dvd hmpos hdvd).trans hm

theorem lcmUpto_le_three_pow_nat_of_dvd_certificates
    (hcert : ∀ n : ℕ, ∃ m : ℕ, Nat.lcmUpto n ∣ m ∧ 0 < m ∧ m ≤ 3 ^ n) :
    lcmUpto_le_three_pow_nat_statement := by
  intro n
  rcases hcert n with ⟨m, hdvd, hmpos, hm⟩
  exact lcmUpto_le_three_pow_nat_at_of_dvd_certificate n m hdvd hmpos hm

structure LcmDvdCertificate (n : ℕ) where
  witness : ℕ
  dvd_witness : Nat.lcmUpto n ∣ witness
  witness_pos : 0 < witness
  witness_le_three_pow : witness ≤ 3 ^ n

theorem LcmDvdCertificate.bound {n : ℕ} (cert : LcmDvdCertificate n) :
    Nat.lcmUpto n ≤ 3 ^ n :=
  lcmUpto_le_three_pow_nat_at_of_dvd_certificate
    n cert.witness cert.dvd_witness cert.witness_pos cert.witness_le_three_pow

theorem lcmUpto_le_three_pow_nat_of_certificate_family
    (cert : ∀ n : ℕ, LcmDvdCertificate n) :
    lcmUpto_le_three_pow_nat_statement := by
  intro n
  exact (cert n).bound

theorem lcmUpto_le_three_pow_nat_of_certificate_family_ge
    (N : ℕ)
    (hfinite : ∀ n : ℕ, n < N → Nat.lcmUpto n ≤ 3 ^ n)
    (cert : ∀ n : ℕ, N ≤ n → LcmDvdCertificate n) :
    lcmUpto_le_three_pow_nat_statement := by
  intro n
  by_cases hn : n < N
  · exact hfinite n hn
  · exact (cert n (Nat.le_of_not_gt hn)).bound

noncomputable def primePowProductLE (n : ℕ) (beta : ℕ → ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE n, p ^ beta p

theorem lcmUpto_dvd_primePowProductLE_of_log_le
    (n : ℕ) (beta : ℕ → ℕ)
    (hbeta : ∀ p : ℕ, p ∈ Nat.primesLE n → p.log n ≤ beta p) :
    Nat.lcmUpto n ∣ primePowProductLE n beta := by
  rw [Nat.lcmUpto_eq_prod_pow_log, primePowProductLE]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun p hp =>
    pow_dvd_pow p (hbeta p hp)

noncomputable def LcmDvdCertificate.ofPrimeExponentBounds
    (n : ℕ) (beta : ℕ → ℕ)
    (hbeta : ∀ p : ℕ, p ∈ Nat.primesLE n → p.log n ≤ beta p)
    (hpos : 0 < primePowProductLE n beta)
    (hsmall : primePowProductLE n beta ≤ 3 ^ n) :
    LcmDvdCertificate n where
  witness := primePowProductLE n beta
  dvd_witness := lcmUpto_dvd_primePowProductLE_of_log_le n beta hbeta
  witness_pos := hpos
  witness_le_three_pow := hsmall

theorem primePowProductLE_pos (n : ℕ) (beta : ℕ → ℕ) :
    0 < primePowProductLE n beta := by
  rw [primePowProductLE]
  exact Finset.prod_pos fun p hp =>
    pow_pos (Nat.prime_of_mem_primesLE hp).pos (beta p)

theorem multinomial_term_le_sum_pow
    {α : Type*} (s : Finset α) (f : α → ℕ)
    (hzero : ∀ a : α, f a ≠ 0 → a ∈ s) :
    Nat.multinomial s f * (∏ a ∈ s, f a ^ f a) ≤
      (∑ a ∈ s, f a) ^ (∑ a ∈ s, f a) := by
  classical
  have hmem : f ∈ Finset.piAntidiag s (∑ a ∈ s, f a) := by
    rw [Finset.mem_piAntidiag]
    exact ⟨rfl, hzero⟩
  have hsingle :
      Nat.multinomial s f * (∏ a ∈ s, f a ^ f a) ≤
        ∑ k ∈ Finset.piAntidiag s (∑ a ∈ s, f a),
          Nat.multinomial s k * ∏ a ∈ s, f a ^ k a := by
    exact Finset.single_le_sum
      (s := Finset.piAntidiag s (∑ a ∈ s, f a))
      (f := fun k => Nat.multinomial s k * ∏ a ∈ s, f a ^ k a)
      (fun _ _ => Nat.zero_le _) hmem
  calc
    Nat.multinomial s f * (∏ a ∈ s, f a ^ f a)
        ≤ ∑ k ∈ Finset.piAntidiag s (∑ a ∈ s, f a),
            Nat.multinomial s k * ∏ a ∈ s, f a ^ k a := hsingle
    _ = (∑ a ∈ s, f a) ^ (∑ a ∈ s, f a) := by
        simpa using
          (Finset.sum_pow_eq_sum_piAntidiag
            (s := s) (f := fun a => (f a : ℕ))
            (n := ∑ a ∈ s, f a)).symm

/-- Hanson's Sylvester-type sequence, indexed from zero:
`2, 3, 7, 43, ...`. -/
def hansonA : ℕ → ℕ
  | 0 => 2
  | n + 1 => hansonA n ^ 2 - hansonA n + 1

theorem two_le_hansonA (n : ℕ) : 2 ≤ hansonA n := by
  induction n with
  | zero =>
      norm_num [hansonA]
  | succ n ih =>
      dsimp [hansonA]
      have htwomul :
          2 * hansonA n ≤ hansonA n * hansonA n :=
        Nat.mul_le_mul_right (hansonA n) ih
      have hself :
          hansonA n ≤ hansonA n ^ 2 - hansonA n := by
        rw [pow_two]
        exact Nat.le_sub_of_add_le (by simpa [two_mul] using htwomul)
      exact ih.trans hself |>.trans (Nat.le_add_right _ _)

theorem hansonA_pos (n : ℕ) : 0 < hansonA n :=
  lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_hansonA n)

theorem hansonA_lt_succ (n : ℕ) : hansonA n < hansonA (n + 1) := by
  dsimp [hansonA]
  have htwomul :
      2 * hansonA n ≤ hansonA n * hansonA n :=
    Nat.mul_le_mul_right (hansonA n) (two_le_hansonA n)
  have hself :
      hansonA n ≤ hansonA n ^ 2 - hansonA n := by
    rw [pow_two]
    exact Nat.le_sub_of_add_le (by simpa [two_mul] using htwomul)
  exact Nat.lt_add_one_of_le hself

theorem hansonA_strictMono : StrictMono hansonA := by
  exact strictMono_nat_of_lt_succ hansonA_lt_succ

theorem hansonA_succ_eq_prod_range_add_one (n : ℕ) :
    hansonA (n + 1) =
      (∏ i ∈ Finset.range (n + 1), hansonA i) + 1 := by
  induction n with
  | zero =>
      norm_num [hansonA]
  | succ n ih =>
      rw [Finset.prod_range_succ]
      change hansonA (n + 1) ^ 2 - hansonA (n + 1) + 1 =
        (∏ x ∈ Finset.range (n + 1), hansonA x) * hansonA (n + 1) + 1
      have hprod :
          (∏ x ∈ Finset.range (n + 1), hansonA x) =
            hansonA (n + 1) - 1 := by
        omega
      rw [hprod]
      rw [pow_two, Nat.sub_mul]
      simp

theorem prod_range_hansonA_eq_pred (k : ℕ) :
    (∏ i ∈ Finset.range k, hansonA i) = hansonA k - 1 := by
  cases k with
  | zero =>
      norm_num [hansonA]
  | succ k =>
      have h := hansonA_succ_eq_prod_range_add_one k
      omega

theorem le_prod_range_hansonA_of_lt_hansonA
    {n k : ℕ} (hn : n < hansonA k) :
    n ≤ ∏ i ∈ Finset.range k, hansonA i := by
  rw [prod_range_hansonA_eq_pred]
  omega

theorem hansonA_succ_sub_one (n : ℕ) :
    hansonA (n + 1) - 1 = (hansonA n - 1) * hansonA n := by
  change (hansonA n ^ 2 - hansonA n + 1) - 1 =
    (hansonA n - 1) * hansonA n
  rw [pow_two, Nat.sub_mul]
  simp

theorem hansonA_reciprocal_sum_eq (k : ℕ) :
    (∑ i ∈ Finset.range k, (1 : ℚ) / hansonA i) =
      1 - (1 : ℚ) / ((hansonA k : ℚ) - 1) := by
  induction k with
  | zero =>
      norm_num [hansonA]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hk1nat : 1 ≤ hansonA k := by
        exact (by norm_num : 1 ≤ 2).trans (two_le_hansonA k)
      have hksucc1nat : 1 ≤ hansonA (k + 1) := by
        exact (by norm_num : 1 ≤ 2).trans (two_le_hansonA (k + 1))
      have hk1 : ((hansonA k : ℚ) - 1) ≠ 0 := by
        have hgt : (1 : ℚ) < hansonA k := by
          exact_mod_cast (by
            have := two_le_hansonA k
            omega : 1 < hansonA k)
        linarith
      have hk : ((hansonA k : ℚ)) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (hansonA_pos k))
      have hksucc : ((hansonA (k + 1) : ℚ) - 1) =
          ((hansonA k : ℚ) - 1) * (hansonA k : ℚ) := by
        calc
          ((hansonA (k + 1) : ℚ) - 1) =
              ((hansonA (k + 1) - 1 : ℕ) : ℚ) := by
            exact (Nat.cast_sub hksucc1nat).symm
          _ = (((hansonA k - 1) * hansonA k : ℕ) : ℚ) := by
            rw [hansonA_succ_sub_one]
          _ = ((hansonA k : ℚ) - 1) * (hansonA k : ℚ) := by
            rw [Nat.cast_mul, Nat.cast_sub hk1nat]
            norm_num
      rw [hksucc]
      field_simp [hk1, hk]
      ring

theorem rat_div_sub_one_le_nat_div_cast
    (n a : ℕ) (ha : 0 < a) :
    (n : ℚ) / (a : ℚ) - 1 ≤ ((n / a : ℕ) : ℚ) := by
  have hlt_nat : n < a * (n / a + 1) := by
    calc
      n = n % a + a * (n / a) := by
          exact (Nat.mod_add_div n a).symm
      _ < a + a * (n / a) := by
          exact Nat.add_lt_add_right (Nat.mod_lt n ha) _
      _ = a * (n / a + 1) := by ring
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hltQ : (n : ℚ) < (a : ℚ) * (((n / a : ℕ) : ℚ) + 1) := by
    exact_mod_cast hlt_nat
  have hdiv : (n : ℚ) / (a : ℚ) < ((n / a : ℕ) : ℚ) + 1 := by
    rw [div_lt_iff₀ haQ]
    simpa [mul_comm] using hltQ
  linarith

theorem hanson_floor_sum_q_lower (n k : ℕ) :
    (n : ℚ) * (∑ i ∈ Finset.range k, (1 : ℚ) / hansonA i) - k ≤
      (((∑ i ∈ Finset.range k, n / hansonA i) : ℕ) : ℚ) := by
  have hsum :
      (∑ i ∈ Finset.range k, ((n : ℚ) / hansonA i - 1)) ≤
        ∑ i ∈ Finset.range k, (((n / hansonA i : ℕ) : ℚ)) := by
    exact Finset.sum_le_sum fun i _ =>
      rat_div_sub_one_le_nat_div_cast n (hansonA i) (hansonA_pos i)
  calc
    (n : ℚ) * (∑ i ∈ Finset.range k, (1 : ℚ) / hansonA i) - k
        = ∑ i ∈ Finset.range k, ((n : ℚ) / hansonA i - 1) := by
            rw [Finset.mul_sum, Finset.sum_sub_distrib]
            simp [Finset.card_range]
            ring_nf
    _ ≤ ∑ i ∈ Finset.range k, (((n / hansonA i : ℕ) : ℚ)) := hsum
    _ = (((∑ i ∈ Finset.range k, n / hansonA i) : ℕ) : ℚ) := by
            norm_num

theorem hanson_floor_sum_q_lower_closed (n k : ℕ) :
    (n : ℚ) *
        (1 - (1 : ℚ) / ((hansonA k : ℚ) - 1)) - k ≤
      (((∑ i ∈ Finset.range k, n / hansonA i) : ℕ) : ℚ) := by
  have h := hanson_floor_sum_q_lower n k
  rw [hansonA_reciprocal_sum_eq] at h
  exact h

theorem prod_factorial_dvd_factorial_of_sum_le
    {α : Type*} (s : Finset α) (f : α → ℕ) {n : ℕ}
    (hsum : (∑ i ∈ s, f i) ≤ n) :
    (∏ i ∈ s, Nat.factorial (f i)) ∣ Nat.factorial n :=
  (Nat.prod_factorial_dvd_factorial_sum s f).trans
    (Nat.factorial_dvd_factorial hsum)

/-- The finite Hanson denominator
`∏_{i < k} floor(n / a_i)!` used in Hanson's factorial quotient. -/
def hansonDenominator (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.factorial (n / hansonA i)

theorem hansonDenominator_pos (n k : ℕ) : 0 < hansonDenominator n k := by
  rw [hansonDenominator]
  exact Nat.prod_factorial_pos (Finset.range k) fun i => n / hansonA i

theorem hansonDenominator_dvd_factorial_of_sum_le
    (n k : ℕ)
    (hsum : (∑ i ∈ Finset.range k, n / hansonA i) ≤ n) :
    hansonDenominator n k ∣ Nat.factorial n := by
  rw [hansonDenominator]
  exact prod_factorial_dvd_factorial_of_sum_le
    (Finset.range k) (fun i => n / hansonA i) hsum

theorem hanson_floor_sum_le (n k : ℕ) :
    (∑ i ∈ Finset.range k, n / hansonA i) ≤ n := by
  have hsumQ :
      (((∑ i ∈ Finset.range k, n / hansonA i) : ℕ) : ℚ) ≤ (n : ℚ) := by
    calc
      (((∑ i ∈ Finset.range k, n / hansonA i) : ℕ) : ℚ)
          = ∑ i ∈ Finset.range k, ((n / hansonA i : ℕ) : ℚ) := by
            norm_num
      _ ≤ ∑ i ∈ Finset.range k, (n : ℚ) / hansonA i := by
        exact Finset.sum_le_sum fun _ _ => Nat.cast_div_le
      _ = (n : ℚ) * (∑ i ∈ Finset.range k, (1 : ℚ) / hansonA i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      _ = (n : ℚ) *
          (1 - (1 : ℚ) / ((hansonA k : ℚ) - 1)) := by
        rw [hansonA_reciprocal_sum_eq]
      _ ≤ (n : ℚ) := by
        have hdenpos : (0 : ℚ) < (hansonA k : ℚ) - 1 := by
          have hgt : (1 : ℚ) < hansonA k := by
            exact_mod_cast (by
              have := two_le_hansonA k
              omega : 1 < hansonA k)
          linarith
        have hfrac_nonneg :
            0 ≤ (1 : ℚ) / ((hansonA k : ℚ) - 1) := by
          positivity
        have hnnonneg : (0 : ℚ) ≤ n := by positivity
        nlinarith
  exact_mod_cast hsumQ

theorem hanson_floor_sum_lt_self {m k : ℕ} (hm : 0 < m) :
    (∑ i ∈ Finset.range k, m / hansonA i) < m := by
  have hsumQ :
      (((∑ i ∈ Finset.range k, m / hansonA i) : ℕ) : ℚ) < (m : ℚ) := by
    calc
      (((∑ i ∈ Finset.range k, m / hansonA i) : ℕ) : ℚ)
          = ∑ i ∈ Finset.range k, ((m / hansonA i : ℕ) : ℚ) := by
            norm_num
      _ ≤ ∑ i ∈ Finset.range k, (m : ℚ) / hansonA i := by
        exact Finset.sum_le_sum fun _ _ => Nat.cast_div_le
      _ = (m : ℚ) * (∑ i ∈ Finset.range k, (1 : ℚ) / hansonA i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      _ = (m : ℚ) *
          (1 - (1 : ℚ) / ((hansonA k : ℚ) - 1)) := by
        rw [hansonA_reciprocal_sum_eq]
      _ < (m : ℚ) := by
        have hdenpos : (0 : ℚ) < (hansonA k : ℚ) - 1 := by
          have hgt : (1 : ℚ) < hansonA k := by
            exact_mod_cast (by
              have := two_le_hansonA k
              omega : 1 < hansonA k)
          linarith
        have hfrac_pos :
            0 < (1 : ℚ) / ((hansonA k : ℚ) - 1) := by
          positivity
        have hmposQ : (0 : ℚ) < m := by exact_mod_cast hm
        nlinarith
  exact_mod_cast hsumQ

theorem hanson_floor_sum_succ_le {m k : ℕ} (hm : 0 < m) :
    (∑ i ∈ Finset.range k, m / hansonA i) + 1 ≤ m :=
  Nat.succ_le_iff.mpr (hanson_floor_sum_lt_self hm)

theorem hanson_legendre_floor_sum_succ_le
    {n k p r : ℕ} (hpos : 0 < n / p ^ r) :
    (∑ i ∈ Finset.range k, (n / hansonA i) / p ^ r) + 1 ≤
      n / p ^ r := by
  have hrewrite :
      (∑ i ∈ Finset.range k, (n / hansonA i) / p ^ r) =
        ∑ i ∈ Finset.range k, (n / p ^ r) / hansonA i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm]
  rw [hrewrite]
  exact hanson_floor_sum_succ_le hpos

theorem one_le_hanson_legendre_defect
    {n k p r : ℕ} (hpos : 0 < n / p ^ r) :
    1 ≤ n / p ^ r -
      ∑ i ∈ Finset.range k, (n / hansonA i) / p ^ r :=
  Nat.le_sub_of_add_le (by
    simpa [Nat.add_comm] using hanson_legendre_floor_sum_succ_le hpos)

theorem card_le_sum_sub_sum_of_succ_le
    {α : Type*} (s : Finset α) (a b : α → ℕ)
    (h : ∀ i ∈ s, b i + 1 ≤ a i) :
    s.card ≤ (∑ i ∈ s, a i) - ∑ i ∈ s, b i := by
  have hsum : (∑ i ∈ s, (b i + 1)) ≤ ∑ i ∈ s, a i := by
    exact Finset.sum_le_sum h
  have hsum_eq :
      (∑ i ∈ s, (b i + 1)) = (∑ i ∈ s, b i) + s.card := by
    simp [Finset.sum_add_distrib]
  exact Nat.le_sub_of_add_le (by
    simpa [hsum_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum)

theorem hansonDenominator_dvd_factorial (n k : ℕ) :
    hansonDenominator n k ∣ Nat.factorial n :=
  hansonDenominator_dvd_factorial_of_sum_le n k (hanson_floor_sum_le n k)

theorem hansonDenominator_dvd_hansonDenominator_of_le
    {n k l : ℕ} (hkl : k ≤ l) :
    hansonDenominator n k ∣ hansonDenominator n l := by
  rw [hansonDenominator, hansonDenominator]
  let extra := ∏ i ∈ Finset.range l \ Finset.range k,
    Nat.factorial (n / hansonA i)
  refine ⟨extra, ?_⟩
  dsimp [extra]
  rw [mul_comm]
  exact (Finset.prod_sdiff (f := fun i => Nat.factorial (n / hansonA i)) (by
    intro x hx
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le hkl))).symm

/-- Hanson's finite factorial quotient `n! / ∏_{i < k} floor(n / a_i)!`. -/
def hansonC (n k : ℕ) : ℕ :=
  Nat.factorial n / hansonDenominator n k

theorem hansonDenominator_mul_hansonC_of_sum_le
    (n k : ℕ)
    (hsum : (∑ i ∈ Finset.range k, n / hansonA i) ≤ n) :
    hansonDenominator n k * hansonC n k = Nat.factorial n := by
  rw [hansonC]
  exact Nat.mul_div_cancel'
    (hansonDenominator_dvd_factorial_of_sum_le n k hsum)

theorem hansonDenominator_mul_hansonC (n k : ℕ) :
    hansonDenominator n k * hansonC n k = Nat.factorial n :=
  hansonDenominator_mul_hansonC_of_sum_le n k (hanson_floor_sum_le n k)

theorem hansonC_pos_of_sum_le
    (n k : ℕ)
    (hsum : (∑ i ∈ Finset.range k, n / hansonA i) ≤ n) :
    0 < hansonC n k := by
  rw [hansonC]
  exact Nat.div_pos
    (Nat.le_of_dvd (Nat.factorial_pos n)
      (hansonDenominator_dvd_factorial_of_sum_le n k hsum))
    (hansonDenominator_pos n k)

theorem hansonC_pos (n k : ℕ) : 0 < hansonC n k :=
  hansonC_pos_of_sum_le n k (hanson_floor_sum_le n k)

theorem hansonC_antitone_right
    {n k l : ℕ} (hkl : k ≤ l) :
    hansonC n l ≤ hansonC n k := by
  rcases hansonDenominator_dvd_hansonDenominator_of_le (n := n) hkl with
    ⟨e, he⟩
  rcases hansonDenominator_dvd_factorial n l with ⟨c, hc⟩
  have hCl : hansonC n l = c := by
    rw [hansonC, hc]
    rw [mul_comm]
    exact Nat.mul_div_left c (hansonDenominator_pos n l)
  have hCk : hansonC n k = e * c := by
    rw [hansonC, hc, he]
    have hmul : hansonDenominator n k * e * c =
        e * c * hansonDenominator n k := by
      ac_rfl
    rw [hmul]
    exact Nat.mul_div_left (e * c) (hansonDenominator_pos n k)
  rw [hCl, hCk]
  have hepos : 0 < e := by
    have hprod_pos : 0 < hansonDenominator n k * e := by
      simpa [← he] using hansonDenominator_pos n l
    exact Nat.pos_of_mul_pos_left hprod_pos
  exact Nat.le_mul_of_pos_left c hepos

def hansonMultinomialPart (n k j : ℕ) : ℕ :=
  if j < k then n / hansonA j
  else if j = k then n - ∑ i ∈ Finset.range k, n / hansonA i
  else 0

theorem hansonMultinomialPart_eq_floor_of_lt
    {n k j : ℕ} (hjk : j < k) :
    hansonMultinomialPart n k j = n / hansonA j := by
  simp [hansonMultinomialPart, hjk]

theorem hansonMultinomialPart_eq_remainder
    (n k : ℕ) :
    hansonMultinomialPart n k k =
      n - ∑ i ∈ Finset.range k, n / hansonA i := by
  simp [hansonMultinomialPart]

theorem hansonMultinomialPart_eq_zero_of_succ_le
    {n k j : ℕ} (hjk : k + 1 ≤ j) :
    hansonMultinomialPart n k j = 0 := by
  have hnot_lt : ¬ j < k := by omega
  have hne : j ≠ k := by omega
  simp [hansonMultinomialPart, hnot_lt, hne]

theorem hansonMultinomialPart_zero_outside_range_succ
    (n k j : ℕ)
    (hj : hansonMultinomialPart n k j ≠ 0) :
    j ∈ Finset.range (k + 1) := by
  rw [Finset.mem_range]
  by_contra hnot
  have hjk : k + 1 ≤ j := Nat.le_of_not_gt hnot
  exact hj (hansonMultinomialPart_eq_zero_of_succ_le (n := n) hjk)

theorem sum_hansonMultinomialPart_range_succ
    (n k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), hansonMultinomialPart n k j) = n := by
  rw [Finset.sum_range_succ]
  have hsum :
      (∑ j ∈ Finset.range k, hansonMultinomialPart n k j) =
        ∑ j ∈ Finset.range k, n / hansonA j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact hansonMultinomialPart_eq_floor_of_lt
      (n := n) (k := k) (Finset.mem_range.mp hj)
  rw [hsum, hansonMultinomialPart_eq_remainder]
  have hle := hanson_floor_sum_le n k
  omega

theorem prod_factorial_hansonMultinomialPart_range_succ
    (n k : ℕ) :
    (∏ j ∈ Finset.range (k + 1),
        Nat.factorial (hansonMultinomialPart n k j)) =
      hansonDenominator n k *
        Nat.factorial (n - ∑ i ∈ Finset.range k, n / hansonA i) := by
  rw [Finset.prod_range_succ]
  have hprod :
      (∏ j ∈ Finset.range k,
          Nat.factorial (hansonMultinomialPart n k j)) =
        ∏ j ∈ Finset.range k, Nat.factorial (n / hansonA j) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    rw [hansonMultinomialPart_eq_floor_of_lt
      (n := n) (k := k) (Finset.mem_range.mp hj)]
  rw [hprod, hansonMultinomialPart_eq_remainder, hansonDenominator]

theorem prod_pow_hansonMultinomialPart_range_succ
    (n k : ℕ) :
    (∏ j ∈ Finset.range (k + 1),
        hansonMultinomialPart n k j ^ hansonMultinomialPart n k j) =
      (∏ j ∈ Finset.range k, (n / hansonA j) ^ (n / hansonA j)) *
        (n - ∑ i ∈ Finset.range k, n / hansonA i) ^
          (n - ∑ i ∈ Finset.range k, n / hansonA i) := by
  rw [Finset.prod_range_succ]
  have hprod :
      (∏ j ∈ Finset.range k,
          hansonMultinomialPart n k j ^ hansonMultinomialPart n k j) =
        ∏ j ∈ Finset.range k, (n / hansonA j) ^ (n / hansonA j) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    rw [hansonMultinomialPart_eq_floor_of_lt
      (n := n) (k := k) (Finset.mem_range.mp hj)]
  rw [hprod, hansonMultinomialPart_eq_remainder]

theorem hansonC_mul_floor_pow_prod_le_pow
    (n k : ℕ) :
    hansonC n k *
        (∏ j ∈ Finset.range k, (n / hansonA j) ^ (n / hansonA j)) ≤
      n ^ n := by
  classical
  let r := n - ∑ i ∈ Finset.range k, n / hansonA i
  let s := Finset.range (k + 1)
  let f := hansonMultinomialPart n k
  have hsum : (∑ j ∈ s, f j) = n := by
    simpa [s, f] using sum_hansonMultinomialPart_range_succ n k
  have hprod_fac :
      (∏ j ∈ s, Nat.factorial (f j)) =
        hansonDenominator n k * Nat.factorial r := by
    simpa [s, f, r] using prod_factorial_hansonMultinomialPart_range_succ n k
  have hprod_pow :
      (∏ j ∈ s, f j ^ f j) =
        (∏ j ∈ Finset.range k, (n / hansonA j) ^ (n / hansonA j)) *
          r ^ r := by
    simpa [s, f, r] using prod_pow_hansonMultinomialPart_range_succ n k
  have hmult_spec := Nat.multinomial_spec s f
  rw [hprod_fac, hsum] at hmult_spec
  have hCeq :
      hansonC n k = Nat.factorial r * Nat.multinomial s f := by
    have hden_ne : hansonDenominator n k ≠ 0 :=
      Nat.ne_of_gt (hansonDenominator_pos n k)
    have hleft :
        hansonDenominator n k *
            (Nat.factorial r * Nat.multinomial s f) =
          hansonDenominator n k * hansonC n k := by
      rw [← Nat.mul_assoc]
      exact hmult_spec.trans (hansonDenominator_mul_hansonC n k).symm
    exact mul_left_cancel₀ hden_ne hleft.symm
  have hterm :=
    multinomial_term_le_sum_pow s f
      (by
        intro j hj
        exact hansonMultinomialPart_zero_outside_range_succ n k j (by simpa [f] using hj))
  rw [hsum, hprod_pow] at hterm
  rw [hCeq]
  calc
    Nat.factorial r * Nat.multinomial s f *
        (∏ j ∈ Finset.range k, (n / hansonA j) ^ (n / hansonA j))
        ≤ r ^ r * Nat.multinomial s f *
            (∏ j ∈ Finset.range k, (n / hansonA j) ^ (n / hansonA j)) := by
          gcongr
          exact Nat.factorial_le_pow r
    _ = Nat.multinomial s f *
          ((∏ j ∈ Finset.range k, (n / hansonA j) ^ (n / hansonA j)) * r ^ r) := by
          ring
    _ ≤ n ^ n := by
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hterm

theorem nat_self_pow_pos (q : ℕ) : 0 < q ^ q := by
  cases q with
  | zero =>
      norm_num
  | succ q =>
      exact pow_pos (Nat.succ_pos q) (q + 1)

theorem one_le_nat_self_pow (q : ℕ) : 1 ≤ q ^ q :=
  Nat.succ_le_iff.mpr (nat_self_pow_pos q)

theorem floor_pow_prod_mono_right {n k l : ℕ} (hkl : k ≤ l) :
    (∏ j ∈ Finset.range k, (n / hansonA j) ^ (n / hansonA j)) ≤
      ∏ j ∈ Finset.range l, (n / hansonA j) ^ (n / hansonA j) := by
  exact Finset.prod_le_prod_of_subset_of_one_le'
    (by
      intro j hj
      exact Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hkl))
    (by
      intro j _ _
      exact one_le_nat_self_pow (n / hansonA j))

theorem log_floor_pow_prod (n k : ℕ) :
    Real.log ((∏ j ∈ Finset.range k,
        (n / hansonA j) ^ (n / hansonA j) : ℕ) : ℝ) =
      ∑ j ∈ Finset.range k,
        ((n / hansonA j : ℕ) : ℝ) *
          Real.log ((n / hansonA j : ℕ) : ℝ) := by
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl ?_
    intro j _
    rw [Nat.cast_pow, Real.log_pow]
  · intro j _
    exact_mod_cast Nat.ne_of_gt (nat_self_pow_pos (n / hansonA j))

theorem log_hansonC_add_floor_pow_log_le_n_log
    {n k : ℕ} (hn : 1 ≤ n) :
    Real.log (hansonC n k : ℝ) +
      ∑ j ∈ Finset.range k,
        ((n / hansonA j : ℕ) : ℝ) *
          Real.log ((n / hansonA j : ℕ) : ℝ) ≤
      (n : ℝ) * Real.log n := by
  let P : ℕ :=
    ∏ j ∈ Finset.range k, (n / hansonA j) ^ (n / hansonA j)
  have hP_pos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun j _ => nat_self_pow_pos (n / hansonA j)
  have hmul_pos : 0 < hansonC n k * P :=
    Nat.mul_pos (hansonC_pos n k) hP_pos
  have hnpos : 0 < n := by omega
  have hpow_pos : 0 < n ^ n := pow_pos hnpos n
  have hmul_le : hansonC n k * P ≤ n ^ n := by
    simpa [P] using hansonC_mul_floor_pow_prod_le_pow n k
  have hmul_le_real :
      ((hansonC n k * P : ℕ) : ℝ) ≤ ((n ^ n : ℕ) : ℝ) := by
    exact_mod_cast hmul_le
  have hlog_le :
      Real.log ((hansonC n k * P : ℕ) : ℝ) ≤
        Real.log ((n ^ n : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hmul_pos) hmul_le_real
  have hleft :
      Real.log ((hansonC n k * P : ℕ) : ℝ) =
        Real.log (hansonC n k : ℝ) + Real.log (P : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul]
    · exact_mod_cast Nat.ne_of_gt (hansonC_pos n k)
    · exact_mod_cast Nat.ne_of_gt hP_pos
  have hright :
      Real.log ((n ^ n : ℕ) : ℝ) = (n : ℝ) * Real.log n := by
    rw [Nat.cast_pow, Real.log_pow]
  have hPlog :
      Real.log (P : ℝ) =
        ∑ j ∈ Finset.range k,
          ((n / hansonA j : ℕ) : ℝ) *
            Real.log ((n / hansonA j : ℕ) : ℝ) := by
    dsimp [P]
    exact log_floor_pow_prod n k
  rw [hleft, hright, hPlog] at hlog_le
  exact hlog_le

theorem log_hansonC_le_log_three_of_floor_pow_log_lower
    {n k : ℕ} (hn : 1 ≤ n)
    (hlower :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ∑ j ∈ Finset.range k,
          ((n / hansonA j : ℕ) : ℝ) *
            Real.log ((n / hansonA j : ℕ) : ℝ)) :
    Real.log (hansonC n k : ℝ) ≤ Real.log 3 * (n : ℝ) := by
  have hlog := log_hansonC_add_floor_pow_log_le_n_log (n := n) (k := k) hn
  linarith

theorem mul_log_mono_of_one_le
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x * Real.log x ≤ y * Real.log y := by
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := lt_of_lt_of_le hx_pos hxy
  exact mul_le_mul hxy (Real.log_le_log hx_pos hxy)
    (Real.log_nonneg hx) (le_of_lt hy_pos)

theorem real_div_sub_one_le_nat_div_cast
    (n a : ℕ) (ha : 0 < a) :
    (n : ℝ) / (a : ℝ) - 1 ≤ ((n / a : ℕ) : ℝ) := by
  have hlt_nat : n < a * (n / a + 1) := by
    calc
      n = n % a + a * (n / a) := by
          exact (Nat.mod_add_div n a).symm
      _ < a + a * (n / a) := by
          exact Nat.add_lt_add_right (Nat.mod_lt n ha) _
      _ = a * (n / a + 1) := by ring
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hltR : (n : ℝ) < (a : ℝ) * (((n / a : ℕ) : ℝ) + 1) := by
    exact_mod_cast hlt_nat
  have hdiv : (n : ℝ) / (a : ℝ) < ((n / a : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ haR]
    simpa [mul_comm] using hltR
  linarith

theorem div_sub_one_mul_log_le_floor_mul_log_of_two_mul_le
    {n a : ℕ} (ha : 0 < a) (h2 : 2 * a ≤ n) :
    ((n : ℝ) / (a : ℝ) - 1) *
        Real.log ((n : ℝ) / (a : ℝ) - 1) ≤
      ((n / a : ℕ) : ℝ) * Real.log ((n / a : ℕ) : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have htwo : (2 : ℝ) ≤ (n : ℝ) / (a : ℝ) := by
    rw [le_div_iff₀ haR]
    exact_mod_cast h2
  have hone : (1 : ℝ) ≤ (n : ℝ) / (a : ℝ) - 1 := by linarith
  exact mul_log_mono_of_one_le hone
    (real_div_sub_one_le_nat_div_cast n a ha)

theorem neg_two_mul_le_log_one_sub
    {t : ℝ} (h0 : 0 ≤ t) (hhalf : t ≤ 1 / 2) :
    -2 * t ≤ Real.log (1 - t) := by
  have hpos : 0 < 1 - t := by linarith
  have hbase : 1 - (1 - t)⁻¹ ≤ Real.log (1 - t) :=
    Real.one_sub_inv_le_log_of_pos hpos
  have hleft : -2 * t ≤ 1 - (1 - t)⁻¹ := by
    have hden : 0 < 1 - t := hpos
    have hrewrite : 1 - (1 - t)⁻¹ = -t / (1 - t) := by
      field_simp [hden.ne']
      ring
    rw [hrewrite]
    by_cases ht : t = 0
    · subst ht
      norm_num
    · have htpos : 0 < t := lt_of_le_of_ne h0 (Ne.symm ht)
      have hdivle : t / (1 - t) ≤ 2 * t := by
        rw [div_le_iff₀ hden]
        nlinarith
      have hneg := neg_le_neg hdivle
      simpa [neg_div, mul_comm, mul_left_comm, mul_assoc] using hneg
  exact hleft.trans hbase

theorem two_mul_hansonA_le_86_of_lt_four {i : ℕ} (hi : i < 4) :
    2 * hansonA i ≤ 86 := by
  interval_cases i <;> norm_num [hansonA]

theorem floor_log_sum_four_lower_of_ge_86
    {n : ℕ} (hn : 86 ≤ n) :
    (∑ i ∈ Finset.range 4,
        ((n : ℝ) / (hansonA i : ℝ) - 1) *
          Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) ≤
      ∑ i ∈ Finset.range 4,
        ((n / hansonA i : ℕ) : ℝ) *
          Real.log ((n / hansonA i : ℕ) : ℝ) := by
  exact Finset.sum_le_sum fun i hi =>
    div_sub_one_mul_log_le_floor_mul_log_of_two_mul_le
      (hansonA_pos i)
      ((two_mul_hansonA_le_86_of_lt_four (Finset.mem_range.mp hi)).trans hn)

theorem floor_pow_log_lower_four_of_shifted_log_lower
    {n : ℕ} (hn : 86 ≤ n)
    (hlower :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ∑ i ∈ Finset.range 4,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) :
    (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
      ∑ j ∈ Finset.range 4,
        ((n / hansonA j : ℕ) : ℝ) *
          Real.log ((n / hansonA j : ℕ) : ℝ) :=
  hlower.trans (floor_log_sum_four_lower_of_ge_86 hn)

theorem hansonC_le_three_pow_of_floor_pow_prod_lower
    (n k : ℕ)
    (hprod :
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range k, (n / hansonA j) ^ (n / hansonA j)) :
    hansonC n k ≤ 3 ^ n := by
  let P : ℕ :=
    ∏ j ∈ Finset.range k, (n / hansonA j) ^ (n / hansonA j)
  have hP_pos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun j _ => nat_self_pow_pos (n / hansonA j)
  have hCP :
      hansonC n k * P ≤ 3 ^ n * P := by
    exact (hansonC_mul_floor_pow_prod_le_pow n k).trans (by simpa [P] using hprod)
  exact Nat.le_of_mul_le_mul_right hCP hP_pos

theorem hansonC_le_three_pow_of_floor_pow_prod_prefix_lower
    (n k l : ℕ) (hkl : k ≤ l)
    (hprod :
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range k, (n / hansonA j) ^ (n / hansonA j)) :
    hansonC n l ≤ 3 ^ n := by
  refine hansonC_le_three_pow_of_floor_pow_prod_lower n l ?_
  exact hprod.trans
    (Nat.mul_le_mul_left _ (floor_pow_prod_mono_right (n := n) hkl))

theorem hansonC_le_three_pow_of_log_le
    (n k : ℕ)
    (hlog :
      Real.log (hansonC n k : ℝ) ≤ Real.log 3 * (n : ℝ)) :
    hansonC n k ≤ 3 ^ n := by
  have hlog' :
      Real.log (hansonC n k : ℝ) ≤ Real.log ((3 ^ n : ℕ) : ℝ) := by
    calc
      Real.log (hansonC n k : ℝ) ≤ Real.log 3 * (n : ℝ) := hlog
      _ = Real.log ((3 ^ n : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
        ring_nf
  have hpow_pos : (0 : ℝ) < ((3 ^ n : ℕ) : ℝ) := by positivity
  exact_mod_cast
    ((Real.log_le_log_iff
      (by exact_mod_cast hansonC_pos n k) hpow_pos).1 hlog')

theorem hansonC_four_le_three_pow_of_shifted_log_lower
    {n : ℕ} (hn : 86 ≤ n)
    (hlower :
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ∑ i ∈ Finset.range 4,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((n : ℝ) / (hansonA i : ℝ) - 1)) :
    hansonC n 4 ≤ 3 ^ n :=
  hansonC_le_three_pow_of_log_le n 4
    (log_hansonC_le_log_three_of_floor_pow_log_lower
      (n := n) (k := 4) (by omega)
      (floor_pow_log_lower_four_of_shifted_log_lower hn hlower))

theorem seven_lt_exp_two : (7 : ℝ) < Real.exp 2 := by
  have hone : (2.7182818283 : ℝ) < Real.exp 1 :=
    Real.exp_one_gt_d9
  have hsq : (7 : ℝ) < (2.7182818283 : ℝ) ^ 2 := by norm_num
  have hsq_exp : (2.7182818283 : ℝ) ^ 2 < (Real.exp 1) ^ 2 := by
    nlinarith
  calc
    (7 : ℝ) < (2.7182818283 : ℝ) ^ 2 := hsq
    _ < (Real.exp 1) ^ 2 := hsq_exp
    _ = Real.exp 2 := by
      rw [← Real.exp_nat_mul]
      norm_num

theorem forty_three_lt_exp_four : (43 : ℝ) < Real.exp 4 := by
  have htwo := seven_lt_exp_two
  have hsq : (43 : ℝ) < (7 : ℝ) ^ 2 := by norm_num
  have hsq_exp : (7 : ℝ) ^ 2 < (Real.exp 2) ^ 2 := by
    nlinarith
  calc
    (43 : ℝ) < (7 : ℝ) ^ 2 := hsq
    _ < (Real.exp 2) ^ 2 := hsq_exp
    _ = Real.exp 4 := by
      rw [← Real.exp_nat_mul]
      norm_num

theorem log_seven_lt_two : Real.log (7 : ℝ) < 2 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 7)).mpr
    seven_lt_exp_two

theorem log_forty_three_lt_four : Real.log (43 : ℝ) < 4 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 43)).mpr
    forty_three_lt_exp_four

theorem hanson_log_weight_four_lt_log_three :
    (1 / 2 : ℝ) * Real.log 2 +
        (1 / 3 : ℝ) * Real.log 3 +
        (1 / 7 : ℝ) * Real.log 7 +
        (1 / 43 : ℝ) * Real.log 43 < Real.log 3 := by
  have h2 : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have h3 : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
  have h7 : Real.log 7 < (2 : ℝ) := log_seven_lt_two
  have h43 : Real.log 43 < (4 : ℝ) := log_forty_three_lt_four
  nlinarith

theorem hanson_reciprocal_sum_four_eq :
    (∑ i ∈ Finset.range 4, (1 : ℚ) / hansonA i) = 1805 / 1806 := by
  norm_num [Finset.sum_range_succ, hansonA]

theorem hanson_log_weight_four_sum_eq :
    (∑ i ∈ Finset.range 4,
      ((1 : ℝ) / hansonA i) * Real.log (hansonA i)) =
        (1 / 2 : ℝ) * Real.log 2 +
          (1 / 3 : ℝ) * Real.log 3 +
          (1 / 7 : ℝ) * Real.log 7 +
          (1 / 43 : ℝ) * Real.log 43 := by
  norm_num [Finset.sum_range_succ, hansonA]

theorem hanson_log_weight_four_sum_lt_log_three :
    (∑ i ∈ Finset.range 4,
      ((1 : ℝ) / hansonA i) * Real.log (hansonA i)) < Real.log 3 := by
  rw [hanson_log_weight_four_sum_eq]
  exact hanson_log_weight_four_lt_log_three

theorem hansonC_four_le_three_pow_of_lt_588
    {n : ℕ} (hn : n < 588) :
    hansonC n 4 ≤ 3 ^ n := by
  set_option maxRecDepth 8192 in
  set_option exponentiation.threshold 4096 in
  revert n
  decide

theorem hansonC_succ_index_le_three_pow_of_lt_588
    {n : ℕ} (hn : n < 588) :
    hansonC n (n + 1) ≤ 3 ^ n := by
  by_cases h4 : 4 ≤ n + 1
  · exact (hansonC_antitone_right (n := n) h4).trans
      (hansonC_four_le_three_pow_of_lt_588 hn)
  · set_option maxRecDepth 8192 in
    set_option exponentiation.threshold 64 in
    revert n
    decide

theorem hansonC_four_le_three_pow_of_lt_882
    {n : ℕ} (hn : n < 882) :
    hansonC n 4 ≤ 3 ^ n := by
  set_option maxRecDepth 8192 in
  set_option exponentiation.threshold 8192 in
  revert n
  decide

theorem hansonC_succ_index_le_three_pow_of_lt_882
    {n : ℕ} (hn : n < 882) :
    hansonC n (n + 1) ≤ 3 ^ n := by
  by_cases h4 : 4 ≤ n + 1
  · exact (hansonC_antitone_right (n := n) h4).trans
      (hansonC_four_le_three_pow_of_lt_882 hn)
  · set_option maxRecDepth 8192 in
    set_option exponentiation.threshold 64 in
    revert n
    decide

theorem floor_pow_prod_four_lower_of_ge_882_lt_1807
    {n : ℕ} (hlo : 882 ≤ n) (hhi : n < 1807) :
    n ^ n ≤
      3 ^ n *
        ∏ j ∈ Finset.range 4, (n / hansonA j) ^ (n / hansonA j) := by
  set_option maxRecDepth 8192 in
  set_option exponentiation.threshold 8192 in
  revert n
  decide

theorem hansonC_succ_index_le_three_pow_of_ge_882_lt_1807
    {n : ℕ} (hlo : 882 ≤ n) (hhi : n < 1807) :
    hansonC n (n + 1) ≤ 3 ^ n :=
  hansonC_le_three_pow_of_floor_pow_prod_prefix_lower
    n 4 (n + 1) (by omega)
    (floor_pow_prod_four_lower_of_ge_882_lt_1807 hlo hhi)

theorem floor_pow_prod_four_lower_of_ge_1807_lt_2048
    {n : ℕ} (hlo : 1807 ≤ n) (hhi : n < 2048) :
    n ^ n ≤
      3 ^ n *
        ∏ j ∈ Finset.range 4, (n / hansonA j) ^ (n / hansonA j) := by
  set_option maxRecDepth 8192 in
  set_option exponentiation.threshold 8192 in
  revert n
  decide

theorem hansonC_succ_index_le_three_pow_of_ge_1807_lt_2048
    {n : ℕ} (hlo : 1807 ≤ n) (hhi : n < 2048) :
    hansonC n (n + 1) ≤ 3 ^ n :=
  hansonC_le_three_pow_of_floor_pow_prod_prefix_lower
    n 4 (n + 1) (by omega)
    (floor_pow_prod_four_lower_of_ge_1807_lt_2048 hlo hhi)

theorem log_hansonDenominator (n k : ℕ) :
    Real.log (hansonDenominator n k : ℝ) =
      ∑ i ∈ Finset.range k,
        Real.log (Nat.factorial (n / hansonA i) : ℝ) := by
  rw [hansonDenominator]
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  intro i _
  exact_mod_cast Nat.factorial_ne_zero (n / hansonA i)

theorem log_hansonC_eq_log_factorial_sub_sum (n k : ℕ) :
    Real.log (hansonC n k : ℝ) =
      Real.log (Nat.factorial n : ℝ) -
        ∑ i ∈ Finset.range k,
          Real.log (Nat.factorial (n / hansonA i) : ℝ) := by
  have hmul := hansonDenominator_mul_hansonC n k
  have hlog_mul :
      Real.log (hansonDenominator n k : ℝ) + Real.log (hansonC n k : ℝ) =
        Real.log (Nat.factorial n : ℝ) := by
    rw [← Real.log_mul]
    · rw [← Nat.cast_mul, hmul]
    · exact_mod_cast Nat.ne_of_gt (hansonDenominator_pos n k)
    · exact_mod_cast Nat.ne_of_gt (hansonC_pos n k)
  rw [log_hansonDenominator] at hlog_mul
  linarith

theorem log_factorial_eq_sum_range_log_succ (n : ℕ) :
    Real.log (Nat.factorial n : ℝ) =
      ∑ i ∈ Finset.range n,
        Real.log ((i + 1 : ℕ) : ℝ) := by
  rw [Nat.factorial_eq_prod_range_add_one]
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  intro i _
  exact_mod_cast Nat.succ_ne_zero i

theorem log_factorial_le_sub_add
    {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Nat.factorial n : ℝ) ≤
      (n : ℝ) * Real.log n - (n : ℝ) + Real.log n + 1 := by
  rw [log_factorial_eq_sum_range_log_succ]
  have hsum_eq :
      (∑ i ∈ Finset.range n, Real.log ((i + 1 : ℕ) : ℝ)) =
        ∑ j ∈ Finset.Ico 1 (n + 1), Real.log (j : ℝ) := by
    rw [← Nat.Ico_zero_eq_range]
    simpa using
      (Finset.sum_Ico_add' (fun j : ℕ => Real.log (j : ℝ)) 0 n 1)
  rw [hsum_eq]
  have hsplit :
      (∑ j ∈ Finset.Ico 1 (n + 1), Real.log (j : ℝ)) =
        (∑ j ∈ Finset.Ico 1 n, Real.log (j : ℝ)) +
          Real.log (n : ℝ) := by
    exact Finset.sum_Ico_succ_top hn
      (fun j : ℕ => Real.log (j : ℝ))
  rw [hsplit]
  have hmono : MonotoneOn (fun x : ℝ => Real.log x)
      (Set.Icc (((1 : ℕ) : ℝ)) (n : ℝ)) := by
    intro x hx _ _ hxy
    exact Real.log_le_log (by norm_num at hx ⊢; linarith [hx.1]) hxy
  have hsum_le :
      (∑ j ∈ Finset.Ico 1 n, Real.log (j : ℝ)) ≤
        ∫ x in (((1 : ℕ) : ℝ))..(n : ℝ), Real.log x := by
    exact MonotoneOn.sum_le_integral_Ico
      (f := fun x : ℝ => Real.log x) hn hmono
  have hsum_le' :
      (∑ j ∈ Finset.Ico 1 n, Real.log (j : ℝ)) ≤
        (n : ℝ) * Real.log n - (n : ℝ) + 1 := by
    rw [integral_log] at hsum_le
    norm_num at hsum_le
    exact hsum_le
  nlinarith [hsum_le']

noncomputable def hansonStirlingLogLower (q : ℕ) : ℝ :=
  (q : ℝ) * Real.log q - (q : ℝ) +
    Real.log q / 2 + Real.log (2 * Real.pi) / 2

theorem hansonStirlingLogLower_le_log_factorial
    {q : ℕ} (hq : q ≠ 0) :
    hansonStirlingLogLower q ≤ Real.log (Nat.factorial q : ℝ) := by
  exact Stirling.le_log_factorial_stirling hq

theorem sum_hansonStirlingLogLower_le_hansonDenominator_log_sum
    (n k : ℕ) :
    (∑ i ∈ (Finset.range k).filter (fun i => 0 < n / hansonA i),
      hansonStirlingLogLower (n / hansonA i)) ≤
      ∑ i ∈ Finset.range k,
        Real.log (Nat.factorial (n / hansonA i) : ℝ) := by
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  by_cases hq : 0 < n / hansonA i
  · rw [if_pos hq]
    exact hansonStirlingLogLower_le_log_factorial
      (q := n / hansonA i) (Nat.ne_of_gt hq)
  · rw [if_neg hq]
    have hzero : n / hansonA i = 0 := Nat.eq_zero_of_not_pos hq
    simp [hzero]

theorem log_hansonC_le_factorial_upper_sub_stirling_sum
    {n k : ℕ} (hn : 1 ≤ n) :
    Real.log (hansonC n k : ℝ) ≤
      ((n : ℝ) * Real.log n - (n : ℝ) + Real.log n + 1) -
        ∑ i ∈ (Finset.range k).filter (fun i => 0 < n / hansonA i),
          hansonStirlingLogLower (n / hansonA i) := by
  rw [log_hansonC_eq_log_factorial_sub_sum]
  have hnum := log_factorial_le_sub_add hn
  have hden := sum_hansonStirlingLogLower_le_hansonDenominator_log_sum n k
  linarith

theorem sum_hansonStirlingLogLower_two_le_le_hansonDenominator_log_sum
    (n k : ℕ) :
    (∑ i ∈ (Finset.range k).filter (fun i => 2 ≤ n / hansonA i),
      hansonStirlingLogLower (n / hansonA i)) ≤
      ∑ i ∈ Finset.range k,
        Real.log (Nat.factorial (n / hansonA i) : ℝ) := by
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  by_cases hq : 2 ≤ n / hansonA i
  · rw [if_pos hq]
    exact hansonStirlingLogLower_le_log_factorial
      (q := n / hansonA i) (by omega)
  · rw [if_neg hq]
    exact Real.log_nonneg (by
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos (n / hansonA i)))

theorem log_hansonC_le_factorial_upper_sub_stirling_two_le_sum
    {n k : ℕ} (hn : 1 ≤ n) :
    Real.log (hansonC n k : ℝ) ≤
      ((n : ℝ) * Real.log n - (n : ℝ) + Real.log n + 1) -
        ∑ i ∈ (Finset.range k).filter (fun i => 2 ≤ n / hansonA i),
          hansonStirlingLogLower (n / hansonA i) := by
  rw [log_hansonC_eq_log_factorial_sub_sum]
  have hnum := log_factorial_le_sub_add hn
  have hden := sum_hansonStirlingLogLower_two_le_le_hansonDenominator_log_sum n k
  linarith

theorem lcmUpto_dvd_of_factorization_log_le
    (n m : ℕ) (hm : m ≠ 0)
    (hfac : ∀ p : ℕ, p.Prime → p.log n ≤ m.factorization p) :
    Nat.lcmUpto n ∣ m := by
  rw [← Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero n) hm]
  intro p hp
  rw [Nat.factorization_lcmUpto n hp]
  exact hfac p hp

theorem lcmUpto_dvd_hansonC_of_factorization_log_le
    (n k : ℕ)
    (hfac : ∀ p : ℕ, p.Prime → p.log n ≤ (hansonC n k).factorization p) :
    Nat.lcmUpto n ∣ hansonC n k :=
  lcmUpto_dvd_of_factorization_log_le
    n (hansonC n k) (Nat.ne_of_gt (hansonC_pos n k)) hfac

theorem hansonC_factorization_log_le
    (n k p : ℕ) (hp : p.Prime) :
    p.log n ≤ (hansonC n k).factorization p := by
  let b := p.log n + 1
  have hb : p.log n < b := Nat.lt_succ_self _
  have hfac_n : (Nat.factorial n).factorization p =
      ∑ r ∈ Finset.Ico 1 b, n / p ^ r := by
    exact Nat.factorization_factorial hp hb
  have hfac_den : (hansonDenominator n k).factorization p =
      ∑ i ∈ Finset.range k, ∑ r ∈ Finset.Ico 1 b,
        (n / hansonA i) / p ^ r := by
    rw [hansonDenominator, Nat.factorization_prod_apply]
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [Nat.factorization_factorial hp]
      exact (Nat.log_mono_right (Nat.div_le_self n (hansonA i))).trans_lt hb
    · intro i _
      exact Nat.factorial_ne_zero _
  have hfac_C : (hansonC n k).factorization p =
      (∑ r ∈ Finset.Ico 1 b, n / p ^ r) -
        ∑ i ∈ Finset.range k, ∑ r ∈ Finset.Ico 1 b,
          (n / hansonA i) / p ^ r := by
    rw [hansonC, Nat.factorization_div (hansonDenominator_dvd_factorial n k)]
    rw [Finsupp.coe_tsub, Pi.sub_apply, hfac_n, hfac_den]
  rw [hfac_C]
  have hcomm :
      (∑ i ∈ Finset.range k, ∑ r ∈ Finset.Ico 1 b,
          (n / hansonA i) / p ^ r) =
        ∑ r ∈ Finset.Ico 1 b, ∑ i ∈ Finset.range k,
          (n / hansonA i) / p ^ r := by
    rw [Finset.sum_comm]
  rw [hcomm]
  have hcard : (Finset.Ico 1 b).card = p.log n := by
    simp [b]
  rw [← hcard]
  apply card_le_sum_sub_sum_of_succ_le
  intro r hr
  have hrmem := Finset.mem_Ico.mp hr
  have hrle : r ≤ p.log n := by
    exact Nat.lt_succ_iff.mp hrmem.2
  have hnz : n ≠ 0 := by
    intro hn
    subst hn
    simp [b] at hrmem
    omega
  have hpowle : p ^ r ≤ n := Nat.pow_le_of_le_log hnz hrle
  have hpos : 0 < n / p ^ r := Nat.div_pos hpowle (pow_pos hp.pos r)
  exact hanson_legendre_floor_sum_succ_le hpos

theorem lcmUpto_dvd_hansonC (n k : ℕ) :
    Nat.lcmUpto n ∣ hansonC n k :=
  lcmUpto_dvd_hansonC_of_factorization_log_le
    n k (hansonC_factorization_log_le n k)

def LcmDvdCertificate.ofHansonC
    (n k : ℕ)
    (hfac : ∀ p : ℕ, p.Prime → p.log n ≤ (hansonC n k).factorization p)
    (hsmall : hansonC n k ≤ 3 ^ n) :
    LcmDvdCertificate n where
  witness := hansonC n k
  dvd_witness := lcmUpto_dvd_hansonC_of_factorization_log_le n k hfac
  witness_pos := hansonC_pos n k
  witness_le_three_pow := hsmall

def LcmDvdCertificate.ofHansonCUpperBound
    (n k : ℕ)
    (hsmall : hansonC n k ≤ 3 ^ n) :
    LcmDvdCertificate n where
  witness := hansonC n k
  dvd_witness := lcmUpto_dvd_hansonC n k
  witness_pos := hansonC_pos n k
  witness_le_three_pow := hsmall

theorem lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family
    (k : ℕ → ℕ)
    (hsmall : ∀ n : ℕ, hansonC n (k n) ≤ 3 ^ n) :
    lcmUpto_le_three_pow_nat_statement :=
  lcmUpto_le_three_pow_nat_of_certificate_family fun n =>
    LcmDvdCertificate.ofHansonCUpperBound n (k n) (hsmall n)

theorem lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
    (N : ℕ)
    (hfinite : ∀ n : ℕ, n < N → Nat.lcmUpto n ≤ 3 ^ n)
    (k : ℕ → ℕ)
    (hsmall : ∀ n : ℕ, N ≤ n → hansonC n (k n) ≤ 3 ^ n) :
    lcmUpto_le_three_pow_nat_statement :=
  lcmUpto_le_three_pow_nat_of_certificate_family_ge N hfinite fun n hn =>
    LcmDvdCertificate.ofHansonCUpperBound n (k n) (hsmall n hn)

theorem lcmUpto_le_three_pow_nat_of_hansonC_succ_index_log_bound_ge_588
    (hlog : ∀ n : ℕ, 588 ≤ n →
      Real.log (hansonC n (n + 1) : ℝ) ≤ Real.log 3 * (n : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
    588 ?_ (fun n => n + 1) ?_
  · intro n hn
    exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
      (hansonC_succ_index_le_three_pow_of_lt_588 hn)).bound
  · intro n hn
    exact hansonC_le_three_pow_of_log_le n (n + 1) (hlog n hn)

theorem lcmUpto_le_three_pow_nat_of_hansonC_succ_index_log_bound_ge_882
    (hlog : ∀ n : ℕ, 882 ≤ n →
      Real.log (hansonC n (n + 1) : ℝ) ≤ Real.log 3 * (n : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
    882 ?_ (fun n => n + 1) ?_
  · intro n hn
    exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
      (hansonC_succ_index_le_three_pow_of_lt_882 hn)).bound
  · intro n hn
    exact hansonC_le_three_pow_of_log_le n (n + 1) (hlog n hn)

theorem lcmUpto_le_three_pow_nat_of_hansonC_succ_index_floor_pow_log_lower_ge_588
    (hlower : ∀ n : ℕ, 588 ≤ n →
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ∑ j ∈ Finset.range (n + 1),
          ((n / hansonA j : ℕ) : ℝ) *
            Real.log ((n / hansonA j : ℕ) : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_succ_index_log_bound_ge_588 ?_
  intro n hn
  exact log_hansonC_le_log_three_of_floor_pow_log_lower
    (n := n) (k := n + 1) (by omega) (hlower n hn)

theorem lcmUpto_le_three_pow_nat_of_hansonC_succ_index_floor_pow_log_lower_ge_882
    (hlower : ∀ n : ℕ, 882 ≤ n →
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ∑ j ∈ Finset.range (n + 1),
          ((n / hansonA j : ℕ) : ℝ) *
            Real.log ((n / hansonA j : ℕ) : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_succ_index_log_bound_ge_882 ?_
  intro n hn
  exact log_hansonC_le_log_three_of_floor_pow_log_lower
    (n := n) (k := n + 1) (by omega) (hlower n hn)

theorem lcmUpto_le_three_pow_nat_of_hansonC_succ_index_floor_pow_prod_lower_ge_882
    (hprod : ∀ n : ℕ, 882 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (n + 1),
            (n / hansonA j) ^ (n / hansonA j)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
    882 ?_ (fun n => n + 1) ?_
  · intro n hn
    exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
      (hansonC_succ_index_le_three_pow_of_lt_882 hn)).bound
  · intro n hn
    exact hansonC_le_three_pow_of_floor_pow_prod_lower
      n (n + 1) (hprod n hn)

theorem lcmUpto_le_three_pow_nat_of_hansonC_floor_pow_prod_prefix_lower_ge_882
    (k : ℕ → ℕ)
    (hk : ∀ n : ℕ, 882 ≤ n → k n ≤ n + 1)
    (hprod : ∀ n : ℕ, 882 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (k n),
            (n / hansonA j) ^ (n / hansonA j)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
    882 ?_ (fun n => n + 1) ?_
  · intro n hn
    exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
      (hansonC_succ_index_le_three_pow_of_lt_882 hn)).bound
  · intro n hn
    exact hansonC_le_three_pow_of_floor_pow_prod_prefix_lower
      n (k n) (n + 1) (hk n hn) (hprod n hn)

theorem lcmUpto_le_three_pow_nat_of_hansonC_floor_pow_prod_prefix_lower_ge_1807
    (k : ℕ → ℕ)
    (hk : ∀ n : ℕ, 1807 ≤ n → k n ≤ n + 1)
    (hprod : ∀ n : ℕ, 1807 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (k n),
            (n / hansonA j) ^ (n / hansonA j)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
    1807 ?_ (fun n => n + 1) ?_
  · intro n hn
    by_cases h882 : n < 882
    · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
        (hansonC_succ_index_le_three_pow_of_lt_882 h882)).bound
    · exact (LcmDvdCertificate.ofHansonCUpperBound n (n + 1)
        (hansonC_succ_index_le_three_pow_of_ge_882_lt_1807
          (Nat.le_of_not_gt h882) hn)).bound
  · intro n hn
    exact hansonC_le_three_pow_of_floor_pow_prod_prefix_lower
      n (k n) (n + 1) (hk n hn) (hprod n hn)

theorem lcmUpto_le_three_pow_nat_of_hansonC_floor_pow_prod_prefix_lower_ge_2048
    (k : ℕ → ℕ)
    (hk : ∀ n : ℕ, 2048 ≤ n → k n ≤ n + 1)
    (hprod : ∀ n : ℕ, 2048 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (k n),
            (n / hansonA j) ^ (n / hansonA j)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
    2048 ?_ (fun n => n + 1) ?_
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
    exact hansonC_le_three_pow_of_floor_pow_prod_prefix_lower
      n (k n) (n + 1) (hk n hn) (hprod n hn)

theorem lcmUpto_le_three_pow_nat_of_hansonC_succ_index_floor_pow_prod_lower_ge_2048
    (hprod : ∀ n : ℕ, 2048 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (n + 1),
            (n / hansonA j) ^ (n / hansonA j)) :
    lcmUpto_le_three_pow_nat_statement := by
  exact lcmUpto_le_three_pow_nat_of_hansonC_floor_pow_prod_prefix_lower_ge_2048
    (fun n => n + 1) (fun _ _ => le_rfl) hprod

theorem lcmUpto_le_three_pow_nat_of_hansonC_four_prod_lower_ge_2048_lt_hansonA_five
    (hprod4 : ∀ n : ℕ, 2048 ≤ n → n < hansonA 5 →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range 4, (n / hansonA j) ^ (n / hansonA j))
    (htail : ∀ n : ℕ, hansonA 5 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (n + 1),
            (n / hansonA j) ^ (n / hansonA j)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_floor_pow_prod_prefix_lower_ge_2048
    (fun n => n + 1) (fun _ _ => le_rfl) ?_
  intro n hn
  by_cases hsmall : n < hansonA 5
  · exact (hprod4 n hn hsmall).trans
      (Nat.mul_le_mul_left _ (floor_pow_prod_mono_right (n := n) (by omega : 4 ≤ n + 1)))
  · exact htail n (Nat.le_of_not_gt hsmall)

theorem lcmUpto_le_three_pow_nat_of_hansonC_four_shifted_log_lower_ge_2048_lt_hansonA_five
    (hlog4 : ∀ n : ℕ, 2048 ≤ n → n < hansonA 5 →
      (n : ℝ) * Real.log n - Real.log 3 * (n : ℝ) ≤
        ∑ i ∈ Finset.range 4,
          ((n : ℝ) / (hansonA i : ℝ) - 1) *
            Real.log ((n : ℝ) / (hansonA i : ℝ) - 1))
    (htail : ∀ n : ℕ, hansonA 5 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (n + 1),
            (n / hansonA j) ^ (n / hansonA j)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
    2048 ?_ (fun n => n + 1) ?_
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
    by_cases hsmall : n < hansonA 5
    · exact (hansonC_antitone_right (n := n) (by omega : 4 ≤ n + 1)).trans
        (hansonC_four_le_three_pow_of_shifted_log_lower
          (by omega : 86 ≤ n) (hlog4 n hn hsmall))
    · exact hansonC_le_three_pow_of_floor_pow_prod_lower
        n (n + 1) (htail n (Nat.le_of_not_gt hsmall))

theorem lcmUpto_le_three_pow_nat_of_hansonC_succ_index_stirling_tail_ge_588
    (htail : ∀ n : ℕ, 588 ≤ n →
      ((n : ℝ) * Real.log n - (n : ℝ) + Real.log n + 1) -
        ∑ i ∈ (Finset.range (n + 1)).filter (fun i => 0 < n / hansonA i),
          hansonStirlingLogLower (n / hansonA i) ≤
        Real.log 3 * (n : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_succ_index_log_bound_ge_588 ?_
  intro n hn
  exact (log_hansonC_le_factorial_upper_sub_stirling_sum
    (n := n) (k := n + 1) (by omega)).trans (htail n hn)

theorem lcmUpto_le_three_pow_nat_of_hansonC_succ_index_stirling_two_le_tail_ge_588
    (htail : ∀ n : ℕ, 588 ≤ n →
      ((n : ℝ) * Real.log n - (n : ℝ) + Real.log n + 1) -
        ∑ i ∈ (Finset.range (n + 1)).filter (fun i => 2 ≤ n / hansonA i),
          hansonStirlingLogLower (n / hansonA i) ≤
        Real.log 3 * (n : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_hansonC_succ_index_log_bound_ge_588 ?_
  intro n hn
  exact (log_hansonC_le_factorial_upper_sub_stirling_two_le_sum
    (n := n) (k := n + 1) (by omega)).trans (htail n hn)

theorem lcmUpto_le_three_pow_nat_of_ge_257
    (hlarge : ∀ n : ℕ, 257 ≤ n → Nat.lcmUpto n ≤ 3 ^ n) :
    lcmUpto_le_three_pow_nat_statement := by
  intro n
  by_cases hn : n ≤ 256
  · exact lcmUpto_le_three_pow_nat_of_le_256 hn
  · exact hlarge n (by omega)

theorem lcmUpto_le_three_pow_nat_of_mid_257_512_and_ge_513
    (hmid : ∀ n : ℕ, 257 ≤ n → n ≤ 512 → Nat.lcmUpto n ≤ 3 ^ n)
    (hlarge : ∀ n : ℕ, 513 ≤ n → Nat.lcmUpto n ≤ 3 ^ n) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_ge_257 ?_
  intro n hn
  by_cases h512 : n ≤ 512
  · exact hmid n hn h512
  · exact hlarge n (by omega)

theorem lcmUpto_le_three_pow_nat_of_log_lcmUpto_le_ge_257
    (hlarge : ∀ n : ℕ, 257 ≤ n →
      Real.log (Nat.lcmUpto n : ℝ) ≤ Real.log 3 * (n : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_ge_257 ?_
  intro n hn
  exact lcmUpto_le_three_pow_nat_of_log_lcmUpto_le_at n (hlarge n hn)

theorem lcmUpto_le_three_pow_nat_of_psi_le_log_three_ge_257
    (hlarge : ∀ n : ℕ, 257 ≤ n →
      Chebyshev.psi n ≤ Real.log 3 * (n : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_log_lcmUpto_le_ge_257 ?_
  intro n hn
  calc
    Real.log (Nat.lcmUpto n : ℝ) = Chebyshev.psi n := by
      rw [Chebyshev.psi_eq_log_lcmUpto]
    _ ≤ Real.log 3 * (n : ℝ) := hlarge n hn

theorem lcmUpto_le_three_pow_nat_of_strong_even_odd_increment_bounds
    (hstep_even : ∀ n : ℕ, Nat.lcmUpto (2 * n) ≤ 3 ^ n * Nat.lcmUpto n)
    (hstep_odd : ∀ n : ℕ, Nat.lcmUpto (2 * n + 1) ≤ 3 ^ (n + 1) * Nat.lcmUpto n) :
    lcmUpto_le_three_pow_nat_statement := by
  intro n
  induction n using Nat.evenOddRec with
  | h0 =>
      simp [Nat.lcmUpto]
  | h_even n ih =>
      calc
        Nat.lcmUpto (2 * n) ≤ 3 ^ n * Nat.lcmUpto n := hstep_even n
        _ ≤ 3 ^ n * 3 ^ n := Nat.mul_le_mul_left _ ih
        _ = 3 ^ (2 * n) := by
          rw [← pow_add]
          congr 1
          omega
  | h_odd n ih =>
      calc
        Nat.lcmUpto (2 * n + 1) ≤ 3 ^ (n + 1) * Nat.lcmUpto n := hstep_odd n
        _ ≤ 3 ^ (n + 1) * 3 ^ n := Nat.mul_le_mul_left _ ih
        _ = 3 ^ (2 * n + 1) := by
          rw [← pow_add]
          congr 1
          omega

theorem lcmUpto_le_three_pow_nat_of_eventual_even_odd_increment_bounds
    (N : ℕ)
    (hfinite : ∀ n : ℕ, n ≤ 2 * N + 1 → Nat.lcmUpto n ≤ 3 ^ n)
    (hstep_even :
      ∀ n : ℕ, N ≤ n → Nat.lcmUpto (2 * n) ≤ 3 ^ n * Nat.lcmUpto n)
    (hstep_odd :
      ∀ n : ℕ, N ≤ n → Nat.lcmUpto (2 * n + 1) ≤
        3 ^ (n + 1) * Nat.lcmUpto n) :
    lcmUpto_le_three_pow_nat_statement := by
  intro n
  induction n using Nat.evenOddRec with
  | h0 =>
      exact hfinite 0 (by omega)
  | h_even n ih =>
      by_cases hN : N ≤ n
      · calc
          Nat.lcmUpto (2 * n) ≤ 3 ^ n * Nat.lcmUpto n := hstep_even n hN
          _ ≤ 3 ^ n * 3 ^ n := Nat.mul_le_mul_left _ ih
          _ = 3 ^ (2 * n) := by
            rw [← pow_add]
            congr 1
            omega
      · exact hfinite (2 * n) (by omega)
  | h_odd n ih =>
      by_cases hN : N ≤ n
      · calc
          Nat.lcmUpto (2 * n + 1) ≤ 3 ^ (n + 1) * Nat.lcmUpto n :=
            hstep_odd n hN
          _ ≤ 3 ^ (n + 1) * 3 ^ n := Nat.mul_le_mul_left _ ih
          _ = 3 ^ (2 * n + 1) := by
            rw [← pow_add]
            congr 1
            omega
      · exact hfinite (2 * n + 1) (by omega)

theorem Nat.lcmUpto_two_mul_le_three_pow_mul_lcmUpto_of_psi_increment
    (n : ℕ)
    (hpsi :
      Chebyshev.psi (2 * n) - Chebyshev.psi n ≤ Real.log 3 * (n : ℝ)) :
    Nat.lcmUpto (2 * n) ≤ 3 ^ n * Nat.lcmUpto n := by
  have hlog :
      Real.log (Nat.lcmUpto (2 * n) : ℝ) ≤
        Real.log ((3 ^ n * Nat.lcmUpto n : ℕ) : ℝ) := by
    have hlog_lcm :
        Real.log (Nat.lcmUpto (2 * n) : ℝ) =
          Chebyshev.psi (2 * n) := by
      simpa [Nat.cast_mul] using (Chebyshev.psi_eq_log_lcmUpto (2 * n)).symm
    have hlog_rhs :
        Real.log ((3 ^ n * Nat.lcmUpto n : ℕ) : ℝ) =
          Real.log 3 * (n : ℝ) + Chebyshev.psi n := by
      have hpow_ne : ((3 ^ n : ℕ) : ℝ) ≠ 0 := by positivity
      have hlcm_ne : ((Nat.lcmUpto n : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.lcmUpto_ne_zero n
      rw [Nat.cast_mul, Real.log_mul hpow_ne hlcm_ne]
      rw [Nat.cast_pow, Real.log_pow, ← Chebyshev.psi_eq_log_lcmUpto]
      ring_nf
    rw [hlog_lcm, hlog_rhs]
    linarith
  have hlhs_pos : (0 : ℝ) < (Nat.lcmUpto (2 * n) : ℝ) := by
    exact_mod_cast Nat.lcmUpto_pos (2 * n)
  have hrhs_pos : (0 : ℝ) < ((3 ^ n * Nat.lcmUpto n : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (pow_pos (by omega : 0 < 3) n) (Nat.lcmUpto_pos n)
  exact_mod_cast ((Real.log_le_log_iff hlhs_pos hrhs_pos).1 hlog)

theorem Nat.lcmUpto_two_mul_add_one_le_three_pow_mul_lcmUpto_of_psi_increment
    (n : ℕ)
    (hpsi :
      Chebyshev.psi (2 * n + 1) - Chebyshev.psi n ≤
        Real.log 3 * ((n + 1 : ℕ) : ℝ)) :
    Nat.lcmUpto (2 * n + 1) ≤ 3 ^ (n + 1) * Nat.lcmUpto n := by
  have hlog :
      Real.log (Nat.lcmUpto (2 * n + 1) : ℝ) ≤
        Real.log ((3 ^ (n + 1) * Nat.lcmUpto n : ℕ) : ℝ) := by
    have hlog_lcm :
        Real.log (Nat.lcmUpto (2 * n + 1) : ℝ) =
          Chebyshev.psi (2 * n + 1) := by
      simpa [Nat.cast_add, Nat.cast_mul] using
        (Chebyshev.psi_eq_log_lcmUpto (2 * n + 1)).symm
    have hlog_rhs :
        Real.log ((3 ^ (n + 1) * Nat.lcmUpto n : ℕ) : ℝ) =
          Real.log 3 * ((n + 1 : ℕ) : ℝ) + Chebyshev.psi n := by
      have hpow_ne : ((3 ^ (n + 1) : ℕ) : ℝ) ≠ 0 := by positivity
      have hlcm_ne : ((Nat.lcmUpto n : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.lcmUpto_ne_zero n
      rw [Nat.cast_mul, Real.log_mul hpow_ne hlcm_ne]
      rw [Nat.cast_pow, Real.log_pow, ← Chebyshev.psi_eq_log_lcmUpto]
      ring_nf
    rw [hlog_lcm, hlog_rhs]
    linarith
  have hlhs_pos : (0 : ℝ) < (Nat.lcmUpto (2 * n + 1) : ℝ) := by
    exact_mod_cast Nat.lcmUpto_pos (2 * n + 1)
  have hrhs_pos : (0 : ℝ) < ((3 ^ (n + 1) * Nat.lcmUpto n : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (pow_pos (by omega : 0 < 3) (n + 1)) (Nat.lcmUpto_pos n)
  exact_mod_cast ((Real.log_le_log_iff hlhs_pos hrhs_pos).1 hlog)

theorem lcmUpto_le_three_pow_nat_of_psi_increment_bounds_eventual
    (N : ℕ)
    (hfinite : ∀ n : ℕ, n ≤ 2 * N + 1 → Nat.lcmUpto n ≤ 3 ^ n)
    (hpsi_even :
      ∀ n : ℕ, N ≤ n →
        Chebyshev.psi (2 * n) - Chebyshev.psi n ≤ Real.log 3 * (n : ℝ))
    (hpsi_odd :
      ∀ n : ℕ, N ≤ n →
        Chebyshev.psi (2 * n + 1) - Chebyshev.psi n ≤
          Real.log 3 * ((n + 1 : ℕ) : ℝ)) :
    lcmUpto_le_three_pow_nat_statement :=
  lcmUpto_le_three_pow_nat_of_eventual_even_odd_increment_bounds
    N hfinite
    (fun n hn =>
      Nat.lcmUpto_two_mul_le_three_pow_mul_lcmUpto_of_psi_increment
        n (hpsi_even n hn))
    (fun n hn =>
      Nat.lcmUpto_two_mul_add_one_le_three_pow_mul_lcmUpto_of_psi_increment
        n (hpsi_odd n hn))

theorem lcmUpto_le_three_pow_nat_of_psi_increment_bounds_ge_101
    (hpsi_even :
      ∀ n : ℕ, 101 ≤ n →
        Chebyshev.psi (2 * n) - Chebyshev.psi n ≤ Real.log 3 * (n : ℝ))
    (hpsi_odd :
      ∀ n : ℕ, 101 ≤ n →
        Chebyshev.psi (2 * n + 1) - Chebyshev.psi n ≤
          Real.log 3 * ((n + 1 : ℕ) : ℝ)) :
    lcmUpto_le_three_pow_nat_statement :=
  lcmUpto_le_three_pow_nat_of_psi_increment_bounds_eventual
    101 (fun n hn => lcmUpto_le_three_pow_nat_of_le_256 (by omega))
    hpsi_even hpsi_odd

theorem psi_two_mul_sub_psi_le_theta_increment_add_error
    (n : ℕ) (hn : 1 ≤ n) :
    Chebyshev.psi ((2 * n : ℕ) : ℝ) - Chebyshev.psi (n : ℝ) ≤
      (Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
        2 * Real.sqrt (((2 * n : ℕ) : ℝ)) *
          Real.log (((2 * n : ℕ) : ℝ)) := by
  have harg : (1 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * n)
  have htail :=
    Chebyshev.psi_sub_theta_le
      (x := ((2 * n : ℕ) : ℝ)) harg
  have htheta_le_psi := Chebyshev.theta_le_psi (n : ℝ)
  linarith

theorem psi_two_mul_add_one_sub_psi_le_theta_increment_add_error
    (n : ℕ) :
    Chebyshev.psi ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.psi (n : ℝ) ≤
      (Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
        2 * Real.sqrt (((2 * n + 1 : ℕ) : ℝ)) *
          Real.log (((2 * n + 1 : ℕ) : ℝ)) := by
  have harg : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * n + 1)
  have htail :=
    Chebyshev.psi_sub_theta_le
      (x := ((2 * n + 1 : ℕ) : ℝ)) harg
  have htheta_le_psi := Chebyshev.theta_le_psi (n : ℝ)
  linarith

theorem lcmUpto_le_three_pow_nat_of_theta_increment_error_bounds_ge_101
    (htheta_even :
      ∀ n : ℕ, 101 ≤ n →
        (Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
          2 * Real.sqrt (((2 * n : ℕ) : ℝ)) *
            Real.log (((2 * n : ℕ) : ℝ)) ≤
          Real.log 3 * (n : ℝ))
    (htheta_odd :
      ∀ n : ℕ, 101 ≤ n →
        (Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
          2 * Real.sqrt (((2 * n + 1 : ℕ) : ℝ)) *
            Real.log (((2 * n + 1 : ℕ) : ℝ)) ≤
          Real.log 3 * ((n + 1 : ℕ) : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_psi_increment_bounds_ge_101 ?_ ?_
  · intro n hn
    have hpsi :=
      psi_two_mul_sub_psi_le_theta_increment_add_error n (by omega)
    have hpsi' :
        Chebyshev.psi (2 * n) - Chebyshev.psi n ≤
          (Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
            2 * Real.sqrt (((2 * n : ℕ) : ℝ)) *
              Real.log (((2 * n : ℕ) : ℝ)) := by
      simpa [Nat.cast_mul] using hpsi
    exact le_trans hpsi' (htheta_even n hn)
  · intro n hn
    have hpsi := psi_two_mul_add_one_sub_psi_le_theta_increment_add_error n
    have hpsi' :
        Chebyshev.psi (2 * n + 1) - Chebyshev.psi n ≤
          (Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
            2 * Real.sqrt (((2 * n + 1 : ℕ) : ℝ)) *
              Real.log (((2 * n + 1 : ℕ) : ℝ)) := by
      simpa [Nat.cast_mul, Nat.cast_add] using hpsi
    exact le_trans hpsi' (htheta_odd n hn)

theorem psi_two_mul_sub_psi_eq_theta_increment_add_tail_increment
    (n : ℕ) :
    Chebyshev.psi ((2 * n : ℕ) : ℝ) - Chebyshev.psi (n : ℝ) =
      (Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
        ((Chebyshev.psi ((2 * n : ℕ) : ℝ) -
            Chebyshev.theta ((2 * n : ℕ) : ℝ)) -
          (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ))) := by
  ring

theorem psi_two_mul_add_one_sub_psi_eq_theta_increment_add_tail_increment
    (n : ℕ) :
    Chebyshev.psi ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.psi (n : ℝ) =
      (Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
        ((Chebyshev.psi ((2 * n + 1 : ℕ) : ℝ) -
            Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ)) -
          (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ))) := by
  ring

noncomputable def nonPrimeVonMangoldtSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 n with ¬ k.Prime, ArithmeticFunction.vonMangoldt k

theorem psi_sub_theta_eq_nonPrimeVonMangoldtSum (n : ℕ) :
    Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) =
      nonPrimeVonMangoldtSum n := by
  simpa [nonPrimeVonMangoldtSum] using
    Chebyshev.psi_sub_theta_eq_sum_not_prime (n : ℝ)

theorem psi_two_mul_sub_psi_eq_theta_increment_add_nonPrime_tail
    (n : ℕ) :
    Chebyshev.psi ((2 * n : ℕ) : ℝ) - Chebyshev.psi (n : ℝ) =
      (Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
        (nonPrimeVonMangoldtSum (2 * n) - nonPrimeVonMangoldtSum n) := by
  rw [psi_two_mul_sub_psi_eq_theta_increment_add_tail_increment]
  rw [psi_sub_theta_eq_nonPrimeVonMangoldtSum (2 * n)]
  rw [psi_sub_theta_eq_nonPrimeVonMangoldtSum n]

theorem psi_two_mul_add_one_sub_psi_eq_theta_increment_add_nonPrime_tail
    (n : ℕ) :
    Chebyshev.psi ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.psi (n : ℝ) =
      (Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
        (nonPrimeVonMangoldtSum (2 * n + 1) - nonPrimeVonMangoldtSum n) := by
  rw [psi_two_mul_add_one_sub_psi_eq_theta_increment_add_tail_increment]
  rw [psi_sub_theta_eq_nonPrimeVonMangoldtSum (2 * n + 1)]
  rw [psi_sub_theta_eq_nonPrimeVonMangoldtSum n]

noncomputable def primeIntervalLogSum (a b : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p

theorem theta_sub_theta_eq_primeIntervalLogSum
    {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) =
      primeIntervalLogSum a b := by
  have hsubset : Nat.primesLE a ⊆ Nat.primesLE b :=
    Nat.primesLE_mono hab
  have hsum :
      (∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p) +
        (∑ p ∈ Nat.primesLE a, Real.log p) =
          ∑ p ∈ Nat.primesLE b, Real.log p := by
    simpa [add_comm] using
      (Finset.sum_sdiff
        (s₁ := Nat.primesLE a) (s₂ := Nat.primesLE b)
        (f := fun p => Real.log p) hsubset)
  rw [Chebyshev.theta_eq_sum_primesLE_log b,
    Chebyshev.theta_eq_sum_primesLE_log a, primeIntervalLogSum]
  linarith

theorem theta_two_mul_sub_theta_eq_primeIntervalLogSum
    (n : ℕ) :
    Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ) =
      primeIntervalLogSum n (2 * n) := by
  exact theta_sub_theta_eq_primeIntervalLogSum (by omega : n ≤ 2 * n)

theorem theta_two_mul_add_one_sub_theta_eq_primeIntervalLogSum
    (n : ℕ) :
    Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.theta (n : ℝ) =
      primeIntervalLogSum n (2 * n + 1) := by
  exact theta_sub_theta_eq_primeIntervalLogSum (by omega : n ≤ 2 * n + 1)

theorem psi_two_mul_sub_psi_eq_primeInterval_add_nonPrime_tail
    (n : ℕ) :
    Chebyshev.psi ((2 * n : ℕ) : ℝ) - Chebyshev.psi (n : ℝ) =
      primeIntervalLogSum n (2 * n) +
        (nonPrimeVonMangoldtSum (2 * n) - nonPrimeVonMangoldtSum n) := by
  rw [psi_two_mul_sub_psi_eq_theta_increment_add_nonPrime_tail]
  rw [theta_two_mul_sub_theta_eq_primeIntervalLogSum]

theorem psi_two_mul_add_one_sub_psi_eq_primeInterval_add_nonPrime_tail
    (n : ℕ) :
    Chebyshev.psi ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.psi (n : ℝ) =
      primeIntervalLogSum n (2 * n + 1) +
        (nonPrimeVonMangoldtSum (2 * n + 1) - nonPrimeVonMangoldtSum n) := by
  rw [psi_two_mul_add_one_sub_psi_eq_theta_increment_add_nonPrime_tail]
  rw [theta_two_mul_add_one_sub_theta_eq_primeIntervalLogSum]

theorem lcmUpto_le_three_pow_nat_of_theta_tail_increment_bounds_ge_101
    (htail_even :
      ∀ n : ℕ, 101 ≤ n →
        (Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
          ((Chebyshev.psi ((2 * n : ℕ) : ℝ) -
              Chebyshev.theta ((2 * n : ℕ) : ℝ)) -
            (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ))) ≤
          Real.log 3 * (n : ℝ))
    (htail_odd :
      ∀ n : ℕ, 101 ≤ n →
        (Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
          ((Chebyshev.psi ((2 * n + 1 : ℕ) : ℝ) -
              Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ)) -
            (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ))) ≤
          Real.log 3 * ((n + 1 : ℕ) : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_psi_increment_bounds_ge_101 ?_ ?_
  · intro n hn
    have hid := psi_two_mul_sub_psi_eq_theta_increment_add_tail_increment n
    have hid' :
        Chebyshev.psi (2 * n) - Chebyshev.psi n =
          (Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
            ((Chebyshev.psi ((2 * n : ℕ) : ℝ) -
                Chebyshev.theta ((2 * n : ℕ) : ℝ)) -
              (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ))) := by
      simpa [Nat.cast_mul] using hid
    rw [hid']
    exact htail_even n hn
  · intro n hn
    have hid := psi_two_mul_add_one_sub_psi_eq_theta_increment_add_tail_increment n
    have hid' :
        Chebyshev.psi (2 * n + 1) - Chebyshev.psi n =
          (Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
            ((Chebyshev.psi ((2 * n + 1 : ℕ) : ℝ) -
                Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ)) -
              (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ))) := by
      simpa [Nat.cast_mul, Nat.cast_add] using hid
    rw [hid']
    exact htail_odd n hn

theorem lcmUpto_le_three_pow_nat_of_theta_nonPrime_tail_bounds_ge_101
    (htail_even :
      ∀ n : ℕ, 101 ≤ n →
        (Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
          (nonPrimeVonMangoldtSum (2 * n) - nonPrimeVonMangoldtSum n) ≤
          Real.log 3 * (n : ℝ))
    (htail_odd :
      ∀ n : ℕ, 101 ≤ n →
        (Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
          (nonPrimeVonMangoldtSum (2 * n + 1) - nonPrimeVonMangoldtSum n) ≤
          Real.log 3 * ((n + 1 : ℕ) : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_psi_increment_bounds_ge_101 ?_ ?_
  · intro n hn
    have hid := psi_two_mul_sub_psi_eq_theta_increment_add_nonPrime_tail n
    have hid' :
        Chebyshev.psi (2 * n) - Chebyshev.psi n =
          (Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
            (nonPrimeVonMangoldtSum (2 * n) - nonPrimeVonMangoldtSum n) := by
      simpa [Nat.cast_mul] using hid
    rw [hid']
    exact htail_even n hn
  · intro n hn
    have hid := psi_two_mul_add_one_sub_psi_eq_theta_increment_add_nonPrime_tail n
    have hid' :
        Chebyshev.psi (2 * n + 1) - Chebyshev.psi n =
          (Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
            (nonPrimeVonMangoldtSum (2 * n + 1) - nonPrimeVonMangoldtSum n) := by
      simpa [Nat.cast_mul, Nat.cast_add] using hid
    rw [hid']
    exact htail_odd n hn

theorem lcmUpto_le_three_pow_nat_of_primeInterval_nonPrime_tail_bounds_ge_101
    (hfinite_even :
      ∀ n : ℕ, 101 ≤ n →
        primeIntervalLogSum n (2 * n) +
          (nonPrimeVonMangoldtSum (2 * n) - nonPrimeVonMangoldtSum n) ≤
          Real.log 3 * (n : ℝ))
    (hfinite_odd :
      ∀ n : ℕ, 101 ≤ n →
        primeIntervalLogSum n (2 * n + 1) +
          (nonPrimeVonMangoldtSum (2 * n + 1) - nonPrimeVonMangoldtSum n) ≤
          Real.log 3 * ((n + 1 : ℕ) : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_psi_increment_bounds_ge_101 ?_ ?_
  · intro n hn
    have hid := psi_two_mul_sub_psi_eq_primeInterval_add_nonPrime_tail n
    have hid' :
        Chebyshev.psi (2 * n) - Chebyshev.psi n =
          primeIntervalLogSum n (2 * n) +
            (nonPrimeVonMangoldtSum (2 * n) - nonPrimeVonMangoldtSum n) := by
      simpa [Nat.cast_mul] using hid
    rw [hid']
    exact hfinite_even n hn
  · intro n hn
    have hid := psi_two_mul_add_one_sub_psi_eq_primeInterval_add_nonPrime_tail n
    have hid' :
        Chebyshev.psi (2 * n + 1) - Chebyshev.psi n =
          primeIntervalLogSum n (2 * n + 1) +
            (nonPrimeVonMangoldtSum (2 * n + 1) - nonPrimeVonMangoldtSum n) := by
      simpa [Nat.cast_mul, Nat.cast_add] using hid
    rw [hid']
    exact hfinite_odd n hn

theorem lcmUpto_le_three_pow_nat_of_even_odd_increment_bounds_ge_101
    (hstep_even :
      ∀ n : ℕ, 101 ≤ n → Nat.lcmUpto (2 * n) ≤ 3 ^ n * Nat.lcmUpto n)
    (hstep_odd :
      ∀ n : ℕ, 101 ≤ n → Nat.lcmUpto (2 * n + 1) ≤
        3 ^ (n + 1) * Nat.lcmUpto n) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_eventual_even_odd_increment_bounds
    101 ?_ hstep_even hstep_odd
  intro n hn
  exact lcmUpto_le_three_pow_nat_of_le_256 (by omega)

theorem lcmUpto_le_three_pow_nat_of_psi_le_log_three
    (hpsi : ∀ n : ℕ, Chebyshev.psi n ≤ Real.log 3 * (n : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_log_lcmUpto_le ?_
  intro n
  calc
    Real.log (Nat.lcmUpto n : ℝ) = Chebyshev.psi n := by
      rw [Chebyshev.psi_eq_log_lcmUpto]
    _ ≤ Real.log 3 * (n : ℝ) := hpsi n

theorem lcmUpto_le_three_pow_nat_of_psi_le_const
    {c : ℝ}
    (hpsi : ∀ n : ℕ, Chebyshev.psi n ≤ c * (n : ℝ))
    (hc : c ≤ Real.log 3) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_psi_le_log_three ?_
  intro n
  exact (hpsi n).trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg n))

theorem lcmUpto_le_three_pow_nat_of_real_psi_le_const
    {c : ℝ}
    (hpsi : ∀ x : ℝ, 0 < x → Chebyshev.psi x ≤ c * x)
    (hc : c ≤ Real.log 3) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_psi_le_const ?_ hc
  intro n
  by_cases hn : n = 0
  · subst hn
    simp
  · exact hpsi n (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))

theorem lcmUpto_le_three_pow_nat_of_real_psi_le_const_ge_257
    {c : ℝ}
    (hpsi : ∀ x : ℝ, 257 ≤ x → Chebyshev.psi x ≤ c * x)
    (hc : c ≤ Real.log 3) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_psi_le_log_three_ge_257 ?_
  intro n hn
  exact (hpsi n (by exact_mod_cast hn)).trans
    (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg n))

theorem lcmUpto_le_three_pow_nat_of_theta_and_error_ge_257
    {a b : ℝ}
    (htheta : ∀ x : ℝ, 257 ≤ x → Chebyshev.theta x ≤ a * x)
    (herror : ∀ x : ℝ, 257 ≤ x → 2 * Real.sqrt x * Real.log x ≤ b * x)
    (hab : a + b ≤ Real.log 3) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_psi_le_log_three_ge_257 ?_
  intro n hn
  have hn_real : (257 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_one_nat : 1 ≤ n := by omega
  have hn_one_real : (1 : ℝ) ≤ n := by exact_mod_cast hn_one_nat
  have hsub := Chebyshev.psi_sub_theta_le (x := (n : ℝ)) hn_one_real
  have htheta_n := htheta n hn_real
  have herror_n := herror n hn_real
  calc
    Chebyshev.psi n
        ≤ Chebyshev.theta n + 2 * Real.sqrt (n : ℝ) * Real.log n := by linarith
    _ ≤ a * (n : ℝ) + b * (n : ℝ) := by gcongr
    _ = (a + b) * (n : ℝ) := by ring
    _ ≤ Real.log 3 * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n)

theorem lcmUpto_le_three_pow_nat_of_theta_and_log_sqrt_ge_257
    {a b : ℝ}
    (htheta : ∀ x : ℝ, 257 ≤ x → Chebyshev.theta x ≤ a * x)
    (hlog_sqrt : ∀ x : ℝ, 257 ≤ x → Real.log x ≤ (b / 2) * Real.sqrt x)
    (hab : a + b ≤ Real.log 3) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_theta_and_error_ge_257 htheta ?_ hab
  intro x hx
  have hx_nonneg : 0 ≤ x := by linarith
  calc
    2 * Real.sqrt x * Real.log x
        ≤ 2 * Real.sqrt x * ((b / 2) * Real.sqrt x) := by
          gcongr
          exact hlog_sqrt x hx
    _ = b * (Real.sqrt x) ^ 2 := by ring
    _ = b * x := by rw [Real.sq_sqrt hx_nonneg]

theorem log_257_le_28_div_5 :
    Real.log (257 : ℝ) ≤ 28 / 5 := by
  have hlog_tail :
      Real.log ((257 : ℝ) / 256) ≤ 1 / 256 := by
    have hpos : 0 < (257 : ℝ) / 256 := by norm_num
    have h := Real.log_le_sub_one_of_pos hpos
    norm_num at h ⊢
    exact h
  calc
    Real.log (257 : ℝ)
        = Real.log ((2 : ℝ) ^ 8 * ((257 : ℝ) / 256)) := by norm_num
    _ = Real.log ((2 : ℝ) ^ 8) + Real.log ((257 : ℝ) / 256) := by
      rw [Real.log_mul] <;> positivity
    _ = 8 * Real.log 2 + Real.log ((257 : ℝ) / 256) := by
      rw [Real.log_pow]
      ring
    _ ≤ 8 * 0.6931471808 + 1 / 256 := by
      gcongr
      exact Real.log_two_lt_d9.le
    _ ≤ 28 / 5 := by norm_num

theorem log_257_le_seven_twentieths_mul_sqrt_257 :
    Real.log (257 : ℝ) ≤ (7 / 20 : ℝ) * Real.sqrt 257 := by
  have hsqrt : (16 : ℝ) ≤ Real.sqrt 257 := by
    exact Real.le_sqrt_of_sq_le (by norm_num)
  nlinarith [log_257_le_28_div_5]

theorem log_le_seven_twentieths_mul_sqrt_of_antitone_log_div_sqrt
    (hanti : AntitoneOn (fun x : ℝ => Real.log x / Real.sqrt x) (Set.Ici 257))
    {x : ℝ} (hx : 257 ≤ x) :
    Real.log x ≤ (7 / 20 : ℝ) * Real.sqrt x := by
  have hx_mem : x ∈ Set.Ici (257 : ℝ) := hx
  have h257_mem : (257 : ℝ) ∈ Set.Ici (257 : ℝ) := by simp
  have hx_pos : 0 < x := by linarith
  have hsx_pos : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx_pos
  have hs257_pos : 0 < Real.sqrt (257 : ℝ) := by positivity
  have hratio :
      Real.log x / Real.sqrt x ≤ Real.log (257 : ℝ) / Real.sqrt (257 : ℝ) :=
    hanti h257_mem hx_mem hx
  have hend :
      Real.log (257 : ℝ) / Real.sqrt (257 : ℝ) ≤ (7 / 20 : ℝ) := by
    rw [div_le_iff₀ hs257_pos]
    simpa [mul_comm] using log_257_le_seven_twentieths_mul_sqrt_257
  have hle : Real.log x / Real.sqrt x ≤ (7 / 20 : ℝ) := hratio.trans hend
  rw [div_le_iff₀ hsx_pos] at hle
  simpa [mul_comm] using hle

theorem antitoneOn_log_div_sqrt_Ici_257 :
    AntitoneOn (fun x : ℝ => Real.log x / Real.sqrt x) (Set.Ici 257) := by
  change AntitoneOn (Real.log / Real.sqrt) (Set.Ici (257 : ℝ))
  refine (strictAntiOn_of_deriv_neg (convex_Ici (257 : ℝ)) ?_ ?_).antitoneOn
  · change ContinuousOn (fun x : ℝ => Real.log x / Real.sqrt x) (Set.Ici (257 : ℝ))
    refine (continuousOn_id.log ?_).div (Real.continuous_sqrt.continuousOn) ?_
    · intro x hx
      exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 257) hx)
    · intro x hx
      exact ne_of_gt (Real.sqrt_pos_of_pos
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 257) hx))
  · intro x hxmem
    rw [interior_Ici] at hxmem
    have hx257 : (257 : ℝ) < x := hxmem
    have hx : 0 < x := by linarith
    have hsx : Real.sqrt x ≠ 0 := by positivity
    have hderiv := ((Real.hasDerivAt_log hx.ne').div (Real.hasDerivAt_sqrt hx.ne') hsx).deriv
    rw [hderiv, Real.sq_sqrt hx.le]
    have hlog2 : 2 < Real.log x := by
      have hexp2 : Real.exp 2 < x := by
        have h : Real.exp 2 < (257 : ℝ) := by
          calc
            Real.exp 2 = Real.exp 1 ^ 2 := by
              rw [← Real.exp_nat_mul]
              norm_num
            _ < (3 : ℝ) ^ 2 := by
              gcongr
              exact Real.exp_one_lt_three
            _ < 257 := by norm_num
        exact h.trans hx257
      exact (Real.lt_log_iff_exp_lt hx).mpr hexp2
    refine div_neg_of_neg_of_pos ?_ hx
    field_simp [hsx, hx.ne']
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_pos_of_pos hx]

theorem log_le_seven_twentieths_mul_sqrt_ge_257
    {x : ℝ} (hx : 257 ≤ x) :
    Real.log x ≤ (7 / 20 : ℝ) * Real.sqrt x :=
  log_le_seven_twentieths_mul_sqrt_of_antitone_log_div_sqrt
    antitoneOn_log_div_sqrt_Ici_257 hx

-- This is a strong sufficient condition: the `0.7*x` error leaves only
-- `log 3 - 0.7` for the theta main term, so it is not the expected
-- asymptotic route.  It is kept as a verified decomposition checkpoint.
theorem lcmUpto_le_three_pow_nat_of_strong_theta_and_log_div_sqrt_antitone_ge_257
    {a : ℝ}
    (htheta : ∀ x : ℝ, 257 ≤ x → Chebyshev.theta x ≤ a * x)
    (hanti : AntitoneOn (fun x : ℝ => Real.log x / Real.sqrt x) (Set.Ici 257))
    (ha : a + (7 / 10 : ℝ) ≤ Real.log 3) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_theta_and_log_sqrt_ge_257 htheta ?_ ha
  intro x hx
  have hlog :=
    log_le_seven_twentieths_mul_sqrt_of_antitone_log_div_sqrt hanti hx
  simpa [show ((7 / 10 : ℝ) / 2) = (7 / 20 : ℝ) by norm_num] using hlog

theorem lcmUpto_le_three_pow_nat_of_strong_theta_ge_257
    {a : ℝ}
    (htheta : ∀ x : ℝ, 257 ≤ x → Chebyshev.theta x ≤ a * x)
    (ha : a + (7 / 10 : ℝ) ≤ Real.log 3) :
    lcmUpto_le_three_pow_nat_statement :=
  lcmUpto_le_three_pow_nat_of_strong_theta_and_log_div_sqrt_antitone_ge_257
    htheta antitoneOn_log_div_sqrt_Ici_257 ha

theorem lcmUpto_le_three_pow_nat_of_strong_theta_0_398_ge_257
    (htheta : ∀ x : ℝ, 257 ≤ x → Chebyshev.theta x ≤ (0.398 : ℝ) * x) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_strong_theta_ge_257 htheta ?_
  exact (by norm_num : (0.398 : ℝ) + (7 / 10 : ℝ) ≤ 1.0986122885).trans
    Real.log_three_gt_d9.le

theorem log_three_gt_one :
    (1 : ℝ) < Real.log 3 :=
  (by norm_num : (1 : ℝ) < 1.0986122885).trans
    Real.log_three_gt_d9

theorem log_three_gt_1_03883 :
    (1.03883 : ℝ) < Real.log 3 :=
  (by norm_num : (1.03883 : ℝ) < 1.0986122885).trans
    Real.log_three_gt_d9

theorem lcmUpto_le_three_pow_nat_of_psi_le_one
    (hpsi : ∀ n : ℕ, Chebyshev.psi n ≤ (n : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  exact lcmUpto_le_three_pow_nat_of_psi_le_const
    (c := 1) (by simpa using hpsi) log_three_gt_one.le

theorem lcmUpto_le_three_pow_nat_of_psi_le_1_03883
    (hpsi : ∀ n : ℕ, Chebyshev.psi n ≤ (1.03883 : ℝ) * (n : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  exact lcmUpto_le_three_pow_nat_of_psi_le_const
    (c := 1.03883) hpsi log_three_gt_1_03883.le

theorem lcmUpto_le_three_pow_nat_of_psi_le_1_03883_ge_257
    (hlarge : ∀ n : ℕ, 257 ≤ n →
      Chebyshev.psi n ≤ (1.03883 : ℝ) * (n : ℝ)) :
    lcmUpto_le_three_pow_nat_statement := by
  refine lcmUpto_le_three_pow_nat_of_psi_le_log_three_ge_257 ?_
  intro n hn
  exact (hlarge n hn).trans
    (mul_le_mul_of_nonneg_right log_three_gt_1_03883.le (Nat.cast_nonneg n))

def SondowForwardInputs.of_psi_le_log_three
    (hpsi : ∀ n : ℕ, Chebyshev.psi n ≤ Real.log 3 * (n : ℝ))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_psi_le_log_three hpsi
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_psi_le_log_three_ge_257
    (hlarge : ∀ n : ℕ, 257 ≤ n →
      Chebyshev.psi n ≤ Real.log 3 * (n : ℝ))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_psi_le_log_three_ge_257 hlarge
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_mid_257_512_and_ge_513
    (hmid : ∀ n : ℕ, 257 ≤ n → n ≤ 512 → Nat.lcmUpto n ≤ 3 ^ n)
    (hlarge : ∀ n : ℕ, 513 ≤ n → Nat.lcmUpto n ≤ 3 ^ n)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_mid_257_512_and_ge_513 hmid hlarge
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_psi_le_1_03883
    (hpsi : ∀ n : ℕ, Chebyshev.psi n ≤ (1.03883 : ℝ) * (n : ℝ))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_psi_le_1_03883 hpsi
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_psi_le_1_03883_ge_257
    (hlarge : ∀ n : ℕ, 257 ≤ n →
      Chebyshev.psi n ≤ (1.03883 : ℝ) * (n : ℝ))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_psi_le_1_03883_ge_257 hlarge
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_log_lcmUpto_le
    (hlog : ∀ n : ℕ,
      Real.log (Nat.lcmUpto n : ℝ) ≤ Real.log 3 * (n : ℝ))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_log_lcmUpto_le hlog
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_strong_even_odd_increment_bounds
    (hstep_even : ∀ n : ℕ, Nat.lcmUpto (2 * n) ≤ 3 ^ n * Nat.lcmUpto n)
    (hstep_odd : ∀ n : ℕ, Nat.lcmUpto (2 * n + 1) ≤ 3 ^ (n + 1) * Nat.lcmUpto n)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_strong_even_odd_increment_bounds hstep_even hstep_odd
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_eventual_even_odd_increment_bounds
    (N : ℕ)
    (hfinite : ∀ n : ℕ, n ≤ 2 * N + 1 → Nat.lcmUpto n ≤ 3 ^ n)
    (hstep_even :
      ∀ n : ℕ, N ≤ n → Nat.lcmUpto (2 * n) ≤ 3 ^ n * Nat.lcmUpto n)
    (hstep_odd :
      ∀ n : ℕ, N ≤ n → Nat.lcmUpto (2 * n + 1) ≤
        3 ^ (n + 1) * Nat.lcmUpto n)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_eventual_even_odd_increment_bounds
      N hfinite hstep_even hstep_odd
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_even_odd_increment_bounds_ge_101
    (hstep_even :
      ∀ n : ℕ, 101 ≤ n → Nat.lcmUpto (2 * n) ≤ 3 ^ n * Nat.lcmUpto n)
    (hstep_odd :
      ∀ n : ℕ, 101 ≤ n → Nat.lcmUpto (2 * n + 1) ≤
        3 ^ (n + 1) * Nat.lcmUpto n)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_even_odd_increment_bounds_ge_101
      hstep_even hstep_odd
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_psi_increment_bounds_ge_101
    (hpsi_even :
      ∀ n : ℕ, 101 ≤ n →
        Chebyshev.psi (2 * n) - Chebyshev.psi n ≤ Real.log 3 * (n : ℝ))
    (hpsi_odd :
      ∀ n : ℕ, 101 ≤ n →
        Chebyshev.psi (2 * n + 1) - Chebyshev.psi n ≤
          Real.log 3 * ((n + 1 : ℕ) : ℝ))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_psi_increment_bounds_ge_101
    hpsi_even hpsi_odd
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_psi_increment_bounds_eventual
    (N : ℕ)
    (hfinite : ∀ n : ℕ, n ≤ 2 * N + 1 → Nat.lcmUpto n ≤ 3 ^ n)
    (hpsi_even :
      ∀ n : ℕ, N ≤ n →
        Chebyshev.psi (2 * n) - Chebyshev.psi n ≤ Real.log 3 * (n : ℝ))
    (hpsi_odd :
      ∀ n : ℕ, N ≤ n →
        Chebyshev.psi (2 * n + 1) - Chebyshev.psi n ≤
          Real.log 3 * ((n + 1 : ℕ) : ℝ))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_psi_increment_bounds_eventual
      N hfinite hpsi_even hpsi_odd
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_theta_increment_error_bounds_ge_101
    (htheta_even :
      ∀ n : ℕ, 101 ≤ n →
        (Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
          2 * Real.sqrt (((2 * n : ℕ) : ℝ)) *
            Real.log (((2 * n : ℕ) : ℝ)) ≤
          Real.log 3 * (n : ℝ))
    (htheta_odd :
      ∀ n : ℕ, 101 ≤ n →
        (Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
          2 * Real.sqrt (((2 * n + 1 : ℕ) : ℝ)) *
            Real.log (((2 * n + 1 : ℕ) : ℝ)) ≤
          Real.log 3 * ((n + 1 : ℕ) : ℝ))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_theta_increment_error_bounds_ge_101
      htheta_even htheta_odd
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_theta_tail_increment_bounds_ge_101
    (htail_even :
      ∀ n : ℕ, 101 ≤ n →
        (Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
          ((Chebyshev.psi ((2 * n : ℕ) : ℝ) -
              Chebyshev.theta ((2 * n : ℕ) : ℝ)) -
            (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ))) ≤
          Real.log 3 * (n : ℝ))
    (htail_odd :
      ∀ n : ℕ, 101 ≤ n →
        (Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
          ((Chebyshev.psi ((2 * n + 1 : ℕ) : ℝ) -
              Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ)) -
            (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ))) ≤
          Real.log 3 * ((n + 1 : ℕ) : ℝ))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_theta_tail_increment_bounds_ge_101
      htail_even htail_odd
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_theta_nonPrime_tail_bounds_ge_101
    (htail_even :
      ∀ n : ℕ, 101 ≤ n →
        (Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
          (nonPrimeVonMangoldtSum (2 * n) - nonPrimeVonMangoldtSum n) ≤
          Real.log 3 * (n : ℝ))
    (htail_odd :
      ∀ n : ℕ, 101 ≤ n →
        (Chebyshev.theta ((2 * n + 1 : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)) +
          (nonPrimeVonMangoldtSum (2 * n + 1) - nonPrimeVonMangoldtSum n) ≤
          Real.log 3 * ((n + 1 : ℕ) : ℝ))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_theta_nonPrime_tail_bounds_ge_101
      htail_even htail_odd
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_primeInterval_nonPrime_tail_bounds_ge_101
    (hfinite_even :
      ∀ n : ℕ, 101 ≤ n →
        primeIntervalLogSum n (2 * n) +
          (nonPrimeVonMangoldtSum (2 * n) - nonPrimeVonMangoldtSum n) ≤
          Real.log 3 * (n : ℝ))
    (hfinite_odd :
      ∀ n : ℕ, 101 ≤ n →
        primeIntervalLogSum n (2 * n + 1) +
          (nonPrimeVonMangoldtSum (2 * n + 1) - nonPrimeVonMangoldtSum n) ≤
          Real.log 3 * ((n + 1 : ℕ) : ℝ))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_primeInterval_nonPrime_tail_bounds_ge_101
      hfinite_even hfinite_odd
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_lcm_dvd_certificates
    (hcert : ∀ n : ℕ, ∃ m : ℕ, Nat.lcmUpto n ∣ m ∧ 0 < m ∧ m ≤ 3 ^ n)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_dvd_certificates hcert
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_lcm_certificate_family
    (cert : ∀ n : ℕ, LcmDvdCertificate n)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_certificate_family cert
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_lcm_certificate_family_ge
    (N : ℕ)
    (hfinite : ∀ n : ℕ, n < N → Nat.lcmUpto n ≤ 3 ^ n)
    (cert : ∀ n : ℕ, N ≤ n → LcmDvdCertificate n)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_certificate_family_ge N hfinite cert
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_hansonC_upper_bound_family
    (k : ℕ → ℕ)
    (hsmall : ∀ n : ℕ, hansonC n (k n) ≤ 3 ^ n)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family k hsmall
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_hansonC_upper_bound_family_ge
    (N : ℕ)
    (hfinite : ∀ n : ℕ, n < N → Nat.lcmUpto n ≤ 3 ^ n)
    (k : ℕ → ℕ)
    (hsmall : ∀ n : ℕ, N ≤ n → hansonC n (k n) ≤ 3 ^ n)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_hansonC_upper_bound_family_ge
      N hfinite k hsmall
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_hansonC_floor_pow_prod_prefix_lower_ge_2048
    (k : ℕ → ℕ)
    (hk : ∀ n : ℕ, 2048 ≤ n → k n ≤ n + 1)
    (hprod : ∀ n : ℕ, 2048 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (k n),
            (n / hansonA j) ^ (n / hansonA j))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_hansonC_floor_pow_prod_prefix_lower_ge_2048
      k hk hprod
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_hansonC_succ_index_floor_pow_prod_lower_ge_2048
    (hprod : ∀ n : ℕ, 2048 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (n + 1),
            (n / hansonA j) ^ (n / hansonA j))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_hansonC_succ_index_floor_pow_prod_lower_ge_2048
      hprod
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_hansonC_four_prod_lower_ge_2048_lt_hansonA_five
    (hprod4 : ∀ n : ℕ, 2048 ≤ n → n < hansonA 5 →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range 4, (n / hansonA j) ^ (n / hansonA j))
    (htail : ∀ n : ℕ, hansonA 5 ≤ n →
      n ^ n ≤
        3 ^ n *
          ∏ j ∈ Finset.range (n + 1),
            (n / hansonA j) ^ (n / hansonA j))
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_hansonC_four_prod_lower_ge_2048_lt_hansonA_five
      hprod4 htail
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_prime_exponent_certificate_family
    (beta : ℕ → ℕ → ℕ)
    (hbeta : ∀ n p : ℕ, p ∈ Nat.primesLE n → p.log n ≤ beta n p)
    (hsmall : ∀ n : ℕ, primePowProductLE n (beta n) ≤ 3 ^ n)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_certificate_family fun n =>
      LcmDvdCertificate.ofPrimeExponentBounds
        n (beta n) (hbeta n) (primePowProductLE_pos n (beta n)) (hsmall n)
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_prime_exponent_certificate_family_ge
    (N : ℕ)
    (hfinite : ∀ n : ℕ, n < N → Nat.lcmUpto n ≤ 3 ^ n)
    (beta : ℕ → ℕ → ℕ)
    (hbeta : ∀ n p : ℕ, N ≤ n → p ∈ Nat.primesLE n → p.log n ≤ beta n p)
    (hsmall : ∀ n : ℕ, N ≤ n → primePowProductLE n (beta n) ≤ 3 ^ n)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_certificate_family_ge N hfinite fun n hn =>
      LcmDvdCertificate.ofPrimeExponentBounds
        n (beta n) (fun p hp => hbeta n p hn hp)
        (primePowProductLE_pos n (beta n)) (hsmall n hn)
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_psi_le_const
    {c : ℝ}
    (hpsi : ∀ n : ℕ, Chebyshev.psi n ≤ c * (n : ℝ))
    (hc : c ≤ Real.log 3)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_psi_le_const hpsi hc
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_real_psi_le_const
    {c : ℝ}
    (hpsi : ∀ x : ℝ, 0 < x → Chebyshev.psi x ≤ c * x)
    (hc : c ≤ Real.log 3)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_real_psi_le_const hpsi hc
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_real_psi_le_const_ge_257
    {c : ℝ}
    (hpsi : ∀ x : ℝ, 257 ≤ x → Chebyshev.psi x ≤ c * x)
    (hc : c ≤ Real.log 3)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_real_psi_le_const_ge_257 hpsi hc
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_theta_and_error_ge_257
    {a b : ℝ}
    (htheta : ∀ x : ℝ, 257 ≤ x → Chebyshev.theta x ≤ a * x)
    (herror : ∀ x : ℝ, 257 ≤ x → 2 * Real.sqrt x * Real.log x ≤ b * x)
    (hab : a + b ≤ Real.log 3)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound := lcmUpto_le_three_pow_nat_of_theta_and_error_ge_257 htheta herror hab
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_theta_and_log_sqrt_ge_257
    {a b : ℝ}
    (htheta : ∀ x : ℝ, 257 ≤ x → Chebyshev.theta x ≤ a * x)
    (hlog_sqrt : ∀ x : ℝ, 257 ≤ x → Real.log x ≤ (b / 2) * Real.sqrt x)
    (hab : a + b ≤ Real.log 3)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_theta_and_log_sqrt_ge_257 htheta hlog_sqrt hab
  product_log := hproduct_log
  decomposition := hdecomposition

def SondowForwardInputs.of_theta_and_log_div_sqrt_antitone_ge_257
    {a : ℝ}
    (htheta : ∀ x : ℝ, 257 ≤ x → Chebyshev.theta x ≤ a * x)
    (hanti : AntitoneOn (fun x : ℝ => Real.log x / Real.sqrt x) (Set.Ici 257))
    (ha : a + (7 / 10 : ℝ) ≤ Real.log 3)
    (hproduct_log :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_product_log_relation_prop n)
    (hdecomposition :
      ∀ n : ℕ, 1 ≤ n → sondow_explicit_decomposition_prop n) :
    SondowForwardInputs where
  lcm_bound :=
    lcmUpto_le_three_pow_nat_of_strong_theta_and_log_div_sqrt_antitone_ge_257 htheta hanti ha
  product_log := hproduct_log
  decomposition := hdecomposition
