import Foundation.FirstOrder.Incompleteness.RestrictedProvability
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Exponential bit-length lower bound for restricted Goedel sentences

This file records a fully checked lower-bound route already available in
FormalizedFormalLogic/Foundation.  It deliberately does not identify this
self-referential formula family with the project's finite-consistency family.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic
open Filter Asymptotics

noncomputable section

namespace FoundationRestrictedGodelPowerLowerBound

abbrev PA : LO.FirstOrder.ArithmeticTheory :=
  LO.FirstOrder.Arithmetic.Peano

/-- The restricted Goedel sentence whose code cutoff exponent is `2^n`. -/
noncomputable def sentence (n : Nat) :
    LO.FirstOrder.ArithmeticSentence :=
  PA.restrictedGödel (2 ^ n)

/-- Foundation's arithmetized PA proof checker for the exact sentence. -/
def Checks (d n : Nat) : Prop :=
  LO.FirstOrder.Arithmetic.Bootstrapping.Proof
    PA d (⌜sentence n⌝ : Nat)

/-- Every accepted raw proof code is at least `2^(2^n)`. -/
theorem checks_code_ge_doublePow
    {d n : Nat} (hd : Checks d n) :
    2 ^ (2 ^ n) ≤ d := by
  have htrue :
      Nat↓[ℒₒᵣ] ⊧ PA.restrictedGödel (2 ^ n) :=
    LO.FirstOrder.Arithmetic.true_restrictedGödel
      (T := PA) (e := 2 ^ n)
  have hno :=
    (LO.FirstOrder.Arithmetic.models_restrictedGödel
      (V := Nat) (T := PA) (e := 2 ^ n)).mp htrue
  apply Nat.le_of_not_gt
  intro hdlt
  exact hno d (by simpa using hdlt) hd

/-- Consequently every accepted proof code has binary length above `2^n`. -/
theorem checks_bitSize_gt_powTwo
    {d n : Nat} (hd : Checks d n) :
    2 ^ n < Nat.size d := by
  have hcode := checks_code_ge_doublePow hd
  by_contra hnot
  have hsize : Nat.size d ≤ 2 ^ n := Nat.le_of_not_gt hnot
  have hdlt : d < 2 ^ (2 ^ n) := Nat.size_le.mp hsize
  exact (not_lt_of_ge hcode) hdlt

/-- PA proves every member of this restricted-Goedel family. -/
theorem provable_sentence (n : Nat) :
    PA ⊢ sentence n :=
  LO.FirstOrder.Arithmetic.provable_restrictedGödel
    (T := PA) (e := 2 ^ n)

noncomputable def proof (n : Nat) :
    PA ⊢! sentence n :=
  Classical.choice (provable_sentence n)

/-- The checker is complete on this family. -/
theorem checks_complete (n : Nat) :
    ∃ d : Nat, Checks d n := by
  refine ⟨⌜proof n⌝, ?_⟩
  exact LO.FirstOrder.proof_of_quote_proof (proof n)

theorem acceptedBitSize_exists (n : Nat) :
    ∃ k : Nat, ∃ d : Nat,
      Checks d n ∧ Nat.size d = k := by
  rcases checks_complete n with ⟨d, hd⟩
  exact ⟨Nat.size d, d, hd, rfl⟩

/-- Minimum binary length of a checker-accepted proof code at index `n`. -/
noncomputable def minAcceptedBitSize (n : Nat) : Nat := by
  classical
  exact Nat.find (acceptedBitSize_exists n)

theorem minAcceptedBitSize_spec (n : Nat) :
    ∃ d : Nat,
      Checks d n ∧ Nat.size d = minAcceptedBitSize n := by
  classical
  exact Nat.find_spec (acceptedBitSize_exists n)

/-- The minimum accepted proof-code bit length is strictly above `2^n`. -/
theorem minAcceptedBitSize_gt_powTwo (n : Nat) :
    2 ^ n < minAcceptedBitSize n := by
  rcases minAcceptedBitSize_spec n with ⟨d, hd, hsize⟩
  simpa [hsize] using checks_bitSize_gt_powTwo hd

/-- Exact local copy of the project's polynomial-bound predicate. -/
def PolynomialBound (f : Nat → Real) : Prop :=
  ∃ (c : Real) (k : Nat),
    ∀ n : Nat, f n ≤ c * ((n : Real) + 1) ^ k

def powTwoLowerEnvelope (n : Nat) : Real :=
  (2 : Real) ^ n

/-- `2^n` eventually strictly dominates every project-shaped real polynomial
bound. -/
theorem powTwoLowerEnvelope_eventually_gt_polynomial
    (U : Nat → Real) (hU : PolynomialBound U) :
    ∀ᶠ n in atTop, U n < powTwoLowerEnvelope n := by
  rcases hU with ⟨c, k, hc⟩
  have hlittle :
      (fun n : Nat => (n : Real) ^ k) =o[atTop]
        (fun n : Nat => (2 : Real) ^ n) :=
    isLittleO_pow_const_const_pow_of_one_lt k (by norm_num)
  have hshift :
      (fun n : Nat => ((n + 1 : Nat) : Real) ^ k) =o[atTop]
        (fun n : Nat => (2 : Real) ^ (n + 1)) :=
    hlittle.comp_tendsto (tendsto_add_atTop_nat 1)
  have hscaled :
      (fun n : Nat => c * ((n + 1 : Nat) : Real) ^ k) =o[atTop]
        (fun n : Nat => (2 : Real) ^ n) := by
    have hconst :
        (fun n : Nat => c * ((n + 1 : Nat) : Real) ^ k) =o[atTop]
          (fun n : Nat => (2 : Real) ^ (n + 1)) :=
      hshift.const_mul_left c
    have hbigO :
        (fun n : Nat => (2 : Real) ^ (n + 1)) =O[atTop]
          (fun n : Nat => (2 : Real) ^ n) := by
      apply IsBigO.of_bound 2
      filter_upwards with n
      rw [pow_succ]
      simp only [Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
      rw [mul_comm (2 : Real)]
    exact hconst.trans_isBigO hbigO
  have hlt :
      ∀ᶠ n in atTop,
        c * ((n + 1 : Nat) : Real) ^ k < (2 : Real) ^ n := by
    have hnorm := hscaled.eventuallyLT_norm_of_eventually_pos
      (Filter.Eventually.of_forall fun n => by simp)
    filter_upwards [hnorm] with n hn
    have habs_lt :
        |c * ((n + 1 : Nat) : Real) ^ k| < (2 : Real) ^ n := by
      simpa [Real.norm_eq_abs, abs_pow,
        abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)] using hn
    exact (le_abs_self _).trans_lt habs_lt
  filter_upwards [hlt] with n hn
  exact (hc n).trans_lt (by
    simpa [powTwoLowerEnvelope, Nat.cast_add, Nat.cast_one] using hn)

/-- The exact minimum accepted bit length eventually exceeds every real
polynomial bound of the project's shape. -/
theorem minAcceptedBitSize_eventually_gt_polynomial
    (U : Nat → Real) (hU : PolynomialBound U) :
    ∀ᶠ n in atTop, U n < (minAcceptedBitSize n : Real) := by
  have hpoly := powTwoLowerEnvelope_eventually_gt_polynomial U hU
  filter_upwards [hpoly] with n hn
  have hmin : powTwoLowerEnvelope n < (minAcceptedBitSize n : Real) := by
    unfold powTwoLowerEnvelope
    exact_mod_cast minAcceptedBitSize_gt_powTwo n
  exact hn.trans hmin

/-- Strong-growth endpoint matching the quantifier shape used by the project. -/
theorem minAcceptedBitSize_strongLowerBound :
    ∀ U : Nat → Real, PolynomialBound U →
      ∃ᶠ n in atTop, (minAcceptedBitSize n : Real) > U n := by
  intro U hU
  have hevent := minAcceptedBitSize_eventually_gt_polynomial U hU
  rw [Filter.frequently_atTop]
  intro N
  rcases Filter.eventually_atTop.1 hevent with ⟨Nmin, hNmin⟩
  exact ⟨max N Nmin, le_max_left _ _, hNmin _ (le_max_right _ _)⟩

#check checks_code_ge_doublePow
#print axioms checks_code_ge_doublePow

#check checks_bitSize_gt_powTwo
#print axioms checks_bitSize_gt_powTwo

#check checks_complete
#print axioms checks_complete

#check minAcceptedBitSize_gt_powTwo
#print axioms minAcceptedBitSize_gt_powTwo

#check minAcceptedBitSize_eventually_gt_polynomial
#print axioms minAcceptedBitSize_eventually_gt_polynomial

#check minAcceptedBitSize_strongLowerBound
#print axioms minAcceptedBitSize_strongLowerBound

end FoundationRestrictedGodelPowerLowerBound
