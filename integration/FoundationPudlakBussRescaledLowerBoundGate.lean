import EulerLimit.StrengthenedConsistency

noncomputable section

open Filter

/--
The elementary super-polynomial carrier used to state the rescaled
Pudlak-Buss lower bound without fractional real powers.
-/
def pudlakBussGrowthCarrier (n : Nat) : Nat :=
  (n + 1) ^ n

/--
The perfect-power scale corresponding to a fixed-root lower bound.  If the
unscaled lower bound has exponent at least `1 / degree`, then its value on this
scale is at least `pudlakBussGrowthCarrier`.
-/
def pudlakBussPerfectPowerScale (degree n : Nat) : Nat :=
  (n + 1) ^ (degree * n)

/--
The carrier `n ↦ (n+1)^n` eventually strictly dominates every polynomially
bounded real-valued function.
-/
theorem eventually_lt_pudlakBussGrowthCarrier
    (U : Nat → Real) (hU : is_polynomial_bound U) :
    ∀ᶠ n in atTop, U n < (pudlakBussGrowthCarrier n : Real) := by
  let c : Real := Classical.choose hU.nonneg_coefficient
  let k : Nat :=
    Classical.choose (Classical.choose_spec hU.nonneg_coefficient)
  have hc_nonneg : 0 ≤ c :=
    (Classical.choose_spec
      (Classical.choose_spec hU.nonneg_coefficient)).1
  have hbound :
      ∀ n : Nat, U n ≤ c * ((n : Real) + 1) ^ k :=
    (Classical.choose_spec
      (Classical.choose_spec hU.nonneg_coefficient)).2
  let C : Nat := Classical.choose (exists_nat_ge c)
  have hC : c ≤ (C : Real) :=
    Classical.choose_spec (exists_nat_ge c)
  filter_upwards [eventually_ge_atTop (C + k + 1)] with n hn
  let B : Real := (n : Real) + 1
  have hU_le : U n ≤ c * B ^ k := by
    simpa [B] using hbound n
  have hB_ge_one : (1 : Real) ≤ B := by
    dsimp [B]
    nlinarith [show (0 : Real) ≤ (n : Real) by exact Nat.cast_nonneg n]
  have hpow_nonneg : 0 ≤ B ^ k := by
    positivity
  have hpow_pos : 0 < B ^ k := by
    positivity
  have hC_mul_le : c * B ^ k ≤ (C : Real) * B ^ k :=
    mul_le_mul_of_nonneg_right hC hpow_nonneg
  have hk_succ_le_n : k + 1 ≤ n := by
    omega
  have hC_lt_B : (C : Real) < B := by
    have hC_lt_n_succ : C < n + 1 := by
      omega
    have hC_lt_n_succ_real : (C : Real) < ((n + 1 : Nat) : Real) := by
      exact_mod_cast hC_lt_n_succ
    simpa [B, Nat.cast_add] using hC_lt_n_succ_real
  have hC_mul_lt : (C : Real) * B ^ k < B * B ^ k :=
    mul_lt_mul_of_pos_right hC_lt_B hpow_pos
  have hB_mul_eq : B * B ^ k = B ^ (k + 1) := by
    rw [show k + 1 = Nat.succ k by omega, pow_succ]
    ring
  have hpow_le : B ^ (k + 1) ≤ B ^ n :=
    pow_le_pow_right₀ hB_ge_one hk_succ_le_n
  calc
    U n ≤ c * B ^ k := hU_le
    _ ≤ (C : Real) * B ^ k := hC_mul_le
    _ < B * B ^ k := hC_mul_lt
    _ = B ^ (k + 1) := hB_mul_eq
    _ ≤ B ^ n := hpow_le
    _ = (pudlakBussGrowthCarrier n : Real) := by
      simp [pudlakBussGrowthCarrier, B, Nat.cast_add, Nat.cast_pow]

/--
Faithful lower-bound endpoint for the rescaled family.

This does not assert a super-polynomial lower bound for the unscaled family
`source n`.  It asserts an eventual fixed-root lower bound on the perfect-power
subfamily `source ((n+1)^(degree*n))`, exactly the form from which a
super-polynomial lower bound in the outer parameter `n` follows.
-/
structure PudlakBussPerfectPowerRescaledLowerBound
    (source : Nat → FormulaCode) where
  degree : Nat
  degree_pos : 0 < degree
  eventually_lower :
    ∀ᶠ n in atTop,
      (pudlakBussGrowthCarrier n : Real) <
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (source (pudlakBussPerfectPowerScale degree n))

/--
A faithful perfect-power lower bound yields the strong lower bound required
for collision, but only on the same rescaled formula family.
-/
theorem PudlakBussPerfectPowerRescaledLowerBound.toStrongRescaledLowerBound
    {source : Nat → FormulaCode}
    (h : PudlakBussPerfectPowerRescaledLowerBound source) :
    StrongProofLengthLowerBound
      ProofSystem.PA ProofLengthMeasure.symbolSize
      (fun n => source (pudlakBussPerfectPowerScale h.degree n)) where
  frequently_beats_every_polynomial := by
    intro U hU
    exact
      ((eventually_lt_pudlakBussGrowthCarrier U hU).and h.eventually_lower).mono
        (fun n hn =>
          lt_trans hn.1 hn.2)
        |>.frequently

/--
The perfect-power scale is itself super-polynomial as soon as the fixed root
degree is positive.  Consequently it cannot satisfy the old
`PolynomialCofinalScale` interface used to transfer a strong lower bound back
to the unscaled family.
-/
theorem not_polynomial_bound_pudlakBussPerfectPowerScale
    {degree : Nat} (hdegree : 0 < degree) :
    ¬ is_polynomial_bound
      (fun n : Nat => (pudlakBussPerfectPowerScale degree n : Real)) := by
  intro hpoly
  rcases
      (eventually_lt_pudlakBussGrowthCarrier
        (fun n : Nat => (pudlakBussPerfectPowerScale degree n : Real))
        hpoly).exists with
    ⟨n, hlt⟩
  have hexponent : n ≤ degree * n := by
    exact Nat.le_mul_of_pos_left n hdegree
  have hbase : (1 : Real) ≤ (n : Real) + 1 := by
    nlinarith [show (0 : Real) ≤ (n : Real) by exact Nat.cast_nonneg n]
  have hcarrier_le :
      (pudlakBussGrowthCarrier n : Real) ≤
        (pudlakBussPerfectPowerScale degree n : Real) := by
    simpa [pudlakBussGrowthCarrier, pudlakBussPerfectPowerScale,
      Nat.cast_add, Nat.cast_pow] using
        (pow_le_pow_right₀ hbase hexponent)
  exact (not_lt_of_ge hcarrier_le) hlt

/--
In particular, the faithful perfect-power scale cannot be packaged as a
`PolynomialCofinalScale`.  The rescaled family must remain the common object
on both sides of the final collision.
-/
theorem no_polynomialCofinalScale_pudlakBussPerfectPowerScale
    {degree : Nat} (hdegree : 0 < degree) :
    ¬ PolynomialCofinalScale (pudlakBussPerfectPowerScale degree) := by
  intro hscale
  exact
    not_polynomial_bound_pudlakBussPerfectPowerScale hdegree
      (hscale.polynomial_substitution
        (fun n : Nat => (n : Real))
        ⟨1, 1, by
          intro n
          norm_num⟩)

#print axioms eventually_lt_pudlakBussGrowthCarrier
#print axioms
  PudlakBussPerfectPowerRescaledLowerBound.toStrongRescaledLowerBound
#print axioms not_polynomial_bound_pudlakBussPerfectPowerScale
#print axioms no_polynomialCofinalScale_pudlakBussPerfectPowerScale
