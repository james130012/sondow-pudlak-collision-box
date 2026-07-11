import Foundation.FirstOrder.Incompleteness.RestrictedProvability
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Real PA finite-consistency lower-bound target

This file opens the finite-consistency endpoint over Foundation's actual PA
proof predicate and proves the raw-code asymptotic reduction.  The companion
encoding audit shows that this raw `Nat.size` coordinate already has a trivial
degree-one lower bound because the proof code contains the unary-parameter
conclusion.  Consequently the propositions below are diagnostic only; the
paper-grade theorem must use a succinct parameter formula and a calibrated
structural proof length.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic
open Filter Asymptotics

noncomputable section

namespace FoundationPAFiniteConsistencyLowerBoundTarget

abbrev PA : LO.FirstOrder.ArithmeticTheory :=
  LO.FirstOrder.Arithmetic.Peano

/-- `Con_PA(e)`: no PA proof of falsity has raw Goedel code below `2^e`. -/
noncomputable def finiteConsistencySentence (e : Nat) :
    LO.FirstOrder.ArithmeticSentence :=
  ∼(LO.FirstOrder.Theory.restrictedProvabilityPred
      (T := PA) e (⊥ : LO.FirstOrder.ArithmeticSentence))

/-- Pudlak's concrete bounded-provability relation for Foundation PA: `sigma`
has an accepted raw proof code whose binary length is at most `e`. -/
def ShortPAProof
    (e : Nat) (sigma : LO.FirstOrder.ArithmeticSentence) : Prop :=
  ∃ d : Nat,
    Nat.size d ≤ e ∧
      LO.FirstOrder.Arithmetic.Bootstrapping.Proof
        PA d (⌜sigma⌝ : Nat)

/-- Pudlak condition (0) at the external semantic level: increasing the length
cutoff preserves bounded provability. -/
theorem ShortPAProof.mono
    {e e' : Nat} {sigma : LO.FirstOrder.ArithmeticSentence}
    (hee' : e ≤ e') (h : ShortPAProof e sigma) :
    ShortPAProof e' sigma := by
  rcases h with ⟨d, hsize, hproof⟩
  exact ⟨d, hsize.trans hee', hproof⟩

/-- Foundation's restricted-provability semantics is exactly Pudlak's
bit-length-bounded proof relation, with no encoding slack. -/
theorem restrictedProvable_iff_shortPAProof
    (e : Nat) (sigma : LO.FirstOrder.ArithmeticSentence) :
    LO.FirstOrder.Theory.RestrictedProvable
        e PA (⌜sigma⌝ : Nat) ↔
      ShortPAProof e sigma := by
  simp [LO.FirstOrder.Theory.RestrictedProvable,
    ShortPAProof, Nat.size_le]

theorem no_standard_proof_falsum (d : Nat) :
    ¬ LO.FirstOrder.Arithmetic.Bootstrapping.Proof
      PA d (⌜(⊥ : LO.FirstOrder.ArithmeticSentence)⌝ : Nat) := by
  intro hd
  have hprov : PA ⊢ (⊥ : LO.FirstOrder.ArithmeticSentence) :=
    LO.FirstOrder.Arithmetic.Bootstrapping.provable_of_standard_proof
      (T := PA) (V := Nat) (n := d) (by simpa using hd)
  exact LO.Entailment.Consistent.not_bot (𝓢 := PA) inferInstance hprov

/-- Encoding audit: Foundation stores the concluding singleton sequent inside
every raw proof code.  Consequently the binary size of any accepted proof code
strictly exceeds the numeric Goedel code of its conclusion. -/
theorem conclusionCode_lt_bitSize_of_proof
    {d phi : Nat}
    (hproof :
      LO.FirstOrder.Arithmetic.Bootstrapping.Proof PA d phi) :
    phi < Nat.size d := by
  rw [Nat.lt_size]
  have hsingleton : (2 ^ phi : Nat) = ({phi} : Nat) := by
    rw [LO.FirstOrder.Arithmetic.singleton_def]
    exact (LO.FirstOrder.Arithmetic.exp_nat (n := phi)).symm
  have hfst_le : LO.FirstOrder.Arithmetic.fstIdx d ≤ d := by
    have hfoundation := LO.FirstOrder.Arithmetic.fstIdx_le_self d
    rw [LO.FirstOrder.Arithmetic.le_def] at hfoundation
    rcases hfoundation with hEq | hLt
    · exact hEq.le
    · exact Nat.le_of_lt hLt
  calc
    2 ^ phi = ({phi} : Nat) := hsingleton
    _ = LO.FirstOrder.Arithmetic.fstIdx d := hproof.1.symm
    _ ≤ d := hfst_le

/-- Standard-model meaning of the finite-consistency sentence. -/
theorem models_finiteConsistencySentence (e : Nat) :
    Nat↓[ℒₒᵣ] ⊧ finiteConsistencySentence e := by
  simp [finiteConsistencySentence, models_iff,
    LO.FirstOrder.Theory.RestrictedProvable,
    no_standard_proof_falsum]

/-- Exact input-measure calibration: `finiteConsistencySentence e` says that
there is no PA proof code of falsity whose binary bit length is at most `e`.
Thus the exponent in Foundation's restricted provability predicate is not an
extra asymptotic assumption; it is exactly the bit-length cutoff. -/
theorem models_finiteConsistencySentence_iff_no_bitSize_proof (e : Nat) :
    Nat↓[ℒₒᵣ] ⊧ finiteConsistencySentence e ↔
      ∀ d : Nat, Nat.size d ≤ e →
        ¬ LO.FirstOrder.Arithmetic.Bootstrapping.Proof
          PA d (⌜(⊥ : LO.FirstOrder.ArithmeticSentence)⌝ : Nat) := by
  simp [finiteConsistencySentence, models_iff,
    LO.FirstOrder.Theory.RestrictedProvable, Nat.size_le]

/-- Exact Pudlak reading of the target sentence in the standard model. -/
theorem models_finiteConsistencySentence_iff_not_shortPAProof (e : Nat) :
    Nat↓[ℒₒᵣ] ⊧ finiteConsistencySentence e ↔
      ¬ ShortPAProof e (⊥ : LO.FirstOrder.ArithmeticSentence) := by
  rw [models_finiteConsistencySentence_iff_no_bitSize_proof]
  simp [ShortPAProof]

theorem finiteConsistencySentence_sigmaOne (e : Nat) :
    LO.FirstOrder.Arithmetic.Hierarchy 𝚺 1
      (finiteConsistencySentence e) := by
  simp [finiteConsistencySentence]

/-- PA proves each fixed finite-consistency sentence. -/
theorem provable_finiteConsistencySentence (e : Nat) :
    PA ⊢ finiteConsistencySentence e :=
  LO.FirstOrder.Arithmetic.sigma_one_completeness
    (T := PA)
    (finiteConsistencySentence_sigmaOne e)
    (models_finiteConsistencySentence e)

noncomputable def finiteConsistencyProof (e : Nat) :
    PA ⊢! finiteConsistencySentence e :=
  Classical.choice (provable_finiteConsistencySentence e)

/-- Fast outer exponent `2^(A*n)`, with explicit amplification `A`. -/
def powerExponent (amplification n : Nat) : Nat :=
  2 ^ (amplification * n)

/-- Fast outer rescaling used by the lower-bound target. -/
noncomputable def powerSentence (amplification n : Nat) :
    LO.FirstOrder.ArithmeticSentence :=
  finiteConsistencySentence (powerExponent amplification n)

/-- Foundation's real arithmetized PA checker for `Con_PA(2^(A*n))`. -/
def Checks (amplification d n : Nat) : Prop :=
  LO.FirstOrder.Arithmetic.Bootstrapping.Proof
    PA d (⌜powerSentence amplification n⌝ : Nat)

/-- The same real Foundation checker before the exponential outer
reparameterization.  Its input `e` is the exact bit-length cutoff appearing in
`finiteConsistencySentence e`. -/
def ChecksAtBitCutoff (d e : Nat) : Prop :=
  LO.FirstOrder.Arithmetic.Bootstrapping.Proof
    PA d (⌜finiteConsistencySentence e⌝ : Nat)

@[simp] theorem checks_iff_checksAtBitCutoff
    (amplification d n : Nat) :
    Checks amplification d n ↔
      ChecksAtBitCutoff d (powerExponent amplification n) := by
  rfl

theorem checks_complete (amplification n : Nat) :
    ∃ d : Nat, Checks amplification d n := by
  refine ⟨⌜finiteConsistencyProof (powerExponent amplification n)⌝, ?_⟩
  exact LO.FirstOrder.proof_of_quote_proof
    (finiteConsistencyProof (powerExponent amplification n))

theorem acceptedBitSize_exists (amplification n : Nat) :
    ∃ k : Nat, ∃ d : Nat,
      Checks amplification d n ∧ Nat.size d = k := by
  rcases checks_complete amplification n with ⟨d, hd⟩
  exact ⟨Nat.size d, d, hd, rfl⟩

noncomputable def minAcceptedBitSize
    (amplification n : Nat) : Nat := by
  classical
  exact Nat.find (acceptedBitSize_exists amplification n)

theorem minAcceptedBitSize_spec (amplification n : Nat) :
    ∃ d : Nat,
      Checks amplification d n ∧
        Nat.size d = minAcceptedBitSize amplification n := by
  classical
  exact Nat.find_spec (acceptedBitSize_exists amplification n)

/-- Raw-code growth endpoint.  This is not the Friedman-Pudlak/Buss theorem:
the encoding audit proves it from conclusion-size inflation alone. -/
def EventuallyEveryFiniteConsistencyProofAbovePowTwo
    (amplification : Nat) : Prop :=
  ∀ᶠ n in atTop,
    ∀ d : Nat, Checks amplification d n → 2 ^ n < Nat.size d

/-- Diagnostic discrete power form in Foundation's raw-code coordinate.
Although this shape resembles a Pudlak/Friedman lower bound, degree one follows
from the encoding of the conclusion itself.  It must not be cited as a
proof-complexity result. -/
def EventuallyFiniteConsistencyProofPowerLower
    (degree : Nat) : Prop :=
  ∀ᶠ e in atTop,
    ∀ d : Nat, ChecksAtBitCutoff d e → e < (Nat.size d) ^ degree

/-- Existential positive-exponent form of the remaining quantitative lower
bound. -/
def FiniteConsistencyProofPowerLowerBound : Prop :=
  ∃ degree : Nat,
    0 < degree ∧ EventuallyFiniteConsistencyProofPowerLower degree

/-- Existential amplification endpoint for the diagnostic raw-code measure. -/
def AmplifiedFiniteConsistencyProofLowerBound : Prop :=
  ∃ amplification : Nat,
    0 < amplification ∧
      EventuallyEveryFiniteConsistencyProofAbovePowTwo amplification

theorem self_le_powTwo (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ n + 2 ^ n :=
          Nat.add_le_add_left Nat.one_le_two_pow (2 ^ n)
        _ = 2 ^ (n + 1) := by simp [pow_succ, Nat.mul_two]

/-- The full exponent-amplification calculation.  Given the source inequality
`e < outputBitSize^degree`, choosing the cutoff
`e = 2^(degree*n)` forces every accepted output proof code to have bit length
strictly greater than `2^n`.  The calculation is valid, but in the current raw
coordinate its premise is an encoding artifact rather than a literature
lower-bound theorem. -/
theorem finiteConsistencyPowerLower_to_amplified
    (hlower : FiniteConsistencyProofPowerLowerBound) :
    AmplifiedFiniteConsistencyProofLowerBound := by
  rcases hlower with ⟨degree, hdegree, hpower⟩
  refine ⟨degree, hdegree, ?_⟩
  change ∀ᶠ e in atTop,
    ∀ d : Nat, ChecksAtBitCutoff d e →
      e < (Nat.size d) ^ degree at hpower
  change ∀ᶠ n in atTop,
    ∀ d : Nat, Checks degree d n → 2 ^ n < Nat.size d
  rw [Filter.eventually_atTop] at hpower ⊢
  rcases hpower with ⟨cutoff, hcutoff⟩
  refine ⟨cutoff, ?_⟩
  intro n hn d hchecks
  have hone_degree : 1 ≤ degree := hdegree
  have hn_degree : n ≤ degree * n := by
    simpa only [one_mul] using Nat.mul_le_mul_right n hone_degree
  have hn_scale : n ≤ powerExponent degree n := by
    exact (self_le_powTwo n).trans
      (by
        unfold powerExponent
        exact Nat.pow_le_pow_right (by decide) hn_degree)
  have hsource :
      powerExponent degree n < (Nat.size d) ^ degree := by
    exact hcutoff (powerExponent degree n) (hn.trans hn_scale) d
      (checks_iff_checksAtBitCutoff degree d n |>.mp hchecks)
  by_contra hnot
  have hsize : Nat.size d ≤ 2 ^ n := Nat.le_of_not_gt hnot
  have hsize_power :
      (Nat.size d) ^ degree ≤ (2 ^ n) ^ degree :=
    Nat.pow_le_pow_left hsize degree
  have hupper :
      (Nat.size d) ^ degree ≤ powerExponent degree n := by
    calc
      (Nat.size d) ^ degree ≤ (2 ^ n) ^ degree := hsize_power
      _ = 2 ^ (n * degree) := by rw [pow_mul]
      _ = 2 ^ (degree * n) := by rw [Nat.mul_comm]
      _ = powerExponent degree n := rfl
  exact (not_lt_of_ge hupper) hsource

def PolynomialBound (f : Nat → Real) : Prop :=
  ∃ (c : Real) (k : Nat),
    ∀ n : Nat, f n ≤ c * ((n : Real) + 1) ^ k

def powTwoLowerEnvelope (n : Nat) : Real :=
  (2 : Real) ^ n

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

/-- The missing concrete theorem implies an eventual lower bound for the exact
minimum accepted bit length. -/
theorem eventualProofLower_to_minAcceptedBitSize_eventually_gt_powTwo
    {amplification : Nat}
    (hlower :
      EventuallyEveryFiniteConsistencyProofAbovePowTwo amplification) :
    ∀ᶠ n in atTop,
      powTwoLowerEnvelope n <
        (minAcceptedBitSize amplification n : Real) := by
  filter_upwards [hlower] with n hn
  rcases minAcceptedBitSize_spec amplification n with ⟨d, hd, hsize⟩
  have hnat : 2 ^ n < minAcceptedBitSize amplification n := by
    simpa [hsize] using hn d hd
  unfold powTwoLowerEnvelope
  exact_mod_cast hnat

/-- Full strong-growth conclusion for the real finite-consistency checker. -/
theorem eventualProofLower_to_minAcceptedBitSize_strongLowerBound
    {amplification : Nat}
    (hlower :
      EventuallyEveryFiniteConsistencyProofAbovePowTwo amplification) :
    ∀ U : Nat → Real, PolynomialBound U →
      ∃ᶠ n in atTop,
        (minAcceptedBitSize amplification n : Real) > U n := by
  intro U hU
  have hpoly := powTwoLowerEnvelope_eventually_gt_polynomial U hU
  have hmin :=
    eventualProofLower_to_minAcceptedBitSize_eventually_gt_powTwo hlower
  have hevent :
      ∀ᶠ n in atTop,
        U n < (minAcceptedBitSize amplification n : Real) := by
    filter_upwards [hpoly, hmin] with n hnPoly hnMin
    exact hnPoly.trans hnMin
  rw [Filter.frequently_atTop]
  intro N
  rcases Filter.eventually_atTop.1 hevent with ⟨Nmin, hNmin⟩
  exact ⟨max N Nmin, le_max_left _ _, hNmin _ (le_max_right _ _)⟩

/-- Existential amplified literature input gives one concrete fast family with
the full strong lower bound. -/
theorem amplifiedProofLower_to_exists_strongLowerBound
    (hlower : AmplifiedFiniteConsistencyProofLowerBound) :
    ∃ amplification : Nat,
      0 < amplification ∧
        ∀ U : Nat → Real, PolynomialBound U →
          ∃ᶠ n in atTop,
            (minAcceptedBitSize amplification n : Real) > U n := by
  rcases hlower with ⟨amplification, hpositive, hcodes⟩
  exact ⟨amplification, hpositive,
    eventualProofLower_to_minAcceptedBitSize_strongLowerBound hcodes⟩

#check no_standard_proof_falsum
#print axioms no_standard_proof_falsum

#check checks_complete
#print axioms checks_complete

#check models_finiteConsistencySentence_iff_no_bitSize_proof
#print axioms models_finiteConsistencySentence_iff_no_bitSize_proof

#check finiteConsistencyPowerLower_to_amplified
#print axioms finiteConsistencyPowerLower_to_amplified

#check eventualProofLower_to_minAcceptedBitSize_strongLowerBound
#print axioms eventualProofLower_to_minAcceptedBitSize_strongLowerBound

end FoundationPAFiniteConsistencyLowerBoundTarget
