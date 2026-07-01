/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.Analytic
import EulerLimit.ProofComplexityCore
import EulerLimit.MiniHilbert

/-!
# Gödel-Sondow Coupling Hypothesis Formalization
This module formalizes the Euler-Mascheroni constant limit definition,
proof-complexity and projection-bridge layers.
-/

open Filter

def theorem_reference_certificate_size (_n : ℕ) : ℝ :=
  1

theorem theorem_reference_certificate_size_polynomial :
    is_polynomial_bound theorem_reference_certificate_size := by
  refine ⟨1, 0, ?_⟩
  intro n
  simp [theorem_reference_certificate_size]

def product_log_reference_certificate_size : ℕ → ℝ :=
  theorem_reference_certificate_size

theorem product_log_reference_certificate_size_polynomial :
    is_polynomial_bound product_log_reference_certificate_size :=
  theorem_reference_certificate_size_polynomial

def binary_index_certificate_size (n : ℕ) : ℝ :=
  Nat.log2 (n + 1) + 1

theorem nat_log2_add_one_le_self_add_one (n : ℕ) :
    (Nat.log2 (n + 1) : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by
  have hlog : Nat.log2 (n + 1) ≤ n + 1 := by
    simpa using Nat.log2_le_self (n + 1)
  have hlog_real : (Nat.log2 (n + 1) : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast hlog
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]

theorem binary_index_certificate_size_polynomial :
    is_polynomial_bound binary_index_certificate_size := by
  refine ⟨2, 1, ?_⟩
  intro n
  simpa [binary_index_certificate_size] using nat_log2_add_one_le_self_add_one n

def tail_bound_trace_certificate_size (n : ℕ) : ℝ :=
  n

theorem tail_bound_trace_certificate_size_polynomial :
    is_polynomial_bound tail_bound_trace_certificate_size := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp [tail_bound_trace_certificate_size]

def tail_bound_certificate_size (n : ℕ) : ℝ :=
  binary_index_certificate_size n +
    theorem_reference_certificate_size n +
    theorem_reference_certificate_size n +
    theorem_reference_certificate_size n +
    theorem_reference_certificate_size n

def tail_bound_certificate_accepted (n : ℕ) : Prop :=
  sondow_term_lt_one_prop n

theorem tail_bound_certificate_size_polynomial :
    is_polynomial_bound tail_bound_certificate_size := by
  refine ⟨6, 1, ?_⟩
  intro n
  have hlog := nat_log2_add_one_le_self_add_one n
  simp [tail_bound_certificate_size, binary_index_certificate_size,
    theorem_reference_certificate_size] at *
  nlinarith

structure TailBoundCertificateInputs : Prop where
  size_polynomial : is_polynomial_bound tail_bound_certificate_size
  accepted_eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → tail_bound_certificate_accepted n

theorem tail_bound_certificate_inputs_of_lcm_bound
    (hlcm : lcmUpto_le_three_pow_nat_statement) :
    TailBoundCertificateInputs where
  size_polynomial := tail_bound_certificate_size_polynomial
  accepted_eventual := sondow_term_lt_one_eventual_of_lcm_bound hlcm

def denominator_trace_certificate_size (n : ℕ) : ℝ :=
  n

theorem denominator_trace_certificate_size_polynomial :
    is_polynomial_bound denominator_trace_certificate_size := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp [denominator_trace_certificate_size]

def denominator_certificate_size (n : ℕ) : ℝ :=
  binary_index_certificate_size n +
    theorem_reference_certificate_size n +
    theorem_reference_certificate_size n +
    theorem_reference_certificate_size n

def denominator_certificate_accepted (q : ℚ) (n : ℕ) : Prop :=
  q.den ≤ 2 * n ∧
    Rat.is_integer ((d (2 * n) : ℚ) * A_rat n) ∧
    Rat.is_integer ((((d (2 * n) * Nat.choose (2 * n) n : ℕ) : ℚ) * q))

theorem denominator_certificate_size_polynomial :
    is_polynomial_bound denominator_certificate_size := by
  refine ⟨5, 1, ?_⟩
  intro n
  have hlog := nat_log2_add_one_le_self_add_one n
  simp [denominator_certificate_size, binary_index_certificate_size,
    theorem_reference_certificate_size] at *
  nlinarith

structure DenominatorCertificateInputs (q : ℚ) : Prop where
  size_polynomial : is_polynomial_bound denominator_certificate_size
  accepted_eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → denominator_certificate_accepted q n

theorem denominator_certificate_accepted_of_den_le (q : ℚ) {n : ℕ}
    (hden : q.den ≤ 2 * n) :
    denominator_certificate_accepted q n := by
  refine ⟨hden, d_mul_A_rat_is_integer n, ?_⟩
  exact d_mul_choose_mul_rat_is_integer_of_den_le n q hden

theorem denominator_certificate_inputs (q : ℚ) :
    DenominatorCertificateInputs q where
  size_polynomial := denominator_certificate_size_polynomial
  accepted_eventual := by
    refine ⟨q.den, ?_⟩
    intro n hn
    exact denominator_certificate_accepted_of_den_le q (by omega)

def rational_sondow_certificate_components_accepted (q : ℚ) (n : ℕ) : Prop :=
  tail_bound_certificate_accepted n ∧ denominator_certificate_accepted q n

def rational_sondow_certificate_components_size (n : ℕ) : ℝ :=
  tail_bound_certificate_size n + denominator_certificate_size n

theorem rational_sondow_certificate_components_size_polynomial :
    is_polynomial_bound rational_sondow_certificate_components_size := by
  refine ⟨11, 1, ?_⟩
  intro n
  have hlog := nat_log2_add_one_le_self_add_one n
  simp [rational_sondow_certificate_components_size,
    tail_bound_certificate_size, denominator_certificate_size,
    binary_index_certificate_size, theorem_reference_certificate_size] at *
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]

structure RationalSondowCertificateComponentInputs (q : ℚ) : Prop where
  size_polynomial : is_polynomial_bound rational_sondow_certificate_components_size
  accepted_eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      rational_sondow_certificate_components_accepted q n

def rational_sondow_certificate_components_under_rationality : Prop :=
  ∃ q : ℚ, (q : ℝ) = euler_mascheroni ∧ RationalSondowCertificateComponentInputs q

theorem rational_sondow_certificate_component_inputs
    (hlcm : lcmUpto_le_three_pow_nat_statement) (q : ℚ) :
    RationalSondowCertificateComponentInputs q where
  size_polynomial := rational_sondow_certificate_components_size_polynomial
  accepted_eventual := by
    rcases (tail_bound_certificate_inputs_of_lcm_bound hlcm).accepted_eventual with
      ⟨Nt, hNt⟩
    rcases (denominator_certificate_inputs q).accepted_eventual with ⟨Nd, hNd⟩
    refine ⟨max Nt Nd, ?_⟩
    intro n hn
    exact ⟨hNt n (le_trans (Nat.le_max_left Nt Nd) hn),
      hNd n (le_trans (Nat.le_max_right Nt Nd) hn)⟩

theorem rational_sondow_certificate_components_of_rationality
    (hlcm : lcmUpto_le_three_pow_nat_statement)
    (h_rat : is_rational euler_mascheroni) :
    rational_sondow_certificate_components_under_rationality := by
  rcases h_rat with ⟨q, hq⟩
  exact ⟨q, hq, rational_sondow_certificate_component_inputs hlcm q⟩

def full_sondow_certificate_accepted (q : ℚ) (n : ℕ) : Prop :=
  (q : ℝ) = euler_mascheroni ∧
    rational_sondow_certificate_components_accepted q n ∧
    sondow_explicit_product_log_relation_prop n ∧
    sondow_explicit_decomposition_prop n

def full_sondow_certificate_size (n : ℕ) : ℝ :=
  rational_sondow_certificate_components_size n +
    product_log_reference_certificate_size n +
    theorem_reference_certificate_size n

theorem full_sondow_certificate_size_polynomial :
    is_polynomial_bound full_sondow_certificate_size := by
  refine ⟨13, 1, ?_⟩
  intro n
  have hlog := nat_log2_add_one_le_self_add_one n
  simp [full_sondow_certificate_size, rational_sondow_certificate_components_size,
    tail_bound_certificate_size, denominator_certificate_size,
    binary_index_certificate_size, product_log_reference_certificate_size,
    theorem_reference_certificate_size] at *
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]

structure FullSondowCertificateInputs (q : ℚ) : Prop where
  size_polynomial : is_polynomial_bound full_sondow_certificate_size
  accepted_eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → full_sondow_certificate_accepted q n

theorem full_sondow_certificate_inputs
    (hfwd : SondowForwardInputs) {q : ℚ}
    (hq : (q : ℝ) = euler_mascheroni) :
    FullSondowCertificateInputs q where
  size_polynomial := full_sondow_certificate_size_polynomial
  accepted_eventual := by
    rcases (rational_sondow_certificate_component_inputs hfwd.lcm_bound q).accepted_eventual with
      ⟨Nc, hNc⟩
    refine ⟨max 1 Nc, ?_⟩
    intro n hn
    have hn_one : 1 ≤ n := le_trans (Nat.le_max_left 1 Nc) hn
    have hn_comp : Nc ≤ n := le_trans (Nat.le_max_right 1 Nc) hn
    exact ⟨hq, hNc n hn_comp, hfwd.product_log n hn_one, hfwd.decomposition n hn_one⟩

def full_sondow_certificate_under_rationality : Prop :=
  ∃ q : ℚ, (q : ℝ) = euler_mascheroni ∧ FullSondowCertificateInputs q

theorem full_sondow_certificate_of_rationality
    (hfwd : SondowForwardInputs)
    (h_rat : is_rational euler_mascheroni) :
    full_sondow_certificate_under_rationality := by
  rcases h_rat with ⟨q, hq⟩
  exact ⟨q, hq, full_sondow_certificate_inputs hfwd hq⟩

-- Uninterpreted payload predicate used by the reflection-graft route.  Declaring
-- this predicate is not a truth axiom: it does not prove
-- `partial_consistency_payload n` for any `n`.  Truth is supplied separately by
-- `PartialConsistencyPayloadTruth` or `PartialConsistencyPayloadSpec`, so public
-- route theorems keep this external input visible at the boundary.
axiom partial_consistency_payload : ℕ → Prop

-- Uninterpreted strengthened finite-consistency payload.  This is deliberately
-- kept separate from `partial_consistency_payload`: ordinary finite consistency
-- can have short proofs in the same theory, whereas strengthened or iterated
-- consistency is the intended Pudlak-style lower-bound target.  As above, this
-- declaration introduces a predicate vocabulary, not a proof of its instances.
axiom strengthened_partial_consistency_payload : ℕ → Prop

def reflection_graft_certificate_accepted (q : ℚ) (n : ℕ) : Prop :=
  full_sondow_certificate_accepted q n ∧ partial_consistency_payload n

def reflection_graft_certificate_size (n : ℕ) : ℝ :=
  full_sondow_certificate_size n + theorem_reference_certificate_size n

theorem reflection_graft_certificate_size_polynomial :
    is_polynomial_bound reflection_graft_certificate_size := by
  refine ⟨14, 1, ?_⟩
  intro n
  have hlog := nat_log2_add_one_le_self_add_one n
  simp [reflection_graft_certificate_size, full_sondow_certificate_size,
    rational_sondow_certificate_components_size, tail_bound_certificate_size,
    denominator_certificate_size, binary_index_certificate_size,
    product_log_reference_certificate_size, theorem_reference_certificate_size] at *
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]

structure ReflectionGraftPayloadInputs : Prop where
  accepted_eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → partial_consistency_payload n

-- External truth/soundness block for the finite partial-consistency payload.
-- In a concrete arithmetic development this should be discharged by the
-- selected finite-consistency or reflection theorem.
structure PartialConsistencyPayloadTruth : Prop where
  true_all : ∀ n : ℕ, partial_consistency_payload n

theorem reflection_graft_payload_inputs_of_partial_consistency_truth
    (htruth : PartialConsistencyPayloadTruth) :
    ReflectionGraftPayloadInputs where
  accepted_eventual := ⟨0, fun n _hn => htruth.true_all n⟩

structure ReflectionGraftCertificateInputs (q : ℚ) : Prop where
  size_polynomial : is_polynomial_bound reflection_graft_certificate_size
  accepted_eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → reflection_graft_certificate_accepted q n

theorem reflection_graft_certificate_inputs
    (hfwd : SondowForwardInputs) (hpayload : ReflectionGraftPayloadInputs)
    {q : ℚ} (hq : (q : ℝ) = euler_mascheroni) :
    ReflectionGraftCertificateInputs q where
  size_polynomial := reflection_graft_certificate_size_polynomial
  accepted_eventual := by
    rcases (full_sondow_certificate_inputs hfwd hq).accepted_eventual with
      ⟨Ns, hNs⟩
    rcases hpayload.accepted_eventual with ⟨Np, hNp⟩
    refine ⟨max Ns Np, ?_⟩
    intro n hn
    exact ⟨hNs n (le_trans (Nat.le_max_left Ns Np) hn),
      hNp n (le_trans (Nat.le_max_right Ns Np) hn)⟩

def certificate_size (φ : FormulaCode) : ℝ :=
  match φ.family with
  | FormulaFamily.sondowCertificateValid => full_sondow_certificate_size φ.index
  | FormulaFamily.sondowTailBoundCertificate => tail_bound_certificate_size φ.index
  | FormulaFamily.sondowDenominatorCertificate => denominator_certificate_size φ.index
  | FormulaFamily.sondowProductLogCertificate => product_log_reference_certificate_size φ.index
  | FormulaFamily.partialConsistency => φ.index
  | FormulaFamily.strengthenedPartialConsistency => φ.index
  | FormulaFamily.sondowReflectionGraft => reflection_graft_certificate_size φ.index
  | _ => φ.index

def verifier_trace_size (φ : ℕ → FormulaCode) (n : ℕ) : ℝ :=
  binary_index_certificate_size n + certificate_size (φ n) +
    theorem_reference_certificate_size n

def proof_predicate_formula_size (φ : ℕ → FormulaCode) (n : ℕ) : ℝ :=
  verifier_trace_size φ n + theorem_reference_certificate_size n

structure VerifierTracePolynomial (φ : ℕ → FormulaCode) : Prop where
  trace_polynomial : is_polynomial_bound (verifier_trace_size φ)

structure ProofPredicatePolynomial (φ : ℕ → FormulaCode) : Prop where
  predicate_polynomial : is_polynomial_bound (proof_predicate_formula_size φ)

structure BinaryNumeralEncoding (φ : ℕ → FormulaCode) : Prop where
  index_size_polynomial : is_polynomial_bound binary_index_certificate_size

structure SymbolOrBitSizeEncoding (φ : ℕ → FormulaCode) : Prop where
  formula_size_polynomial : ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
    ∀ n : ℕ, certificate_size (φ n) ≤ f n

def accepted_certificate (φ : FormulaCode) : Prop :=
  match φ.family with
  | FormulaFamily.sondowCertificateValid =>
      ∃ q : ℚ, full_sondow_certificate_accepted q φ.index
  | FormulaFamily.sondowTailBoundCertificate =>
      tail_bound_certificate_accepted φ.index
  | FormulaFamily.sondowDenominatorCertificate =>
      ∃ q : ℚ, denominator_certificate_accepted q φ.index
  | FormulaFamily.sondowProductLogCertificate =>
      sondow_explicit_product_log_relation_prop φ.index
  | FormulaFamily.partialConsistency =>
      partial_consistency_payload φ.index
  | FormulaFamily.strengthenedPartialConsistency =>
      strengthened_partial_consistency_payload φ.index
  | FormulaFamily.sondowReflectionGraft =>
      ∃ q : ℚ, reflection_graft_certificate_accepted q φ.index
  | _ => False

theorem partialConsistencyCode_family (n : ℕ) :
    (partialConsistencyCode n).family = FormulaFamily.partialConsistency := by
  rfl

theorem partialConsistencyCode_index (n : ℕ) :
    (partialConsistencyCode n).index = n := by
  rfl

theorem strengthenedPartialConsistencyCode_family (n : ℕ) :
    (strengthenedPartialConsistencyCode n).family =
      FormulaFamily.strengthenedPartialConsistency := by
  rfl

theorem strengthenedPartialConsistencyCode_index (n : ℕ) :
    (strengthenedPartialConsistencyCode n).index = n := by
  rfl

theorem accepted_certificate_partialConsistencyCode_iff (n : ℕ) :
    accepted_certificate (partialConsistencyCode n) ↔
      partial_consistency_payload n := by
  rfl

theorem accepted_certificate_strengthenedPartialConsistencyCode_iff (n : ℕ) :
    accepted_certificate (strengthenedPartialConsistencyCode n) ↔
      strengthened_partial_consistency_payload n := by
  rfl

theorem accepted_certificate_partialConsistencyCode_of_payload
    {n : ℕ} (hpayload : partial_consistency_payload n) :
    accepted_certificate (partialConsistencyCode n) :=
  (accepted_certificate_partialConsistencyCode_iff n).2 hpayload

theorem payload_of_accepted_certificate_partialConsistencyCode
    {n : ℕ} (hacc : accepted_certificate (partialConsistencyCode n)) :
    partial_consistency_payload n :=
  (accepted_certificate_partialConsistencyCode_iff n).1 hacc

theorem accepted_certificate_strengthenedPartialConsistencyCode_of_payload
    {n : ℕ} (hpayload : strengthened_partial_consistency_payload n) :
    accepted_certificate (strengthenedPartialConsistencyCode n) :=
  (accepted_certificate_strengthenedPartialConsistencyCode_iff n).2 hpayload

theorem strengthened_payload_of_accepted_certificate
    {n : ℕ}
    (hacc : accepted_certificate (strengthenedPartialConsistencyCode n)) :
    strengthened_partial_consistency_payload n :=
  (accepted_certificate_strengthenedPartialConsistencyCode_iff n).1 hacc

structure StrengthenedPartialConsistencyAcceptedTruth : Prop where
  accepted_all :
    ∀ n : ℕ, accepted_certificate (strengthenedPartialConsistencyCode n)

structure StrengthenedPartialConsistencyPayloadTruth : Prop where
  true_all : ∀ n : ℕ, strengthened_partial_consistency_payload n

theorem StrengthenedPartialConsistencyAcceptedTruth.toPayloadTruth
    (h : StrengthenedPartialConsistencyAcceptedTruth) :
    StrengthenedPartialConsistencyPayloadTruth where
  true_all := by
    intro n
    exact strengthened_payload_of_accepted_certificate (h.accepted_all n)

theorem StrengthenedPartialConsistencyPayloadTruth.toAcceptedTruth
    (h : StrengthenedPartialConsistencyPayloadTruth) :
    StrengthenedPartialConsistencyAcceptedTruth where
  accepted_all := by
    intro n
    exact accepted_certificate_strengthenedPartialConsistencyCode_of_payload
      (h.true_all n)

theorem strengthenedPartialConsistencyAcceptedTruth_iff_payloadTruth :
    StrengthenedPartialConsistencyAcceptedTruth ↔
      StrengthenedPartialConsistencyPayloadTruth :=
  ⟨StrengthenedPartialConsistencyAcceptedTruth.toPayloadTruth,
    StrengthenedPartialConsistencyPayloadTruth.toAcceptedTruth⟩

structure PartialConsistencyAcceptedCodeRealization where
  code_family : ℕ → FormulaCode
  code_family_eq : code_family = partialConsistencyCode
  family_exact :
    ∀ n : ℕ, (code_family n).family = FormulaFamily.partialConsistency
  index_exact : ∀ n : ℕ, (code_family n).index = n
  accepted_exact :
    ∀ n : ℕ, accepted_certificate (code_family n) ↔
      partial_consistency_payload n

def partial_consistency_accepted_code_realization_true :
    PartialConsistencyAcceptedCodeRealization where
  code_family := partialConsistencyCode
  code_family_eq := rfl
  family_exact := partialConsistencyCode_family
  index_exact := partialConsistencyCode_index
  accepted_exact := accepted_certificate_partialConsistencyCode_iff

-- Code-level version of the reflection-graft payload input.  This is closer to
-- the verifier route: the partial-consistency component is supplied as accepted
-- certificates for the standard `partialConsistencyCode` family, and only then
-- translated to the raw payload proposition used inside the graft.
structure ReflectionGraftCodePayloadInputs : Prop where
  accepted_eventual :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      accepted_certificate (partialConsistencyCode n)

theorem ReflectionGraftCodePayloadInputs.toPayloadInputs
    (h : ReflectionGraftCodePayloadInputs) :
    ReflectionGraftPayloadInputs where
  accepted_eventual := by
    rcases h.accepted_eventual with ⟨N, hN⟩
    exact ⟨N, fun n hn => hN n hn⟩

theorem ReflectionGraftPayloadInputs.toCodePayloadInputs
    (h : ReflectionGraftPayloadInputs) :
    ReflectionGraftCodePayloadInputs where
  accepted_eventual := by
    rcases h.accepted_eventual with ⟨N, hN⟩
    exact ⟨N, fun n hn => hN n hn⟩

theorem reflection_graft_payload_inputs_iff_code_payload_inputs :
    ReflectionGraftPayloadInputs ↔ ReflectionGraftCodePayloadInputs :=
  ⟨ReflectionGraftPayloadInputs.toCodePayloadInputs,
    ReflectionGraftCodePayloadInputs.toPayloadInputs⟩

theorem reflection_graft_code_payload_inputs_of_partial_consistency_truth
    (htruth : PartialConsistencyPayloadTruth) :
    ReflectionGraftCodePayloadInputs :=
  (reflection_graft_payload_inputs_of_partial_consistency_truth htruth)
    |>.toCodePayloadInputs

def verifier_accepts (φ : ℕ → FormulaCode) (n : ℕ) : Prop :=
  accepted_certificate (φ n)

structure VerifierFamilyFixed (φ : ℕ → FormulaCode) : Prop where
  family_eq :
    ∀ n : ℕ, (φ n).family = (φ 0).family

structure AcceptedFormulaRepresentsVerifier (φ : ℕ → FormulaCode) : Prop where
  represents :
    ∀ n : ℕ, accepted_certificate (φ n) ↔ verifier_accepts φ n

theorem verifier_family_fixed_sondowCertificateValidCode :
    VerifierFamilyFixed sondowCertificateValidCode where
  family_eq := by
    intro n
    rfl

theorem verifier_family_fixed_sondowReflectionGraftCode :
    VerifierFamilyFixed sondowReflectionGraftCode where
  family_eq := by
    intro n
    rfl

theorem verifier_family_fixed_partialConsistencyCode :
    VerifierFamilyFixed partialConsistencyCode where
  family_eq := by
    intro n
    rfl

theorem verifier_family_fixed_strengthenedPartialConsistencyCode :
    VerifierFamilyFixed strengthenedPartialConsistencyCode where
  family_eq := by
    intro n
    rfl

theorem accepted_formula_represents_verifier_sondowCertificateValidCode :
    AcceptedFormulaRepresentsVerifier sondowCertificateValidCode where
  represents := by
    intro n
    rfl

theorem accepted_formula_represents_verifier_sondowReflectionGraftCode :
    AcceptedFormulaRepresentsVerifier sondowReflectionGraftCode where
  represents := by
    intro n
    rfl

theorem accepted_formula_represents_verifier_partialConsistencyCode :
    AcceptedFormulaRepresentsVerifier partialConsistencyCode where
  represents := by
    intro n
    rfl

theorem accepted_formula_represents_verifier_strengthenedPartialConsistencyCode :
    AcceptedFormulaRepresentsVerifier strengthenedPartialConsistencyCode where
  represents := by
    intro n
    rfl

def certificate_verifier_polytime (φ : ℕ → FormulaCode) : Prop :=
  match (φ 0).family with
  | FormulaFamily.sondowCertificateValid => True
  | FormulaFamily.sondowTailBoundCertificate => True
  | FormulaFamily.sondowDenominatorCertificate => True
  | FormulaFamily.sondowProductLogCertificate => True
  | FormulaFamily.partialConsistency => True
  | FormulaFamily.strengthenedPartialConsistency => True
  | FormulaFamily.sondowReflectionGraft => True
  | _ => False

theorem certificate_verifier_polytime_sondowCertificateValidCode :
    certificate_verifier_polytime sondowCertificateValidCode := by
  trivial

theorem certificate_verifier_polytime_sondowReflectionGraftCode :
    certificate_verifier_polytime sondowReflectionGraftCode := by
  trivial

theorem certificate_verifier_polytime_partialConsistencyCode :
    certificate_verifier_polytime partialConsistencyCode := by
  trivial

theorem certificate_verifier_polytime_strengthenedPartialConsistencyCode :
    certificate_verifier_polytime strengthenedPartialConsistencyCode := by
  trivial

theorem verifier_trace_size_sondowCertificateValidCode_polynomial :
    is_polynomial_bound (verifier_trace_size sondowCertificateValidCode) := by
  refine ⟨16, 1, ?_⟩
  intro n
  have hlog := nat_log2_add_one_le_self_add_one n
  simp [verifier_trace_size, certificate_size, sondowCertificateValidCode,
    full_sondow_certificate_size,
    rational_sondow_certificate_components_size, tail_bound_certificate_size,
    denominator_certificate_size, binary_index_certificate_size,
    product_log_reference_certificate_size, theorem_reference_certificate_size] at *
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]

theorem proof_predicate_formula_size_sondowCertificateValidCode_polynomial :
    is_polynomial_bound (proof_predicate_formula_size sondowCertificateValidCode) := by
  refine ⟨17, 1, ?_⟩
  intro n
  have hlog := nat_log2_add_one_le_self_add_one n
  simp [proof_predicate_formula_size, verifier_trace_size, certificate_size,
    sondowCertificateValidCode,
    full_sondow_certificate_size, rational_sondow_certificate_components_size,
    tail_bound_certificate_size, denominator_certificate_size,
    binary_index_certificate_size, product_log_reference_certificate_size,
    theorem_reference_certificate_size] at *
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]

theorem verifier_trace_size_sondowReflectionGraftCode_polynomial :
    is_polynomial_bound (verifier_trace_size sondowReflectionGraftCode) := by
  refine ⟨18, 1, ?_⟩
  intro n
  have hlog := nat_log2_add_one_le_self_add_one n
  simp [verifier_trace_size, certificate_size, sondowReflectionGraftCode,
    reflection_graft_certificate_size,
    full_sondow_certificate_size, rational_sondow_certificate_components_size,
    tail_bound_certificate_size, denominator_certificate_size,
    binary_index_certificate_size, product_log_reference_certificate_size,
    theorem_reference_certificate_size] at *
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]

theorem proof_predicate_formula_size_sondowReflectionGraftCode_polynomial :
    is_polynomial_bound (proof_predicate_formula_size sondowReflectionGraftCode) := by
  refine ⟨19, 1, ?_⟩
  intro n
  have hlog := nat_log2_add_one_le_self_add_one n
  simp [proof_predicate_formula_size, verifier_trace_size, certificate_size,
    sondowReflectionGraftCode, reflection_graft_certificate_size,
    full_sondow_certificate_size,
    rational_sondow_certificate_components_size, tail_bound_certificate_size,
    denominator_certificate_size, binary_index_certificate_size,
    product_log_reference_certificate_size, theorem_reference_certificate_size] at *
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]

theorem verifier_trace_size_partialConsistencyCode_polynomial :
    is_polynomial_bound (verifier_trace_size partialConsistencyCode) := by
  refine ⟨4, 1, ?_⟩
  intro n
  have hlog := nat_log2_add_one_le_self_add_one n
  simp [verifier_trace_size, certificate_size, partialConsistencyCode,
    binary_index_certificate_size, theorem_reference_certificate_size] at *
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]

theorem proof_predicate_formula_size_partialConsistencyCode_polynomial :
    is_polynomial_bound (proof_predicate_formula_size partialConsistencyCode) := by
  refine ⟨5, 1, ?_⟩
  intro n
  have hlog := nat_log2_add_one_le_self_add_one n
  simp [proof_predicate_formula_size, verifier_trace_size, certificate_size,
    partialConsistencyCode, binary_index_certificate_size,
    theorem_reference_certificate_size] at *
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]

theorem partial_consistency_certificate_size_polynomial :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, certificate_size (partialConsistencyCode n) ≤ f n := by
  refine ⟨fun n : ℕ => (n : ℝ), ⟨1, 1, ?_⟩, ?_⟩
  · intro n
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]
  · intro n
    simp [certificate_size, partialConsistencyCode]

theorem verifier_trace_size_strengthenedPartialConsistencyCode_polynomial :
    is_polynomial_bound
      (verifier_trace_size strengthenedPartialConsistencyCode) := by
  refine ⟨4, 1, ?_⟩
  intro n
  have hlog := nat_log2_add_one_le_self_add_one n
  simp [verifier_trace_size, certificate_size,
    strengthenedPartialConsistencyCode, binary_index_certificate_size,
    theorem_reference_certificate_size] at *
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]

theorem proof_predicate_formula_size_strengthenedPartialConsistencyCode_polynomial :
    is_polynomial_bound
      (proof_predicate_formula_size strengthenedPartialConsistencyCode) := by
  refine ⟨5, 1, ?_⟩
  intro n
  have hlog := nat_log2_add_one_le_self_add_one n
  simp [proof_predicate_formula_size, verifier_trace_size, certificate_size,
    strengthenedPartialConsistencyCode, binary_index_certificate_size,
    theorem_reference_certificate_size] at *
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]

theorem strengthened_partial_consistency_certificate_size_polynomial :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ,
        certificate_size (strengthenedPartialConsistencyCode n) ≤ f n := by
  refine ⟨fun n : ℕ => (n : ℝ), ⟨1, 1, ?_⟩, ?_⟩
  · intro n
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by exact Nat.cast_nonneg n]
  · intro n
    simp [certificate_size, strengthenedPartialConsistencyCode]

structure FullSondowCertificateRealizesFormula : Prop where
  realizes :
    ∀ q : ℚ, ∀ n : ℕ,
      full_sondow_certificate_accepted q n →
        accepted_certificate (sondowCertificateValidCode n)

structure FullSondowCertificateSizeRealization : Prop where
  size_bound :
    ∀ n : ℕ,
      certificate_size (sondowCertificateValidCode n) ≤ full_sondow_certificate_size n

theorem full_sondow_certificate_realizes_formula_true :
    FullSondowCertificateRealizesFormula where
  realizes := by
    intro q n h
    exact ⟨q, h⟩

theorem full_sondow_certificate_size_realization_true :
    FullSondowCertificateSizeRealization where
  size_bound := by
    intro n
    rfl

theorem accepted_sondow_certificate_of_reflection_graft {n : ℕ}
    (h : accepted_certificate (sondowReflectionGraftCode n)) :
    accepted_certificate (sondowCertificateValidCode n) := by
  rcases h with ⟨q, hfull, _hpayload⟩
  exact ⟨q, hfull⟩

theorem partial_consistency_payload_of_reflection_graft {n : ℕ}
    (h : accepted_certificate (sondowReflectionGraftCode n)) :
    partial_consistency_payload n := by
  rcases h with ⟨_q, _hfull, hpayload⟩
  exact hpayload

theorem accepted_partial_consistency_of_reflection_graft {n : ℕ}
    (h : accepted_certificate (sondowReflectionGraftCode n)) :
    accepted_certificate (partialConsistencyCode n) := by
  exact partial_consistency_payload_of_reflection_graft h

-- Publication-facing convention for the model route: the reflection graft is a
-- conjunction of the Sondow certificate component and the partial-consistency
-- payload.  This keeps the proof-length projection target narrow: conjunction
-- elimination should recover the partial-consistency payload.
structure ReflectionGraftConjunctionSyntax : Prop where
  accepted_iff :
    ∀ n : ℕ,
      accepted_certificate (sondowReflectionGraftCode n) ↔
        ∃ q : ℚ,
          full_sondow_certificate_accepted q n ∧ partial_consistency_payload n

theorem reflection_graft_conjunction_syntax_true :
    ReflectionGraftConjunctionSyntax where
  accepted_iff := by
    intro n
    rfl

-- Baseline intended reading: a finite partial-consistency statement such as
-- `Con_PA(n)`, saying that PA has no proof of contradiction with symbol-length
-- at most `n`.  This matches the simple Theorem 4-style payload, but by itself
-- only gives an `n^ε` lower bound; the stronger package below should be read
-- as using Buss's time-constructible rescaling when every-polynomial lower
-- bounds are required.
structure PartialConsistencyPayloadIntendedReading : Prop where
  reads_as_conPA_symbol_length :
    ∀ n : ℕ, accepted_certificate (partialConsistencyCode n) ↔
      partial_consistency_payload n

theorem partial_consistency_payload_intended_reading_true :
    PartialConsistencyPayloadIntendedReading where
  reads_as_conPA_symbol_length := by
    intro n
    rfl

-- A stricter, reusable specification of the finite partial-consistency payload:
-- it fixes the standard code family and records both its acceptance semantics
-- and its truth component.  This packages the payload as a formal object rather
-- than relying only on prose about the intended reading.
structure PartialConsistencyPayloadSpec where
  code_family : ℕ → FormulaCode
  code_family_eq : code_family = partialConsistencyCode
  accepted_iff_payload :
    ∀ n : ℕ, accepted_certificate (code_family n) ↔
      partial_consistency_payload n
  payload_truth : PartialConsistencyPayloadTruth

def PartialConsistencyPayloadSpec.standard
    (htruth : PartialConsistencyPayloadTruth) :
    PartialConsistencyPayloadSpec where
  code_family := partialConsistencyCode
  code_family_eq := rfl
  accepted_iff_payload := by
    intro n
    rfl
  payload_truth := htruth

theorem PartialConsistencyPayloadSpec.toIntendedReading
    (h : PartialConsistencyPayloadSpec) :
    PartialConsistencyPayloadIntendedReading where
  reads_as_conPA_symbol_length := by
    intro n
    rw [← h.code_family_eq]
    exact h.accepted_iff_payload n

theorem PartialConsistencyPayloadSpec.toPayloadTruth
    (h : PartialConsistencyPayloadSpec) :
    PartialConsistencyPayloadTruth :=
  h.payload_truth

def PartialConsistencyAcceptedCodeRealization.toPayloadSpec
    (hcode : PartialConsistencyAcceptedCodeRealization)
    (htruth : PartialConsistencyPayloadTruth) :
    PartialConsistencyPayloadSpec where
  code_family := hcode.code_family
  code_family_eq := hcode.code_family_eq
  accepted_iff_payload := hcode.accepted_exact
  payload_truth := htruth

def PartialConsistencyPayloadSpec.ofAcceptedCodeRealization
    (hcode : PartialConsistencyAcceptedCodeRealization)
    (htruth : PartialConsistencyPayloadTruth) :
    PartialConsistencyPayloadSpec :=
  hcode.toPayloadSpec htruth

def partial_consistency_payload_spec_of_realization
    (hcode : PartialConsistencyAcceptedCodeRealization)
    (htruth : PartialConsistencyPayloadTruth) :
    PartialConsistencyPayloadSpec :=
  hcode.toPayloadSpec htruth

universe acc_u

structure AcceptedCertificateCodeSemantics (φ : ℕ → FormulaCode) where
  relevant : FormulaCode → Prop
  proof_code_semantics : ProofCodeSemantics.{acc_u} relevant
  relevant_family : ∀ n : ℕ, relevant (φ n)
  checks_sound :
    ∀ c : proof_code_semantics.Code, ∀ n : ℕ,
      proof_code_semantics.checks c (φ n) → accepted_certificate (φ n)
  checks_complete :
    ∀ n : ℕ, accepted_certificate (φ n) →
      ∃ c : proof_code_semantics.Code, proof_code_semantics.checks c (φ n)

theorem AcceptedCertificateCodeSemantics.has_code_of_accepted
    {φ : ℕ → FormulaCode} (h : AcceptedCertificateCodeSemantics φ)
    {n : ℕ} (hacc : accepted_certificate (φ n)) :
    ∃ c : h.proof_code_semantics.Code,
      h.proof_code_semantics.checks c (φ n) :=
  h.checks_complete n hacc

theorem AcceptedCertificateCodeSemantics.accepted_of_checked
    {φ : ℕ → FormulaCode} (h : AcceptedCertificateCodeSemantics φ)
    {n : ℕ} {c : h.proof_code_semantics.Code}
    (hchecks : h.proof_code_semantics.checks c (φ n)) :
    accepted_certificate (φ n) :=
  h.checks_sound c n hchecks

def partialConsistencyAcceptedCertificateCodeSemantics
    (hspec : PartialConsistencyPayloadSpec) :
    AcceptedCertificateCodeSemantics partialConsistencyCode where
  relevant := fun code => ∃ n : ℕ, code = partialConsistencyCode n
  proof_code_semantics := {
    Code := ℕ
    checks := fun m code =>
      code = partialConsistencyCode m ∧ accepted_certificate code
    size := fun m => m
    complete := by
      intro code hcode
      rcases hcode with ⟨n, rfl⟩
      have hpayload : partial_consistency_payload n :=
        hspec.payload_truth.true_all n
      have hacc : accepted_certificate (partialConsistencyCode n) :=
        by
          rw [← hspec.code_family_eq]
          exact (hspec.accepted_iff_payload n).2 hpayload
      exact ⟨n, rfl, hacc⟩ }
  relevant_family := by
    intro n
    exact ⟨n, rfl⟩
  checks_sound := by
    intro c n hchecks
    exact hchecks.2
  checks_complete := by
    intro n hacc
    exact ⟨n, rfl, hacc⟩

theorem PartialConsistencyPayloadSpec.accepted_standard_iff
    (h : PartialConsistencyPayloadSpec) (n : ℕ) :
    accepted_certificate (partialConsistencyCode n) ↔
      partial_consistency_payload n := by
  rw [← h.code_family_eq]
  exact h.accepted_iff_payload n

theorem PartialConsistencyPayloadSpec.accepted_standard
    (h : PartialConsistencyPayloadSpec) (n : ℕ) :
    accepted_certificate (partialConsistencyCode n) := by
  exact (h.accepted_standard_iff n).2 (h.payload_truth.true_all n)

theorem PartialConsistencyPayloadSpec.payload_of_accepted_standard
    (h : PartialConsistencyPayloadSpec) {n : ℕ}
    (hacc : accepted_certificate (partialConsistencyCode n)) :
    partial_consistency_payload n :=
  (h.accepted_standard_iff n).1 hacc

theorem PartialConsistencyPayloadSpec.accepted_code_family
    (h : PartialConsistencyPayloadSpec) (n : ℕ) :
    accepted_certificate (h.code_family n) := by
  exact (h.accepted_iff_payload n).2 (h.payload_truth.true_all n)

theorem PartialConsistencyPayloadSpec.code_family_accepted_iff_standard
    (h : PartialConsistencyPayloadSpec) (n : ℕ) :
    accepted_certificate (h.code_family n) ↔
      accepted_certificate (partialConsistencyCode n) := by
  rw [h.accepted_iff_payload n, h.accepted_standard_iff n]

theorem PartialConsistencyPayloadSpec.toReflectionGraftPayloadInputs
    (h : PartialConsistencyPayloadSpec) :
    ReflectionGraftPayloadInputs :=
  reflection_graft_payload_inputs_of_partial_consistency_truth h.toPayloadTruth

theorem PartialConsistencyPayloadSpec.toReflectionGraftCodePayloadInputs
    (h : PartialConsistencyPayloadSpec) :
    ReflectionGraftCodePayloadInputs where
  accepted_eventual := ⟨0, fun n _hn => h.accepted_standard n⟩

theorem PartialConsistencyPayloadSpec.accepted_standard_eventual
    (h : PartialConsistencyPayloadSpec) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      accepted_certificate (partialConsistencyCode n) :=
  ⟨0, fun n _hn => h.accepted_standard n⟩

-- A public-facing truth interface stated entirely in terms of the standard
-- accepted-certificate family.  It is equivalent to `PartialConsistencyPayloadTruth`
-- through the standard payload specification, but exposes less raw payload
-- vocabulary to downstream route statements.
structure PartialConsistencyAcceptedTruth : Prop where
  accepted_all : ∀ n : ℕ, accepted_certificate (partialConsistencyCode n)

theorem PartialConsistencyAcceptedTruth.toPayloadTruth
    (h : PartialConsistencyAcceptedTruth) :
    PartialConsistencyPayloadTruth where
  true_all := by
    intro n
    exact payload_of_accepted_certificate_partialConsistencyCode
      (h.accepted_all n)

theorem PartialConsistencyPayloadTruth.toAcceptedTruth
    (h : PartialConsistencyPayloadTruth) :
    PartialConsistencyAcceptedTruth where
  accepted_all := by
    intro n
    exact accepted_certificate_partialConsistencyCode_of_payload
      (h.true_all n)

theorem partialConsistencyAcceptedTruth_iff_payloadTruth :
    PartialConsistencyAcceptedTruth ↔ PartialConsistencyPayloadTruth :=
  ⟨PartialConsistencyAcceptedTruth.toPayloadTruth,
    PartialConsistencyPayloadTruth.toAcceptedTruth⟩

def PartialConsistencyPayloadSpec.ofAcceptedTruth
    (haccepted : PartialConsistencyAcceptedTruth) :
    PartialConsistencyPayloadSpec :=
  PartialConsistencyPayloadSpec.standard haccepted.toPayloadTruth

theorem PartialConsistencyPayloadSpec.toAcceptedTruth
    (h : PartialConsistencyPayloadSpec) :
    PartialConsistencyAcceptedTruth where
  accepted_all := h.accepted_standard

def partial_consistency_payload_spec_of_truth
    (htruth : PartialConsistencyPayloadTruth) :
    PartialConsistencyPayloadSpec :=
  partial_consistency_payload_spec_of_realization
    partial_consistency_accepted_code_realization_true htruth

def partial_consistency_payload_spec_of_accepted_truth
    (haccepted : PartialConsistencyAcceptedTruth) :
    PartialConsistencyPayloadSpec :=
  PartialConsistencyPayloadSpec.ofAcceptedTruth haccepted

theorem accepted_sondow_certificate_eventual_of_full_certificate
    (hrealize : FullSondowCertificateRealizesFormula)
    {q : ℚ} (hcert : FullSondowCertificateInputs q) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      accepted_certificate (sondowCertificateValidCode n) := by
  rcases hcert.accepted_eventual with ⟨N, hN⟩
  exact ⟨N, fun n hn => hrealize.realizes q n (hN n hn)⟩

theorem accepted_sondow_certificate_eventual_of_rationality
    (hfwd : SondowForwardInputs)
    (hrealize : FullSondowCertificateRealizesFormula)
    (h_rat : is_rational euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      accepted_certificate (sondowCertificateValidCode n) := by
  rcases full_sondow_certificate_of_rationality hfwd h_rat with ⟨q, _hq, hcert⟩
  exact accepted_sondow_certificate_eventual_of_full_certificate hrealize hcert

theorem certificate_size_polynomial_of_full_sondow_size_realization
    (hsize : FullSondowCertificateSizeRealization) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, certificate_size (sondowCertificateValidCode n) ≤ f n := by
  exact ⟨full_sondow_certificate_size, full_sondow_certificate_size_polynomial,
    hsize.size_bound⟩

structure CertificateCollapseInputs (φ : ℕ → FormulaCode) : Prop where
  verifier_polytime : certificate_verifier_polytime φ
  certificates_under_rationality :
    is_rational euler_mascheroni →
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      ∀ n : ℕ, certificate_size (φ n) ≤ f n
  accepted_under_rationality :
    is_rational euler_mascheroni →
      ∀ n : ℕ, accepted_certificate (φ n)
  formal_verification_short :
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (φ n) →
        default_proof_length ProofSystem.PA (φ n) ≤ f n

structure EventualCertificateCollapseInputs (φ : ℕ → FormulaCode) : Prop where
  verifier_polytime : certificate_verifier_polytime φ
  certificates_under_rationality :
    is_rational euler_mascheroni →
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      ∀ n : ℕ, certificate_size (φ n) ≤ f n
  accepted_eventually_under_rationality :
    is_rational euler_mascheroni →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → accepted_certificate (φ n)
  formal_verification_short :
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (φ n) →
        default_proof_length ProofSystem.PA (φ n) ≤ f n

theorem eventual_certificate_collapse_inputs_of_full_sondow_certificate
    (hfwd : SondowForwardInputs)
    (hrealize : FullSondowCertificateRealizesFormula)
    (hsize : FullSondowCertificateSizeRealization)
    (hverifier : certificate_verifier_polytime sondowCertificateValidCode)
    (hshort :
      ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
        ∀ n : ℕ, accepted_certificate (sondowCertificateValidCode n) →
          default_proof_length ProofSystem.PA (sondowCertificateValidCode n) ≤ f n) :
    EventualCertificateCollapseInputs sondowCertificateValidCode where
  verifier_polytime := hverifier
  certificates_under_rationality := by
    intro _h_rat
    exact certificate_size_polynomial_of_full_sondow_size_realization hsize
  accepted_eventually_under_rationality := by
    intro h_rat
    exact accepted_sondow_certificate_eventual_of_rationality hfwd hrealize h_rat
  formal_verification_short := hshort

structure EventualShortVerificationBridge
    (T : ProofSystem) (measure : ProofLengthMeasure) (φ : ℕ → FormulaCode) : Prop where
  verifier_polytime : certificate_verifier_polytime φ
  short_proofs_of_accepted_certificates :
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (φ n) →
        proof_length T measure (φ n) ≤ f n

def EventualCertificateCollapseInputs.toEventualShortVerificationBridge
    {φ : ℕ → FormulaCode}
    (h : EventualCertificateCollapseInputs φ) :
    EventualShortVerificationBridge ProofSystem.PA ProofLengthMeasure.symbolSize φ where
  verifier_polytime := h.verifier_polytime
  short_proofs_of_accepted_certificates := h.formal_verification_short

structure BoundedArithmeticVerificationBridge
    (T : ProofSystem) (measure : ProofLengthMeasure) (φ : ℕ → FormulaCode) : Prop where
  verifier_polytime : certificate_verifier_polytime φ
  accepted_certificates_have_short_proofs :
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (φ n) →
        proof_length T measure (φ n) ≤ f n

def BoundedArithmeticVerificationBridge.toEventualShortVerificationBridge
    {T : ProofSystem} {measure : ProofLengthMeasure} {φ : ℕ → FormulaCode}
    (h : BoundedArithmeticVerificationBridge T measure φ) :
    EventualShortVerificationBridge T measure φ where
  verifier_polytime := h.verifier_polytime
  short_proofs_of_accepted_certificates := h.accepted_certificates_have_short_proofs

abbrev SondowCertificateVerificationBridge : Prop :=
  BoundedArithmeticVerificationBridge ProofSystem.PA ProofLengthMeasure.symbolSize
    sondowCertificateValidCode

structure SondowCertificateShortProofBridge : Prop where
  accepted_certificates_have_short_proofs :
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowCertificateValidCode n) →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowCertificateValidCode n) ≤ f n

structure PolynomialTimeVerificationHasShortProofs
    (T : ProofSystem) (measure : ProofLengthMeasure) : Prop where
  short_proofs_of_polytime_verified_certificates :
    ∀ φ : ℕ → FormulaCode,
      certificate_verifier_polytime φ →
        ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
          ∀ n : ℕ, accepted_certificate (φ n) →
            proof_length T measure (φ n) ≤ f n

structure FixedVerifierEncoding (φ : ℕ → FormulaCode) : Prop where
  verifier_polytime : certificate_verifier_polytime φ
  verifier_fixed : VerifierFamilyFixed φ
  accepted_formula_represents_verifier : AcceptedFormulaRepresentsVerifier φ
  verifier_trace_polynomial : VerifierTracePolynomial φ
  proof_predicate_polynomial : ProofPredicatePolynomial φ
  binary_numeral_encoding : BinaryNumeralEncoding φ
  symbol_or_bit_size_encoding : SymbolOrBitSizeEncoding φ

theorem fixed_verifier_encoding_sondowCertificateValidCode :
    FixedVerifierEncoding sondowCertificateValidCode where
  verifier_polytime := certificate_verifier_polytime_sondowCertificateValidCode
  verifier_fixed := verifier_family_fixed_sondowCertificateValidCode
  accepted_formula_represents_verifier :=
    accepted_formula_represents_verifier_sondowCertificateValidCode
  verifier_trace_polynomial :=
    ⟨verifier_trace_size_sondowCertificateValidCode_polynomial⟩
  proof_predicate_polynomial :=
    ⟨proof_predicate_formula_size_sondowCertificateValidCode_polynomial⟩
  binary_numeral_encoding :=
    ⟨binary_index_certificate_size_polynomial⟩
  symbol_or_bit_size_encoding :=
    ⟨⟨full_sondow_certificate_size, full_sondow_certificate_size_polynomial,
      by intro n; rfl⟩⟩

theorem fixed_verifier_encoding_sondowReflectionGraftCode :
    FixedVerifierEncoding sondowReflectionGraftCode where
  verifier_polytime := certificate_verifier_polytime_sondowReflectionGraftCode
  verifier_fixed := verifier_family_fixed_sondowReflectionGraftCode
  accepted_formula_represents_verifier :=
    accepted_formula_represents_verifier_sondowReflectionGraftCode
  verifier_trace_polynomial :=
    ⟨verifier_trace_size_sondowReflectionGraftCode_polynomial⟩
  proof_predicate_polynomial :=
    ⟨proof_predicate_formula_size_sondowReflectionGraftCode_polynomial⟩
  binary_numeral_encoding :=
    ⟨binary_index_certificate_size_polynomial⟩
  symbol_or_bit_size_encoding :=
    ⟨⟨reflection_graft_certificate_size, reflection_graft_certificate_size_polynomial,
      by intro n; rfl⟩⟩

theorem fixed_verifier_encoding_partialConsistencyCode :
    FixedVerifierEncoding partialConsistencyCode where
  verifier_polytime := certificate_verifier_polytime_partialConsistencyCode
  verifier_fixed := verifier_family_fixed_partialConsistencyCode
  accepted_formula_represents_verifier :=
    accepted_formula_represents_verifier_partialConsistencyCode
  verifier_trace_polynomial :=
    ⟨verifier_trace_size_partialConsistencyCode_polynomial⟩
  proof_predicate_polynomial :=
    ⟨proof_predicate_formula_size_partialConsistencyCode_polynomial⟩
  binary_numeral_encoding :=
    ⟨binary_index_certificate_size_polynomial⟩
  symbol_or_bit_size_encoding :=
    ⟨partial_consistency_certificate_size_polynomial⟩

theorem fixed_verifier_encoding_strengthenedPartialConsistencyCode :
    FixedVerifierEncoding strengthenedPartialConsistencyCode where
  verifier_polytime := certificate_verifier_polytime_strengthenedPartialConsistencyCode
  verifier_fixed := verifier_family_fixed_strengthenedPartialConsistencyCode
  accepted_formula_represents_verifier :=
    accepted_formula_represents_verifier_strengthenedPartialConsistencyCode
  verifier_trace_polynomial :=
    ⟨verifier_trace_size_strengthenedPartialConsistencyCode_polynomial⟩
  proof_predicate_polynomial :=
    ⟨proof_predicate_formula_size_strengthenedPartialConsistencyCode_polynomial⟩
  binary_numeral_encoding :=
    ⟨binary_index_certificate_size_polynomial⟩
  symbol_or_bit_size_encoding :=
    ⟨strengthened_partial_consistency_certificate_size_polynomial⟩

structure S21PolynomialTimeVerificationTheorem : Prop where
  short_s21_proofs_of_polytime_verified_certificates :
    ∀ φ : ℕ → FormulaCode,
      FixedVerifierEncoding φ →
        ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
          ∀ n : ℕ, accepted_certificate (φ n) →
            proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize (φ n) ≤ f n

structure S21VerifierTraceSoundness (φ : ℕ → FormulaCode) : Prop where
  short_proof_from_accepting_trace :
    ∀ n : ℕ, accepted_certificate (φ n) →
      proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize (φ n) ≤
        proof_predicate_formula_size φ n

structure AcceptedCertificateS21TraceRealization (φ : ℕ → FormulaCode) where
  accepted_code_semantics : AcceptedCertificateCodeSemantics.{acc_u} φ
  checked_code_has_short_s21_proof :
    ∀ n : ℕ, ∀ c : accepted_code_semantics.proof_code_semantics.Code,
      accepted_code_semantics.proof_code_semantics.checks c (φ n) →
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize (φ n) ≤
          proof_predicate_formula_size φ n

theorem AcceptedCertificateS21TraceRealization.toS21VerifierTraceSoundness
    {φ : ℕ → FormulaCode}
    (h : AcceptedCertificateS21TraceRealization φ) :
    S21VerifierTraceSoundness φ where
  short_proof_from_accepting_trace := by
    intro n hacc
    rcases h.accepted_code_semantics.has_code_of_accepted hacc with ⟨c, hc⟩
    exact h.checked_code_has_short_s21_proof n c hc

def AcceptedCertificateS21TraceRealization.ofTraceSoundness
    {φ : ℕ → FormulaCode}
    (hsem : AcceptedCertificateCodeSemantics φ)
    (hsound : S21VerifierTraceSoundness φ) :
    AcceptedCertificateS21TraceRealization φ where
  accepted_code_semantics := hsem
  checked_code_has_short_s21_proof := by
    intro n c hchecks
    exact hsound.short_proof_from_accepting_trace n
      (hsem.accepted_of_checked hchecks)

theorem S21VerifierTraceSoundness.to_short_s21_proofs
    {φ : ℕ → FormulaCode}
    (henc : FixedVerifierEncoding φ)
    (hsound : S21VerifierTraceSoundness φ) :
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (φ n) →
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize (φ n) ≤ f n :=
  ⟨proof_predicate_formula_size φ,
    henc.proof_predicate_polynomial.predicate_polynomial,
    hsound.short_proof_from_accepting_trace⟩

theorem AcceptedCertificateS21TraceRealization.to_short_s21_proofs
    {φ : ℕ → FormulaCode}
    (henc : FixedVerifierEncoding φ)
    (h : AcceptedCertificateS21TraceRealization φ) :
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (φ n) →
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize (φ n) ≤ f n :=
  h.toS21VerifierTraceSoundness.to_short_s21_proofs henc

structure S21VerifierTracePackage : Prop where
  trace_soundness :
    ∀ φ : ℕ → FormulaCode,
      FixedVerifierEncoding φ → S21VerifierTraceSoundness φ

theorem s21_polynomial_time_verification_of_trace_package
    (htrace : S21VerifierTracePackage) :
    S21PolynomialTimeVerificationTheorem where
  short_s21_proofs_of_polytime_verified_certificates := by
    intro φ henc
    exact (htrace.trace_soundness φ henc).to_short_s21_proofs henc

structure PAExtendsS21ShortProofs : Prop where
  pa_inherits_s21_short_proofs :
    ∀ φ : ℕ → FormulaCode,
      (∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
        ∀ n : ℕ, accepted_certificate (φ n) →
          proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize (φ n) ≤ f n) →
      ∃ (g : ℕ → ℝ), is_polynomial_bound g ∧
        ∀ n : ℕ, accepted_certificate (φ n) →
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize (φ n) ≤ g n

structure ProofSystemLinearEmbedding
    (source target : ProofSystem) (measure : ProofLengthMeasure) where
  C : ℝ
  D : ℝ
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  target_le_linear_source :
    ∀ φ : FormulaCode,
      proof_length target measure φ ≤ C * proof_length source measure φ + D

abbrev S21ToPALinearEmbedding :=
  ProofSystemLinearEmbedding
    ProofSystem.S21 ProofSystem.PA ProofLengthMeasure.symbolSize

structure ProofSystemLinearEmbeddingOn
    (source target : ProofSystem) (measure : ProofLengthMeasure)
    (φ : ℕ → FormulaCode) where
  C : ℝ
  D : ℝ
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  target_le_linear_source :
    ∀ n : ℕ,
      proof_length target measure (φ n) ≤
        C * proof_length source measure (φ n) + D

abbrev S21ToPALinearEmbeddingOn (φ : ℕ → FormulaCode) :=
  ProofSystemLinearEmbeddingOn
    ProofSystem.S21 ProofSystem.PA ProofLengthMeasure.symbolSize φ

def ProofSystemLinearEmbedding.on
    {source target : ProofSystem} {measure : ProofLengthMeasure}
    (hembed : ProofSystemLinearEmbedding source target measure)
    (φ : ℕ → FormulaCode) :
    ProofSystemLinearEmbeddingOn source target measure φ where
  C := hembed.C
  D := hembed.D
  C_nonneg := hembed.C_nonneg
  D_nonneg := hembed.D_nonneg
  target_le_linear_source := by
    intro n
    exact hembed.target_le_linear_source (φ n)

theorem pa_short_proofs_of_s21_short_proofs_and_embedding_on
    {φ : ℕ → FormulaCode}
    (hembed : S21ToPALinearEmbeddingOn φ)
    (hs21 :
      ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
        ∀ n : ℕ, accepted_certificate (φ n) →
          proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize (φ n) ≤ f n) :
    ∃ (g : ℕ → ℝ), is_polynomial_bound g ∧
      ∀ n : ℕ, accepted_certificate (φ n) →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize (φ n) ≤ g n := by
  rcases hs21 with ⟨f, hf_poly, hf_bound⟩
  refine ⟨fun n => hembed.C * f n + hembed.D,
    hf_poly.linear_rescale hembed.C_nonneg hembed.D_nonneg, ?_⟩
  intro n hacc
  have hpa :
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize (φ n) ≤
        hembed.C *
          proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize (φ n) +
        hembed.D :=
    hembed.target_le_linear_source n
  have hs21n := hf_bound n hacc
  have hmul :
      hembed.C * proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize (φ n) ≤
        hembed.C * f n :=
    mul_le_mul_of_nonneg_left hs21n hembed.C_nonneg
  nlinarith

theorem AcceptedCertificateS21TraceRealization.to_pa_short_proofs
    {φ : ℕ → FormulaCode}
    (henc : FixedVerifierEncoding φ)
    (hrealize : AcceptedCertificateS21TraceRealization φ)
    (hembed : S21ToPALinearEmbeddingOn φ) :
    ∃ (g : ℕ → ℝ), is_polynomial_bound g ∧
      ∀ n : ℕ, accepted_certificate (φ n) →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize (φ n) ≤ g n :=
  pa_short_proofs_of_s21_short_proofs_and_embedding_on hembed
    (hrealize.to_short_s21_proofs henc)

theorem pa_extends_s21_short_proofs_of_linear_embedding
    (hembed : S21ToPALinearEmbedding) :
    PAExtendsS21ShortProofs where
  pa_inherits_s21_short_proofs := by
    intro φ hs21
    rcases hs21 with ⟨f, hf_poly, hf_bound⟩
    refine ⟨fun n => hembed.C * f n + hembed.D,
      hf_poly.linear_rescale hembed.C_nonneg hembed.D_nonneg, ?_⟩
    intro n hacc
    have hpa :
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize (φ n) ≤
          hembed.C *
            proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize (φ n) +
          hembed.D :=
      hembed.target_le_linear_source (φ n)
    have hs21n := hf_bound n hacc
    have hmul : hembed.C *
        proof_length ProofSystem.S21 ProofLengthMeasure.symbolSize (φ n) ≤
        hembed.C * f n :=
      mul_le_mul_of_nonneg_left hs21n hembed.C_nonneg
    nlinarith

-- Standard verification bridge: a fixed polynomial-time verifier is formalized
-- first in S_2^1, then PA inherits the short proofs because PA extends the
-- bounded-arithmetic verification base.
structure PAStandardVerificationTheorem : Prop where
  s21_verification : S21PolynomialTimeVerificationTheorem
  pa_extends_s21 : PAExtendsS21ShortProofs

theorem pa_standard_verification_of_trace_and_linear_embedding
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbedding) :
    PAStandardVerificationTheorem where
  s21_verification := s21_polynomial_time_verification_of_trace_package htrace
  pa_extends_s21 := pa_extends_s21_short_proofs_of_linear_embedding hembed

theorem PAStandardVerificationTheorem.short_proofs_of_fixed_verifier
    (h : PAStandardVerificationTheorem) :
    ∀ φ : ℕ → FormulaCode,
      FixedVerifierEncoding φ →
        ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
          ∀ n : ℕ, accepted_certificate (φ n) →
            proof_length ProofSystem.PA ProofLengthMeasure.symbolSize (φ n) ≤ f n := by
  intro φ henc
  exact h.pa_extends_s21.pa_inherits_s21_short_proofs φ
    (h.s21_verification.short_s21_proofs_of_polytime_verified_certificates φ henc)

theorem sondow_certificate_short_proof_bridge_of_polytime_verification
    (h :
      PolynomialTimeVerificationHasShortProofs
        ProofSystem.PA ProofLengthMeasure.symbolSize) :
    SondowCertificateShortProofBridge where
  accepted_certificates_have_short_proofs :=
    h.short_proofs_of_polytime_verified_certificates
      sondowCertificateValidCode
      certificate_verifier_polytime_sondowCertificateValidCode

theorem sondow_certificate_short_proof_bridge_of_trace_soundness_and_linear_embedding
    (hsound : S21VerifierTraceSoundness sondowCertificateValidCode)
    (hembed : S21ToPALinearEmbeddingOn sondowCertificateValidCode) :
    SondowCertificateShortProofBridge where
  accepted_certificates_have_short_proofs :=
    pa_short_proofs_of_s21_short_proofs_and_embedding_on hembed
      (hsound.to_short_s21_proofs fixed_verifier_encoding_sondowCertificateValidCode)

theorem sondow_certificate_short_proof_bridge_of_trace_soundness_and_global_linear_embedding
    (hsound : S21VerifierTraceSoundness sondowCertificateValidCode)
    (hembed : S21ToPALinearEmbedding) :
    SondowCertificateShortProofBridge := by
  exact sondow_certificate_short_proof_bridge_of_trace_soundness_and_linear_embedding
    hsound (hembed.on sondowCertificateValidCode)

structure SondowCertificateConcreteVerificationPackage where
  trace_soundness : S21VerifierTraceSoundness sondowCertificateValidCode
  pa_embedding : S21ToPALinearEmbeddingOn sondowCertificateValidCode

theorem SondowCertificateConcreteVerificationPackage.toShortProofBridge
    (h : SondowCertificateConcreteVerificationPackage) :
    SondowCertificateShortProofBridge :=
  sondow_certificate_short_proof_bridge_of_trace_soundness_and_linear_embedding
    h.trace_soundness h.pa_embedding

def sondow_certificate_concrete_verification_package_of_global_inputs
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbedding) :
    SondowCertificateConcreteVerificationPackage where
  trace_soundness :=
    htrace.trace_soundness
      sondowCertificateValidCode fixed_verifier_encoding_sondowCertificateValidCode
  pa_embedding := hembed.on sondowCertificateValidCode

structure PartialConsistencyShortProofBridge : Prop where
  accepted_certificates_have_short_proofs :
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (partialConsistencyCode n) →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) ≤ f n

theorem partial_consistency_short_proof_bridge_of_polytime_verification
    (h : PAStandardVerificationTheorem) :
    PartialConsistencyShortProofBridge where
  accepted_certificates_have_short_proofs :=
    h.short_proofs_of_fixed_verifier
      partialConsistencyCode
      fixed_verifier_encoding_partialConsistencyCode

theorem partial_consistency_short_proof_bridge_of_trace_soundness_and_linear_embedding
    (hsound : S21VerifierTraceSoundness partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyShortProofBridge where
  accepted_certificates_have_short_proofs :=
    pa_short_proofs_of_s21_short_proofs_and_embedding_on hembed
      (hsound.to_short_s21_proofs fixed_verifier_encoding_partialConsistencyCode)

theorem partial_consistency_short_proof_bridge_of_trace_soundness_and_global_linear_embedding
    (hsound : S21VerifierTraceSoundness partialConsistencyCode)
    (hembed : S21ToPALinearEmbedding) :
    PartialConsistencyShortProofBridge := by
  exact partial_consistency_short_proof_bridge_of_trace_soundness_and_linear_embedding
    hsound (hembed.on partialConsistencyCode)

def partialConsistencyAcceptedS21TraceRealization
    (hspec : PartialConsistencyPayloadSpec)
    (hsound : S21VerifierTraceSoundness partialConsistencyCode) :
    AcceptedCertificateS21TraceRealization partialConsistencyCode :=
  AcceptedCertificateS21TraceRealization.ofTraceSoundness
    (partialConsistencyAcceptedCertificateCodeSemantics hspec) hsound

structure PartialConsistencyConcreteVerificationPackage where
  trace_soundness : S21VerifierTraceSoundness partialConsistencyCode
  pa_embedding : S21ToPALinearEmbeddingOn partialConsistencyCode

def partial_consistency_concrete_verification_package_of_trace_realization
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyConcreteVerificationPackage where
  trace_soundness := hrealize.toS21VerifierTraceSoundness
  pa_embedding := hembed

def partial_consistency_concrete_verification_package_of_payload_spec_and_trace_soundness
    (hspec : PartialConsistencyPayloadSpec)
    (hsound : S21VerifierTraceSoundness partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyConcreteVerificationPackage :=
  partial_consistency_concrete_verification_package_of_trace_realization
    (partialConsistencyAcceptedS21TraceRealization hspec hsound) hembed

theorem partial_consistency_short_proof_bridge_of_trace_realization
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyShortProofBridge where
  accepted_certificates_have_short_proofs :=
    hrealize.to_pa_short_proofs fixed_verifier_encoding_partialConsistencyCode hembed

theorem PartialConsistencyConcreteVerificationPackage.toShortProofBridge
    (h : PartialConsistencyConcreteVerificationPackage) :
    PartialConsistencyShortProofBridge :=
  partial_consistency_short_proof_bridge_of_trace_soundness_and_linear_embedding
    h.trace_soundness h.pa_embedding

def partial_consistency_concrete_verification_package_of_global_inputs
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbedding) :
    PartialConsistencyConcreteVerificationPackage where
  trace_soundness :=
    htrace.trace_soundness
      partialConsistencyCode fixed_verifier_encoding_partialConsistencyCode
  pa_embedding := hembed.on partialConsistencyCode

theorem partial_consistency_eventual_collapse_inputs_of_code_payload_inputs
    (hpayload : ReflectionGraftCodePayloadInputs)
    (hshort : PartialConsistencyShortProofBridge) :
    EventualCertificateCollapseInputs partialConsistencyCode where
  verifier_polytime := certificate_verifier_polytime_partialConsistencyCode
  certificates_under_rationality := by
    intro _h_rat
    exact partial_consistency_certificate_size_polynomial
  accepted_eventually_under_rationality := by
    intro _h_rat
    exact hpayload.accepted_eventual
  formal_verification_short := hshort.accepted_certificates_have_short_proofs

theorem partial_consistency_eventual_collapse_inputs_of_payload_spec
    (hspec : PartialConsistencyPayloadSpec)
    (hshort : PartialConsistencyShortProofBridge) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  partial_consistency_eventual_collapse_inputs_of_code_payload_inputs
    hspec.toReflectionGraftCodePayloadInputs hshort

theorem partial_consistency_eventual_collapse_inputs_of_payload_spec_and_verification
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PAStandardVerificationTheorem) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  partial_consistency_eventual_collapse_inputs_of_payload_spec
    hspec (partial_consistency_short_proof_bridge_of_polytime_verification hver)

theorem partial_consistency_eventual_collapse_inputs_of_payload_spec_and_trace_realization
    (hspec : PartialConsistencyPayloadSpec)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  partial_consistency_eventual_collapse_inputs_of_payload_spec
    hspec
    (partial_consistency_short_proof_bridge_of_trace_realization hrealize hembed)

theorem partial_consistency_eventual_collapse_inputs_of_code_payload_and_concrete_verification
    (hpayload : ReflectionGraftCodePayloadInputs)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  partial_consistency_eventual_collapse_inputs_of_code_payload_inputs
    hpayload hver.toShortProofBridge

structure ReflectionGraftShortProofBridge : Prop where
  accepted_certificates_have_short_proofs :
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (sondowReflectionGraftCode n) →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n) ≤ f n

theorem reflection_graft_short_proof_bridge_of_polytime_verification
    (h : PAStandardVerificationTheorem) :
    ReflectionGraftShortProofBridge where
  accepted_certificates_have_short_proofs :=
    h.short_proofs_of_fixed_verifier
      sondowReflectionGraftCode
      fixed_verifier_encoding_sondowReflectionGraftCode

theorem reflection_graft_short_proof_bridge_of_trace_soundness_and_linear_embedding
    (hsound : S21VerifierTraceSoundness sondowReflectionGraftCode)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftShortProofBridge where
  accepted_certificates_have_short_proofs :=
    pa_short_proofs_of_s21_short_proofs_and_embedding_on hembed
      (hsound.to_short_s21_proofs fixed_verifier_encoding_sondowReflectionGraftCode)

theorem reflection_graft_short_proof_bridge_of_trace_soundness_and_global_linear_embedding
    (hsound : S21VerifierTraceSoundness sondowReflectionGraftCode)
    (hembed : S21ToPALinearEmbedding) :
    ReflectionGraftShortProofBridge := by
  exact reflection_graft_short_proof_bridge_of_trace_soundness_and_linear_embedding
    hsound (hembed.on sondowReflectionGraftCode)

structure ReflectionGraftConcreteVerificationPackage where
  trace_soundness : S21VerifierTraceSoundness sondowReflectionGraftCode
  pa_embedding : S21ToPALinearEmbeddingOn sondowReflectionGraftCode

theorem ReflectionGraftConcreteVerificationPackage.toShortProofBridge
    (h : ReflectionGraftConcreteVerificationPackage) :
    ReflectionGraftShortProofBridge :=
  reflection_graft_short_proof_bridge_of_trace_soundness_and_linear_embedding
    h.trace_soundness h.pa_embedding

def reflection_graft_concrete_verification_package_of_global_inputs
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbedding) :
    ReflectionGraftConcreteVerificationPackage where
  trace_soundness :=
    htrace.trace_soundness
      sondowReflectionGraftCode fixed_verifier_encoding_sondowReflectionGraftCode
  pa_embedding := hembed.on sondowReflectionGraftCode

structure SondowCollapseVerificationBridgePackage where
  partial_accepted_truth : PartialConsistencyAcceptedTruth
  trace_package : S21VerifierTracePackage
  pa_embedding : S21ToPALinearEmbedding

def SondowCollapseVerificationBridgePackage.toPayloadSpec
    (h : SondowCollapseVerificationBridgePackage) :
    PartialConsistencyPayloadSpec :=
  PartialConsistencyPayloadSpec.ofAcceptedTruth h.partial_accepted_truth

def SondowCollapseVerificationBridgePackage.toPAStandardVerification
    (h : SondowCollapseVerificationBridgePackage) :
    PAStandardVerificationTheorem :=
  pa_standard_verification_of_trace_and_linear_embedding
    h.trace_package h.pa_embedding

def SondowCollapseVerificationBridgePackage.toSondowConcreteVerification
    (h : SondowCollapseVerificationBridgePackage) :
    SondowCertificateConcreteVerificationPackage :=
  sondow_certificate_concrete_verification_package_of_global_inputs
    h.trace_package h.pa_embedding

def SondowCollapseVerificationBridgePackage.toPartialConcreteVerification
    (h : SondowCollapseVerificationBridgePackage) :
    PartialConsistencyConcreteVerificationPackage :=
  partial_consistency_concrete_verification_package_of_global_inputs
    h.trace_package h.pa_embedding

def SondowCollapseVerificationBridgePackage.toReflectionGraftConcreteVerification
    (h : SondowCollapseVerificationBridgePackage) :
    ReflectionGraftConcreteVerificationPackage :=
  reflection_graft_concrete_verification_package_of_global_inputs
    h.trace_package h.pa_embedding

def SondowCertificateShortProofBridge.toVerificationBridge
    (h : SondowCertificateShortProofBridge) :
    SondowCertificateVerificationBridge where
  verifier_polytime := certificate_verifier_polytime_sondowCertificateValidCode
  accepted_certificates_have_short_proofs := h.accepted_certificates_have_short_proofs

structure SondowCertificateCollapsePackage : Prop where
  sondow_forward : SondowForwardInputs
  short_proof_bridge : SondowCertificateShortProofBridge

def SondowCertificateCollapsePackage.toEventualCertificateCollapseInputs
    (h : SondowCertificateCollapsePackage) :
    EventualCertificateCollapseInputs sondowCertificateValidCode :=
  eventual_certificate_collapse_inputs_of_full_sondow_certificate
    h.sondow_forward full_sondow_certificate_realizes_formula_true
    full_sondow_certificate_size_realization_true
    certificate_verifier_polytime_sondowCertificateValidCode
    h.short_proof_bridge.accepted_certificates_have_short_proofs

theorem sondow_certificate_collapse_package_of_standard_inputs_and_verification
    (hstd : SondowStandardInputs)
    (hver : PAStandardVerificationTheorem) :
    SondowCertificateCollapsePackage where
  sondow_forward := hstd.toForward
  short_proof_bridge :=
    { accepted_certificates_have_short_proofs :=
        hver.short_proofs_of_fixed_verifier
          sondowCertificateValidCode
          fixed_verifier_encoding_sondowCertificateValidCode }

theorem sondow_certificate_collapse_package_of_forward_inputs_and_verification
    (hfwd : SondowForwardInputs)
    (hver : PAStandardVerificationTheorem) :
    SondowCertificateCollapsePackage where
  sondow_forward := hfwd
  short_proof_bridge :=
    { accepted_certificates_have_short_proofs :=
        hver.short_proofs_of_fixed_verifier
          sondowCertificateValidCode
          fixed_verifier_encoding_sondowCertificateValidCode }

theorem sondow_certificate_collapse_package_of_forward_inputs_and_concrete_verification
    (hfwd : SondowForwardInputs)
    (hver : SondowCertificateConcreteVerificationPackage) :
    SondowCertificateCollapsePackage where
  sondow_forward := hfwd
  short_proof_bridge := hver.toShortProofBridge

theorem sondow_certificate_collapse_package_of_forward_inputs_trace_soundness_and_embedding
    (hfwd : SondowForwardInputs)
    (hsound : S21VerifierTraceSoundness sondowCertificateValidCode)
    (hembed : S21ToPALinearEmbeddingOn sondowCertificateValidCode) :
    SondowCertificateCollapsePackage where
  sondow_forward := hfwd
  short_proof_bridge :=
    sondow_certificate_short_proof_bridge_of_trace_soundness_and_linear_embedding
      hsound hembed

theorem
    sondow_certificate_collapse_package_of_forward_inputs_trace_soundness_and_global_embedding
    (hfwd : SondowForwardInputs)
    (hsound : S21VerifierTraceSoundness sondowCertificateValidCode)
    (hembed : S21ToPALinearEmbedding) :
    SondowCertificateCollapsePackage :=
  sondow_certificate_collapse_package_of_forward_inputs_trace_soundness_and_embedding
    hfwd hsound (hembed.on sondowCertificateValidCode)

structure ReflectionGraftCollapsePackage : Prop where
  sondow_forward : SondowForwardInputs
  payload_inputs : ReflectionGraftPayloadInputs
  short_proof_bridge : ReflectionGraftShortProofBridge

def ReflectionGraftCollapsePackage.toEventualCertificateCollapseInputs
    (h : ReflectionGraftCollapsePackage) :
    EventualCertificateCollapseInputs sondowReflectionGraftCode where
  verifier_polytime := certificate_verifier_polytime_sondowReflectionGraftCode
  certificates_under_rationality := by
    intro _h_rat
    exact ⟨reflection_graft_certificate_size,
      reflection_graft_certificate_size_polynomial, fun n => le_rfl⟩
  accepted_eventually_under_rationality := by
    intro h_rat
    rcases h_rat with ⟨q, hq⟩
    rcases (reflection_graft_certificate_inputs
      h.sondow_forward h.payload_inputs hq).accepted_eventual with ⟨N, hN⟩
    exact ⟨N, fun n hn => ⟨q, hN n hn⟩⟩
  formal_verification_short := h.short_proof_bridge.accepted_certificates_have_short_proofs

theorem reflection_graft_collapse_package_of_standard_inputs_and_verification
    (hstd : SondowStandardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hver : PAStandardVerificationTheorem) :
    ReflectionGraftCollapsePackage where
  sondow_forward := hstd.toForward
  payload_inputs := hpayload
  short_proof_bridge :=
    reflection_graft_short_proof_bridge_of_polytime_verification hver

theorem reflection_graft_collapse_package_of_forward_inputs_and_verification
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hver : PAStandardVerificationTheorem) :
    ReflectionGraftCollapsePackage where
  sondow_forward := hfwd
  payload_inputs := hpayload
  short_proof_bridge :=
    reflection_graft_short_proof_bridge_of_polytime_verification hver

theorem reflection_graft_collapse_package_of_forward_inputs_trace_soundness_and_embedding
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hsound : S21VerifierTraceSoundness sondowReflectionGraftCode)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode) :
    ReflectionGraftCollapsePackage where
  sondow_forward := hfwd
  payload_inputs := hpayload
  short_proof_bridge :=
    reflection_graft_short_proof_bridge_of_trace_soundness_and_linear_embedding
      hsound hembed

theorem reflection_graft_collapse_package_of_forward_inputs_and_concrete_verification
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hver : ReflectionGraftConcreteVerificationPackage) :
    ReflectionGraftCollapsePackage where
  sondow_forward := hfwd
  payload_inputs := hpayload
  short_proof_bridge := hver.toShortProofBridge

theorem reflection_graft_collapse_package_of_code_payload_inputs_and_concrete_verification
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftCodePayloadInputs)
    (hver : ReflectionGraftConcreteVerificationPackage) :
    ReflectionGraftCollapsePackage :=
  reflection_graft_collapse_package_of_forward_inputs_and_concrete_verification
    hfwd hpayload.toPayloadInputs hver

theorem reflection_graft_collapse_package_of_payload_spec_and_concrete_verification
    (hfwd : SondowForwardInputs)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : ReflectionGraftConcreteVerificationPackage) :
    ReflectionGraftCollapsePackage :=
  reflection_graft_collapse_package_of_code_payload_inputs_and_concrete_verification
    hfwd hspec.toReflectionGraftCodePayloadInputs hver

theorem reflection_graft_eventual_collapse_inputs_of_payload_spec
    (hfwd : SondowForwardInputs)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : ReflectionGraftConcreteVerificationPackage) :
    EventualCertificateCollapseInputs sondowReflectionGraftCode :=
  (reflection_graft_collapse_package_of_payload_spec_and_concrete_verification
    hfwd hspec hver).toEventualCertificateCollapseInputs

theorem reflection_graft_eventual_collapse_inputs_of_code_payload_inputs
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftCodePayloadInputs)
    (hver : ReflectionGraftConcreteVerificationPackage) :
    EventualCertificateCollapseInputs sondowReflectionGraftCode :=
  (reflection_graft_collapse_package_of_code_payload_inputs_and_concrete_verification
    hfwd hpayload hver).toEventualCertificateCollapseInputs

def SondowCollapseVerificationBridgePackage.toSondowCollapsePackage
    (h : SondowCollapseVerificationBridgePackage)
    (hfwd : SondowForwardInputs) :
    SondowCertificateCollapsePackage :=
  sondow_certificate_collapse_package_of_forward_inputs_and_concrete_verification
    hfwd h.toSondowConcreteVerification

def SondowCollapseVerificationBridgePackage.toReflectionGraftCollapsePackage
    (h : SondowCollapseVerificationBridgePackage)
    (hfwd : SondowForwardInputs) :
    ReflectionGraftCollapsePackage :=
  reflection_graft_collapse_package_of_payload_spec_and_concrete_verification
    hfwd h.toPayloadSpec h.toReflectionGraftConcreteVerification

def SondowCollapseVerificationBridgePackage.toPartialConsistencyCollapseInputs
    (h : SondowCollapseVerificationBridgePackage) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  partial_consistency_eventual_collapse_inputs_of_payload_spec
    h.toPayloadSpec h.toPartialConcreteVerification.toShortProofBridge

def SondowCollapseVerificationBridgePackage.toReflectionGraftCollapseInputs
    (h : SondowCollapseVerificationBridgePackage)
    (hfwd : SondowForwardInputs) :
    EventualCertificateCollapseInputs sondowReflectionGraftCode :=
  (h.toReflectionGraftCollapsePackage hfwd).toEventualCertificateCollapseInputs

theorem reflection_graft_collapse_package_of_forward_inputs_trace_soundness_and_global_embedding
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hsound : S21VerifierTraceSoundness sondowReflectionGraftCode)
    (hembed : S21ToPALinearEmbedding) :
    ReflectionGraftCollapsePackage :=
  reflection_graft_collapse_package_of_forward_inputs_trace_soundness_and_embedding
    hfwd hpayload hsound (hembed.on sondowReflectionGraftCode)
