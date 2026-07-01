/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.PartialConsistency
import EulerLimit.MiniHilbert
/-!
# Gödel-Sondow Coupling Hypothesis Formalization
This module formalizes the Euler-Mascheroni constant limit definition,
proof-complexity and projection-bridge layers.
-/

open Filter
structure EventualNaturalSondowConditionalInputs
    (T : ProofSystem) (measure : ProofLengthMeasure) (φ : ℕ → FormulaCode) : Prop where
  certificate_collapse : EventualCertificateCollapseInputs φ
  short_verification : EventualShortVerificationBridge T measure φ
  natural_lower_bound : EventualLowerBound T measure φ

structure EventualReflectionGraftModelInputs
    (T : ProofSystem) (measure : ProofLengthMeasure) (φ : ℕ → FormulaCode) : Prop where
  certificate_collapse : EventualCertificateCollapseInputs φ
  short_verification : EventualShortVerificationBridge T measure φ
  graft_lower_bound : EventualLowerBound T measure φ

structure EventualPartialConsistencyModelInputs
    (T : ProofSystem) (measure : ProofLengthMeasure) (φ : ℕ → FormulaCode) : Prop where
  certificate_collapse : EventualCertificateCollapseInputs φ
  short_verification : EventualShortVerificationBridge T measure φ
  source_lower_bound : EventualLowerBound T measure φ

structure EventualSemanticShortVerificationBridge
    (length : FormulaCode → ℕ) (φ : ℕ → FormulaCode) : Prop where
  verifier_polytime : certificate_verifier_polytime φ
  short_proofs_of_accepted_certificates :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (φ n) → (length (φ n) : ℝ) ≤ f n

structure EventualSemanticLowerBound
    (length : FormulaCode → ℕ) (φ : ℕ → FormulaCode) : Prop where
  lower_bound :
    ∀ f : ℕ → ℝ, is_polynomial_bound f →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (length (φ n) : ℝ) > f n

structure EventualSemanticReflectionGraftModelInputs
    (length : FormulaCode → ℕ) (φ : ℕ → FormulaCode) : Prop where
  certificate_collapse : EventualCertificateCollapseInputs φ
  short_verification : EventualSemanticShortVerificationBridge length φ
  graft_lower_bound : EventualSemanticLowerBound length φ

theorem eventual_natural_sondow_inputs_of_bridges
    (hcollapse : EventualCertificateCollapseInputs sondowCertificateValidCode)
    (hverify : SondowCertificateVerificationBridge)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowCertificateValidCode) :
    EventualNaturalSondowConditionalInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowCertificateValidCode where
  certificate_collapse := hcollapse
  short_verification := hverify.toEventualShortVerificationBridge
  natural_lower_bound := hlower

theorem eventual_reflection_graft_inputs_of_collapse_package
    (hcollapse : ReflectionGraftCollapsePackage)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowReflectionGraftCode) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode where
  certificate_collapse := hcollapse.toEventualCertificateCollapseInputs
  short_verification := {
    verifier_polytime := certificate_verifier_polytime_sondowReflectionGraftCode
    short_proofs_of_accepted_certificates :=
      hcollapse.short_proof_bridge.accepted_certificates_have_short_proofs }
  graft_lower_bound := hlower

theorem eventual_partial_consistency_inputs_of_collapse_and_lower_bound
    (hcollapse : EventualCertificateCollapseInputs partialConsistencyCode)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        partialConsistencyCode) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode where
  certificate_collapse := hcollapse
  short_verification := hcollapse.toEventualShortVerificationBridge
  source_lower_bound := hlower

theorem eventual_partial_consistency_inputs_of_spec_package
    (h : PartialConsistencySpecExternalPackage)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  eventual_partial_consistency_inputs_of_collapse_and_lower_bound
    (h.toEventualPartialConsistencyCollapseInputs hver)
    (partial_consistency_eventual_lower_bound_of_strong h.strong_lower_bound)

theorem eventual_partial_consistency_inputs_of_spec_package_and_verification
    (h : PartialConsistencySpecExternalPackage)
    (hver : PAStandardVerificationTheorem) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  eventual_partial_consistency_inputs_of_collapse_and_lower_bound
    (h.toEventualPartialConsistencyCollapseInputs' hver)
    (partial_consistency_eventual_lower_bound_of_strong h.strong_lower_bound)

theorem eventual_partial_consistency_inputs_of_spec_package_and_trace
    (h : PartialConsistencySpecExternalPackage)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  eventual_partial_consistency_inputs_of_collapse_and_lower_bound
    (h.toEventualPartialConsistencyCollapseInputsOfTrace hrealize hembed)
    (partial_consistency_eventual_lower_bound_of_strong h.strong_lower_bound)

structure ShortVerificationBridge (T : ProofSystem) (measure : ProofLengthMeasure)
    (φ : ℕ → FormulaCode) : Prop where
  verifier_polytime : certificate_verifier_polytime φ
  short_proofs_of_accepted_certificates :
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      ∀ n : ℕ, accepted_certificate (φ n) →
        proof_length T measure (φ n) ≤ f n

structure NaturalSondowLowerBound (T : ProofSystem) (measure : ProofLengthMeasure)
    (φ : ℕ → FormulaCode) : Prop where
  lower_bound :
    ∀ f : ℕ → ℝ, is_polynomial_bound f →
      ∃ n : ℕ, proof_length T measure (φ n) > f n

structure ReflectionGraftLowerBound (T : ProofSystem) (measure : ProofLengthMeasure)
    (φ : ℕ → FormulaCode) : Prop where
  lower_bound :
    ∀ f : ℕ → ℝ, is_polynomial_bound f →
      ∃ n : ℕ, proof_length T measure (φ n) > f n

structure NaturalSondowConditionalInputs (T : ProofSystem) (measure : ProofLengthMeasure)
    (φ : ℕ → FormulaCode) : Prop where
  certificate_collapse : CertificateCollapseInputs φ
  short_verification : ShortVerificationBridge T measure φ
  natural_lower_bound : NaturalSondowLowerBound T measure φ

structure ReflectionGraftModelInputs (T : ProofSystem) (measure : ProofLengthMeasure)
    (φ : ℕ → FormulaCode) : Prop where
  certificate_collapse : CertificateCollapseInputs φ
  short_verification : ShortVerificationBridge T measure φ
  graft_lower_bound : ReflectionGraftLowerBound T measure φ

abbrev NaturalSondowMainInputs : Prop :=
  NaturalSondowConditionalInputs ProofSystem.PA ProofLengthMeasure.symbolSize
    sondowCertificateValidCode

abbrev ReflectionGraftMainInputs : Prop :=
  ReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
    sondowReflectionGraftCode

structure ProofComplexityComparisonInputs
    (weak strong : ProofSystem) (measure : ProofLengthMeasure)
    (φ : ℕ → FormulaCode) : Prop where
  strong_collapse_under_rationality :
    is_rational euler_mascheroni →
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      (∀ n : ℕ, proof_length strong measure (φ n) ≤ f n)
  weak_lower_bound :
    ∀ f : ℕ → ℝ, is_polynomial_bound f →
      ∃ n : ℕ, proof_length weak measure (φ n) > f n
  transfer_to_weak :
    ∀ f : ℕ → ℝ,
      (∀ n : ℕ, proof_length strong measure (φ n) ≤ f n) →
      ∃ g : ℕ → ℝ, is_polynomial_bound g ∧
        ∀ n : ℕ, proof_length weak measure (φ n) ≤ g n

structure ProofComplexityInputs : Prop where
  collapse_under_rationality :
    is_rational euler_mascheroni →
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      (∀ n : ℕ, default_proof_length ProofSystem.PA (sondowIdentityCode n) ≤ f n)
  lower_bound :
    ∀ f : ℕ → ℝ, is_polynomial_bound f →
      ∃ n : ℕ, default_proof_length ProofSystem.PA (sondowIdentityCode n) > f n

structure ProofComplexityInputsFor (φ : ℕ → FormulaCode) : Prop where
  collapse_under_rationality :
    is_rational euler_mascheroni →
    ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
      (∀ n : ℕ, default_proof_length ProofSystem.PA (φ n) ≤ f n)
  lower_bound :
    ∀ f : ℕ → ℝ, is_polynomial_bound f →
      ∃ n : ℕ, default_proof_length ProofSystem.PA (φ n) > f n

def ProofComplexityInputs.toFor
    (hpc : ProofComplexityInputs) :
    ProofComplexityInputsFor sondowIdentityCode where
  collapse_under_rationality := hpc.collapse_under_rationality
  lower_bound := hpc.lower_bound

def ProofComplexityInputs.ofFor
    (hpc : ProofComplexityInputsFor sondowIdentityCode) :
    ProofComplexityInputs where
  collapse_under_rationality := hpc.collapse_under_rationality
  lower_bound := hpc.lower_bound


-- ==========================================================================
-- 6. GÖDEL-SONDOW COUPLING HYPOTHESIS AND SPEED-UP COLLAPSE THEOREMS
-- ==========================================================================

-- Legacy summary axiom for the original Sondow-identity route.  Newer routes
-- should pass explicit verification/collapse packages instead of citing this
-- bundled assumption: it is not an internal proof of the Sondow collapse.
axiom proof_length_collapse_under_rationality :
  is_rational euler_mascheroni →
  ∃ (f : ℕ → ℝ), is_polynomial_bound f ∧
    (∀ n : ℕ, default_proof_length ProofSystem.PA (sondowIdentityCode n) ≤ f n)

-- Legacy summary axiom for the original natural Sondow-identity lower-bound
-- route.  It is intentionally not used as evidence for the Pudlak finite-
-- consistency route; modern endpoints should import a concrete lower-bound
-- certificate for the chosen formula family.
axiom proof_complexity_lower_bound :
  ∀ f : ℕ → ℝ, is_polynomial_bound f →
    ∃ n : ℕ, default_proof_length ProofSystem.PA (sondowIdentityCode n) > f n

-- Legacy aggregate input package.  Prefer explicit route-specific packages in
-- new statements, so the remaining external assumptions are visible at the
-- theorem boundary.
def proof_complexity_inputs_from_axioms : ProofComplexityInputs where
  collapse_under_rationality := proof_length_collapse_under_rationality
  lower_bound := proof_complexity_lower_bound

theorem godel_sondow_coupling_hypothesis_of_proof_complexity
    (hpc : ProofComplexityInputs) :
    ¬ (is_rational euler_mascheroni) := by
  intro h_rat
  have ⟨f, h_poly, h_le⟩ := hpc.collapse_under_rationality h_rat
  have ⟨n, h_gt⟩ := hpc.lower_bound f h_poly
  have h_le_n := h_le n
  linarith

theorem irrational_of_proof_complexity_inputs_for
    {φ : ℕ → FormulaCode}
    (hpc : ProofComplexityInputsFor φ) :
    ¬ (is_rational euler_mascheroni) := by
  intro h_rat
  have ⟨f, h_poly, h_le⟩ := hpc.collapse_under_rationality h_rat
  have ⟨n, h_gt⟩ := hpc.lower_bound f h_poly
  have h_le_n := h_le n
  linarith

theorem irrational_of_proof_complexity_comparison_inputs
    {weak strong : ProofSystem} {measure : ProofLengthMeasure}
    {φ : ℕ → FormulaCode}
    (hpc : ProofComplexityComparisonInputs weak strong measure φ) :
    ¬ (is_rational euler_mascheroni) := by
  intro h_rat
  have ⟨f, _h_poly_f, h_strong_le⟩ := hpc.strong_collapse_under_rationality h_rat
  have ⟨g, h_poly_g, h_weak_le⟩ := hpc.transfer_to_weak f h_strong_le
  have ⟨n, h_gt⟩ := hpc.weak_lower_bound g h_poly_g
  have h_le_n := h_weak_le n
  linarith

theorem irrational_of_natural_sondow_conditional_inputs
    {T : ProofSystem} {measure : ProofLengthMeasure} {φ : ℕ → FormulaCode}
    (h : NaturalSondowConditionalInputs T measure φ) :
    ¬ (is_rational euler_mascheroni) := by
  intro h_rat
  have h_accept : ∀ n : ℕ, accepted_certificate (φ n) :=
    h.certificate_collapse.accepted_under_rationality h_rat
  have ⟨f, h_poly, h_short⟩ := h.short_verification.short_proofs_of_accepted_certificates
  have ⟨n, h_gt⟩ := h.natural_lower_bound.lower_bound f h_poly
  have h_le_n := h_short n (h_accept n)
  linarith

theorem irrational_of_reflection_graft_model_inputs
    {T : ProofSystem} {measure : ProofLengthMeasure} {φ : ℕ → FormulaCode}
    (h : ReflectionGraftModelInputs T measure φ) :
    ¬ (is_rational euler_mascheroni) := by
  intro h_rat
  have h_accept : ∀ n : ℕ, accepted_certificate (φ n) :=
    h.certificate_collapse.accepted_under_rationality h_rat
  have ⟨f, h_poly, h_short⟩ := h.short_verification.short_proofs_of_accepted_certificates
  have ⟨n, h_gt⟩ := h.graft_lower_bound.lower_bound f h_poly
  have h_le_n := h_short n (h_accept n)
  linarith

theorem eventual_certificate_collision
    {T : ProofSystem} {measure : ProofLengthMeasure} {φ : ℕ → FormulaCode}
    (accepted_eventually_under_rationality :
      is_rational euler_mascheroni →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → accepted_certificate (φ n))
    (short_proofs_of_accepted_certificates :
      ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
        ∀ n : ℕ, accepted_certificate (φ n) →
          proof_length T measure (φ n) ≤ f n)
    (lower_bound : EventualLowerBound T measure φ) :
    ¬ (is_rational euler_mascheroni) := by
  intro h_rat
  rcases accepted_eventually_under_rationality h_rat with ⟨N, h_accept⟩
  rcases short_proofs_of_accepted_certificates with ⟨f, h_poly, h_short⟩
  rcases lower_bound.lower_bound f h_poly N with ⟨n, hn_ge, h_gt⟩
  have h_le_n := h_short n (h_accept n hn_ge)
  linarith

theorem eventual_certificate_collision_of_inputs
    {T : ProofSystem} {measure : ProofLengthMeasure} {φ : ℕ → FormulaCode}
    (hcollapse : EventualCertificateCollapseInputs φ)
    (hverify : EventualShortVerificationBridge T measure φ)
    (hlower : EventualLowerBound T measure φ) :
    ¬ (is_rational euler_mascheroni) :=
  eventual_certificate_collision
    hcollapse.accepted_eventually_under_rationality
    hverify.short_proofs_of_accepted_certificates
    hlower

theorem irrational_of_eventual_natural_sondow_conditional_inputs
    {T : ProofSystem} {measure : ProofLengthMeasure} {φ : ℕ → FormulaCode}
    (h : EventualNaturalSondowConditionalInputs T measure φ) :
    ¬ (is_rational euler_mascheroni) :=
  eventual_certificate_collision_of_inputs
    h.certificate_collapse h.short_verification h.natural_lower_bound

theorem irrational_of_eventual_reflection_graft_model_inputs
    {T : ProofSystem} {measure : ProofLengthMeasure} {φ : ℕ → FormulaCode}
    (h : EventualReflectionGraftModelInputs T measure φ) :
    ¬ (is_rational euler_mascheroni) :=
  eventual_certificate_collision_of_inputs
    h.certificate_collapse h.short_verification h.graft_lower_bound

theorem irrational_of_eventual_partial_consistency_model_inputs
    {T : ProofSystem} {measure : ProofLengthMeasure} {φ : ℕ → FormulaCode}
    (h : EventualPartialConsistencyModelInputs T measure φ) :
    ¬ (is_rational euler_mascheroni) :=
  eventual_certificate_collision_of_inputs
    h.certificate_collapse h.short_verification h.source_lower_bound

theorem partial_consistency_collapse_lower_bound_collision
    (h :
      EventualPartialConsistencyModelInputs
        ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_eventual_partial_consistency_model_inputs h

theorem irrational_of_partial_consistency_spec_package
    (h : PartialConsistencySpecExternalPackage)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    ¬ (is_rational euler_mascheroni) :=
  partial_consistency_collapse_lower_bound_collision
    (eventual_partial_consistency_inputs_of_spec_package h hver)

theorem irrational_of_partial_consistency_spec_package_and_verification
    (h : PartialConsistencySpecExternalPackage)
    (hver : PAStandardVerificationTheorem) :
    ¬ (is_rational euler_mascheroni) :=
  partial_consistency_collapse_lower_bound_collision
    (eventual_partial_consistency_inputs_of_spec_package_and_verification h hver)

theorem irrational_of_partial_consistency_spec_package_and_trace
    (h : PartialConsistencySpecExternalPackage)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  partial_consistency_collapse_lower_bound_collision
    (eventual_partial_consistency_inputs_of_spec_package_and_trace
      h hrealize hembed)

theorem irrational_of_eventual_semantic_reflection_graft_model_inputs
    {length : FormulaCode → ℕ} {φ : ℕ → FormulaCode}
    (h : EventualSemanticReflectionGraftModelInputs length φ) :
    ¬ (is_rational euler_mascheroni) := by
  intro h_rat
  rcases h.certificate_collapse.accepted_eventually_under_rationality h_rat with
    ⟨N, h_accept⟩
  have ⟨f, h_poly, h_short⟩ :=
    h.short_verification.short_proofs_of_accepted_certificates
  have ⟨n, hn_ge, h_gt⟩ := h.graft_lower_bound.lower_bound f h_poly N
  have h_le_n := h_short n (h_accept n hn_ge)
  linarith

theorem irrational_of_reflection_graft_collapse_package
    (hcollapse : ReflectionGraftCollapsePackage)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowReflectionGraftCode) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_eventual_reflection_graft_model_inputs
    (eventual_reflection_graft_inputs_of_collapse_package hcollapse hlower)

theorem irrational_of_sondow_certificate_bridges
    (hcollapse : EventualCertificateCollapseInputs sondowCertificateValidCode)
    (hverify : SondowCertificateVerificationBridge)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowCertificateValidCode) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_eventual_natural_sondow_conditional_inputs
    (eventual_natural_sondow_inputs_of_bridges hcollapse hverify hlower)

theorem irrational_of_sondow_certificate_collapse_package
    (hcollapse : SondowCertificateCollapsePackage)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowCertificateValidCode) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_sondow_certificate_bridges
    hcollapse.toEventualCertificateCollapseInputs
    hcollapse.short_proof_bridge.toVerificationBridge
    hlower

theorem irrational_of_payload_spec_concrete_verification_and_graft_lower_bound
    (hfwd : SondowForwardInputs)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowReflectionGraftCode) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_reflection_graft_collapse_package
    (reflection_graft_collapse_package_of_payload_spec_and_concrete_verification
      hfwd hspec hver)
    hlower

theorem irrational_of_partial_consistency_spec_package_and_graft_lower_bound
    (hfwd : SondowForwardInputs)
    (hpkg : PartialConsistencySpecExternalPackage)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowReflectionGraftCode) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_reflection_graft_collapse_package
    (hpkg.toReflectionGraftCollapsePackage hfwd hver)
    hlower

theorem irrational_of_buss_pudlak_spec_package_and_graft_lower_bound
    (hfwd : SondowForwardInputs)
    (hpkg : BussPudlakPartialConsistencySpecPackage)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowReflectionGraftCode) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_partial_consistency_spec_package_and_graft_lower_bound
    hfwd hpkg.toPartialConsistencySpecExternalPackage hver hlower

theorem irrational_of_buss_pudlak_rescaled_spec_package_and_graft_lower_bound
    (hfwd : SondowForwardInputs)
    (hpkg : BussPudlakRescaledPartialConsistencySpecPackage)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowReflectionGraftCode) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_partial_consistency_spec_package_and_graft_lower_bound
    hfwd hpkg.toPartialConsistencySpecExternalPackage hver hlower

theorem irrational_of_wu_sondow_lower_bound
    (hcollapse : SondowCertificateCollapsePackage)
    (hwu : WuSondowLowerBoundConjecture) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_sondow_certificate_collapse_package hcollapse hwu

theorem irrational_of_forward_sondow_concrete_verification_and_wu_conjecture
    (hfwd : SondowForwardInputs)
    (hver : SondowCertificateConcreteVerificationPackage)
    (hwu : WuSondowLowerBoundConjecture) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_wu_sondow_lower_bound
    (sondow_certificate_collapse_package_of_forward_inputs_and_concrete_verification
      hfwd hver)
    hwu

theorem irrational_of_forward_sondow_trace_soundness_and_wu_conjecture
    (hfwd : SondowForwardInputs)
    (hsound : S21VerifierTraceSoundness sondowCertificateValidCode)
    (hembed : S21ToPALinearEmbeddingOn sondowCertificateValidCode)
    (hwu : WuSondowLowerBoundConjecture) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_wu_sondow_lower_bound
    (sondow_certificate_collapse_package_of_forward_inputs_trace_soundness_and_embedding
      hfwd hsound hembed)
    hwu

theorem irrational_of_standard_sondow_concrete_verification_and_wu_conjecture
    (hstd : SondowStandardInputs)
    (hver : SondowCertificateConcreteVerificationPackage)
    (hwu : WuSondowLowerBoundConjecture) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_concrete_verification_and_wu_conjecture
    hstd.toForward hver hwu

theorem irrational_of_standard_sondow_verification_and_wu_conjecture
    (hstd : SondowStandardInputs)
    (hver : PAStandardVerificationTheorem)
    (hwu : WuSondowLowerBoundConjecture) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_wu_sondow_lower_bound
    (sondow_certificate_collapse_package_of_standard_inputs_and_verification hstd hver)
    hwu

theorem irrational_of_standard_sondow_verification_and_strong_wu_conjecture
    (hstd : SondowStandardInputs)
    (hver : PAStandardVerificationTheorem)
    (hwu : StrongWuSondowLowerBoundConjecture) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_standard_sondow_verification_and_wu_conjecture
    hstd hver (WuSondowLowerBoundConjecture.of_strong hwu)

theorem irrational_of_forward_sondow_concrete_verification_and_strong_wu_conjecture
    (hfwd : SondowForwardInputs)
    (hver : SondowCertificateConcreteVerificationPackage)
    (hwu : StrongWuSondowLowerBoundConjecture) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_concrete_verification_and_wu_conjecture
    hfwd hver (WuSondowLowerBoundConjecture.of_strong hwu)

theorem irrational_of_forward_sondow_trace_soundness_and_strong_wu_conjecture
    (hfwd : SondowForwardInputs)
    (hsound : S21VerifierTraceSoundness sondowCertificateValidCode)
    (hembed : S21ToPALinearEmbeddingOn sondowCertificateValidCode)
    (hwu : StrongWuSondowLowerBoundConjecture) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_trace_soundness_and_wu_conjecture
    hfwd hsound hembed (WuSondowLowerBoundConjecture.of_strong hwu)

theorem irrational_of_standard_sondow_concrete_verification_and_strong_wu_conjecture
    (hstd : SondowStandardInputs)
    (hver : SondowCertificateConcreteVerificationPackage)
    (hwu : StrongWuSondowLowerBoundConjecture) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_concrete_verification_and_strong_wu_conjecture
    hstd.toForward hver hwu

theorem irrational_of_partial_consistency_transfer
    (hstd : SondowStandardInputs)
    (hver : PAStandardVerificationTheorem)
    (hlower : StrongPartialConsistencyLowerBound)
    (htransfer : PartialConsistencyToSondowCertificateTransfer) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_standard_sondow_verification_and_strong_wu_conjecture
    hstd hver
    (strong_wu_conjecture_of_partial_consistency_transfer hlower htransfer)

theorem irrational_of_forward_sondow_concrete_verification_and_partial_consistency_transfer
    (hfwd : SondowForwardInputs)
    (hver : SondowCertificateConcreteVerificationPackage)
    (hlower : StrongPartialConsistencyLowerBound)
    (htransfer : PartialConsistencyToSondowCertificateTransfer) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_concrete_verification_and_strong_wu_conjecture
    hfwd hver
    (strong_wu_conjecture_of_partial_consistency_transfer hlower htransfer)

theorem irrational_of_forward_sondow_trace_soundness_and_partial_consistency_transfer
    (hfwd : SondowForwardInputs)
    (hsound : S21VerifierTraceSoundness sondowCertificateValidCode)
    (hembed : S21ToPALinearEmbeddingOn sondowCertificateValidCode)
    (hlower : StrongPartialConsistencyLowerBound)
    (htransfer : PartialConsistencyToSondowCertificateTransfer) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_trace_soundness_and_strong_wu_conjecture
    hfwd hsound hembed
    (strong_wu_conjecture_of_partial_consistency_transfer hlower htransfer)

theorem irrational_of_standard_sondow_concrete_verification_and_partial_consistency_transfer
    (hstd : SondowStandardInputs)
    (hver : SondowCertificateConcreteVerificationPackage)
    (hlower : StrongPartialConsistencyLowerBound)
    (htransfer : PartialConsistencyToSondowCertificateTransfer) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_concrete_verification_and_partial_consistency_transfer
    hstd.toForward hver hlower htransfer

theorem irrational_of_forward_sondow_verification_payload_and_graft_lower_bound
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hver : PAStandardVerificationTheorem)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowReflectionGraftCode) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_reflection_graft_collapse_package
    (reflection_graft_collapse_package_of_forward_inputs_and_verification
      hfwd hpayload hver)
    hlower

theorem irrational_of_forward_sondow_trace_soundness_payload_and_graft_lower_bound
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hsound : S21VerifierTraceSoundness sondowReflectionGraftCode)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowReflectionGraftCode) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_reflection_graft_collapse_package
    (reflection_graft_collapse_package_of_forward_inputs_trace_soundness_and_embedding
      hfwd hpayload hsound hembed)
    hlower

theorem irrational_of_forward_sondow_concrete_verification_payload_and_graft_lower_bound
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowReflectionGraftCode) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_reflection_graft_collapse_package
    (reflection_graft_collapse_package_of_forward_inputs_and_concrete_verification
      hfwd hpayload hver)
    hlower

theorem eventual_reflection_graft_inputs_of_forward_sondow_concrete_verification
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowReflectionGraftCode) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  eventual_reflection_graft_inputs_of_collapse_package
    (reflection_graft_collapse_package_of_forward_inputs_and_concrete_verification
      hfwd hpayload hver)
    hlower

theorem irrational_of_forward_sondow_trace_soundness_global_embedding
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hsound : S21VerifierTraceSoundness sondowReflectionGraftCode)
    (hembed : S21ToPALinearEmbedding)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowReflectionGraftCode) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_trace_soundness_payload_and_graft_lower_bound
    hfwd hpayload hsound (hembed.on sondowReflectionGraftCode) hlower

theorem irrational_of_standard_sondow_verification_payload_and_graft_lower_bound
    (hstd : SondowStandardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hver : PAStandardVerificationTheorem)
    (hlower :
      EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
        sondowReflectionGraftCode) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_verification_payload_and_graft_lower_bound
    hstd.toForward hpayload hver hlower

theorem irrational_of_reflection_graft_projection
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hver : PAStandardVerificationTheorem)
    (hlower : StrongPartialConsistencyLowerBound)
    (hprojection : PartialConsistencyToReflectionGraftProjection) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_verification_payload_and_graft_lower_bound
    hfwd hpayload hver
    (reflection_graft_eventual_lower_bound_of_partial_consistency
      hlower hprojection)

theorem irrational_of_reflection_graft_lower_bound_transfer
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hver : PAStandardVerificationTheorem)
    (hlower : StrongPartialConsistencyLowerBound)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_verification_payload_and_graft_lower_bound
    hfwd hpayload hver
    (reflection_graft_eventual_lower_bound_of_partial_consistency_transfer
      hlower htransfer)

theorem irrational_of_buss_pudlak_conjunction_transfer
    (hfwd : SondowForwardInputs)
    (hver : PAStandardVerificationTheorem)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_reflection_graft_lower_bound_transfer
    hfwd
    (reflection_graft_payload_inputs_of_partial_consistency_truth hbuss.payload_truth)
    hver hbuss.strong_lower_bound htransfer

theorem irrational_of_buss_pudlak_conjunction_transfer_of_trace_soundness
    (hfwd : SondowForwardInputs)
    (hsound : S21VerifierTraceSoundness sondowReflectionGraftCode)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_trace_soundness_payload_and_graft_lower_bound
    hfwd
    (reflection_graft_payload_inputs_of_partial_consistency_truth hbuss.payload_truth)
    hsound hembed
    (reflection_graft_eventual_lower_bound_of_partial_consistency_transfer
      hbuss.strong_lower_bound htransfer)

theorem irrational_of_buss_pudlak_conjunction_transfer_of_concrete_verification
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_concrete_verification_payload_and_graft_lower_bound
    hfwd
    (reflection_graft_payload_inputs_of_partial_consistency_truth hbuss.payload_truth)
    hver
    (reflection_graft_eventual_lower_bound_of_partial_consistency_transfer
      hbuss.strong_lower_bound htransfer)

theorem irrational_of_buss_pudlak_conjunction_transfer_of_rescaled_package
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hbuss : BussPudlakRescaledPartialConsistencyPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_concrete_verification_payload_and_graft_lower_bound
    hfwd
    (reflection_graft_payload_inputs_of_partial_consistency_truth hbuss.payload_truth)
    hver
    (reflection_graft_eventual_lower_bound_of_rescaled_partial_consistency
      hbuss.rescaling htransfer)

theorem irrational_of_buss_pudlak_conjunction_transfer_of_time_constructible_rescaling
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_buss_pudlak_conjunction_transfer_of_rescaled_package
    hfwd hver
    (BussPudlakRescaledPartialConsistencyPackage.of_time_constructible_rescaling
      htruth hreading hrescale)
    htransfer

theorem eventual_reflection_graft_inputs_of_rescaled_buss_pudlak_package
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (hbuss : BussPudlakRescaledPartialConsistencyPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  eventual_reflection_graft_inputs_of_forward_sondow_concrete_verification
    hfwd
    (reflection_graft_payload_inputs_of_partial_consistency_truth hbuss.payload_truth)
    hver
    (reflection_graft_eventual_lower_bound_of_rescaled_partial_consistency
      hbuss.rescaling htransfer)

theorem eventual_reflection_graft_inputs_of_time_constructible_rescaling
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (htruth : PartialConsistencyPayloadTruth)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  eventual_reflection_graft_inputs_of_forward_sondow_concrete_verification
    hfwd
    (reflection_graft_payload_inputs_of_partial_consistency_truth htruth)
    hver
    (reflection_graft_eventual_lower_bound_of_time_constructible_rescaling
      hrescale htransfer)

theorem irrational_of_reflection_graft_projection_principle
    (hfwd : SondowForwardInputs)
    (hpayload : ReflectionGraftPayloadInputs)
    (hver : PAStandardVerificationTheorem)
    (hlower : StrongPartialConsistencyLowerBound)
    (hprinciple : PAProofLengthProjectionPrinciple) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_reflection_graft_projection
    hfwd hpayload hver hlower
    (partial_consistency_to_reflection_graft_projection_of_principle hprinciple)

theorem irrational_of_partial_consistency_truth_and_projection_principle
    (hfwd : SondowForwardInputs)
    (htruth : PartialConsistencyPayloadTruth)
    (hver : PAStandardVerificationTheorem)
    (hlower : StrongPartialConsistencyLowerBound)
    (hprinciple : PAProofLengthProjectionPrinciple) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_reflection_graft_projection_principle
    hfwd
    (reflection_graft_payload_inputs_of_partial_consistency_truth htruth)
    hver hlower hprinciple

theorem irrational_of_partial_consistency_external_package
    (hfwd : SondowForwardInputs)
    (hver : PAStandardVerificationTheorem)
    (hpartial : PartialConsistencyExternalPackage)
    (hprinciple : PAProofLengthProjectionPrinciple) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_partial_consistency_truth_and_projection_principle
    hfwd hpartial.payload_truth hver hpartial.strong_lower_bound hprinciple

theorem irrational_of_buss_pudlak_partial_consistency_package
    (hfwd : SondowForwardInputs)
    (hver : PAStandardVerificationTheorem)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hprinciple : PAProofLengthProjectionPrinciple) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_partial_consistency_external_package
    hfwd hver hbuss.toPartialConsistencyExternalPackage hprinciple

theorem irrational_of_buss_pudlak_conjunction_graft
    (hfwd : SondowForwardInputs)
    (hver : PAStandardVerificationTheorem)
    (hbuss : BussPudlakPartialConsistencyPackage)
    (hprojection : PartialConsistencyToReflectionGraftProjection) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_reflection_graft_projection
    hfwd
    (reflection_graft_payload_inputs_of_partial_consistency_truth hbuss.payload_truth)
    hver hbuss.strong_lower_bound hprojection

-- Narrow publication-facing bridge for the conjunction graft.  It records both
-- the intended `A ∧ B` graft syntax and the concrete proof-length projection
-- from the graft to the partial-consistency payload.
