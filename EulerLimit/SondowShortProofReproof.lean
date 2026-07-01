/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.SondowForwardReproof
import EulerLimit.ReflectionGraftTrace

/-!
# Short-proof collapse adapters from the reproved Sondow forward package

This module instantiates the existing short-proof/collapse bridges with the
Lean-closed `SondowForwardInputs.of_reproof` package.  It does not discharge the
bounded-arithmetic verifier, payload, embedding, or Pudlak lower-bound inputs;
it makes the analytic Sondow side no longer appear as an external parameter in
the collapse construction.
-/

noncomputable section

/-- Rationality gives eventual acceptance of the Sondow certificate family,
using the internally reproved forward package. -/
theorem accepted_sondow_certificate_eventual_of_rationality_reproof
    (h_rat : is_rational euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      accepted_certificate (sondowCertificateValidCode n) :=
  accepted_sondow_certificate_eventual_of_rationality
    SondowForwardInputs.of_reproof
    full_sondow_certificate_realizes_formula_true
    h_rat

/-- The Sondow certificate collapse inputs with the analytic forward package
already closed internally. -/
def sondow_certificate_eventual_collapse_inputs_of_reproof
    (hver : SondowCertificateConcreteVerificationPackage) :
    EventualCertificateCollapseInputs sondowCertificateValidCode :=
  (sondow_certificate_collapse_package_of_forward_inputs_and_concrete_verification
    SondowForwardInputs.of_reproof hver).toEventualCertificateCollapseInputs

/-- The reflection-graft collapse package with the analytic forward package
already closed internally. -/
def reflection_graft_collapse_package_of_reproof
    (hpayload : ReflectionGraftPayloadInputs)
    (hver : ReflectionGraftConcreteVerificationPackage) :
    ReflectionGraftCollapsePackage :=
  reflection_graft_collapse_package_of_forward_inputs_and_concrete_verification
    SondowForwardInputs.of_reproof hpayload hver

/-- The reflection-graft collapse inputs with the analytic forward package
already closed internally. -/
def reflection_graft_eventual_collapse_inputs_of_reproof
    (hspec : PartialConsistencyPayloadSpec)
    (hver : ReflectionGraftConcreteVerificationPackage) :
    EventualCertificateCollapseInputs sondowReflectionGraftCode :=
  reflection_graft_eventual_collapse_inputs_of_payload_spec
    SondowForwardInputs.of_reproof hspec hver

/-- A packaged verification bridge becomes a reflection-graft collapse input
without any remaining Sondow-forward parameter. -/
def SondowCollapseVerificationBridgePackage.toReflectionGraftCollapseInputsOfReproof
    (h : SondowCollapseVerificationBridgePackage) :
    EventualCertificateCollapseInputs sondowReflectionGraftCode :=
  h.toReflectionGraftCollapseInputs SondowForwardInputs.of_reproof

/-- A packaged bounded-arithmetic verification bridge plus rationality gives
eventual polynomial PA short proofs for the reflection-graft family. -/
theorem SondowCollapseVerificationBridgePackage.eventual_short_proofs_of_reproof_rationality
    (h : SondowCollapseVerificationBridgePackage)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n := by
  let hcollapse := h.toReflectionGraftCollapseInputsOfReproof
  rcases hcollapse.formal_verification_short with ⟨f, hf_poly, hf_bound⟩
  rcases hcollapse.accepted_eventually_under_rationality h_rat with ⟨N, hN⟩
  refine ⟨f, hf_poly, N, ?_⟩
  intro n hn
  have hacc := hN n hn
  exact ⟨hacc, hf_bound n hacc⟩

/-- Public short-proof/collapse endpoint: after the Sondow forward reproof, the
remaining bounded-arithmetic verification bridge is enough to turn rationality
of `γ` into eventual polynomial PA short proofs for the reflection-graft family. -/
theorem bounded_arithmetic_short_proof_collapse_of_rationality_reproof
    (hverify : SondowCollapseVerificationBridgePackage)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n :=
  hverify.eventual_short_proofs_of_reproof_rationality h_rat

/-- Direct short-proof/collapse statement: under rationality, the reflection-graft
family has eventual polynomial PA short proofs, with the Sondow forward package
filled by the internal reproof. -/
theorem reflection_graft_eventual_short_proofs_of_reproof_rationality
    (htrace : S21VerifierTracePackage)
    (hcost : S21GraftConjunctionIntroductionCost)
    (hembed : S21ToPALinearEmbeddingOn sondowReflectionGraftCode)
    (hpayload : ReflectionGraftPayloadInputs)
    (h_rat : is_rational euler_mascheroni) :
    ∃ f : ℕ → ℝ, is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        accepted_certificate (sondowReflectionGraftCode n) ∧
          proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
            (sondowReflectionGraftCode n) ≤ f n :=
  reflection_graft_eventual_short_proofs_of_global_trace_cost_and_rationality
    htrace hcost hembed
    SondowForwardInputs.of_reproof hpayload h_rat

end
