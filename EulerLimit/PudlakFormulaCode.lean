/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.RouteDefaults

/-!
# Pudlak package to formula-code realization routes

This module keeps the Pudlak finite-consistency lower-bound package connected to
the local MiniHilbert formula-code realization layer without adding more route
combinators to `EulerLimit.Basic`.
-/

open Filter MiniHilbert

universe u v w

def PudlakFiniteConsistencyLowerBoundPackage.toBussPudlakTimeConstructibleRescalingTheorem
    (h : PudlakFiniteConsistencyLowerBoundPackage) :
    BussPudlakTimeConstructibleRescalingTheorem where
  scale := h.scale
  scale_properties := h.scale_properties
  rescaled_strong_lower_bound := h.rescaled_strong_lower_bound

def PudlakFiniteConsistencyLowerBoundPackage.toPartialConsistencyRescalingPackage
    (h : PudlakFiniteConsistencyLowerBoundPackage) :
    PartialConsistencyRescalingPackage :=
  PartialConsistencyRescalingPackage.of_polynomial_cofinal_scale
    h.scale_properties h.rescaled_strong_lower_bound

def PudlakFiniteConsistencyLowerBoundPackage.transferToPartialConsistency
    (h : PudlakFiniteConsistencyLowerBoundPackage) :
    RescaledPartialConsistencyToPartialConsistencyTransfer h.scale :=
  rescaled_partial_consistency_transfer_of_polynomial_cofinal_scale
    h.scale_properties

def PudlakFiniteConsistencyLowerBoundPackage.toBussPudlakRescaledSpecPackage
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec) :
    BussPudlakRescaledPartialConsistencySpecPackage where
  payload_spec := hspec
  rescaling := h.toPartialConsistencyRescalingPackage

def PudlakFiniteConsistencyLowerBoundPackage.toStrongPartialConsistencyLowerBound
    (h : PudlakFiniteConsistencyLowerBoundPackage) :
    StrongPartialConsistencyLowerBound :=
  h.toPartialConsistencyRescalingPackage.toStrongPartialConsistencyLowerBound

def PudlakFiniteConsistencyLowerBoundPackage.toBussPudlakSpecPackage
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec) :
    BussPudlakPartialConsistencySpecPackage :=
  (h.toBussPudlakRescaledSpecPackage hspec)
    |>.toBussPudlakPartialConsistencySpecPackage

theorem PudlakFiniteConsistencyLowerBoundPackage.rescaled_to_payload_lower_bound
    (h : PudlakFiniteConsistencyLowerBoundPackage) :
    h.rescaled_strong_lower_bound.transfer h.transferToPartialConsistency =
      h.toStrongPartialConsistencyLowerBound := by
  rfl

theorem PudlakFiniteConsistencyLowerBoundPackage.eventualPartialConsistencyLowerBound
    (h : PudlakFiniteConsistencyLowerBoundPackage) :
    EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      partialConsistencyCode :=
  partial_consistency_eventual_lower_bound_of_strong
    h.toStrongPartialConsistencyLowerBound

theorem PudlakFiniteConsistencyLowerBoundPackage.toEventualPartialConsistencyModelInputs
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  eventual_partial_consistency_inputs_of_collapse_and_lower_bound
    ((h.toBussPudlakSpecPackage hspec)
      |>.toEventualPartialConsistencyCollapseInputs hver)
    h.eventualPartialConsistencyLowerBound

theorem PudlakFiniteConsistencyLowerBoundPackage.toEventualPartialConsistencyModelInputs'
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PAStandardVerificationTheorem) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  eventual_partial_consistency_inputs_of_collapse_and_lower_bound
    ((h.toBussPudlakSpecPackage hspec)
      |>.toEventualPartialConsistencyCollapseInputs' hver)
    h.eventualPartialConsistencyLowerBound

theorem PudlakFiniteConsistencyLowerBoundPackage.toEventualPartialConsistencyModelInputsOfTrace
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  eventual_partial_consistency_inputs_of_collapse_and_lower_bound
    ((h.toBussPudlakSpecPackage hspec)
      |>.toEventualPartialConsistencyCollapseInputsOfTrace hrealize hembed)
    h.eventualPartialConsistencyLowerBound

theorem irrational_of_payload_spec_partial_consistency_verification_pudlak_package
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PartialConsistencyConcreteVerificationPackage)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage) :
    ¬ (is_rational euler_mascheroni) :=
  partial_consistency_collapse_lower_bound_collision
    (pudlak_lower_bound.toEventualPartialConsistencyModelInputs hspec hver)

theorem irrational_of_payload_spec_standard_verification_pudlak_package
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PAStandardVerificationTheorem)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage) :
    ¬ (is_rational euler_mascheroni) :=
  partial_consistency_collapse_lower_bound_collision
    (pudlak_lower_bound.toEventualPartialConsistencyModelInputs' hspec hver)

theorem irrational_of_payload_spec_trace_realization_pudlak_package
    (hspec : PartialConsistencyPayloadSpec)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage) :
    ¬ (is_rational euler_mascheroni) :=
  partial_consistency_collapse_lower_bound_collision
    (pudlak_lower_bound.toEventualPartialConsistencyModelInputsOfTrace
      hspec hrealize hembed)

theorem irrational_of_buss_pudlak_spec_package_partial_consistency_verification
    (hpkg : BussPudlakPartialConsistencySpecPackage)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_partial_consistency_spec_package
    hpkg.toPartialConsistencySpecExternalPackage hver

theorem irrational_of_buss_pudlak_spec_package_standard_verification
    (hpkg : BussPudlakPartialConsistencySpecPackage)
    (hver : PAStandardVerificationTheorem) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_partial_consistency_spec_package_and_verification
    hpkg.toPartialConsistencySpecExternalPackage hver

theorem irrational_of_buss_pudlak_spec_package_trace_realization
    (hpkg : BussPudlakPartialConsistencySpecPackage)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_partial_consistency_spec_package_and_trace
    hpkg.toPartialConsistencySpecExternalPackage hrealize hembed

theorem irrational_of_buss_pudlak_rescaled_spec_package_partial_consistency_verification
    (hpkg : BussPudlakRescaledPartialConsistencySpecPackage)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_buss_pudlak_spec_package_partial_consistency_verification
    hpkg.toBussPudlakPartialConsistencySpecPackage hver

theorem irrational_of_buss_pudlak_rescaled_spec_package_standard_verification
    (hpkg : BussPudlakRescaledPartialConsistencySpecPackage)
    (hver : PAStandardVerificationTheorem) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_buss_pudlak_spec_package_standard_verification
    hpkg.toBussPudlakPartialConsistencySpecPackage hver

theorem irrational_of_buss_pudlak_rescaled_spec_package_trace_realization
    (hpkg : BussPudlakRescaledPartialConsistencySpecPackage)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_buss_pudlak_spec_package_trace_realization
    hpkg.toBussPudlakPartialConsistencySpecPackage hrealize hembed

theorem PudlakFiniteConsistencyLowerBoundPackage.strongReflectionGraftLowerBound_of_transfer
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    StrongProofLengthLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  strong_reflection_graft_lower_bound_of_partial_consistency_transfer
    h.toStrongPartialConsistencyLowerBound htransfer

theorem PudlakFiniteConsistencyLowerBoundPackage.eventualReflectionGraftLowerBound_of_transfer
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  reflection_graft_eventual_lower_bound_of_partial_consistency_transfer
    h.toStrongPartialConsistencyLowerBound htransfer

/-- Short audit name: the transferred Pudlak lower bound yields an explicit
eventual strict gap against any fixed polynomial Sondow upper function on the
reflection-graft family. -/
theorem PudlakFiniteConsistencyLowerBoundPackage.reflectionGraftGap_of_transfer
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (U : ℕ → ℝ) (hU : is_polynomial_bound U) :
    EventualStrictGap U
      (fun n : ℕ =>
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n)) :=
  (h.eventualReflectionGraftLowerBound_of_transfer htransfer).toProofLengthGap
    U hU

theorem PudlakFiniteConsistencyLowerBoundPackage.strongReflectionGraftLowerBound_of_projection
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hprojection : PartialConsistencyToReflectionGraftProjection) :
    StrongProofLengthLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  strong_reflection_graft_lower_bound_of_partial_consistency
    h.toStrongPartialConsistencyLowerBound hprojection

theorem PudlakFiniteConsistencyLowerBoundPackage.eventualReflectionGraftLowerBound_of_projection
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hprojection : PartialConsistencyToReflectionGraftProjection) :
    EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  reflection_graft_eventual_lower_bound_of_partial_consistency
    h.toStrongPartialConsistencyLowerBound hprojection

/-- Short audit name: the projection route also exposes the final gap
certificate on the reflection-graft family. -/
theorem PudlakFiniteConsistencyLowerBoundPackage.reflectionGraftGap_of_projection
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hprojection : PartialConsistencyToReflectionGraftProjection)
    (U : ℕ → ℝ) (hU : is_polynomial_bound U) :
    EventualStrictGap U
      (fun n : ℕ =>
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n)) :=
  (h.eventualReflectionGraftLowerBound_of_projection hprojection).toProofLengthGap
    U hU

/-- Short audit name: a projection principle also exposes the final gap
certificate on the reflection-graft family. -/
theorem PudlakFiniteConsistencyLowerBoundPackage.reflectionGraftGap_of_projection_principle
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hprinciple : PAProofLengthProjectionPrinciple)
    (U : ℕ → ℝ) (hU : is_polynomial_bound U) :
    EventualStrictGap U
      (fun n : ℕ =>
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n)) :=
  h.reflectionGraftGap_of_projection
    (partial_consistency_to_reflection_graft_projection_of_principle
      hprinciple)
    U hU

/-- Audit alias: the transfer certificate preserves the Pudlak gap after moving
from partial consistency to the reflection-graft family. -/
theorem PudlakFiniteConsistencyLowerBoundPackage.transfer_preservesReflectionGraftGap
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (U : ℕ → ℝ) (hU : is_polynomial_bound U) :
    EventualStrictGap U
      (fun n : ℕ =>
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n)) :=
  h.reflectionGraftGap_of_transfer htransfer U hU

/-- Audit alias: a concrete projection certificate preserves the Pudlak gap on
the reflection-graft family. -/
theorem PudlakFiniteConsistencyLowerBoundPackage.projection_preservesReflectionGraftGap
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hprojection : PartialConsistencyToReflectionGraftProjection)
    (U : ℕ → ℝ) (hU : is_polynomial_bound U) :
    EventualStrictGap U
      (fun n : ℕ =>
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n)) :=
  h.reflectionGraftGap_of_projection hprojection U hU

/-- Audit alias: the projection principle also preserves the final Pudlak gap
on the reflection-graft family. -/
theorem PudlakFiniteConsistencyLowerBoundPackage.projectionPrinciple_preservesReflectionGraftGap
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hprinciple : PAProofLengthProjectionPrinciple)
    (U : ℕ → ℝ) (hU : is_polynomial_bound U) :
    EventualStrictGap U
      (fun n : ℕ =>
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode n)) :=
  h.reflectionGraftGap_of_projection_principle hprinciple U hU

theorem pudlak_eventualReflectionGraftLowerBound_of_projection_principle
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hprinciple : PAProofLengthProjectionPrinciple) :
    EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  h.eventualReflectionGraftLowerBound_of_projection
    (partial_consistency_to_reflection_graft_projection_of_principle hprinciple)

theorem PudlakFiniteConsistencyLowerBoundPackage.strongWuSondowLowerBound_of_certificateTransfer
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : PartialConsistencyToSondowCertificateTransfer) :
    StrongWuSondowLowerBoundConjecture :=
  strong_wu_conjecture_of_partial_consistency_transfer
    h.toStrongPartialConsistencyLowerBound htransfer

theorem PudlakFiniteConsistencyLowerBoundPackage.wuSondowLowerBound_of_certificateTransfer
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : PartialConsistencyToSondowCertificateTransfer) :
    WuSondowLowerBoundConjecture :=
  WuSondowLowerBoundConjecture.of_strong
    (h.strongWuSondowLowerBound_of_certificateTransfer htransfer)

theorem irrational_of_payload_spec_concrete_verification_pudlak_package_and_projection
    (hfwd : SondowForwardInputs)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (hprojection : PartialConsistencyToReflectionGraftProjection) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_reflection_graft_collapse_package
    (reflection_graft_collapse_package_of_payload_spec_and_concrete_verification
      hfwd hspec hver)
    (pudlak_lower_bound.eventualReflectionGraftLowerBound_of_projection
      hprojection)

theorem
    irrational_of_payload_spec_concrete_verification_pudlak_package_and_projection_principle
    (hfwd : SondowForwardInputs)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : ReflectionGraftConcreteVerificationPackage)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (hprinciple : PAProofLengthProjectionPrinciple) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_payload_spec_concrete_verification_pudlak_package_and_projection
    hfwd hspec hver pudlak_lower_bound
    (partial_consistency_to_reflection_graft_projection_of_principle hprinciple)

theorem irrational_of_verified_collapse_pudlak_package_and_projection
    (hfwd : SondowForwardInputs)
    (hverify : SondowCollapseVerificationBridgePackage)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (hprojection : PartialConsistencyToReflectionGraftProjection) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_payload_spec_concrete_verification_pudlak_package_and_projection
    hfwd
    hverify.toPayloadSpec
    hverify.toReflectionGraftConcreteVerification
    pudlak_lower_bound
    hprojection

theorem irrational_of_verified_collapse_pudlak_package_and_projection_principle
    (hfwd : SondowForwardInputs)
    (hverify : SondowCollapseVerificationBridgePackage)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (hprinciple : PAProofLengthProjectionPrinciple) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_verified_collapse_pudlak_package_and_projection
    hfwd hverify pudlak_lower_bound
    (partial_consistency_to_reflection_graft_projection_of_principle hprinciple)

theorem irrational_of_forward_sondow_concrete_verification_pudlak_package_and_certificate_transfer
    (hfwd : SondowForwardInputs)
    (hver : SondowCertificateConcreteVerificationPackage)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : PartialConsistencyToSondowCertificateTransfer) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_eventual_natural_sondow_conditional_inputs
    (eventual_natural_sondow_inputs_of_bridges
      (sondow_certificate_collapse_package_of_forward_inputs_and_concrete_verification
        hfwd hver).toEventualCertificateCollapseInputs
      hver.toShortProofBridge.toVerificationBridge
      (pudlak_lower_bound.wuSondowLowerBound_of_certificateTransfer htransfer))

theorem irrational_of_forward_sondow_trace_soundness_pudlak_package_and_certificate_transfer
    (hfwd : SondowForwardInputs)
    (hsound : S21VerifierTraceSoundness sondowCertificateValidCode)
    (hembed : S21ToPALinearEmbeddingOn sondowCertificateValidCode)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : PartialConsistencyToSondowCertificateTransfer) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_eventual_natural_sondow_conditional_inputs
    (eventual_natural_sondow_inputs_of_bridges
      (sondow_certificate_collapse_package_of_forward_inputs_trace_soundness_and_embedding
        hfwd hsound hembed).toEventualCertificateCollapseInputs
      (sondow_certificate_short_proof_bridge_of_trace_soundness_and_linear_embedding
        hsound hembed).toVerificationBridge
      (pudlak_lower_bound.wuSondowLowerBound_of_certificateTransfer htransfer))

theorem irrational_of_standard_sondow_concrete_verification_pudlak_package_and_certificate_transfer
    (hstd : SondowStandardInputs)
    (hver : SondowCertificateConcreteVerificationPackage)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (htransfer : PartialConsistencyToSondowCertificateTransfer) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_forward_sondow_concrete_verification_pudlak_package_and_certificate_transfer
    hstd.toForward hver pudlak_lower_bound htransfer

theorem gamma_irrational_of_pudlak_formula_code_realization_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_truth : PartialConsistencyPayloadTruth)
    (partial_payload_reading : PartialConsistencyPayloadIntendedReading)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (hilbert_formula_code_realization :
      HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_time_rescaling_and_formula_code_realization
    sondow_forward
    concrete_verification
    partial_payload_truth
    partial_payload_reading
    pudlak_lower_bound.toBussPudlakTimeConstructibleRescalingTheorem
    hilbert_formula_code_realization

theorem gamma_irrational_of_pudlak_formula_code_transfer_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_truth : PartialConsistencyPayloadTruth)
    (partial_payload_reading : PartialConsistencyPayloadIntendedReading)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (hilbert_formula_code_realization :
      HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_time_rescaling_and_formula_code_transfer
    sondow_forward
    concrete_verification
    partial_payload_truth
    partial_payload_reading
    pudlak_lower_bound.toBussPudlakTimeConstructibleRescalingTheorem
    hilbert_formula_code_realization

theorem gamma_irrational_of_pudlak_formula_code_realization_spec_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_spec : PartialConsistencyPayloadSpec)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (hilbert_formula_code_realization :
      HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pudlak_formula_code_realization_components
    sondow_forward
    concrete_verification
    partial_payload_spec.toPayloadTruth
    partial_payload_spec.toIntendedReading
    pudlak_lower_bound
    hilbert_formula_code_realization

theorem gamma_irrational_of_pudlak_formula_code_transfer_spec_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_spec : PartialConsistencyPayloadSpec)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (hilbert_formula_code_realization :
      HilbertRightConjElimFormulaCodeRealization Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pudlak_formula_code_transfer_components
    sondow_forward
    concrete_verification
    partial_payload_spec.toPayloadTruth
    partial_payload_spec.toIntendedReading
    pudlak_lower_bound
    hilbert_formula_code_realization

theorem gamma_irrational_of_pudlak_default_formula_code_realization_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_truth : PartialConsistencyPayloadTruth)
    (partial_payload_reading : PartialConsistencyPayloadIntendedReading)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (hilbert_formula_code_realization :
      DefaultHilbertRightConjElimFormulaCodeRealization Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pudlak_formula_code_realization_components
    sondow_forward
    concrete_verification
    partial_payload_truth
    partial_payload_reading
    pudlak_lower_bound
    hilbert_formula_code_realization

theorem gamma_irrational_of_pudlak_default_formula_code_transfer_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_truth : PartialConsistencyPayloadTruth)
    (partial_payload_reading : PartialConsistencyPayloadIntendedReading)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (hilbert_formula_code_realization :
      DefaultHilbertRightConjElimFormulaCodeRealization Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pudlak_formula_code_transfer_components
    sondow_forward
    concrete_verification
    partial_payload_truth
    partial_payload_reading
    pudlak_lower_bound
    hilbert_formula_code_realization

theorem gamma_irrational_of_pudlak_default_formula_code_realization_spec_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_spec : PartialConsistencyPayloadSpec)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (hilbert_formula_code_realization :
      DefaultHilbertRightConjElimFormulaCodeRealization Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pudlak_formula_code_realization_spec_components
    sondow_forward
    concrete_verification
    partial_payload_spec
    pudlak_lower_bound
    hilbert_formula_code_realization

theorem gamma_irrational_of_pudlak_default_formula_code_transfer_spec_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_spec : PartialConsistencyPayloadSpec)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (hilbert_formula_code_realization :
      DefaultHilbertRightConjElimFormulaCodeRealization Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pudlak_formula_code_transfer_spec_components
    sondow_forward
    concrete_verification
    partial_payload_spec
    pudlak_lower_bound
    hilbert_formula_code_realization
