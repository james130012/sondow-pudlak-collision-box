/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.MainRoutes

/-!
# Strengthened finite-consistency lower-bound interface

This module separates the intended Pudlak-style strengthened finite-consistency
target from the ordinary `partialConsistencyCode` family.  A strengthened lower
bound only enters the existing collision route through an explicit transfer
theorem to the standard partial-consistency family.
-/

open Filter

universe q

abbrev StrongStrengthenedPartialConsistencyLowerBound : Prop :=
  StrongProofLengthLowerBound
    ProofSystem.PA ProofLengthMeasure.symbolSize
    strengthenedPartialConsistencyCode

abbrev StrengthenedToPartialConsistencyLowerBoundTransfer : Prop :=
  StrongLowerBoundTransfer
    ProofSystem.PA ProofLengthMeasure.symbolSize
    strengthenedPartialConsistencyCode partialConsistencyCode

abbrev StrengthenedToPartialConsistencyProjection : Prop :=
  ProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    strengthenedPartialConsistencyCode partialConsistencyCode

abbrev StrengthenedToPartialConsistencyLinearProjection :=
  LinearProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    strengthenedPartialConsistencyCode partialConsistencyCode

abbrev StrengthenedToPartialConsistencyConstantProjection :=
  ConstantProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    strengthenedPartialConsistencyCode partialConsistencyCode

def rescaledStrengthenedPartialConsistencyCode (ρ : ℕ → ℕ) (n : ℕ) :
    FormulaCode :=
  strengthenedPartialConsistencyCode (ρ n)

def pudlakStrengthenedFiniteConsistencyCode (n : ℕ) : FormulaCode :=
  strengthenedPartialConsistencyCode n

theorem pudlakStrengthenedFiniteConsistencyCode_eq
    (n : ℕ) :
    pudlakStrengthenedFiniteConsistencyCode n =
      strengthenedPartialConsistencyCode n := by
  rfl

def rescaledPudlakStrengthenedFiniteConsistencyCode
    (ρ : ℕ → ℕ) (n : ℕ) : FormulaCode :=
  pudlakStrengthenedFiniteConsistencyCode (ρ n)

theorem rescaledPudlakStrengthenedFiniteConsistencyCode_eq
    (ρ : ℕ → ℕ) (n : ℕ) :
    rescaledPudlakStrengthenedFiniteConsistencyCode ρ n =
      rescaledStrengthenedPartialConsistencyCode ρ n := by
  rfl

abbrev StrongRescaledStrengthenedPartialConsistencyLowerBound
    (ρ : ℕ → ℕ) : Prop :=
  StrongProofLengthLowerBound
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledStrengthenedPartialConsistencyCode ρ)

abbrev RescaledStrengthenedToStrengthenedLowerBoundTransfer
    (ρ : ℕ → ℕ) : Prop :=
  StrongLowerBoundTransfer
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledStrengthenedPartialConsistencyCode ρ)
    strengthenedPartialConsistencyCode

abbrev SourceToStrengthenedLowerBoundTransfer (source : ℕ → FormulaCode) : Prop :=
  StrongLowerBoundTransfer
    ProofSystem.PA ProofLengthMeasure.symbolSize
    source strengthenedPartialConsistencyCode

abbrev SourceToStrengthenedProjection (source : ℕ → FormulaCode) : Prop :=
  ProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    source strengthenedPartialConsistencyCode

abbrev SourceToStrengthenedLinearProjection (source : ℕ → FormulaCode) :=
  LinearProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    source strengthenedPartialConsistencyCode

abbrev SourceToStrengthenedConstantProjection (source : ℕ → FormulaCode) :=
  ConstantProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    source strengthenedPartialConsistencyCode

structure ExternalStrengthenedLowerBoundSource where
  code : ℕ → FormulaCode
  strong_lower_bound :
    StrongProofLengthLowerBound
      ProofSystem.PA ProofLengthMeasure.symbolSize code

structure CalibratedExternalStrengthenedLowerBoundSource where
  source : ExternalStrengthenedLowerBoundSource
  transfer_to_strengthened : SourceToStrengthenedLowerBoundTransfer source.code
  transfer_to_partial : StrengthenedToPartialConsistencyLowerBoundTransfer

def rescaledExternalStrengthenedLowerBoundCode
    (source : ℕ → FormulaCode) (ρ : ℕ → ℕ) (n : ℕ) : FormulaCode :=
  source (ρ n)

abbrev StrongRescaledExternalStrengthenedLowerBound
    (source : ℕ → FormulaCode) (ρ : ℕ → ℕ) : Prop :=
  StrongProofLengthLowerBound
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledExternalStrengthenedLowerBoundCode source ρ)

abbrev RescaledSourceToRescaledStrengthenedLowerBoundTransfer
    (source : ℕ → FormulaCode) (ρ : ℕ → ℕ) : Prop :=
  StrongLowerBoundTransfer
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledExternalStrengthenedLowerBoundCode source ρ)
    (rescaledStrengthenedPartialConsistencyCode ρ)

abbrev RescaledSourceToRescaledStrengthenedProjection
    (source : ℕ → FormulaCode) (ρ : ℕ → ℕ) : Prop :=
  ProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledExternalStrengthenedLowerBoundCode source ρ)
    (rescaledStrengthenedPartialConsistencyCode ρ)

abbrev RescaledSourceToRescaledStrengthenedLinearProjection
    (source : ℕ → FormulaCode) (ρ : ℕ → ℕ) :=
  LinearProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledExternalStrengthenedLowerBoundCode source ρ)
    (rescaledStrengthenedPartialConsistencyCode ρ)

abbrev RescaledSourceToRescaledStrengthenedConstantProjection
    (source : ℕ → FormulaCode) (ρ : ℕ → ℕ) :=
  ConstantProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledExternalStrengthenedLowerBoundCode source ρ)
    (rescaledStrengthenedPartialConsistencyCode ρ)

structure RescaledExternalStrengthenedLowerBoundSource where
  code : ℕ → FormulaCode
  scale : ℕ → ℕ
  scale_properties : PolynomialCofinalScale scale
  rescaled_strong_lower_bound :
    StrongRescaledExternalStrengthenedLowerBound code scale

structure CalibratedRescaledExternalStrengthenedLowerBoundSource where
  source : RescaledExternalStrengthenedLowerBoundSource
  transfer_to_rescaled_strengthened :
    RescaledSourceToRescaledStrengthenedLowerBoundTransfer
      source.code source.scale
  transfer_to_partial : StrengthenedToPartialConsistencyLowerBoundTransfer

abbrev RawPudlakToPudlakStrengthenedProjection
    (raw : ℕ → FormulaCode) : Prop :=
  ProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    raw pudlakStrengthenedFiniteConsistencyCode

abbrev RawPudlakToPudlakStrengthenedLinearProjection
    (raw : ℕ → FormulaCode) :=
  LinearProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    raw pudlakStrengthenedFiniteConsistencyCode

abbrev RawPudlakToPudlakStrengthenedConstantProjection
    (raw : ℕ → FormulaCode) :=
  ConstantProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    raw pudlakStrengthenedFiniteConsistencyCode

abbrev RawPudlakToPudlakStrengthenedTransfer
    (raw : ℕ → FormulaCode) : Prop :=
  StrongLowerBoundTransfer
    ProofSystem.PA ProofLengthMeasure.symbolSize
    raw pudlakStrengthenedFiniteConsistencyCode

structure RawPudlakStrengthenedEncodingCalibration where
  raw : ℕ → FormulaCode
  transfer_to_pudlak :
    RawPudlakToPudlakStrengthenedTransfer raw

structure RawPudlakStrengthenedLowerBoundSource where
  raw : ℕ → FormulaCode
  strong_lower_bound :
    StrongProofLengthLowerBound
      ProofSystem.PA ProofLengthMeasure.symbolSize raw
  calibration : RawPudlakStrengthenedEncodingCalibration
  calibration_raw_eq : calibration.raw = raw

abbrev RescaledRawPudlakToRescaledPudlakStrengthenedProjection
    (raw : ℕ → FormulaCode) (ρ : ℕ → ℕ) : Prop :=
  ProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledExternalStrengthenedLowerBoundCode raw ρ)
    (rescaledPudlakStrengthenedFiniteConsistencyCode ρ)

abbrev RescaledRawPudlakToRescaledPudlakStrengthenedLinearProjection
    (raw : ℕ → FormulaCode) (ρ : ℕ → ℕ) :=
  LinearProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledExternalStrengthenedLowerBoundCode raw ρ)
    (rescaledPudlakStrengthenedFiniteConsistencyCode ρ)

abbrev RescaledRawPudlakToRescaledPudlakStrengthenedConstantProjection
    (raw : ℕ → FormulaCode) (ρ : ℕ → ℕ) :=
  ConstantProofLengthProjection
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledExternalStrengthenedLowerBoundCode raw ρ)
    (rescaledPudlakStrengthenedFiniteConsistencyCode ρ)

abbrev RescaledRawPudlakToRescaledPudlakStrengthenedTransfer
    (raw : ℕ → FormulaCode) (ρ : ℕ → ℕ) : Prop :=
  StrongLowerBoundTransfer
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledExternalStrengthenedLowerBoundCode raw ρ)
    (rescaledPudlakStrengthenedFiniteConsistencyCode ρ)

structure RescaledRawPudlakStrengthenedEncodingCalibration where
  raw : ℕ → FormulaCode
  scale : ℕ → ℕ
  transfer_to_rescaled_pudlak :
    RescaledRawPudlakToRescaledPudlakStrengthenedTransfer raw scale

structure RescaledRawPudlakStrengthenedLowerBoundSource where
  raw : ℕ → FormulaCode
  scale : ℕ → ℕ
  scale_properties : PolynomialCofinalScale scale
  rescaled_strong_lower_bound :
    StrongRescaledExternalStrengthenedLowerBound raw scale
  calibration : RescaledRawPudlakStrengthenedEncodingCalibration
  calibration_raw_eq : calibration.raw = raw
  calibration_scale_eq : calibration.scale = scale

structure StrengthenedConsistencyRescalingPackage where
  scale : ℕ → ℕ
  rescaled_strong_lower_bound :
    StrongRescaledStrengthenedPartialConsistencyLowerBound scale
  transfer_to_strengthened :
    RescaledStrengthenedToStrengthenedLowerBoundTransfer scale
  transfer_to_partial : StrengthenedToPartialConsistencyLowerBoundTransfer

structure StrengthenedTimeConstructibleRescalingTheorem where
  scale : ℕ → ℕ
  scale_properties : PolynomialCofinalScale scale
  rescaled_strong_lower_bound :
    StrongRescaledStrengthenedPartialConsistencyLowerBound scale
  transfer_to_partial : StrengthenedToPartialConsistencyLowerBoundTransfer

structure StrengthenedFiniteConsistencyLowerBoundPackage where
  strong_lower_bound : StrongStrengthenedPartialConsistencyLowerBound
  transfer_to_partial : StrengthenedToPartialConsistencyLowerBoundTransfer

structure StrengthenedFiniteConsistencyAcceptedPackage where
  accepted_truth : StrengthenedPartialConsistencyAcceptedTruth
  lower_bound_package : StrengthenedFiniteConsistencyLowerBoundPackage

def StrengthenedFiniteConsistencyAcceptedPackage.ofPayloadTruth
    (htruth : StrengthenedPartialConsistencyPayloadTruth)
    (hlower : StrongStrengthenedPartialConsistencyLowerBound)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    StrengthenedFiniteConsistencyAcceptedPackage where
  accepted_truth := htruth.toAcceptedTruth
  lower_bound_package := {
    strong_lower_bound := hlower
    transfer_to_partial := hpartial }

def StrengthenedFiniteConsistencyAcceptedPackage.toPayloadTruth
    (h : StrengthenedFiniteConsistencyAcceptedPackage) :
    StrengthenedPartialConsistencyPayloadTruth :=
  h.accepted_truth.toPayloadTruth

def StrengthenedFiniteConsistencyAcceptedPackage.toLowerBoundPackage
    (h : StrengthenedFiniteConsistencyAcceptedPackage) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  h.lower_bound_package

structure PartialConsistencyLowerBoundNormalForm where
  code : ℕ → FormulaCode
  strong_lower_bound :
    StrongProofLengthLowerBound
      ProofSystem.PA ProofLengthMeasure.symbolSize code
  transfer_to_partial :
    StrongLowerBoundTransfer
      ProofSystem.PA ProofLengthMeasure.symbolSize code partialConsistencyCode

structure PartialConsistencyCollisionStandard where
  inputs :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode

structure PartialConsistencySpecProvider where
  toSpecPackage : PartialConsistencyPayloadSpec → PartialConsistencySpecExternalPackage

structure PartialConsistencyFixedSpecProvider where
  specPackage : PartialConsistencySpecExternalPackage

theorem PartialConsistencyCollisionStandard.collision
    (h : PartialConsistencyCollisionStandard) :
    ¬ (is_rational euler_mascheroni) :=
  partial_consistency_collapse_lower_bound_collision h.inputs

def PartialConsistencyCollisionStandard.ofSpecPackage
    (h : PartialConsistencySpecExternalPackage)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    PartialConsistencyCollisionStandard where
  inputs := eventual_partial_consistency_inputs_of_spec_package h hver

def PartialConsistencyCollisionStandard.ofTrace
    (h : PartialConsistencySpecExternalPackage)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard where
  inputs :=
    eventual_partial_consistency_inputs_of_spec_package_and_trace
      h hrealize hembed

def PartialConsistencySpecProvider.toCollisionStandard
    (h : PartialConsistencySpecProvider)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    PartialConsistencyCollisionStandard :=
  PartialConsistencyCollisionStandard.ofSpecPackage
    (h.toSpecPackage hspec) hver

def PartialConsistencySpecProvider.toCollisionStandardOfTrace
    (h : PartialConsistencySpecProvider)
    (hspec : PartialConsistencyPayloadSpec)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  PartialConsistencyCollisionStandard.ofTrace
    (h.toSpecPackage hspec) hrealize hembed

theorem PartialConsistencySpecProvider.collision
    (h : PartialConsistencySpecProvider)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    ¬ (is_rational euler_mascheroni) :=
  (h.toCollisionStandard hspec hver).collision

theorem PartialConsistencySpecProvider.collisionOfTrace
    (h : PartialConsistencySpecProvider)
    (hspec : PartialConsistencyPayloadSpec)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (h.toCollisionStandardOfTrace hspec hrealize hembed).collision

def PartialConsistencyFixedSpecProvider.toCollisionStandard
    (h : PartialConsistencyFixedSpecProvider)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    PartialConsistencyCollisionStandard :=
  PartialConsistencyCollisionStandard.ofSpecPackage h.specPackage hver

def PartialConsistencyFixedSpecProvider.toCollisionStandardOfTrace
    (h : PartialConsistencyFixedSpecProvider)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  PartialConsistencyCollisionStandard.ofTrace h.specPackage hrealize hembed

theorem PartialConsistencyFixedSpecProvider.collision
    (h : PartialConsistencyFixedSpecProvider)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    ¬ (is_rational euler_mascheroni) :=
  (h.toCollisionStandard hver).collision

theorem PartialConsistencyFixedSpecProvider.collisionOfTrace
    (h : PartialConsistencyFixedSpecProvider)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (h.toCollisionStandardOfTrace hrealize hembed).collision

def PartialConsistencyLowerBoundNormalForm.toStrongPartialConsistencyLowerBound
    (h : PartialConsistencyLowerBoundNormalForm) :
    StrongPartialConsistencyLowerBound :=
  h.strong_lower_bound.transfer h.transfer_to_partial

def PartialConsistencyLowerBoundNormalForm.toSpecPackage
    (h : PartialConsistencyLowerBoundNormalForm)
    (hspec : PartialConsistencyPayloadSpec) :
    PartialConsistencySpecExternalPackage where
  payload_spec := hspec
  strong_lower_bound := h.toStrongPartialConsistencyLowerBound

def PartialConsistencyLowerBoundNormalForm.toSpecProvider
    (h : PartialConsistencyLowerBoundNormalForm) :
    PartialConsistencySpecProvider where
  toSpecPackage := h.toSpecPackage

def PartialConsistencyLowerBoundNormalForm.toCollisionStandard
    (h : PartialConsistencyLowerBoundNormalForm)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    PartialConsistencyCollisionStandard :=
  h.toSpecProvider.toCollisionStandard hspec hver

def PartialConsistencyLowerBoundNormalForm.toCollisionStandardOfTrace
    (h : PartialConsistencyLowerBoundNormalForm)
    (hspec : PartialConsistencyPayloadSpec)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toSpecProvider.toCollisionStandardOfTrace hspec hrealize hembed

theorem PartialConsistencyLowerBoundNormalForm.collision
    (h : PartialConsistencyLowerBoundNormalForm)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    ¬ (is_rational euler_mascheroni) :=
  (h.toCollisionStandard hspec hver).collision

theorem PartialConsistencyLowerBoundNormalForm.collisionOfTrace
    (h : PartialConsistencyLowerBoundNormalForm)
    (hspec : PartialConsistencyPayloadSpec)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (h.toCollisionStandardOfTrace hspec hrealize hembed).collision

theorem StrengthenedFiniteConsistencyLowerBoundPackage.toStrongPartialConsistencyLowerBound
    (h : StrengthenedFiniteConsistencyLowerBoundPackage) :
    StrongPartialConsistencyLowerBound :=
  h.strong_lower_bound.transfer h.transfer_to_partial

theorem StrengthenedFiniteConsistencyAcceptedPackage.toStrongPartialConsistencyLowerBound
    (h : StrengthenedFiniteConsistencyAcceptedPackage) :
    StrongPartialConsistencyLowerBound :=
  h.lower_bound_package.toStrongPartialConsistencyLowerBound

theorem strengthened_to_partial_transfer_of_projection
    (hprojection : StrengthenedToPartialConsistencyProjection) :
    StrengthenedToPartialConsistencyLowerBoundTransfer :=
  hprojection.toStrongLowerBoundTransfer

theorem strengthened_to_partial_transfer_of_linear_projection
    (hprojection : StrengthenedToPartialConsistencyLinearProjection) :
    StrengthenedToPartialConsistencyLowerBoundTransfer :=
  hprojection.toStrongLowerBoundTransfer

def StrengthenedToPartialConsistencyConstantProjection.toLinearProjection
    (hprojection : StrengthenedToPartialConsistencyConstantProjection) :
    StrengthenedToPartialConsistencyLinearProjection :=
  hprojection.toLinearProofLengthProjection

theorem strengthened_to_partial_transfer_of_constant_projection
    (hprojection : StrengthenedToPartialConsistencyConstantProjection) :
    StrengthenedToPartialConsistencyLowerBoundTransfer :=
  hprojection.toLinearProjection.toStrongLowerBoundTransfer

structure PartialToStrengthenedAcceptedProjection : Prop where
  accepted_project :
    ∀ n : ℕ, accepted_certificate (partialConsistencyCode n) →
      accepted_certificate (strengthenedPartialConsistencyCode n)

def PartialToStrengthenedAcceptedProjection.toAcceptedCertificateProjection
    (h : PartialToStrengthenedAcceptedProjection) :
    AcceptedCertificateProjection
      strengthenedPartialConsistencyCode partialConsistencyCode where
  accepted_project := h.accepted_project

abbrev PartialToStrengthenedAcceptedProofSystemCalibration
    (haccepted : PartialToStrengthenedAcceptedProjection) : Prop :=
  AcceptedCertificateProjectionToProofLengthCalibration
    ProofSystem.PA ProofLengthMeasure.symbolSize
    haccepted.toAcceptedCertificateProjection

structure StrengthenedToPartialAcceptedProjectionCalibration : Prop where
  accepted_projection : PartialToStrengthenedAcceptedProjection
  proof_system_calibration :
    PartialToStrengthenedAcceptedProofSystemCalibration accepted_projection

def PartialToStrengthenedAcceptedProjection.withProofLengthProjection
    (haccepted : PartialToStrengthenedAcceptedProjection)
    (hprojection : StrengthenedToPartialConsistencyProjection) :
    StrengthenedToPartialAcceptedProjectionCalibration where
  accepted_projection := haccepted
  proof_system_calibration :=
    AcceptedCertificateProjectionToProofLengthCalibration.ofProjection
      hprojection

def PartialToStrengthenedAcceptedProjection.calibrateWithPrinciple
    (haccepted : PartialToStrengthenedAcceptedProjection)
    (hprinciple : PAProofLengthProjectionPrinciple) :
    StrengthenedToPartialAcceptedProjectionCalibration where
  accepted_projection := haccepted
  proof_system_calibration :=
    hprinciple.calibrateAcceptedProjection
      haccepted.toAcceptedCertificateProjection

def PartialToStrengthenedAcceptedProjection.ofStrengthenedAcceptedTruth
    (htruth : StrengthenedPartialConsistencyAcceptedTruth) :
    PartialToStrengthenedAcceptedProjection where
  accepted_project := by
    intro n _
    exact htruth.accepted_all n

def PartialToStrengthenedAcceptedProjection.ofStrengthenedPayloadTruth
    (htruth : StrengthenedPartialConsistencyPayloadTruth) :
    PartialToStrengthenedAcceptedProjection :=
  PartialToStrengthenedAcceptedProjection.ofStrengthenedAcceptedTruth
    htruth.toAcceptedTruth

theorem strengthened_to_partial_projection_of_accepted_projection_principle
    (hprinciple : PAProofLengthProjectionPrinciple)
    (haccepted : PartialToStrengthenedAcceptedProjection) :
    StrengthenedToPartialConsistencyProjection :=
  hprinciple.projection_of_accepted_projection
    strengthenedPartialConsistencyCode partialConsistencyCode
    haccepted.toAcceptedCertificateProjection

theorem strengthened_to_partial_transfer_of_accepted_projection_principle
    (hprinciple : PAProofLengthProjectionPrinciple)
    (haccepted : PartialToStrengthenedAcceptedProjection) :
    StrengthenedToPartialConsistencyLowerBoundTransfer :=
  strengthened_to_partial_transfer_of_projection
    (strengthened_to_partial_projection_of_accepted_projection_principle
      hprinciple haccepted)

theorem StrengthenedToPartialAcceptedProjectionCalibration.toProjection
    (h : StrengthenedToPartialAcceptedProjectionCalibration) :
    StrengthenedToPartialConsistencyProjection :=
  h.proof_system_calibration.proof_length_projection

theorem StrengthenedToPartialAcceptedProjectionCalibration.toTransfer
    (h : StrengthenedToPartialAcceptedProjectionCalibration) :
    StrengthenedToPartialConsistencyLowerBoundTransfer :=
  strengthened_to_partial_transfer_of_projection h.toProjection

def StrengthenedToPartialAcceptedProjectionCalibration.toAcceptedCertificateCalibration
    (h : StrengthenedToPartialAcceptedProjectionCalibration) :
    PAAcceptedCertificateProjectionProofLengthCalibration
      strengthenedPartialConsistencyCode partialConsistencyCode where
  accepted_projection := h.accepted_projection.toAcceptedCertificateProjection
  proof_system_calibration := h.proof_system_calibration

theorem
    StrengthenedToPartialAcceptedProjectionCalibration.toProjection_eq_certificateCalibration
    (h : StrengthenedToPartialAcceptedProjectionCalibration) :
    h.toAcceptedCertificateCalibration.toProofLengthProjection =
      h.toProjection := by
  rfl

def StrengthenedToPartialRelevantCode (code : FormulaCode) : Prop :=
  (∃ n : ℕ, code = strengthenedPartialConsistencyCode n) ∨
    ∃ n : ℕ, code = partialConsistencyCode n

inductive StrengthenedToPartialProofCode
  | strengthened (n : ℕ)
  | ordinary (n : ℕ)

namespace StrengthenedToPartialProofCode

def toFormulaCode : StrengthenedToPartialProofCode → FormulaCode
  | strengthened n => strengthenedPartialConsistencyCode n
  | ordinary n => partialConsistencyCode n

def size : StrengthenedToPartialProofCode → ℕ
  | strengthened n => n
  | ordinary n => n

def checks (c : StrengthenedToPartialProofCode) (code : FormulaCode) : Prop :=
  code = c.toFormulaCode

end StrengthenedToPartialProofCode

def strengthenedToPartialProofCodeSemantics :
    ProofCodeSemantics StrengthenedToPartialRelevantCode where
  Code := StrengthenedToPartialProofCode
  checks := StrengthenedToPartialProofCode.checks
  size := StrengthenedToPartialProofCode.size
  complete := by
    intro code hcode
    rcases hcode with ⟨n, hcode⟩ | ⟨n, hcode⟩
    · subst hcode
      exact ⟨StrengthenedToPartialProofCode.strengthened n, rfl⟩
    · subst hcode
      exact ⟨StrengthenedToPartialProofCode.ordinary n, rfl⟩

theorem strengthenedToPartialProofCodeSemantics_min_strengthened
    (n : ℕ) :
    strengthenedToPartialProofCodeSemantics.minProofCodeSize
        (strengthenedPartialConsistencyCode n) (Or.inl ⟨n, rfl⟩) =
      n := by
  apply Nat.le_antisymm
  · exact
      strengthenedToPartialProofCodeSemantics.minProofCodeSize_le_of_hasProofCodeOfSize
        (Or.inl ⟨n, rfl⟩)
        ⟨StrengthenedToPartialProofCode.strengthened n, rfl, le_rfl⟩
  · rcases
      strengthenedToPartialProofCodeSemantics.hasProofCodeOfSize_minProofCodeSize
        (Or.inl ⟨n, rfl⟩) with ⟨c, hchecks, hsize⟩
    cases c with
    | strengthened m =>
        have hm : n = m := by
          simpa [StrengthenedToPartialProofCode.checks,
            StrengthenedToPartialProofCode.toFormulaCode,
            strengthenedPartialConsistencyCode] using
            congrArg FormulaCode.index hchecks
        subst hm
        exact hsize
    | ordinary m =>
        have hfam := congrArg FormulaCode.family hchecks
        simp [StrengthenedToPartialProofCode.toFormulaCode,
          strengthenedPartialConsistencyCode, partialConsistencyCode] at hfam

theorem strengthenedToPartialProofCodeSemantics_min_partial
    (n : ℕ) :
    strengthenedToPartialProofCodeSemantics.minProofCodeSize
        (partialConsistencyCode n) (Or.inr ⟨n, rfl⟩) =
      n := by
  apply Nat.le_antisymm
  · exact
      strengthenedToPartialProofCodeSemantics.minProofCodeSize_le_of_hasProofCodeOfSize
        (Or.inr ⟨n, rfl⟩)
        ⟨StrengthenedToPartialProofCode.ordinary n, rfl, le_rfl⟩
  · rcases
      strengthenedToPartialProofCodeSemantics.hasProofCodeOfSize_minProofCodeSize
        (Or.inr ⟨n, rfl⟩) with ⟨c, hchecks, hsize⟩
    cases c with
    | strengthened m =>
        have hfam := congrArg FormulaCode.family hchecks
        simp [StrengthenedToPartialProofCode.toFormulaCode,
          strengthenedPartialConsistencyCode, partialConsistencyCode] at hfam
    | ordinary m =>
        have hm : n = m := by
          simpa [StrengthenedToPartialProofCode.checks,
            StrengthenedToPartialProofCode.toFormulaCode,
            partialConsistencyCode] using
            congrArg FormulaCode.index hchecks
        subst hm
        exact hsize

noncomputable def strengthenedToPartialProofLengthCodeSemantics
    (fallback : FormulaCode → ℕ) :
    ProofLengthCodeSemantics.{0}
      ProofSystem.PA ProofLengthMeasure.symbolSize
      StrengthenedToPartialRelevantCode where
  proof_code_semantics := strengthenedToPartialProofCodeSemantics
  fallback_length := fallback

theorem strengthenedToPartialProofLengthCodeSemantics_length_strengthened
    (fallback : FormulaCode → ℕ) (n : ℕ) :
    (strengthenedToPartialProofLengthCodeSemantics fallback).length
        (strengthenedPartialConsistencyCode n) =
      n := by
  rw [ProofLengthCodeSemantics.length]
  rw [ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize]
  exact strengthenedToPartialProofCodeSemantics_min_strengthened n

theorem strengthenedToPartialProofLengthCodeSemantics_length_partial
    (fallback : FormulaCode → ℕ) (n : ℕ) :
    (strengthenedToPartialProofLengthCodeSemantics fallback).length
        (partialConsistencyCode n) =
      n := by
  rw [ProofLengthCodeSemantics.length]
  rw [ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize]
  exact strengthenedToPartialProofCodeSemantics_min_partial n

theorem strengthenedToPartialProofLengthCodeSemantics_semantic_projection
    (fallback : FormulaCode → ℕ) :
    ∀ n : ℕ,
      (strengthenedToPartialProofLengthCodeSemantics fallback).length
          (strengthenedPartialConsistencyCode n) ≤
        (strengthenedToPartialProofLengthCodeSemantics fallback).length
          (partialConsistencyCode n) := by
  intro n
  rw [strengthenedToPartialProofLengthCodeSemantics_length_strengthened,
    strengthenedToPartialProofLengthCodeSemantics_length_partial]

structure StrengthenedToPartialProjectProofLengthExactFamilyLengths : Prop where
  strengthened_length_exact :
    ∀ n : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (strengthenedPartialConsistencyCode n) = n
  partial_length_exact :
    ∀ n : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode n) = n

theorem strengthenedToPartialProofLengthCodeSemantics_calibration_iff_family_lengths
    (fallback : FormulaCode → ℕ) :
    (strengthenedToPartialProofLengthCodeSemantics fallback).Calibration ↔
      (∀ n : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (strengthenedPartialConsistencyCode n) = n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = n) := by
  constructor
  · intro hcal
    refine ⟨?_, ?_⟩
    · intro n
      rw [hcal.proof_length_eq_length
        (strengthenedPartialConsistencyCode n) (Or.inl ⟨n, rfl⟩)]
      exact_mod_cast strengthenedToPartialProofLengthCodeSemantics_length_strengthened
        fallback n
    · intro n
      rw [hcal.proof_length_eq_length
        (partialConsistencyCode n) (Or.inr ⟨n, rfl⟩)]
      exact_mod_cast strengthenedToPartialProofLengthCodeSemantics_length_partial
        fallback n
  · rintro ⟨hstrengthened, hpartial⟩
    refine ⟨?_⟩
    intro code hcode
    rcases hcode with ⟨n, hcode_eq⟩ | ⟨n, hcode_eq⟩
    · subst hcode_eq
      rw [hstrengthened n,
        strengthenedToPartialProofLengthCodeSemantics_length_strengthened
          fallback n]
    · subst hcode_eq
      rw [hpartial n,
        strengthenedToPartialProofLengthCodeSemantics_length_partial
          fallback n]

structure StrengthenedToPartialProjectProofLengthFamilyWitness
    (fallback : FormulaCode → ℕ) : Prop where
  strengthened_length_eq :
    ∀ n : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (strengthenedPartialConsistencyCode n) =
        (strengthenedToPartialProofLengthCodeSemantics fallback).length
          (strengthenedPartialConsistencyCode n)
  partial_length_eq :
    ∀ n : ℕ,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode n) =
        (strengthenedToPartialProofLengthCodeSemantics fallback).length
          (partialConsistencyCode n)

def StrengthenedToPartialProjectProofLengthExactFamilyLengths.toFamilyWitness
    (fallback : FormulaCode → ℕ)
    (hexact : StrengthenedToPartialProjectProofLengthExactFamilyLengths) :
    StrengthenedToPartialProjectProofLengthFamilyWitness fallback where
  strengthened_length_eq := by
    intro n
    rw [hexact.strengthened_length_exact n]
    exact_mod_cast
      (strengthenedToPartialProofLengthCodeSemantics_length_strengthened
        fallback n).symm
  partial_length_eq := by
    intro n
    rw [hexact.partial_length_exact n]
    exact_mod_cast
      (strengthenedToPartialProofLengthCodeSemantics_length_partial
        fallback n).symm

def StrengthenedToPartialProjectProofLengthFamilyWitness.toExactFamilyLengths
    {fallback : FormulaCode → ℕ}
    (hwit : StrengthenedToPartialProjectProofLengthFamilyWitness fallback) :
    StrengthenedToPartialProjectProofLengthExactFamilyLengths where
  strengthened_length_exact := by
    intro n
    rw [hwit.strengthened_length_eq n]
    exact_mod_cast
      strengthenedToPartialProofLengthCodeSemantics_length_strengthened
        fallback n
  partial_length_exact := by
    intro n
    rw [hwit.partial_length_eq n]
    exact_mod_cast
      strengthenedToPartialProofLengthCodeSemantics_length_partial
        fallback n

theorem strengthenedToPartialFamilyWitness_iff_exactFamilyLengths
    (fallback : FormulaCode → ℕ) :
    StrengthenedToPartialProjectProofLengthFamilyWitness fallback ↔
      StrengthenedToPartialProjectProofLengthExactFamilyLengths :=
  ⟨StrengthenedToPartialProjectProofLengthFamilyWitness.toExactFamilyLengths,
    StrengthenedToPartialProjectProofLengthExactFamilyLengths.toFamilyWitness
      fallback⟩

def StrengthenedToPartialProjectProofLengthExactFamilyLengths.toCalibration
    (fallback : FormulaCode → ℕ)
    (hexact : StrengthenedToPartialProjectProofLengthExactFamilyLengths) :
    (strengthenedToPartialProofLengthCodeSemantics fallback).Calibration :=
  (strengthenedToPartialProofLengthCodeSemantics_calibration_iff_family_lengths
    fallback).2
    ⟨hexact.strengthened_length_exact, hexact.partial_length_exact⟩

def StrengthenedToPartialProjectProofLengthExactFamilyLengths.ofCalibration
    (fallback : FormulaCode → ℕ)
    (hcal :
      (strengthenedToPartialProofLengthCodeSemantics fallback).Calibration) :
    StrengthenedToPartialProjectProofLengthExactFamilyLengths where
  strengthened_length_exact :=
    ((strengthenedToPartialProofLengthCodeSemantics_calibration_iff_family_lengths
      fallback).1 hcal).1
  partial_length_exact :=
    ((strengthenedToPartialProofLengthCodeSemantics_calibration_iff_family_lengths
      fallback).1 hcal).2

theorem strengthenedToPartialCalibration_iff_exactFamilyLengths
    (fallback : FormulaCode → ℕ) :
    (strengthenedToPartialProofLengthCodeSemantics fallback).Calibration ↔
      StrengthenedToPartialProjectProofLengthExactFamilyLengths :=
  ⟨StrengthenedToPartialProjectProofLengthExactFamilyLengths.ofCalibration
      fallback,
    StrengthenedToPartialProjectProofLengthExactFamilyLengths.toCalibration
      fallback⟩

def StrengthenedToPartialProjectProofLengthFamilyWitness.toProjectProofLengthSemantics
    {fallback : FormulaCode → ℕ}
    (hwit : StrengthenedToPartialProjectProofLengthFamilyWitness fallback) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      (strengthenedToPartialProofLengthCodeSemantics fallback).length
      StrengthenedToPartialRelevantCode where
  proof_length_eq := by
    intro code hcode
    rcases hcode with ⟨n, hcode_eq⟩ | ⟨n, hcode_eq⟩
    · subst hcode_eq
      exact hwit.strengthened_length_eq n
    · subst hcode_eq
      exact hwit.partial_length_eq n

def StrengthenedToPartialProjectProofLengthFamilyWitness.ofProjectProofLengthSemantics
    (fallback : FormulaCode → ℕ)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        (strengthenedToPartialProofLengthCodeSemantics fallback).length
        StrengthenedToPartialRelevantCode) :
    StrengthenedToPartialProjectProofLengthFamilyWitness fallback where
  strengthened_length_eq := by
    intro n
    exact hsem.proof_length_eq
      (strengthenedPartialConsistencyCode n) (Or.inl ⟨n, rfl⟩)
  partial_length_eq := by
    intro n
    exact hsem.proof_length_eq
      (partialConsistencyCode n) (Or.inr ⟨n, rfl⟩)

theorem strengthenedToPartialProjectProofLengthSemantics_iff_familyWitness
    (fallback : FormulaCode → ℕ) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      (strengthenedToPartialProofLengthCodeSemantics fallback).length
      StrengthenedToPartialRelevantCode ↔
      StrengthenedToPartialProjectProofLengthFamilyWitness fallback :=
  ⟨fun hsem =>
      StrengthenedToPartialProjectProofLengthFamilyWitness.ofProjectProofLengthSemantics
        fallback hsem,
    fun hwit => hwit.toProjectProofLengthSemantics⟩

theorem strengthenedToPartialProjectProofLengthSemantics_iff_exactFamilyLengths
    (fallback : FormulaCode → ℕ) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      (strengthenedToPartialProofLengthCodeSemantics fallback).length
      StrengthenedToPartialRelevantCode ↔
      StrengthenedToPartialProjectProofLengthExactFamilyLengths :=
  (strengthenedToPartialProjectProofLengthSemantics_iff_familyWitness
    fallback).trans
    (strengthenedToPartialFamilyWitness_iff_exactFamilyLengths fallback)

def StrengthenedToPartialProjectProofLengthExactFamilyLengths.toProjectProofLengthSemantics
    (fallback : FormulaCode → ℕ)
    (hexact : StrengthenedToPartialProjectProofLengthExactFamilyLengths) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      (strengthenedToPartialProofLengthCodeSemantics fallback).length
      StrengthenedToPartialRelevantCode :=
  (strengthenedToPartialProjectProofLengthSemantics_iff_exactFamilyLengths
    fallback).2 hexact

structure StrengthenedToPartialConcreteProofLengthRecognition : Prop where
  recognizes_minProofCodeSize :
    ∀ code : FormulaCode, ∀ hcode : StrengthenedToPartialRelevantCode code,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
        strengthenedToPartialProofCodeSemantics.minProofCodeSize code hcode

theorem StrengthenedToPartialConcreteProofLengthRecognition.toCalibration
    (hrec : StrengthenedToPartialConcreteProofLengthRecognition)
    (fallback : FormulaCode → ℕ) :
    (strengthenedToPartialProofLengthCodeSemantics fallback).Calibration where
  proof_length_eq_length := by
    intro code hcode
    rw [hrec.recognizes_minProofCodeSize code hcode]
    rw [ProofLengthCodeSemantics.length]
    exact_mod_cast (ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize
      strengthenedToPartialProofCodeSemantics fallback hcode).symm

theorem StrengthenedToPartialConcreteProofLengthRecognition.ofCalibration
    (fallback : FormulaCode → ℕ)
    (hcal :
      (strengthenedToPartialProofLengthCodeSemantics fallback).Calibration) :
    StrengthenedToPartialConcreteProofLengthRecognition where
  recognizes_minProofCodeSize := by
    intro code hcode
    rw [hcal.proof_length_eq_length code hcode]
    rw [ProofLengthCodeSemantics.length]
    exact_mod_cast ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize
      strengthenedToPartialProofCodeSemantics fallback hcode

theorem strengthenedToPartialConcreteRecognition_iff_calibration
    (fallback : FormulaCode → ℕ) :
    StrengthenedToPartialConcreteProofLengthRecognition ↔
      (strengthenedToPartialProofLengthCodeSemantics fallback).Calibration :=
  ⟨fun hrec => hrec.toCalibration fallback,
    StrengthenedToPartialConcreteProofLengthRecognition.ofCalibration
      fallback⟩

theorem strengthenedToPartialConcreteRecognition_iff_family_lengths
    (fallback : FormulaCode → ℕ) :
    StrengthenedToPartialConcreteProofLengthRecognition ↔
      (∀ n : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (strengthenedPartialConsistencyCode n) = n) ∧
      (∀ n : ℕ,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode n) = n) :=
  (strengthenedToPartialConcreteRecognition_iff_calibration fallback).trans
    (strengthenedToPartialProofLengthCodeSemantics_calibration_iff_family_lengths
      fallback)

/-- Proof-length convention for the fixed strengthened-to-partial checker.

It states that the project-level PA proof length agrees with the semantic
length induced by `strengthenedToPartialProofLengthCodeSemantics` on the two
relevant formula families. -/
structure StrengthenedToPartialProofLengthConvention where
  fallback : FormulaCode → ℕ
  proof_length_eq_length :
    ∀ code : FormulaCode, StrengthenedToPartialRelevantCode code →
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
        (strengthenedToPartialProofLengthCodeSemantics fallback).length code

def StrengthenedToPartialProofLengthConvention.toCalibration
    (hconv : StrengthenedToPartialProofLengthConvention) :
    (strengthenedToPartialProofLengthCodeSemantics
      hconv.fallback).Calibration where
  proof_length_eq_length := hconv.proof_length_eq_length

def StrengthenedToPartialProofLengthConvention.ofCalibration
    (fallback : FormulaCode → ℕ)
    (hcal :
      (strengthenedToPartialProofLengthCodeSemantics fallback).Calibration) :
    StrengthenedToPartialProofLengthConvention where
  fallback := fallback
  proof_length_eq_length := hcal.proof_length_eq_length

def StrengthenedToPartialProofLengthConvention.ofProjectProofLengthSemantics
    (fallback : FormulaCode → ℕ)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        (strengthenedToPartialProofLengthCodeSemantics fallback).length
        StrengthenedToPartialRelevantCode) :
    StrengthenedToPartialProofLengthConvention where
  fallback := fallback
  proof_length_eq_length := hsem.proof_length_eq

def StrengthenedToPartialProofLengthConvention.toProjectProofLengthSemantics
    (hconv : StrengthenedToPartialProofLengthConvention) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      (strengthenedToPartialProofLengthCodeSemantics hconv.fallback).length
      StrengthenedToPartialRelevantCode where
  proof_length_eq := hconv.proof_length_eq_length

structure StrengthenedToPartialCanonicalCheckerExactness
    (fallback : FormulaCode → ℕ) : Prop where
  length_eq_minProofCodeSize :
    ∀ code : FormulaCode, ∀ hcode : StrengthenedToPartialRelevantCode code,
      (strengthenedToPartialProofLengthCodeSemantics fallback).length code =
        strengthenedToPartialProofCodeSemantics.minProofCodeSize code hcode

theorem strengthenedToPartialCanonicalCheckerExactness
    (fallback : FormulaCode → ℕ) :
    StrengthenedToPartialCanonicalCheckerExactness fallback where
  length_eq_minProofCodeSize := by
    intro code hcode
    rw [ProofLengthCodeSemantics.length]
    exact
      ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize
        strengthenedToPartialProofCodeSemantics fallback hcode

structure StrengthenedToPartialCanonicalRecognitionCertificate where
  convention : StrengthenedToPartialProofLengthConvention
  checker_exactness :
    StrengthenedToPartialCanonicalCheckerExactness convention.fallback

theorem StrengthenedToPartialCanonicalRecognitionCertificate.toConcreteRecognition
    (hcert : StrengthenedToPartialCanonicalRecognitionCertificate) :
    StrengthenedToPartialConcreteProofLengthRecognition where
  recognizes_minProofCodeSize := by
    intro code hcode
    rw [hcert.convention.proof_length_eq_length code hcode]
    exact_mod_cast
      hcert.checker_exactness.length_eq_minProofCodeSize code hcode

def StrengthenedToPartialCanonicalRecognitionCertificate.toCalibration
    (hcert : StrengthenedToPartialCanonicalRecognitionCertificate) :
    (strengthenedToPartialProofLengthCodeSemantics
      hcert.convention.fallback).Calibration :=
  hcert.convention.toCalibration

def StrengthenedToPartialCanonicalRecognitionCertificate.ofProjectProofLengthSemantics
    (fallback : FormulaCode → ℕ)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        (strengthenedToPartialProofLengthCodeSemantics fallback).length
        StrengthenedToPartialRelevantCode) :
    StrengthenedToPartialCanonicalRecognitionCertificate where
  convention :=
    StrengthenedToPartialProofLengthConvention.ofProjectProofLengthSemantics
      fallback hsem
  checker_exactness :=
    strengthenedToPartialCanonicalCheckerExactness fallback

def StrengthenedToPartialProjectProofLengthFamilyWitness.toProofLengthConvention
    {fallback : FormulaCode → ℕ}
    (hwit : StrengthenedToPartialProjectProofLengthFamilyWitness fallback) :
    StrengthenedToPartialProofLengthConvention :=
  StrengthenedToPartialProofLengthConvention.ofProjectProofLengthSemantics
    fallback hwit.toProjectProofLengthSemantics

def StrengthenedToPartialProjectProofLengthFamilyWitness.toCanonicalRecognitionCertificate
    {fallback : FormulaCode → ℕ}
    (hwit : StrengthenedToPartialProjectProofLengthFamilyWitness fallback) :
    StrengthenedToPartialCanonicalRecognitionCertificate :=
  StrengthenedToPartialCanonicalRecognitionCertificate.ofProjectProofLengthSemantics
    fallback hwit.toProjectProofLengthSemantics

def StrengthenedToPartialConcreteProofLengthRecognition.toProofLengthConvention
    (hrec : StrengthenedToPartialConcreteProofLengthRecognition)
    (fallback : FormulaCode → ℕ) :
    StrengthenedToPartialProofLengthConvention :=
  StrengthenedToPartialProofLengthConvention.ofCalibration
    fallback (hrec.toCalibration fallback)

def StrengthenedToPartialConcreteProofLengthRecognition.toCanonicalRecognitionCertificate
    (hrec : StrengthenedToPartialConcreteProofLengthRecognition)
    (fallback : FormulaCode → ℕ) :
    StrengthenedToPartialCanonicalRecognitionCertificate where
  convention := hrec.toProofLengthConvention fallback
  checker_exactness :=
    strengthenedToPartialCanonicalCheckerExactness fallback

theorem strengthenedToPartialConcreteRecognition_iff_canonicalCertificate :
    StrengthenedToPartialConcreteProofLengthRecognition ↔
      Nonempty StrengthenedToPartialCanonicalRecognitionCertificate := by
  constructor
  · intro hrec
    exact
      ⟨hrec.toCanonicalRecognitionCertificate (fun _ => 0)⟩
  · intro hcert
    rcases hcert with ⟨hcert⟩
    exact hcert.toConcreteRecognition

/-- External project convention for the strengthened-to-partial checker.

This is a named calibration input, not an internal proof: it identifies the
project-level PA proof length with the fixed strengthened-to-partial checked
code length on the relevant fragment. -/
axiom externalStrengthenedToPartialProofLengthConvention_eq_length :
  ∀ code : FormulaCode, StrengthenedToPartialRelevantCode code →
    proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
      (strengthenedToPartialProofLengthCodeSemantics (fun _ => 0)).length code

noncomputable def externalStrengthenedToPartialProofLengthConvention :
    StrengthenedToPartialProofLengthConvention where
  fallback := fun _ => 0
  proof_length_eq_length :=
    externalStrengthenedToPartialProofLengthConvention_eq_length

noncomputable def externalStrengthenedToPartialCanonicalRecognitionCertificate :
    StrengthenedToPartialCanonicalRecognitionCertificate where
  convention := externalStrengthenedToPartialProofLengthConvention
  checker_exactness :=
    strengthenedToPartialCanonicalCheckerExactness (fun _ => 0)

-- Code-semantics version of the strengthened-to-partial projection
-- calibration.  A concrete checker for just these two formula families can
-- instantiate `code_model`; the calibration field identifies its semantic
-- length with the project-level PA proof length on the relevant fragment.
structure StrengthenedToPartialProofLengthCodeProjectionCalibration where
  code_model :
    ProofLengthCodeSemantics.{q}
      ProofSystem.PA ProofLengthMeasure.symbolSize
      StrengthenedToPartialRelevantCode
  code_calibration : code_model.Calibration
  semantic_projection :
    ∀ n : ℕ,
      code_model.length (strengthenedPartialConsistencyCode n) ≤
        code_model.length (partialConsistencyCode n)

theorem StrengthenedToPartialProofLengthCodeProjectionCalibration.toProjection
    (h : StrengthenedToPartialProofLengthCodeProjectionCalibration) :
    StrengthenedToPartialConsistencyProjection where
  source_le_target := by
    intro n
    rw [
      h.code_calibration.proof_length_eq_length
        (strengthenedPartialConsistencyCode n) (Or.inl ⟨n, rfl⟩),
      h.code_calibration.proof_length_eq_length
        (partialConsistencyCode n) (Or.inr ⟨n, rfl⟩)]
    exact_mod_cast h.semantic_projection n

def StrengthenedToPartialProofLengthCodeProjectionCalibration.toAcceptedCalibration
    (h : StrengthenedToPartialProofLengthCodeProjectionCalibration)
    (haccepted : PartialToStrengthenedAcceptedProjection) :
    StrengthenedToPartialAcceptedProjectionCalibration :=
  haccepted.withProofLengthProjection h.toProjection

def StrengthenedToPartialProofLengthCodeProjectionCalibration.toProofSystemCalibration
    (h : StrengthenedToPartialProofLengthCodeProjectionCalibration)
    (haccepted : PartialToStrengthenedAcceptedProjection) :
    PartialToStrengthenedAcceptedProofSystemCalibration haccepted :=
  (h.toAcceptedCalibration haccepted).proof_system_calibration

structure StrengthenedToPartialConcreteProofCodeProjectionCalibration where
  fallback : FormulaCode → ℕ
  code_calibration :
    (strengthenedToPartialProofLengthCodeSemantics fallback).Calibration

def StrengthenedToPartialConcreteProofLengthRecognition.toConcreteProjectionCalibration
    (hrec : StrengthenedToPartialConcreteProofLengthRecognition)
    (fallback : FormulaCode → ℕ) :
    StrengthenedToPartialConcreteProofCodeProjectionCalibration where
  fallback := fallback
  code_calibration := hrec.toCalibration fallback

noncomputable def
    StrengthenedToPartialConcreteProofCodeProjectionCalibration.toCodeProjectionCalibration
    (h : StrengthenedToPartialConcreteProofCodeProjectionCalibration) :
    StrengthenedToPartialProofLengthCodeProjectionCalibration where
  code_model := strengthenedToPartialProofLengthCodeSemantics h.fallback
  code_calibration := h.code_calibration
  semantic_projection :=
    strengthenedToPartialProofLengthCodeSemantics_semantic_projection
      h.fallback

noncomputable def StrengthenedToPartialConcreteProofCodeProjectionCalibration.toProjection
    (h : StrengthenedToPartialConcreteProofCodeProjectionCalibration) :
    StrengthenedToPartialConsistencyProjection :=
  h.toCodeProjectionCalibration.toProjection

noncomputable def StrengthenedToPartialConcreteProofCodeProjectionCalibration.toAcceptedCalibration
    (h : StrengthenedToPartialConcreteProofCodeProjectionCalibration)
    (haccepted : PartialToStrengthenedAcceptedProjection) :
    StrengthenedToPartialAcceptedProjectionCalibration :=
  h.toCodeProjectionCalibration.toAcceptedCalibration haccepted

structure StrengthenedToPartialAcceptedProjectionPackage : Prop where
  proof_length_projection_principle : PAProofLengthProjectionPrinciple
  accepted_projection : PartialToStrengthenedAcceptedProjection

def StrengthenedToPartialAcceptedProjectionPackage.toCalibration
    (h : StrengthenedToPartialAcceptedProjectionPackage) :
    StrengthenedToPartialAcceptedProjectionCalibration :=
  h.accepted_projection.calibrateWithPrinciple
    h.proof_length_projection_principle

def StrengthenedToPartialAcceptedProjectionPackage.ofStrengthenedAcceptedTruth
    (hprinciple : PAProofLengthProjectionPrinciple)
    (htruth : StrengthenedPartialConsistencyAcceptedTruth) :
    StrengthenedToPartialAcceptedProjectionPackage where
  proof_length_projection_principle := hprinciple
  accepted_projection :=
    PartialToStrengthenedAcceptedProjection.ofStrengthenedAcceptedTruth htruth

def StrengthenedToPartialAcceptedProjectionPackage.ofStrengthenedPayloadTruth
    (hprinciple : PAProofLengthProjectionPrinciple)
    (htruth : StrengthenedPartialConsistencyPayloadTruth) :
    StrengthenedToPartialAcceptedProjectionPackage :=
  StrengthenedToPartialAcceptedProjectionPackage.ofStrengthenedAcceptedTruth
    hprinciple htruth.toAcceptedTruth

theorem StrengthenedToPartialAcceptedProjectionPackage.toProjection
    (h : StrengthenedToPartialAcceptedProjectionPackage) :
    StrengthenedToPartialConsistencyProjection :=
  h.toCalibration.toProjection

theorem StrengthenedToPartialAcceptedProjectionPackage.toTransfer
    (h : StrengthenedToPartialAcceptedProjectionPackage) :
    StrengthenedToPartialConsistencyLowerBoundTransfer :=
  h.toCalibration.toTransfer

theorem rescaled_strengthened_transfer_of_polynomial_cofinal_scale
    {ρ : ℕ → ℕ} (hscale : PolynomialCofinalScale ρ) :
    RescaledStrengthenedToStrengthenedLowerBoundTransfer ρ := by
  change StrongLowerBoundTransfer ProofSystem.PA ProofLengthMeasure.symbolSize
    (fun n : ℕ => strengthenedPartialConsistencyCode (ρ n))
    strengthenedPartialConsistencyCode
  exact StrongLowerBoundTransfer.of_polynomial_cofinal_scale
    (T := ProofSystem.PA) (measure := ProofLengthMeasure.symbolSize)
    (φ := strengthenedPartialConsistencyCode) hscale

theorem source_to_strengthened_transfer_of_projection
    {source : ℕ → FormulaCode}
    (hprojection : SourceToStrengthenedProjection source) :
    SourceToStrengthenedLowerBoundTransfer source :=
  hprojection.toStrongLowerBoundTransfer

theorem source_to_strengthened_transfer_of_linear_projection
    {source : ℕ → FormulaCode}
    (hprojection : SourceToStrengthenedLinearProjection source) :
    SourceToStrengthenedLowerBoundTransfer source :=
  hprojection.toStrongLowerBoundTransfer

def SourceToStrengthenedConstantProjection.toLinearProjection
    {source : ℕ → FormulaCode}
    (hprojection : SourceToStrengthenedConstantProjection source) :
    SourceToStrengthenedLinearProjection source :=
  hprojection.toLinearProofLengthProjection

theorem source_to_strengthened_transfer_of_constant_projection
    {source : ℕ → FormulaCode}
    (hprojection : SourceToStrengthenedConstantProjection source) :
    SourceToStrengthenedLowerBoundTransfer source :=
  hprojection.toLinearProjection.toStrongLowerBoundTransfer

theorem rescaled_source_to_rescaled_strengthened_transfer_of_projection
    {source : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection : RescaledSourceToRescaledStrengthenedProjection source ρ) :
    RescaledSourceToRescaledStrengthenedLowerBoundTransfer source ρ :=
  hprojection.toStrongLowerBoundTransfer

theorem rescaled_source_to_rescaled_strengthened_transfer_of_linear_projection
    {source : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledSourceToRescaledStrengthenedLinearProjection source ρ) :
    RescaledSourceToRescaledStrengthenedLowerBoundTransfer source ρ :=
  hprojection.toStrongLowerBoundTransfer

def RescaledSourceToRescaledStrengthenedConstantProjection.toLinearProjection
    {source : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledSourceToRescaledStrengthenedConstantProjection source ρ) :
    RescaledSourceToRescaledStrengthenedLinearProjection source ρ :=
  hprojection.toLinearProofLengthProjection

theorem rescaled_source_to_rescaled_strengthened_transfer_of_constant_projection
    {source : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledSourceToRescaledStrengthenedConstantProjection source ρ) :
    RescaledSourceToRescaledStrengthenedLowerBoundTransfer source ρ :=
  hprojection.toLinearProjection.toStrongLowerBoundTransfer

theorem source_to_strengthened_projection_of_pointwise_eq
    {source : ℕ → FormulaCode}
    (hcode : ∀ n : ℕ, source n = strengthenedPartialConsistencyCode n) :
    SourceToStrengthenedProjection source where
  source_le_target := by
    intro n
    rw [hcode n]

def source_to_strengthened_constant_projection_of_pointwise_eq
    {source : ℕ → FormulaCode}
    (hcode : ∀ n : ℕ, source n = strengthenedPartialConsistencyCode n) :
    SourceToStrengthenedConstantProjection source where
  D := 0
  D_nonneg := by norm_num
  source_le_target_add := by
    intro n
    rw [hcode n]
    simp

def source_to_strengthened_linear_projection_of_pointwise_eq
    {source : ℕ → FormulaCode}
    (hcode : ∀ n : ℕ, source n = strengthenedPartialConsistencyCode n) :
    SourceToStrengthenedLinearProjection source :=
  (source_to_strengthened_constant_projection_of_pointwise_eq
    hcode).toLinearProjection

theorem rescaled_source_to_rescaled_strengthened_projection_of_pointwise_eq
    {source : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hcode : ∀ n : ℕ, source n = strengthenedPartialConsistencyCode n) :
    RescaledSourceToRescaledStrengthenedProjection source ρ where
  source_le_target := by
    intro n
    change
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize (source (ρ n)) ≤
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (strengthenedPartialConsistencyCode (ρ n))
    rw [hcode (ρ n)]

def rescaled_source_to_rescaled_strengthened_constant_projection_of_pointwise_eq
    {source : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hcode : ∀ n : ℕ, source n = strengthenedPartialConsistencyCode n) :
    RescaledSourceToRescaledStrengthenedConstantProjection source ρ where
  D := 0
  D_nonneg := by norm_num
  source_le_target_add := by
    intro n
    change
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize (source (ρ n)) ≤
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (strengthenedPartialConsistencyCode (ρ n)) + 0
    rw [hcode (ρ n)]
    simp

def rescaled_source_to_rescaled_strengthened_linear_projection_of_pointwise_eq
    {source : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hcode : ∀ n : ℕ, source n = strengthenedPartialConsistencyCode n) :
    RescaledSourceToRescaledStrengthenedLinearProjection source ρ :=
  (rescaled_source_to_rescaled_strengthened_constant_projection_of_pointwise_eq
    (ρ := ρ) hcode).toLinearProjection

theorem strengthened_identity_projection :
    SourceToStrengthenedProjection strengthenedPartialConsistencyCode :=
  ProofLengthProjection.refl
    ProofSystem.PA ProofLengthMeasure.symbolSize strengthenedPartialConsistencyCode

theorem pudlak_strengthened_to_strengthened_projection :
    SourceToStrengthenedProjection pudlakStrengthenedFiniteConsistencyCode :=
  source_to_strengthened_projection_of_pointwise_eq
    pudlakStrengthenedFiniteConsistencyCode_eq

def pudlak_strengthened_to_strengthened_linear_projection :
    SourceToStrengthenedLinearProjection pudlakStrengthenedFiniteConsistencyCode :=
  source_to_strengthened_linear_projection_of_pointwise_eq
    pudlakStrengthenedFiniteConsistencyCode_eq

def pudlak_strengthened_to_strengthened_constant_projection :
    SourceToStrengthenedConstantProjection pudlakStrengthenedFiniteConsistencyCode :=
  source_to_strengthened_constant_projection_of_pointwise_eq
    pudlakStrengthenedFiniteConsistencyCode_eq

theorem pudlak_strengthened_to_strengthened_transfer :
    SourceToStrengthenedLowerBoundTransfer
      pudlakStrengthenedFiniteConsistencyCode :=
  source_to_strengthened_transfer_of_projection
    pudlak_strengthened_to_strengthened_projection

def strengthened_identity_linear_projection :
    SourceToStrengthenedLinearProjection strengthenedPartialConsistencyCode :=
  LinearProofLengthProjection.refl
    ProofSystem.PA ProofLengthMeasure.symbolSize strengthenedPartialConsistencyCode

def strengthened_identity_constant_projection :
    SourceToStrengthenedConstantProjection strengthenedPartialConsistencyCode :=
  ConstantProofLengthProjection.refl
    ProofSystem.PA ProofLengthMeasure.symbolSize strengthenedPartialConsistencyCode

theorem rescaled_strengthened_identity_projection
    (ρ : ℕ → ℕ) :
    RescaledSourceToRescaledStrengthenedProjection
      strengthenedPartialConsistencyCode ρ :=
  ProofLengthProjection.refl
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledStrengthenedPartialConsistencyCode ρ)

theorem rescaled_pudlak_strengthened_to_rescaled_strengthened_projection
    (ρ : ℕ → ℕ) :
    RescaledSourceToRescaledStrengthenedProjection
      pudlakStrengthenedFiniteConsistencyCode ρ :=
  rescaled_source_to_rescaled_strengthened_projection_of_pointwise_eq
    (ρ := ρ) pudlakStrengthenedFiniteConsistencyCode_eq

def rescaled_pudlak_strengthened_to_rescaled_strengthened_linear_projection
    (ρ : ℕ → ℕ) :
    RescaledSourceToRescaledStrengthenedLinearProjection
      pudlakStrengthenedFiniteConsistencyCode ρ :=
  rescaled_source_to_rescaled_strengthened_linear_projection_of_pointwise_eq
    (ρ := ρ) pudlakStrengthenedFiniteConsistencyCode_eq

def rescaled_pudlak_strengthened_to_rescaled_strengthened_constant_projection
    (ρ : ℕ → ℕ) :
    RescaledSourceToRescaledStrengthenedConstantProjection
      pudlakStrengthenedFiniteConsistencyCode ρ :=
  rescaled_source_to_rescaled_strengthened_constant_projection_of_pointwise_eq
    (ρ := ρ) pudlakStrengthenedFiniteConsistencyCode_eq

theorem rescaled_pudlak_strengthened_to_rescaled_strengthened_transfer
    (ρ : ℕ → ℕ) :
    RescaledSourceToRescaledStrengthenedLowerBoundTransfer
      pudlakStrengthenedFiniteConsistencyCode ρ :=
  rescaled_source_to_rescaled_strengthened_transfer_of_projection
    (rescaled_pudlak_strengthened_to_rescaled_strengthened_projection ρ)

theorem raw_pudlak_to_pudlak_transfer_of_projection
    {raw : ℕ → FormulaCode}
    (hprojection : RawPudlakToPudlakStrengthenedProjection raw) :
    RawPudlakToPudlakStrengthenedTransfer raw :=
  hprojection.toStrongLowerBoundTransfer

theorem raw_pudlak_to_pudlak_transfer_of_linear_projection
    {raw : ℕ → FormulaCode}
    (hprojection : RawPudlakToPudlakStrengthenedLinearProjection raw) :
    RawPudlakToPudlakStrengthenedTransfer raw :=
  hprojection.toStrongLowerBoundTransfer

def RawPudlakToPudlakStrengthenedConstantProjection.toLinearProjection
    {raw : ℕ → FormulaCode}
    (hprojection : RawPudlakToPudlakStrengthenedConstantProjection raw) :
    RawPudlakToPudlakStrengthenedLinearProjection raw :=
  hprojection.toLinearProofLengthProjection

theorem raw_pudlak_to_pudlak_transfer_of_constant_projection
    {raw : ℕ → FormulaCode}
    (hprojection : RawPudlakToPudlakStrengthenedConstantProjection raw) :
    RawPudlakToPudlakStrengthenedTransfer raw :=
  hprojection.toLinearProjection.toStrongLowerBoundTransfer

theorem raw_pudlak_to_pudlak_projection_of_pointwise_eq
    {raw : ℕ → FormulaCode}
    (hcode : ∀ n : ℕ, raw n = pudlakStrengthenedFiniteConsistencyCode n) :
    RawPudlakToPudlakStrengthenedProjection raw where
  source_le_target := by
    intro n
    rw [hcode n]

def raw_pudlak_to_pudlak_constant_projection_of_pointwise_eq
    {raw : ℕ → FormulaCode}
    (hcode : ∀ n : ℕ, raw n = pudlakStrengthenedFiniteConsistencyCode n) :
    RawPudlakToPudlakStrengthenedConstantProjection raw where
  D := 0
  D_nonneg := by norm_num
  source_le_target_add := by
    intro n
    rw [hcode n]
    simp

def raw_pudlak_to_pudlak_linear_projection_of_pointwise_eq
    {raw : ℕ → FormulaCode}
    (hcode : ∀ n : ℕ, raw n = pudlakStrengthenedFiniteConsistencyCode n) :
    RawPudlakToPudlakStrengthenedLinearProjection raw :=
  (raw_pudlak_to_pudlak_constant_projection_of_pointwise_eq
    hcode).toLinearProjection

def RawPudlakStrengthenedEncodingCalibration.of_transfer
    {raw : ℕ → FormulaCode}
    (htransfer : RawPudlakToPudlakStrengthenedTransfer raw) :
    RawPudlakStrengthenedEncodingCalibration where
  raw := raw
  transfer_to_pudlak := htransfer

def RawPudlakStrengthenedEncodingCalibration.of_projection
    {raw : ℕ → FormulaCode}
    (hprojection : RawPudlakToPudlakStrengthenedProjection raw) :
    RawPudlakStrengthenedEncodingCalibration :=
  RawPudlakStrengthenedEncodingCalibration.of_transfer
    (raw_pudlak_to_pudlak_transfer_of_projection hprojection)

def RawPudlakStrengthenedEncodingCalibration.of_linear_projection
    {raw : ℕ → FormulaCode}
    (hprojection : RawPudlakToPudlakStrengthenedLinearProjection raw) :
    RawPudlakStrengthenedEncodingCalibration :=
  RawPudlakStrengthenedEncodingCalibration.of_transfer
    (raw_pudlak_to_pudlak_transfer_of_linear_projection hprojection)

def RawPudlakStrengthenedEncodingCalibration.of_constant_projection
    {raw : ℕ → FormulaCode}
    (hprojection : RawPudlakToPudlakStrengthenedConstantProjection raw) :
    RawPudlakStrengthenedEncodingCalibration :=
  RawPudlakStrengthenedEncodingCalibration.of_transfer
    (raw_pudlak_to_pudlak_transfer_of_constant_projection hprojection)

def RawPudlakStrengthenedEncodingCalibration.of_pointwise_eq
    {raw : ℕ → FormulaCode}
    (hcode : ∀ n : ℕ, raw n = pudlakStrengthenedFiniteConsistencyCode n) :
    RawPudlakStrengthenedEncodingCalibration :=
  RawPudlakStrengthenedEncodingCalibration.of_projection
    (raw_pudlak_to_pudlak_projection_of_pointwise_eq hcode)

theorem rescaled_raw_pudlak_to_rescaled_pudlak_transfer_of_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledRawPudlakToRescaledPudlakStrengthenedProjection raw ρ) :
    RescaledRawPudlakToRescaledPudlakStrengthenedTransfer raw ρ :=
  hprojection.toStrongLowerBoundTransfer

theorem rescaled_raw_pudlak_to_rescaled_pudlak_transfer_of_linear_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledRawPudlakToRescaledPudlakStrengthenedLinearProjection raw ρ) :
    RescaledRawPudlakToRescaledPudlakStrengthenedTransfer raw ρ :=
  hprojection.toStrongLowerBoundTransfer

def RescaledRawPudlakToRescaledPudlakStrengthenedConstantProjection.toLinearProjection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledRawPudlakToRescaledPudlakStrengthenedConstantProjection raw ρ) :
    RescaledRawPudlakToRescaledPudlakStrengthenedLinearProjection raw ρ :=
  hprojection.toLinearProofLengthProjection

theorem rescaled_raw_pudlak_to_rescaled_pudlak_transfer_of_constant_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledRawPudlakToRescaledPudlakStrengthenedConstantProjection raw ρ) :
    RescaledRawPudlakToRescaledPudlakStrengthenedTransfer raw ρ :=
  hprojection.toLinearProjection.toStrongLowerBoundTransfer

theorem rescaled_raw_pudlak_to_rescaled_pudlak_projection_of_pointwise_eq
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hcode : ∀ n : ℕ, raw n = pudlakStrengthenedFiniteConsistencyCode n) :
    RescaledRawPudlakToRescaledPudlakStrengthenedProjection raw ρ where
  source_le_target := by
    intro n
    change
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize (raw (ρ n)) ≤
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (pudlakStrengthenedFiniteConsistencyCode (ρ n))
    rw [hcode (ρ n)]

def rescaled_raw_pudlak_to_rescaled_pudlak_constant_projection_of_pointwise_eq
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hcode : ∀ n : ℕ, raw n = pudlakStrengthenedFiniteConsistencyCode n) :
    RescaledRawPudlakToRescaledPudlakStrengthenedConstantProjection raw ρ where
  D := 0
  D_nonneg := by norm_num
  source_le_target_add := by
    intro n
    change
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize (raw (ρ n)) ≤
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (pudlakStrengthenedFiniteConsistencyCode (ρ n)) + 0
    rw [hcode (ρ n)]
    simp

def rescaled_raw_pudlak_to_rescaled_pudlak_linear_projection_of_pointwise_eq
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hcode : ∀ n : ℕ, raw n = pudlakStrengthenedFiniteConsistencyCode n) :
    RescaledRawPudlakToRescaledPudlakStrengthenedLinearProjection raw ρ :=
  (rescaled_raw_pudlak_to_rescaled_pudlak_constant_projection_of_pointwise_eq
    (ρ := ρ) hcode).toLinearProjection

def RescaledRawPudlakStrengthenedEncodingCalibration.of_transfer
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (htransfer :
      RescaledRawPudlakToRescaledPudlakStrengthenedTransfer raw ρ) :
    RescaledRawPudlakStrengthenedEncodingCalibration where
  raw := raw
  scale := ρ
  transfer_to_rescaled_pudlak := htransfer

def RescaledRawPudlakStrengthenedEncodingCalibration.of_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledRawPudlakToRescaledPudlakStrengthenedProjection raw ρ) :
    RescaledRawPudlakStrengthenedEncodingCalibration :=
  RescaledRawPudlakStrengthenedEncodingCalibration.of_transfer
    (rescaled_raw_pudlak_to_rescaled_pudlak_transfer_of_projection
      hprojection)

def RescaledRawPudlakStrengthenedEncodingCalibration.of_linear_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledRawPudlakToRescaledPudlakStrengthenedLinearProjection raw ρ) :
    RescaledRawPudlakStrengthenedEncodingCalibration :=
  RescaledRawPudlakStrengthenedEncodingCalibration.of_transfer
    (rescaled_raw_pudlak_to_rescaled_pudlak_transfer_of_linear_projection
      hprojection)

def RescaledRawPudlakStrengthenedEncodingCalibration.of_constant_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledRawPudlakToRescaledPudlakStrengthenedConstantProjection raw ρ) :
    RescaledRawPudlakStrengthenedEncodingCalibration :=
  RescaledRawPudlakStrengthenedEncodingCalibration.of_transfer
    (rescaled_raw_pudlak_to_rescaled_pudlak_transfer_of_constant_projection
      hprojection)

def RescaledRawPudlakStrengthenedEncodingCalibration.of_pointwise_eq
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hcode : ∀ n : ℕ, raw n = pudlakStrengthenedFiniteConsistencyCode n) :
    RescaledRawPudlakStrengthenedEncodingCalibration :=
  RescaledRawPudlakStrengthenedEncodingCalibration.of_projection
    (rescaled_raw_pudlak_to_rescaled_pudlak_projection_of_pointwise_eq
      (ρ := ρ) hcode)

def rescaled_strengthened_identity_linear_projection
    (ρ : ℕ → ℕ) :
    RescaledSourceToRescaledStrengthenedLinearProjection
      strengthenedPartialConsistencyCode ρ :=
  LinearProofLengthProjection.refl
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledStrengthenedPartialConsistencyCode ρ)

def rescaled_strengthened_identity_constant_projection
    (ρ : ℕ → ℕ) :
    RescaledSourceToRescaledStrengthenedConstantProjection
      strengthenedPartialConsistencyCode ρ :=
  ConstantProofLengthProjection.refl
    ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledStrengthenedPartialConsistencyCode ρ)

def ExternalStrengthenedLowerBoundSource.toStrongStrengthenedLowerBound
    (h : ExternalStrengthenedLowerBoundSource)
    (htransfer : SourceToStrengthenedLowerBoundTransfer h.code) :
    StrongStrengthenedPartialConsistencyLowerBound :=
  h.strong_lower_bound.transfer htransfer

def ExternalStrengthenedLowerBoundSource.of_strengthened
    (hlower : StrongStrengthenedPartialConsistencyLowerBound) :
    ExternalStrengthenedLowerBoundSource where
  code := strengthenedPartialConsistencyCode
  strong_lower_bound := hlower

def CalibratedExternalStrengthenedLowerBoundSource.of_strengthened
    (hlower : StrongStrengthenedPartialConsistencyLowerBound)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    CalibratedExternalStrengthenedLowerBoundSource where
  source := ExternalStrengthenedLowerBoundSource.of_strengthened hlower
  transfer_to_strengthened :=
    source_to_strengthened_transfer_of_projection
      strengthened_identity_projection
  transfer_to_partial := hpartial

def ExternalStrengthenedLowerBoundSource.of_pointwise_strengthened
    {source : ℕ → FormulaCode}
    (_hcode : ∀ n : ℕ, source n = strengthenedPartialConsistencyCode n)
    (hlower :
      StrongProofLengthLowerBound
        ProofSystem.PA ProofLengthMeasure.symbolSize source) :
    ExternalStrengthenedLowerBoundSource where
  code := source
  strong_lower_bound := hlower

abbrev StrongPudlakStrengthenedFiniteConsistencyLowerBound : Prop :=
  StrongProofLengthLowerBound
    ProofSystem.PA ProofLengthMeasure.symbolSize
    pudlakStrengthenedFiniteConsistencyCode

def ExternalStrengthenedLowerBoundSource.of_pudlak_strengthened
    (hlower : StrongPudlakStrengthenedFiniteConsistencyLowerBound) :
    ExternalStrengthenedLowerBoundSource :=
  ExternalStrengthenedLowerBoundSource.of_pointwise_strengthened
    pudlakStrengthenedFiniteConsistencyCode_eq hlower

def CalibratedExternalStrengthenedLowerBoundSource.of_pudlak_strengthened
    (hlower : StrongPudlakStrengthenedFiniteConsistencyLowerBound)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    CalibratedExternalStrengthenedLowerBoundSource where
  source := ExternalStrengthenedLowerBoundSource.of_pudlak_strengthened hlower
  transfer_to_strengthened := pudlak_strengthened_to_strengthened_transfer
  transfer_to_partial := hpartial

theorem RawPudlakStrengthenedEncodingCalibration.transfer_to_strengthened
    (h : RawPudlakStrengthenedEncodingCalibration) :
    SourceToStrengthenedLowerBoundTransfer h.raw :=
  h.transfer_to_pudlak.comp pudlak_strengthened_to_strengthened_transfer

theorem RescaledRawPudlakStrengthenedEncodingCalibration.transfer_to_rescaled_strengthened
    (h : RescaledRawPudlakStrengthenedEncodingCalibration) :
    RescaledSourceToRescaledStrengthenedLowerBoundTransfer h.raw h.scale :=
  h.transfer_to_rescaled_pudlak.comp
    (rescaled_pudlak_strengthened_to_rescaled_strengthened_transfer h.scale)

def RawPudlakStrengthenedLowerBoundSource.toExternalSource
    (h : RawPudlakStrengthenedLowerBoundSource) :
    ExternalStrengthenedLowerBoundSource where
  code := h.raw
  strong_lower_bound := h.strong_lower_bound

def RawPudlakStrengthenedLowerBoundSource.toCalibratedExternalSource
    (h : RawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    CalibratedExternalStrengthenedLowerBoundSource where
  source := h.toExternalSource
  transfer_to_strengthened := by
    change SourceToStrengthenedLowerBoundTransfer h.raw
    rw [← h.calibration_raw_eq]
    exact h.calibration.transfer_to_strengthened
  transfer_to_partial := hpartial

def RawPudlakStrengthenedLowerBoundSource.toNormalForm
    (h : RawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    PartialConsistencyLowerBoundNormalForm where
  code := h.raw
  strong_lower_bound := h.strong_lower_bound
  transfer_to_partial := by
    rw [← h.calibration_raw_eq]
    exact h.calibration.transfer_to_strengthened.comp hpartial

def RawPudlakStrengthenedLowerBoundSource.of_pointwise_eq
    {raw : ℕ → FormulaCode}
    (hcode : ∀ n : ℕ, raw n = pudlakStrengthenedFiniteConsistencyCode n)
    (hlower :
      StrongProofLengthLowerBound
        ProofSystem.PA ProofLengthMeasure.symbolSize raw) :
    RawPudlakStrengthenedLowerBoundSource where
  raw := raw
  strong_lower_bound := hlower
  calibration := RawPudlakStrengthenedEncodingCalibration.of_pointwise_eq hcode
  calibration_raw_eq := rfl

def RawPudlakStrengthenedLowerBoundSource.of_projection
    {raw : ℕ → FormulaCode}
    (hprojection : RawPudlakToPudlakStrengthenedProjection raw)
    (hlower :
      StrongProofLengthLowerBound
        ProofSystem.PA ProofLengthMeasure.symbolSize raw) :
    RawPudlakStrengthenedLowerBoundSource where
  raw := raw
  strong_lower_bound := hlower
  calibration := RawPudlakStrengthenedEncodingCalibration.of_projection hprojection
  calibration_raw_eq := rfl

def RawPudlakStrengthenedLowerBoundSource.of_linear_projection
    {raw : ℕ → FormulaCode}
    (hprojection : RawPudlakToPudlakStrengthenedLinearProjection raw)
    (hlower :
      StrongProofLengthLowerBound
        ProofSystem.PA ProofLengthMeasure.symbolSize raw) :
    RawPudlakStrengthenedLowerBoundSource where
  raw := raw
  strong_lower_bound := hlower
  calibration :=
    RawPudlakStrengthenedEncodingCalibration.of_linear_projection hprojection
  calibration_raw_eq := rfl

def RescaledRawPudlakStrengthenedLowerBoundSource.toRescaledExternalSource
    (h : RescaledRawPudlakStrengthenedLowerBoundSource) :
    RescaledExternalStrengthenedLowerBoundSource where
  code := h.raw
  scale := h.scale
  scale_properties := h.scale_properties
  rescaled_strong_lower_bound := h.rescaled_strong_lower_bound

def RescaledRawPudlakStrengthenedLowerBoundSource.toCalibratedRescaledExternalSource
    (h : RescaledRawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    CalibratedRescaledExternalStrengthenedLowerBoundSource where
  source := h.toRescaledExternalSource
  transfer_to_rescaled_strengthened := by
    change RescaledSourceToRescaledStrengthenedLowerBoundTransfer h.raw h.scale
    rw [← h.calibration_raw_eq, ← h.calibration_scale_eq]
    exact h.calibration.transfer_to_rescaled_strengthened
  transfer_to_partial := hpartial

def RescaledRawPudlakStrengthenedLowerBoundSource.toNormalForm
    (h : RescaledRawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    PartialConsistencyLowerBoundNormalForm where
  code := rescaledExternalStrengthenedLowerBoundCode h.raw h.scale
  strong_lower_bound := h.rescaled_strong_lower_bound
  transfer_to_partial := by
    have hcal :
        RescaledSourceToRescaledStrengthenedLowerBoundTransfer
          h.raw h.scale := by
      rw [← h.calibration_raw_eq, ← h.calibration_scale_eq]
      exact h.calibration.transfer_to_rescaled_strengthened
    exact hcal.comp
      ((rescaled_strengthened_transfer_of_polynomial_cofinal_scale
        h.scale_properties).comp hpartial)

def RescaledRawPudlakStrengthenedLowerBoundSource.of_pointwise_eq
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hcode : ∀ n : ℕ, raw n = pudlakStrengthenedFiniteConsistencyCode n)
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledExternalStrengthenedLowerBound raw ρ) :
    RescaledRawPudlakStrengthenedLowerBoundSource where
  raw := raw
  scale := ρ
  scale_properties := hscale
  rescaled_strong_lower_bound := hlower
  calibration :=
    RescaledRawPudlakStrengthenedEncodingCalibration.of_pointwise_eq
      (ρ := ρ) hcode
  calibration_raw_eq := rfl
  calibration_scale_eq := rfl

def RescaledRawPudlakStrengthenedLowerBoundSource.of_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledRawPudlakToRescaledPudlakStrengthenedProjection raw ρ)
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledExternalStrengthenedLowerBound raw ρ) :
    RescaledRawPudlakStrengthenedLowerBoundSource where
  raw := raw
  scale := ρ
  scale_properties := hscale
  rescaled_strong_lower_bound := hlower
  calibration :=
    RescaledRawPudlakStrengthenedEncodingCalibration.of_projection
      hprojection
  calibration_raw_eq := rfl
  calibration_scale_eq := rfl

def RescaledRawPudlakStrengthenedLowerBoundSource.of_linear_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledRawPudlakToRescaledPudlakStrengthenedLinearProjection raw ρ)
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledExternalStrengthenedLowerBound raw ρ) :
    RescaledRawPudlakStrengthenedLowerBoundSource where
  raw := raw
  scale := ρ
  scale_properties := hscale
  rescaled_strong_lower_bound := hlower
  calibration :=
    RescaledRawPudlakStrengthenedEncodingCalibration.of_linear_projection
      hprojection
  calibration_raw_eq := rfl
  calibration_scale_eq := rfl

def RescaledRawPudlakStrengthenedLowerBoundSource.of_constant_projection
    {raw : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hprojection :
      RescaledRawPudlakToRescaledPudlakStrengthenedConstantProjection raw ρ)
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledExternalStrengthenedLowerBound raw ρ) :
    RescaledRawPudlakStrengthenedLowerBoundSource where
  raw := raw
  scale := ρ
  scale_properties := hscale
  rescaled_strong_lower_bound := hlower
  calibration :=
    RescaledRawPudlakStrengthenedEncodingCalibration.of_constant_projection
      hprojection
  calibration_raw_eq := rfl
  calibration_scale_eq := rfl

def CalibratedExternalStrengthenedLowerBoundSource.of_pointwise_strengthened
    {source : ℕ → FormulaCode}
    (hcode : ∀ n : ℕ, source n = strengthenedPartialConsistencyCode n)
    (hlower :
      StrongProofLengthLowerBound
        ProofSystem.PA ProofLengthMeasure.symbolSize source)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    CalibratedExternalStrengthenedLowerBoundSource where
  source :=
    ExternalStrengthenedLowerBoundSource.of_pointwise_strengthened
      hcode hlower
  transfer_to_strengthened :=
    source_to_strengthened_transfer_of_projection
      (source_to_strengthened_projection_of_pointwise_eq hcode)
  transfer_to_partial := hpartial

def ExternalStrengthenedLowerBoundSource.toStrongStrengthenedLowerBoundOfProjection
    (h : ExternalStrengthenedLowerBoundSource)
    (hprojection : SourceToStrengthenedProjection h.code) :
    StrongStrengthenedPartialConsistencyLowerBound :=
  h.toStrongStrengthenedLowerBound
    (source_to_strengthened_transfer_of_projection hprojection)

def ExternalStrengthenedLowerBoundSource.toStrongStrengthenedLowerBoundOfLinearProjection
    (h : ExternalStrengthenedLowerBoundSource)
    (hprojection : SourceToStrengthenedLinearProjection h.code) :
    StrongStrengthenedPartialConsistencyLowerBound :=
  h.toStrongStrengthenedLowerBound
    (source_to_strengthened_transfer_of_linear_projection hprojection)

def ExternalStrengthenedLowerBoundSource.toStrongStrengthenedLowerBoundOfConstantProjection
    (h : ExternalStrengthenedLowerBoundSource)
    (hprojection : SourceToStrengthenedConstantProjection h.code) :
    StrongStrengthenedPartialConsistencyLowerBound :=
  h.toStrongStrengthenedLowerBound
    (source_to_strengthened_transfer_of_constant_projection hprojection)

def StrengthenedFiniteConsistencyLowerBoundPackage.of_projection
    (hlower : StrongStrengthenedPartialConsistencyLowerBound)
    (hprojection : StrengthenedToPartialConsistencyProjection) :
    StrengthenedFiniteConsistencyLowerBoundPackage where
  strong_lower_bound := hlower
  transfer_to_partial :=
    strengthened_to_partial_transfer_of_projection hprojection

def StrengthenedFiniteConsistencyLowerBoundPackage.of_linear_projection
    (hlower : StrongStrengthenedPartialConsistencyLowerBound)
    (hprojection : StrengthenedToPartialConsistencyLinearProjection) :
    StrengthenedFiniteConsistencyLowerBoundPackage where
  strong_lower_bound := hlower
  transfer_to_partial :=
    strengthened_to_partial_transfer_of_linear_projection hprojection

def StrengthenedFiniteConsistencyLowerBoundPackage.of_constant_projection
    (hlower : StrongStrengthenedPartialConsistencyLowerBound)
    (hprojection : StrengthenedToPartialConsistencyConstantProjection) :
    StrengthenedFiniteConsistencyLowerBoundPackage where
  strong_lower_bound := hlower
  transfer_to_partial :=
    strengthened_to_partial_transfer_of_constant_projection hprojection

def ExternalStrengthenedLowerBoundSource.toPackage
    (h : ExternalStrengthenedLowerBoundSource)
    (hsource : SourceToStrengthenedLowerBoundTransfer h.code)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    StrengthenedFiniteConsistencyLowerBoundPackage where
  strong_lower_bound := h.toStrongStrengthenedLowerBound hsource
  transfer_to_partial := hpartial

def ExternalStrengthenedLowerBoundSource.toPackageOfProjection
    (h : ExternalStrengthenedLowerBoundSource)
    (hsource : SourceToStrengthenedProjection h.code)
    (hpartial : StrengthenedToPartialConsistencyProjection) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  h.toPackage
    (source_to_strengthened_transfer_of_projection hsource)
    (strengthened_to_partial_transfer_of_projection hpartial)

def ExternalStrengthenedLowerBoundSource.toPackageOfLinearProjection
    (h : ExternalStrengthenedLowerBoundSource)
    (hsource : SourceToStrengthenedLinearProjection h.code)
    (hpartial : StrengthenedToPartialConsistencyLinearProjection) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  h.toPackage
    (source_to_strengthened_transfer_of_linear_projection hsource)
    (strengthened_to_partial_transfer_of_linear_projection hpartial)

def ExternalStrengthenedLowerBoundSource.toPackageOfConstantProjection
    (h : ExternalStrengthenedLowerBoundSource)
    (hsource : SourceToStrengthenedConstantProjection h.code)
    (hpartial : StrengthenedToPartialConsistencyConstantProjection) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  h.toPackage
    (source_to_strengthened_transfer_of_constant_projection hsource)
    (strengthened_to_partial_transfer_of_constant_projection hpartial)

def CalibratedExternalStrengthenedLowerBoundSource.toStrongStrengthenedLowerBound
    (h : CalibratedExternalStrengthenedLowerBoundSource) :
    StrongStrengthenedPartialConsistencyLowerBound :=
  h.source.toStrongStrengthenedLowerBound h.transfer_to_strengthened

def CalibratedExternalStrengthenedLowerBoundSource.toPackage
    (h : CalibratedExternalStrengthenedLowerBoundSource) :
    StrengthenedFiniteConsistencyLowerBoundPackage where
  strong_lower_bound := h.toStrongStrengthenedLowerBound
  transfer_to_partial := h.transfer_to_partial

def StrengthenedFiniteConsistencyLowerBoundPackage.toNormalForm
    (h : StrengthenedFiniteConsistencyLowerBoundPackage) :
    PartialConsistencyLowerBoundNormalForm where
  code := strengthenedPartialConsistencyCode
  strong_lower_bound := h.strong_lower_bound
  transfer_to_partial := h.transfer_to_partial

def StrengthenedFiniteConsistencyAcceptedPackage.toNormalForm
    (h : StrengthenedFiniteConsistencyAcceptedPackage) :
    PartialConsistencyLowerBoundNormalForm :=
  h.lower_bound_package.toNormalForm

def CalibratedExternalStrengthenedLowerBoundSource.toNormalForm
    (h : CalibratedExternalStrengthenedLowerBoundSource) :
    PartialConsistencyLowerBoundNormalForm where
  code := h.source.code
  strong_lower_bound := h.source.strong_lower_bound
  transfer_to_partial := h.transfer_to_strengthened.comp h.transfer_to_partial

def RescaledExternalStrengthenedLowerBoundSource.toRescaledStrengthenedLowerBound
    (h : RescaledExternalStrengthenedLowerBoundSource)
    (htransfer :
      RescaledSourceToRescaledStrengthenedLowerBoundTransfer
        h.code h.scale) :
    StrongRescaledStrengthenedPartialConsistencyLowerBound h.scale :=
  h.rescaled_strong_lower_bound.transfer htransfer

def RescaledExternalStrengthenedLowerBoundSource.of_rescaled_strengthened
    {ρ : ℕ → ℕ}
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledStrengthenedPartialConsistencyLowerBound ρ) :
    RescaledExternalStrengthenedLowerBoundSource where
  code := strengthenedPartialConsistencyCode
  scale := ρ
  scale_properties := hscale
  rescaled_strong_lower_bound := hlower

def CalibratedRescaledExternalStrengthenedLowerBoundSource.of_rescaled_strengthened
    {ρ : ℕ → ℕ}
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledStrengthenedPartialConsistencyLowerBound ρ)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    CalibratedRescaledExternalStrengthenedLowerBoundSource where
  source :=
    RescaledExternalStrengthenedLowerBoundSource.of_rescaled_strengthened
      hscale hlower
  transfer_to_rescaled_strengthened :=
    rescaled_source_to_rescaled_strengthened_transfer_of_projection
      (rescaled_strengthened_identity_projection ρ)
  transfer_to_partial := hpartial

def RescaledExternalStrengthenedLowerBoundSource.of_pointwise_strengthened
    {source : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (_hcode : ∀ n : ℕ, source n = strengthenedPartialConsistencyCode n)
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledExternalStrengthenedLowerBound source ρ) :
    RescaledExternalStrengthenedLowerBoundSource where
  code := source
  scale := ρ
  scale_properties := hscale
  rescaled_strong_lower_bound := hlower

abbrev StrongRescaledPudlakStrengthenedFiniteConsistencyLowerBound
    (ρ : ℕ → ℕ) : Prop :=
  StrongRescaledExternalStrengthenedLowerBound
    pudlakStrengthenedFiniteConsistencyCode ρ

def RescaledExternalStrengthenedLowerBoundSource.of_rescaled_pudlak_strengthened
    {ρ : ℕ → ℕ}
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledPudlakStrengthenedFiniteConsistencyLowerBound ρ) :
    RescaledExternalStrengthenedLowerBoundSource :=
  RescaledExternalStrengthenedLowerBoundSource.of_pointwise_strengthened
    pudlakStrengthenedFiniteConsistencyCode_eq hscale hlower

def CalibratedRescaledExternalStrengthenedLowerBoundSource.of_rescaled_pudlak_strengthened
    {ρ : ℕ → ℕ}
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledPudlakStrengthenedFiniteConsistencyLowerBound ρ)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    CalibratedRescaledExternalStrengthenedLowerBoundSource where
  source :=
    RescaledExternalStrengthenedLowerBoundSource.of_rescaled_pudlak_strengthened
      hscale hlower
  transfer_to_rescaled_strengthened :=
    rescaled_pudlak_strengthened_to_rescaled_strengthened_transfer ρ
  transfer_to_partial := hpartial

def CalibratedRescaledExternalStrengthenedLowerBoundSource.of_pointwise_strengthened
    {source : ℕ → FormulaCode} {ρ : ℕ → ℕ}
    (hcode : ∀ n : ℕ, source n = strengthenedPartialConsistencyCode n)
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledExternalStrengthenedLowerBound source ρ)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    CalibratedRescaledExternalStrengthenedLowerBoundSource where
  source :=
    RescaledExternalStrengthenedLowerBoundSource.of_pointwise_strengthened
      hcode hscale hlower
  transfer_to_rescaled_strengthened :=
    rescaled_source_to_rescaled_strengthened_transfer_of_projection
      (rescaled_source_to_rescaled_strengthened_projection_of_pointwise_eq
        (ρ := ρ) hcode)
  transfer_to_partial := hpartial

def StrengthenedConsistencyRescalingPackage.toStrongStrengthenedLowerBound
    (h : StrengthenedConsistencyRescalingPackage) :
    StrongStrengthenedPartialConsistencyLowerBound :=
  h.rescaled_strong_lower_bound.transfer h.transfer_to_strengthened

def StrengthenedConsistencyRescalingPackage.toPackage
    (h : StrengthenedConsistencyRescalingPackage) :
    StrengthenedFiniteConsistencyLowerBoundPackage where
  strong_lower_bound := h.toStrongStrengthenedLowerBound
  transfer_to_partial := h.transfer_to_partial

theorem StrengthenedConsistencyRescalingPackage.transfer_to_standard
    (h : StrengthenedConsistencyRescalingPackage) :
    StrongLowerBoundTransfer
      ProofSystem.PA ProofLengthMeasure.symbolSize
      (rescaledStrengthenedPartialConsistencyCode h.scale)
      partialConsistencyCode :=
  h.transfer_to_strengthened.comp h.transfer_to_partial

def StrengthenedConsistencyRescalingPackage.toNormalForm
    (h : StrengthenedConsistencyRescalingPackage) :
    PartialConsistencyLowerBoundNormalForm where
  code := rescaledStrengthenedPartialConsistencyCode h.scale
  strong_lower_bound := h.rescaled_strong_lower_bound
  transfer_to_partial := h.transfer_to_standard

def StrengthenedConsistencyRescalingPackage.of_polynomial_cofinal_scale
    {ρ : ℕ → ℕ}
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledStrengthenedPartialConsistencyLowerBound ρ)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    StrengthenedConsistencyRescalingPackage where
  scale := ρ
  rescaled_strong_lower_bound := hlower
  transfer_to_strengthened :=
    rescaled_strengthened_transfer_of_polynomial_cofinal_scale hscale
  transfer_to_partial := hpartial

def RescaledExternalStrengthenedLowerBoundSource.toRescalingPackage
    (h : RescaledExternalStrengthenedLowerBoundSource)
    (htransfer :
      RescaledSourceToRescaledStrengthenedLowerBoundTransfer
        h.code h.scale)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    StrengthenedConsistencyRescalingPackage :=
  StrengthenedConsistencyRescalingPackage.of_polynomial_cofinal_scale
    h.scale_properties (h.toRescaledStrengthenedLowerBound htransfer) hpartial

def RescaledExternalStrengthenedLowerBoundSource.toPackage
    (h : RescaledExternalStrengthenedLowerBoundSource)
    (htransfer :
      RescaledSourceToRescaledStrengthenedLowerBoundTransfer
        h.code h.scale)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  (h.toRescalingPackage htransfer hpartial).toPackage

def RescaledExternalStrengthenedLowerBoundSource.toPackageOfProjection
    (h : RescaledExternalStrengthenedLowerBoundSource)
    (hprojection :
      RescaledSourceToRescaledStrengthenedProjection h.code h.scale)
    (hpartial : StrengthenedToPartialConsistencyProjection) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  h.toPackage
    (rescaled_source_to_rescaled_strengthened_transfer_of_projection
      hprojection)
    (strengthened_to_partial_transfer_of_projection hpartial)

def RescaledExternalStrengthenedLowerBoundSource.toPackageOfLinearProjection
    (h : RescaledExternalStrengthenedLowerBoundSource)
    (hprojection :
      RescaledSourceToRescaledStrengthenedLinearProjection h.code h.scale)
    (hpartial : StrengthenedToPartialConsistencyLinearProjection) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  h.toPackage
    (rescaled_source_to_rescaled_strengthened_transfer_of_linear_projection
      hprojection)
    (strengthened_to_partial_transfer_of_linear_projection hpartial)

def RescaledExternalStrengthenedLowerBoundSource.toPackageOfConstantProjection
    (h : RescaledExternalStrengthenedLowerBoundSource)
    (hprojection :
      RescaledSourceToRescaledStrengthenedConstantProjection h.code h.scale)
    (hpartial : StrengthenedToPartialConsistencyConstantProjection) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  h.toPackage
    (rescaled_source_to_rescaled_strengthened_transfer_of_constant_projection
      hprojection)
    (strengthened_to_partial_transfer_of_constant_projection hpartial)

def CalibratedRescaledExternalStrengthenedLowerBoundSource.toRescalingPackage
    (h : CalibratedRescaledExternalStrengthenedLowerBoundSource) :
    StrengthenedConsistencyRescalingPackage :=
  h.source.toRescalingPackage
    h.transfer_to_rescaled_strengthened h.transfer_to_partial

def CalibratedRescaledExternalStrengthenedLowerBoundSource.toPackage
    (h : CalibratedRescaledExternalStrengthenedLowerBoundSource) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  h.toRescalingPackage.toPackage

theorem CalibratedRescaledExternalStrengthenedLowerBoundSource.transfer_to_standard
    (h : CalibratedRescaledExternalStrengthenedLowerBoundSource) :
    StrongLowerBoundTransfer
      ProofSystem.PA ProofLengthMeasure.symbolSize
      (rescaledExternalStrengthenedLowerBoundCode h.source.code h.source.scale)
      partialConsistencyCode :=
  h.transfer_to_rescaled_strengthened.comp
    h.toRescalingPackage.transfer_to_standard

def CalibratedRescaledExternalStrengthenedLowerBoundSource.toNormalForm
    (h : CalibratedRescaledExternalStrengthenedLowerBoundSource) :
    PartialConsistencyLowerBoundNormalForm where
  code := rescaledExternalStrengthenedLowerBoundCode h.source.code h.source.scale
  strong_lower_bound := h.source.rescaled_strong_lower_bound
  transfer_to_partial := h.transfer_to_standard

def StrengthenedTimeConstructibleRescalingTheorem.toRescalingPackage
    (h : StrengthenedTimeConstructibleRescalingTheorem) :
    StrengthenedConsistencyRescalingPackage :=
  StrengthenedConsistencyRescalingPackage.of_polynomial_cofinal_scale
    h.scale_properties h.rescaled_strong_lower_bound h.transfer_to_partial

def StrengthenedTimeConstructibleRescalingTheorem.toPackage
    (h : StrengthenedTimeConstructibleRescalingTheorem) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  h.toRescalingPackage.toPackage

def StrengthenedTimeConstructibleRescalingTheorem.toNormalForm
    (h : StrengthenedTimeConstructibleRescalingTheorem) :
    PartialConsistencyLowerBoundNormalForm :=
  h.toRescalingPackage.toNormalForm

def StrengthenedFiniteConsistencyLowerBoundPackage.of_rescaled_lower_bound
    {ρ : ℕ → ℕ}
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledStrengthenedPartialConsistencyLowerBound ρ)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  (StrengthenedConsistencyRescalingPackage.of_polynomial_cofinal_scale
    hscale hlower hpartial).toPackage

def StrengthenedFiniteConsistencyLowerBoundPackage.of_rescaled_lower_bound_and_projection
    {ρ : ℕ → ℕ}
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledStrengthenedPartialConsistencyLowerBound ρ)
    (hpartial : StrengthenedToPartialConsistencyProjection) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  StrengthenedFiniteConsistencyLowerBoundPackage.of_rescaled_lower_bound
    hscale hlower (strengthened_to_partial_transfer_of_projection hpartial)

def StrengthenedFiniteConsistencyLowerBoundPackage.of_rescaled_lower_bound_and_linear_projection
    {ρ : ℕ → ℕ}
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledStrengthenedPartialConsistencyLowerBound ρ)
    (hpartial : StrengthenedToPartialConsistencyLinearProjection) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  StrengthenedFiniteConsistencyLowerBoundPackage.of_rescaled_lower_bound
    hscale hlower (strengthened_to_partial_transfer_of_linear_projection hpartial)

def StrengthenedFiniteConsistencyLowerBoundPackage.of_rescaled_lower_bound_and_constant_projection
    {ρ : ℕ → ℕ}
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledStrengthenedPartialConsistencyLowerBound ρ)
    (hpartial : StrengthenedToPartialConsistencyConstantProjection) :
    StrengthenedFiniteConsistencyLowerBoundPackage :=
  StrengthenedFiniteConsistencyLowerBoundPackage.of_rescaled_lower_bound
    hscale hlower (strengthened_to_partial_transfer_of_constant_projection hpartial)

theorem CalibratedExternalStrengthenedLowerBoundSource.transfer_to_standard
    (h : CalibratedExternalStrengthenedLowerBoundSource) :
    StrongLowerBoundTransfer
      ProofSystem.PA ProofLengthMeasure.symbolSize h.source.code partialConsistencyCode :=
  h.transfer_to_strengthened.comp h.transfer_to_partial

theorem CalibratedExternalStrengthenedLowerBoundSource.toStrongPartialConsistencyLowerBound
    (h : CalibratedExternalStrengthenedLowerBoundSource) :
    StrongPartialConsistencyLowerBound :=
  h.source.strong_lower_bound.transfer h.transfer_to_standard

def StrengthenedFiniteConsistencyLowerBoundPackage.toPartialConsistencySpecPackage
    (h : StrengthenedFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec) :
    PartialConsistencySpecExternalPackage where
  payload_spec := hspec
  strong_lower_bound := h.toStrongPartialConsistencyLowerBound

def StrengthenedFiniteConsistencyLowerBoundPackage.toSpecProvider
    (h : StrengthenedFiniteConsistencyLowerBoundPackage) :
    PartialConsistencySpecProvider where
  toSpecPackage := h.toPartialConsistencySpecPackage

theorem StrengthenedFiniteConsistencyLowerBoundPackage.toEventualPartialConsistencyLowerBound
    (h : StrengthenedFiniteConsistencyLowerBoundPackage) :
    EventualLowerBound
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  partial_consistency_eventual_lower_bound_of_strong
    h.toStrongPartialConsistencyLowerBound

theorem StrengthenedFiniteConsistencyLowerBoundPackage.toEventualPartialConsistencyInputs
    (h : StrengthenedFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  eventual_partial_consistency_inputs_of_spec_package
    (h.toPartialConsistencySpecPackage hspec) hver

def StrengthenedFiniteConsistencyLowerBoundPackage.toCollisionStandard
    (h : StrengthenedFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    PartialConsistencyCollisionStandard :=
  h.toSpecProvider.toCollisionStandard hspec hver

theorem StrengthenedFiniteConsistencyLowerBoundPackage.toEventualPartialConsistencyInputsOfTrace
    (h : StrengthenedFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  eventual_partial_consistency_inputs_of_spec_package_and_trace
    (h.toPartialConsistencySpecPackage hspec) hrealize hembed

def StrengthenedFiniteConsistencyLowerBoundPackage.toCollisionStandardOfTrace
    (h : StrengthenedFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toSpecProvider.toCollisionStandardOfTrace hspec hrealize hembed

theorem irrational_of_strengthened_finite_consistency_package
    (h : StrengthenedFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    ¬ (is_rational euler_mascheroni) :=
  (h.toCollisionStandard hspec hver).collision

theorem irrational_of_strengthened_finite_consistency_package_and_trace
    (h : StrengthenedFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (h.toCollisionStandardOfTrace hspec hrealize hembed).collision

theorem irrational_of_calibrated_external_strengthened_source
    (h : CalibratedExternalStrengthenedLowerBoundSource)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_strengthened_finite_consistency_package
    h.toPackage hspec hver

theorem irrational_of_calibrated_external_strengthened_source_and_trace
    (h : CalibratedExternalStrengthenedLowerBoundSource)
    (hspec : PartialConsistencyPayloadSpec)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_strengthened_finite_consistency_package_and_trace
    h.toPackage hspec hrealize hembed
