/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.Certificate
import EulerLimit.MiniHilbert
/-!
# Gödel-Sondow Coupling Hypothesis Formalization
This module formalizes the Euler-Mascheroni constant limit definition,
proof-complexity and projection-bridge layers.
-/

open Filter
structure AcceptedCertificateProjection
    (source target : ℕ → FormulaCode) : Prop where
  accepted_project :
    ∀ n : ℕ, accepted_certificate (target n) → accepted_certificate (source n)

theorem accepted_partial_consistency_projection_from_reflection_graft :
    AcceptedCertificateProjection partialConsistencyCode sondowReflectionGraftCode where
  accepted_project := by
    intro n h
    exact accepted_partial_consistency_of_reflection_graft h

-- External proof-calculus block: when a target formula is encoded as a graft
-- containing the source formula as a recoverable payload, PA proofs admit the
-- corresponding proof-length projection.  The semantic projection is proved
-- above; this principle is where a concrete Hilbert/sequent/Frege calculus
-- implementation should discharge the proof-code extraction.
structure ProofLengthProjectionPrinciple
    (T : ProofSystem) (measure : ProofLengthMeasure) : Prop where
  projection_of_accepted_projection :
    ∀ source target : ℕ → FormulaCode,
      AcceptedCertificateProjection source target →
        ProofLengthProjection T measure source target

abbrev PAProofLengthProjectionPrinciple : Prop :=
  ProofLengthProjectionPrinciple ProofSystem.PA ProofLengthMeasure.symbolSize

-- Family-specific replacement for the broad projection principle.  The accepted
-- certificate projection is fixed first; the proof-system calibration then
-- supplies exactly the proof-length projection for that projection, not a global
-- principle over every formula family.
structure AcceptedCertificateProjectionToProofLengthCalibration
    (T : ProofSystem) (measure : ProofLengthMeasure)
    {source target : ℕ → FormulaCode}
    (haccepted : AcceptedCertificateProjection source target) : Prop where
  proof_length_projection :
    ProofLengthProjection T measure source target

structure AcceptedCertificateProjectionProofLengthCalibration
    (T : ProofSystem) (measure : ProofLengthMeasure)
    (source target : ℕ → FormulaCode) : Prop where
  accepted_projection : AcceptedCertificateProjection source target
  proof_system_calibration :
    AcceptedCertificateProjectionToProofLengthCalibration
      T measure accepted_projection

abbrev PAAcceptedCertificateProjectionProofLengthCalibration
    (source target : ℕ → FormulaCode) : Prop :=
  AcceptedCertificateProjectionProofLengthCalibration
    ProofSystem.PA ProofLengthMeasure.symbolSize source target

def AcceptedCertificateProjectionToProofLengthCalibration.ofProjection
    {T : ProofSystem} {measure : ProofLengthMeasure}
    {source target : ℕ → FormulaCode}
    {haccepted : AcceptedCertificateProjection source target}
    (hprojection : ProofLengthProjection T measure source target) :
    AcceptedCertificateProjectionToProofLengthCalibration
      T measure haccepted where
  proof_length_projection := hprojection

def AcceptedCertificateProjectionProofLengthCalibration.ofProjection
    {T : ProofSystem} {measure : ProofLengthMeasure}
    {source target : ℕ → FormulaCode}
    (haccepted : AcceptedCertificateProjection source target)
    (hprojection : ProofLengthProjection T measure source target) :
    AcceptedCertificateProjectionProofLengthCalibration
      T measure source target where
  accepted_projection := haccepted
  proof_system_calibration :=
    AcceptedCertificateProjectionToProofLengthCalibration.ofProjection
      hprojection

def ProofLengthProjectionPrinciple.calibrateAcceptedProjection
    {T : ProofSystem} {measure : ProofLengthMeasure}
    (hprinciple : ProofLengthProjectionPrinciple T measure)
    {source target : ℕ → FormulaCode}
    (haccepted : AcceptedCertificateProjection source target) :
    AcceptedCertificateProjectionToProofLengthCalibration
      T measure haccepted where
  proof_length_projection :=
    hprinciple.projection_of_accepted_projection source target haccepted

def ProofLengthProjectionPrinciple.toAcceptedProjectionCalibration
    {T : ProofSystem} {measure : ProofLengthMeasure}
    (hprinciple : ProofLengthProjectionPrinciple T measure)
    {source target : ℕ → FormulaCode}
    (haccepted : AcceptedCertificateProjection source target) :
    AcceptedCertificateProjectionProofLengthCalibration
      T measure source target where
  accepted_projection := haccepted
  proof_system_calibration :=
    hprinciple.calibrateAcceptedProjection haccepted

theorem proofLengthProjectionPrinciple_iff_forallAcceptedProjectionCalibration
    {T : ProofSystem} {measure : ProofLengthMeasure} :
    ProofLengthProjectionPrinciple T measure ↔
      ∀ source target : ℕ → FormulaCode,
        (haccepted : AcceptedCertificateProjection source target) →
          AcceptedCertificateProjectionToProofLengthCalibration
            T measure haccepted := by
  constructor
  · intro hprinciple source target haccepted
    exact hprinciple.calibrateAcceptedProjection haccepted
  · intro hcal
    refine ⟨?_⟩
    intro source target haccepted
    exact (hcal source target haccepted).proof_length_projection

theorem AcceptedCertificateProjectionProofLengthCalibration.toProofLengthProjection
    {T : ProofSystem} {measure : ProofLengthMeasure}
    {source target : ℕ → FormulaCode}
    (hcal :
      AcceptedCertificateProjectionProofLengthCalibration
        T measure source target) :
    ProofLengthProjection T measure source target :=
  hcal.proof_system_calibration.proof_length_projection

theorem AcceptedCertificateProjectionProofLengthCalibration.toStrongLowerBoundTransfer
    {T : ProofSystem} {measure : ProofLengthMeasure}
    {source target : ℕ → FormulaCode}
    (hcal :
      AcceptedCertificateProjectionProofLengthCalibration
        T measure source target) :
    StrongLowerBoundTransfer T measure source target :=
  hcal.toProofLengthProjection.toStrongLowerBoundTransfer

abbrev PAPartialConsistencyToReflectionGraftAcceptedCalibration : Prop :=
  PAAcceptedCertificateProjectionProofLengthCalibration
    partialConsistencyCode sondowReflectionGraftCode

def partial_consistency_to_reflection_graft_accepted_calibration_of_principle
    (hprinciple : PAProofLengthProjectionPrinciple) :
    PAPartialConsistencyToReflectionGraftAcceptedCalibration :=
  hprinciple.toAcceptedProjectionCalibration
    accepted_partial_consistency_projection_from_reflection_graft

theorem partial_consistency_to_reflection_graft_projection_of_calibration
    (hcal : PAPartialConsistencyToReflectionGraftAcceptedCalibration) :
    ProofLengthProjection ProofSystem.PA ProofLengthMeasure.symbolSize
      partialConsistencyCode sondowReflectionGraftCode :=
  hcal.toProofLengthProjection

theorem partial_consistency_to_reflection_graft_transfer_of_calibration
    (hcal : PAPartialConsistencyToReflectionGraftAcceptedCalibration) :
    StrongLowerBoundTransfer ProofSystem.PA ProofLengthMeasure.symbolSize
      partialConsistencyCode sondowReflectionGraftCode :=
  hcal.toStrongLowerBoundTransfer

theorem partial_consistency_to_reflection_graft_projection_of_principle
    (hprinciple : PAProofLengthProjectionPrinciple) :
    ProofLengthProjection ProofSystem.PA ProofLengthMeasure.symbolSize
      partialConsistencyCode sondowReflectionGraftCode :=
  partial_consistency_to_reflection_graft_projection_of_calibration
    (partial_consistency_to_reflection_graft_accepted_calibration_of_principle
      hprinciple)

-- Wu's Sondow lower-bound conjecture: the natural Sondow certificate family has
-- no eventual polynomial proof-length bound in PA, measured by symbol size.
abbrev WuSondowLowerBoundConjecture : Prop :=
  EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
    sondowCertificateValidCode

-- A stronger form useful for matching standard proof-complexity lower-bound
-- packages: every polynomial is beaten frequently, hence arbitrarily far out.
abbrev StrongWuSondowLowerBoundConjecture : Prop :=
  ∀ f : ℕ → ℝ, is_polynomial_bound f →
    ∃ᶠ n in atTop,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowCertificateValidCode n) > f n

theorem WuSondowLowerBoundConjecture.of_strong
    (h : StrongWuSondowLowerBoundConjecture) :
    WuSondowLowerBoundConjecture :=
  EventualLowerBound.of_frequently h


abbrev StrongWuSourceLowerBound
    (source : ℕ → FormulaCode) : Prop :=
  StrongProofLengthLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize source

abbrev StrongWuTransferFrom
    (source : ℕ → FormulaCode) : Prop :=
  StrongLowerBoundTransfer ProofSystem.PA ProofLengthMeasure.symbolSize
    source sondowCertificateValidCode

theorem strong_wu_conjecture_of_source_transfer
    {source : ℕ → FormulaCode}
    (hsource : StrongWuSourceLowerBound source)
    (htransfer : StrongWuTransferFrom source) :
    StrongWuSondowLowerBoundConjecture := by
  intro f hf
  exact (hsource.transfer htransfer).frequently_beats_every_polynomial f hf

abbrev StrongPartialConsistencyLowerBound : Prop :=
  StrongWuSourceLowerBound partialConsistencyCode

structure PartialConsistencyExternalPackage : Prop where
  payload_truth : PartialConsistencyPayloadTruth
  strong_lower_bound : StrongPartialConsistencyLowerBound

structure PartialConsistencySpecExternalPackage where
  payload_spec : PartialConsistencyPayloadSpec
  strong_lower_bound : StrongPartialConsistencyLowerBound

def PartialConsistencySpecExternalPackage.ofAcceptedTruth
    (haccepted : PartialConsistencyAcceptedTruth)
    (hlower : StrongPartialConsistencyLowerBound) :
    PartialConsistencySpecExternalPackage where
  payload_spec := PartialConsistencyPayloadSpec.ofAcceptedTruth haccepted
  strong_lower_bound := hlower

def PartialConsistencySpecExternalPackage.toPartialConsistencyExternalPackage
    (h : PartialConsistencySpecExternalPackage) :
    PartialConsistencyExternalPackage where
  payload_truth := h.payload_spec.toPayloadTruth
  strong_lower_bound := h.strong_lower_bound

theorem PartialConsistencySpecExternalPackage.toReflectionGraftPayloadInputs
    (h : PartialConsistencySpecExternalPackage) :
    ReflectionGraftPayloadInputs :=
  h.payload_spec.toReflectionGraftPayloadInputs

theorem PartialConsistencySpecExternalPackage.accepted_standard
    (h : PartialConsistencySpecExternalPackage) (n : ℕ) :
    accepted_certificate (partialConsistencyCode n) :=
  h.payload_spec.accepted_standard n

theorem PartialConsistencySpecExternalPackage.accepted_standard_eventual
    (h : PartialConsistencySpecExternalPackage) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      accepted_certificate (partialConsistencyCode n) :=
  h.payload_spec.accepted_standard_eventual

theorem PartialConsistencySpecExternalPackage.toReflectionGraftCollapsePackage
    (h : PartialConsistencySpecExternalPackage)
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage) :
    ReflectionGraftCollapsePackage :=
  reflection_graft_collapse_package_of_payload_spec_and_concrete_verification
    hfwd h.payload_spec hver

theorem PartialConsistencySpecExternalPackage.toEventualReflectionGraftCollapseInputs
    (h : PartialConsistencySpecExternalPackage)
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage) :
    EventualCertificateCollapseInputs sondowReflectionGraftCode :=
  (h.toReflectionGraftCollapsePackage hfwd hver)
    |>.toEventualCertificateCollapseInputs

theorem PartialConsistencySpecExternalPackage.toEventualPartialConsistencyCollapseInputs
    (h : PartialConsistencySpecExternalPackage)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  partial_consistency_eventual_collapse_inputs_of_payload_spec
    h.payload_spec hver.toShortProofBridge

theorem PartialConsistencySpecExternalPackage.toEventualPartialConsistencyCollapseInputs'
    (h : PartialConsistencySpecExternalPackage)
    (hver : PAStandardVerificationTheorem) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  partial_consistency_eventual_collapse_inputs_of_payload_spec_and_verification
    h.payload_spec hver

theorem PartialConsistencySpecExternalPackage.toEventualPartialConsistencyCollapseInputsOfTrace
    (h : PartialConsistencySpecExternalPackage)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  partial_consistency_eventual_collapse_inputs_of_payload_spec_and_trace_realization
    h.payload_spec hrealize hembed

def rescaledPartialConsistencyCode (ρ : ℕ → ℕ) (n : ℕ) : FormulaCode :=
  partialConsistencyCode (ρ n)

abbrev StrongRescaledPartialConsistencyLowerBound (ρ : ℕ → ℕ) : Prop :=
  StrongWuSourceLowerBound (rescaledPartialConsistencyCode ρ)

abbrev RescaledPartialConsistencyToPartialConsistencyTransfer (ρ : ℕ → ℕ) : Prop :=
  StrongLowerBoundTransfer ProofSystem.PA ProofLengthMeasure.symbolSize
    (rescaledPartialConsistencyCode ρ) partialConsistencyCode

theorem rescaled_partial_consistency_transfer_of_polynomial_cofinal_scale
    {ρ : ℕ → ℕ} (hscale : PolynomialCofinalScale ρ) :
    RescaledPartialConsistencyToPartialConsistencyTransfer ρ := by
  change StrongLowerBoundTransfer ProofSystem.PA ProofLengthMeasure.symbolSize
    (fun n : ℕ => partialConsistencyCode (ρ n)) partialConsistencyCode
  exact StrongLowerBoundTransfer.of_polynomial_cofinal_scale
    (T := ProofSystem.PA) (measure := ProofLengthMeasure.symbolSize)
    (φ := partialConsistencyCode) hscale

structure PartialConsistencyRescalingPackage where
  scale : ℕ → ℕ
  rescaled_strong_lower_bound : StrongRescaledPartialConsistencyLowerBound scale
  transfer_to_payload : RescaledPartialConsistencyToPartialConsistencyTransfer scale

structure BussPudlakTimeConstructibleRescalingTheorem where
  scale : ℕ → ℕ
  scale_properties : PolynomialCofinalScale scale
  rescaled_strong_lower_bound : StrongRescaledPartialConsistencyLowerBound scale

def BussPudlakTimeConstructibleRescalingTheorem.comp_scale
    (h : BussPudlakTimeConstructibleRescalingTheorem)
    {σ : ℕ → ℕ} (hσ : PolynomialCofinalScale σ)
    (hlower :
      StrongRescaledPartialConsistencyLowerBound
        (fun n : ℕ => h.scale (σ n))) :
    BussPudlakTimeConstructibleRescalingTheorem where
  scale := fun n : ℕ => h.scale (σ n)
  scale_properties := h.scale_properties.comp hσ
  rescaled_strong_lower_bound := hlower

def PartialConsistencyRescalingPackage.of_polynomial_cofinal_scale
    {ρ : ℕ → ℕ}
    (hscale : PolynomialCofinalScale ρ)
    (hlower : StrongRescaledPartialConsistencyLowerBound ρ) :
    PartialConsistencyRescalingPackage where
  scale := ρ
  rescaled_strong_lower_bound := hlower
  transfer_to_payload :=
    rescaled_partial_consistency_transfer_of_polynomial_cofinal_scale hscale

def BussPudlakTimeConstructibleRescalingTheorem.toPartialConsistencyRescalingPackage
    (h : BussPudlakTimeConstructibleRescalingTheorem) :
    PartialConsistencyRescalingPackage :=
  PartialConsistencyRescalingPackage.of_polynomial_cofinal_scale
    h.scale_properties h.rescaled_strong_lower_bound

def BussPudlakTimeConstructibleRescalingTheorem.toStrongPartialConsistencyLowerBound
    (h : BussPudlakTimeConstructibleRescalingTheorem) :
    StrongPartialConsistencyLowerBound :=
  (h.toPartialConsistencyRescalingPackage).rescaled_strong_lower_bound.transfer
    (h.toPartialConsistencyRescalingPackage).transfer_to_payload

def PartialConsistencyRescalingPackage.of_unrescaled_lower_bound
    (hlower : StrongPartialConsistencyLowerBound) :
    PartialConsistencyRescalingPackage :=
  PartialConsistencyRescalingPackage.of_polynomial_cofinal_scale
    PolynomialCofinalScale.id hlower

def PartialConsistencyRescalingPackage.toStrongPartialConsistencyLowerBound
    (h : PartialConsistencyRescalingPackage) :
    StrongPartialConsistencyLowerBound :=
  h.rescaled_strong_lower_bound.transfer h.transfer_to_payload

-- External Buss/Pudlák/Friedman proof-length package for the reflection-graft
-- route.  This names the intended source of the partial-consistency payload and
-- its lower bound, but it deliberately does not include the separate
-- proof-calculus projection principle from the graft back to the payload.
structure BussPudlakPartialConsistencyPackage : Prop where
  payload_truth : PartialConsistencyPayloadTruth
  strong_payload_reading : PartialConsistencyPayloadIntendedReading
  strong_lower_bound : StrongPartialConsistencyLowerBound

structure BussPudlakPartialConsistencySpecPackage where
  payload_spec : PartialConsistencyPayloadSpec
  strong_lower_bound : StrongPartialConsistencyLowerBound

def BussPudlakPartialConsistencySpecPackage.ofAcceptedTruth
    (haccepted : PartialConsistencyAcceptedTruth)
    (hlower : StrongPartialConsistencyLowerBound) :
    BussPudlakPartialConsistencySpecPackage where
  payload_spec := PartialConsistencyPayloadSpec.ofAcceptedTruth haccepted
  strong_lower_bound := hlower

structure BussPudlakRescaledPartialConsistencyPackage where
  payload_truth : PartialConsistencyPayloadTruth
  strong_payload_reading : PartialConsistencyPayloadIntendedReading
  rescaling : PartialConsistencyRescalingPackage

structure BussPudlakRescaledPartialConsistencySpecPackage where
  payload_spec : PartialConsistencyPayloadSpec
  rescaling : PartialConsistencyRescalingPackage

def BussPudlakRescaledPartialConsistencySpecPackage.ofAcceptedTruth
    (haccepted : PartialConsistencyAcceptedTruth)
    (hrescale : PartialConsistencyRescalingPackage) :
    BussPudlakRescaledPartialConsistencySpecPackage where
  payload_spec := PartialConsistencyPayloadSpec.ofAcceptedTruth haccepted
  rescaling := hrescale

def BussPudlakPartialConsistencySpecPackage.toBussPudlakPartialConsistencyPackage
    (h : BussPudlakPartialConsistencySpecPackage) :
    BussPudlakPartialConsistencyPackage where
  payload_truth := h.payload_spec.toPayloadTruth
  strong_payload_reading := h.payload_spec.toIntendedReading
  strong_lower_bound := h.strong_lower_bound

def BussPudlakPartialConsistencySpecPackage.toPartialConsistencySpecExternalPackage
    (h : BussPudlakPartialConsistencySpecPackage) :
    PartialConsistencySpecExternalPackage where
  payload_spec := h.payload_spec
  strong_lower_bound := h.strong_lower_bound

def BussPudlakPartialConsistencySpecPackage.toPartialConsistencyExternalPackage
    (h : BussPudlakPartialConsistencySpecPackage) :
    PartialConsistencyExternalPackage :=
  h.toPartialConsistencySpecExternalPackage.toPartialConsistencyExternalPackage

theorem BussPudlakPartialConsistencySpecPackage.toReflectionGraftPayloadInputs
    (h : BussPudlakPartialConsistencySpecPackage) :
    ReflectionGraftPayloadInputs :=
  h.payload_spec.toReflectionGraftPayloadInputs

theorem BussPudlakPartialConsistencySpecPackage.accepted_standard
    (h : BussPudlakPartialConsistencySpecPackage) (n : ℕ) :
    accepted_certificate (partialConsistencyCode n) :=
  h.payload_spec.accepted_standard n

theorem BussPudlakPartialConsistencySpecPackage.toReflectionGraftCollapsePackage
    (h : BussPudlakPartialConsistencySpecPackage)
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage) :
    ReflectionGraftCollapsePackage :=
  h.toPartialConsistencySpecExternalPackage
    |>.toReflectionGraftCollapsePackage hfwd hver

theorem BussPudlakPartialConsistencySpecPackage.toEventualReflectionGraftCollapseInputs
    (h : BussPudlakPartialConsistencySpecPackage)
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage) :
    EventualCertificateCollapseInputs sondowReflectionGraftCode :=
  h.toPartialConsistencySpecExternalPackage
    |>.toEventualReflectionGraftCollapseInputs hfwd hver

theorem BussPudlakPartialConsistencySpecPackage.toEventualPartialConsistencyCollapseInputs
    (h : BussPudlakPartialConsistencySpecPackage)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  h.toPartialConsistencySpecExternalPackage
    |>.toEventualPartialConsistencyCollapseInputs hver

theorem BussPudlakPartialConsistencySpecPackage.toEventualPartialConsistencyCollapseInputs'
    (h : BussPudlakPartialConsistencySpecPackage)
    (hver : PAStandardVerificationTheorem) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  h.toPartialConsistencySpecExternalPackage
    |>.toEventualPartialConsistencyCollapseInputs' hver

theorem
    BussPudlakPartialConsistencySpecPackage.toEventualPartialConsistencyCollapseInputsOfTrace
    (h : BussPudlakPartialConsistencySpecPackage)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  h.toPartialConsistencySpecExternalPackage
    |>.toEventualPartialConsistencyCollapseInputsOfTrace hrealize hembed

def BussPudlakRescaledPartialConsistencyPackage.of_time_constructible_rescaling
    (htruth : PartialConsistencyPayloadTruth)
    (hreading : PartialConsistencyPayloadIntendedReading)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem) :
    BussPudlakRescaledPartialConsistencyPackage where
  payload_truth := htruth
  strong_payload_reading := hreading
  rescaling := hrescale.toPartialConsistencyRescalingPackage

def BussPudlakRescaledPartialConsistencySpecPackage.of_time_constructible_rescaling
    (hspec : PartialConsistencyPayloadSpec)
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem) :
    BussPudlakRescaledPartialConsistencySpecPackage where
  payload_spec := hspec
  rescaling := hrescale.toPartialConsistencyRescalingPackage

def BussPudlakRescaledPartialConsistencyPackage.toBussPudlakPartialConsistencyPackage
    (h : BussPudlakRescaledPartialConsistencyPackage) :
    BussPudlakPartialConsistencyPackage where
  payload_truth := h.payload_truth
  strong_payload_reading := h.strong_payload_reading
  strong_lower_bound := h.rescaling.toStrongPartialConsistencyLowerBound

def BussPudlakRescaledPartialConsistencySpecPackage.toBussPudlakPartialConsistencySpecPackage
    (h : BussPudlakRescaledPartialConsistencySpecPackage) :
    BussPudlakPartialConsistencySpecPackage where
  payload_spec := h.payload_spec
  strong_lower_bound := h.rescaling.toStrongPartialConsistencyLowerBound

def BussPudlakRescaledPartialConsistencySpecPackage.toBussPudlakPartialConsistencyPackage
    (h : BussPudlakRescaledPartialConsistencySpecPackage) :
    BussPudlakPartialConsistencyPackage :=
  h.toBussPudlakPartialConsistencySpecPackage.toBussPudlakPartialConsistencyPackage

def BussPudlakPartialConsistencyPackage.toPartialConsistencyExternalPackage
    (h : BussPudlakPartialConsistencyPackage) :
    PartialConsistencyExternalPackage where
  payload_truth := h.payload_truth
  strong_lower_bound := h.strong_lower_bound

def BussPudlakRescaledPartialConsistencyPackage.toPartialConsistencyExternalPackage
    (h : BussPudlakRescaledPartialConsistencyPackage) :
    PartialConsistencyExternalPackage :=
  h.toBussPudlakPartialConsistencyPackage.toPartialConsistencyExternalPackage

def BussPudlakRescaledPartialConsistencySpecPackage.toPartialConsistencySpecExternalPackage
    (h : BussPudlakRescaledPartialConsistencySpecPackage) :
    PartialConsistencySpecExternalPackage :=
  h.toBussPudlakPartialConsistencySpecPackage.toPartialConsistencySpecExternalPackage

def BussPudlakRescaledPartialConsistencySpecPackage.toPartialConsistencyExternalPackage
    (h : BussPudlakRescaledPartialConsistencySpecPackage) :
    PartialConsistencyExternalPackage :=
  h.toPartialConsistencySpecExternalPackage.toPartialConsistencyExternalPackage

theorem BussPudlakRescaledPartialConsistencySpecPackage.toReflectionGraftPayloadInputs
    (h : BussPudlakRescaledPartialConsistencySpecPackage) :
    ReflectionGraftPayloadInputs :=
  h.payload_spec.toReflectionGraftPayloadInputs

theorem BussPudlakRescaledPartialConsistencySpecPackage.accepted_standard
    (h : BussPudlakRescaledPartialConsistencySpecPackage) (n : ℕ) :
    accepted_certificate (partialConsistencyCode n) :=
  h.payload_spec.accepted_standard n

theorem BussPudlakRescaledPartialConsistencySpecPackage.toReflectionGraftCollapsePackage
    (h : BussPudlakRescaledPartialConsistencySpecPackage)
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage) :
    ReflectionGraftCollapsePackage :=
  h.toPartialConsistencySpecExternalPackage
    |>.toReflectionGraftCollapsePackage hfwd hver

theorem BussPudlakRescaledPartialConsistencySpecPackage.toEventualReflectionGraftCollapseInputs
    (h : BussPudlakRescaledPartialConsistencySpecPackage)
    (hfwd : SondowForwardInputs)
    (hver : ReflectionGraftConcreteVerificationPackage) :
    EventualCertificateCollapseInputs sondowReflectionGraftCode :=
  h.toPartialConsistencySpecExternalPackage
    |>.toEventualReflectionGraftCollapseInputs hfwd hver

theorem BussPudlakRescaledPartialConsistencySpecPackage.toEventualPartialConsistencyCollapseInputs
    (h : BussPudlakRescaledPartialConsistencySpecPackage)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  h.toPartialConsistencySpecExternalPackage
    |>.toEventualPartialConsistencyCollapseInputs hver

theorem BussPudlakRescaledPartialConsistencySpecPackage.toEventualPartialConsistencyCollapseInputs'
    (h : BussPudlakRescaledPartialConsistencySpecPackage)
    (hver : PAStandardVerificationTheorem) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  h.toPartialConsistencySpecExternalPackage
    |>.toEventualPartialConsistencyCollapseInputs' hver

theorem
    BussPudlakRescaledPartialConsistencySpecPackage.toEventualPartialConsistencyCollapseOfTrace
    (h : BussPudlakRescaledPartialConsistencySpecPackage)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    EventualCertificateCollapseInputs partialConsistencyCode :=
  h.toPartialConsistencySpecExternalPackage
    |>.toEventualPartialConsistencyCollapseInputsOfTrace hrealize hembed

abbrev PartialConsistencyToSondowCertificateTransfer : Prop :=
  StrongWuTransferFrom partialConsistencyCode

theorem strong_wu_conjecture_of_partial_consistency_transfer
    (hlower : StrongPartialConsistencyLowerBound)
    (htransfer : PartialConsistencyToSondowCertificateTransfer) :
    StrongWuSondowLowerBoundConjecture :=
  strong_wu_conjecture_of_source_transfer hlower htransfer

theorem partial_consistency_eventual_lower_bound_of_strong
    (hlower : StrongPartialConsistencyLowerBound) :
    EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      partialConsistencyCode :=
  hlower.toEventualLowerBound

abbrev PartialConsistencyToReflectionGraftProjection : Prop :=
  ProofLengthProjection ProofSystem.PA ProofLengthMeasure.symbolSize
    partialConsistencyCode sondowReflectionGraftCode

abbrev PartialConsistencyToReflectionGraftLowerBoundTransfer : Prop :=
  StrongLowerBoundTransfer ProofSystem.PA ProofLengthMeasure.symbolSize
    partialConsistencyCode sondowReflectionGraftCode

theorem partial_consistency_to_reflection_graft_transfer
    (hprojection : PartialConsistencyToReflectionGraftProjection) :
    StrongLowerBoundTransfer ProofSystem.PA ProofLengthMeasure.symbolSize
      partialConsistencyCode sondowReflectionGraftCode :=
  hprojection.toStrongLowerBoundTransfer

theorem strong_reflection_graft_lower_bound_of_partial_consistency
    (hlower : StrongPartialConsistencyLowerBound)
    (hprojection : PartialConsistencyToReflectionGraftProjection) :
    StrongProofLengthLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  hlower.transfer (partial_consistency_to_reflection_graft_transfer hprojection)

theorem reflection_graft_eventual_lower_bound_of_partial_consistency
    (hlower : StrongPartialConsistencyLowerBound)
    (hprojection : PartialConsistencyToReflectionGraftProjection) :
    EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  EventualLowerBound.of_frequently
    (strong_reflection_graft_lower_bound_of_partial_consistency
      hlower hprojection).frequently_beats_every_polynomial

theorem strong_reflection_graft_lower_bound_of_partial_consistency_transfer
    (hlower : StrongPartialConsistencyLowerBound)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    StrongProofLengthLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  hlower.transfer htransfer

theorem rescaled_partial_consistency_to_reflection_graft_transfer
    (hrescale : PartialConsistencyRescalingPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    StrongLowerBoundTransfer ProofSystem.PA ProofLengthMeasure.symbolSize
      (rescaledPartialConsistencyCode hrescale.scale) sondowReflectionGraftCode :=
  hrescale.transfer_to_payload.comp htransfer

theorem strong_reflection_graft_lower_bound_of_rescaled_partial_consistency
    (hrescale : PartialConsistencyRescalingPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    StrongProofLengthLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  hrescale.rescaled_strong_lower_bound.transfer
    (rescaled_partial_consistency_to_reflection_graft_transfer hrescale htransfer)

theorem strong_reflection_graft_lower_bound_of_time_constructible_rescaling
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    StrongProofLengthLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  strong_reflection_graft_lower_bound_of_rescaled_partial_consistency
    hrescale.toPartialConsistencyRescalingPackage htransfer

theorem reflection_graft_eventual_lower_bound_of_partial_consistency_transfer
    (hlower : StrongPartialConsistencyLowerBound)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  EventualLowerBound.of_frequently
    (strong_reflection_graft_lower_bound_of_partial_consistency_transfer
      hlower htransfer).frequently_beats_every_polynomial

theorem reflection_graft_eventual_lower_bound_of_rescaled_partial_consistency
    (hrescale : PartialConsistencyRescalingPackage)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  (strong_reflection_graft_lower_bound_of_rescaled_partial_consistency
    hrescale htransfer).toEventualLowerBound

theorem reflection_graft_eventual_lower_bound_of_time_constructible_rescaling
    (hrescale : BussPudlakTimeConstructibleRescalingTheorem)
    (htransfer : PartialConsistencyToReflectionGraftLowerBoundTransfer) :
    EventualLowerBound ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  (strong_reflection_graft_lower_bound_of_time_constructible_rescaling
    hrescale htransfer).toEventualLowerBound
