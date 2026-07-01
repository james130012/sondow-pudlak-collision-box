/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.ExternalPudlakRawEncoding
import EulerLimit.ProjectionBridge
import EulerLimit.PudlakFormulaCode

/-!
# Hilbert-Pudlak route combinators

This module connects the Pudlak finite-consistency lower-bound package to the
local Hilbert proof-code trace route.  It keeps these downstream route
combinators out of `EulerLimit.Basic`.
-/

open Filter MiniHilbert

universe u v w

theorem PudlakFiniteConsistencyLowerBoundPackage.toPartialConsistencyInputsOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  h.toEventualPartialConsistencyModelInputsOfTrace hspec
    (interp.toPartialConsistencyAcceptedS21TraceRealizationOfPayloadSpec
      hspec htrace)
    hembed

def PudlakFiniteConsistencyLowerBoundPackage.toSpecProvider
    (h : PudlakFiniteConsistencyLowerBoundPackage) :
    PartialConsistencySpecProvider where
  toSpecPackage := fun hspec =>
    (h.toBussPudlakSpecPackage hspec).toPartialConsistencySpecExternalPackage

def BussPudlakPartialConsistencySpecPackage.toFixedSpecProvider
    (h : BussPudlakPartialConsistencySpecPackage) :
    PartialConsistencyFixedSpecProvider where
  specPackage := h.toPartialConsistencySpecExternalPackage

def BussPudlakRescaledPartialConsistencySpecPackage.toFixedSpecProvider
    (h : BussPudlakRescaledPartialConsistencySpecPackage) :
    PartialConsistencyFixedSpecProvider where
  specPackage :=
    h.toBussPudlakPartialConsistencySpecPackage.toPartialConsistencySpecExternalPackage

def PudlakFiniteConsistencyLowerBoundPackage.toNormalForm
    (h : PudlakFiniteConsistencyLowerBoundPackage) :
    PartialConsistencyLowerBoundNormalForm where
  code := rescaledPartialConsistencyCode h.scale
  strong_lower_bound := h.rescaled_strong_lower_bound
  transfer_to_partial := h.transferToPartialConsistency

def PudlakFiniteConsistencyLowerBoundPackage.toNormalFormSpecProvider
    (h : PudlakFiniteConsistencyLowerBoundPackage) :
    PartialConsistencySpecProvider :=
  h.toNormalForm.toSpecProvider

def PudlakFiniteConsistencyLowerBoundPackage.toNormalFormCollisionStandard
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    PartialConsistencyCollisionStandard :=
  h.toNormalForm.toCollisionStandard hspec hver

def PudlakFiniteConsistencyLowerBoundPackage.toNormalFormCollisionStandardOfTrace
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toNormalForm.toCollisionStandardOfTrace hspec hrealize hembed

theorem PudlakFiniteConsistencyLowerBoundPackage.normalFormStrongLowerBound_eq
    (h : PudlakFiniteConsistencyLowerBoundPackage) :
    h.toNormalForm.toStrongPartialConsistencyLowerBound =
      h.toStrongPartialConsistencyLowerBound := by
  rfl

theorem PudlakFiniteConsistencyLowerBoundPackage.normalFormSpecPackage_eq
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec) :
    h.toNormalForm.toSpecPackage hspec =
      (h.toBussPudlakSpecPackage hspec).toPartialConsistencySpecExternalPackage := by
  rfl

theorem PudlakFiniteConsistencyLowerBoundPackage.normalFormSpecProvider_eq
    (h : PudlakFiniteConsistencyLowerBoundPackage) :
    h.toNormalFormSpecProvider = h.toSpecProvider := by
  rfl

theorem PudlakFiniteConsistencyLowerBoundPackage.normalFormCollisionStandard_eq
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (hver : PartialConsistencyConcreteVerificationPackage) :
    h.toNormalFormCollisionStandard hspec hver =
      h.toSpecProvider.toCollisionStandard hspec hver := by
  rfl

theorem PudlakFiniteConsistencyLowerBoundPackage.normalFormCollisionStandardOfTrace_eq
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (hrealize : AcceptedCertificateS21TraceRealization partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    h.toNormalFormCollisionStandardOfTrace hspec hrealize hembed =
      h.toSpecProvider.toCollisionStandardOfTrace hspec hrealize hembed := by
  rfl

def PudlakFiniteConsistencyLowerBoundPackage.toNormalFormCollisionStandardOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toNormalForm.toCollisionStandardOfTrace hspec
    (interp.toPartialConsistencyAcceptedS21TraceRealizationOfPayloadSpec
      hspec htrace)
    hembed

def PudlakFiniteConsistencyLowerBoundPackage.toNormalFormCollisionStandardOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toNormalFormCollisionStandardOfHilbertTrace interp hspec
    (PartialConsistencyHilbertS21TraceSoundness.of_payload_spec_and_verifier_trace
      hspec
      (htrace.trace_soundness
        partialConsistencyCode fixed_verifier_encoding_partialConsistencyCode))
    hembed

def PudlakFiniteConsistencyLowerBoundPackage.toCollisionStandardOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toSpecProvider.toCollisionStandardOfTrace hspec
    (interp.toPartialConsistencyAcceptedS21TraceRealizationOfPayloadSpec
      hspec htrace)
    hembed

theorem PudlakFiniteConsistencyLowerBoundPackage.toPartialConsistencyInputsOfVerifierTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (hsound : S21VerifierTraceSoundness partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  h.toPartialConsistencyInputsOfHilbertTrace interp hspec
    (PartialConsistencyHilbertS21TraceSoundness.of_payload_spec_and_verifier_trace
      hspec hsound)
    hembed

def PudlakFiniteConsistencyLowerBoundPackage.toCollisionStandardOfVerifierTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (hsound : S21VerifierTraceSoundness partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toCollisionStandardOfHilbertTrace interp hspec
    (PartialConsistencyHilbertS21TraceSoundness.of_payload_spec_and_verifier_trace
      hspec hsound)
    hembed

theorem PudlakFiniteConsistencyLowerBoundPackage.toPartialConsistencyInputsOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  h.toPartialConsistencyInputsOfVerifierTrace interp hspec
    (htrace.trace_soundness
      partialConsistencyCode fixed_verifier_encoding_partialConsistencyCode)
    hembed

def PudlakFiniteConsistencyLowerBoundPackage.toCollisionStandardOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toCollisionStandardOfVerifierTrace interp hspec
    (htrace.trace_soundness
      partialConsistencyCode fixed_verifier_encoding_partialConsistencyCode)
    hembed

theorem PudlakFiniteConsistencyLowerBoundPackage.normalFormCollisionStandardOfHilbertTrace_eq
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    h.toNormalFormCollisionStandardOfHilbertTrace interp hspec htrace hembed =
      h.toCollisionStandardOfHilbertTrace interp hspec htrace hembed := by
  rfl

theorem PudlakFiniteConsistencyLowerBoundPackage.normalFormCollisionStandardOfTracePackage_eq
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    h.toNormalFormCollisionStandardOfTracePackage interp hspec htrace hembed =
      h.toCollisionStandardOfTracePackage interp hspec htrace hembed := by
  rfl

theorem PudlakFiniteConsistencyLowerBoundPackage.toPartialConsistencyInputsOfTracePackage'
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : PudlakFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbedding) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  h.toPartialConsistencyInputsOfTracePackage interp hspec htrace
    (hembed.on partialConsistencyCode)

theorem irrational_of_payload_spec_hilbert_trace_pudlak_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage) :
    ¬ (is_rational euler_mascheroni) :=
  (pudlak_lower_bound.toCollisionStandardOfHilbertTrace
    interp hspec htrace hembed).collision

theorem irrational_of_payload_spec_verifier_trace_pudlak_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (hsound : S21VerifierTraceSoundness partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage) :
    ¬ (is_rational euler_mascheroni) :=
  (pudlak_lower_bound.toCollisionStandardOfVerifierTrace
    interp hspec hsound hembed).collision

theorem irrational_of_payload_spec_trace_package_pudlak_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage) :
    ¬ (is_rational euler_mascheroni) :=
  (pudlak_lower_bound.toCollisionStandardOfTracePackage
    interp hspec htrace hembed).collision

theorem irrational_of_payload_spec_trace_package_pudlak_package'
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbedding)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_payload_spec_trace_package_pudlak_package interp hspec
    htrace (hembed.on partialConsistencyCode) pudlak_lower_bound

theorem StrengthenedFiniteConsistencyLowerBoundPackage.toPartialConsistencyInputsOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : StrengthenedFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  eventual_partial_consistency_inputs_of_spec_package_and_trace
    (h.toPartialConsistencySpecPackage hspec)
    (interp.toPartialConsistencyAcceptedS21TraceRealizationOfPayloadSpec
      hspec htrace)
    hembed

def StrengthenedFiniteConsistencyLowerBoundPackage.toCollisionStandardOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : StrengthenedFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toSpecProvider.toCollisionStandardOfTrace hspec
    (interp.toPartialConsistencyAcceptedS21TraceRealizationOfPayloadSpec
      hspec htrace)
    hembed

theorem StrengthenedFiniteConsistencyLowerBoundPackage.toPartialConsistencyInputsOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : StrengthenedFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    EventualPartialConsistencyModelInputs
      ProofSystem.PA ProofLengthMeasure.symbolSize partialConsistencyCode :=
  h.toPartialConsistencyInputsOfHilbertTrace interp hspec
    (PartialConsistencyHilbertS21TraceSoundness.of_payload_spec_and_verifier_trace
      hspec
      (htrace.trace_soundness
        partialConsistencyCode fixed_verifier_encoding_partialConsistencyCode))
    hembed

def StrengthenedFiniteConsistencyLowerBoundPackage.toCollisionStandardOfVerifierTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : StrengthenedFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (hsound : S21VerifierTraceSoundness partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toCollisionStandardOfHilbertTrace interp hspec
    (PartialConsistencyHilbertS21TraceSoundness.of_payload_spec_and_verifier_trace
      hspec hsound)
    hembed

def StrengthenedFiniteConsistencyLowerBoundPackage.toCollisionStandardOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : StrengthenedFiniteConsistencyLowerBoundPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toCollisionStandardOfVerifierTrace interp hspec
    (htrace.trace_soundness
      partialConsistencyCode fixed_verifier_encoding_partialConsistencyCode)
    hembed

theorem irrational_of_strengthened_hilbert_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hstrengthened : StrengthenedFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hstrengthened.toCollisionStandardOfHilbertTrace
    interp hspec htrace hembed).collision

theorem irrational_of_strengthened_trace_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hstrengthened : StrengthenedFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hstrengthened.toCollisionStandardOfTracePackage
    interp hspec htrace hembed).collision

theorem irrational_of_strengthened_trace_package'
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hstrengthened : StrengthenedFiniteConsistencyLowerBoundPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbedding) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_strengthened_trace_package interp hstrengthened hspec htrace
    (hembed.on partialConsistencyCode)

def CalibratedExternalStrengthenedLowerBoundSource.toCollisionStandardOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : CalibratedExternalStrengthenedLowerBoundSource)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toPackage.toCollisionStandardOfHilbertTrace interp hspec htrace hembed

def CalibratedExternalStrengthenedLowerBoundSource.toCollisionStandardOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : CalibratedExternalStrengthenedLowerBoundSource)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toPackage.toCollisionStandardOfTracePackage interp hspec htrace hembed

theorem irrational_of_calibrated_external_strengthened_hilbert_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : CalibratedExternalStrengthenedLowerBoundSource)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardOfHilbertTrace
    interp hspec htrace hembed).collision

theorem irrational_of_calibrated_external_strengthened_trace_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : CalibratedExternalStrengthenedLowerBoundSource)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardOfTracePackage
    interp hspec htrace hembed).collision

theorem irrational_of_calibrated_external_strengthened_trace_package'
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : CalibratedExternalStrengthenedLowerBoundSource)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbedding) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_calibrated_external_strengthened_trace_package
    interp hsource hspec htrace (hembed.on partialConsistencyCode)

def StrengthenedConsistencyRescalingPackage.toCollisionStandardOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : StrengthenedConsistencyRescalingPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toPackage.toCollisionStandardOfHilbertTrace interp hspec htrace hembed

def StrengthenedConsistencyRescalingPackage.toCollisionStandardOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : StrengthenedConsistencyRescalingPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toPackage.toCollisionStandardOfTracePackage interp hspec htrace hembed

def StrengthenedTimeConstructibleRescalingTheorem.toCollisionStandardOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : StrengthenedTimeConstructibleRescalingTheorem)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toPackage.toCollisionStandardOfHilbertTrace interp hspec htrace hembed

def StrengthenedTimeConstructibleRescalingTheorem.toCollisionStandardOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : StrengthenedTimeConstructibleRescalingTheorem)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toPackage.toCollisionStandardOfTracePackage interp hspec htrace hembed

theorem irrational_of_rescaled_strengthened_hilbert_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hrescaled : StrengthenedConsistencyRescalingPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hrescaled.toCollisionStandardOfHilbertTrace
    interp hspec htrace hembed).collision

theorem irrational_of_rescaled_strengthened_trace_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hrescaled : StrengthenedConsistencyRescalingPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hrescaled.toCollisionStandardOfTracePackage
    interp hspec htrace hembed).collision

theorem irrational_of_time_constructible_rescaled_strengthened_hilbert_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hrescaled : StrengthenedTimeConstructibleRescalingTheorem)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hrescaled.toCollisionStandardOfHilbertTrace
    interp hspec htrace hembed).collision

theorem irrational_of_time_constructible_rescaled_strengthened_trace_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hrescaled : StrengthenedTimeConstructibleRescalingTheorem)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hrescaled.toCollisionStandardOfTracePackage
    interp hspec htrace hembed).collision

def CalibratedRescaledExternalStrengthenedLowerBoundSource.toCollisionStandardOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : CalibratedRescaledExternalStrengthenedLowerBoundSource)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toPackage.toCollisionStandardOfHilbertTrace interp hspec htrace hembed

def CalibratedRescaledExternalStrengthenedLowerBoundSource.toCollisionStandardOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : CalibratedRescaledExternalStrengthenedLowerBoundSource)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toPackage.toCollisionStandardOfTracePackage interp hspec htrace hembed

theorem irrational_of_calibrated_rescaled_external_strengthened_hilbert_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : CalibratedRescaledExternalStrengthenedLowerBoundSource)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardOfHilbertTrace
    interp hspec htrace hembed).collision

theorem irrational_of_calibrated_rescaled_external_strengthened_trace_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : CalibratedRescaledExternalStrengthenedLowerBoundSource)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardOfTracePackage
    interp hspec htrace hembed).collision

theorem irrational_of_calibrated_rescaled_external_strengthened_trace_package'
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : CalibratedRescaledExternalStrengthenedLowerBoundSource)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbedding) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_calibrated_rescaled_external_strengthened_trace_package
    interp hsource hspec htrace (hembed.on partialConsistencyCode)

def PartialConsistencyLowerBoundNormalForm.toCollisionStandardOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : PartialConsistencyLowerBoundNormalForm)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toCollisionStandardOfTrace hspec
    (interp.toPartialConsistencyAcceptedS21TraceRealizationOfPayloadSpec
      hspec htrace)
    hembed

def PartialConsistencyLowerBoundNormalForm.toCollisionStandardOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : PartialConsistencyLowerBoundNormalForm)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toCollisionStandardOfHilbertTrace interp hspec
    (PartialConsistencyHilbertS21TraceSoundness.of_payload_spec_and_verifier_trace
      hspec
      (htrace.trace_soundness
        partialConsistencyCode fixed_verifier_encoding_partialConsistencyCode))
    hembed

def RawPudlakStrengthenedLowerBoundSource.toNormalFormCollisionStandardOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : RawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalForm hpartial).toCollisionStandardOfHilbertTrace
    interp hspec htrace hembed

def RawPudlakStrengthenedLowerBoundSource.toNormalFormCollisionStandardOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : RawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalForm hpartial).toCollisionStandardOfTracePackage
    interp hspec htrace hembed

theorem RawPudlakStrengthenedLowerBoundSource.normalFormCollisionStandardOfHilbertTrace_eq
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : RawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    h.toNormalFormCollisionStandardOfHilbertTrace
      hpartial interp hspec htrace hembed =
      (h.toNormalForm hpartial).toCollisionStandardOfHilbertTrace
        interp hspec htrace hembed := by
  rfl

theorem irrational_of_raw_pudlak_strengthened_hilbert_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : RawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toNormalFormCollisionStandardOfHilbertTrace
    hpartial interp hspec htrace hembed).collision

theorem irrational_of_raw_pudlak_strengthened_trace_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : RawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toNormalFormCollisionStandardOfTracePackage
    hpartial interp hspec htrace hembed).collision

def RescaledRawPudlakStrengthenedLowerBoundSource.toNormalFormCollisionStandardOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : RescaledRawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalForm hpartial).toCollisionStandardOfHilbertTrace
    interp hspec htrace hembed

def RescaledRawPudlakStrengthenedLowerBoundSource.toNormalFormCollisionStandardOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : RescaledRawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalForm hpartial).toCollisionStandardOfTracePackage
    interp hspec htrace hembed

theorem RescaledRawPudlakStrengthenedLowerBoundSource.normalFormCollisionStandardOfHilbertTrace_eq
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : RescaledRawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    h.toNormalFormCollisionStandardOfHilbertTrace
      hpartial interp hspec htrace hembed =
      (h.toNormalForm hpartial).toCollisionStandardOfHilbertTrace
        interp hspec htrace hembed := by
  rfl

theorem irrational_of_rescaled_raw_pudlak_strengthened_hilbert_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : RescaledRawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toNormalFormCollisionStandardOfHilbertTrace
    hpartial interp hspec htrace hembed).collision

theorem irrational_of_rescaled_raw_pudlak_strengthened_trace_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : RescaledRawPudlakStrengthenedLowerBoundSource)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toNormalFormCollisionStandardOfTracePackage
    hpartial interp hspec htrace hembed).collision

def LiteraturePudlakTheorem5StandardInstance.toNormalFormCollisionStandardOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5StandardInstance)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toLowerBoundSource.toNormalFormCollisionStandardOfHilbertTrace
    hpartial interp hspec htrace hembed

def LiteraturePudlakTheorem5StandardInstance.toNormalFormCollisionStandardOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5StandardInstance)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toLowerBoundSource.toNormalFormCollisionStandardOfTracePackage
    hpartial interp hspec htrace hembed

theorem irrational_of_literature_pudlak_theorem5_hilbert_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5StandardInstance)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toNormalFormCollisionStandardOfHilbertTrace
    hpartial interp hspec htrace hembed).collision

theorem irrational_of_literature_pudlak_theorem5_trace_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5StandardInstance)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toNormalFormCollisionStandardOfTracePackage
    hpartial interp hspec htrace hembed).collision

def LiteraturePudlakTheorem5LowerBoundCertificate.toNormalFormCollisionStandardOfHilbertTrace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toStandardInstance.toNormalFormCollisionStandardOfHilbertTrace
    hpartial interp hspec htrace hembed

def LiteraturePudlakTheorem5LowerBoundCertificate.toNormalFormCollisionStandardOfTracePackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  h.toStandardInstance.toNormalFormCollisionStandardOfTracePackage
    hpartial interp hspec htrace hembed

def LiteraturePudlakTheorem5LowerBoundCertificate.toCollisionStandardHilbertTraceOfProjection
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyProjection)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalFormOfProjection hpartial).toCollisionStandardOfHilbertTrace
    interp hspec htrace hembed

def LiteraturePudlakTheorem5LowerBoundCertificate.toCollisionStandardHilbertTraceOfAccepted
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hprinciple : PAProofLengthProjectionPrinciple)
    (haccepted : PartialToStrengthenedAcceptedProjection)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalFormOfAcceptedProjection hprinciple haccepted)
    |>.toCollisionStandardOfHilbertTrace interp hspec htrace hembed

def LiteraturePudlakTheorem5LowerBoundCertificate.toCollisionStandardHilbertTraceOfAcceptedPackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpackage : StrengthenedToPartialAcceptedProjectionPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalFormOfAcceptedProjectionPackage hpackage)
    |>.toCollisionStandardOfHilbertTrace interp hspec htrace hembed

def LiteraturePudlakTheorem5LowerBoundCertificate.toCollisionStandardTracePackageOfProjection
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyProjection)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalFormOfProjection hpartial).toCollisionStandardOfTracePackage
    interp hspec htrace hembed

def LiteraturePudlakTheorem5LowerBoundCertificate.toCollisionStandardTracePackageOfAccepted
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hprinciple : PAProofLengthProjectionPrinciple)
    (haccepted : PartialToStrengthenedAcceptedProjection)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalFormOfAcceptedProjection hprinciple haccepted)
    |>.toCollisionStandardOfTracePackage interp hspec htrace hembed

def LiteraturePudlakTheorem5LowerBoundCertificate.toCollisionStandardTracePackageOfAcceptedPackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpackage : StrengthenedToPartialAcceptedProjectionPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalFormOfAcceptedProjectionPackage hpackage)
    |>.toCollisionStandardOfTracePackage interp hspec htrace hembed

def LiteraturePudlakTheorem5LowerBoundCertificate.toCollisionStandardOfVerifiedAcceptedPackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpackage : StrengthenedToPartialAcceptedProjectionPackage)
    (hverify : SondowCollapseVerificationBridgePackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PartialConsistencyCollisionStandard :=
  h.toCollisionStandardTracePackageOfAcceptedPackage
    hpackage interp hverify.toPayloadSpec hverify.trace_package
    (hverify.pa_embedding.on partialConsistencyCode)

structure LiteraturePudlakVerifiedCollisionPackage where
  lower_bound_certificate : LiteraturePudlakTheorem5LowerBoundCertificate
  accepted_projection_package : StrengthenedToPartialAcceptedProjectionPackage
  collapse_verification : SondowCollapseVerificationBridgePackage

def LiteraturePudlakVerifiedCollisionPackage.ofStrengthenedAcceptedTruth
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hprinciple : PAProofLengthProjectionPrinciple)
    (hstrengthened : StrengthenedPartialConsistencyAcceptedTruth)
    (hverify : SondowCollapseVerificationBridgePackage) :
    LiteraturePudlakVerifiedCollisionPackage where
  lower_bound_certificate := hsource
  accepted_projection_package :=
    StrengthenedToPartialAcceptedProjectionPackage.ofStrengthenedAcceptedTruth
      hprinciple hstrengthened
  collapse_verification := hverify

def LiteraturePudlakVerifiedCollisionPackage.ofStrengthenedPayloadTruth
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hprinciple : PAProofLengthProjectionPrinciple)
    (hstrengthened : StrengthenedPartialConsistencyPayloadTruth)
    (hverify : SondowCollapseVerificationBridgePackage) :
    LiteraturePudlakVerifiedCollisionPackage :=
  LiteraturePudlakVerifiedCollisionPackage.ofStrengthenedAcceptedTruth
    hsource hprinciple hstrengthened.toAcceptedTruth hverify

def LiteraturePudlakVerifiedCollisionPackage.toCollisionStandard
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakVerifiedCollisionPackage)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PartialConsistencyCollisionStandard :=
  h.lower_bound_certificate.toCollisionStandardOfVerifiedAcceptedPackage
    h.accepted_projection_package h.collapse_verification interp


def LiteraturePudlakTheorem5LowerBoundCertificate.toCollisionStandardHilbertTraceOfLinearProjection
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLinearProjection)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalFormOfLinearProjection hpartial).toCollisionStandardOfHilbertTrace
    interp hspec htrace hembed

def LiteraturePudlakTheorem5LowerBoundCertificate.toCollisionStandardTracePackageOfLinearProjection
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLinearProjection)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalFormOfLinearProjection hpartial).toCollisionStandardOfTracePackage
    interp hspec htrace hembed

def LiteraturePudlakTheorem5LowerBoundCertificate.toCollisionStandardHilbertTraceOfConstant
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyConstantProjection)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalFormOfConstantProjection hpartial).toCollisionStandardOfHilbertTrace
    interp hspec htrace hembed

def LiteraturePudlakTheorem5LowerBoundCertificate.toCollisionStandardTracePackageOfConstant
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyConstantProjection)
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    PartialConsistencyCollisionStandard :=
  (h.toNormalFormOfConstantProjection hpartial).toCollisionStandardOfTracePackage
    interp hspec htrace hembed

theorem irrational_of_literature_pudlak_theorem5_lower_bound_certificate_hilbert_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toNormalFormCollisionStandardOfHilbertTrace
    hpartial interp hspec htrace hembed).collision

theorem irrational_of_literature_pudlak_theorem5_lower_bound_certificate_trace_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLowerBoundTransfer)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toNormalFormCollisionStandardOfTracePackage
    hpartial interp hspec htrace hembed).collision

theorem irrational_of_literature_pudlak_theorem5_certificate_hilbert_trace_projection
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyProjection)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardHilbertTraceOfProjection
    hpartial interp hspec htrace hembed).collision

theorem irrational_of_literature_pudlak_theorem5_certificate_trace_package_projection
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyProjection)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardTracePackageOfProjection
    hpartial interp hspec htrace hembed).collision

theorem irrational_of_literature_pudlak_theorem5_certificate_hilbert_trace_accepted_projection
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hprinciple : PAProofLengthProjectionPrinciple)
    (haccepted : PartialToStrengthenedAcceptedProjection)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardHilbertTraceOfAccepted
    hprinciple haccepted interp hspec htrace hembed).collision

theorem irrational_of_literature_pudlak_theorem5_certificate_trace_package_accepted_projection
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hprinciple : PAProofLengthProjectionPrinciple)
    (haccepted : PartialToStrengthenedAcceptedProjection)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardTracePackageOfAccepted
    hprinciple haccepted interp hspec htrace hembed).collision

theorem irrational_of_literature_pudlak_theorem5_certificate_hilbert_trace_accepted_pkg
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpackage : StrengthenedToPartialAcceptedProjectionPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardHilbertTraceOfAcceptedPackage
    hpackage interp hspec htrace hembed).collision

theorem irrational_of_literature_pudlak_theorem5_certificate_trace_package_accepted_pkg
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpackage : StrengthenedToPartialAcceptedProjectionPackage)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardTracePackageOfAcceptedPackage
    hpackage interp hspec htrace hembed).collision

theorem irrational_of_literature_pudlak_theorem5_certificate_verified_accepted_pkg
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpackage : StrengthenedToPartialAcceptedProjectionPackage)
    (hverify : SondowCollapseVerificationBridgePackage) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardOfVerifiedAcceptedPackage
    hpackage hverify interp).collision

theorem irrational_of_literature_pudlak_verified_collision_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (h : LiteraturePudlakVerifiedCollisionPackage) :
    ¬ (is_rational euler_mascheroni) :=
  (h.toCollisionStandard interp).collision

structure LiteraturePudlakVerifiedCollisionInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  interpretation : FormulaCodeHilbertInterpretation Ax A B halign
  collision_package : LiteraturePudlakVerifiedCollisionPackage

abbrev LiteraturePudlakDefaultVerifiedCollisionInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  LiteraturePudlakVerifiedCollisionInputs
    Ax A B hilbert_projection_code_alignment_true

def LiteraturePudlakVerifiedCollisionInputs.ofPackages
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hpackage : LiteraturePudlakVerifiedCollisionPackage) :
    LiteraturePudlakVerifiedCollisionInputs Ax A B halign where
  interpretation := interp
  collision_package := hpackage

theorem LiteraturePudlakVerifiedCollisionInputs.ofPackages_interpretation
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hpackage : LiteraturePudlakVerifiedCollisionPackage) :
    (LiteraturePudlakVerifiedCollisionInputs.ofPackages
      interp hpackage).interpretation = interp := by
  rfl

theorem LiteraturePudlakVerifiedCollisionInputs.ofPackages_collisionPackage
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hpackage : LiteraturePudlakVerifiedCollisionPackage) :
    (LiteraturePudlakVerifiedCollisionInputs.ofPackages
      interp hpackage).collision_package = hpackage := by
  rfl

theorem LiteraturePudlakVerifiedCollisionInputs.toCollisionStandard_eq
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakVerifiedCollisionInputs Ax A B halign) :
    h.collision_package.toCollisionStandard h.interpretation =
      h.collision_package.lower_bound_certificate.toCollisionStandardOfVerifiedAcceptedPackage
          h.collision_package.accepted_projection_package
          h.collision_package.collapse_verification h.interpretation := by
  rfl

def LiteraturePudlakVerifiedCollisionInputs.ofStrengthenedAcceptedTruth
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hprinciple : PAProofLengthProjectionPrinciple)
    (hstrengthened : StrengthenedPartialConsistencyAcceptedTruth)
    (hverify : SondowCollapseVerificationBridgePackage) :
    LiteraturePudlakVerifiedCollisionInputs Ax A B halign :=
  LiteraturePudlakVerifiedCollisionInputs.ofPackages interp
    (LiteraturePudlakVerifiedCollisionPackage.ofStrengthenedAcceptedTruth
      hsource hprinciple hstrengthened hverify)

def LiteraturePudlakVerifiedCollisionInputs.ofStrengthenedPayloadTruth
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hprinciple : PAProofLengthProjectionPrinciple)
    (hstrengthened : StrengthenedPartialConsistencyPayloadTruth)
    (hverify : SondowCollapseVerificationBridgePackage) :
    LiteraturePudlakVerifiedCollisionInputs Ax A B halign :=
  LiteraturePudlakVerifiedCollisionInputs.ofStrengthenedAcceptedTruth
    interp hsource hprinciple hstrengthened.toAcceptedTruth hverify

theorem irrational_of_literature_pudlak_verified_collision_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakVerifiedCollisionInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_literature_pudlak_verified_collision_package
    h.interpretation h.collision_package

theorem irrational_of_literature_pudlak_theorem5_certificate_hilbert_trace_linear_projection
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLinearProjection)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardHilbertTraceOfLinearProjection
    hpartial interp hspec htrace hembed).collision

theorem irrational_of_literature_pudlak_theorem5_certificate_trace_package_linear_projection
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyLinearProjection)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardTracePackageOfLinearProjection
    hpartial interp hspec htrace hembed).collision

theorem irrational_of_literature_pudlak_theorem5_certificate_hilbert_trace_constant_projection
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyConstantProjection)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardHilbertTraceOfConstant
    hpartial interp hspec htrace hembed).collision

theorem irrational_of_literature_pudlak_theorem5_certificate_trace_package_constant_projection
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpartial : StrengthenedToPartialConsistencyConstantProjection)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hsource.toCollisionStandardTracePackageOfConstant
    hpartial interp hspec htrace hembed).collision

theorem irrational_of_partial_consistency_lower_bound_normal_form_hilbert_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hnormal : PartialConsistencyLowerBoundNormalForm)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hnormal.toCollisionStandardOfHilbertTrace
    interp hspec htrace hembed).collision

theorem irrational_of_partial_consistency_lower_bound_normal_form_trace_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hnormal : PartialConsistencyLowerBoundNormalForm)
    (hspec : PartialConsistencyPayloadSpec)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hnormal.toCollisionStandardOfTracePackage
    interp hspec htrace hembed).collision

theorem irrational_of_buss_pudlak_hilbert_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hpkg : BussPudlakPartialConsistencySpecPackage)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hpkg.toFixedSpecProvider.toCollisionStandardOfTrace
    (interp.toPartialConsistencyAcceptedS21TraceRealizationOfPayloadSpec
      hpkg.payload_spec htrace)
    hembed).collision

theorem irrational_of_buss_pudlak_verifier_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hpkg : BussPudlakPartialConsistencySpecPackage)
    (hsound : S21VerifierTraceSoundness partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_buss_pudlak_hilbert_trace interp hpkg
    (PartialConsistencyHilbertS21TraceSoundness.of_payload_spec_and_verifier_trace
      hpkg.payload_spec hsound)
    hembed

theorem irrational_of_buss_pudlak_trace_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hpkg : BussPudlakPartialConsistencySpecPackage)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_buss_pudlak_verifier_trace interp hpkg
    (htrace.trace_soundness
      partialConsistencyCode fixed_verifier_encoding_partialConsistencyCode)
    hembed

theorem irrational_of_buss_pudlak_trace_package'
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hpkg : BussPudlakPartialConsistencySpecPackage)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbedding) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_buss_pudlak_trace_package interp hpkg htrace
    (hembed.on partialConsistencyCode)

theorem irrational_of_buss_pudlak_rescaled_hilbert_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hpkg : BussPudlakRescaledPartialConsistencySpecPackage)
    (htrace : PartialConsistencyHilbertS21TraceSoundness interp)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  (hpkg.toFixedSpecProvider.toCollisionStandardOfTrace
    (interp.toPartialConsistencyAcceptedS21TraceRealizationOfPayloadSpec
      hpkg.payload_spec htrace)
    hembed).collision

theorem irrational_of_buss_pudlak_rescaled_verifier_trace
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hpkg : BussPudlakRescaledPartialConsistencySpecPackage)
    (hsound : S21VerifierTraceSoundness partialConsistencyCode)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_buss_pudlak_rescaled_hilbert_trace interp hpkg
    (PartialConsistencyHilbertS21TraceSoundness.of_payload_spec_and_verifier_trace
      hpkg.payload_spec hsound)
    hembed

theorem irrational_of_buss_pudlak_rescaled_trace_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hpkg : BussPudlakRescaledPartialConsistencySpecPackage)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbeddingOn partialConsistencyCode) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_buss_pudlak_rescaled_verifier_trace interp hpkg
    (htrace.trace_soundness
      partialConsistencyCode fixed_verifier_encoding_partialConsistencyCode)
    hembed

theorem irrational_of_buss_pudlak_rescaled_trace_package'
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hpkg : BussPudlakRescaledPartialConsistencySpecPackage)
    (htrace : S21VerifierTracePackage)
    (hembed : S21ToPALinearEmbedding) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_buss_pudlak_rescaled_trace_package interp hpkg htrace
    (hembed.on partialConsistencyCode)
