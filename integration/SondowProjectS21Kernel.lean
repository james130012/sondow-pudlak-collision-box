/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowShortProofUpperBridge
import EulerLimit.InputCore

open BoundedArithmeticLab

namespace SondowMainCheckedCodeBridge

universe u

/-!
## Project-local S²₁ trace kernel

This module formalizes the S²₁ coverage actually needed by the current Sondow
short-proof route.  It intentionally does not claim a global
`S21VerifierTracePackage`; it covers exactly the three fixed verifier families
used by the reflection-graft collapse:

* `sondowCertificateValidCode`
* `partialConsistencyCode`
* `sondowReflectionGraftCode`
-/

inductive SondowProjectS21Family
  | sondowCertificate
  | partialConsistency
  | reflectionGraft
  deriving DecidableEq, Repr

namespace SondowProjectS21Family

def code : SondowProjectS21Family → ℕ → _root_.FormulaCode
  | sondowCertificate => _root_.sondowCertificateValidCode
  | partialConsistency => _root_.partialConsistencyCode
  | reflectionGraft => _root_.sondowReflectionGraftCode

def fixedVerifierEncoding
    (family : SondowProjectS21Family) :
    _root_.FixedVerifierEncoding family.code := by
  cases family
  · exact _root_.fixed_verifier_encoding_sondowCertificateValidCode
  · exact _root_.fixed_verifier_encoding_partialConsistencyCode
  · exact _root_.fixed_verifier_encoding_sondowReflectionGraftCode

end SondowProjectS21Family

/-- The exact family set covered by the project-local S²₁ kernel. -/
def SondowProjectS21CoveredFamily (φ : ℕ → _root_.FormulaCode) : Prop :=
  φ = _root_.sondowCertificateValidCode ∨
    φ = _root_.partialConsistencyCode ∨
      φ = _root_.sondowReflectionGraftCode

theorem sondowProjectS21CoveredFamily_iff_exists_family
    {φ : ℕ → _root_.FormulaCode} :
    SondowProjectS21CoveredFamily φ ↔
      ∃ family : SondowProjectS21Family,
        φ = family.code := by
  constructor
  · intro hcovered
    rcases hcovered with hsondow | hpartial | hreflection
    · exact ⟨SondowProjectS21Family.sondowCertificate, hsondow⟩
    · exact ⟨SondowProjectS21Family.partialConsistency, hpartial⟩
    · exact ⟨SondowProjectS21Family.reflectionGraft, hreflection⟩
  · intro hfamily
    rcases hfamily with ⟨family, hφ⟩
    cases family
    · exact Or.inl hφ
    · exact Or.inr (Or.inl hφ)
    · exact Or.inr (Or.inr hφ)

theorem SondowProjectS21CoveredFamily.fixedVerifierEncoding
    {φ : ℕ → _root_.FormulaCode}
    (hcovered : SondowProjectS21CoveredFamily φ) :
    _root_.FixedVerifierEncoding φ := by
  rcases (sondowProjectS21CoveredFamily_iff_exists_family.mp hcovered) with
    ⟨family, hφ⟩
  subst hφ
  exact family.fixedVerifierEncoding

/-- The minimal local S²₁ trace kernel needed by the current project.  It keeps
the two primitive trace obligations and the fixed graft-conjunction proof step
separate; the reflection-graft trace is derived, not assumed. -/
structure SondowProjectLocalS21Kernel where
  sondow_trace :
    _root_.S21VerifierTraceSoundness _root_.sondowCertificateValidCode
  partial_consistency_trace :
    _root_.S21VerifierTraceSoundness _root_.partialConsistencyCode
  graft_intro : _root_.ReflectionGraftS21ConjunctionIntroduction

namespace SondowProjectLocalS21Kernel

def traceComposition
    (kernel : SondowProjectLocalS21Kernel) :
    _root_.ReflectionGraftS21TraceComposition :=
  kernel.graft_intro.toTraceComposition
    kernel.sondow_trace kernel.partial_consistency_trace

def reflection_trace
    (kernel : SondowProjectLocalS21Kernel) :
    _root_.S21VerifierTraceSoundness _root_.sondowReflectionGraftCode :=
  kernel.traceComposition.toTraceSoundness

def traceSoundness
    (kernel : SondowProjectLocalS21Kernel)
    (family : SondowProjectS21Family) :
    _root_.S21VerifierTraceSoundness family.code := by
  cases family
  · exact kernel.sondow_trace
  · exact kernel.partial_consistency_trace
  · exact kernel.reflection_trace

theorem traceSoundness_of_covered
    (kernel : SondowProjectLocalS21Kernel)
    {φ : ℕ → _root_.FormulaCode}
    (hcovered : SondowProjectS21CoveredFamily φ) :
    _root_.S21VerifierTraceSoundness φ := by
  rcases (sondowProjectS21CoveredFamily_iff_exists_family.mp hcovered) with
    ⟨family, hφ⟩
  subst hφ
  exact kernel.traceSoundness family

theorem short_s21_proofs_of_covered
    (kernel : SondowProjectLocalS21Kernel)
    {φ : ℕ → _root_.FormulaCode}
    (hcovered : SondowProjectS21CoveredFamily φ) :
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∀ n : ℕ, _root_.accepted_certificate (φ n) →
        _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize (φ n) ≤ f n :=
  (kernel.traceSoundness_of_covered hcovered).to_short_s21_proofs
    hcovered.fixedVerifierEncoding

def toNarrowCollapseVerificationBridgeInputs
    (kernel : SondowProjectLocalS21Kernel)
    (htruth : _root_.PartialConsistencyAcceptedTruth)
    (hembed :
      _root_.S21ToPALinearEmbeddingOn
        _root_.sondowReflectionGraftCode) :
    SondowNarrowCollapseVerificationBridgeInputs where
  partial_accepted_truth := htruth
  sondow_trace := kernel.sondow_trace
  partial_consistency_trace := kernel.partial_consistency_trace
  graft_intro := kernel.graft_intro
  pa_embedding := hembed

theorem eventual_pa_short_proofs_of_reproof_rationality
    (kernel : SondowProjectLocalS21Kernel)
    (htruth : _root_.PartialConsistencyAcceptedTruth)
    (hembed :
      _root_.S21ToPALinearEmbeddingOn
        _root_.sondowReflectionGraftCode)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.accepted_certificate
            (_root_.sondowReflectionGraftCode n) ∧
          _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) ≤ f n :=
  (kernel.toNarrowCollapseVerificationBridgeInputs htruth hembed)
    |>.eventual_pa_short_proofs_of_reproof_rationality h_rat

def ofGlobalTraceAndGraftIntro
    (htrace : _root_.S21VerifierTracePackage)
    (hgraft : _root_.ReflectionGraftS21ConjunctionIntroduction) :
    SondowProjectLocalS21Kernel where
  sondow_trace :=
    htrace.trace_soundness
      _root_.sondowCertificateValidCode
      _root_.fixed_verifier_encoding_sondowCertificateValidCode
  partial_consistency_trace :=
    htrace.trace_soundness
      _root_.partialConsistencyCode
      _root_.fixed_verifier_encoding_partialConsistencyCode
  graft_intro := hgraft

end SondowProjectLocalS21Kernel

/-- A source-oriented form of the local kernel.  This is the next practical
target for replacing trace assumptions by concrete checked-code compilers. -/
structure SondowProjectLocalS21KernelSources where
  sondow_realization :
    _root_.AcceptedCertificateS21TraceRealization.{u}
      _root_.sondowCertificateValidCode
  partial_consistency_realization :
    _root_.AcceptedCertificateS21TraceRealization.{u}
      _root_.partialConsistencyCode
  graft_intro : _root_.ReflectionGraftS21ConjunctionIntroduction

def SondowProjectLocalS21KernelSources.toKernel
    (sources : SondowProjectLocalS21KernelSources.{u}) :
    SondowProjectLocalS21Kernel where
  sondow_trace := sources.sondow_realization.toS21VerifierTraceSoundness
  partial_consistency_trace :=
    sources.partial_consistency_realization.toS21VerifierTraceSoundness
  graft_intro := sources.graft_intro

/-- A calibrated checked-code source for one verifier family.  This is the
audit layer that still has to be closed for the final unconditional theorem:
the checked-code semantics must be accompanied by the exact S²₁ proof-length
bound used by `AcceptedCertificateS21TraceRealization`. -/
structure CheckedCodeS21TraceCalibration
    (φ : ℕ → _root_.FormulaCode) where
  accepted_code_semantics :
    _root_.AcceptedCertificateCodeSemantics.{u} φ
  checked_code_has_short_s21_proof :
    ∀ n : ℕ,
      ∀ c : accepted_code_semantics.proof_code_semantics.Code,
        accepted_code_semantics.proof_code_semantics.checks c (φ n) →
          _root_.proof_length _root_.ProofSystem.S21
              _root_.ProofLengthMeasure.symbolSize (φ n) ≤
            _root_.proof_predicate_formula_size φ n

def CheckedCodeS21TraceCalibration.toTraceRealization
    {φ : ℕ → _root_.FormulaCode}
    (h : CheckedCodeS21TraceCalibration.{u} φ) :
    _root_.AcceptedCertificateS21TraceRealization φ where
  accepted_code_semantics := h.accepted_code_semantics
  checked_code_has_short_s21_proof :=
    h.checked_code_has_short_s21_proof

def CheckedCodeS21TraceCalibration.toTraceSoundness
    {φ : ℕ → _root_.FormulaCode}
    (h : CheckedCodeS21TraceCalibration.{u} φ) :
    _root_.S21VerifierTraceSoundness φ :=
  h.toTraceRealization.toS21VerifierTraceSoundness

def CheckedCodeS21TraceCalibration.ofTraceSoundness
    {φ : ℕ → _root_.FormulaCode}
    (hsem : _root_.AcceptedCertificateCodeSemantics.{u} φ)
    (hsound : _root_.S21VerifierTraceSoundness φ) :
    CheckedCodeS21TraceCalibration.{u} φ where
  accepted_code_semantics := hsem
  checked_code_has_short_s21_proof := by
    intro n c hchecks
    exact hsound.short_proof_from_accepting_trace n
      (hsem.accepted_of_checked hchecks)

def acceptedCertificateCodeSemanticsULift
    {φ : ℕ → _root_.FormulaCode}
    (hsem : _root_.AcceptedCertificateCodeSemantics.{0} φ) :
    _root_.AcceptedCertificateCodeSemantics.{u} φ where
  relevant := hsem.relevant
  proof_code_semantics := {
    Code := ULift.{u} hsem.proof_code_semantics.Code
    checks := fun c code =>
      hsem.proof_code_semantics.checks c.down code
    size := fun c => hsem.proof_code_semantics.size c.down
    complete := by
      intro code hcode
      rcases hsem.proof_code_semantics.complete code hcode with
        ⟨c, hchecks⟩
      exact ⟨ULift.up c, hchecks⟩ }
  relevant_family := hsem.relevant_family
  checks_sound := by
    intro c n hchecks
    exact hsem.checks_sound c.down n hchecks
  checks_complete := by
    intro n hacc
    rcases hsem.checks_complete n hacc with ⟨c, hchecks⟩
    exact ⟨ULift.up c, hchecks⟩

/-- Standard partial-consistency checked-code calibration.  The semantic part is
fixed by the payload truth object; only the S²₁ proof-length check remains as a
real proof-system calibration obligation. -/
structure PartialConsistencyStandardS21TraceCalibration where
  payload_truth : _root_.PartialConsistencyPayloadTruth
  trace_soundness :
    _root_.S21VerifierTraceSoundness
      _root_.partialConsistencyCode

namespace PartialConsistencyStandardS21TraceCalibration

def payloadSpec
    (h : PartialConsistencyStandardS21TraceCalibration) :
    _root_.PartialConsistencyPayloadSpec :=
  _root_.PartialConsistencyPayloadSpec.standard h.payload_truth

def codeSemantics
    (h : PartialConsistencyStandardS21TraceCalibration) :
    _root_.AcceptedCertificateCodeSemantics.{u}
      _root_.partialConsistencyCode :=
  acceptedCertificateCodeSemanticsULift
    (_root_.partialConsistencyAcceptedCertificateCodeSemantics h.payloadSpec)

def toCalibration
    (h : PartialConsistencyStandardS21TraceCalibration) :
    CheckedCodeS21TraceCalibration.{u}
      _root_.partialConsistencyCode :=
  CheckedCodeS21TraceCalibration.ofTraceSoundness
    h.codeSemantics h.trace_soundness

def ofPayloadTruthAndTraceSoundness
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hsound :
      _root_.S21VerifierTraceSoundness
        _root_.partialConsistencyCode) :
    PartialConsistencyStandardS21TraceCalibration where
  payload_truth := htruth
  trace_soundness := hsound

def ofAcceptedTruthAndTraceSoundness
    (htruth : _root_.PartialConsistencyAcceptedTruth)
    (hsound :
      _root_.S21VerifierTraceSoundness
        _root_.partialConsistencyCode) :
    PartialConsistencyStandardS21TraceCalibration :=
  ofPayloadTruthAndTraceSoundness htruth.toPayloadTruth hsound

end PartialConsistencyStandardS21TraceCalibration

/-- The two concrete checked-code trace calibrations needed by the local S²₁
kernel.  The reflection-graft trace is derived from these two sources plus the
fixed graft-introduction proof step. -/
structure SondowProjectLocalS21TraceCalibrationSources where
  sondow_calibration :
    CheckedCodeS21TraceCalibration.{u}
      _root_.sondowCertificateValidCode
  partial_consistency_calibration :
    CheckedCodeS21TraceCalibration.{u}
      _root_.partialConsistencyCode
  graft_intro : _root_.ReflectionGraftS21ConjunctionIntroduction

def SondowProjectLocalS21TraceCalibrationSources.toKernelSources
    (sources : SondowProjectLocalS21TraceCalibrationSources.{u}) :
    SondowProjectLocalS21KernelSources.{u} where
  sondow_realization :=
    sources.sondow_calibration.toTraceRealization
  partial_consistency_realization :=
    sources.partial_consistency_calibration.toTraceRealization
  graft_intro := sources.graft_intro

def SondowProjectLocalS21TraceCalibrationSources.toKernel
    (sources : SondowProjectLocalS21TraceCalibrationSources.{u}) :
    SondowProjectLocalS21Kernel :=
  sources.toKernelSources.toKernel

/-- Primitive project-local kernel sources with the partial-consistency semantic
side fixed to the standard payload code.  This is equivalent to the previous
calibration-source package but gives auditors a single payload-truth origin for
both the partial-consistency verifier and the reflection-graft payload. -/
structure SondowProjectLocalS21PrimitiveKernelSources where
  sondow_calibration :
    CheckedCodeS21TraceCalibration.{u}
      _root_.sondowCertificateValidCode
  partial_standard_calibration :
    PartialConsistencyStandardS21TraceCalibration
  graft_intro : _root_.ReflectionGraftS21ConjunctionIntroduction

def SondowProjectLocalS21PrimitiveKernelSources.toTraceCalibrationSources
    (sources : SondowProjectLocalS21PrimitiveKernelSources.{u}) :
    SondowProjectLocalS21TraceCalibrationSources.{u} where
  sondow_calibration := sources.sondow_calibration
  partial_consistency_calibration :=
    sources.partial_standard_calibration.toCalibration
  graft_intro := sources.graft_intro

def SondowProjectLocalS21PrimitiveKernelSources.toKernel
    (sources : SondowProjectLocalS21PrimitiveKernelSources.{u}) :
    SondowProjectLocalS21Kernel :=
  sources.toTraceCalibrationSources.toKernel

/-- Exact completion package for the project-local short-proof collapse route.
Supplying this package is precisely what remains before one may call the
reflection-graft PA upper bound unconditional inside the current project scope. -/
structure SondowProjectLocalS21CollapseCompletion where
  trace_sources :
    SondowProjectLocalS21TraceCalibrationSources.{u}
  partial_accepted_truth : _root_.PartialConsistencyAcceptedTruth
  pa_embedding :
    _root_.S21ToPALinearEmbeddingOn
      _root_.sondowReflectionGraftCode

/-- A less redundant completion package.  The partial-consistency truth field is
carried once, inside the standard partial-consistency calibration, and is then
used both for the partial verifier semantics and for the reflection-graft
payload. -/
structure SondowProjectLocalS21PrimitiveCollapseCompletion where
  primitive_sources :
    SondowProjectLocalS21PrimitiveKernelSources.{u}
  pa_embedding :
    _root_.S21ToPALinearEmbeddingOn
      _root_.sondowReflectionGraftCode

def SondowProjectLocalS21PrimitiveCollapseCompletion.toCompletion
    (h : SondowProjectLocalS21PrimitiveCollapseCompletion.{u}) :
    SondowProjectLocalS21CollapseCompletion.{u} where
  trace_sources := h.primitive_sources.toTraceCalibrationSources
  partial_accepted_truth :=
    h.primitive_sources.partial_standard_calibration.payload_truth
      |>.toAcceptedTruth
  pa_embedding := h.pa_embedding

def SondowProjectLocalS21CollapseCompletion.toPrimitiveCompletion
    (h : SondowProjectLocalS21CollapseCompletion.{u}) :
    SondowProjectLocalS21PrimitiveCollapseCompletion.{u} where
  primitive_sources := {
    sondow_calibration := h.trace_sources.sondow_calibration
    partial_standard_calibration :=
      PartialConsistencyStandardS21TraceCalibration.ofAcceptedTruthAndTraceSoundness
        h.partial_accepted_truth
        h.trace_sources.partial_consistency_calibration.toTraceSoundness
    graft_intro := h.trace_sources.graft_intro }
  pa_embedding := h.pa_embedding

theorem sondowProjectLocalS21PrimitiveCompletion_nonempty_iff_completion_nonempty :
    Nonempty SondowProjectLocalS21PrimitiveCollapseCompletion.{u} ↔
      Nonempty SondowProjectLocalS21CollapseCompletion.{u} := by
  constructor
  · intro h
    rcases h with ⟨completion⟩
    exact ⟨completion.toCompletion⟩
  · intro h
    rcases h with ⟨completion⟩
    exact ⟨completion.toPrimitiveCompletion⟩

/-- The genuinely minimal project-local completion package for the collapse
endpoint.  It avoids the stronger `AcceptedCertificateCodeSemantics` requirement
for `sondowCertificateValidCode`: the upper-bound route only needs S²₁ trace
soundness for the Sondow verifier family, not a total checked-code semantics for
every Sondow index. -/
structure SondowProjectLocalS21TraceCollapseCompletion where
  sondow_trace :
    _root_.S21VerifierTraceSoundness
      _root_.sondowCertificateValidCode
  partial_standard_calibration :
    PartialConsistencyStandardS21TraceCalibration
  graft_intro : _root_.ReflectionGraftS21ConjunctionIntroduction
  pa_embedding :
    _root_.S21ToPALinearEmbeddingOn
      _root_.sondowReflectionGraftCode

namespace SondowProjectLocalS21TraceCollapseCompletion

def toKernel
    (h : SondowProjectLocalS21TraceCollapseCompletion) :
    SondowProjectLocalS21Kernel where
  sondow_trace := h.sondow_trace
  partial_consistency_trace :=
    h.partial_standard_calibration.trace_soundness
  graft_intro := h.graft_intro

def toNarrowBridge
    (h : SondowProjectLocalS21TraceCollapseCompletion) :
    SondowNarrowCollapseVerificationBridgeInputs where
  partial_accepted_truth :=
    h.partial_standard_calibration.payload_truth.toAcceptedTruth
  sondow_trace := h.sondow_trace
  partial_consistency_trace :=
    h.partial_standard_calibration.trace_soundness
  graft_intro := h.graft_intro
  pa_embedding := h.pa_embedding

theorem eventual_pa_short_proofs_of_reproof_rationality
    (h : SondowProjectLocalS21TraceCollapseCompletion)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.accepted_certificate
            (_root_.sondowReflectionGraftCode n) ∧
          _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) ≤ f n :=
  h.toNarrowBridge.eventual_pa_short_proofs_of_reproof_rationality h_rat

def toPrimitiveCompletion
    (h : SondowProjectLocalS21TraceCollapseCompletion)
    (hsem :
      _root_.AcceptedCertificateCodeSemantics.{u}
        _root_.sondowCertificateValidCode) :
    SondowProjectLocalS21PrimitiveCollapseCompletion.{u} where
  primitive_sources := {
    sondow_calibration :=
      CheckedCodeS21TraceCalibration.ofTraceSoundness
        hsem h.sondow_trace
    partial_standard_calibration := h.partial_standard_calibration
    graft_intro := h.graft_intro }
  pa_embedding := h.pa_embedding

end SondowProjectLocalS21TraceCollapseCompletion

def SondowProjectLocalS21PrimitiveCollapseCompletion.toTraceCompletion
    (h : SondowProjectLocalS21PrimitiveCollapseCompletion.{u}) :
    SondowProjectLocalS21TraceCollapseCompletion where
  sondow_trace :=
    h.primitive_sources.sondow_calibration.toTraceSoundness
  partial_standard_calibration :=
    h.primitive_sources.partial_standard_calibration
  graft_intro := h.primitive_sources.graft_intro
  pa_embedding := h.pa_embedding

def SondowNarrowCollapseVerificationBridgeInputs.toProjectTraceCompletion
    (h : SondowNarrowCollapseVerificationBridgeInputs) :
    SondowProjectLocalS21TraceCollapseCompletion where
  sondow_trace := h.sondow_trace
  partial_standard_calibration :=
    PartialConsistencyStandardS21TraceCalibration.ofAcceptedTruthAndTraceSoundness
      h.partial_accepted_truth
      h.partial_consistency_trace
  graft_intro := h.graft_intro
  pa_embedding := h.pa_embedding

def SondowCollapseVerificationBridgeInputs.toProjectTraceCompletion
    (h : SondowCollapseVerificationBridgeInputs)
    (hgraft : _root_.ReflectionGraftS21ConjunctionIntroduction) :
    SondowProjectLocalS21TraceCollapseCompletion :=
  (SondowNarrowCollapseVerificationBridgeInputs.ofGlobalBridgeInputsAndGraftIntro
    h hgraft)
    |>.toProjectTraceCompletion

def projectTraceCompletionOfCollapseVerificationBridgePackage
    (h : _root_.SondowCollapseVerificationBridgePackage)
    (hgraft : _root_.ReflectionGraftS21ConjunctionIntroduction) :
    SondowProjectLocalS21TraceCollapseCompletion :=
  SondowCollapseVerificationBridgeInputs.toProjectTraceCompletion
    { partial_payload_truth := h.partial_accepted_truth.toPayloadTruth
      trace_package := h.trace_package
      pa_embedding := h.pa_embedding }
    hgraft

def SondowProjectLocalS21TraceCollapseCompletion.ofComponentTraceInputs
    (hcomponent : _root_.ReflectionGraftComponentTraceInputs)
    (htruth : _root_.PartialConsistencyPayloadTruth) :
    SondowProjectLocalS21TraceCollapseCompletion where
  sondow_trace := hcomponent.sondow_trace
  partial_standard_calibration :=
    PartialConsistencyStandardS21TraceCalibration.ofPayloadTruthAndTraceSoundness
      htruth
      hcomponent.partial_consistency_trace
  graft_intro := hcomponent.graft_intro
  pa_embedding := hcomponent.pa_embedding

/-- Component-level inputs equivalent to the trace-only project completion:
component trace data plus the payload truth used to interpret the partial
consistency family. -/
structure SondowProjectLocalS21TraceCollapseComponentPayloadInputs where
  component_trace : _root_.ReflectionGraftComponentTraceInputs
  payload_truth : _root_.PartialConsistencyPayloadTruth

def SondowProjectLocalS21TraceCollapseComponentPayloadInputs.toTraceCompletion
    (h : SondowProjectLocalS21TraceCollapseComponentPayloadInputs) :
    SondowProjectLocalS21TraceCollapseCompletion :=
  SondowProjectLocalS21TraceCollapseCompletion.ofComponentTraceInputs
    h.component_trace h.payload_truth

def SondowProjectLocalS21TraceCollapseCompletion.toComponentTraceInputs
    (h : SondowProjectLocalS21TraceCollapseCompletion) :
    _root_.ReflectionGraftComponentTraceInputs where
  sondow_trace := h.sondow_trace
  partial_consistency_trace :=
    h.partial_standard_calibration.trace_soundness
  graft_intro := h.graft_intro
  pa_embedding := h.pa_embedding

def SondowProjectLocalS21TraceCollapseCompletion.toComponentPayloadInputs
    (h : SondowProjectLocalS21TraceCollapseCompletion) :
    SondowProjectLocalS21TraceCollapseComponentPayloadInputs where
  component_trace := h.toComponentTraceInputs
  payload_truth := h.partial_standard_calibration.payload_truth

theorem sondowProjectLocalS21TraceCompletion_nonempty_iff_componentTraceAndPayloadTruth_nonempty :
    Nonempty SondowProjectLocalS21TraceCollapseCompletion ↔
      Nonempty
        SondowProjectLocalS21TraceCollapseComponentPayloadInputs := by
  constructor
  · intro h
    rcases h with ⟨completion⟩
    exact ⟨completion.toComponentPayloadInputs⟩
  · intro h
    rcases h with ⟨inputs⟩
    exact ⟨inputs.toTraceCompletion⟩

/-- Direct trace completion for the short-proof collapse endpoint.  This is
strictly shorter than the component-trace route: it only needs an already built
reflection-graft concrete verification package plus the partial-consistency
payload truth used to obtain eventual accepted graft certificates. -/
structure SondowProjectLocalDirectTraceCollapseCompletion where
  concrete_verification :
    _root_.ReflectionGraftConcreteVerificationPackage
  payload_truth : _root_.PartialConsistencyPayloadTruth

namespace SondowProjectLocalDirectTraceCollapseCompletion

def toPayloadInputs
    (h : SondowProjectLocalDirectTraceCollapseCompletion) :
    _root_.ReflectionGraftPayloadInputs :=
  _root_.reflection_graft_payload_inputs_of_partial_consistency_truth
    h.payload_truth

def toTraceInputs
    (h : SondowProjectLocalDirectTraceCollapseCompletion) :
    _root_.ReflectionGraftTraceInputs where
  trace_soundness := h.concrete_verification.trace_soundness
  pa_embedding := h.concrete_verification.pa_embedding

theorem eventual_pa_short_proofs_of_reproof_rationality
    (h : SondowProjectLocalDirectTraceCollapseCompletion)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.accepted_certificate
            (_root_.sondowReflectionGraftCode n) ∧
          _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) ≤ f n :=
  h.toTraceInputs.eventual_short_proofs_of_rationality
    _root_.SondowForwardInputs.of_reproof
    h.toPayloadInputs
    h_rat

end SondowProjectLocalDirectTraceCollapseCompletion

def SondowCollapseVerificationBridgeInputs.toProjectDirectTraceCompletion
    (h : SondowCollapseVerificationBridgeInputs) :
    SondowProjectLocalDirectTraceCollapseCompletion where
  concrete_verification :=
    _root_.reflection_graft_concrete_verification_package_of_global_inputs
      h.trace_package h.pa_embedding
  payload_truth := h.partial_payload_truth

def projectDirectTraceCompletionOfCollapseVerificationBridgePackage
    (h : _root_.SondowCollapseVerificationBridgePackage) :
    SondowProjectLocalDirectTraceCollapseCompletion where
  concrete_verification :=
    _root_.SondowCollapseVerificationBridgePackage.toReflectionGraftConcreteVerification
      h
  payload_truth :=
    (_root_.SondowCollapseVerificationBridgePackage.toPayloadSpec h)
      |>.toPayloadTruth

def GammaIrrationalityMainInputs.toProjectDirectTraceCompletion
    (h : _root_.GammaIrrationalityMainInputs) :
    SondowProjectLocalDirectTraceCollapseCompletion where
  concrete_verification := h.concrete_verification
  payload_truth := h.partial_payload_truth

def GammaIrrationalityVerifiedMainInputs.toProjectDirectTraceCompletion
    (h : _root_.GammaIrrationalityVerifiedMainInputs) :
    SondowProjectLocalDirectTraceCollapseCompletion :=
  GammaIrrationalityMainInputs.toProjectDirectTraceCompletion h.toMainInputs

def GammaIrrationalityExactProjectionInputs.toProjectDirectTraceCompletion
    (h : _root_.GammaIrrationalityExactProjectionInputs) :
    SondowProjectLocalDirectTraceCollapseCompletion :=
  GammaIrrationalityMainInputs.toProjectDirectTraceCompletion h.toMainInputs

def GammaIrrationalityVerifiedExactProjectionInputs.toProjectDirectTraceCompletion
    (h : _root_.GammaIrrationalityVerifiedExactProjectionInputs) :
    SondowProjectLocalDirectTraceCollapseCompletion :=
  GammaIrrationalityMainInputs.toProjectDirectTraceCompletion h.toMainInputs

def GammaIrrationalityTargetExactProjectionInputs.toProjectDirectTraceCompletion
    (h : _root_.GammaIrrationalityTargetExactProjectionInputs) :
    SondowProjectLocalDirectTraceCollapseCompletion :=
  GammaIrrationalityMainInputs.toProjectDirectTraceCompletion h.toMainInputs

def GammaIrrationalityVerifiedTargetExactProjectionInputs.toProjectDirectTraceCompletion
    (h : _root_.GammaIrrationalityVerifiedTargetExactProjectionInputs) :
    SondowProjectLocalDirectTraceCollapseCompletion :=
  GammaIrrationalityMainInputs.toProjectDirectTraceCompletion h.toMainInputs

theorem sondowProjectLocalDirectTraceCompletion_nonempty_iff_concreteVerificationAndPayloadTruth_nonempty :
    Nonempty SondowProjectLocalDirectTraceCollapseCompletion ↔
      Nonempty _root_.ReflectionGraftConcreteVerificationPackage ∧
        Nonempty _root_.PartialConsistencyPayloadTruth := by
  constructor
  · intro h
    rcases h with ⟨completion⟩
    exact
      ⟨⟨completion.concrete_verification⟩,
        ⟨completion.payload_truth⟩⟩
  · intro h
    rcases h with ⟨hverification, htruth⟩
    rcases hverification with ⟨verification⟩
    rcases htruth with ⟨truth⟩
    exact
      ⟨{ concrete_verification := verification
         payload_truth := truth }⟩

/-- The installed project-local reflection-graft verifier.  It is the exact
S²₁-to-PA verifier object used by the collapse route: the S²₁ side is derived
from the local kernel, while the PA side is the explicit local linear embedding
for the final reflection-graft family. -/
structure SondowProjectLocalReflectionGraftVerifier where
  kernel : SondowProjectLocalS21Kernel
  pa_embedding :
    _root_.S21ToPALinearEmbeddingOn
      _root_.sondowReflectionGraftCode

namespace SondowProjectLocalReflectionGraftVerifier

def traceSoundness
    (verifier : SondowProjectLocalReflectionGraftVerifier) :
    _root_.S21VerifierTraceSoundness
      _root_.sondowReflectionGraftCode :=
  verifier.kernel.reflection_trace

def traceInputs
    (verifier : SondowProjectLocalReflectionGraftVerifier) :
    _root_.ReflectionGraftTraceInputs where
  trace_soundness := verifier.traceSoundness
  pa_embedding := verifier.pa_embedding

def concreteVerificationPackage
    (verifier : SondowProjectLocalReflectionGraftVerifier) :
    _root_.ReflectionGraftConcreteVerificationPackage where
  trace_soundness := verifier.traceSoundness
  pa_embedding := verifier.pa_embedding

def toNarrowBridge
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyAcceptedTruth) :
    SondowNarrowCollapseVerificationBridgeInputs :=
  verifier.kernel.toNarrowCollapseVerificationBridgeInputs
    htruth verifier.pa_embedding

def toDirectTraceCompletion
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth) :
    SondowProjectLocalDirectTraceCollapseCompletion where
  concrete_verification := verifier.concreteVerificationPackage
  payload_truth := htruth

theorem short_pa_proofs_of_accepted_certificates
    (verifier : SondowProjectLocalReflectionGraftVerifier) :
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∀ n : ℕ,
        _root_.accepted_certificate
          (_root_.sondowReflectionGraftCode n) →
          _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowReflectionGraftCode n) ≤ f n :=
  verifier.concreteVerificationPackage
    |>.toShortProofBridge
    |>.accepted_certificates_have_short_proofs

theorem eventual_pa_short_proofs_of_reproof_rationality
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.accepted_certificate
            (_root_.sondowReflectionGraftCode n) ∧
          _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) ≤ f n :=
  (verifier.toDirectTraceCompletion htruth)
    |>.eventual_pa_short_proofs_of_reproof_rationality h_rat

end SondowProjectLocalReflectionGraftVerifier

def SondowProjectLocalS21Kernel.toReflectionGraftVerifier
    (kernel : SondowProjectLocalS21Kernel)
    (hembed :
      _root_.S21ToPALinearEmbeddingOn
        _root_.sondowReflectionGraftCode) :
    SondowProjectLocalReflectionGraftVerifier where
  kernel := kernel
  pa_embedding := hembed

theorem sondowProjectLocalReflectionGraftVerifier_nonempty_iff_kernelAndPAEmbedding_nonempty :
    Nonempty SondowProjectLocalReflectionGraftVerifier ↔
      Nonempty SondowProjectLocalS21Kernel ∧
        Nonempty
          (_root_.S21ToPALinearEmbeddingOn
            _root_.sondowReflectionGraftCode) := by
  constructor
  · intro h
    rcases h with ⟨verifier⟩
    exact ⟨⟨verifier.kernel⟩, ⟨verifier.pa_embedding⟩⟩
  · intro h
    rcases h with ⟨hkernel, hembed⟩
    rcases hkernel with ⟨kernel⟩
    rcases hembed with ⟨embed⟩
    exact ⟨kernel.toReflectionGraftVerifier embed⟩

theorem verifierAndPayloadTruth_nonempty_to_projectDirectTraceCompletion_nonempty
    (h :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :
    Nonempty SondowProjectLocalDirectTraceCollapseCompletion := by
  rcases h with ⟨hverifier, htruth⟩
  rcases hverifier with ⟨verifier⟩
  rcases htruth with ⟨truth⟩
  exact ⟨verifier.toDirectTraceCompletion truth⟩

/-- Cost/absorption presentation of the component-trace completion.  This is the
auditable way to build the component route from a global S²₁ trace package:
the proof-calculus cost and the predicate-size absorption are separate fields. -/
structure SondowProjectLocalS21TraceCollapseCostAbsorptionInputs where
  trace_package : _root_.S21VerifierTracePackage
  graft_cost : _root_.S21GraftConjunctionIntroductionCost
  graft_absorption :
    _root_.ReflectionGraftPredicateAbsorption graft_cost.C
  pa_embedding :
    _root_.S21ToPALinearEmbeddingOn
      _root_.sondowReflectionGraftCode
  payload_truth : _root_.PartialConsistencyPayloadTruth

namespace SondowProjectLocalS21TraceCollapseCostAbsorptionInputs

def toComponentTraceInputs
    (h : SondowProjectLocalS21TraceCollapseCostAbsorptionInputs) :
    _root_.ReflectionGraftComponentTraceInputs :=
  _root_.ReflectionGraftComponentTraceInputs.ofGlobalTraceCostAndAbsorption
    h.trace_package h.graft_cost h.graft_absorption h.pa_embedding

def toComponentPayloadInputs
    (h : SondowProjectLocalS21TraceCollapseCostAbsorptionInputs) :
    SondowProjectLocalS21TraceCollapseComponentPayloadInputs where
  component_trace := h.toComponentTraceInputs
  payload_truth := h.payload_truth

def toTraceCompletion
    (h : SondowProjectLocalS21TraceCollapseCostAbsorptionInputs) :
    SondowProjectLocalS21TraceCollapseCompletion :=
  h.toComponentPayloadInputs.toTraceCompletion

def ofGlobalEmbedding
    (htrace : _root_.S21VerifierTracePackage)
    (hcost : _root_.S21GraftConjunctionIntroductionCost)
    (habsorb :
      _root_.ReflectionGraftPredicateAbsorption hcost.C)
    (hembed : _root_.S21ToPALinearEmbedding)
    (htruth : _root_.PartialConsistencyPayloadTruth) :
    SondowProjectLocalS21TraceCollapseCostAbsorptionInputs where
  trace_package := htrace
  graft_cost := hcost
  graft_absorption := habsorb
  pa_embedding := hembed.on _root_.sondowReflectionGraftCode
  payload_truth := htruth

end SondowProjectLocalS21TraceCollapseCostAbsorptionInputs

def SondowCollapseVerificationBridgeInputs.toCostAbsorptionInputs
    (h : SondowCollapseVerificationBridgeInputs)
    (hcost : _root_.S21GraftConjunctionIntroductionCost)
    (habsorb :
      _root_.ReflectionGraftPredicateAbsorption hcost.C) :
    SondowProjectLocalS21TraceCollapseCostAbsorptionInputs :=
  SondowProjectLocalS21TraceCollapseCostAbsorptionInputs.ofGlobalEmbedding
    h.trace_package hcost habsorb h.pa_embedding h.partial_payload_truth

def SondowCollapseVerificationBridgeInputs.toComponentPayloadInputsOfCostAndAbsorption
    (h : SondowCollapseVerificationBridgeInputs)
    (hcost : _root_.S21GraftConjunctionIntroductionCost)
    (habsorb :
      _root_.ReflectionGraftPredicateAbsorption hcost.C) :
    SondowProjectLocalS21TraceCollapseComponentPayloadInputs :=
  (h.toCostAbsorptionInputs hcost habsorb).toComponentPayloadInputs

def collapseVerificationBridgePackage_toCostAbsorptionInputs
    (h : _root_.SondowCollapseVerificationBridgePackage)
    (hcost : _root_.S21GraftConjunctionIntroductionCost)
    (habsorb :
      _root_.ReflectionGraftPredicateAbsorption hcost.C) :
    SondowProjectLocalS21TraceCollapseCostAbsorptionInputs :=
  SondowProjectLocalS21TraceCollapseCostAbsorptionInputs.ofGlobalEmbedding
    h.trace_package hcost habsorb h.pa_embedding
    h.partial_accepted_truth.toPayloadTruth

theorem sondowProjectLocalS21TraceCompletion_nonempty_iff_narrowBridge_nonempty :
    Nonempty SondowProjectLocalS21TraceCollapseCompletion ↔
      Nonempty SondowNarrowCollapseVerificationBridgeInputs := by
  constructor
  · intro h
    rcases h with ⟨completion⟩
    exact ⟨completion.toNarrowBridge⟩
  · intro h
    rcases h with ⟨bridge⟩
    exact ⟨bridge.toProjectTraceCompletion⟩

theorem sondowProjectLocalS21PrimitiveCompletion_nonempty_to_traceCompletion_nonempty :
    Nonempty SondowProjectLocalS21PrimitiveCollapseCompletion.{u} →
      Nonempty SondowProjectLocalS21TraceCollapseCompletion := by
  intro h
  rcases h with ⟨completion⟩
  exact ⟨completion.toTraceCompletion⟩

theorem sondowProjectLocalS21TraceCompletion_nonempty_iff_primitiveCompletion_nonempty_of_semantics
    (hsem :
      _root_.AcceptedCertificateCodeSemantics.{u}
        _root_.sondowCertificateValidCode) :
    Nonempty SondowProjectLocalS21TraceCollapseCompletion ↔
      Nonempty SondowProjectLocalS21PrimitiveCollapseCompletion.{u} := by
  constructor
  · intro h
    rcases h with ⟨completion⟩
    exact ⟨completion.toPrimitiveCompletion hsem⟩
  · exact
      sondowProjectLocalS21PrimitiveCompletion_nonempty_to_traceCompletion_nonempty

/-- The exact final collapse conclusion used by the short-proof route.  It is
separated as a named proposition so audit statements can say exactly whether the
route has been closed, instead of silently changing hypotheses. -/
def SondowProjectLocalS21CollapseConclusion : Prop :=
  _root_.is_rational _root_.euler_mascheroni →
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.accepted_certificate
            (_root_.sondowReflectionGraftCode n) ∧
        _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) ≤ f n

/-- The final project-local inputs for the short-proof upper-bound route after
removing the global `S21VerifierTracePackage` dependency. -/
structure SondowProjectLocalS21CollapseInputs where
  kernel : SondowProjectLocalS21Kernel
  partial_accepted_truth : _root_.PartialConsistencyAcceptedTruth
  pa_embedding :
    _root_.S21ToPALinearEmbeddingOn _root_.sondowReflectionGraftCode

def SondowProjectLocalS21CollapseInputs.toNarrowBridge
    (h : SondowProjectLocalS21CollapseInputs) :
    SondowNarrowCollapseVerificationBridgeInputs :=
  h.kernel.toNarrowCollapseVerificationBridgeInputs
    h.partial_accepted_truth h.pa_embedding

theorem SondowProjectLocalS21CollapseInputs.eventual_pa_short_proofs_of_reproof_rationality
    (h : SondowProjectLocalS21CollapseInputs)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.accepted_certificate
            (_root_.sondowReflectionGraftCode n) ∧
          _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) ≤ f n :=
  h.toNarrowBridge.eventual_pa_short_proofs_of_reproof_rationality h_rat

def SondowProjectLocalS21CollapseInputs.ofSources
    (sources : SondowProjectLocalS21KernelSources.{u})
    (htruth : _root_.PartialConsistencyAcceptedTruth)
    (hembed :
      _root_.S21ToPALinearEmbeddingOn
        _root_.sondowReflectionGraftCode) :
    SondowProjectLocalS21CollapseInputs where
  kernel := sources.toKernel
  partial_accepted_truth := htruth
  pa_embedding := hembed

def SondowProjectLocalS21CollapseInputs.ofGlobalBridgeInputsAndGraftIntro
    (hglobal : SondowCollapseVerificationBridgeInputs)
    (hgraft : _root_.ReflectionGraftS21ConjunctionIntroduction) :
    SondowProjectLocalS21CollapseInputs where
  kernel :=
    SondowProjectLocalS21Kernel.ofGlobalTraceAndGraftIntro
      hglobal.trace_package hgraft
  partial_accepted_truth := hglobal.toPartialAcceptedTruth
  pa_embedding := hglobal.pa_embedding.on _root_.sondowReflectionGraftCode

theorem projectLocalS21Collapse_of_globalBridgeInputs_eventual_pa_short_proofs
    (hglobal : SondowCollapseVerificationBridgeInputs)
    (hgraft : _root_.ReflectionGraftS21ConjunctionIntroduction)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.accepted_certificate
            (_root_.sondowReflectionGraftCode n) ∧
          _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) ≤ f n :=
  (SondowProjectLocalS21CollapseInputs.ofGlobalBridgeInputsAndGraftIntro
    hglobal hgraft)
    |>.eventual_pa_short_proofs_of_reproof_rationality h_rat

def SondowProjectLocalS21TraceCollapseCompletion.toCollapseInputs
    (h : SondowProjectLocalS21TraceCollapseCompletion) :
    SondowProjectLocalS21CollapseInputs where
  kernel := h.toKernel
  partial_accepted_truth :=
    h.partial_standard_calibration.payload_truth.toAcceptedTruth
  pa_embedding := h.pa_embedding

theorem SondowProjectLocalS21TraceCollapseCompletion.toCollapseConclusion
    (h : SondowProjectLocalS21TraceCollapseCompletion) :
    SondowProjectLocalS21CollapseConclusion := by
  intro h_rat
  exact h.eventual_pa_short_proofs_of_reproof_rationality h_rat

theorem SondowProjectLocalS21TraceCollapseCompletion.nonempty_to_collapseConclusion
    (h : Nonempty SondowProjectLocalS21TraceCollapseCompletion) :
    SondowProjectLocalS21CollapseConclusion := by
  rcases h with ⟨completion⟩
  exact completion.toCollapseConclusion

theorem SondowProjectLocalDirectTraceCollapseCompletion.toCollapseConclusion
    (h : SondowProjectLocalDirectTraceCollapseCompletion) :
    SondowProjectLocalS21CollapseConclusion := by
  intro h_rat
  exact h.eventual_pa_short_proofs_of_reproof_rationality h_rat

theorem SondowProjectLocalDirectTraceCollapseCompletion.nonempty_to_collapseConclusion
    (h : Nonempty SondowProjectLocalDirectTraceCollapseCompletion) :
    SondowProjectLocalS21CollapseConclusion := by
  rcases h with ⟨completion⟩
  exact completion.toCollapseConclusion

theorem SondowProjectLocalReflectionGraftVerifier.toCollapseConclusion
    (verifier : SondowProjectLocalReflectionGraftVerifier)
    (htruth : _root_.PartialConsistencyPayloadTruth) :
    SondowProjectLocalS21CollapseConclusion :=
  (verifier.toDirectTraceCompletion htruth).toCollapseConclusion

theorem concreteVerificationAndPayloadTruth_nonempty_to_projectCollapseConclusion
    (h :
      Nonempty _root_.ReflectionGraftConcreteVerificationPackage ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.nonempty_to_collapseConclusion
    ((sondowProjectLocalDirectTraceCompletion_nonempty_iff_concreteVerificationAndPayloadTruth_nonempty).2
      h)

theorem verifierAndPayloadTruth_nonempty_to_projectCollapseConclusion
    (h :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty _root_.PartialConsistencyPayloadTruth) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.nonempty_to_collapseConclusion
    (verifierAndPayloadTruth_nonempty_to_projectDirectTraceCompletion_nonempty
      h)

theorem SondowCollapseVerificationBridgeInputs.toProjectDirectTraceCollapseConclusion
    (h : SondowCollapseVerificationBridgeInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  h.toProjectDirectTraceCompletion.toCollapseConclusion

theorem collapseVerificationBridgePackage_toProjectDirectTraceCollapseConclusion
    (h : _root_.SondowCollapseVerificationBridgePackage) :
    SondowProjectLocalS21CollapseConclusion :=
  (projectDirectTraceCompletionOfCollapseVerificationBridgePackage h)
    |>.toCollapseConclusion

theorem GammaIrrationalityMainInputs.toProjectDirectTraceCollapseConclusion
    (h : _root_.GammaIrrationalityMainInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.toCollapseConclusion
    (GammaIrrationalityMainInputs.toProjectDirectTraceCompletion h)

theorem GammaIrrationalityVerifiedMainInputs.toProjectDirectTraceCollapseConclusion
    (h : _root_.GammaIrrationalityVerifiedMainInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.toCollapseConclusion
    (GammaIrrationalityVerifiedMainInputs.toProjectDirectTraceCompletion h)

theorem GammaIrrationalityExactProjectionInputs.toProjectDirectTraceCollapseConclusion
    (h : _root_.GammaIrrationalityExactProjectionInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.toCollapseConclusion
    (GammaIrrationalityExactProjectionInputs.toProjectDirectTraceCompletion h)

theorem GammaIrrationalityVerifiedExactProjectionInputs.toProjectDirectTraceCollapseConclusion
    (h : _root_.GammaIrrationalityVerifiedExactProjectionInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.toCollapseConclusion
    (GammaIrrationalityVerifiedExactProjectionInputs.toProjectDirectTraceCompletion
      h)

theorem GammaIrrationalityTargetExactProjectionInputs.toProjectDirectTraceCollapseConclusion
    (h : _root_.GammaIrrationalityTargetExactProjectionInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.toCollapseConclusion
    (GammaIrrationalityTargetExactProjectionInputs.toProjectDirectTraceCompletion
      h)

theorem GammaIrrationalityVerifiedTargetExactProjectionInputs.toProjectDirectTraceCollapseConclusion
    (h : _root_.GammaIrrationalityVerifiedTargetExactProjectionInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.toCollapseConclusion
    (GammaIrrationalityVerifiedTargetExactProjectionInputs.toProjectDirectTraceCompletion
      h)

theorem gammaIrrationalityMainInputs_nonempty_to_projectDirectTraceCompletion_nonempty
    (h : Nonempty _root_.GammaIrrationalityMainInputs) :
    Nonempty SondowProjectLocalDirectTraceCollapseCompletion := by
  rcases h with ⟨inputs⟩
  exact ⟨GammaIrrationalityMainInputs.toProjectDirectTraceCompletion inputs⟩

theorem gammaIrrationalityVerifiedMainInputs_nonempty_to_projectDirectTraceCompletion_nonempty
    (h : Nonempty _root_.GammaIrrationalityVerifiedMainInputs) :
    Nonempty SondowProjectLocalDirectTraceCollapseCompletion := by
  rcases h with ⟨inputs⟩
  exact
    ⟨GammaIrrationalityVerifiedMainInputs.toProjectDirectTraceCompletion
      inputs⟩

theorem gammaIrrationalityExactProjectionInputs_nonempty_to_projectDirectTraceCompletion_nonempty
    (h : Nonempty _root_.GammaIrrationalityExactProjectionInputs) :
    Nonempty SondowProjectLocalDirectTraceCollapseCompletion := by
  rcases h with ⟨inputs⟩
  exact
    ⟨GammaIrrationalityExactProjectionInputs.toProjectDirectTraceCompletion
      inputs⟩

theorem gammaIrrationalityVerifiedExactProjectionInputs_nonempty_to_projectDirectTraceCompletion_nonempty
    (h : Nonempty _root_.GammaIrrationalityVerifiedExactProjectionInputs) :
    Nonempty SondowProjectLocalDirectTraceCollapseCompletion := by
  rcases h with ⟨inputs⟩
  exact
    ⟨GammaIrrationalityVerifiedExactProjectionInputs.toProjectDirectTraceCompletion
      inputs⟩

theorem gammaIrrationalityTargetExactProjectionInputs_nonempty_to_projectDirectTraceCompletion_nonempty
    (h : Nonempty _root_.GammaIrrationalityTargetExactProjectionInputs) :
    Nonempty SondowProjectLocalDirectTraceCollapseCompletion := by
  rcases h with ⟨inputs⟩
  exact
    ⟨GammaIrrationalityTargetExactProjectionInputs.toProjectDirectTraceCompletion
      inputs⟩

theorem gammaIrrationalityVerifiedTargetExactProjectionInputs_nonempty_to_projectDirectTraceCompletion_nonempty
    (h : Nonempty _root_.GammaIrrationalityVerifiedTargetExactProjectionInputs) :
    Nonempty SondowProjectLocalDirectTraceCollapseCompletion := by
  rcases h with ⟨inputs⟩
  exact
    ⟨GammaIrrationalityVerifiedTargetExactProjectionInputs.toProjectDirectTraceCompletion
      inputs⟩

theorem gammaIrrationalityMainInputs_nonempty_to_projectCollapseConclusion
    (h : Nonempty _root_.GammaIrrationalityMainInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.nonempty_to_collapseConclusion
    (gammaIrrationalityMainInputs_nonempty_to_projectDirectTraceCompletion_nonempty
      h)

theorem gammaIrrationalityVerifiedMainInputs_nonempty_to_projectCollapseConclusion
    (h : Nonempty _root_.GammaIrrationalityVerifiedMainInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.nonempty_to_collapseConclusion
    (gammaIrrationalityVerifiedMainInputs_nonempty_to_projectDirectTraceCompletion_nonempty
      h)

theorem gammaIrrationalityExactProjectionInputs_nonempty_to_projectCollapseConclusion
    (h : Nonempty _root_.GammaIrrationalityExactProjectionInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.nonempty_to_collapseConclusion
    (gammaIrrationalityExactProjectionInputs_nonempty_to_projectDirectTraceCompletion_nonempty
      h)

theorem gammaIrrationalityVerifiedExactProjectionInputs_nonempty_to_projectCollapseConclusion
    (h : Nonempty _root_.GammaIrrationalityVerifiedExactProjectionInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.nonempty_to_collapseConclusion
    (gammaIrrationalityVerifiedExactProjectionInputs_nonempty_to_projectDirectTraceCompletion_nonempty
      h)

theorem gammaIrrationalityTargetExactProjectionInputs_nonempty_to_projectCollapseConclusion
    (h : Nonempty _root_.GammaIrrationalityTargetExactProjectionInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.nonempty_to_collapseConclusion
    (gammaIrrationalityTargetExactProjectionInputs_nonempty_to_projectDirectTraceCompletion_nonempty
      h)

theorem gammaIrrationalityVerifiedTargetExactProjectionInputs_nonempty_to_projectCollapseConclusion
    (h : Nonempty _root_.GammaIrrationalityVerifiedTargetExactProjectionInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  SondowProjectLocalDirectTraceCollapseCompletion.nonempty_to_collapseConclusion
    (gammaIrrationalityVerifiedTargetExactProjectionInputs_nonempty_to_projectDirectTraceCompletion_nonempty
      h)

theorem SondowProjectLocalS21TraceCollapseCostAbsorptionInputs.toCollapseConclusion
    (h : SondowProjectLocalS21TraceCollapseCostAbsorptionInputs) :
    SondowProjectLocalS21CollapseConclusion :=
  h.toTraceCompletion.toCollapseConclusion

theorem SondowCollapseVerificationBridgeInputs.toCostAbsorptionCollapseConclusion
    (h : SondowCollapseVerificationBridgeInputs)
    (hcost : _root_.S21GraftConjunctionIntroductionCost)
    (habsorb :
      _root_.ReflectionGraftPredicateAbsorption hcost.C) :
    SondowProjectLocalS21CollapseConclusion :=
  (h.toCostAbsorptionInputs hcost habsorb).toCollapseConclusion

theorem collapseVerificationBridgePackage_toCostAbsorptionCollapseConclusion
    (h : _root_.SondowCollapseVerificationBridgePackage)
    (hcost : _root_.S21GraftConjunctionIntroductionCost)
    (habsorb :
      _root_.ReflectionGraftPredicateAbsorption hcost.C) :
    SondowProjectLocalS21CollapseConclusion :=
  (collapseVerificationBridgePackage_toCostAbsorptionInputs
    h hcost habsorb)
    |>.toCollapseConclusion

theorem SondowProjectLocalS21TraceCollapseCompletion.componentTraceAndPayloadTruth_toCollapseConclusion
    (hcomponent : _root_.ReflectionGraftComponentTraceInputs)
    (htruth : _root_.PartialConsistencyPayloadTruth) :
    SondowProjectLocalS21CollapseConclusion :=
  (SondowProjectLocalS21TraceCollapseCompletion.ofComponentTraceInputs
    hcomponent htruth)
    |>.toCollapseConclusion

theorem SondowCollapseVerificationBridgeInputs.toProjectTraceCollapseConclusion
    (h : SondowCollapseVerificationBridgeInputs)
    (hgraft : _root_.ReflectionGraftS21ConjunctionIntroduction) :
    SondowProjectLocalS21CollapseConclusion :=
  (h.toProjectTraceCompletion hgraft).toCollapseConclusion

theorem collapseVerificationBridgePackage_toProjectTraceCollapseConclusion
    (h : _root_.SondowCollapseVerificationBridgePackage)
    (hgraft : _root_.ReflectionGraftS21ConjunctionIntroduction) :
    SondowProjectLocalS21CollapseConclusion :=
  (projectTraceCompletionOfCollapseVerificationBridgePackage h hgraft)
    |>.toCollapseConclusion

def SondowProjectLocalS21CollapseCompletion.toCollapseInputs
    (h : SondowProjectLocalS21CollapseCompletion.{u}) :
    SondowProjectLocalS21CollapseInputs where
  kernel := h.trace_sources.toKernel
  partial_accepted_truth := h.partial_accepted_truth
  pa_embedding := h.pa_embedding

theorem SondowProjectLocalS21CollapseCompletion.toCollapseConclusion
    (h : SondowProjectLocalS21CollapseCompletion.{u}) :
    SondowProjectLocalS21CollapseConclusion := by
  intro h_rat
  exact h.toCollapseInputs.eventual_pa_short_proofs_of_reproof_rationality
    h_rat

theorem SondowProjectLocalS21CollapseCompletion.nonempty_to_collapseConclusion
    (h : Nonempty SondowProjectLocalS21CollapseCompletion.{u}) :
    SondowProjectLocalS21CollapseConclusion := by
  rcases h with ⟨completion⟩
  exact completion.toCollapseConclusion

theorem SondowProjectLocalS21PrimitiveCollapseCompletion.toCollapseConclusion
    (h : SondowProjectLocalS21PrimitiveCollapseCompletion.{u}) :
    SondowProjectLocalS21CollapseConclusion :=
  h.toCompletion.toCollapseConclusion

theorem SondowProjectLocalS21PrimitiveCollapseCompletion.nonempty_to_collapseConclusion
    (h : Nonempty SondowProjectLocalS21PrimitiveCollapseCompletion.{u}) :
    SondowProjectLocalS21CollapseConclusion := by
  rcases h with ⟨completion⟩
  exact completion.toCollapseConclusion

end SondowMainCheckedCodeBridge
