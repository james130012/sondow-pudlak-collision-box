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

def toReflectionGraftS21ShortVerificationBridge
    (kernel : SondowProjectLocalS21Kernel) :
    _root_.EventualShortVerificationBridge
      _root_.ProofSystem.S21 _root_.ProofLengthMeasure.symbolSize
      _root_.sondowReflectionGraftCode where
  verifier_polytime :=
    _root_.certificate_verifier_polytime_sondowReflectionGraftCode
  short_proofs_of_accepted_certificates :=
    kernel.short_s21_proofs_of_covered (Or.inr (Or.inr rfl))

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

/-- Accepted-code route to the partial-consistency payload truth.  This keeps
the witness on the standard verifier/code side until the final projection to
the raw payload predicate. -/
structure PartialConsistencyAcceptedCodeTruthCertificate : Prop where
  accepted_truth : _root_.PartialConsistencyAcceptedTruth

namespace PartialConsistencyAcceptedCodeTruthCertificate

theorem toPayloadTruth
    (h : PartialConsistencyAcceptedCodeTruthCertificate) :
    _root_.PartialConsistencyPayloadTruth :=
  h.accepted_truth.toPayloadTruth

def toPayloadSpec
    (h : PartialConsistencyAcceptedCodeTruthCertificate) :
    _root_.PartialConsistencyPayloadSpec :=
  _root_.PartialConsistencyPayloadSpec.ofAcceptedTruth h.accepted_truth

end PartialConsistencyAcceptedCodeTruthCertificate

/-- Payload-semantics route for partial consistency.  A concrete realization of
the standard partial-consistency code family is paired with accepted-code truth
for that realized family; the raw payload truth is derived through the recorded
acceptance equivalence. -/
structure PartialConsistencyPayloadSemanticsCertificate where
  code_realization : _root_.PartialConsistencyAcceptedCodeRealization
  accepted_all :
    ∀ n : ℕ,
      _root_.accepted_certificate (code_realization.code_family n)

namespace PartialConsistencyPayloadSemanticsCertificate

theorem toPayloadTruth
    (h : PartialConsistencyPayloadSemanticsCertificate) :
    _root_.PartialConsistencyPayloadTruth where
  true_all := by
    intro n
    exact (h.code_realization.accepted_exact n).1 (h.accepted_all n)

theorem toAcceptedTruth
    (h : PartialConsistencyPayloadSemanticsCertificate) :
    _root_.PartialConsistencyAcceptedTruth where
  accepted_all := by
    intro n
    rw [← h.code_realization.code_family_eq]
    exact h.accepted_all n

def toPayloadSpec
    (h : PartialConsistencyPayloadSemanticsCertificate) :
    _root_.PartialConsistencyPayloadSpec :=
  h.code_realization.toPayloadSpec h.toPayloadTruth

def ofAcceptedTruth
    (haccepted : _root_.PartialConsistencyAcceptedTruth) :
    PartialConsistencyPayloadSemanticsCertificate where
  code_realization := _root_.partial_consistency_accepted_code_realization_true
  accepted_all := haccepted.accepted_all

end PartialConsistencyPayloadSemanticsCertificate

/-- Finite-consistency reading route.  It separates the intended reading of the
standard code family from the accepted-code truth witness and only then derives
the raw payload truth. -/
structure PartialConsistencyFiniteConsistencyReadingCertificate : Prop where
  intended_reading : _root_.PartialConsistencyPayloadIntendedReading
  accepted_all :
    ∀ n : ℕ,
      _root_.accepted_certificate (_root_.partialConsistencyCode n)

namespace PartialConsistencyFiniteConsistencyReadingCertificate

theorem toPayloadTruth
    (h : PartialConsistencyFiniteConsistencyReadingCertificate) :
    _root_.PartialConsistencyPayloadTruth where
  true_all := by
    intro n
    exact (h.intended_reading.reads_as_conPA_symbol_length n).1
      (h.accepted_all n)

theorem toAcceptedTruth
    (h : PartialConsistencyFiniteConsistencyReadingCertificate) :
    _root_.PartialConsistencyAcceptedTruth where
  accepted_all := h.accepted_all

def ofAcceptedTruth
    (haccepted : _root_.PartialConsistencyAcceptedTruth) :
    PartialConsistencyFiniteConsistencyReadingCertificate where
  intended_reading :=
    _root_.partial_consistency_payload_intended_reading_true
  accepted_all := haccepted.accepted_all

end PartialConsistencyFiniteConsistencyReadingCertificate

/-- Payload-spec route.  This is still a witness boundary, but a more structured
one: it fixes the standard code family, acceptance semantics, and payload truth
inside the existing project-local specification object. -/
structure PartialConsistencyPayloadSpecCertificate where
  payload_spec : _root_.PartialConsistencyPayloadSpec

namespace PartialConsistencyPayloadSpecCertificate

theorem toPayloadTruth
    (h : PartialConsistencyPayloadSpecCertificate) :
    _root_.PartialConsistencyPayloadTruth :=
  h.payload_spec.toPayloadTruth

theorem toAcceptedTruth
    (h : PartialConsistencyPayloadSpecCertificate) :
    _root_.PartialConsistencyAcceptedTruth :=
  h.payload_spec.toAcceptedTruth

theorem accepted_standard
    (h : PartialConsistencyPayloadSpecCertificate) (n : ℕ) :
    _root_.accepted_certificate (_root_.partialConsistencyCode n) :=
  h.payload_spec.accepted_standard n

theorem accepted_standard_iff_payload
    (h : PartialConsistencyPayloadSpecCertificate) (n : ℕ) :
    _root_.accepted_certificate (_root_.partialConsistencyCode n) ↔
      _root_.partial_consistency_payload n :=
  h.payload_spec.accepted_standard_iff n

def toAcceptedCodeTruthCertificate
    (h : PartialConsistencyPayloadSpecCertificate) :
    PartialConsistencyAcceptedCodeTruthCertificate where
  accepted_truth := h.toAcceptedTruth

end PartialConsistencyPayloadSpecCertificate

namespace PartialConsistencyAcceptedCodeTruthCertificate

def toPayloadSemanticsCertificate
    (h : PartialConsistencyAcceptedCodeTruthCertificate) :
    PartialConsistencyPayloadSemanticsCertificate :=
  PartialConsistencyPayloadSemanticsCertificate.ofAcceptedTruth
    h.accepted_truth

def toFiniteConsistencyReadingCertificate
    (h : PartialConsistencyAcceptedCodeTruthCertificate) :
    PartialConsistencyFiniteConsistencyReadingCertificate :=
  PartialConsistencyFiniteConsistencyReadingCertificate.ofAcceptedTruth
    h.accepted_truth

def toPayloadSpecCertificate
    (h : PartialConsistencyAcceptedCodeTruthCertificate) :
    PartialConsistencyPayloadSpecCertificate where
  payload_spec := h.toPayloadSpec

end PartialConsistencyAcceptedCodeTruthCertificate

namespace PartialConsistencyPayloadSemanticsCertificate

def toAcceptedCodeTruthCertificate
    (h : PartialConsistencyPayloadSemanticsCertificate) :
    PartialConsistencyAcceptedCodeTruthCertificate where
  accepted_truth := h.toAcceptedTruth

def toFiniteConsistencyReadingCertificate
    (h : PartialConsistencyPayloadSemanticsCertificate) :
    PartialConsistencyFiniteConsistencyReadingCertificate :=
  PartialConsistencyFiniteConsistencyReadingCertificate.ofAcceptedTruth
    h.toAcceptedTruth

def toPayloadSpecCertificate
    (h : PartialConsistencyPayloadSemanticsCertificate) :
    PartialConsistencyPayloadSpecCertificate where
  payload_spec := h.toPayloadSpec

end PartialConsistencyPayloadSemanticsCertificate

namespace PartialConsistencyFiniteConsistencyReadingCertificate

def toAcceptedCodeTruthCertificate
    (h : PartialConsistencyFiniteConsistencyReadingCertificate) :
    PartialConsistencyAcceptedCodeTruthCertificate where
  accepted_truth := h.toAcceptedTruth

def toPayloadSemanticsCertificate
    (h : PartialConsistencyFiniteConsistencyReadingCertificate) :
    PartialConsistencyPayloadSemanticsCertificate :=
  PartialConsistencyPayloadSemanticsCertificate.ofAcceptedTruth
    h.toAcceptedTruth

def toPayloadSpecCertificate
    (h : PartialConsistencyFiniteConsistencyReadingCertificate) :
    PartialConsistencyPayloadSpecCertificate where
  payload_spec :=
    _root_.PartialConsistencyPayloadSpec.ofAcceptedTruth h.toAcceptedTruth

end PartialConsistencyFiniteConsistencyReadingCertificate

namespace PartialConsistencyPayloadSpecCertificate

def toPayloadSemanticsCertificate
    (h : PartialConsistencyPayloadSpecCertificate) :
    PartialConsistencyPayloadSemanticsCertificate :=
  PartialConsistencyPayloadSemanticsCertificate.ofAcceptedTruth
    h.toAcceptedTruth

def toFiniteConsistencyReadingCertificate
    (h : PartialConsistencyPayloadSpecCertificate) :
    PartialConsistencyFiniteConsistencyReadingCertificate :=
  PartialConsistencyFiniteConsistencyReadingCertificate.ofAcceptedTruth
    h.toAcceptedTruth

end PartialConsistencyPayloadSpecCertificate

theorem partialConsistencyAcceptedCodeTruthCertificate_nonempty_iff_payloadSemanticsCertificate_nonempty :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate ↔
      Nonempty PartialConsistencyPayloadSemanticsCertificate := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toPayloadSemanticsCertificate⟩
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toAcceptedCodeTruthCertificate⟩

theorem partialConsistencyAcceptedCodeTruthCertificate_nonempty_iff_finiteConsistencyReadingCertificate_nonempty :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate ↔
      Nonempty PartialConsistencyFiniteConsistencyReadingCertificate := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toFiniteConsistencyReadingCertificate⟩
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toAcceptedCodeTruthCertificate⟩

theorem partialConsistencyAcceptedCodeTruthCertificate_nonempty_iff_payloadSpecCertificate_nonempty :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate ↔
      Nonempty PartialConsistencyPayloadSpecCertificate := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toPayloadSpecCertificate⟩
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toAcceptedCodeTruthCertificate⟩

theorem partialConsistencyPayloadSemanticsCertificate_nonempty_iff_payloadSpecCertificate_nonempty :
    Nonempty PartialConsistencyPayloadSemanticsCertificate ↔
      Nonempty PartialConsistencyPayloadSpecCertificate := by
  calc
    Nonempty PartialConsistencyPayloadSemanticsCertificate ↔
        Nonempty PartialConsistencyAcceptedCodeTruthCertificate :=
      (partialConsistencyAcceptedCodeTruthCertificate_nonempty_iff_payloadSemanticsCertificate_nonempty).symm
    _ ↔ Nonempty PartialConsistencyPayloadSpecCertificate :=
      partialConsistencyAcceptedCodeTruthCertificate_nonempty_iff_payloadSpecCertificate_nonempty

theorem partialConsistencyFiniteConsistencyReadingCertificate_nonempty_iff_payloadSpecCertificate_nonempty :
    Nonempty PartialConsistencyFiniteConsistencyReadingCertificate ↔
      Nonempty PartialConsistencyPayloadSpecCertificate := by
  calc
    Nonempty PartialConsistencyFiniteConsistencyReadingCertificate ↔
        Nonempty PartialConsistencyAcceptedCodeTruthCertificate :=
      (partialConsistencyAcceptedCodeTruthCertificate_nonempty_iff_finiteConsistencyReadingCertificate_nonempty).symm
    _ ↔ Nonempty PartialConsistencyPayloadSpecCertificate :=
      partialConsistencyAcceptedCodeTruthCertificate_nonempty_iff_payloadSpecCertificate_nonempty

theorem partialConsistencyPayloadTruth_nonempty_ofAcceptedCodeTruthCertificate
    (h : Nonempty PartialConsistencyAcceptedCodeTruthCertificate) :
    Nonempty _root_.PartialConsistencyPayloadTruth := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toPayloadTruth⟩

theorem partialConsistencyPayloadTruth_nonempty_ofPayloadSemanticsCertificate
    (h : Nonempty PartialConsistencyPayloadSemanticsCertificate) :
    Nonempty _root_.PartialConsistencyPayloadTruth := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toPayloadTruth⟩

theorem partialConsistencyPayloadTruth_nonempty_ofFiniteConsistencyReadingCertificate
    (h : Nonempty PartialConsistencyFiniteConsistencyReadingCertificate) :
    Nonempty _root_.PartialConsistencyPayloadTruth := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toPayloadTruth⟩

theorem partialConsistencyPayloadTruth_nonempty_ofPayloadSpecCertificate
    (h : Nonempty PartialConsistencyPayloadSpecCertificate) :
    Nonempty _root_.PartialConsistencyPayloadTruth := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toPayloadTruth⟩

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

/-- Local certificate for the fixed graft-introduction step.  The cost and
predicate-absorption inputs are named separately by `ofCostAndAbsorption`. -/
structure SondowProjectLocalGraftIntroCertificate where
  graft_intro : _root_.ReflectionGraftS21ConjunctionIntroduction

namespace SondowProjectLocalGraftIntroCertificate

def ofCostAndAbsorption
    (hcost : _root_.S21GraftConjunctionIntroductionCost)
    (habsorb :
      _root_.ReflectionGraftPredicateAbsorption hcost.C) :
    SondowProjectLocalGraftIntroCertificate where
  graft_intro :=
    _root_.ReflectionGraftS21ConjunctionIntroduction.ofCostAndAbsorption
      hcost habsorb

end SondowProjectLocalGraftIntroCertificate

/-- Checked-code certificate for the Sondow verifier trace. -/
structure SondowProjectLocalSondowTraceCertificate where
  checked_code :
    CheckedCodeS21TraceCalibration.{u}
      _root_.sondowCertificateValidCode

namespace SondowProjectLocalSondowTraceCertificate

def traceSoundness
    (h : SondowProjectLocalSondowTraceCertificate.{u}) :
    _root_.S21VerifierTraceSoundness
      _root_.sondowCertificateValidCode :=
  h.checked_code.toTraceSoundness

end SondowProjectLocalSondowTraceCertificate

/-- Standard-code certificate for the partial-consistency trace.  The payload
truth remains internal to the standard calibration and is not asserted
unconditionally. -/
structure SondowProjectLocalPartialConsistencyTraceCertificate where
  standard_calibration : PartialConsistencyStandardS21TraceCalibration

namespace SondowProjectLocalPartialConsistencyTraceCertificate

def payloadTruth
    (h : SondowProjectLocalPartialConsistencyTraceCertificate) :
    _root_.PartialConsistencyPayloadTruth :=
  h.standard_calibration.payload_truth

def traceSoundness
    (h : SondowProjectLocalPartialConsistencyTraceCertificate) :
    _root_.S21VerifierTraceSoundness
      _root_.partialConsistencyCode :=
  h.standard_calibration.trace_soundness

def checkedCodeCalibration
    (h : SondowProjectLocalPartialConsistencyTraceCertificate) :
    CheckedCodeS21TraceCalibration.{u}
      _root_.partialConsistencyCode :=
  h.standard_calibration.toCalibration

end SondowProjectLocalPartialConsistencyTraceCertificate

/-- Partial-consistency trace sourced from the accepted-code truth certificate.
This is a structured input boundary: the payload truth is obtained from accepted
standard codes, then paired with the local S²₁ trace soundness witness. -/
structure PartialConsistencyAcceptedCodeTraceCertificate where
  accepted_truth : PartialConsistencyAcceptedCodeTruthCertificate
  trace_soundness :
    _root_.S21VerifierTraceSoundness
      _root_.partialConsistencyCode

namespace PartialConsistencyAcceptedCodeTraceCertificate

def toStandardTraceCalibration
    (h : PartialConsistencyAcceptedCodeTraceCertificate) :
    PartialConsistencyStandardS21TraceCalibration :=
  PartialConsistencyStandardS21TraceCalibration.ofAcceptedTruthAndTraceSoundness
    h.accepted_truth.accepted_truth h.trace_soundness

def toProjectLocalTraceCertificate
    (h : PartialConsistencyAcceptedCodeTraceCertificate) :
    SondowProjectLocalPartialConsistencyTraceCertificate where
  standard_calibration := h.toStandardTraceCalibration

theorem toPayloadTruth
    (h : PartialConsistencyAcceptedCodeTraceCertificate) :
    _root_.PartialConsistencyPayloadTruth :=
  h.accepted_truth.toPayloadTruth

end PartialConsistencyAcceptedCodeTraceCertificate

/-- Partial-consistency trace sourced from the payload-spec certificate.  This
keeps the accepted-code semantics, finite-consistency reading, and raw payload
truth inside `PartialConsistencyPayloadSpec` until the final local trace
calibration is built. -/
structure PartialConsistencyPayloadSpecTraceCertificate where
  payload_spec : PartialConsistencyPayloadSpecCertificate
  trace_soundness :
    _root_.S21VerifierTraceSoundness
      _root_.partialConsistencyCode

namespace PartialConsistencyPayloadSpecTraceCertificate

def toStandardTraceCalibration
    (h : PartialConsistencyPayloadSpecTraceCertificate) :
    PartialConsistencyStandardS21TraceCalibration :=
  PartialConsistencyStandardS21TraceCalibration.ofPayloadTruthAndTraceSoundness
    h.payload_spec.toPayloadTruth h.trace_soundness

def toProjectLocalTraceCertificate
    (h : PartialConsistencyPayloadSpecTraceCertificate) :
    SondowProjectLocalPartialConsistencyTraceCertificate where
  standard_calibration := h.toStandardTraceCalibration

def toAcceptedCodeTraceCertificate
    (h : PartialConsistencyPayloadSpecTraceCertificate) :
    PartialConsistencyAcceptedCodeTraceCertificate where
  accepted_truth := h.payload_spec.toAcceptedCodeTruthCertificate
  trace_soundness := h.trace_soundness

theorem toPayloadTruth
    (h : PartialConsistencyPayloadSpecTraceCertificate) :
    _root_.PartialConsistencyPayloadTruth :=
  h.payload_spec.toPayloadTruth

end PartialConsistencyPayloadSpecTraceCertificate

theorem partialConsistencyPayloadSpecTraceCertificate_nonempty_iff_payloadSpecAndTraceSoundness_nonempty :
    Nonempty PartialConsistencyPayloadSpecTraceCertificate ↔
      Nonempty PartialConsistencyPayloadSpecCertificate ∧
        Nonempty
          (_root_.S21VerifierTraceSoundness
            _root_.partialConsistencyCode) := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact
      ⟨⟨certificate.payload_spec⟩,
        ⟨certificate.trace_soundness⟩⟩
  · intro h
    rcases h with ⟨hspec, htrace⟩
    rcases hspec with ⟨spec⟩
    rcases htrace with ⟨trace⟩
    exact
      ⟨{ payload_spec := spec
         trace_soundness := trace }⟩

/-- Fully split checked-code presentation of the local S²₁ kernel data.  The
fields deliberately mirror the three kernel witnesses:
`sondow_trace`, `partial_consistency_trace`, and `graft_intro`. -/
structure SondowProjectLocalS21KernelCheckedCodeCertificate where
  sondow_trace :
    CheckedCodeS21TraceCalibration.{u}
      _root_.sondowCertificateValidCode
  partial_consistency_trace :
    CheckedCodeS21TraceCalibration.{u}
      _root_.partialConsistencyCode
  graft_intro : SondowProjectLocalGraftIntroCertificate

namespace SondowProjectLocalS21KernelCheckedCodeCertificate

def toTraceCalibrationSources
    (h : SondowProjectLocalS21KernelCheckedCodeCertificate.{u}) :
    SondowProjectLocalS21TraceCalibrationSources.{u} where
  sondow_calibration := h.sondow_trace
  partial_consistency_calibration := h.partial_consistency_trace
  graft_intro := h.graft_intro.graft_intro

def toKernel
    (h : SondowProjectLocalS21KernelCheckedCodeCertificate.{u}) :
    SondowProjectLocalS21Kernel :=
  h.toTraceCalibrationSources.toKernel

def ofTraceCalibrationSources
    (sources : SondowProjectLocalS21TraceCalibrationSources.{u}) :
    SondowProjectLocalS21KernelCheckedCodeCertificate.{u} where
  sondow_trace := sources.sondow_calibration
  partial_consistency_trace :=
    sources.partial_consistency_calibration
  graft_intro := ⟨sources.graft_intro⟩

end SondowProjectLocalS21KernelCheckedCodeCertificate

theorem sondowProjectLocalS21KernelCheckedCodeCertificate_nonempty_iff_traceCalibrationSources_nonempty :
    Nonempty SondowProjectLocalS21KernelCheckedCodeCertificate.{u} ↔
      Nonempty SondowProjectLocalS21TraceCalibrationSources.{u} := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toTraceCalibrationSources⟩
  · intro h
    rcases h with ⟨sources⟩
    exact
      ⟨SondowProjectLocalS21KernelCheckedCodeCertificate.ofTraceCalibrationSources
        sources⟩

theorem sondowProjectLocalS21Kernel_nonempty_ofCheckedCodeCertificate
    (h :
      Nonempty SondowProjectLocalS21KernelCheckedCodeCertificate.{u}) :
    Nonempty SondowProjectLocalS21Kernel := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toKernel⟩

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

/-- Primitive split certificate for the local S²₁ kernel.  Compared with the
checked-code split certificate, the partial-consistency trace is sourced from
the standard partial-consistency calibration, so its payload-truth witness has a
single named origin. -/
structure SondowProjectLocalS21PrimitiveKernelCertificate where
  sondow_trace : SondowProjectLocalSondowTraceCertificate.{u}
  partial_consistency_trace :
    SondowProjectLocalPartialConsistencyTraceCertificate
  graft_intro : SondowProjectLocalGraftIntroCertificate

namespace SondowProjectLocalS21PrimitiveKernelCertificate

def toPrimitiveKernelSources
    (h : SondowProjectLocalS21PrimitiveKernelCertificate.{u}) :
    SondowProjectLocalS21PrimitiveKernelSources.{u} where
  sondow_calibration := h.sondow_trace.checked_code
  partial_standard_calibration :=
    h.partial_consistency_trace.standard_calibration
  graft_intro := h.graft_intro.graft_intro

def toKernel
    (h : SondowProjectLocalS21PrimitiveKernelCertificate.{u}) :
    SondowProjectLocalS21Kernel :=
  h.toPrimitiveKernelSources.toKernel

def toCheckedCodeCertificate
    (h : SondowProjectLocalS21PrimitiveKernelCertificate.{u}) :
    SondowProjectLocalS21KernelCheckedCodeCertificate.{u} where
  sondow_trace := h.sondow_trace.checked_code
  partial_consistency_trace :=
    h.partial_consistency_trace.checkedCodeCalibration
  graft_intro := h.graft_intro

def ofPrimitiveKernelSources
    (sources : SondowProjectLocalS21PrimitiveKernelSources.{u}) :
    SondowProjectLocalS21PrimitiveKernelCertificate.{u} where
  sondow_trace := ⟨sources.sondow_calibration⟩
  partial_consistency_trace :=
    ⟨sources.partial_standard_calibration⟩
  graft_intro := ⟨sources.graft_intro⟩

end SondowProjectLocalS21PrimitiveKernelCertificate

theorem sondowProjectLocalS21PrimitiveKernelCertificate_nonempty_iff_sources_nonempty :
    Nonempty SondowProjectLocalS21PrimitiveKernelCertificate.{u} ↔
      Nonempty SondowProjectLocalS21PrimitiveKernelSources.{u} := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toPrimitiveKernelSources⟩
  · intro h
    rcases h with ⟨sources⟩
    exact
      ⟨SondowProjectLocalS21PrimitiveKernelCertificate.ofPrimitiveKernelSources
        sources⟩

theorem sondowProjectLocalS21Kernel_nonempty_ofPrimitiveKernelCertificate
    (h :
      Nonempty SondowProjectLocalS21PrimitiveKernelCertificate.{u}) :
    Nonempty SondowProjectLocalS21Kernel := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toKernel⟩

/-- Cost/absorption checked-code presentation of the local S²₁ kernel.  This is
the more concrete audit boundary for the three kernel witnesses:
`sondow_trace` comes from checked-code calibration, `partial_consistency_trace`
comes from a payload-spec trace certificate, and `graft_intro` is built from the
separate local conjunction-cost and predicate-absorption certificates. -/
structure SondowProjectLocalS21KernelCostAbsorptionCertificate where
  sondow_trace : SondowProjectLocalSondowTraceCertificate.{u}
  partial_consistency_trace :
    PartialConsistencyPayloadSpecTraceCertificate
  graft_cost : _root_.S21GraftConjunctionIntroductionCost
  graft_absorption :
    _root_.ReflectionGraftPredicateAbsorption graft_cost.C

namespace SondowProjectLocalS21KernelCostAbsorptionCertificate

def graftIntroCertificate
    (h : SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}) :
    SondowProjectLocalGraftIntroCertificate :=
  SondowProjectLocalGraftIntroCertificate.ofCostAndAbsorption
    h.graft_cost h.graft_absorption

def toPrimitiveKernelCertificate
    (h : SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}) :
    SondowProjectLocalS21PrimitiveKernelCertificate.{u} where
  sondow_trace := h.sondow_trace
  partial_consistency_trace :=
    h.partial_consistency_trace.toProjectLocalTraceCertificate
  graft_intro := h.graftIntroCertificate

def toCheckedCodeCertificate
    (h : SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}) :
    SondowProjectLocalS21KernelCheckedCodeCertificate.{u} :=
  h.toPrimitiveKernelCertificate.toCheckedCodeCertificate

def toKernel
    (h : SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}) :
    SondowProjectLocalS21Kernel :=
  h.toPrimitiveKernelCertificate.toKernel

theorem payloadTruth
    (h : SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}) :
    _root_.PartialConsistencyPayloadTruth :=
  h.partial_consistency_trace.toPayloadTruth

def payloadSpecCertificate
    (h : SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}) :
    PartialConsistencyPayloadSpecCertificate :=
  h.partial_consistency_trace.payload_spec

def acceptedCodeTruthCertificate
    (h : SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}) :
    PartialConsistencyAcceptedCodeTruthCertificate :=
  h.payloadSpecCertificate.toAcceptedCodeTruthCertificate

def payloadSemanticsCertificate
    (h : SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}) :
    PartialConsistencyPayloadSemanticsCertificate :=
  h.payloadSpecCertificate.toPayloadSemanticsCertificate

def finiteConsistencyReadingCertificate
    (h : SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}) :
    PartialConsistencyFiniteConsistencyReadingCertificate :=
  h.payloadSpecCertificate.toFiniteConsistencyReadingCertificate

end SondowProjectLocalS21KernelCostAbsorptionCertificate

theorem sondowProjectLocalS21Kernel_nonempty_ofCostAbsorptionCertificate
    (h :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}) :
    Nonempty SondowProjectLocalS21Kernel := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toKernel⟩

theorem partialConsistencyPayloadSpecCertificate_nonempty_ofCostAbsorptionKernelCertificate
    (h :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}) :
    Nonempty PartialConsistencyPayloadSpecCertificate := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.payloadSpecCertificate⟩

theorem partialConsistencyAcceptedCodeTruthCertificate_nonempty_ofCostAbsorptionKernelCertificate
    (h :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}) :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.acceptedCodeTruthCertificate⟩

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

/-- The bounded-arithmetic sidecar target whose code is the reflection-graft
family.  It is named here so the main/sidecar embedding certificate has a single
target, instead of repeating the component conjunction inline. -/
abbrev sondowReflectionGraftSidecarTarget :
    ℕ → BoundedArithmeticLab.BAFormula :=
  BoundedArithmeticLab.sondowProjectComponentFormulas.target

/-- The sidecar formula-code map used with the reflection-graft target. -/
abbrev sondowReflectionGraftSidecarCode :
    BoundedArithmeticLab.BAFormula →
      BoundedArithmeticLab.FormulaCode :=
  BoundedArithmeticLab.sondowProjectComponentCode

@[simp] theorem sondowReflectionGraftSidecarTarget_code_eq
    (n : ℕ) :
    sondowReflectionGraftSidecarCode
        (sondowReflectionGraftSidecarTarget n) =
      BoundedArithmeticLab.sondowReflectionGraftCode n := by
  exact BoundedArithmeticLab.sondowProjectComponentCode_target n

/-- The checked family-code equality for the bounded-arithmetic sidecar target.
This closes the definitional part of the sidecar/root-recognition obligation:
the remaining proof-length issue is only the main repository's abstract
`proof_length` convention on the corresponding root family. -/
structure SondowReflectionGraftSidecarFamilyCodeEquality : Prop where
  target_code_eq :
    ∀ n : ℕ,
      sondowReflectionGraftSidecarCode
          (sondowReflectionGraftSidecarTarget n) =
        BoundedArithmeticLab.sondowReflectionGraftCode n

theorem sondowReflectionGraftSidecarFamilyCodeEquality :
    SondowReflectionGraftSidecarFamilyCodeEquality where
  target_code_eq := sondowReflectionGraftSidecarTarget_code_eq

/-- Per-index S²₁ sidecar proof object for the reflection-graft target. -/
structure SondowReflectionGraftSidecarS21SemanticProofAt (n : ℕ) where
  proof_object :
    BoundedArithmeticLab.BAProofObject
      BoundedArithmeticLab.BussS21Axiom
  conclusion_eq :
    proof_object.conclusion = sondowReflectionGraftSidecarTarget n

namespace SondowReflectionGraftSidecarS21SemanticProofAt

theorem toExists
    {n : ℕ}
    (h : SondowReflectionGraftSidecarS21SemanticProofAt n) :
    ∃ p :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      p.conclusion = sondowReflectionGraftSidecarTarget n :=
  ⟨h.proof_object, h.conclusion_eq⟩

end SondowReflectionGraftSidecarS21SemanticProofAt

/-- Sidecar S²₁ semantic nonemptiness, split per index. -/
structure SondowReflectionGraftSidecarS21SemanticNonempty where
  proof_at :
    ∀ n : ℕ, SondowReflectionGraftSidecarS21SemanticProofAt n

namespace SondowReflectionGraftSidecarS21SemanticNonempty

theorem semantic_nonempty
    (h : SondowReflectionGraftSidecarS21SemanticNonempty)
    (n : ℕ) :
    ∃ p :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      p.conclusion = sondowReflectionGraftSidecarTarget n :=
  (h.proof_at n).toExists

end SondowReflectionGraftSidecarS21SemanticNonempty

/-- Component-proof sufficient certificate for one sidecar target index.  It
records the five concrete S²₁ component proof objects and their conclusions;
the right-nested conjunction proof is then built by the bounded-arithmetic
sidecar's `SondowComponentCertificate.buildProof`. -/
structure SondowReflectionGraftSidecarComponentProofAt (n : ℕ) where
  component_certificate :
    BoundedArithmeticLab.SondowComponentCertificate
  product_conclusion :
    component_certificate.productProof.conclusion =
      BoundedArithmeticLab.sondowProjectComponentFormulas.product n
  log_conclusion :
    component_certificate.logProof.conclusion =
      BoundedArithmeticLab.sondowProjectComponentFormulas.logRelation n
  decomposition_conclusion :
    component_certificate.decompositionProof.conclusion =
      BoundedArithmeticLab.sondowProjectComponentFormulas.decomposition n
  threePow_conclusion :
    component_certificate.threePowProof.conclusion =
      BoundedArithmeticLab.sondowProjectComponentFormulas.threePow n
  payload_conclusion :
    component_certificate.payloadProof.conclusion =
      BoundedArithmeticLab.sondowProjectComponentFormulas.payload n

namespace SondowReflectionGraftSidecarComponentProofAt

def toS21SemanticProofAt
    {n : ℕ}
    (h : SondowReflectionGraftSidecarComponentProofAt n) :
    SondowReflectionGraftSidecarS21SemanticProofAt n where
  proof_object := h.component_certificate.buildProof
  conclusion_eq := by
    let bound : ℕ → ℝ :=
      fun _ => (h.component_certificate.certSize : ℝ)
    have hvalid :
        BoundedArithmeticLab.SondowComponentCertificate.Valid
          BoundedArithmeticLab.sondowProjectComponentFormulas
          bound n h.component_certificate :=
      { product_conclusion := h.product_conclusion
        log_conclusion := h.log_conclusion
        decomposition_conclusion := h.decomposition_conclusion
        threePow_conclusion := h.threePow_conclusion
        payload_conclusion := h.payload_conclusion
        size_le_bound := le_rfl }
    exact
      BoundedArithmeticLab.SondowComponentCertificate.buildProof_conclusion
        hvalid

end SondowReflectionGraftSidecarComponentProofAt

/-- Component-proof sufficient certificate for sidecar S²₁ semantic
nonemptiness at every index. -/
structure SondowReflectionGraftSidecarComponentProofCertificate where
  proof_at :
    ∀ n : ℕ, SondowReflectionGraftSidecarComponentProofAt n

namespace SondowReflectionGraftSidecarComponentProofCertificate

def toSidecarS21SemanticNonempty
    (h : SondowReflectionGraftSidecarComponentProofCertificate) :
    SondowReflectionGraftSidecarS21SemanticNonempty where
  proof_at := fun n => (h.proof_at n).toS21SemanticProofAt

end SondowReflectionGraftSidecarComponentProofCertificate

/-- Eventual sidecar semantic nonemptiness.  This is intentionally not strong
enough for `SondowReflectionGraftConcreteSemanticLengthCalibration`, whose PA
embedding needs all indices; it records the weaker certificate shape separately
so eventual compiler exports are not mistaken for a global calibration. -/
structure SondowReflectionGraftSidecarS21SemanticNonemptyEventually where
  threshold : ℕ
  proof_at :
    ∀ n : ℕ, threshold ≤ n →
      SondowReflectionGraftSidecarS21SemanticProofAt n

namespace SondowReflectionGraftSidecarS21SemanticNonemptyEventually

theorem semantic_nonempty_after
    (h : SondowReflectionGraftSidecarS21SemanticNonemptyEventually)
    {n : ℕ} (hn : h.threshold ≤ n) :
    ∃ p :
      BoundedArithmeticLab.BAProofObject
        BoundedArithmeticLab.BussS21Axiom,
      p.conclusion = sondowReflectionGraftSidecarTarget n :=
  (h.proof_at n hn).toExists

end SondowReflectionGraftSidecarS21SemanticNonemptyEventually

/-- Checked proof-object validity for one reflection-graft sidecar index.  This
uses the bounded-arithmetic sidecar's existing `ProofObjectSystemValid`
certificate, which includes the five component conclusions and their size
bounds. -/
structure SondowReflectionGraftSidecarProofObjectSystemValidAt
    (bounds : BoundedArithmeticLab.SondowComponentBounds) (n : ℕ) where
  component_certificate :
    BoundedArithmeticLab.SondowComponentCertificate
  valid :
    BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
      BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
      component_certificate

namespace SondowReflectionGraftSidecarProofObjectSystemValidAt

def toComponentProofAt
    {bounds : BoundedArithmeticLab.SondowComponentBounds} {n : ℕ}
    (h : SondowReflectionGraftSidecarProofObjectSystemValidAt bounds n) :
    SondowReflectionGraftSidecarComponentProofAt n where
  component_certificate := h.component_certificate
  product_conclusion := h.valid.product_conclusion
  log_conclusion := h.valid.log_conclusion
  decomposition_conclusion := h.valid.decomposition_conclusion
  threePow_conclusion := h.valid.threePow_conclusion
  payload_conclusion := h.valid.payload_conclusion

def toS21SemanticProofAt
    {bounds : BoundedArithmeticLab.SondowComponentBounds} {n : ℕ}
    (h : SondowReflectionGraftSidecarProofObjectSystemValidAt bounds n) :
    SondowReflectionGraftSidecarS21SemanticProofAt n :=
  h.toComponentProofAt.toS21SemanticProofAt

end SondowReflectionGraftSidecarProofObjectSystemValidAt

/-- Narrow checker-exactness certificate for one sidecar index.  Instead of
postulating the grouped `ProofObjectSystemValid` record directly, this uses the
sidecar's proof-object component certificate systems and their existing checker
validity predicates. -/
structure SondowReflectionGraftSidecarProofObjectCheckerExactAt
    (bounds : BoundedArithmeticLab.SondowComponentBounds) (n : ℕ) where
  system_certificate :
    BoundedArithmeticLab.SondowComponentSystemCertificateAt
      (BoundedArithmeticLab.sondowProjectProofObjectCertificateSystems bounds) n

namespace SondowReflectionGraftSidecarProofObjectCheckerExactAt

def componentCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds} {n : ℕ}
    (h : SondowReflectionGraftSidecarProofObjectCheckerExactAt bounds n) :
    BoundedArithmeticLab.SondowComponentCertificate where
  productProof := h.system_certificate.productProof
  logProof := h.system_certificate.logProof
  decompositionProof := h.system_certificate.decompositionProof
  threePowProof := h.system_certificate.threePowProof
  payloadProof := h.system_certificate.payloadProof

theorem componentCertificate_valid
    {bounds : BoundedArithmeticLab.SondowComponentBounds} {n : ℕ}
    (h : SondowReflectionGraftSidecarProofObjectCheckerExactAt bounds n) :
    BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
      BoundedArithmeticLab.sondowProjectComponentFormulas bounds n
      h.componentCertificate := by
  let systems :=
    BoundedArithmeticLab.sondowProjectProofObjectCertificateSystems bounds
  exact
    { product_conclusion := by
        simpa [componentCertificate] using
          h.system_certificate.productProof_conclusion
      log_conclusion := by
        simpa [componentCertificate] using
          h.system_certificate.logProof_conclusion
      decomposition_conclusion := by
        simpa [componentCertificate] using
          h.system_certificate.decompositionProof_conclusion
      threePow_conclusion := by
        simpa [componentCertificate] using
          h.system_certificate.threePowProof_conclusion
      payload_conclusion := by
        simpa [componentCertificate] using
          h.system_certificate.payloadProof_conclusion
      product_size_plus_two_le := by
        simpa [systems, componentCertificate,
          BoundedArithmeticLab.SondowComponentSystemCertificateAt.productProof] using
          systems.productSystem.proof_size_plus_two_le_bound
            h.system_certificate.productValid
      log_size_plus_two_le := by
        simpa [systems, componentCertificate,
          BoundedArithmeticLab.SondowComponentSystemCertificateAt.logProof] using
          systems.logSystem.proof_size_plus_two_le_bound
            h.system_certificate.logValid
      decomposition_size_plus_two_le := by
        simpa [systems, componentCertificate,
          BoundedArithmeticLab.SondowComponentSystemCertificateAt.decompositionProof] using
          systems.decompositionSystem.proof_size_plus_two_le_bound
            h.system_certificate.decompositionValid
      threePow_size_plus_two_le := by
        simpa [systems, componentCertificate,
          BoundedArithmeticLab.SondowComponentSystemCertificateAt.threePowProof] using
          systems.threePowSystem.proof_size_plus_two_le_bound
            h.system_certificate.threePowValid
      payload_size_plus_two_le := by
        simpa [systems, componentCertificate,
          BoundedArithmeticLab.SondowComponentSystemCertificateAt.payloadProof] using
          systems.payloadSystem.proof_size_plus_two_le_bound
            h.system_certificate.payloadValid }

def toProofObjectSystemValidAt
    {bounds : BoundedArithmeticLab.SondowComponentBounds} {n : ℕ}
    (h : SondowReflectionGraftSidecarProofObjectCheckerExactAt bounds n) :
    SondowReflectionGraftSidecarProofObjectSystemValidAt bounds n where
  component_certificate := h.componentCertificate
  valid := h.componentCertificate_valid

end SondowReflectionGraftSidecarProofObjectCheckerExactAt

def SondowReflectionGraftSidecarProofObjectSystemValidAt.toCheckerExactAt
    {bounds : BoundedArithmeticLab.SondowComponentBounds} {n : ℕ}
    (h : SondowReflectionGraftSidecarProofObjectSystemValidAt bounds n) :
    SondowReflectionGraftSidecarProofObjectCheckerExactAt bounds n where
  system_certificate := by
    simpa [BoundedArithmeticLab.sondowProjectProofObjectCertificateSystems] using
      h.valid.toSystemCertificateAt

/-- All-index checked proof-object certificate for the sidecar S²₁ semantic
nonemptiness obligation. -/
structure SondowReflectionGraftSidecarProofObjectSystemValidCertificate
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  proof_at :
    ∀ n : ℕ,
      SondowReflectionGraftSidecarProofObjectSystemValidAt bounds n

namespace SondowReflectionGraftSidecarProofObjectSystemValidCertificate

def toComponentProofCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarProofObjectSystemValidCertificate
        bounds) :
    SondowReflectionGraftSidecarComponentProofCertificate where
  proof_at := fun n => (h.proof_at n).toComponentProofAt

def toSidecarS21SemanticNonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarProofObjectSystemValidCertificate
        bounds) :
    SondowReflectionGraftSidecarS21SemanticNonempty :=
  h.toComponentProofCertificate.toSidecarS21SemanticNonempty

end SondowReflectionGraftSidecarProofObjectSystemValidCertificate

/-- All-index checker-exactness certificate for the sidecar proof-object route.
It is narrower than the existing all-index `ProofObjectSystemValid` witness:
each index only supplies a certificate accepted by the fixed proof-object
component checkers. -/
structure SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  exact_at :
    ∀ n : ℕ,
      SondowReflectionGraftSidecarProofObjectCheckerExactAt bounds n

namespace SondowReflectionGraftSidecarProofObjectCheckerExactCertificate

def toProofObjectSystemValidCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
        bounds) :
    SondowReflectionGraftSidecarProofObjectSystemValidCertificate bounds where
  proof_at := fun n => (h.exact_at n).toProofObjectSystemValidAt

def toSidecarS21SemanticNonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
        bounds) :
    SondowReflectionGraftSidecarS21SemanticNonempty :=
  h.toProofObjectSystemValidCertificate.toSidecarS21SemanticNonempty

end SondowReflectionGraftSidecarProofObjectCheckerExactCertificate

def SondowReflectionGraftSidecarProofObjectSystemValidCertificate.toCheckerExactCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarProofObjectSystemValidCertificate
        bounds) :
    SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
      bounds where
  exact_at := fun n => (h.proof_at n).toCheckerExactAt

theorem sondowReflectionGraftSidecarProofObjectCheckerExactCertificate_nonempty_iff_systemValidCertificate_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds) ↔
      Nonempty
        (SondowReflectionGraftSidecarProofObjectSystemValidCertificate
          bounds) := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toProofObjectSystemValidCertificate⟩
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toCheckerExactCertificate⟩

/-- Primitive all-index existence form for the reflection-graft sidecar proof
objects.  This is the natural target for a concrete exporter: for every index it
only has to provide a component certificate and prove the fixed proof-object
systems accept it. -/
structure SondowReflectionGraftSidecarProofObjectExistsCertificate
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  proof_exists :
    ∀ n : ℕ,
      ∃ cert : BoundedArithmeticLab.SondowComponentCertificate,
        BoundedArithmeticLab.SondowComponentCertificate.ProofObjectSystemValid
          BoundedArithmeticLab.sondowProjectComponentFormulas bounds n cert

namespace SondowReflectionGraftSidecarProofObjectExistsCertificate

noncomputable def proofAt
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarProofObjectExistsCertificate
        bounds)
    (n : ℕ) :
    SondowReflectionGraftSidecarProofObjectSystemValidAt bounds n where
  component_certificate := Classical.choose (h.proof_exists n)
  valid := Classical.choose_spec (h.proof_exists n)

noncomputable def toSystemValidCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarProofObjectExistsCertificate
        bounds) :
    SondowReflectionGraftSidecarProofObjectSystemValidCertificate
      bounds where
  proof_at := h.proofAt

noncomputable def toCheckerExactCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarProofObjectExistsCertificate
        bounds) :
    SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
      bounds :=
  h.toSystemValidCertificate.toCheckerExactCertificate

end SondowReflectionGraftSidecarProofObjectExistsCertificate

def SondowReflectionGraftSidecarProofObjectSystemValidCertificate.toExistsCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarProofObjectSystemValidCertificate
        bounds) :
    SondowReflectionGraftSidecarProofObjectExistsCertificate bounds where
  proof_exists := fun n =>
    ⟨(h.proof_at n).component_certificate, (h.proof_at n).valid⟩

theorem sondowReflectionGraftSidecarProofObjectExistsCertificate_nonempty_iff_systemValidCertificate_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty
        (SondowReflectionGraftSidecarProofObjectExistsCertificate
          bounds) ↔
      Nonempty
        (SondowReflectionGraftSidecarProofObjectSystemValidCertificate
          bounds) := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toSystemValidCertificate⟩
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toExistsCertificate⟩

theorem sondowReflectionGraftSidecarProofObjectCheckerExactCertificate_nonempty_iff_existsCertificate_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds) ↔
      Nonempty
        (SondowReflectionGraftSidecarProofObjectExistsCertificate
          bounds) := by
  calc
    Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds) ↔
      Nonempty
        (SondowReflectionGraftSidecarProofObjectSystemValidCertificate
          bounds) :=
        sondowReflectionGraftSidecarProofObjectCheckerExactCertificate_nonempty_iff_systemValidCertificate_nonempty
    _ ↔
      Nonempty
        (SondowReflectionGraftSidecarProofObjectExistsCertificate
          bounds) :=
        (sondowReflectionGraftSidecarProofObjectExistsCertificate_nonempty_iff_systemValidCertificate_nonempty).symm

/-- Componentwise primitive existence form for the reflection-graft sidecar.
This is the audit-facing decomposition of the bundled proof-object witness:
each of the five fixed component formulas has its own Buss S²₁ proof object and
size bound. -/
structure SondowReflectionGraftSidecarComponentProofObjectExistsCertificate
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  product_exists :
    ∀ n : ℕ,
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.product n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n
  log_exists :
    ∀ n : ℕ,
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.logRelation n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n
  decomposition_exists :
    ∀ n : ℕ,
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.decomposition n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.decomposition n
  threePow_exists :
    ∀ n : ℕ,
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.threePow n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.threePow n
  payload_exists :
    ∀ n : ℕ,
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.payload n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.payload n

namespace SondowReflectionGraftSidecarComponentProofObjectExistsCertificate

noncomputable def toProofObjectExistsCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarComponentProofObjectExistsCertificate
        bounds) :
    SondowReflectionGraftSidecarProofObjectExistsCertificate bounds where
  proof_exists := by
    intro n
    rcases h.product_exists n with
      ⟨productProof, hproduct_conclusion, hproduct_size⟩
    rcases h.log_exists n with
      ⟨logProof, hlog_conclusion, hlog_size⟩
    rcases h.decomposition_exists n with
      ⟨decompositionProof, hdecomposition_conclusion,
        hdecomposition_size⟩
    rcases h.threePow_exists n with
      ⟨threePowProof, hthreePow_conclusion, hthreePow_size⟩
    rcases h.payload_exists n with
      ⟨payloadProof, hpayload_conclusion, hpayload_size⟩
    exact
      ⟨{ productProof := productProof
         logProof := logProof
         decompositionProof := decompositionProof
         threePowProof := threePowProof
         payloadProof := payloadProof },
       { product_conclusion := hproduct_conclusion
         log_conclusion := hlog_conclusion
         decomposition_conclusion := hdecomposition_conclusion
         threePow_conclusion := hthreePow_conclusion
         payload_conclusion := hpayload_conclusion
         product_size_plus_two_le := hproduct_size
         log_size_plus_two_le := hlog_size
         decomposition_size_plus_two_le := hdecomposition_size
         threePow_size_plus_two_le := hthreePow_size
         payload_size_plus_two_le := hpayload_size }⟩

end SondowReflectionGraftSidecarComponentProofObjectExistsCertificate

def SondowReflectionGraftSidecarProofObjectExistsCertificate.toComponentProofObjectExistsCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarProofObjectExistsCertificate
        bounds) :
    SondowReflectionGraftSidecarComponentProofObjectExistsCertificate
      bounds where
  product_exists := by
    intro n
    rcases h.proof_exists n with ⟨cert, hvalid⟩
    exact
      ⟨cert.productProof,
        hvalid.product_conclusion,
        hvalid.product_size_plus_two_le⟩
  log_exists := by
    intro n
    rcases h.proof_exists n with ⟨cert, hvalid⟩
    exact
      ⟨cert.logProof,
        hvalid.log_conclusion,
        hvalid.log_size_plus_two_le⟩
  decomposition_exists := by
    intro n
    rcases h.proof_exists n with ⟨cert, hvalid⟩
    exact
      ⟨cert.decompositionProof,
        hvalid.decomposition_conclusion,
        hvalid.decomposition_size_plus_two_le⟩
  threePow_exists := by
    intro n
    rcases h.proof_exists n with ⟨cert, hvalid⟩
    exact
      ⟨cert.threePowProof,
        hvalid.threePow_conclusion,
        hvalid.threePow_size_plus_two_le⟩
  payload_exists := by
    intro n
    rcases h.proof_exists n with ⟨cert, hvalid⟩
    exact
      ⟨cert.payloadProof,
        hvalid.payload_conclusion,
        hvalid.payload_size_plus_two_le⟩

theorem sondowReflectionGraftSidecarComponentProofObjectExistsCertificate_nonempty_iff_proofObjectExistsCertificate_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty
        (SondowReflectionGraftSidecarComponentProofObjectExistsCertificate
          bounds) ↔
      Nonempty
        (SondowReflectionGraftSidecarProofObjectExistsCertificate
          bounds) := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toProofObjectExistsCertificate⟩
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toComponentProofObjectExistsCertificate⟩

theorem sondowReflectionGraftSidecarCheckerExactCertificate_nonempty_iff_componentProofObjectExistsCertificate_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds) ↔
      Nonempty
        (SondowReflectionGraftSidecarComponentProofObjectExistsCertificate
          bounds) := by
  calc
    Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds) ↔
      Nonempty
        (SondowReflectionGraftSidecarProofObjectExistsCertificate
          bounds) :=
        sondowReflectionGraftSidecarProofObjectCheckerExactCertificate_nonempty_iff_existsCertificate_nonempty
    _ ↔
      Nonempty
        (SondowReflectionGraftSidecarComponentProofObjectExistsCertificate
          bounds) :=
        (sondowReflectionGraftSidecarComponentProofObjectExistsCertificate_nonempty_iff_proofObjectExistsCertificate_nonempty).symm

/-- Eventual componentwise existence form for the reflection-graft sidecar.
This is the exact shape supplied by the Sondow upper-bound route: after a
threshold, each of the five fixed component formulas has an accepted Buss S²₁
proof object with the required size bound.  It deliberately does not imply the
all-index checker-exactness certificate. -/
structure SondowReflectionGraftSidecarComponentProofObjectExistsEventually
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  threshold : ℕ
  product_exists :
    ∀ n : ℕ, threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.product n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.product n
  log_exists :
    ∀ n : ℕ, threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.logRelation n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.logRelation n
  decomposition_exists :
    ∀ n : ℕ, threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.decomposition n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.decomposition n
  threePow_exists :
    ∀ n : ℕ, threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.threePow n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.threePow n
  payload_exists :
    ∀ n : ℕ, threshold ≤ n →
      ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
            BoundedArithmeticLab.sondowProjectComponentFormulas.payload n ∧
          (((proof.size + 2 : ℕ) : ℝ)) ≤ bounds.payload n

/-- Eventual checked proof-object certificate for the sidecar.  It is useful for
compiler exports that only start after a threshold, but it deliberately does not
coerce to the all-index semantic nonemptiness required by the PA embedding. -/
structure SondowReflectionGraftSidecarProofObjectSystemValidEventually
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  threshold : ℕ
  proof_at :
    ∀ n : ℕ, threshold ≤ n →
      SondowReflectionGraftSidecarProofObjectSystemValidAt bounds n

/-- Data-level checked Sondow certificate at one index.  This is stronger than
`mainSondowAcceptedAt n`: it keeps the rational parameter and the checked-code
proof as fields, so downstream compilers do not have to recover them from an
existential proposition. -/
structure MainSondowFullCertificateCheckedAt (n : ℕ) where
  q : ℚ
  checked : mainSondowFullCertificateChecks q n

namespace MainSondowFullCertificateCheckedAt

def toAcceptedAt {n : ℕ}
    (h : MainSondowFullCertificateCheckedAt n) :
    mainSondowAcceptedAt n :=
  ⟨h.q, h.checked⟩

end MainSondowFullCertificateCheckedAt

/-- Data-level eventual accepted-tail certificate for the main Sondow
certificate family.  This is the computable replacement for merely knowing
`∃ N, ∀ n ≥ N, mainSondowAcceptedAt n`. -/
structure MainSondowFullCertificateCheckedTail where
  threshold : ℕ
  checked_at :
    ∀ n : ℕ, threshold ≤ n →
      MainSondowFullCertificateCheckedAt n

namespace MainSondowFullCertificateCheckedTail

theorem accepted_eventually
    (h : MainSondowFullCertificateCheckedTail) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → mainSondowAcceptedAt n :=
  ⟨h.threshold, fun n hn => (h.checked_at n hn).toAcceptedAt⟩

theorem four_mul_nine_sixteenth_pow_lt_one_of_three_le
    {n : ℕ} (hn : 3 ≤ n) :
    4 * ((9 : ℝ) / 16) ^ n < 1 := by
  have hpow :
      ((9 : ℝ) / 16) ^ n ≤ ((9 : ℝ) / 16) ^ 3 := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hmul :
      4 * ((9 : ℝ) / 16) ^ n ≤
        4 * ((9 : ℝ) / 16) ^ 3 := by
    exact mul_le_mul_of_nonneg_left hpow (by norm_num)
  have htarget : 4 * ((9 : ℝ) / 16) ^ 3 < 1 := by
    norm_num
  exact lt_of_le_of_lt hmul htarget

theorem tail_bound_certificate_accepted_of_three_le
    {n : ℕ} (hn : 3 ≤ n) :
    _root_.tail_bound_certificate_accepted n := by
  have hn_one : 1 ≤ n :=
    le_trans (by norm_num) hn
  exact lt_of_le_of_lt
    (_root_.sondow_product_le_four_mul_nine_sixteenth_pow
      _root_.SondowForwardInputs.of_reproof.lcm_bound n hn_one)
    (four_mul_nine_sixteenth_pow_lt_one_of_three_le hn)

def ofReproofRationalParameter
    (q : ℚ) (hq : (q : ℝ) = _root_.euler_mascheroni) :
    MainSondowFullCertificateCheckedTail where
  threshold := max 3 q.den
  checked_at := by
    intro n hn
    have hn_three : 3 ≤ n :=
      le_trans (Nat.le_max_left 3 q.den) hn
    have hn_den : q.den ≤ n :=
      le_trans (Nat.le_max_right 3 q.den) hn
    have hn_one : 1 ≤ n :=
      le_trans (by norm_num) hn_three
    exact
      { q := q
        checked :=
          ⟨hq,
            ⟨tail_bound_certificate_accepted_of_three_le hn_three,
              _root_.denominator_certificate_accepted_of_den_le q
                (by omega)⟩,
            _root_.SondowForwardInputs.of_reproof.product_log n hn_one,
            _root_.SondowForwardInputs.of_reproof.decomposition n hn_one⟩ }

theorem ofReproofRationalParameter_threshold
    (q : ℚ) (hq : (q : ℝ) = _root_.euler_mascheroni) :
    (ofReproofRationalParameter q hq).threshold = max 3 q.den :=
  rfl

noncomputable def ofAcceptedEventually
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → mainSondowAcceptedAt n) :
    MainSondowFullCertificateCheckedTail where
  threshold := Classical.choose h
  checked_at := by
    intro n hn
    let accepted : mainSondowAcceptedAt n :=
      (Classical.choose_spec h) n hn
    exact
      { q := Classical.choose accepted
        checked := Classical.choose_spec accepted }

end MainSondowFullCertificateCheckedTail

/-- Data-level rationality witness: the rational parameter is explicit data,
while the equality to Euler's constant remains a proof field.  This is the
computable-frontier replacement for eliminating `is_rational` directly into
data. -/
structure MainSondowRationalParameter : Type where
  q : ℚ
  gamma_eq : (q : ℝ) = _root_.euler_mascheroni

namespace MainSondowRationalParameter

def checkedTail
    (h : MainSondowRationalParameter) :
    MainSondowFullCertificateCheckedTail :=
  MainSondowFullCertificateCheckedTail.ofReproofRationalParameter
    h.q h.gamma_eq

theorem checkedTail_threshold
    (h : MainSondowRationalParameter) :
    h.checkedTail.threshold = max 3 h.q.den :=
  rfl

end MainSondowRationalParameter

/-- Rationality-to-checked-tail provider.  This is the data-level version of the
accepted-tail theorem needed for a computable upper-bound route. -/
structure MainSondowExplicitCheckedTailProvider : Type where
  checkedTailOfRationality :
    _root_.is_rational _root_.euler_mascheroni →
      MainSondowFullCertificateCheckedTail

namespace MainSondowExplicitCheckedTailProvider

theorem accepted_eventually_under_rationality
    (h : MainSondowExplicitCheckedTailProvider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → mainSondowAcceptedAt n :=
  (h.checkedTailOfRationality hrat).accepted_eventually

def ofRationalParameter
    (h : MainSondowRationalParameter) :
    MainSondowExplicitCheckedTailProvider where
  checkedTailOfRationality := fun _hrat => h.checkedTail

theorem ofRationalParameter_threshold
    (h : MainSondowRationalParameter)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((ofRationalParameter h).checkedTailOfRationality hrat).threshold =
      max 3 h.q.den :=
  rfl

/-- Legacy compatibility provider obtained from the existing reproved Sondow
accepted-tail theorem by classical choice.  This proves the explicit checked
tail is not a weaker logical target.  It is deliberately not the final
computational source for a numerical large `N`, because the selected threshold
and parameters are hidden behind `Classical.choose`. -/
noncomputable def ofReproofChoice :
    MainSondowExplicitCheckedTailProvider where
  checkedTailOfRationality := fun hrat =>
    MainSondowFullCertificateCheckedTail.ofAcceptedEventually
      (_root_.accepted_sondow_certificate_eventual_of_rationality_reproof hrat)

theorem ofReproofChoice_accepted_eventually_under_rationality
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → mainSondowAcceptedAt n :=
  ofReproofChoice.accepted_eventually_under_rationality hrat

end MainSondowExplicitCheckedTailProvider

namespace SondowReflectionGraftSidecarProofObjectSystemValidEventually

def ofMainEventualCompilerAndCheckedTail
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (tail : MainSondowFullCertificateCheckedTail) :
    SondowReflectionGraftSidecarProofObjectSystemValidEventually
      bounds where
  threshold := max compiler.threshold tail.threshold
  proof_at := by
    intro n hn
    have hcompiler : compiler.threshold ≤ n :=
      le_trans (Nat.le_max_left compiler.threshold tail.threshold) hn
    have htail : tail.threshold ≤ n :=
      le_trans (Nat.le_max_right compiler.threshold tail.threshold) hn
    let checked := tail.checked_at n htail
    exact
      { component_certificate :=
          { productProof :=
              compiler.productProof n checked.q hcompiler checked.checked
            logProof :=
              compiler.logProof n checked.q hcompiler checked.checked
            decompositionProof :=
              compiler.decompositionProof n checked.q hcompiler checked.checked
            threePowProof :=
              compiler.threePowProof n checked.q hcompiler checked.checked
            payloadProof :=
              compiler.payloadProof n checked.q hcompiler checked.checked }
        valid :=
          { product_conclusion :=
              compiler.product_conclusion
                n checked.q hcompiler checked.checked
            log_conclusion :=
              compiler.log_conclusion
                n checked.q hcompiler checked.checked
            decomposition_conclusion :=
              compiler.decomposition_conclusion
                n checked.q hcompiler checked.checked
            threePow_conclusion :=
              compiler.threePow_conclusion
                n checked.q hcompiler checked.checked
            payload_conclusion :=
              compiler.payload_conclusion
                n checked.q hcompiler checked.checked
            product_size_plus_two_le :=
              compiler.product_size_plus_two_le
                n checked.q hcompiler checked.checked
            log_size_plus_two_le :=
              compiler.log_size_plus_two_le
                n checked.q hcompiler checked.checked
            decomposition_size_plus_two_le :=
              compiler.decomposition_size_plus_two_le
                n checked.q hcompiler checked.checked
            threePow_size_plus_two_le :=
              compiler.threePow_size_plus_two_le
                n checked.q hcompiler checked.checked
            payload_size_plus_two_le :=
              compiler.payload_size_plus_two_le
                n checked.q hcompiler checked.checked } }

theorem ofMainEventualCompilerAndCheckedTail_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (tail : MainSondowFullCertificateCheckedTail) :
    (ofMainEventualCompilerAndCheckedTail compiler tail).threshold =
      max compiler.threshold tail.threshold :=
  rfl

def ofMainEventualCompilerAndCheckedTailProvider
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (provider : MainSondowExplicitCheckedTailProvider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    SondowReflectionGraftSidecarProofObjectSystemValidEventually
      bounds :=
  ofMainEventualCompilerAndCheckedTail
    compiler (provider.checkedTailOfRationality hrat)

def ofMainEventualCompilerAndRationalParameter
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (rat : MainSondowRationalParameter) :
    SondowReflectionGraftSidecarProofObjectSystemValidEventually
      bounds :=
  ofMainEventualCompilerAndCheckedTail compiler rat.checkedTail

theorem ofMainEventualCompilerAndRationalParameter_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (rat : MainSondowRationalParameter) :
    (ofMainEventualCompilerAndRationalParameter compiler rat).threshold =
      max compiler.threshold (max 3 rat.q.den) :=
  rfl

noncomputable def toSemanticNonemptyEventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds) :
    SondowReflectionGraftSidecarS21SemanticNonemptyEventually where
  threshold := h.threshold
  proof_at := fun n hn => (h.proof_at n hn).toS21SemanticProofAt

end SondowReflectionGraftSidecarProofObjectSystemValidEventually

namespace SondowReflectionGraftSidecarComponentProofObjectExistsEventually

noncomputable def toSystemValidEventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds) :
    SondowReflectionGraftSidecarProofObjectSystemValidEventually
      bounds where
  threshold := h.threshold
  proof_at := by
    intro n hn
    let hproduct := h.product_exists n hn
    let productProof := Classical.choose hproduct
    have hproduct_valid := Classical.choose_spec hproduct
    let hlog := h.log_exists n hn
    let logProof := Classical.choose hlog
    have hlog_valid := Classical.choose_spec hlog
    let hdecomposition := h.decomposition_exists n hn
    let decompositionProof := Classical.choose hdecomposition
    have hdecomposition_valid := Classical.choose_spec hdecomposition
    let hthreePow := h.threePow_exists n hn
    let threePowProof := Classical.choose hthreePow
    have hthreePow_valid := Classical.choose_spec hthreePow
    let hpayload := h.payload_exists n hn
    let payloadProof := Classical.choose hpayload
    have hpayload_valid := Classical.choose_spec hpayload
    exact
      { component_certificate :=
          { productProof := productProof
            logProof := logProof
            decompositionProof := decompositionProof
            threePowProof := threePowProof
            payloadProof := payloadProof }
        valid :=
          { product_conclusion := hproduct_valid.1
            log_conclusion := hlog_valid.1
            decomposition_conclusion := hdecomposition_valid.1
            threePow_conclusion := hthreePow_valid.1
            payload_conclusion := hpayload_valid.1
            product_size_plus_two_le := hproduct_valid.2
            log_size_plus_two_le := hlog_valid.2
            decomposition_size_plus_two_le := hdecomposition_valid.2
            threePow_size_plus_two_le := hthreePow_valid.2
            payload_size_plus_two_le := hpayload_valid.2 } }

noncomputable def toSemanticNonemptyEventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds) :
    SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  h.toSystemValidEventually.toSemanticNonemptyEventually

end SondowReflectionGraftSidecarComponentProofObjectExistsEventually

def SondowReflectionGraftSidecarProofObjectSystemValidEventually.toComponentProofObjectExistsEventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      SondowReflectionGraftSidecarProofObjectSystemValidEventually
        bounds) :
    SondowReflectionGraftSidecarComponentProofObjectExistsEventually
      bounds where
  threshold := h.threshold
  product_exists := by
    intro n hn
    let entry := h.proof_at n hn
    exact
      ⟨entry.component_certificate.productProof,
        entry.valid.product_conclusion,
        entry.valid.product_size_plus_two_le⟩
  log_exists := by
    intro n hn
    let entry := h.proof_at n hn
    exact
      ⟨entry.component_certificate.logProof,
        entry.valid.log_conclusion,
        entry.valid.log_size_plus_two_le⟩
  decomposition_exists := by
    intro n hn
    let entry := h.proof_at n hn
    exact
      ⟨entry.component_certificate.decompositionProof,
        entry.valid.decomposition_conclusion,
        entry.valid.decomposition_size_plus_two_le⟩
  threePow_exists := by
    intro n hn
    let entry := h.proof_at n hn
    exact
      ⟨entry.component_certificate.threePowProof,
        entry.valid.threePow_conclusion,
        entry.valid.threePow_size_plus_two_le⟩
  payload_exists := by
    intro n hn
    let entry := h.proof_at n hn
    exact
      ⟨entry.component_certificate.payloadProof,
        entry.valid.payload_conclusion,
        entry.valid.payload_size_plus_two_le⟩

theorem sondowReflectionGraftSidecarComponentProofObjectExistsEventually_nonempty_iff_systemValidEventually_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty
        (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
          bounds) ↔
      Nonempty
        (SondowReflectionGraftSidecarProofObjectSystemValidEventually
          bounds) := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toSystemValidEventually⟩
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toComponentProofObjectExistsEventually⟩

/-- Data-level Sondow checked-tail plus the concrete eventual component compiler
directly produce the sidecar proof-object system-valid tail.  This is the
choice-free upstream handoff for computable upper certificates. -/
def sidecarProofObjectSystemValidEventually_of_mainEventualCompiler_checkedTailProvider
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (provider : MainSondowExplicitCheckedTailProvider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    SondowReflectionGraftSidecarProofObjectSystemValidEventually
      bounds :=
  SondowReflectionGraftSidecarProofObjectSystemValidEventually.ofMainEventualCompilerAndCheckedTailProvider
    compiler provider hrat

theorem sidecarProofObjectSystemValidEventually_of_mainEventualCompiler_checkedTailProvider_threshold
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (provider : MainSondowExplicitCheckedTailProvider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (sidecarProofObjectSystemValidEventually_of_mainEventualCompiler_checkedTailProvider
      compiler provider hrat).threshold =
      max compiler.threshold
        (provider.checkedTailOfRationality hrat).threshold :=
  rfl

/-- Forget the data-level system-valid tail to the older component-exists tail.
This implication goes from stronger data to weaker propositions, so it does not
weaken the route. -/
def sidecarComponentProofObjectExistsEventually_of_mainEventualCompiler_checkedTailProvider
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (provider : MainSondowExplicitCheckedTailProvider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    SondowReflectionGraftSidecarComponentProofObjectExistsEventually
      bounds :=
  (sidecarProofObjectSystemValidEventually_of_mainEventualCompiler_checkedTailProvider
    compiler provider hrat).toComponentProofObjectExistsEventually

/-- The semantic S²₁ nonemptiness tail derived from data-level checked
certificates.  This is the clean counterpart of the legacy route through
`SondowRationalityToProjectProofObjectCertificates`, which used choice to
recover the certificates from existential propositions. -/
noncomputable def sidecarS21SemanticNonemptyEventually_of_mainEventualCompiler_checkedTailProvider
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (provider : MainSondowExplicitCheckedTailProvider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  (sidecarProofObjectSystemValidEventually_of_mainEventualCompiler_checkedTailProvider
    compiler provider hrat).toSemanticNonemptyEventually

noncomputable def sidecarComponentProofObjectExistsEventually_of_rationalityProjectProofObjects
    {ctx : BoundedArithmeticLab.GammaRationalityContext}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcerts :
      BoundedArithmeticLab.SondowRationalityToProjectProofObjectCertificates
        ctx bounds)
    (hgamma : BoundedArithmeticLab.GammaRationalityWitness ctx) :
    SondowReflectionGraftSidecarComponentProofObjectExistsEventually
      bounds where
  threshold := Classical.choose (hcerts.certificates_of_rationality hgamma)
  product_exists := by
    intro n hn
    rcases
      (Classical.choose_spec
        (hcerts.certificates_of_rationality hgamma)) n hn with
      ⟨cert, hvalid⟩
    exact
      ⟨cert.productProof,
        hvalid.product_conclusion,
        hvalid.product_size_plus_two_le⟩
  log_exists := by
    intro n hn
    rcases
      (Classical.choose_spec
        (hcerts.certificates_of_rationality hgamma)) n hn with
      ⟨cert, hvalid⟩
    exact
      ⟨cert.logProof,
        hvalid.log_conclusion,
        hvalid.log_size_plus_two_le⟩
  decomposition_exists := by
    intro n hn
    rcases
      (Classical.choose_spec
        (hcerts.certificates_of_rationality hgamma)) n hn with
      ⟨cert, hvalid⟩
    exact
      ⟨cert.decompositionProof,
        hvalid.decomposition_conclusion,
        hvalid.decomposition_size_plus_two_le⟩
  threePow_exists := by
    intro n hn
    rcases
      (Classical.choose_spec
        (hcerts.certificates_of_rationality hgamma)) n hn with
      ⟨cert, hvalid⟩
    exact
      ⟨cert.threePowProof,
        hvalid.threePow_conclusion,
        hvalid.threePow_size_plus_two_le⟩
  payload_exists := by
    intro n hn
    rcases
      (Classical.choose_spec
        (hcerts.certificates_of_rationality hgamma)) n hn with
      ⟨cert, hvalid⟩
    exact
      ⟨cert.payloadProof,
        hvalid.payload_conclusion,
        hvalid.payload_size_plus_two_le⟩

theorem sidecarComponentProofObjectExistsEventually_nonempty_of_rationalityProjectProofObjects
    {ctx : BoundedArithmeticLab.GammaRationalityContext}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcerts :
      Nonempty
        (BoundedArithmeticLab.SondowRationalityToProjectProofObjectCertificates
          ctx bounds))
    (hgamma : BoundedArithmeticLab.GammaRationalityWitness ctx) :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds) := by
  rcases hcerts with ⟨certs⟩
  exact
    ⟨sidecarComponentProofObjectExistsEventually_of_rationalityProjectProofObjects
      certs hgamma⟩

theorem sidecarS21SemanticNonemptyEventually_nonempty_of_componentProofObjectExistsEventually
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcomponent :
      Nonempty
        (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
          bounds)) :
    Nonempty
      SondowReflectionGraftSidecarS21SemanticNonemptyEventually := by
  rcases hcomponent with ⟨certificate⟩
  exact ⟨certificate.toSemanticNonemptyEventually⟩

theorem sidecarS21SemanticNonemptyEventually_nonempty_of_rationalityProjectProofObjects
    {ctx : BoundedArithmeticLab.GammaRationalityContext}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcerts :
      Nonempty
        (BoundedArithmeticLab.SondowRationalityToProjectProofObjectCertificates
          ctx bounds))
    (hgamma : BoundedArithmeticLab.GammaRationalityWitness ctx) :
    Nonempty
      SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  sidecarS21SemanticNonemptyEventually_nonempty_of_componentProofObjectExistsEventually
    (sidecarComponentProofObjectExistsEventually_nonempty_of_rationalityProjectProofObjects
      hcerts hgamma)

theorem sidecarComponentProofObjectExistsEventually_nonempty_of_mainEventualCompiler_and_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty
      (SondowReflectionGraftSidecarComponentProofObjectExistsEventually
        bounds) :=
  ⟨sidecarComponentProofObjectExistsEventually_of_rationalityProjectProofObjects
    compiler.toProjectProofObjectCertificates h_rat⟩

theorem sidecarS21SemanticNonemptyEventually_nonempty_of_mainEventualCompiler_and_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    Nonempty
      SondowReflectionGraftSidecarS21SemanticNonemptyEventually :=
  sidecarS21SemanticNonemptyEventually_nonempty_of_componentProofObjectExistsEventually
    (sidecarComponentProofObjectExistsEventually_nonempty_of_mainEventualCompiler_and_rationality
      compiler h_rat)

/-- The exact upper-bound frontier currently supplied by the concrete Sondow
eventual compiler.  It reaches eventual S²₁ sidecar semantic nonemptiness, not
the all-index PA proof-length calibration used by the final collision box. -/
def SondowReflectionGraftSidecarS21SemanticEventualUpperBound
    (_bounds : BoundedArithmeticLab.SondowComponentBounds) : Prop :=
  _root_.is_rational _root_.euler_mascheroni →
    Nonempty SondowReflectionGraftSidecarS21SemanticNonemptyEventually

theorem sidecarS21SemanticEventualUpperBound_of_mainEventualCompiler
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds) :
    SondowReflectionGraftSidecarS21SemanticEventualUpperBound bounds := by
  intro h_rat
  exact
    sidecarS21SemanticNonemptyEventually_nonempty_of_mainEventualCompiler_and_rationality
      compiler h_rat

/-- Tail version of the certificate-collision lemma.  The existing main-library
collision theorem asks for a proof-length upper bound for every accepted index;
this variant is equivalent for eventual lower bounds and only asks for the
upper bound after a cutoff. -/
theorem eventual_certificate_collision_of_tail_short_proofs
    {T : _root_.ProofSystem} {measure : _root_.ProofLengthMeasure}
    {φ : ℕ → _root_.FormulaCode}
    (accepted_eventually_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          _root_.accepted_certificate (φ n))
    (tail_short_proofs_of_accepted_certificates :
      ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
        ∃ M : ℕ, ∀ n : ℕ, M ≤ n →
          _root_.accepted_certificate (φ n) →
            _root_.proof_length T measure (φ n) ≤ f n)
    (lower_bound : _root_.EventualLowerBound T measure φ) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  intro h_rat
  rcases accepted_eventually_under_rationality h_rat with
    ⟨Naccept, haccept⟩
  rcases tail_short_proofs_of_accepted_certificates with
    ⟨f, hf_poly, Mshort, hshort⟩
  rcases lower_bound.lower_bound f hf_poly (max Naccept Mshort) with
    ⟨n, hn_tail, hgt⟩
  have hn_accept : Naccept ≤ n :=
    le_trans (Nat.le_max_left Naccept Mshort) hn_tail
  have hn_short : Mshort ≤ n :=
    le_trans (Nat.le_max_right Naccept Mshort) hn_tail
  have hle := hshort n hn_short (haccept n hn_accept)
  linarith

/-- Tail-collision lemma where the short-proof tail bridge is itself obtained
under the rationality assumption.  This matches Sondow-style upper bounds: the
short certificates are conditional on rationality. -/
theorem eventual_certificate_collision_of_rationality_tail_short_proofs
    {T : _root_.ProofSystem} {measure : _root_.ProofLengthMeasure}
    {φ : ℕ → _root_.FormulaCode}
    (accepted_eventually_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          _root_.accepted_certificate (φ n))
    (tail_short_proofs_under_rationality :
      _root_.is_rational _root_.euler_mascheroni →
        ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
          ∃ M : ℕ, ∀ n : ℕ, M ≤ n →
            _root_.accepted_certificate (φ n) →
              _root_.proof_length T measure (φ n) ≤ f n)
    (lower_bound : _root_.EventualLowerBound T measure φ) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  intro h_rat
  rcases accepted_eventually_under_rationality h_rat with
    ⟨Naccept, haccept⟩
  rcases tail_short_proofs_under_rationality h_rat with
    ⟨f, hf_poly, Mshort, hshort⟩
  rcases lower_bound.lower_bound f hf_poly (max Naccept Mshort) with
    ⟨n, hn_tail, hgt⟩
  have hn_accept : Naccept ≤ n :=
    le_trans (Nat.le_max_left Naccept Mshort) hn_tail
  have hn_short : Mshort ≤ n :=
    le_trans (Nat.le_max_right Naccept Mshort) hn_tail
  have hle := hshort n hn_short (haccept n hn_accept)
  linarith

/-- Tail short-verification bridge, used when a concrete verifier/calibration
only starts after a threshold. -/
structure EventualShortVerificationBridgeOnTail
    (T : _root_.ProofSystem) (measure : _root_.ProofLengthMeasure)
    (φ : ℕ → _root_.FormulaCode) : Prop where
  verifier_polytime : _root_.certificate_verifier_polytime φ
  short_proofs_of_accepted_certificates_after :
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∃ M : ℕ, ∀ n : ℕ, M ≤ n →
        _root_.accepted_certificate (φ n) →
          _root_.proof_length T measure (φ n) ≤ f n

namespace EventualShortVerificationBridgeOnTail

def ofEventualShortVerificationBridge
    {T : _root_.ProofSystem} {measure : _root_.ProofLengthMeasure}
    {φ : ℕ → _root_.FormulaCode}
    (h : _root_.EventualShortVerificationBridge T measure φ) :
    EventualShortVerificationBridgeOnTail T measure φ where
  verifier_polytime := h.verifier_polytime
  short_proofs_of_accepted_certificates_after := by
    rcases h.short_proofs_of_accepted_certificates with
      ⟨f, hf_poly, hshort⟩
    exact ⟨f, hf_poly, 0, fun n _hn hacc => hshort n hacc⟩

end EventualShortVerificationBridgeOnTail

/-- Family-local linear embedding that only has to hold after a cutoff.  This is
the proof-system calibration shape needed by eventual collision arguments. -/
structure ProofSystemEventualLinearEmbeddingOn
    (source target : _root_.ProofSystem)
    (measure : _root_.ProofLengthMeasure)
    (φ : ℕ → _root_.FormulaCode) where
  threshold : ℕ
  C : ℝ
  D : ℝ
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  target_le_linear_source_after :
    ∀ n : ℕ, threshold ≤ n →
      _root_.proof_length target measure (φ n) ≤
        C * _root_.proof_length source measure (φ n) + D

abbrev S21ToPAEventualLinearEmbeddingOn (φ : ℕ → _root_.FormulaCode) :=
  ProofSystemEventualLinearEmbeddingOn
    _root_.ProofSystem.S21 _root_.ProofSystem.PA
    _root_.ProofLengthMeasure.symbolSize φ

theorem tail_short_proofs_of_source_short_proofs_and_eventual_embedding_on
    {source target : _root_.ProofSystem}
    {measure : _root_.ProofLengthMeasure}
    {φ : ℕ → _root_.FormulaCode}
    (hembed :
      ProofSystemEventualLinearEmbeddingOn source target measure φ)
    (hsource :
      ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
        ∀ n : ℕ, _root_.accepted_certificate (φ n) →
          _root_.proof_length source measure (φ n) ≤ f n) :
    ∃ g : ℕ → ℝ, _root_.is_polynomial_bound g ∧
      ∃ M : ℕ, ∀ n : ℕ, M ≤ n →
        _root_.accepted_certificate (φ n) →
          _root_.proof_length target measure (φ n) ≤ g n := by
  rcases hsource with ⟨f, hf_poly, hf_bound⟩
  refine
    ⟨fun n => hembed.C * f n + hembed.D,
      hf_poly.linear_rescale hembed.C_nonneg hembed.D_nonneg,
      hembed.threshold, ?_⟩
  intro n hn hacc
  have htarget :=
    hembed.target_le_linear_source_after n hn
  have hsource_n := hf_bound n hacc
  have hmul :
      hembed.C *
          _root_.proof_length source measure (φ n) ≤
        hembed.C * f n :=
    mul_le_mul_of_nonneg_left hsource_n hembed.C_nonneg
  nlinarith

def EventualShortVerificationBridgeOnTail.ofSourceBridgeAndEventualEmbedding
    {source target : _root_.ProofSystem}
    {measure : _root_.ProofLengthMeasure}
    {φ : ℕ → _root_.FormulaCode}
    (hsource :
      _root_.EventualShortVerificationBridge source measure φ)
    (hembed :
      ProofSystemEventualLinearEmbeddingOn source target measure φ) :
    EventualShortVerificationBridgeOnTail target measure φ where
  verifier_polytime := hsource.verifier_polytime
  short_proofs_of_accepted_certificates_after :=
    tail_short_proofs_of_source_short_proofs_and_eventual_embedding_on
      hembed hsource.short_proofs_of_accepted_certificates

theorem eventual_certificate_collision_of_tail_inputs
    {T : _root_.ProofSystem} {measure : _root_.ProofLengthMeasure}
    {φ : ℕ → _root_.FormulaCode}
    (hcollapse : _root_.EventualCertificateCollapseInputs φ)
    (hverify : EventualShortVerificationBridgeOnTail T measure φ)
    (hlower : _root_.EventualLowerBound T measure φ) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  eventual_certificate_collision_of_tail_short_proofs
    hcollapse.accepted_eventually_under_rationality
    hverify.short_proofs_of_accepted_certificates_after
    hlower

/-- Root S²₁ proof-length calibration against the bounded-arithmetic sidecar
semantic length. -/
structure SondowReflectionGraftRootS21ProofLengthCalibration where
  root_s21_length_eq :
    ∀ n : ℕ,
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n) =
        BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.BussS21Axiom
          sondowReflectionGraftSidecarTarget n

/-- Root PA proof-length calibration against the bounded-arithmetic sidecar
semantic length. -/
structure SondowReflectionGraftRootPAProofLengthCalibration where
  root_pa_length_eq :
    ∀ n : ℕ,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n) =
        BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.PAAxiom
          sondowReflectionGraftSidecarTarget n

/-- A shared root proof-length convention for the reflection-graft family.  It
groups the two root/sidecar equalities that are still external to the concrete
BA proof-object simulation. -/
structure SondowReflectionGraftRootProofLengthConvention where
  root_s21_length_eq :
    ∀ n : ℕ,
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n) =
        BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.BussS21Axiom
          sondowReflectionGraftSidecarTarget n
  root_pa_length_eq :
    ∀ n : ℕ,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n) =
        BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.PAAxiom
          sondowReflectionGraftSidecarTarget n

namespace SondowReflectionGraftRootProofLengthConvention

def ofSplitCalibrations
    (hs21 : SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa : SondowReflectionGraftRootPAProofLengthCalibration) :
    SondowReflectionGraftRootProofLengthConvention where
  root_s21_length_eq := hs21.root_s21_length_eq
  root_pa_length_eq := hpa.root_pa_length_eq

def toRootS21ProofLengthCalibration
    (h : SondowReflectionGraftRootProofLengthConvention) :
    SondowReflectionGraftRootS21ProofLengthCalibration where
  root_s21_length_eq := h.root_s21_length_eq

def toRootPAProofLengthCalibration
    (h : SondowReflectionGraftRootProofLengthConvention) :
    SondowReflectionGraftRootPAProofLengthCalibration where
  root_pa_length_eq := h.root_pa_length_eq

end SondowReflectionGraftRootProofLengthConvention

theorem sondowReflectionGraftRootProofLengthConvention_nonempty_iff_splitCalibrations_nonempty :
    Nonempty SondowReflectionGraftRootProofLengthConvention ↔
      Nonempty SondowReflectionGraftRootS21ProofLengthCalibration ∧
        Nonempty SondowReflectionGraftRootPAProofLengthCalibration := by
  constructor
  · intro h
    rcases h with ⟨convention⟩
    exact
      ⟨⟨convention.toRootS21ProofLengthCalibration⟩,
        ⟨convention.toRootPAProofLengthCalibration⟩⟩
  · intro h
    rcases h with ⟨hs21, hpa⟩
    rcases hs21 with ⟨s21⟩
    rcases hpa with ⟨pa⟩
    exact
      ⟨SondowReflectionGraftRootProofLengthConvention.ofSplitCalibrations
        s21 pa⟩

/-- Eventual variant of the concrete semantic length calibration.  Unlike
`SondowReflectionGraftConcreteSemanticLengthCalibration`, this only requires
S²₁ sidecar semantic nonemptiness after a cutoff; the root proof-length
equalities remain pointwise equalities for the reflection-graft family. -/
structure SondowReflectionGraftConcreteSemanticLengthCalibrationEventually where
  threshold : ℕ
  s21_semantic_nonempty_after :
    ∀ n : ℕ, threshold ≤ n →
      ∃ p :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        p.conclusion = sondowReflectionGraftSidecarTarget n
  root_s21_length_eq :
    ∀ n : ℕ,
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n) =
        BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.BussS21Axiom
          sondowReflectionGraftSidecarTarget n
  root_pa_length_eq :
    ∀ n : ℕ,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n) =
        BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.PAAxiom
          sondowReflectionGraftSidecarTarget n

namespace SondowReflectionGraftConcreteSemanticLengthCalibrationEventually

def ofSidecarSemanticNonemptyEventuallyAndRootConvention
    (hside : SondowReflectionGraftSidecarS21SemanticNonemptyEventually)
    (hroot : SondowReflectionGraftRootProofLengthConvention) :
    SondowReflectionGraftConcreteSemanticLengthCalibrationEventually where
  threshold := hside.threshold
  s21_semantic_nonempty_after := by
    intro n hn
    exact (hside.proof_at n hn).toExists
  root_s21_length_eq := hroot.root_s21_length_eq
  root_pa_length_eq := hroot.root_pa_length_eq

def ofSidecarSemanticNonemptyEventuallyAndSplitRootCalibrations
    (hside : SondowReflectionGraftSidecarS21SemanticNonemptyEventually)
    (hs21 : SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa : SondowReflectionGraftRootPAProofLengthCalibration) :
    SondowReflectionGraftConcreteSemanticLengthCalibrationEventually :=
  ofSidecarSemanticNonemptyEventuallyAndRootConvention hside
    (SondowReflectionGraftRootProofLengthConvention.ofSplitCalibrations
      hs21 hpa)

theorem concrete_semantic_length_le_after
    (h : SondowReflectionGraftConcreteSemanticLengthCalibrationEventually)
    {n : ℕ} (hn : h.threshold ≤ n) :
    BoundedArithmeticLab.semanticBAProofLength
        BoundedArithmeticLab.PAAxiom
        sondowReflectionGraftSidecarTarget n ≤
      (1 : ℝ) *
        BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.BussS21Axiom
          sondowReflectionGraftSidecarTarget n + 0 := by
  have hsemantic :=
    BoundedArithmeticLab.semanticBAProofLength_pa_le_bussS21
      sondowReflectionGraftSidecarTarget
      (n := n)
      (h.s21_semantic_nonempty_after n hn)
  simpa using hsemantic

noncomputable def toS21ToPAEventualLinearEmbeddingOn
    (h : SondowReflectionGraftConcreteSemanticLengthCalibrationEventually) :
    S21ToPAEventualLinearEmbeddingOn _root_.sondowReflectionGraftCode where
  threshold := h.threshold
  C := 1
  D := 0
  C_nonneg := by norm_num
  D_nonneg := by norm_num
  target_le_linear_source_after := by
    intro n hn
    have hsemantic := h.concrete_semantic_length_le_after hn
    rw [h.root_pa_length_eq n, h.root_s21_length_eq n]
    exact hsemantic

end SondowReflectionGraftConcreteSemanticLengthCalibrationEventually

noncomputable def sondowReflectionGraftTailVerificationBridge_of_s21Bridge_semanticEventual_rootConvention
    (hs21 :
      _root_.EventualShortVerificationBridge
        _root_.ProofSystem.S21 _root_.ProofLengthMeasure.symbolSize
        _root_.sondowReflectionGraftCode)
    (hsemantic :
      SondowReflectionGraftSidecarS21SemanticNonemptyEventually)
    (hroot : SondowReflectionGraftRootProofLengthConvention) :
    EventualShortVerificationBridgeOnTail
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      _root_.sondowReflectionGraftCode :=
  EventualShortVerificationBridgeOnTail.ofSourceBridgeAndEventualEmbedding
    hs21
    ((SondowReflectionGraftConcreteSemanticLengthCalibrationEventually.ofSidecarSemanticNonemptyEventuallyAndRootConvention
        hsemantic hroot).toS21ToPAEventualLinearEmbeddingOn)

/-- Q-parametric tail-verification bridge.  Unlike the legacy rationality
adapter below, this does not select the rational parameter or the Sondow checked
tail from a proposition: the parameter is explicit data, and the tail threshold
is definitionally `max compiler.threshold (max 3 rat.q.den)`. -/
noncomputable def sondowReflectionGraftTailVerificationBridge_of_mainEventualCompiler_rootConvention_and_rationalParameter
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hs21 :
      _root_.EventualShortVerificationBridge
        _root_.ProofSystem.S21 _root_.ProofLengthMeasure.symbolSize
        _root_.sondowReflectionGraftCode)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hroot : SondowReflectionGraftRootProofLengthConvention)
    (rat : MainSondowRationalParameter) :
    EventualShortVerificationBridgeOnTail
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      _root_.sondowReflectionGraftCode :=
  sondowReflectionGraftTailVerificationBridge_of_s21Bridge_semanticEventual_rootConvention
    hs21
    ((SondowReflectionGraftSidecarProofObjectSystemValidEventually.ofMainEventualCompilerAndRationalParameter
        compiler rat)
      |>.toSemanticNonemptyEventually)
    hroot

theorem sondowReflectionGraftTailVerificationBridge_rationalParameter_explicit_short_proofs_after
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hs21 :
      _root_.EventualShortVerificationBridge
        _root_.ProofSystem.S21 _root_.ProofLengthMeasure.symbolSize
        _root_.sondowReflectionGraftCode)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hroot : SondowReflectionGraftRootProofLengthConvention)
    (rat : MainSondowRationalParameter) :
    ∃ g : ℕ → ℝ, _root_.is_polynomial_bound g ∧
      ∀ n : ℕ, max compiler.threshold (max 3 rat.q.den) ≤ n →
        _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) →
          _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) ≤ g n := by
  rcases hs21.short_proofs_of_accepted_certificates with
    ⟨f, hf_poly, hf_bound⟩
  let hsemantic :=
    (SondowReflectionGraftSidecarProofObjectSystemValidEventually.ofMainEventualCompilerAndRationalParameter
        compiler rat)
      |>.toSemanticNonemptyEventually
  let hcal :=
    SondowReflectionGraftConcreteSemanticLengthCalibrationEventually.ofSidecarSemanticNonemptyEventuallyAndRootConvention
      hsemantic hroot
  let hembed := hcal.toS21ToPAEventualLinearEmbeddingOn
  refine
    ⟨fun n => hembed.C * f n + hembed.D,
      hf_poly.linear_rescale hembed.C_nonneg hembed.D_nonneg,
      ?_⟩
  intro n hn hacc
  have hthreshold : hembed.threshold ≤ n := by
    dsimp [hembed, hcal, hsemantic,
      SondowReflectionGraftSidecarProofObjectSystemValidEventually.ofMainEventualCompilerAndRationalParameter,
      SondowReflectionGraftSidecarProofObjectSystemValidEventually.ofMainEventualCompilerAndCheckedTail,
      SondowReflectionGraftConcreteSemanticLengthCalibrationEventually.toS21ToPAEventualLinearEmbeddingOn,
      SondowReflectionGraftConcreteSemanticLengthCalibrationEventually.ofSidecarSemanticNonemptyEventuallyAndRootConvention,
      SondowReflectionGraftSidecarProofObjectSystemValidEventually.toSemanticNonemptyEventually,
      MainSondowRationalParameter.checkedTail,
      MainSondowFullCertificateCheckedTail.ofReproofRationalParameter]
    exact hn
  have htarget :=
    hembed.target_le_linear_source_after n hthreshold
  have hsource := hf_bound n hacc
  have hmul :
      hembed.C *
          _root_.proof_length _root_.ProofSystem.S21
            _root_.ProofLengthMeasure.symbolSize
            (_root_.sondowReflectionGraftCode n) ≤
        hembed.C * f n :=
    mul_le_mul_of_nonneg_left hsource hembed.C_nonneg
  nlinarith

theorem accepted_sondowReflectionGraftCode_after_rationalParameter_payloadTruth
    (rat : MainSondowRationalParameter)
    (hpayload : _root_.PartialConsistencyPayloadTruth) :
    ∀ n : ℕ, max 3 rat.q.den ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) := by
  intro n hn
  have htail :=
    (MainSondowFullCertificateCheckedTail.ofReproofRationalParameter
      rat.q rat.gamma_eq).checked_at n hn
  exact
    ⟨htail.q,
      htail.checked,
      hpayload.true_all n⟩

theorem sondowReflectionGraft_rationalParameter_payloadTruth_explicit_upper_tail_prop
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hs21 :
      _root_.EventualShortVerificationBridge
        _root_.ProofSystem.S21 _root_.ProofLengthMeasure.symbolSize
        _root_.sondowReflectionGraftCode)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hroot : SondowReflectionGraftRootProofLengthConvention)
    (rat : MainSondowRationalParameter)
    (hpayload : _root_.PartialConsistencyPayloadTruth) :
    ∃ U : ℕ → ℝ, _root_.is_polynomial_bound U ∧
      ∀ n : ℕ, max compiler.threshold (max 3 rat.q.den) ≤ n →
        _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) ∧
          _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) ≤ U n := by
  rcases
    sondowReflectionGraftTailVerificationBridge_rationalParameter_explicit_short_proofs_after
      hs21 compiler hroot rat with
    ⟨U, hU_poly, hU_after⟩
  exact
    ⟨U, hU_poly, fun n hn => by
      have haccepted :
          _root_.accepted_certificate (_root_.sondowReflectionGraftCode n) :=
        accepted_sondowReflectionGraftCode_after_rationalParameter_payloadTruth
          rat hpayload n (le_trans (Nat.le_max_right compiler.threshold
            (max 3 rat.q.den)) hn)
      exact ⟨haccepted, hU_after n hn haccepted⟩⟩

noncomputable def sondowReflectionGraftTailVerificationBridge_of_mainEventualCompiler_rootConvention_and_rationality
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hs21 :
      _root_.EventualShortVerificationBridge
        _root_.ProofSystem.S21 _root_.ProofLengthMeasure.symbolSize
        _root_.sondowReflectionGraftCode)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hroot : SondowReflectionGraftRootProofLengthConvention)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    EventualShortVerificationBridgeOnTail
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      _root_.sondowReflectionGraftCode := by
  rcases
    sidecarS21SemanticNonemptyEventually_nonempty_of_mainEventualCompiler_and_rationality
      compiler h_rat with
    ⟨hsemantic⟩
  exact
    sondowReflectionGraftTailVerificationBridge_of_s21Bridge_semanticEventual_rootConvention
      hs21 hsemantic hroot

theorem irrational_of_sondowReflectionGraft_mainEventualCompiler_rootConvention_s21Bridge_tailLowerBound
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcollapse :
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode)
    (hs21 :
      _root_.EventualShortVerificationBridge
        _root_.ProofSystem.S21 _root_.ProofLengthMeasure.symbolSize
        _root_.sondowReflectionGraftCode)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hroot : SondowReflectionGraftRootProofLengthConvention)
    (hlower :
      _root_.EventualLowerBound
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        _root_.sondowReflectionGraftCode) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  eventual_certificate_collision_of_rationality_tail_short_proofs
    hcollapse.accepted_eventually_under_rationality
    (fun h_rat =>
      (sondowReflectionGraftTailVerificationBridge_of_mainEventualCompiler_rootConvention_and_rationality
        hs21 compiler hroot h_rat).short_proofs_of_accepted_certificates_after)
    hlower

theorem irrational_of_sondowReflectionGraft_mainEventualCompiler_rootConvention_kernel_tailLowerBound
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcollapse :
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode)
    (kernel : SondowProjectLocalS21Kernel)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hroot : SondowReflectionGraftRootProofLengthConvention)
    (hlower :
      _root_.EventualLowerBound
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        _root_.sondowReflectionGraftCode) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_sondowReflectionGraft_mainEventualCompiler_rootConvention_s21Bridge_tailLowerBound
    hcollapse kernel.toReflectionGraftS21ShortVerificationBridge compiler
    hroot hlower

theorem irrational_of_sondowReflectionGraft_mainEventualCompiler_splitRootCalibrations_kernel_tailLowerBound
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcollapse :
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode)
    (kernel : SondowProjectLocalS21Kernel)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hs21root : SondowReflectionGraftRootS21ProofLengthCalibration)
    (hparoot : SondowReflectionGraftRootPAProofLengthCalibration)
    (hlower :
      _root_.EventualLowerBound
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        _root_.sondowReflectionGraftCode) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_sondowReflectionGraft_mainEventualCompiler_rootConvention_kernel_tailLowerBound
    hcollapse kernel compiler
    (SondowReflectionGraftRootProofLengthConvention.ofSplitCalibrations
      hs21root hparoot)
    hlower

/-- Recognition-theorem form of the root proof-length convention.  The fields
are oriented as semantic sidecar length equals the main repository
`proof_length` on the reflection-graft family, making the remaining external
proof-system obligation explicit and local. -/
structure SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem where
  sidecar_s21_length_eq_root :
    ∀ n : ℕ,
      BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.BussS21Axiom
          sondowReflectionGraftSidecarTarget n =
        _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n)
  sidecar_pa_length_eq_root :
    ∀ n : ℕ,
      BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.PAAxiom
          sondowReflectionGraftSidecarTarget n =
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n)

namespace SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem

def toRootProofLengthConvention
    (h : SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem) :
    SondowReflectionGraftRootProofLengthConvention where
  root_s21_length_eq := by
    intro n
    exact (h.sidecar_s21_length_eq_root n).symm
  root_pa_length_eq := by
    intro n
    exact (h.sidecar_pa_length_eq_root n).symm

def toRootS21ProofLengthCalibration
    (h : SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem) :
    SondowReflectionGraftRootS21ProofLengthCalibration :=
  h.toRootProofLengthConvention.toRootS21ProofLengthCalibration

def toRootPAProofLengthCalibration
    (h : SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem) :
    SondowReflectionGraftRootPAProofLengthCalibration :=
  h.toRootProofLengthConvention.toRootPAProofLengthCalibration

end SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem

def SondowReflectionGraftRootProofLengthConvention.toSidecarSemanticLengthRecognitionTheorem
    (h : SondowReflectionGraftRootProofLengthConvention) :
    SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem where
  sidecar_s21_length_eq_root := by
    intro n
    exact (h.root_s21_length_eq n).symm
  sidecar_pa_length_eq_root := by
    intro n
    exact (h.root_pa_length_eq n).symm

theorem sondowReflectionGraftSidecarSemanticLengthRecognition_nonempty_iff_rootConvention_nonempty :
    Nonempty SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem ↔
      Nonempty SondowReflectionGraftRootProofLengthConvention := by
  constructor
  · intro h
    rcases h with ⟨recognition⟩
    exact ⟨recognition.toRootProofLengthConvention⟩
  · intro h
    rcases h with ⟨convention⟩
    exact
      ⟨convention.toSidecarSemanticLengthRecognitionTheorem⟩

/-- Split form of the sidecar semantic-length recognition obligation.  The
family-code equality is already checked by definitional computation; the only
external witness left here is the root proof-length convention for the abstract
main `proof_length` symbol. -/
structure SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate
    where
  family_code_equality :
    SondowReflectionGraftSidecarFamilyCodeEquality
  proof_length_convention :
    SondowReflectionGraftRootProofLengthConvention

namespace SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate

def toRecognitionTheorem
    (h :
      SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem :=
  h.proof_length_convention.toSidecarSemanticLengthRecognitionTheorem

end SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate

def SondowReflectionGraftRootProofLengthConvention.toRecognitionSplit
    (h : SondowReflectionGraftRootProofLengthConvention) :
    SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate where
  family_code_equality :=
    sondowReflectionGraftSidecarFamilyCodeEquality
  proof_length_convention := h

theorem sondowReflectionGraftRecognitionSplit_nonempty_iff_rootConvention_nonempty :
    Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate ↔
      Nonempty SondowReflectionGraftRootProofLengthConvention := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.proof_length_convention⟩
  · intro h
    rcases h with ⟨convention⟩
    exact ⟨convention.toRecognitionSplit⟩

theorem sondowReflectionGraftRecognition_nonempty_iff_split_nonempty :
    Nonempty SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem ↔
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate := by
  calc
    Nonempty SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem ↔
        Nonempty SondowReflectionGraftRootProofLengthConvention :=
      sondowReflectionGraftSidecarSemanticLengthRecognition_nonempty_iff_rootConvention_nonempty
    _ ↔ Nonempty
          SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate :=
      (sondowReflectionGraftRecognitionSplit_nonempty_iff_rootConvention_nonempty).symm

/-- Auditable checked-code convention witness for the root reflection-graft
family.  The code equality is checked locally; the semantic-length recognition
field is the remaining proof-length convention tying the abstract root
`proof_length` symbols to the sidecar semantic lengths. -/
structure SondowReflectionGraftRootCheckedCodeConventionWitness where
  family_code_equality :
    SondowReflectionGraftSidecarFamilyCodeEquality
  semantic_length_recognition :
    SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem

namespace SondowReflectionGraftRootCheckedCodeConventionWitness

def toRootProofLengthConvention
    (h : SondowReflectionGraftRootCheckedCodeConventionWitness) :
    SondowReflectionGraftRootProofLengthConvention :=
  h.semantic_length_recognition.toRootProofLengthConvention

def toRootS21ProofLengthCalibration
    (h : SondowReflectionGraftRootCheckedCodeConventionWitness) :
    SondowReflectionGraftRootS21ProofLengthCalibration :=
  h.toRootProofLengthConvention.toRootS21ProofLengthCalibration

def toRootPAProofLengthCalibration
    (h : SondowReflectionGraftRootCheckedCodeConventionWitness) :
    SondowReflectionGraftRootPAProofLengthCalibration :=
  h.toRootProofLengthConvention.toRootPAProofLengthCalibration

def toRecognitionSplit
    (h : SondowReflectionGraftRootCheckedCodeConventionWitness) :
    SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate where
  family_code_equality := h.family_code_equality
  proof_length_convention := h.toRootProofLengthConvention

end SondowReflectionGraftRootCheckedCodeConventionWitness

def SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem.toCheckedCodeConventionWitness
    (h : SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem) :
    SondowReflectionGraftRootCheckedCodeConventionWitness where
  family_code_equality := sondowReflectionGraftSidecarFamilyCodeEquality
  semantic_length_recognition := h

def SondowReflectionGraftRootProofLengthConvention.toCheckedCodeConventionWitness
    (h : SondowReflectionGraftRootProofLengthConvention) :
    SondowReflectionGraftRootCheckedCodeConventionWitness :=
  h.toSidecarSemanticLengthRecognitionTheorem.toCheckedCodeConventionWitness

theorem sondowReflectionGraftCheckedCodeConventionWitness_nonempty_iff_rootConvention_nonempty :
    Nonempty SondowReflectionGraftRootCheckedCodeConventionWitness ↔
      Nonempty SondowReflectionGraftRootProofLengthConvention := by
  constructor
  · intro h
    rcases h with ⟨witness⟩
    exact ⟨witness.toRootProofLengthConvention⟩
  · intro h
    rcases h with ⟨convention⟩
    exact ⟨convention.toCheckedCodeConventionWitness⟩

theorem irrational_of_sondowReflectionGraft_mainEventualCompiler_checkedCodeConventionWitness_kernel_tailLowerBound
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hcollapse :
      _root_.EventualCertificateCollapseInputs
        _root_.sondowReflectionGraftCode)
    (kernel : SondowProjectLocalS21Kernel)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hwitness : SondowReflectionGraftRootCheckedCodeConventionWitness)
    (hlower :
      _root_.EventualLowerBound
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        _root_.sondowReflectionGraftCode) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  irrational_of_sondowReflectionGraft_mainEventualCompiler_rootConvention_kernel_tailLowerBound
    hcollapse kernel compiler hwitness.toRootProofLengthConvention hlower

/-- PA root calibration through the existing concrete Buss/Pudlak sidecar
calibration.  The only extra root-side input is the equality between main
`proof_length PA` on `sondowReflectionGraftCode` and the Pudlak lower-source
length. -/
structure SondowReflectionGraftRootPALengthFromPudlakCalibration where
  pudlak_calibration :
    BoundedArithmeticLab.ConcreteBussPudlakFormulaLengthCalibration
      sondowReflectionGraftSidecarTarget
      sondowReflectionGraftSidecarCode
  root_pa_eq_pudlak_length :
    ∀ n : ℕ,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n) =
        pudlak_calibration.lower_source.pa_length n

namespace SondowReflectionGraftRootPALengthFromPudlakCalibration

def toRootPAProofLengthCalibration
    (h : SondowReflectionGraftRootPALengthFromPudlakCalibration) :
    SondowReflectionGraftRootPAProofLengthCalibration where
  root_pa_length_eq := by
    intro n
    calc
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n) =
        h.pudlak_calibration.lower_source.pa_length n :=
          h.root_pa_eq_pudlak_length n
      _ =
        BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.PAAxiom
          sondowReflectionGraftSidecarTarget n :=
          h.pudlak_calibration.length_eq n

end SondowReflectionGraftRootPALengthFromPudlakCalibration

/-- Split certificate chain for the concrete semantic length calibration. -/
structure SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate where
  sidecar_s21_nonempty :
    SondowReflectionGraftSidecarS21SemanticNonempty
  root_s21_calibration :
    SondowReflectionGraftRootS21ProofLengthCalibration
  root_pa_calibration :
    SondowReflectionGraftRootPAProofLengthCalibration

/-- Main/sidecar length calibration needed to turn the concrete proof-object
simulation into the main repository's local S²₁-to-PA embedding interface.  The
fields are intentionally explicit: the object simulation is concrete, while the
main `proof_length` symbol is abstract and must be calibrated on this family. -/
structure SondowReflectionGraftConcreteSemanticLengthCalibration where
  s21_semantic_nonempty :
    ∀ n : ℕ,
      ∃ p :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        p.conclusion = sondowReflectionGraftSidecarTarget n
  root_s21_length_eq :
    ∀ n : ℕ,
      _root_.proof_length _root_.ProofSystem.S21
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n) =
        BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.BussS21Axiom
          sondowReflectionGraftSidecarTarget n
  root_pa_length_eq :
    ∀ n : ℕ,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode n) =
        BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.PAAxiom
          sondowReflectionGraftSidecarTarget n

namespace SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate

def toConcreteSemanticLengthCalibration
    (h :
      SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate) :
    SondowReflectionGraftConcreteSemanticLengthCalibration where
  s21_semantic_nonempty :=
    h.sidecar_s21_nonempty.semantic_nonempty
  root_s21_length_eq :=
    h.root_s21_calibration.root_s21_length_eq
  root_pa_length_eq :=
    h.root_pa_calibration.root_pa_length_eq

def ofSidecarProofObjectsAndRootConvention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hside :
      SondowReflectionGraftSidecarProofObjectSystemValidCertificate
        bounds)
    (hroot : SondowReflectionGraftRootProofLengthConvention) :
    SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate where
  sidecar_s21_nonempty := hside.toSidecarS21SemanticNonempty
  root_s21_calibration := hroot.toRootS21ProofLengthCalibration
  root_pa_calibration := hroot.toRootPAProofLengthCalibration

def ofSidecarProofObjectsAndLengthRecognition
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hside :
      SondowReflectionGraftSidecarProofObjectSystemValidCertificate
        bounds)
    (hrecognition :
      SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem) :
    SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate :=
  ofSidecarProofObjectsAndRootConvention hside
    hrecognition.toRootProofLengthConvention

def ofSidecarProofObjectsAndSplitRootCalibration
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hside :
      SondowReflectionGraftSidecarProofObjectSystemValidCertificate
        bounds)
    (hs21 : SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa : SondowReflectionGraftRootPAProofLengthCalibration) :
    SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate where
  sidecar_s21_nonempty := hside.toSidecarS21SemanticNonempty
  root_s21_calibration := hs21
  root_pa_calibration := hpa

end SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate

/-- Checked proof-object plus recognition-theorem front door for the concrete
semantic length calibration.  Compared with the split certificate, the S²₁
sidecar nonemptiness is sourced from all-index `ProofObjectSystemValid`, while
the remaining root obligation is isolated as semantic-length recognition. -/
structure SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate where
  bounds : BoundedArithmeticLab.SondowComponentBounds
  sidecar_proof_objects :
    SondowReflectionGraftSidecarProofObjectSystemValidCertificate
      bounds
  length_recognition :
    SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem

namespace SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate

def ofCheckerExactAndLengthRecognition
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hchecker :
      SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
        bounds)
    (hrecognition :
      SondowReflectionGraftSidecarSemanticLengthRecognitionTheorem) :
    SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate where
  bounds := bounds
  sidecar_proof_objects :=
    hchecker.toProofObjectSystemValidCertificate
  length_recognition := hrecognition

def ofCheckerExactAndSplitRecognition
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hchecker :
      SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
        bounds)
    (hrecognition :
      SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate :=
  ofCheckerExactAndLengthRecognition hchecker
    hrecognition.toRecognitionTheorem

def ofCheckerExactSplit
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hchecker :
      SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
        bounds)
    (hrecognition :
      SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate :=
  ofCheckerExactAndSplitRecognition hchecker hrecognition

def toSplitCertificate
    (h :
      SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate) :
    SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate :=
  SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate.ofSidecarProofObjectsAndLengthRecognition
    h.sidecar_proof_objects h.length_recognition

def toConcreteSemanticLengthCalibration
    (h :
      SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate) :
    SondowReflectionGraftConcreteSemanticLengthCalibration :=
  h.toSplitCertificate.toConcreteSemanticLengthCalibration

end SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate

theorem sondowReflectionGraftConcreteSemanticLengthRecognitionCertificate_nonempty_to_splitCertificate_nonempty
    (h :
      Nonempty
        SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate) :
    Nonempty
      SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toSplitCertificate⟩

theorem sondowReflectionGraftConcreteSemanticLengthRecognitionCertificate_nonempty_to_calibration_nonempty
    (h :
      Nonempty
        SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate) :
    Nonempty SondowReflectionGraftConcreteSemanticLengthCalibration := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toConcreteSemanticLengthCalibration⟩

noncomputable def SondowReflectionGraftConcreteSemanticLengthCalibration.toCertificate
    (h : SondowReflectionGraftConcreteSemanticLengthCalibration) :
    SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate where
  sidecar_s21_nonempty := {
    proof_at := fun n =>
      { proof_object := Classical.choose (h.s21_semantic_nonempty n)
        conclusion_eq :=
          Classical.choose_spec (h.s21_semantic_nonempty n) } }
  root_s21_calibration := {
    root_s21_length_eq := h.root_s21_length_eq }
  root_pa_calibration := {
    root_pa_length_eq := h.root_pa_length_eq }

theorem sondowReflectionGraftConcreteSemanticLengthCalibration_nonempty_iff_splitCertificate_nonempty :
    Nonempty SondowReflectionGraftConcreteSemanticLengthCalibration ↔
      Nonempty
        SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate := by
  constructor
  · intro h
    rcases h with ⟨calibration⟩
    exact ⟨calibration.toCertificate⟩
  · intro h
    rcases h with ⟨certificate⟩
    exact ⟨certificate.toConcreteSemanticLengthCalibration⟩

namespace SondowReflectionGraftConcreteSemanticLengthCalibration

theorem concrete_semantic_length_le
    (h : SondowReflectionGraftConcreteSemanticLengthCalibration)
    (n : ℕ) :
    BoundedArithmeticLab.semanticBAProofLength
        BoundedArithmeticLab.PAAxiom
        sondowReflectionGraftSidecarTarget n ≤
      (BoundedArithmeticLab.concreteS21ToPALinearObjectSimulation
          sondowReflectionGraftSidecarTarget
          sondowReflectionGraftSidecarCode).C *
        BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.BussS21Axiom
          sondowReflectionGraftSidecarTarget n +
        (BoundedArithmeticLab.concreteS21ToPALinearObjectSimulation
          sondowReflectionGraftSidecarTarget
          sondowReflectionGraftSidecarCode).D := by
  have hsemantic :=
    BoundedArithmeticLab.semanticBAProofLength_pa_le_bussS21
      sondowReflectionGraftSidecarTarget
      (n := n)
      (h.s21_semantic_nonempty n)
  change
    BoundedArithmeticLab.semanticBAProofLength
        BoundedArithmeticLab.PAAxiom
        sondowReflectionGraftSidecarTarget n ≤
      (1 : ℝ) *
        BoundedArithmeticLab.semanticBAProofLength
          BoundedArithmeticLab.BussS21Axiom
          sondowReflectionGraftSidecarTarget n + 0
  simpa using hsemantic

noncomputable def toS21ToPALinearEmbeddingOn
    (h : SondowReflectionGraftConcreteSemanticLengthCalibration) :
    _root_.S21ToPALinearEmbeddingOn
      _root_.sondowReflectionGraftCode where
  C :=
    (BoundedArithmeticLab.concreteS21ToPALinearObjectSimulation
      sondowReflectionGraftSidecarTarget
      sondowReflectionGraftSidecarCode).C
  D :=
    (BoundedArithmeticLab.concreteS21ToPALinearObjectSimulation
      sondowReflectionGraftSidecarTarget
      sondowReflectionGraftSidecarCode).D
  C_nonneg :=
    (BoundedArithmeticLab.concreteS21ToPALinearObjectSimulation
      sondowReflectionGraftSidecarTarget
      sondowReflectionGraftSidecarCode).C_nonneg
  D_nonneg :=
    (BoundedArithmeticLab.concreteS21ToPALinearObjectSimulation
      sondowReflectionGraftSidecarTarget
      sondowReflectionGraftSidecarCode).D_nonneg
  target_le_linear_source := by
    intro n
    have hsemantic := h.concrete_semantic_length_le n
    rw [h.root_pa_length_eq n, h.root_s21_length_eq n]
    exact hsemantic

theorem toS21ToPALinearEmbeddingOn_C_eq_one
    (h : SondowReflectionGraftConcreteSemanticLengthCalibration) :
    h.toS21ToPALinearEmbeddingOn.C = 1 := by
  rfl

theorem toS21ToPALinearEmbeddingOn_D_eq_zero
    (h : SondowReflectionGraftConcreteSemanticLengthCalibration) :
    h.toS21ToPALinearEmbeddingOn.D = 0 := by
  rfl

end SondowReflectionGraftConcreteSemanticLengthCalibration

theorem sondowReflectionGraftConcreteSemanticLengthCalibration_nonempty_to_paEmbedding_nonempty
    (hcal :
      Nonempty SondowReflectionGraftConcreteSemanticLengthCalibration) :
    Nonempty
      (_root_.S21ToPALinearEmbeddingOn
        _root_.sondowReflectionGraftCode) := by
  rcases hcal with ⟨calibration⟩
  exact ⟨calibration.toS21ToPALinearEmbeddingOn⟩

noncomputable def SondowProjectLocalS21Kernel.toTraceCollapseCompletionOfConcreteSemanticCalibration
    (kernel : SondowProjectLocalS21Kernel)
    (htruth : _root_.PartialConsistencyPayloadTruth)
    (hcal : SondowReflectionGraftConcreteSemanticLengthCalibration) :
    SondowProjectLocalS21TraceCollapseCompletion where
  sondow_trace := kernel.sondow_trace
  partial_standard_calibration :=
    PartialConsistencyStandardS21TraceCalibration.ofPayloadTruthAndTraceSoundness
      htruth kernel.partial_consistency_trace
  graft_intro := kernel.graft_intro
  pa_embedding := hcal.toS21ToPALinearEmbeddingOn

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

/-- Certificate-chain form of the local verifier construction.  Compared with
`SondowProjectLocalReflectionGraftVerifier`, the PA side is not a bare field:
it is produced from the bounded-arithmetic proof-object simulation plus an
explicit calibration of the main `proof_length` symbol on the reflection-graft
family. -/
structure SondowProjectLocalReflectionGraftVerifierConcreteCertificate where
  kernel : SondowProjectLocalS21Kernel
  reflection_graft_length_calibration :
    SondowReflectionGraftConcreteSemanticLengthCalibration

noncomputable def SondowProjectLocalReflectionGraftVerifierConcreteCertificate.toVerifier
    (h : SondowProjectLocalReflectionGraftVerifierConcreteCertificate) :
    SondowProjectLocalReflectionGraftVerifier :=
  h.kernel.toReflectionGraftVerifier
    h.reflection_graft_length_calibration.toS21ToPALinearEmbeddingOn

theorem sondowProjectLocalReflectionGraftVerifierConcreteCertificate_nonempty_iff :
    Nonempty SondowProjectLocalReflectionGraftVerifierConcreteCertificate ↔
      Nonempty SondowProjectLocalS21Kernel ∧
        Nonempty SondowReflectionGraftConcreteSemanticLengthCalibration := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact
      ⟨⟨certificate.kernel⟩,
        ⟨certificate.reflection_graft_length_calibration⟩⟩
  · intro h
    rcases h with ⟨hkernel, hcal⟩
    rcases hkernel with ⟨kernel⟩
    rcases hcal with ⟨calibration⟩
    exact
      ⟨{ kernel := kernel
         reflection_graft_length_calibration := calibration }⟩

/-- Fully split certificate-chain form of the local reflection-graft verifier:
the kernel is sourced from the primitive checked-code/payload/graft
certificates, and the PA embedding is sourced from the split concrete semantic
length calibration certificate. -/
structure SondowProjectLocalReflectionGraftVerifierSplitConcreteCertificate where
  kernel_certificate :
    SondowProjectLocalS21PrimitiveKernelCertificate.{u}
  reflection_graft_length_certificate :
    SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate

noncomputable def SondowProjectLocalReflectionGraftVerifierSplitConcreteCertificate.toConcreteCertificate
    (h :
      SondowProjectLocalReflectionGraftVerifierSplitConcreteCertificate.{u}) :
    SondowProjectLocalReflectionGraftVerifierConcreteCertificate where
  kernel := h.kernel_certificate.toKernel
  reflection_graft_length_calibration :=
    h.reflection_graft_length_certificate
      |>.toConcreteSemanticLengthCalibration

noncomputable def SondowProjectLocalReflectionGraftVerifierSplitConcreteCertificate.toVerifier
    (h :
      SondowProjectLocalReflectionGraftVerifierSplitConcreteCertificate.{u}) :
    SondowProjectLocalReflectionGraftVerifier :=
  h.toConcreteCertificate.toVerifier

theorem sondowProjectLocalReflectionGraftVerifierSplitConcreteCertificate_nonempty_to_concreteCertificate_nonempty
    (h :
      Nonempty
        SondowProjectLocalReflectionGraftVerifierSplitConcreteCertificate.{u}) :
    Nonempty SondowProjectLocalReflectionGraftVerifierConcreteCertificate := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toConcreteCertificate⟩

theorem sondowProjectLocalReflectionGraftVerifierSplitConcreteCertificate_nonempty_to_verifier_nonempty
    (h :
      Nonempty
        SondowProjectLocalReflectionGraftVerifierSplitConcreteCertificate.{u}) :
    Nonempty SondowProjectLocalReflectionGraftVerifier := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toVerifier⟩

theorem sondowProjectLocalReflectionGraftVerifierSplitConcreteCertificate_nonempty_of_costAbsorptionKernel_and_lengthCertificate
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hcal :
      Nonempty
        SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate) :
    Nonempty
      SondowProjectLocalReflectionGraftVerifierSplitConcreteCertificate.{u} := by
  rcases hkernel with ⟨kernel_certificate⟩
  rcases hcal with ⟨length_certificate⟩
  exact
    ⟨{ kernel_certificate :=
          kernel_certificate.toPrimitiveKernelCertificate
       reflection_graft_length_certificate := length_certificate }⟩

/-- Direct concrete checked-code front door for the local reflection-graft
verifier.  The kernel side is the cost/absorption checked-code certificate; the
PA side is the sidecar proof-object plus semantic-length recognition
certificate, so the only remaining proof-length convention is named in the
length certificate. -/
structure SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate where
  kernel_certificate :
    SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}
  length_recognition_certificate :
    SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate

namespace SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate

def lengthCertificate
    (h :
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u}) :
    SondowReflectionGraftConcreteSemanticLengthCalibrationCertificate :=
  h.length_recognition_certificate.toSplitCertificate

def toSplitConcreteCertificate
    (h :
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u}) :
    SondowProjectLocalReflectionGraftVerifierSplitConcreteCertificate.{u} where
  kernel_certificate :=
    h.kernel_certificate.toPrimitiveKernelCertificate
  reflection_graft_length_certificate := h.lengthCertificate

noncomputable def toConcreteCertificate
    (h :
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u}) :
    SondowProjectLocalReflectionGraftVerifierConcreteCertificate :=
  h.toSplitConcreteCertificate.toConcreteCertificate

noncomputable def toVerifier
    (h :
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u}) :
    SondowProjectLocalReflectionGraftVerifier :=
  h.toSplitConcreteCertificate.toVerifier

theorem payloadTruth
    (h :
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u}) :
    _root_.PartialConsistencyPayloadTruth :=
  h.kernel_certificate.payloadTruth

def payloadSpecCertificate
    (h :
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u}) :
    PartialConsistencyPayloadSpecCertificate :=
  h.kernel_certificate.payloadSpecCertificate

noncomputable def toDirectTraceCompletion
    (h :
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u}) :
    SondowProjectLocalDirectTraceCollapseCompletion :=
  h.toVerifier.toDirectTraceCompletion h.payloadTruth

end SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate

theorem sondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate_nonempty_iff :
    Nonempty
        SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u} ↔
      Nonempty
          SondowProjectLocalS21KernelCostAbsorptionCertificate.{u} ∧
        Nonempty
          SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact
      ⟨⟨certificate.kernel_certificate⟩,
        ⟨certificate.length_recognition_certificate⟩⟩
  · intro h
    rcases h with ⟨hkernel, hlength⟩
    rcases hkernel with ⟨kernel_certificate⟩
    rcases hlength with ⟨length_recognition_certificate⟩
    exact
      ⟨{ kernel_certificate := kernel_certificate
         length_recognition_certificate :=
          length_recognition_certificate }⟩

theorem sondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate_nonempty_to_splitConcreteCertificate_nonempty
    (h :
      Nonempty
        SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u}) :
    Nonempty
      SondowProjectLocalReflectionGraftVerifierSplitConcreteCertificate.{u} := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toSplitConcreteCertificate⟩

theorem sondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate_nonempty_to_verifier_nonempty
    (h :
      Nonempty
        SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u}) :
    Nonempty SondowProjectLocalReflectionGraftVerifier := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toVerifier⟩

theorem sondowProjectLocalReflectionGraftVerifier_nonempty_of_costAbsorptionKernel_and_semanticLengthRecognition
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hlength :
      Nonempty
        SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate) :
    Nonempty SondowProjectLocalReflectionGraftVerifier :=
  sondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate_nonempty_to_verifier_nonempty
    ((sondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate_nonempty_iff).2
      ⟨hkernel, hlength⟩)

theorem sondowCLineVerifier_nonempty_of_kernel_checkerExact_splitLength
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    Nonempty SondowProjectLocalReflectionGraftVerifier := by
  rcases hchecker with ⟨checker⟩
  rcases hlength with ⟨length⟩
  rcases hkernel with ⟨kernel⟩
  let hsemantic :
      SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate :=
    SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate.ofCheckerExactSplit
      checker length
  exact
    ⟨({ kernel_certificate := kernel
        length_recognition_certificate := hsemantic } :
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u})
      |>.toVerifier⟩

theorem sondowProjectLocalReflectionGraftVerifier_nonempty_of_concreteCertificate
    (h :
      Nonempty
        SondowProjectLocalReflectionGraftVerifierConcreteCertificate) :
    Nonempty SondowProjectLocalReflectionGraftVerifier := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toVerifier⟩

theorem kernelAndConcreteSemanticCalibration_nonempty_to_reflectionGraftVerifier_nonempty
    (hkernel : Nonempty SondowProjectLocalS21Kernel)
    (hcal :
      Nonempty SondowReflectionGraftConcreteSemanticLengthCalibration) :
    Nonempty SondowProjectLocalReflectionGraftVerifier :=
  sondowProjectLocalReflectionGraftVerifier_nonempty_of_concreteCertificate
    ((sondowProjectLocalReflectionGraftVerifierConcreteCertificate_nonempty_iff).2
      ⟨hkernel, hcal⟩)

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

/-- Q-parametric compatibility theorem for the old project-local S²₁ collapse
surface.  The threshold is explicit in the construction,
`max compiler.threshold (max 3 rat.q.den)`, but the result is deliberately
forgotten back to the old propositional `∃ f, ∃ N` interface. -/
theorem sondowProjectLocalS21CollapseConclusion_of_rationalParameter_mainEventualCompiler_rootConvention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hs21 :
      _root_.EventualShortVerificationBridge
        _root_.ProofSystem.S21 _root_.ProofLengthMeasure.symbolSize
        _root_.sondowReflectionGraftCode)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hroot : SondowReflectionGraftRootProofLengthConvention)
    (rat : MainSondowRationalParameter)
    (hpayload : _root_.PartialConsistencyPayloadTruth) :
    SondowProjectLocalS21CollapseConclusion := by
  intro _hrat
  rcases
    sondowReflectionGraft_rationalParameter_payloadTruth_explicit_upper_tail_prop
      hs21 compiler hroot rat hpayload with
    ⟨U, hU_poly, htail⟩
  exact
    ⟨U, hU_poly, max compiler.threshold (max 3 rat.q.den), htail⟩

/-- Kernel-specialized q-parametric compatibility theorem for the old
project-local S²₁ collapse surface. -/
theorem sondowProjectLocalS21CollapseConclusion_of_rationalParameter_mainEventualCompiler_rootConvention_kernel
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (kernel : SondowProjectLocalS21Kernel)
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (hroot : SondowReflectionGraftRootProofLengthConvention)
    (rat : MainSondowRationalParameter)
    (hpayload : _root_.PartialConsistencyPayloadTruth) :
    SondowProjectLocalS21CollapseConclusion :=
  sondowProjectLocalS21CollapseConclusion_of_rationalParameter_mainEventualCompiler_rootConvention
    kernel.toReflectionGraftS21ShortVerificationBridge compiler hroot
    rat hpayload

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

theorem verifierAndPayloadSpecCertificate_nonempty_to_projectCollapseConclusion
    (h :
      Nonempty SondowProjectLocalReflectionGraftVerifier ∧
        Nonempty PartialConsistencyPayloadSpecCertificate) :
    SondowProjectLocalS21CollapseConclusion :=
  verifierAndPayloadTruth_nonempty_to_projectCollapseConclusion
    ⟨h.1,
      partialConsistencyPayloadTruth_nonempty_ofPayloadSpecCertificate h.2⟩

theorem SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.toCollapseConclusion
    (h :
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u}) :
    SondowProjectLocalS21CollapseConclusion :=
  h.toDirectTraceCompletion.toCollapseConclusion

theorem sondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate_nonempty_to_projectCollapseConclusion
    (h :
      Nonempty
        SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u}) :
    SondowProjectLocalS21CollapseConclusion := by
  rcases h with ⟨certificate⟩
  exact certificate.toCollapseConclusion

theorem sondowCLineReflectionGraftVerifier_nonempty_of_concreteCheckedCodeCertificate
    (h :
      Nonempty
        SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u}) :
    Nonempty SondowProjectLocalReflectionGraftVerifier := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toVerifier⟩

theorem sondowCLineProjectCollapseConclusion_of_concreteCheckedCodeCertificate
    (h :
      Nonempty
        SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u}) :
    SondowProjectLocalS21CollapseConclusion := by
  rcases h with ⟨certificate⟩
  exact certificate.toCollapseConclusion

theorem sondowCLineCollapseConclusion_of_kernel_checkerExact_splitLength
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    SondowProjectLocalS21CollapseConclusion := by
  rcases hkernel with ⟨kernel⟩
  rcases hchecker with ⟨checker⟩
  rcases hlength with ⟨length⟩
  let hsemantic :
      SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate :=
    SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate.ofCheckerExactSplit
      checker length
  exact
    ({ kernel_certificate := kernel
       length_recognition_certificate := hsemantic } :
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u})
      |>.toCollapseConclusion

/-- Minimal C-line checked-code closure package.  This is the narrowest
project-local bundle currently needed to build the reflection-graft verifier:
the S²₁ kernel cost/absorption certificate, the sidecar checker exactness, and
the split semantic-length recognition certificate. -/
structure SondowCLineMinimalClosureCertificate
    (bounds : BoundedArithmeticLab.SondowComponentBounds) where
  kernel_certificate :
    SondowProjectLocalS21KernelCostAbsorptionCertificate.{u}
  checker_exactness :
    SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
      bounds
  length_recognition :
    SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate

namespace SondowCLineMinimalClosureCertificate

def lengthRecognitionCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : SondowCLineMinimalClosureCertificate.{u} bounds) :
    SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate :=
  SondowReflectionGraftConcreteSemanticLengthRecognitionCertificate.ofCheckerExactSplit
    h.checker_exactness h.length_recognition

def toConcreteCheckedCodeCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : SondowCLineMinimalClosureCertificate.{u} bounds) :
    SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u} where
  kernel_certificate := h.kernel_certificate
  length_recognition_certificate := h.lengthRecognitionCertificate

noncomputable def toVerifier
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : SondowCLineMinimalClosureCertificate.{u} bounds) :
    SondowProjectLocalReflectionGraftVerifier :=
  h.toConcreteCheckedCodeCertificate.toVerifier

theorem payloadTruth
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : SondowCLineMinimalClosureCertificate.{u} bounds) :
    _root_.PartialConsistencyPayloadTruth :=
  h.kernel_certificate.payloadTruth

def payloadSpecCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : SondowCLineMinimalClosureCertificate.{u} bounds) :
    PartialConsistencyPayloadSpecCertificate :=
  h.kernel_certificate.payloadSpecCertificate

noncomputable def toDirectTraceCompletion
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : SondowCLineMinimalClosureCertificate.{u} bounds) :
    SondowProjectLocalDirectTraceCollapseCompletion :=
  h.toConcreteCheckedCodeCertificate.toDirectTraceCompletion

theorem toCollapseConclusion
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : SondowCLineMinimalClosureCertificate.{u} bounds) :
    SondowProjectLocalS21CollapseConclusion :=
  h.toConcreteCheckedCodeCertificate.toCollapseConclusion

end SondowCLineMinimalClosureCertificate

theorem sondowCLineMinimalClosureCertificate_nonempty_iff
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds) ↔
      Nonempty
          SondowProjectLocalS21KernelCostAbsorptionCertificate.{u} ∧
        Nonempty
          (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
            bounds) ∧
          Nonempty
            SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate := by
  constructor
  · intro h
    rcases h with ⟨certificate⟩
    exact
      ⟨⟨certificate.kernel_certificate⟩,
        ⟨⟨certificate.checker_exactness⟩,
          ⟨certificate.length_recognition⟩⟩⟩
  · intro h
    rcases h with ⟨hkernel, hchecker, hlength⟩
    rcases hkernel with ⟨kernel⟩
    rcases hchecker with ⟨checker⟩
    rcases hlength with ⟨length⟩
    exact
      ⟨{ kernel_certificate := kernel
         checker_exactness := checker
         length_recognition := length }⟩

theorem sondowCLineMinimalClosureCertificate_nonempty_iff_rootConvention
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds) ↔
      Nonempty
          SondowProjectLocalS21KernelCostAbsorptionCertificate.{u} ∧
        Nonempty
          (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
            bounds) ∧
          Nonempty SondowReflectionGraftRootProofLengthConvention := by
  constructor
  · intro h
    rcases (sondowCLineMinimalClosureCertificate_nonempty_iff.mp h) with
      ⟨hkernel, hchecker, hlength⟩
    exact
      ⟨hkernel,
        ⟨hchecker,
          sondowReflectionGraftRecognitionSplit_nonempty_iff_rootConvention_nonempty.mp
            hlength⟩⟩
  · intro h
    rcases h with ⟨hkernel, hchecker, hroot⟩
    exact
      sondowCLineMinimalClosureCertificate_nonempty_iff.mpr
        ⟨hkernel,
          ⟨hchecker,
            sondowReflectionGraftRecognitionSplit_nonempty_iff_rootConvention_nonempty.mpr
              hroot⟩⟩

theorem sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds) :=
  sondowCLineMinimalClosureCertificate_nonempty_iff.mpr
    ⟨hkernel, ⟨hchecker, hlength⟩⟩

theorem sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_rootConvention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hroot :
      Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds) :=
  sondowCLineMinimalClosureCertificate_nonempty_iff_rootConvention.mpr
    ⟨hkernel, ⟨hchecker, hroot⟩⟩

theorem sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitRootCalibrations
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hs21 :
      Nonempty SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa :
      Nonempty SondowReflectionGraftRootPAProofLengthCalibration) :
    Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds) :=
  sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_rootConvention
    hkernel hchecker
    (sondowReflectionGraftRootProofLengthConvention_nonempty_iff_splitCalibrations_nonempty.mpr
      ⟨hs21, hpa⟩)

theorem sondowCLineMinimalClosureCertificate_nonempty_of_kernel_systemValid_splitRootCalibrations
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hsystem :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectSystemValidCertificate
          bounds))
    (hs21 :
      Nonempty SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa :
      Nonempty SondowReflectionGraftRootPAProofLengthCalibration) :
    Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds) :=
  sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitRootCalibrations
    hkernel
    (sondowReflectionGraftSidecarProofObjectCheckerExactCertificate_nonempty_iff_systemValidCertificate_nonempty.mpr
      hsystem)
    hs21 hpa

theorem sondowCLineMinimalClosureCertificate_nonempty_of_kernel_proofObjectExists_splitRootCalibrations
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hexists :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectExistsCertificate
          bounds))
    (hs21 :
      Nonempty SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa :
      Nonempty SondowReflectionGraftRootPAProofLengthCalibration) :
    Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds) :=
  sondowCLineMinimalClosureCertificate_nonempty_of_kernel_systemValid_splitRootCalibrations
    hkernel
    (sondowReflectionGraftSidecarProofObjectExistsCertificate_nonempty_iff_systemValidCertificate_nonempty.mp
      hexists)
    hs21 hpa

theorem sondowCLineMinimalClosureCertificate_nonempty_of_kernel_componentProofObjects_splitRootCalibrations
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hcomponents :
      Nonempty
        (SondowReflectionGraftSidecarComponentProofObjectExistsCertificate
          bounds))
    (hs21 :
      Nonempty SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa :
      Nonempty SondowReflectionGraftRootPAProofLengthCalibration) :
    Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds) :=
  sondowCLineMinimalClosureCertificate_nonempty_of_kernel_proofObjectExists_splitRootCalibrations
    hkernel
    (sondowReflectionGraftSidecarComponentProofObjectExistsCertificate_nonempty_iff_proofObjectExistsCertificate_nonempty.mp
      hcomponents)
    hs21 hpa

theorem sondowCLineMinimalClosureCertificate_nonempty_to_concreteCheckedCodeCertificate_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds)) :
    Nonempty
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u} := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toConcreteCheckedCodeCertificate⟩

theorem sondowCLineConcreteCheckedCodeCertificate_nonempty_of_kernel_checkerExact_rootConvention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hroot :
      Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Nonempty
      SondowProjectLocalReflectionGraftVerifierConcreteCheckedCodeCertificate.{u} :=
  sondowCLineMinimalClosureCertificate_nonempty_to_concreteCheckedCodeCertificate_nonempty
    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_rootConvention
      hkernel hchecker hroot)

theorem sondowCLineMinimalClosureCertificate_nonempty_to_verifier_nonempty
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds)) :
    Nonempty SondowProjectLocalReflectionGraftVerifier := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.toVerifier⟩

theorem sondowCLinePayloadSpecCertificate_nonempty_of_minimalClosureCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds)) :
    Nonempty PartialConsistencyPayloadSpecCertificate := by
  rcases h with ⟨certificate⟩
  exact ⟨certificate.payloadSpecCertificate⟩

theorem sondowCLinePayloadTruth_nonempty_of_minimalClosureCertificate
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds)) :
    Nonempty _root_.PartialConsistencyPayloadTruth :=
  partialConsistencyPayloadTruth_nonempty_ofPayloadSpecCertificate
    (sondowCLinePayloadSpecCertificate_nonempty_of_minimalClosureCertificate
      h)

theorem sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds)) :
    SondowProjectLocalS21CollapseConclusion := by
  rcases h with ⟨certificate⟩
  exact certificate.toCollapseConclusion

theorem sondowCLineVerifier_nonempty_of_kernel_checkerExact_rootConvention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hroot :
      Nonempty SondowReflectionGraftRootProofLengthConvention) :
    Nonempty SondowProjectLocalReflectionGraftVerifier :=
  sondowCLineMinimalClosureCertificate_nonempty_to_verifier_nonempty
    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_rootConvention
      hkernel hchecker hroot)

theorem sondowCLineVerifier_nonempty_of_kernel_systemValid_splitRootCalibrations
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hsystem :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectSystemValidCertificate
          bounds))
    (hs21 :
      Nonempty SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa :
      Nonempty SondowReflectionGraftRootPAProofLengthCalibration) :
    Nonempty SondowProjectLocalReflectionGraftVerifier :=
  sondowCLineMinimalClosureCertificate_nonempty_to_verifier_nonempty
    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_systemValid_splitRootCalibrations
      hkernel hsystem hs21 hpa)

theorem sondowCLineVerifier_nonempty_of_kernel_proofObjectExists_splitRootCalibrations
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hexists :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectExistsCertificate
          bounds))
    (hs21 :
      Nonempty SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa :
      Nonempty SondowReflectionGraftRootPAProofLengthCalibration) :
    Nonempty SondowProjectLocalReflectionGraftVerifier :=
  sondowCLineMinimalClosureCertificate_nonempty_to_verifier_nonempty
    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_proofObjectExists_splitRootCalibrations
      hkernel hexists hs21 hpa)

theorem sondowCLineVerifier_nonempty_of_kernel_componentProofObjects_splitRootCalibrations
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hcomponents :
      Nonempty
        (SondowReflectionGraftSidecarComponentProofObjectExistsCertificate
          bounds))
    (hs21 :
      Nonempty SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa :
      Nonempty SondowReflectionGraftRootPAProofLengthCalibration) :
    Nonempty SondowProjectLocalReflectionGraftVerifier :=
  sondowCLineMinimalClosureCertificate_nonempty_to_verifier_nonempty
    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_componentProofObjects_splitRootCalibrations
      hkernel hcomponents hs21 hpa)

theorem sondowCLineCollapseConclusion_of_kernel_checkerExact_rootConvention
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hroot :
      Nonempty SondowReflectionGraftRootProofLengthConvention) :
    SondowProjectLocalS21CollapseConclusion :=
  sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_rootConvention
      hkernel hchecker hroot)

theorem sondowCLineCollapseConclusion_of_kernel_checkerExact_splitRootCalibrations
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hs21 :
      Nonempty SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa :
      Nonempty SondowReflectionGraftRootPAProofLengthCalibration) :
    SondowProjectLocalS21CollapseConclusion :=
  sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitRootCalibrations
      hkernel hchecker hs21 hpa)

theorem sondowCLineCollapseConclusion_of_kernel_systemValid_splitRootCalibrations
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hsystem :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectSystemValidCertificate
          bounds))
    (hs21 :
      Nonempty SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa :
      Nonempty SondowReflectionGraftRootPAProofLengthCalibration) :
    SondowProjectLocalS21CollapseConclusion :=
  sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_systemValid_splitRootCalibrations
      hkernel hsystem hs21 hpa)

theorem sondowCLineCollapseConclusion_of_kernel_proofObjectExists_splitRootCalibrations
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hexists :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectExistsCertificate
          bounds))
    (hs21 :
      Nonempty SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa :
      Nonempty SondowReflectionGraftRootPAProofLengthCalibration) :
    SondowProjectLocalS21CollapseConclusion :=
  sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_proofObjectExists_splitRootCalibrations
      hkernel hexists hs21 hpa)

theorem sondowCLineCollapseConclusion_of_kernel_componentProofObjects_splitRootCalibrations
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (hkernel :
      Nonempty
        SondowProjectLocalS21KernelCostAbsorptionCertificate.{u})
    (hcomponents :
      Nonempty
        (SondowReflectionGraftSidecarComponentProofObjectExistsCertificate
          bounds))
    (hs21 :
      Nonempty SondowReflectionGraftRootS21ProofLengthCalibration)
    (hpa :
      Nonempty SondowReflectionGraftRootPAProofLengthCalibration) :
    SondowProjectLocalS21CollapseConclusion :=
  sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_componentProofObjects_splitRootCalibrations
      hkernel hcomponents hs21 hpa)

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
