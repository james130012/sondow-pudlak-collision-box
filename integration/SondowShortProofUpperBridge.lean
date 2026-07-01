/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowMainCheckedCodeBridge
import integration.SondowProductLogDecompositionPureFrontier

open BoundedArithmeticLab

namespace SondowMainCheckedCodeBridge

/-!
## Short-proof upper-bound bridge audit

This module keeps the final short-proof endpoint honest.  The product/log and
decomposition components now have an unconditional tail S²₁ compiler, but that
is still not definitionally the whole `SondowCollapseVerificationBridgePackage`.
The lemmas below expose exactly what the component compiler contributes to the
main checked certificate, and then separately state the remaining collapse
package needed to obtain PA short proofs.
-/

/-- The atom-free compiler currently available for the product/log/decomposition
part of the full Sondow certificate. -/
abbrev productLogDecompositionShortProofUpperCompiler :
    ProductLogDecompositionTailPureCompiler
      productLogDecompositionTailPureBounds :=
  productLogDecompositionTailPureCompiler

theorem productLogDecompositionShortProofUpperCompiler_threshold_eq_one :
    productLogDecompositionShortProofUpperCompiler.threshold = 1 := by
  rfl

theorem mainSondowSourceComponents_to_productLogDecomposition_sources
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.product n ∧
      ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.logRelation n ∧
      ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.decomposition n := by
  exact
    ⟨hsource.productLogSource,
      hsource.productLogSource,
      hsource.decompositionSource⟩

theorem mainSondowFullCertificateChecks_to_productLogDecomposition_sources
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.product n ∧
      ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.logRelation n ∧
      ProductLogDecompositionSourcePrimitive.eval
        ProductLogDecompositionSourcePrimitive.decomposition n :=
  mainSondowSourceComponents_to_productLogDecomposition_sources
    ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1 hchecked)

theorem mainSondowSourceComponents_to_productLogDecomposition_targets_eval_on_tail
    {q : ℚ} {n : ℕ}
    (hn : productLogDecompositionShortProofUpperCompiler.threshold ≤ n)
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    productLogDecompositionTailTargetsEval
      productLogDecompositionShortProofUpperCompiler n := by
  exact
    (productLogDecompositionShortProofUpperCompiler
      |>.targets_eval_iff_sources_on_tail (n := n) hn).2
      (mainSondowSourceComponents_to_productLogDecomposition_sources
        hsource)

theorem mainSondowFullCertificateChecks_to_productLogDecomposition_targets_eval_on_tail
    {q : ℚ} {n : ℕ}
    (hn : productLogDecompositionShortProofUpperCompiler.threshold ≤ n)
    (hchecked : mainSondowFullCertificateChecks q n) :
    productLogDecompositionTailTargetsEval
      productLogDecompositionShortProofUpperCompiler n :=
  mainSondowSourceComponents_to_productLogDecomposition_targets_eval_on_tail
    hn ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1 hchecked)

theorem mainSondowSourceComponents_to_productLogDecomposition_proofTriple_on_tail
    {q : ℚ} {n : ℕ}
    (hn : productLogDecompositionShortProofUpperCompiler.threshold ≤ n)
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    Nonempty
      (ProductLogDecompositionTailPureCompiler.ProofTriple
        productLogDecompositionShortProofUpperCompiler n) := by
  exact
    ⟨productLogDecompositionShortProofUpperCompiler.proofTriple n hn
      (mainSondowSourceComponents_to_productLogDecomposition_sources
        hsource)⟩

theorem mainSondowFullCertificateChecks_to_productLogDecomposition_proofTriple_on_tail
    {q : ℚ} {n : ℕ}
    (hn : productLogDecompositionShortProofUpperCompiler.threshold ≤ n)
    (hchecked : mainSondowFullCertificateChecks q n) :
    Nonempty
      (ProductLogDecompositionTailPureCompiler.ProofTriple
        productLogDecompositionShortProofUpperCompiler n) :=
  mainSondowSourceComponents_to_productLogDecomposition_proofTriple_on_tail
    hn ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1 hchecked)

/-- Exact audit package for the part of the short-proof upper-bound route now
closed by product/log/decomposition.  It deliberately does not claim to build
`SondowCollapseVerificationBridgePackage`; that global trace/PA embedding bridge
is recorded separately below. -/
structure ProductLogDecompositionShortProofUpperBridgeAudit : Prop where
  threshold_eq_one :
    productLogDecompositionShortProofUpperCompiler.threshold = 1
  target_atomFree :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      productLogDecompositionAtomFree
        (productLogDecompositionShortProofUpperCompiler.target p n)
  formula_code_eq :
    ∀ p : ProductLogDecompositionSourcePrimitive, ∀ n : ℕ,
      productLogDecompositionShortProofUpperCompiler.code
          (productLogDecompositionShortProofUpperCompiler.target p n) =
        ProductLogDecompositionSourcePrimitive.sourceCode p n
  targets_eval_iff_sources_on_tail :
    ∀ n : ℕ,
      productLogDecompositionShortProofUpperCompiler.threshold ≤ n →
        (productLogDecompositionTailTargetsEval
            productLogDecompositionShortProofUpperCompiler n ↔
          ProductLogDecompositionSourcePrimitive.eval
              ProductLogDecompositionSourcePrimitive.product n ∧
            ProductLogDecompositionSourcePrimitive.eval
              ProductLogDecompositionSourcePrimitive.logRelation n ∧
            ProductLogDecompositionSourcePrimitive.eval
              ProductLogDecompositionSourcePrimitive.decomposition n)
  source_components_to_targets_eval_on_tail :
    ∀ {q : ℚ} {n : ℕ},
      productLogDecompositionShortProofUpperCompiler.threshold ≤ n →
        MainSondowFullCertificateSourceComponents q n →
          productLogDecompositionTailTargetsEval
            productLogDecompositionShortProofUpperCompiler n
  full_certificate_to_targets_eval_on_tail :
    ∀ {q : ℚ} {n : ℕ},
      productLogDecompositionShortProofUpperCompiler.threshold ≤ n →
        mainSondowFullCertificateChecks q n →
          productLogDecompositionTailTargetsEval
            productLogDecompositionShortProofUpperCompiler n
  source_components_to_proofTriple_on_tail :
    ∀ {q : ℚ} {n : ℕ},
      productLogDecompositionShortProofUpperCompiler.threshold ≤ n →
        MainSondowFullCertificateSourceComponents q n →
          Nonempty
            (ProductLogDecompositionTailPureCompiler.ProofTriple
              productLogDecompositionShortProofUpperCompiler n)
  full_certificate_to_proofTriple_on_tail :
    ∀ {q : ℚ} {n : ℕ},
      productLogDecompositionShortProofUpperCompiler.threshold ≤ n →
        mainSondowFullCertificateChecks q n →
          Nonempty
            (ProductLogDecompositionTailPureCompiler.ProofTriple
              productLogDecompositionShortProofUpperCompiler n)
  proofTriple_eventually :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty
        (ProductLogDecompositionTailPureCompiler.ProofTriple
          productLogDecompositionShortProofUpperCompiler n)
  upper_bound_from_collapse_bridge :
    ∀ _ : _root_.SondowCollapseVerificationBridgePackage,
      _root_.is_rational _root_.euler_mascheroni →
        ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            _root_.accepted_certificate
                (_root_.sondowReflectionGraftCode n) ∧
              _root_.proof_length _root_.ProofSystem.PA
                  _root_.ProofLengthMeasure.symbolSize
                  (_root_.sondowReflectionGraftCode n) ≤ f n

theorem productLogDecompositionShortProofUpperBridgeAudit :
    ProductLogDecompositionShortProofUpperBridgeAudit where
  threshold_eq_one :=
    productLogDecompositionShortProofUpperCompiler_threshold_eq_one
  target_atomFree :=
    productLogDecompositionShortProofUpperCompiler.target_atomFree
  formula_code_eq :=
    productLogDecompositionShortProofUpperCompiler.formula_code_eq
  targets_eval_iff_sources_on_tail := by
    intro n hn
    exact
      productLogDecompositionShortProofUpperCompiler
        |>.targets_eval_iff_sources_on_tail (n := n) hn
  source_components_to_targets_eval_on_tail := by
    intro q n hn hsource
    exact
      mainSondowSourceComponents_to_productLogDecomposition_targets_eval_on_tail
        hn hsource
  full_certificate_to_targets_eval_on_tail := by
    intro q n hn hchecked
    exact
      mainSondowFullCertificateChecks_to_productLogDecomposition_targets_eval_on_tail
        hn hchecked
  source_components_to_proofTriple_on_tail := by
    intro q n hn hsource
    exact
      mainSondowSourceComponents_to_productLogDecomposition_proofTriple_on_tail
        hn hsource
  full_certificate_to_proofTriple_on_tail := by
    intro q n hn hchecked
    exact
      mainSondowFullCertificateChecks_to_productLogDecomposition_proofTriple_on_tail
        hn hchecked
  proofTriple_eventually :=
    ProductLogDecompositionTailPureCompiler.proofTriple_eventually_of_threshold_one
      productLogDecompositionShortProofUpperCompiler
      productLogDecompositionShortProofUpperCompiler_threshold_eq_one
  upper_bound_from_collapse_bridge := by
    intro hverify hrat
    exact hverify.eventual_short_proofs_of_reproof_rationality hrat

/-- The exact remaining global data needed after the component compiler audit.
This is intentionally stronger than the three component compilers: it contains
the partial-consistency truth payload, the global S²₁ trace package, and the
linear PA embedding. -/
structure SondowShortProofUpperRemainingObligations where
  partial_accepted_truth : _root_.PartialConsistencyAcceptedTruth
  trace_package : _root_.S21VerifierTracePackage
  pa_embedding : _root_.S21ToPALinearEmbedding

def SondowShortProofUpperRemainingObligations.toCollapseVerificationBridgePackage
    (h : SondowShortProofUpperRemainingObligations) :
    _root_.SondowCollapseVerificationBridgePackage where
  partial_accepted_truth := h.partial_accepted_truth
  trace_package := h.trace_package
  pa_embedding := h.pa_embedding

/-- Equivalent exact inputs for the global collapse package, but with the
partial-consistency field stated in the payload-truth form used by the
reflection-graft route.  This does not weaken the package: payload truth and
accepted truth are already equivalent in the main library. -/
structure SondowCollapseVerificationBridgeInputs where
  partial_payload_truth : _root_.PartialConsistencyPayloadTruth
  trace_package : _root_.S21VerifierTracePackage
  pa_embedding : _root_.S21ToPALinearEmbedding

def SondowCollapseVerificationBridgeInputs.toPartialAcceptedTruth
    (h : SondowCollapseVerificationBridgeInputs) :
    _root_.PartialConsistencyAcceptedTruth :=
  h.partial_payload_truth.toAcceptedTruth

def SondowCollapseVerificationBridgeInputs.toRemainingObligations
    (h : SondowCollapseVerificationBridgeInputs) :
    SondowShortProofUpperRemainingObligations where
  partial_accepted_truth := h.toPartialAcceptedTruth
  trace_package := h.trace_package
  pa_embedding := h.pa_embedding

def SondowCollapseVerificationBridgeInputs.toCollapseVerificationBridgePackage
    (h : SondowCollapseVerificationBridgeInputs) :
    _root_.SondowCollapseVerificationBridgePackage :=
  h.toRemainingObligations.toCollapseVerificationBridgePackage

def SondowCollapseVerificationBridgePackage.toBridgeInputs
    (h : _root_.SondowCollapseVerificationBridgePackage) :
    SondowCollapseVerificationBridgeInputs where
  partial_payload_truth := h.partial_accepted_truth.toPayloadTruth
  trace_package := h.trace_package
  pa_embedding := h.pa_embedding

theorem sondowCollapseVerificationBridgePackage_nonempty_iff_inputs_nonempty :
    Nonempty _root_.SondowCollapseVerificationBridgePackage ↔
      Nonempty SondowCollapseVerificationBridgeInputs := by
  constructor
  · intro hpackage
    rcases hpackage with ⟨hpackage⟩
    exact ⟨SondowCollapseVerificationBridgePackage.toBridgeInputs hpackage⟩
  · intro hinputs
    rcases hinputs with ⟨hinputs⟩
    exact ⟨hinputs.toCollapseVerificationBridgePackage⟩

theorem productLogDecompositionShortProofUpperCurrentAudit_eventual_pa_short_proofs_of_bridgeInputs
    (hinputs : SondowCollapseVerificationBridgeInputs)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.accepted_certificate
            (_root_.sondowReflectionGraftCode n) ∧
          _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) ≤ f n :=
  _root_.SondowCollapseVerificationBridgePackage.eventual_short_proofs_of_reproof_rationality
    hinputs.toCollapseVerificationBridgePackage h_rat

/-- A project-scope collapse bridge for the reflection-graft endpoint.  This is
strictly narrower than `SondowCollapseVerificationBridgePackage`: it only needs
trace soundness for the two component families and a PA embedding for the final
reflection-graft family.  The payoff is that it is exactly targeted at the
short-proof upper-bound endpoint used by the reproof route. -/
structure SondowNarrowCollapseVerificationBridgeInputs where
  partial_accepted_truth : _root_.PartialConsistencyAcceptedTruth
  sondow_trace :
    _root_.S21VerifierTraceSoundness _root_.sondowCertificateValidCode
  partial_consistency_trace :
    _root_.S21VerifierTraceSoundness _root_.partialConsistencyCode
  graft_intro : _root_.ReflectionGraftS21ConjunctionIntroduction
  pa_embedding :
    _root_.S21ToPALinearEmbeddingOn _root_.sondowReflectionGraftCode

def SondowNarrowCollapseVerificationBridgeInputs.toPayloadSpec
    (h : SondowNarrowCollapseVerificationBridgeInputs) :
    _root_.PartialConsistencyPayloadSpec :=
  _root_.PartialConsistencyPayloadSpec.ofAcceptedTruth h.partial_accepted_truth

def SondowNarrowCollapseVerificationBridgeInputs.toReflectionGraftPayloadInputs
    (h : SondowNarrowCollapseVerificationBridgeInputs) :
    _root_.ReflectionGraftPayloadInputs :=
  h.toPayloadSpec.toReflectionGraftPayloadInputs

def SondowNarrowCollapseVerificationBridgeInputs.toTraceComposition
    (h : SondowNarrowCollapseVerificationBridgeInputs) :
    _root_.ReflectionGraftS21TraceComposition :=
  h.graft_intro.toTraceComposition h.sondow_trace
    h.partial_consistency_trace

def SondowNarrowCollapseVerificationBridgeInputs.toReflectionGraftTraceInputs
    (h : SondowNarrowCollapseVerificationBridgeInputs) :
    _root_.ReflectionGraftTraceInputs where
  trace_soundness := h.toTraceComposition.toTraceSoundness
  pa_embedding := h.pa_embedding

def SondowNarrowCollapseVerificationBridgeInputs.toReflectionGraftCollapsePackage
    (h : SondowNarrowCollapseVerificationBridgeInputs) :
    _root_.ReflectionGraftCollapsePackage :=
  h.toReflectionGraftTraceInputs.toCollapsePackage
    _root_.SondowForwardInputs.of_reproof
    h.toReflectionGraftPayloadInputs

def SondowNarrowCollapseVerificationBridgeInputs.toReflectionGraftCollapseInputs
    (h : SondowNarrowCollapseVerificationBridgeInputs) :
    _root_.EventualCertificateCollapseInputs
      _root_.sondowReflectionGraftCode :=
  h.toReflectionGraftCollapsePackage.toEventualCertificateCollapseInputs

theorem SondowNarrowCollapseVerificationBridgeInputs.eventual_pa_short_proofs_of_reproof_rationality
    (h : SondowNarrowCollapseVerificationBridgeInputs)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.accepted_certificate
            (_root_.sondowReflectionGraftCode n) ∧
          _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) ≤ f n :=
  h.toReflectionGraftTraceInputs.eventual_short_proofs_of_rationality
    _root_.SondowForwardInputs.of_reproof
    h.toReflectionGraftPayloadInputs
    h_rat

def SondowNarrowCollapseVerificationBridgeInputs.ofGlobalBridgeInputsAndGraftIntro
    (hglobal : SondowCollapseVerificationBridgeInputs)
    (hgraft : _root_.ReflectionGraftS21ConjunctionIntroduction) :
    SondowNarrowCollapseVerificationBridgeInputs where
  partial_accepted_truth := hglobal.toPartialAcceptedTruth
  sondow_trace :=
    hglobal.trace_package.trace_soundness
      _root_.sondowCertificateValidCode
      _root_.fixed_verifier_encoding_sondowCertificateValidCode
  partial_consistency_trace :=
    hglobal.trace_package.trace_soundness
      _root_.partialConsistencyCode
      _root_.fixed_verifier_encoding_partialConsistencyCode
  graft_intro := hgraft
  pa_embedding := hglobal.pa_embedding.on _root_.sondowReflectionGraftCode

theorem narrowCollapseBridge_of_globalBridgeInputs_eventual_pa_short_proofs
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
  (SondowNarrowCollapseVerificationBridgeInputs.ofGlobalBridgeInputsAndGraftIntro
    hglobal hgraft)
    |>.eventual_pa_short_proofs_of_reproof_rationality h_rat

/-- Once the component audit and the remaining global verification obligations
are both supplied, the existing reproof endpoint yields the PA short-proof upper
bound. -/
theorem productLogDecompositionShortProofUpperAudit_eventual_pa_short_proofs
    (haudit : ProductLogDecompositionShortProofUpperBridgeAudit)
    (hremaining : SondowShortProofUpperRemainingObligations)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.accepted_certificate
            (_root_.sondowReflectionGraftCode n) ∧
          _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) ≤ f n :=
  haudit.upper_bound_from_collapse_bridge
    hremaining.toCollapseVerificationBridgePackage h_rat

theorem productLogDecompositionShortProofUpperCurrentAudit_eventual_pa_short_proofs
    (hremaining : SondowShortProofUpperRemainingObligations)
    (h_rat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ f : ℕ → ℝ, _root_.is_polynomial_bound f ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        _root_.accepted_certificate
            (_root_.sondowReflectionGraftCode n) ∧
          _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (_root_.sondowReflectionGraftCode n) ≤ f n :=
  productLogDecompositionShortProofUpperAudit_eventual_pa_short_proofs
    productLogDecompositionShortProofUpperBridgeAudit hremaining h_rat

end SondowMainCheckedCodeBridge
