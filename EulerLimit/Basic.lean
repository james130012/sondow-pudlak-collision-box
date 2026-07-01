/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.HilbertPudlakRoutes
import EulerLimit.LCMExternal
/-!
# Gödel-Sondow Coupling Hypothesis Formalization
This module formalizes the Euler-Mascheroni constant limit definition,
proof-complexity and projection-bridge layers.
-/

open Filter MiniHilbert

universe u v w

def GammaIrrationalityFormulaCodeRealizationInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityFormulaCodeRealizationInputs Ax A B halign) :
    GammaIrrationalityMainInputs where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_soundness := h.hilbert_formula_code_realization.toBridge

noncomputable def GammaIrrationalityStandardFormulaCodeSemanticsInputs.toExactProjectionInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign) :
    GammaIrrationalityExactProjectionInputs where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_alignment := halign
  hilbert_exact_projection :=
    h.proof_length_semantics.toExactProjectionRealization

noncomputable def GammaIrrationalityStandardFormulaCodeSemanticsInputs.toTargetExactProjectionInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign) :
    GammaIrrationalityTargetExactProjectionInputs where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_alignment := halign
  hilbert_target_exact_projection :=
    h.proof_length_semantics.toTargetExactProjectionRealization

noncomputable def GammaIrrationalityStandardFormulaCodeSemanticsInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign) :
    GammaIrrationalityMainInputs :=
  h.toExactProjectionInputs.toMainInputs

noncomputable def
    GammaIrrationalityPAHilbertFamilyExactnessInputs.toStandardFormulaCodeSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertFamilyExactnessInputs Ax A B halign) :
    GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_semantics :=
    h.proof_length_family_exactness.toStandardFormulaCodeProofLengthSemantics

noncomputable def GammaIrrationalityPAHilbertFamilyExactnessInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertFamilyExactnessInputs Ax A B halign) :
    GammaIrrationalityMainInputs where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_soundness := h.proof_length_family_exactness.toBridge

noncomputable def
    GammaIrrationalityStandardSemanticsLowerBoundInputs.toFamilyExactnessInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardSemanticsLowerBoundInputs Ax A B halign) :
    GammaIrrationalityPAHilbertFamilyExactnessSemanticLowerBoundInputs
      Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_family_exactness :=
    MiniHilbert.PAHilbertProjectionFamilyExactness.ofStandardFormulaCodeProofLengthSemantics
      h.proof_length_semantics
  semantic_partial_lower_bound := h.semantic_partial_lower_bound

noncomputable def GammaIrrationalityStandardSemanticsLowerBoundInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardSemanticsLowerBoundInputs Ax A B halign) :
    GammaIrrationalityMainInputs where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_soundness := by
    exact
      (MiniHilbert.PAHilbertProjectionFamilyExactness.ofStandardFormulaCodeProofLengthSemantics
        h.proof_length_semantics).toBridge

noncomputable def GammaIrrationalityPAHilbertRecognitionInputs.toFamilyExactnessInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertRecognitionInputs Ax A B halign) :
    GammaIrrationalityPAHilbertFamilyExactnessInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_family_exactness := h.proof_length_recognition.toFamilyExactness

noncomputable def GammaIrrationalityPAHilbertRecognitionInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertRecognitionInputs Ax A B halign) :
    GammaIrrationalityMainInputs where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_soundness := h.proof_length_recognition.toBridge

noncomputable def GammaIrrationalityPAHilbertVerifierProjectLengthInputs.toRecognitionInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertVerifierProjectLengthInputs Ax A B halign) :
    GammaIrrationalityPAHilbertRecognitionInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_recognition := by
    exact
      (FormulaCodeHilbertInterpretation.projectCheckedRecognition_iff_localProofCodeProjectLength
        h.formula_code_interpretation h.fallback_length).2
        h.proof_length_eq_verifierProjectLength

noncomputable def GammaIrrationalityPAHilbertVerifierProjectLengthInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertVerifierProjectLengthInputs Ax A B halign) :
    GammaIrrationalityMainInputs :=
  h.toRecognitionInputs.toMainInputs

noncomputable def
    GammaIrrationalityPAHilbertSemanticLowerBoundInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertSemanticLowerBoundInputs Ax A B halign) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  eventual_reflection_graft_inputs_of_collapse_package
    (reflection_graft_collapse_package_of_forward_inputs_and_concrete_verification
      h.sondow_forward
      (reflection_graft_payload_inputs_of_partial_consistency_truth
        h.partial_payload_truth)
      h.concrete_verification)
    (h.proof_length_recognition.toReflectionGraftEventualLowerBound
      h.semantic_partial_lower_bound)

noncomputable def GammaIrrationalityPAHilbertSemanticLowerBoundInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertSemanticLowerBoundInputs Ax A B halign) :
    GammaIrrationalityMainInputs where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_soundness := h.proof_length_recognition.toBridge

noncomputable def GammaIrrationalityPureSemanticLowerBoundInputs.toSemanticGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPureSemanticLowerBoundInputs Ax A B halign) :
    EventualSemanticReflectionGraftModelInputs
      h.formula_code_interpretation.localCheckedCodeProofLength
      sondowReflectionGraftCode where
  certificate_collapse :=
    (reflection_graft_collapse_package_of_forward_inputs_and_concrete_verification
      h.sondow_forward
      (reflection_graft_payload_inputs_of_partial_consistency_truth
        h.partial_payload_truth)
      h.concrete_verification).toEventualCertificateCollapseInputs
  short_verification := h.semantic_short_verification
  graft_lower_bound := by
    exact
      (h.formula_code_interpretation
        |>.semanticReflectionGraftEventualLowerBound_of_localCheckedSource
          h.semantic_partial_lower_bound).toEventualSemanticLowerBound

def GammaIrrationalityPolynomialProofFamilySemanticInputs.toPureSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPolynomialProofFamilySemanticInputs Ax A B halign) :
    GammaIrrationalityPureSemanticLowerBoundInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  formula_code_interpretation := h.formula_code_interpretation
  semantic_short_verification := {
    verifier_polytime := certificate_verifier_polytime_sondowReflectionGraftCode
    short_proofs_of_accepted_certificates := by
      refine ⟨MiniHilbert.nat_bound_as_real
        h.formula_code_interpretation.target_proof_family.length,
        h.target_proof_family_length_polynomial, ?_⟩
      intro m _haccepted
      have hchecked :
          h.formula_code_interpretation.localCheckedCodeProofLength
              (sondowReflectionGraftCode m) =
            h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m :=
        h.formula_code_interpretation.localCheckedCodeProofLength_reflectionGraft m
      have hmin :
          h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m ≤
            h.formula_code_interpretation.target_proof_family.length m := by
        rw [ConcreteProofFamily.minCheckedCodeSize_eq_minLength]
        exact h.formula_code_interpretation.target_proof_family.minLength_le_length m
      rw [hchecked]
      change
        (h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m : ℝ) ≤
          (h.formula_code_interpretation.target_proof_family.length m : ℝ)
      exact_mod_cast hmin }
  semantic_partial_lower_bound := h.semantic_partial_lower_bound

def GammaIrrationalityConcreteShortProofSemanticInputs.toPureSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityConcreteShortProofSemanticInputs Ax A B halign) :
    GammaIrrationalityPureSemanticLowerBoundInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  formula_code_interpretation := h.formula_code_interpretation
  semantic_short_verification := {
    verifier_polytime := certificate_verifier_polytime_sondowReflectionGraftCode
    short_proofs_of_accepted_certificates := by
      refine ⟨MiniHilbert.nat_bound_as_real h.target_short_proofs.bound,
        h.target_short_proofs.bound_polynomial, ?_⟩
      intro m _haccepted
      have hchecked :
          h.formula_code_interpretation.localCheckedCodeProofLength
              (sondowReflectionGraftCode m) =
            h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m :=
        h.formula_code_interpretation.localCheckedCodeProofLength_reflectionGraft m
      have hmin :
          h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m ≤
            h.target_short_proofs.bound m := by
        rw [ConcreteProofFamily.minCheckedCodeSize]
        exact h.target_short_proofs.short_proofs.minCheckedCodeSize_le_bound
          (fun m => h.formula_code_interpretation.target_proof_family.provable m)
          m True.intro
      rw [hchecked]
      change
        (h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m : ℝ) ≤
          (h.target_short_proofs.bound m : ℝ)
      exact_mod_cast hmin }
  semantic_partial_lower_bound := h.semantic_partial_lower_bound

def GammaIrrationalityConcreteShortProofSourceLowerBoundInputs.toConcreteShortProofSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityConcreteShortProofSourceLowerBoundInputs Ax A B halign) :
    GammaIrrationalityConcreteShortProofSemanticInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  semantic_partial_lower_bound :=
    h.formula_code_interpretation.localCheckedPartialConsistencyLowerBound_of_sourceLength
      h.source_minChecked_lower_bound

def GammaIrrationalityConcreteShortProofSourceLowerBoundInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityConcreteShortProofSourceLowerBoundInputs Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_lower_bound := h.source_minChecked_lower_bound

noncomputable def GammaIrrationalityConcreteShortProofSourceCoreInputs.toSemanticGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityConcreteShortProofSourceCoreInputs Ax A B halign) :
    EventualSemanticReflectionGraftModelInputs
      h.formula_code_interpretation.localCheckedCodeProofLength
      sondowReflectionGraftCode where
  certificate_collapse :=
    (reflection_graft_collapse_package_of_forward_inputs_and_concrete_verification
      h.sondow_forward
      (reflection_graft_payload_inputs_of_partial_consistency_truth
        h.partial_payload_truth)
      h.concrete_verification).toEventualCertificateCollapseInputs
  short_verification := {
    verifier_polytime := certificate_verifier_polytime_sondowReflectionGraftCode
    short_proofs_of_accepted_certificates := by
      refine ⟨MiniHilbert.nat_bound_as_real h.target_short_proofs.bound,
        h.target_short_proofs.bound_polynomial, ?_⟩
      intro m _haccepted
      have hchecked :
          h.formula_code_interpretation.localCheckedCodeProofLength
              (sondowReflectionGraftCode m) =
            h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m :=
        h.formula_code_interpretation.localCheckedCodeProofLength_reflectionGraft m
      have hmin :
          h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m ≤
            h.target_short_proofs.bound m := by
        rw [ConcreteProofFamily.minCheckedCodeSize]
        exact h.target_short_proofs.short_proofs.minCheckedCodeSize_le_bound
          (fun m => h.formula_code_interpretation.target_proof_family.provable m)
          m True.intro
      rw [hchecked]
      change
        (h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m : ℝ) ≤
          (h.target_short_proofs.bound m : ℝ)
      exact_mod_cast hmin }
  graft_lower_bound := by
    exact
      (h.formula_code_interpretation
        |>.semanticReflectionGraftEventualLowerBound_of_localCheckedSource
          (h.formula_code_interpretation
            |>.localCheckedPartialConsistencyLowerBound_of_sourceLength
              h.source_minChecked_lower_bound)).toEventualSemanticLowerBound

def GammaIrrationalityConcreteShortProofSourceLowerBoundInputs.toPureSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityConcreteShortProofSourceLowerBoundInputs Ax A B halign) :
    GammaIrrationalityPureSemanticLowerBoundInputs Ax A B halign :=
  h.toConcreteShortProofSemanticInputs.toPureSemanticInputs

noncomputable def GammaIrrationalityConcreteShortProofSourceLowerBoundInputs.toSemanticGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityConcreteShortProofSourceLowerBoundInputs Ax A B halign) :
    EventualSemanticReflectionGraftModelInputs
      h.formula_code_interpretation.localCheckedCodeProofLength
      sondowReflectionGraftCode :=
  h.toCoreInputs.toSemanticGraftInputs

def GammaIrrationalityBussPudlakProofCodeModelSemanticInputs.toProofCodeModelSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeModelSemanticInputs Ax A B halign) :
    GammaIrrationalityProofCodeModelSemanticInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  formula_code_interpretation := h.formula_code_interpretation
  fallback_length := h.fallback_length
  target_short_proofs := h.target_short_proofs
  semantic_partial_lower_bound :=
    h.source_minChecked_lower_bound.toFormulaCodeLowerBound
      (length :=
        h.formula_code_interpretation.localHilbertSemanticProofLength
          h.fallback_length)
      (φ := partialConsistencyCode)
      (by
        intro m
        exact h.formula_code_interpretation
          |>.localHilbertSemanticProofLength_partialConsistency
            h.fallback_length m)

def
    GammaIrrationalityBussPudlakRescaledMinCheckedSourceInputs.sourceMinCheckedLowerBound
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedSourceInputs Ax A B halign) :
    SemanticStrongNatLowerBound
      h.formula_code_interpretation.target_proof_family.rightConjElim.minCheckedCodeSize :=
  SemanticStrongNatLowerBound.of_polynomial_cofinal_rescaling
    h.scale_properties h.rescaled_source_minChecked_lower_bound

def
    GammaIrrationalityBussPudlakRescaledMinCheckedSourceInputs.toSourceLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedSourceInputs Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceLowerBoundInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_lower_bound := h.sourceMinCheckedLowerBound

def
    GammaIrrationalityBussPudlakRescaledMinCheckedSourceInputs.toPureSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedSourceInputs Ax A B halign) :
    GammaIrrationalityPureSemanticLowerBoundInputs Ax A B halign :=
  h.toSourceLowerBoundInputs.toPureSemanticInputs

def
    GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs.sourceMinCheckedLowerBound
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs Ax A B halign) :
    SemanticStrongNatLowerBound
      h.formula_code_interpretation.target_proof_family.rightConjElim.minCheckedCodeSize :=
  SemanticStrongNatLowerBound.of_polynomial_cofinal_rescaling
    h.scale_properties h.rescaled_source_minChecked_lower_bound

def
    GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs.toSourceCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_lower_bound := h.sourceMinCheckedLowerBound

noncomputable def
    GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs.toSemanticGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs Ax A B halign) :
    EventualSemanticReflectionGraftModelInputs
      h.formula_code_interpretation.localCheckedCodeProofLength
      sondowReflectionGraftCode :=
  h.toSourceCoreInputs.toSemanticGraftInputs

def
    GammaIrrationalityBussPudlakRescaledMinCheckedSourceInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedSourceInputs Ax A B halign) :
    GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  scale := h.scale
  scale_properties := h.scale_properties
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  rescaled_source_minChecked_lower_bound := h.rescaled_source_minChecked_lower_bound

def
    GammaIrrationalityBussPudlakRescaledMinCheckedModelInputs.toSourceInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedModelInputs Ax A B halign) :
    GammaIrrationalityBussPudlakRescaledMinCheckedSourceInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  scale := h.scale
  scale_properties := h.scale_properties
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  rescaled_source_minChecked_lower_bound := h.rescaled_source_minChecked_lower_bound

def
    GammaIrrationalityBussPudlakRescaledMinCheckedModelInputs.sourceMinCheckedLowerBound
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedModelInputs Ax A B halign) :
    SemanticStrongNatLowerBound
      h.formula_code_interpretation.target_proof_family.rightConjElim.minCheckedCodeSize :=
  h.toSourceInputs.sourceMinCheckedLowerBound

def
    GammaIrrationalityBussPudlakRescaledMinCheckedModelInputs.toSourceLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedModelInputs Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceLowerBoundInputs Ax A B halign :=
  h.toSourceInputs.toSourceLowerBoundInputs

def
    GammaIrrationalityBussPudlakRescaledMinCheckedModelInputs.toPureSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedModelInputs Ax A B halign) :
    GammaIrrationalityPureSemanticLowerBoundInputs Ax A B halign :=
  h.toSourceInputs.toPureSemanticInputs

def
    GammaIrrationalityBussPudlakRescaledMinCheckedModelInputs.toProofCodeModelSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedModelInputs Ax A B halign) :
    GammaIrrationalityProofCodeModelSemanticInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  formula_code_interpretation := h.formula_code_interpretation
  fallback_length := h.fallback_length
  target_short_proofs := h.target_short_proofs
  semantic_partial_lower_bound :=
    h.sourceMinCheckedLowerBound
      |>.toFormulaCodeLowerBound
        (length :=
          h.formula_code_interpretation.localHilbertSemanticProofLength
            h.fallback_length)
        (φ := partialConsistencyCode)
        (by
          intro m
          exact h.formula_code_interpretation
            |>.localHilbertSemanticProofLength_partialConsistency
              h.fallback_length m)

def
    GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs.toProofCodeModelSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakProofCodeModelSemanticInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  fallback_length := h.fallback_length
  target_short_proofs := h.target_short_proofs
  source_minChecked_lower_bound :=
    ((MiniHilbert.PAHilbertProjectionFamilyExactness.ofLocalPAHilbertCodeCalibration
      h.fallback_length h.proof_code_calibration)
      |>.toPartialConsistencySourceMinCheckedCalibration)
      |>.semanticStrongNatLowerBound_of_rescaling h.buss_pudlak_rescaling

def
    GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs.toSourceCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakSourceCalibratedInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_calibration :=
    (MiniHilbert.PAHilbertProjectionFamilyExactness.ofLocalPAHilbertCodeCalibration
      h.fallback_length h.proof_code_calibration)
      |>.toPartialConsistencySourceMinCheckedCalibration

noncomputable def GammaIrrationalityProofCodeModelSemanticInputs.toSemanticGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProofCodeModelSemanticInputs Ax A B halign) :
    EventualSemanticReflectionGraftModelInputs
      (h.formula_code_interpretation.localHilbertSemanticProofLength
        h.fallback_length)
      sondowReflectionGraftCode where
  certificate_collapse :=
    (reflection_graft_collapse_package_of_forward_inputs_and_concrete_verification
      h.sondow_forward
      (reflection_graft_payload_inputs_of_partial_consistency_truth
        h.partial_payload_truth)
      h.concrete_verification).toEventualCertificateCollapseInputs
  short_verification := {
    verifier_polytime := certificate_verifier_polytime_sondowReflectionGraftCode
    short_proofs_of_accepted_certificates := by
      refine ⟨MiniHilbert.nat_bound_as_real h.target_short_proofs.bound,
        h.target_short_proofs.bound_polynomial, ?_⟩
      intro m _haccepted
      have hchecked :
          h.formula_code_interpretation.localHilbertSemanticProofLength
              h.fallback_length (sondowReflectionGraftCode m) =
            h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m :=
        h.formula_code_interpretation.localHilbertSemanticProofLength_reflectionGraft
          h.fallback_length m
      have hmin :
          h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m ≤
            h.target_short_proofs.bound m := by
        rw [ConcreteProofFamily.minCheckedCodeSize]
        exact h.target_short_proofs.short_proofs.minCheckedCodeSize_le_bound
          (fun m => h.formula_code_interpretation.target_proof_family.provable m)
          m True.intro
      rw [hchecked]
      change
        (h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m : ℝ) ≤
          (h.target_short_proofs.bound m : ℝ)
      exact_mod_cast hmin }
  graft_lower_bound :=
    ((h.semantic_partial_lower_bound.transfer
      ((h.formula_code_interpretation
        |>.semanticBridge_of_localHilbertSemanticProofLength h.fallback_length)
        |>.toSemanticConstantProjection
        |>.toSemanticStrongLowerBoundTransfer))
      |>.toEventualSemanticLowerBound)

def
    GammaIrrationalityBussPudlakSourceCalibratedInputs.toConcreteShortProofSourceLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakSourceCalibratedInputs Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceLowerBoundInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_lower_bound :=
    h.source_minChecked_calibration.semanticStrongNatLowerBound_of_rescaling
      h.buss_pudlak_rescaling

def GammaIrrationalityBussPudlakSourceCalibratedCoreInputs.toConcreteSourceCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakSourceCalibratedCoreInputs Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_lower_bound :=
    h.source_minChecked_calibration.semanticStrongNatLowerBound_of_rescaling
      h.buss_pudlak_rescaling

def GammaIrrationalityBussPudlakSourceCalibratedCoreInputs.sourceMinCheckedLowerBound
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakSourceCalibratedCoreInputs Ax A B halign) :
    SemanticStrongNatLowerBound
      h.formula_code_interpretation.target_proof_family.rightConjElim.minCheckedCodeSize :=
  h.source_minChecked_calibration.semanticStrongNatLowerBound_of_rescaling
    h.buss_pudlak_rescaling

def GammaIrrationalityBussPudlakSourceCalibratedCoreInputs.rescaledSourceMinCheckedLowerBound
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakSourceCalibratedCoreInputs Ax A B halign) :
    SemanticStrongNatLowerBound
      (fun k : ℕ =>
        h.formula_code_interpretation.target_proof_family.rightConjElim.minCheckedCodeSize
          (h.buss_pudlak_rescaling.scale k)) where
  frequently_beats_every_polynomial := by
    intro f hf
    exact
      (h.buss_pudlak_rescaling.rescaled_strong_lower_bound
        |>.frequently_beats_every_polynomial f hf).mono fun k hk => by
          simpa [rescaledPartialConsistencyCode,
            h.source_minChecked_calibration.proof_length_eq_source_minChecked
              (h.buss_pudlak_rescaling.scale k)] using hk

def GammaIrrationalityBussPudlakSourceCalibratedCoreInputs.toRescaledMinCheckedCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakSourceCalibratedCoreInputs Ax A B halign) :
    GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  scale := h.buss_pudlak_rescaling.scale
  scale_properties := h.buss_pudlak_rescaling.scale_properties
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  rescaled_source_minChecked_lower_bound := h.rescaledSourceMinCheckedLowerBound

def GammaIrrationalityBussPudlakSourceCalibratedCoreInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakSourceCalibratedCoreInputs Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_lower_bound := h.sourceMinCheckedLowerBound

def GammaIrrationalityBussPudlakSourceCalibratedInputs.toCoreCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakSourceCalibratedInputs Ax A B halign) :
    GammaIrrationalityBussPudlakSourceCalibratedCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_calibration := h.source_minChecked_calibration

def GammaIrrationalityBussPudlakSourceCalibratedInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakSourceCalibratedInputs Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceCoreInputs Ax A B halign :=
  h.toCoreCalibratedInputs.toCoreInputs

def GammaIrrationalityBussPudlakSourceCalibratedInputs.toPureSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakSourceCalibratedInputs Ax A B halign) :
    GammaIrrationalityPureSemanticLowerBoundInputs Ax A B halign :=
  h.toConcreteShortProofSourceLowerBoundInputs.toPureSemanticInputs

def GammaIrrationalityBussPudlakFamilyExactConcreteInputs.toSourceCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakFamilyExactConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakSourceCalibratedInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_calibration :=
    h.proof_length_family_exactness.toPartialConsistencySourceMinCheckedCalibration

def GammaIrrationalityBussPudlakFamilyExactConcreteInputs.toPureSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakFamilyExactConcreteInputs Ax A B halign) :
    GammaIrrationalityPureSemanticLowerBoundInputs Ax A B halign :=
  h.toSourceCalibratedInputs.toPureSemanticInputs

def GammaIrrationalityBussPudlakFamilyExactConcreteInputs.toCoreCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakFamilyExactConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakSourceCalibratedCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_calibration :=
    h.proof_length_family_exactness.toPartialConsistencySourceMinCheckedCalibration

def GammaIrrationalityBussPudlakFamilyExactConcreteInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakFamilyExactConcreteInputs Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceCoreInputs Ax A B halign :=
  h.toCoreCalibratedInputs.toCoreInputs

def GammaIrrationalityBussPudlakFamilyExactConcreteInputs.toRescaledMinCheckedCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakFamilyExactConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs Ax A B halign :=
  h.toCoreCalibratedInputs.toRescaledMinCheckedCoreInputs

def GammaIrrationalityBussPudlakRecognitionConcreteInputs.toFamilyExactConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRecognitionConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakFamilyExactConcreteInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  proof_length_family_exactness := h.proof_length_recognition.toFamilyExactness

def GammaIrrationalityBussPudlakRecognitionConcreteInputs.toSourceCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRecognitionConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakSourceCalibratedInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_calibration :=
    h.proof_length_recognition.toPartialConsistencySourceMinCheckedCalibration

def GammaIrrationalityBussPudlakRecognitionConcreteInputs.toPureSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRecognitionConcreteInputs Ax A B halign) :
    GammaIrrationalityPureSemanticLowerBoundInputs Ax A B halign :=
  h.toSourceCalibratedInputs.toPureSemanticInputs

def GammaIrrationalityBussPudlakRecognitionConcreteInputs.toCoreCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRecognitionConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakSourceCalibratedCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_calibration :=
    h.proof_length_recognition.toPartialConsistencySourceMinCheckedCalibration

def GammaIrrationalityBussPudlakRecognitionConcreteInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRecognitionConcreteInputs Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceCoreInputs Ax A B halign :=
  h.toCoreCalibratedInputs.toCoreInputs

def GammaIrrationalityBussPudlakRecognitionConcreteInputs.toRescaledMinCheckedCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRecognitionConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs Ax A B halign :=
  h.toCoreCalibratedInputs.toRescaledMinCheckedCoreInputs

def GammaIrrationalityBussPudlakCheckerConcreteInputs.toRecognitionConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakCheckerConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakRecognitionConcreteInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  proof_length_recognition :=
    h.proof_code_checker_recognition.toProjectCheckedRecognition

def GammaIrrationalityBussPudlakCheckerConcreteInputs.toSourceCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakCheckerConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakSourceCalibratedInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_calibration :=
    h.proof_code_checker_recognition.toProjectCheckedRecognition
      |>.toPartialConsistencySourceMinCheckedCalibration

def GammaIrrationalityBussPudlakCheckerConcreteInputs.toPureSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakCheckerConcreteInputs Ax A B halign) :
    GammaIrrationalityPureSemanticLowerBoundInputs Ax A B halign :=
  h.toSourceCalibratedInputs.toPureSemanticInputs

def GammaIrrationalityBussPudlakCheckerConcreteInputs.toCoreCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakCheckerConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakSourceCalibratedCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_calibration :=
    h.proof_code_checker_recognition.toProjectCheckedRecognition
      |>.toPartialConsistencySourceMinCheckedCalibration

def GammaIrrationalityBussPudlakCheckerConcreteInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakCheckerConcreteInputs Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceCoreInputs Ax A B halign :=
  h.toCoreCalibratedInputs.toCoreInputs

def GammaIrrationalityBussPudlakCheckerConcreteInputs.toRescaledMinCheckedCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakCheckerConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs Ax A B halign :=
  h.toCoreCalibratedInputs.toRescaledMinCheckedCoreInputs

def GammaIrrationalityBussPudlakProofObjectConcreteInputs.toRecognitionConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofObjectConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakRecognitionConcreteInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  proof_length_recognition :=
    MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition.ofProjectProofLengthSemantics
      (h.formula_code_interpretation
        |>.projectCheckedCodeSemantics_of_localHilbertProofCodeSemantics
          h.proof_length_eq_minProofCodeSize)

def GammaIrrationalityBussPudlakProofObjectConcreteInputs.toSourceCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofObjectConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakSourceCalibratedInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_calibration :=
    (MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition.ofProjectProofLengthSemantics
      (h.formula_code_interpretation
        |>.projectCheckedCodeSemantics_of_localHilbertProofCodeSemantics
          h.proof_length_eq_minProofCodeSize))
      |>.toPartialConsistencySourceMinCheckedCalibration

def GammaIrrationalityBussPudlakProofObjectConcreteInputs.toPureSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofObjectConcreteInputs Ax A B halign) :
    GammaIrrationalityPureSemanticLowerBoundInputs Ax A B halign :=
  h.toSourceCalibratedInputs.toPureSemanticInputs

def GammaIrrationalityBussPudlakProofObjectConcreteInputs.toCoreCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofObjectConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakSourceCalibratedCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_calibration :=
    (MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition.ofProjectProofLengthSemantics
      (h.formula_code_interpretation
        |>.projectCheckedCodeSemantics_of_localHilbertProofCodeSemantics
          h.proof_length_eq_minProofCodeSize))
      |>.toPartialConsistencySourceMinCheckedCalibration

def GammaIrrationalityBussPudlakProofObjectConcreteInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofObjectConcreteInputs Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceCoreInputs Ax A B halign :=
  h.toCoreCalibratedInputs.toCoreInputs

def GammaIrrationalityBussPudlakProofObjectConcreteInputs.toRescaledMinCheckedCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofObjectConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs Ax A B halign :=
  h.toCoreCalibratedInputs.toRescaledMinCheckedCoreInputs

def
    GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs.toProofObjectConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs Ax A B halign) :
    GammaIrrationalityBussPudlakProofObjectConcreteInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  proof_length_eq_minProofCodeSize := by
    intro code hcode
    rw [h.proof_code_calibration.proof_length_eq_length code hcode]
    exact_mod_cast
      ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize
        h.formula_code_interpretation.localHilbertProofCodeSemantics
        h.fallback_length hcode

def GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs.toPureSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs Ax A B halign) :
    GammaIrrationalityPureSemanticLowerBoundInputs Ax A B halign :=
  h.toSourceCalibratedInputs.toPureSemanticInputs

def MiniHilbert.FormulaCodeHilbertLocalCalibration.toProofLengthCodeCalibration
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (hcal : MiniHilbert.FormulaCodeHilbertLocalCalibration interp)
    (fallback_length : FormulaCode → ℕ) :
    (interp.localHilbertProofLengthCodeSemantics fallback_length).Calibration where
  proof_length_eq_length := by
    intro code hcode
    rw [hcal.to_localHilbertProofCodeSemantics code hcode]
    exact_mod_cast
      (ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize
        interp.localHilbertProofCodeSemantics fallback_length hcode).symm

def GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs.toCoreCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs
      Ax A B halign) :
    GammaIrrationalityBussPudlakSourceCalibratedCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  source_minChecked_calibration :=
    (MiniHilbert.PAHilbertProjectionFamilyExactness.ofLocalPAHilbertCodeCalibration
      h.fallback_length h.proof_code_calibration)
      |>.toPartialConsistencySourceMinCheckedCalibration

def GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs
      Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceCoreInputs Ax A B halign :=
  h.toCoreCalibratedInputs.toCoreInputs

def
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs.toRescaledMinCheckedCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs
      Ax A B halign) :
    GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs Ax A B halign :=
  h.toCoreCalibratedInputs.toRescaledMinCheckedCoreInputs

def GammaIrrationalityBussPudlakProofCodeCalibrationSpecCoreInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationSpecCoreInputs
      Ax A B halign) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs
      Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_spec.toPayloadTruth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  fallback_length := h.fallback_length
  proof_code_calibration := h.proof_code_calibration

def
    GammaIrrationalityBussPudlakProofCodeCalibrationSpecCoreInputs.toRescaledMinCheckedCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationSpecCoreInputs
      Ax A B halign) :
    GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs Ax A B halign :=
  h.toCoreInputs.toRescaledMinCheckedCoreInputs

def GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs.toProofCodeCalibrationCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs
      Ax A B halign) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := h.target_short_proofs
  fallback_length := h.fallback_length
  proof_code_calibration := h.proof_code_calibration

def GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs.toCoreCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs
      Ax A B halign) :
    GammaIrrationalityBussPudlakSourceCalibratedCoreInputs Ax A B halign :=
  h.toProofCodeCalibrationCoreInputs.toCoreCalibratedInputs

def GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs
      Ax A B halign) :
    GammaIrrationalityConcreteShortProofSourceCoreInputs Ax A B halign :=
  h.toProofCodeCalibrationCoreInputs.toCoreInputs

def
    GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs.toRescaledMinCheckedCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs
      Ax A B halign) :
    GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs Ax A B halign :=
  h.toProofCodeCalibrationCoreInputs.toRescaledMinCheckedCoreInputs

noncomputable def GammaIrrationalityPolynomialProofFamilySemanticInputs.toSemanticGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPolynomialProofFamilySemanticInputs Ax A B halign) :
    EventualSemanticReflectionGraftModelInputs
      h.formula_code_interpretation.localCheckedCodeProofLength
      sondowReflectionGraftCode :=
  h.toPureSemanticInputs.toSemanticGraftInputs

noncomputable def
    GammaIrrationalityPolynomialProofFamilySemanticInputs.toSemanticGraftInputsDirect
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPolynomialProofFamilySemanticInputs Ax A B halign) :
    EventualSemanticReflectionGraftModelInputs
      h.formula_code_interpretation.localCheckedCodeProofLength
      sondowReflectionGraftCode where
  certificate_collapse :=
    (reflection_graft_collapse_package_of_forward_inputs_and_concrete_verification
      h.sondow_forward
      (reflection_graft_payload_inputs_of_partial_consistency_truth
        h.partial_payload_truth)
      h.concrete_verification).toEventualCertificateCollapseInputs
  short_verification := {
    verifier_polytime := certificate_verifier_polytime_sondowReflectionGraftCode
    short_proofs_of_accepted_certificates := by
      refine ⟨MiniHilbert.nat_bound_as_real
        h.formula_code_interpretation.target_proof_family.length,
        h.target_proof_family_length_polynomial, ?_⟩
      intro m _haccepted
      have hchecked :
          h.formula_code_interpretation.localCheckedCodeProofLength
              (sondowReflectionGraftCode m) =
            h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m :=
        h.formula_code_interpretation.localCheckedCodeProofLength_reflectionGraft m
      have hmin :
          h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m ≤
            h.formula_code_interpretation.target_proof_family.length m := by
        rw [ConcreteProofFamily.minCheckedCodeSize_eq_minLength]
        exact h.formula_code_interpretation.target_proof_family.minLength_le_length m
      rw [hchecked]
      change
        (h.formula_code_interpretation.target_proof_family.minCheckedCodeSize m : ℝ) ≤
          (h.formula_code_interpretation.target_proof_family.length m : ℝ)
      exact_mod_cast hmin }
  graft_lower_bound := by
    exact
      (h.formula_code_interpretation
        |>.semanticReflectionGraftEventualLowerBound_of_localCheckedSource
          h.semantic_partial_lower_bound).toEventualSemanticLowerBound

noncomputable def
    GammaIrrationalityPAHilbertVerifierSemanticLowerBoundInputs.toSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertVerifierSemanticLowerBoundInputs Ax A B halign) :
    GammaIrrationalityPAHilbertSemanticLowerBoundInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_recognition :=
    (FormulaCodeHilbertInterpretation.projectCheckedRecognition_iff_localProofCodeProjectLength
      h.formula_code_interpretation h.fallback_length).2
      h.proof_length_eq_verifierProjectLength
  semantic_partial_lower_bound := h.semantic_partial_lower_bound

noncomputable def
    GammaIrrationalityPAHilbertVerifierSemanticLowerBoundInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertVerifierSemanticLowerBoundInputs Ax A B halign) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  h.toSemanticLowerBoundInputs.toEventualReflectionGraftInputs

noncomputable def
    GammaIrrationalityPAHilbertVerifierSemanticLowerBoundInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertVerifierSemanticLowerBoundInputs Ax A B halign) :
    GammaIrrationalityMainInputs :=
  h.toSemanticLowerBoundInputs.toMainInputs

def GammaIrrationalityLocalFormulaCodeModelInputs.toLocalCalibration
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign) :
    MiniHilbert.FormulaCodeHilbertLocalCalibration
      h.formula_code_interpretation :=
  h.proof_length_local_calibration

def GammaIrrationalityLocalFormulaCodeModelInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign) :
    GammaIrrationalityLocalFormulaCodeModelCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_local_calibration := h.proof_length_local_calibration

def GammaIrrationalityLocalFormulaCodeModelInputs.toLocalHilbertProofCodeSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign) :
    GammaIrrationalityLocalHilbertProofCodeSemanticsInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_eq_minProofCodeSize :=
    h.toLocalCalibration.to_localHilbertProofCodeSemantics

def GammaIrrationalityLocalFormulaCodeModelCoreInputs.toProofCodeCalibrationCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := target_short_proofs
  fallback_length := fallback_length
  proof_code_calibration :=
    h.proof_length_local_calibration.toProofLengthCodeCalibration fallback_length

def GammaIrrationalityLocalFormulaCodeModelSpecCoreInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelSpecCoreInputs Ax A B halign) :
    GammaIrrationalityLocalFormulaCodeModelCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_spec.toPayloadTruth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_local_calibration := h.proof_length_local_calibration

def
    GammaIrrationalityLocalFormulaCodeModelSpecCoreInputs.toProofCodeCalibrationSpecCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelSpecCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationSpecCoreInputs
      Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_spec := h.partial_payload_spec
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := target_short_proofs
  fallback_length := fallback_length
  proof_code_calibration :=
    h.proof_length_local_calibration.toProofLengthCodeCalibration fallback_length

set_option linter.style.longLine false in
def
    GammaIrrationalityLocalFormulaCodeModelSpecCoreInputs.toProofCodeCalibrationSpecCoreInputsOfLengthPolynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelSpecCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationSpecCoreInputs
      Ax A B halign :=
  h.toProofCodeCalibrationSpecCoreInputs fallback_length
    (h.formula_code_interpretation.target_proof_family.toPolynomialShortProofFamily
      hpoly)

def GammaIrrationalityLocalFormulaCodeModelInputs.toProofCodeCalibrationCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign :=
  h.toCoreInputs.toProofCodeCalibrationCoreInputs fallback_length target_short_proofs

def GammaIrrationalityLocalCalibrationSemanticLowerBoundInputs.toLocalFormulaInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalCalibrationSemanticLowerBoundInputs Ax A B halign) :
    GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_local_calibration := h.proof_length_local_calibration

def GammaIrrationalityLocalCalibrationSemanticLowerBoundInputs.toLocalProofCodeInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalCalibrationSemanticLowerBoundInputs Ax A B halign) :
    GammaIrrationalityLocalProofCodeSemanticLowerBoundInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_eq_minProofCodeSize :=
    h.proof_length_local_calibration.to_localHilbertProofCodeSemantics
  semantic_partial_lower_bound := h.semantic_partial_lower_bound

def GammaIrrationalityProjectProofLengthSemanticsInputs.toLocalFormulaCodeModelInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectProofLengthSemanticsInputs Ax A B halign) :
    GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_local_calibration :=
    MiniHilbert.FormulaCodeHilbertLocalCalibration.of_projectProofLengthSemantics
      h.formula_code_interpretation h.proof_length_semantics

def GammaIrrationalityProjectProofLengthSemanticsInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectProofLengthSemanticsInputs Ax A B halign) :
    GammaIrrationalityProjectProofLengthSemanticsCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_semantics := h.proof_length_semantics

def GammaIrrationalityProjectProofLengthSemanticsCoreInputs.toLocalFormulaCodeModelCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectProofLengthSemanticsCoreInputs Ax A B halign) :
    GammaIrrationalityLocalFormulaCodeModelCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_local_calibration :=
    MiniHilbert.FormulaCodeHilbertLocalCalibration.of_projectProofLengthSemantics
      h.formula_code_interpretation h.proof_length_semantics

def GammaIrrationalityProjectProofLengthSemanticsCoreInputs.toProofCodeCalibrationCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectProofLengthSemanticsCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign :=
  h.toLocalFormulaCodeModelCoreInputs.toProofCodeCalibrationCoreInputs
    fallback_length target_short_proofs

set_option linter.style.longLine false in
def
    GammaIrrationalityProjectProofLengthSemanticsCoreInputs.toProofCodeCalibrationCoreInputsOfLengthPolynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectProofLengthSemanticsCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign :=
  h.toLocalFormulaCodeModelCoreInputs.toProofCodeCalibrationCoreInputs
    fallback_length
    (h.formula_code_interpretation.target_proof_family.toPolynomialShortProofFamily
      hpoly)

def GammaIrrationalityProjectCheckedCodeSemanticsInputs.toLocalFormulaCodeModelInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedCodeSemanticsInputs Ax A B halign) :
    GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_local_calibration :=
    MiniHilbert.FormulaCodeHilbertLocalCalibration.of_projectCheckedCodeProofLengthSemantics
      h.formula_code_interpretation h.proof_length_semantics

def GammaIrrationalityProjectCheckedCodeSemanticsInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedCodeSemanticsInputs Ax A B halign) :
    GammaIrrationalityProjectCheckedCodeSemanticsCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_semantics := h.proof_length_semantics

def GammaIrrationalityProjectCheckedCodeSemanticsCoreInputs.toLocalFormulaCodeModelCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedCodeSemanticsCoreInputs Ax A B halign) :
    GammaIrrationalityLocalFormulaCodeModelCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_local_calibration :=
    MiniHilbert.FormulaCodeHilbertLocalCalibration.of_projectCheckedCodeProofLengthSemantics
      h.formula_code_interpretation h.proof_length_semantics

noncomputable def
    GammaIrrationalityProjectCheckedCodeSemanticsCoreInputs.toPAHilbertFamilyExactness
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedCodeSemanticsCoreInputs Ax A B halign) :
    MiniHilbert.PAHilbertProjectionFamilyExactness h.formula_code_interpretation :=
  MiniHilbert.PAHilbertProjectionFamilyExactness.of_projectCheckedCodeProofLengthSemantics
    h.formula_code_interpretation h.proof_length_semantics

noncomputable def
    GammaIrrationalityProjectCheckedCodeSemanticsCoreInputs.toProofCodeCalibrationCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedCodeSemanticsCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign :=
  h.toLocalFormulaCodeModelCoreInputs.toProofCodeCalibrationCoreInputs
    fallback_length target_short_proofs

set_option linter.style.longLine false in
noncomputable def
    GammaIrrationalityProjectCheckedCodeSemanticsCoreInputs.toProofCodeCalibrationCoreInputsOfLengthPolynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedCodeSemanticsCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign :=
  h.toLocalFormulaCodeModelCoreInputs.toProofCodeCalibrationCoreInputs
    fallback_length
    (h.formula_code_interpretation.target_proof_family.toPolynomialShortProofFamily
      hpoly)

noncomputable def
    GammaIrrationalityProjectCheckedSemanticLowerBoundInputs.toSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedSemanticLowerBoundInputs Ax A B halign) :
    GammaIrrationalityPAHilbertSemanticLowerBoundInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_recognition :=
    MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition.ofProjectProofLengthSemantics
      h.proof_length_semantics
  semantic_partial_lower_bound := h.semantic_partial_lower_bound

noncomputable def
    GammaIrrationalityProjectCheckedSemanticLowerBoundInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedSemanticLowerBoundInputs Ax A B halign) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  h.toSemanticLowerBoundInputs.toEventualReflectionGraftInputs

noncomputable def GammaIrrationalityProjectCheckedSemanticLowerBoundInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedSemanticLowerBoundInputs Ax A B halign) :
    GammaIrrationalityMainInputs :=
  h.toSemanticLowerBoundInputs.toMainInputs

noncomputable def
    GammaIrrationalityPAHilbertFamilyExactnessSemanticLowerBoundInputs.toProjectCheckedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertFamilyExactnessSemanticLowerBoundInputs
      Ax A B halign) :
    GammaIrrationalityProjectCheckedSemanticLowerBoundInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_semantics :=
    h.proof_length_family_exactness.to_projectCheckedCodeProofLengthSemantics
  semantic_partial_lower_bound := h.semantic_partial_lower_bound

noncomputable def
    GammaIrrationalityPAHilbertFamilyExactnessSemanticLowerBoundInputs.toSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertFamilyExactnessSemanticLowerBoundInputs
      Ax A B halign) :
    GammaIrrationalityPAHilbertSemanticLowerBoundInputs Ax A B halign :=
  h.toProjectCheckedInputs.toSemanticLowerBoundInputs

noncomputable def
    GammaIrrationalityPAHilbertFamilyExactnessSemanticLowerBoundInputs.toEventualGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertFamilyExactnessSemanticLowerBoundInputs
      Ax A B halign) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  h.toProjectCheckedInputs.toEventualReflectionGraftInputs

noncomputable def
    GammaIrrationalityPAHilbertFamilyExactnessSemanticLowerBoundInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertFamilyExactnessSemanticLowerBoundInputs
      Ax A B halign) :
    GammaIrrationalityMainInputs :=
  h.toProjectCheckedInputs.toMainInputs

noncomputable def
    GammaIrrationalityProjectCheckedCodeSemanticsInputs.toPAHilbertFamilyExactnessInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedCodeSemanticsInputs Ax A B halign) :
    GammaIrrationalityPAHilbertFamilyExactnessInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_family_exactness :=
    MiniHilbert.PAHilbertProjectionFamilyExactness.of_projectCheckedCodeProofLengthSemantics
      h.formula_code_interpretation h.proof_length_semantics

def GammaIrrationalityLocalHilbertProofCodeSemanticsInputs.toProjectCheckedCodeSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalHilbertProofCodeSemanticsInputs Ax A B halign) :
    GammaIrrationalityProjectCheckedCodeSemanticsInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_semantics :=
    h.formula_code_interpretation.projectCheckedCodeSemantics_of_localHilbertProofCodeSemantics
      h.proof_length_eq_minProofCodeSize

def GammaIrrationalityLocalHilbertProofCodeSemanticsInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalHilbertProofCodeSemanticsInputs Ax A B halign) :
    GammaIrrationalityLocalHilbertProofCodeSemanticsCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_eq_minProofCodeSize := h.proof_length_eq_minProofCodeSize

def GammaIrrationalityLocalHilbertProofCodeSemanticsCoreInputs.toLocalFormulaCodeModelCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalHilbertProofCodeSemanticsCoreInputs Ax A B halign) :
    GammaIrrationalityLocalFormulaCodeModelCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_local_calibration :=
    MiniHilbert.FormulaCodeHilbertLocalCalibration.of_localHilbertProofCodeSemantics
      h.formula_code_interpretation h.proof_length_eq_minProofCodeSize

def GammaIrrationalityLocalHilbertProofCodeSemanticsCoreInputs.toProofCodeCalibrationCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalHilbertProofCodeSemanticsCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign :=
  h.toLocalFormulaCodeModelCoreInputs.toProofCodeCalibrationCoreInputs
    fallback_length target_short_proofs

set_option linter.style.longLine false in
def
    GammaIrrationalityLocalHilbertProofCodeSemanticsCoreInputs.toProofCodeCalibrationCoreInputsOfLengthPolynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalHilbertProofCodeSemanticsCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign :=
  h.toLocalFormulaCodeModelCoreInputs.toProofCodeCalibrationCoreInputs
    fallback_length
    (h.formula_code_interpretation.target_proof_family.toPolynomialShortProofFamily
      hpoly)

def GammaIrrationalityLocalProofCodeSemanticLowerBoundInputs.toLocalProofCodeInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalProofCodeSemanticLowerBoundInputs Ax A B halign) :
    GammaIrrationalityLocalHilbertProofCodeSemanticsInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_eq_minProofCodeSize := h.proof_length_eq_minProofCodeSize

def GammaIrrationalityLocalProofCodeSemanticLowerBoundInputs.toProjectCheckedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalProofCodeSemanticLowerBoundInputs Ax A B halign) :
    GammaIrrationalityProjectCheckedSemanticLowerBoundInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_semantics :=
    h.formula_code_interpretation.projectCheckedCodeSemantics_of_localHilbertProofCodeSemantics
      h.proof_length_eq_minProofCodeSize
  semantic_partial_lower_bound := h.semantic_partial_lower_bound

def GammaIrrationalityLocalProofCodeSemanticLowerBoundInputs.toFamilyExactnessInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalProofCodeSemanticLowerBoundInputs Ax A B halign) :
    GammaIrrationalityPAHilbertFamilyExactnessSemanticLowerBoundInputs
      Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_family_exactness :=
    MiniHilbert.PAHilbertProjectionFamilyExactness.of_projectCheckedCodeProofLengthSemantics
      h.formula_code_interpretation
      h.toProjectCheckedInputs.proof_length_semantics
  semantic_partial_lower_bound := h.semantic_partial_lower_bound

noncomputable def GammaIrrationalityLocalProofCodeSemanticLowerBoundInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalProofCodeSemanticLowerBoundInputs Ax A B halign) :
    GammaIrrationalityMainInputs :=
  h.toProjectCheckedInputs.toMainInputs

noncomputable def
    GammaIrrationalityLocalCalibrationSemanticLowerBoundInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalCalibrationSemanticLowerBoundInputs Ax A B halign) :
    GammaIrrationalityMainInputs :=
  h.toLocalProofCodeInputs.toMainInputs

def GammaIrrationalityLocalHilbertProofCodeSemanticsInputs.toLocalFormulaCodeModelInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalHilbertProofCodeSemanticsInputs Ax A B halign) :
    GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign :=
  h.toProjectCheckedCodeSemanticsInputs.toLocalFormulaCodeModelInputs

noncomputable def
    GammaIrrationalityLocalHilbertProofCodeSemanticsInputs.toPAHilbertFamilyExactnessInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalHilbertProofCodeSemanticsInputs Ax A B halign) :
    GammaIrrationalityPAHilbertFamilyExactnessInputs Ax A B halign :=
  h.toProjectCheckedCodeSemanticsInputs.toPAHilbertFamilyExactnessInputs

def GammaIrrationalityLocalHilbertProofCodeSemanticsInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalHilbertProofCodeSemanticsInputs Ax A B halign) :
    GammaIrrationalityMainInputs where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_soundness :=
    h.formula_code_interpretation.toBridge_of_localHilbertProofCodeSemantics
      h.proof_length_eq_minProofCodeSize

def GammaIrrationalitySemanticProofLengthInputs.toLocalHilbertProofCodeSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthInputs Ax A B halign) :
    GammaIrrationalityLocalHilbertProofCodeSemanticsInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_eq_minProofCodeSize := by
    intro code hcode
    rw [h.proof_length_eq_semanticProofLength code hcode]
    exact_mod_cast
      ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize
        h.formula_code_interpretation.localHilbertProofCodeSemantics
        h.fallback_length hcode

def GammaIrrationalitySemanticProofLengthInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthInputs Ax A B halign) :
    GammaIrrationalitySemanticProofLengthCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  fallback_length := h.fallback_length
  proof_length_eq_semanticProofLength := h.proof_length_eq_semanticProofLength

def GammaIrrationalitySemanticProofLengthCoreInputs.toProofLengthCodeCalibration
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthCoreInputs Ax A B halign) :
    (h.formula_code_interpretation.localHilbertProofLengthCodeSemantics
      h.fallback_length).Calibration where
  proof_length_eq_length := by
    intro code hcode
    rw [h.proof_length_eq_semanticProofLength code hcode]
    rfl

def GammaIrrationalitySemanticProofLengthCoreInputs.toProofCodeCalibrationCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthCoreInputs Ax A B halign)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := target_short_proofs
  fallback_length := h.fallback_length
  proof_code_calibration := h.toProofLengthCodeCalibration

set_option linter.style.longLine false in
def
    GammaIrrationalitySemanticProofLengthCoreInputs.toProofCodeCalibrationCoreInputsOfLengthPolynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthCoreInputs Ax A B halign)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign :=
  h.toProofCodeCalibrationCoreInputs
    (h.formula_code_interpretation.target_proof_family.toPolynomialShortProofFamily
      hpoly)

def GammaIrrationalityLocalHilbertProofCodeSemanticsInputs.toSemanticProofLengthInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalHilbertProofCodeSemanticsInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ) :
    GammaIrrationalitySemanticProofLengthInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  fallback_length := fallback_length
  proof_length_eq_semanticProofLength := by
    intro code hcode
    rw [h.proof_length_eq_minProofCodeSize code hcode]
    exact_mod_cast
      (ProofCodeSemantics.semanticProofLength_eq_minProofCodeSize
        h.formula_code_interpretation.localHilbertProofCodeSemantics
        fallback_length hcode).symm

def GammaIrrationalitySemanticProofLengthInputs.toProjectProofLengthSemantics
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthInputs Ax A B halign) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      (h.formula_code_interpretation.localHilbertSemanticProofLength
        h.fallback_length)
      MiniHilbert.FormulaCodeHilbertRelevantCode :=
  h.formula_code_interpretation.projectSemantics_of_semanticProofLength
    h.fallback_length h.proof_length_eq_semanticProofLength

def GammaIrrationalitySemanticProofLengthInputs.toProofLengthCodeCalibration
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthInputs Ax A B halign) :
    (h.formula_code_interpretation.localHilbertProofLengthCodeSemantics
      h.fallback_length).Calibration where
  proof_length_eq_length := by
    intro code hcode
    rw [h.proof_length_eq_semanticProofLength code hcode]
    rfl

def GammaIrrationalitySemanticProofLengthInputs.toProofCodeCalibrationCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthInputs Ax A B halign)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := target_short_proofs
  fallback_length := h.fallback_length
  proof_code_calibration := h.toProofLengthCodeCalibration

def GammaIrrationalitySemanticProofLengthInputs.toProofCodeCalibrationCoreInputsOfLengthPolynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthInputs Ax A B halign)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign :=
  h.toProofCodeCalibrationCoreInputs
    (h.formula_code_interpretation.target_proof_family.toPolynomialShortProofFamily
      hpoly)

noncomputable def GammaIrrationalitySemanticProofLengthInputs.toPAHilbertProjectionCodeSemantics
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthInputs Ax A B halign) :
    MiniHilbert.PAHilbertProofLengthCodeSemanticsForProjection
      h.formula_code_interpretation :=
  h.formula_code_interpretation.localPAHilbertProofLengthCodeSemanticsForProjection
    h.fallback_length

noncomputable def GammaIrrationalityStandardFormulaCodeSemanticsInputs.toProofLengthCodeCalibration
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign)
    (fallback : FormulaCode → ℕ) :
    (let model :=
      h.formula_code_interpretation.localPAHilbertProofLengthCodeSemanticsForProjection
        fallback
     model.code_model.Calibration) :=
  h.proof_length_semantics.toLocalPAHilbertCodeCalibration fallback

def GammaIrrationalityStandardFormulaCodeSemanticsInputs.toCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign) :
    GammaIrrationalityStandardFormulaCodeSemanticsCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_semantics := h.proof_length_semantics

noncomputable def
    GammaIrrationalityStandardFormulaCodeSemanticsCoreInputs.toProofLengthCodeCalibration
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsCoreInputs Ax A B halign)
    (fallback : FormulaCode → ℕ) :
    (let model :=
      h.formula_code_interpretation.localPAHilbertProofLengthCodeSemanticsForProjection
        fallback
     model.code_model.Calibration) :=
  h.proof_length_semantics.toLocalPAHilbertCodeCalibration fallback

noncomputable def
    GammaIrrationalityStandardFormulaCodeSemanticsCoreInputs.toProofCodeCalibrationCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsCoreInputs Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := target_short_proofs
  fallback_length := fallback
  proof_code_calibration := h.toProofLengthCodeCalibration fallback

set_option linter.style.longLine false in
noncomputable def
    GammaIrrationalityStandardFormulaCodeSemanticsCoreInputs.toProofCodeCalibrationCoreInputsOfLengthPolynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsCoreInputs Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign :=
  h.toProofCodeCalibrationCoreInputs fallback
    (h.formula_code_interpretation.target_proof_family.toPolynomialShortProofFamily
      hpoly)

noncomputable def
    GammaIrrationalityStandardFormulaCodeSemanticsInputs.toProofCodeCalibrationCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  target_short_proofs := target_short_proofs
  fallback_length := fallback
  proof_code_calibration := h.toProofLengthCodeCalibration fallback

set_option linter.style.longLine false in
noncomputable def
    GammaIrrationalityStandardFormulaCodeSemanticsInputs.toProofCodeCalibrationCoreInputsOfLengthPolynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs Ax A B halign :=
  h.toProofCodeCalibrationCoreInputs fallback
    (h.formula_code_interpretation.target_proof_family.toPolynomialShortProofFamily
      hpoly)

def GammaIrrationalitySemanticProofLengthInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthInputs Ax A B halign) :
    GammaIrrationalityMainInputs where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_soundness :=
    h.formula_code_interpretation.toBridge_of_semanticProofLength
      h.fallback_length h.proof_length_eq_semanticProofLength

theorem GammaIrrationalityLocalFormulaCodeModelInputs.localProofCode_roundtrip
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign) :
    (let h' := h.toLocalHilbertProofCodeSemanticsInputs.toLocalFormulaCodeModelInputs
     h'.proof_length_local_calibration) =
        h.proof_length_local_calibration := by
  cases h
  rfl

noncomputable def
    GammaIrrationalityLocalFormulaCodeModelInputs.toStandardSemanticsInputsViaCalibration
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign) :
    GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification := h.concrete_verification
  partial_payload_truth := h.partial_payload_truth
  partial_payload_reading := h.partial_payload_reading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_semantics := h.toLocalCalibration.toStandardSemantics

noncomputable def GammaIrrationalityLocalFormulaCodeModelInputs.toExactProjectionInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign) :
    GammaIrrationalityExactProjectionInputs :=
  { sondow_forward := h.sondow_forward
    concrete_verification := h.concrete_verification
    partial_payload_truth := h.partial_payload_truth
    partial_payload_reading := h.partial_payload_reading
    buss_pudlak_rescaling := h.buss_pudlak_rescaling
    hilbert_alignment := halign
    hilbert_exact_projection :=
      h.proof_length_local_calibration.toExactProjectionRealization }

noncomputable def GammaIrrationalityLocalFormulaCodeModelInputs.toTargetExactProjectionInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign) :
    GammaIrrationalityTargetExactProjectionInputs :=
  { sondow_forward := h.sondow_forward
    concrete_verification := h.concrete_verification
    partial_payload_truth := h.partial_payload_truth
    partial_payload_reading := h.partial_payload_reading
    buss_pudlak_rescaling := h.buss_pudlak_rescaling
    hilbert_alignment := halign
    hilbert_target_exact_projection :=
      h.proof_length_local_calibration.toTargetExactProjectionRealization }

noncomputable def GammaIrrationalityLocalFormulaCodeModelInputs.toMainInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign) :
    GammaIrrationalityMainInputs :=
  h.toStandardSemanticsInputsViaCalibration.toMainInputs

theorem gamma_irrationality_main_inputs_to_eventual_reflection_graft_inputs
    (h : GammaIrrationalityMainInputs) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  eventual_reflection_graft_inputs_of_time_constructible_rescaling
    h.sondow_forward
    h.concrete_verification
    h.partial_payload_truth
    h.buss_pudlak_rescaling
    (partial_consistency_transfer_of_right_conjunction_elimination
      (conjunction_elimination_transfer_package_of_hilbert_realization
        h.hilbert_soundness.toTwoStepRealization))

theorem GammaIrrationalityFormulaCodeRealizationInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityFormulaCodeRealizationInputs Ax A B halign) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  gamma_irrationality_main_inputs_to_eventual_reflection_graft_inputs h.toMainInputs

theorem GammaIrrationalityDefaultFormulaCodeRealizationInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultFormulaCodeRealizationInputs Ax A B) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  GammaIrrationalityFormulaCodeRealizationInputs.toEventualReflectionGraftInputs h

theorem GammaIrrationalityStandardFormulaCodeSemanticsInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  gamma_irrationality_main_inputs_to_eventual_reflection_graft_inputs h.toMainInputs

theorem GammaIrrationalityDefaultStandardFormulaCodeSemanticsInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultStandardFormulaCodeSemanticsInputs Ax A B) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  GammaIrrationalityStandardFormulaCodeSemanticsInputs.toEventualReflectionGraftInputs h

theorem GammaIrrationalityLocalFormulaCodeModelInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  gamma_irrationality_main_inputs_to_eventual_reflection_graft_inputs h.toMainInputs

theorem GammaIrrationalityDefaultLocalFormulaCodeModelInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultLocalFormulaCodeModelInputs Ax A B) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  GammaIrrationalityLocalFormulaCodeModelInputs.toEventualReflectionGraftInputs h

theorem GammaIrrationalityProjectProofLengthSemanticsInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectProofLengthSemanticsInputs Ax A B halign) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  h.toLocalFormulaCodeModelInputs.toEventualReflectionGraftInputs

theorem GammaIrrationalityDefaultProjectProofLengthSemanticsInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultProjectProofLengthSemanticsInputs Ax A B) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  GammaIrrationalityProjectProofLengthSemanticsInputs.toEventualReflectionGraftInputs h

theorem GammaIrrationalityProjectCheckedCodeSemanticsInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedCodeSemanticsInputs Ax A B halign) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  h.toLocalFormulaCodeModelInputs.toEventualReflectionGraftInputs

theorem GammaIrrationalityDefaultProjectCheckedCodeSemanticsInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultProjectCheckedCodeSemanticsInputs Ax A B) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  GammaIrrationalityProjectCheckedCodeSemanticsInputs.toEventualReflectionGraftInputs h

theorem GammaIrrationalityLocalHilbertProofCodeSemanticsInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalHilbertProofCodeSemanticsInputs Ax A B halign) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  h.toLocalFormulaCodeModelInputs.toEventualReflectionGraftInputs

theorem default_local_hilbert_proof_code_inputs_to_eventual_reflection_graft_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultLocalHilbertProofCodeSemanticsInputs Ax A B) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  GammaIrrationalityLocalHilbertProofCodeSemanticsInputs.toEventualReflectionGraftInputs h

theorem GammaIrrationalitySemanticProofLengthInputs.toEventualReflectionGraftInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthInputs Ax A B halign) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  gamma_irrationality_main_inputs_to_eventual_reflection_graft_inputs h.toMainInputs

theorem default_semantic_proof_length_inputs_to_eventual_reflection_graft_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultSemanticProofLengthInputs Ax A B) :
    EventualReflectionGraftModelInputs ProofSystem.PA ProofLengthMeasure.symbolSize
      sondowReflectionGraftCode :=
  GammaIrrationalitySemanticProofLengthInputs.toEventualReflectionGraftInputs h

theorem gamma_irrational_of_main_inputs
    (h : GammaIrrationalityMainInputs) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_time_rescaling_and_hilbert_soundness_bridge
    h.sondow_forward
    h.concrete_verification
    h.partial_payload_truth
    h.partial_payload_reading
    h.buss_pudlak_rescaling
    h.hilbert_soundness

theorem gamma_irrational_of_exact_projection_inputs
    (h : GammaIrrationalityExactProjectionInputs) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_main_inputs h.toMainInputs

theorem gamma_irrational_of_target_exact_projection_inputs
    (h : GammaIrrationalityTargetExactProjectionInputs) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_main_inputs h.toMainInputs

theorem gamma_irrational_of_formula_code_realization_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityFormulaCodeRealizationInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_main_inputs h.toMainInputs

theorem gamma_irrational_of_verified_formula_code_realization_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityVerifiedFormulaCodeRealizationInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_formula_code_realization_inputs
    h.toFormulaCodeRealizationInputs

theorem gamma_irrational_of_default_formula_code_realization_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultFormulaCodeRealizationInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_formula_code_realization_inputs h

theorem gamma_irrational_of_default_verified_formula_code_realization_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultVerifiedFormulaCodeRealizationInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_verified_formula_code_realization_inputs h

theorem gamma_irrational_of_standard_formula_code_semantics_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_main_inputs h.toMainInputs

theorem gamma_irrational_of_verified_standard_formula_code_semantics_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityVerifiedStandardFormulaCodeSemanticsInputs
      Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_standard_formula_code_semantics_inputs h.toStandardInputs

theorem gamma_irrational_of_default_standard_formula_code_semantics_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultStandardFormulaCodeSemanticsInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_standard_formula_code_semantics_inputs h

theorem gamma_irrational_of_default_verified_standard_formula_code_semantics_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultVerifiedStandardFormulaCodeSemanticsInputs
      Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_verified_standard_formula_code_semantics_inputs h

theorem gamma_irrational_of_pa_hilbert_family_exactness_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertFamilyExactnessInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_main_inputs h.toMainInputs

theorem gamma_irrational_of_default_pa_hilbert_family_exactness_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultPAHilbertFamilyExactnessInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pa_hilbert_family_exactness_inputs h

theorem gamma_irrational_of_pa_hilbert_recognition_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertRecognitionInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_main_inputs h.toMainInputs

theorem gamma_irrational_of_default_pa_hilbert_recognition_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultPAHilbertRecognitionInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pa_hilbert_recognition_inputs h

theorem gamma_irrational_of_pa_hilbert_verifier_project_length_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertVerifierProjectLengthInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_main_inputs h.toMainInputs

theorem gamma_irrational_of_default_pa_hilbert_verifier_project_length_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultPAHilbertVerifierProjectLengthInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pa_hilbert_verifier_project_length_inputs h

theorem gamma_irrational_of_local_formula_code_model_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_main_inputs h.toMainInputs

theorem gamma_irrational_of_default_local_formula_code_model_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultLocalFormulaCodeModelInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_local_formula_code_model_inputs h

theorem gamma_irrational_of_project_proof_length_semantics_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectProofLengthSemanticsInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_local_formula_code_model_inputs
    h.toLocalFormulaCodeModelInputs

theorem gamma_irrational_of_default_project_proof_length_semantics_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultProjectProofLengthSemanticsInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_project_proof_length_semantics_inputs h

theorem gamma_irrational_of_project_checked_code_semantics_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedCodeSemanticsInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_local_formula_code_model_inputs
    h.toLocalFormulaCodeModelInputs

theorem gamma_irrational_of_default_project_checked_code_semantics_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultProjectCheckedCodeSemanticsInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_project_checked_code_semantics_inputs h

theorem gamma_irrational_of_local_hilbert_proof_code_semantics_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalHilbertProofCodeSemanticsInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_main_inputs h.toMainInputs

theorem gamma_irrational_of_default_local_hilbert_proof_code_semantics_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultLocalHilbertProofCodeSemanticsInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_local_hilbert_proof_code_semantics_inputs h

theorem gamma_irrational_of_semantic_proof_length_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_main_inputs h.toMainInputs

theorem gamma_irrational_of_default_semantic_proof_length_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultSemanticProofLengthInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_semantic_proof_length_inputs h

theorem gamma_irrational_of_pa_hilbert_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertSemanticLowerBoundInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_eventual_reflection_graft_model_inputs
    h.toEventualReflectionGraftInputs

theorem gamma_irrational_of_default_pa_hilbert_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultPAHilbertSemanticLowerBoundInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pa_hilbert_semantic_lower_bound_inputs h

theorem gamma_irrational_of_pa_hilbert_verifier_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertVerifierSemanticLowerBoundInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pa_hilbert_semantic_lower_bound_inputs
    h.toSemanticLowerBoundInputs

theorem gamma_irrational_of_default_pa_hilbert_verifier_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultPAHilbertVerifierSemanticLowerBoundInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pa_hilbert_verifier_semantic_lower_bound_inputs h

theorem gamma_irrational_of_project_checked_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedSemanticLowerBoundInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pa_hilbert_semantic_lower_bound_inputs
    h.toSemanticLowerBoundInputs

theorem gamma_irrational_of_default_project_checked_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultProjectCheckedSemanticLowerBoundInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_project_checked_semantic_lower_bound_inputs h

theorem gamma_irrational_of_pa_hilbert_family_exactness_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPAHilbertFamilyExactnessSemanticLowerBoundInputs
      Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_project_checked_semantic_lower_bound_inputs
    h.toProjectCheckedInputs

theorem gamma_irrational_of_default_pa_hilbert_family_exactness_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h :
      GammaIrrationalityDefaultPAHilbertFamilyExactnessSemanticLowerBoundInputs
        Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pa_hilbert_family_exactness_semantic_lower_bound_inputs h

theorem gamma_irrational_of_local_proof_code_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalProofCodeSemanticLowerBoundInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_project_checked_semantic_lower_bound_inputs
    h.toProjectCheckedInputs

theorem gamma_irrational_of_default_local_proof_code_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultLocalProofCodeSemanticLowerBoundInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_local_proof_code_semantic_lower_bound_inputs h

theorem gamma_irrational_of_local_calibration_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalCalibrationSemanticLowerBoundInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_local_proof_code_semantic_lower_bound_inputs
    h.toLocalProofCodeInputs

theorem gamma_irrational_of_default_local_calibration_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultLocalCalibrationSemanticLowerBoundInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_local_calibration_semantic_lower_bound_inputs h

theorem gamma_irrational_of_standard_semantics_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardSemanticsLowerBoundInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pa_hilbert_family_exactness_semantic_lower_bound_inputs
    h.toFamilyExactnessInputs

theorem gamma_irrational_of_verified_standard_semantics_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityVerifiedStandardSemanticsLowerBoundInputs
      Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_standard_semantics_lower_bound_inputs
    h.toStandardSemanticsLowerBoundInputs

theorem gamma_irrational_of_default_standard_semantics_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultStandardSemanticsLowerBoundInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_standard_semantics_lower_bound_inputs h

theorem gamma_irrational_of_default_verified_standard_semantics_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultVerifiedStandardSemanticsLowerBoundInputs
      Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_verified_standard_semantics_lower_bound_inputs h

theorem gamma_irrational_of_pure_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPureSemanticLowerBoundInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_eventual_semantic_reflection_graft_model_inputs
    h.toSemanticGraftInputs

theorem gamma_irrational_of_default_pure_semantic_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultPureSemanticLowerBoundInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pure_semantic_lower_bound_inputs h

theorem gamma_irrational_of_polynomial_proof_family_semantic_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityPolynomialProofFamilySemanticInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_eventual_semantic_reflection_graft_model_inputs
    h.toSemanticGraftInputsDirect

theorem gamma_irrational_of_default_polynomial_proof_family_semantic_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultPolynomialProofFamilySemanticInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_polynomial_proof_family_semantic_inputs h

theorem gamma_irrational_of_concrete_short_proof_semantic_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityConcreteShortProofSemanticInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pure_semantic_lower_bound_inputs
    h.toPureSemanticInputs

theorem gamma_irrational_of_default_concrete_short_proof_semantic_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultConcreteShortProofSemanticInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_concrete_short_proof_semantic_inputs h

theorem gamma_irrational_of_concrete_short_proof_source_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityConcreteShortProofSourceLowerBoundInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_eventual_semantic_reflection_graft_model_inputs
    h.toSemanticGraftInputs

theorem gamma_irrational_of_concrete_short_proof_source_core_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityConcreteShortProofSourceCoreInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_eventual_semantic_reflection_graft_model_inputs
    h.toSemanticGraftInputs

theorem gamma_irrational_of_default_concrete_short_proof_source_lower_bound_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultConcreteShortProofSourceLowerBoundInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_concrete_short_proof_source_lower_bound_inputs h

theorem gamma_irrational_of_default_concrete_short_proof_source_core_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultConcreteShortProofSourceCoreInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_concrete_short_proof_source_core_inputs h

theorem gamma_irrational_of_proof_code_model_semantic_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProofCodeModelSemanticInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_eventual_semantic_reflection_graft_model_inputs
    h.toSemanticGraftInputs

theorem gamma_irrational_of_default_proof_code_model_semantic_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultProofCodeModelSemanticInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_proof_code_model_semantic_inputs h

theorem gamma_irrational_of_buss_pudlak_proof_code_model_semantic_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeModelSemanticInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_proof_code_model_semantic_inputs
    h.toProofCodeModelSemanticInputs

theorem gamma_irrational_of_buss_pudlak_rescaled_minChecked_source_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedSourceInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_eventual_semantic_reflection_graft_model_inputs
    h.toCoreInputs.toSemanticGraftInputs

theorem gamma_irrational_of_buss_pudlak_rescaled_minChecked_core_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_eventual_semantic_reflection_graft_model_inputs
    h.toSemanticGraftInputs

theorem gamma_irrational_of_buss_pudlak_rescaled_minChecked_model_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRescaledMinCheckedModelInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_rescaled_minChecked_source_inputs
    h.toSourceInputs

theorem gamma_irrational_of_default_buss_pudlak_proof_code_model_semantic_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultBussPudlakProofCodeModelSemanticInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_model_semantic_inputs h

theorem gamma_irrational_of_default_buss_pudlak_rescaled_minChecked_model_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultBussPudlakRescaledMinCheckedModelInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_rescaled_minChecked_model_inputs h

theorem gamma_irrational_of_default_buss_pudlak_rescaled_minChecked_source_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultBussPudlakRescaledMinCheckedSourceInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_rescaled_minChecked_source_inputs h

theorem gamma_irrational_of_default_buss_pudlak_rescaled_minChecked_core_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultBussPudlakRescaledMinCheckedCoreInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_rescaled_minChecked_core_inputs h

theorem gamma_irrational_of_buss_pudlak_source_calibrated_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakSourceCalibratedInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_rescaled_minChecked_core_inputs
    h.toCoreCalibratedInputs.toRescaledMinCheckedCoreInputs

theorem gamma_irrational_of_buss_pudlak_source_calibrated_core_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakSourceCalibratedCoreInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_rescaled_minChecked_core_inputs
    h.toRescaledMinCheckedCoreInputs

theorem gamma_irrational_of_core_calibrated_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_truth : PartialConsistencyPayloadTruth)
    (buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem)
    (formula_code_interpretation :
      MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True))
    (source_minChecked_calibration :
      MiniHilbert.PartialConsistencySourceMinCheckedCalibration
        formula_code_interpretation) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_source_calibrated_core_inputs
    { sondow_forward := sondow_forward
      concrete_verification := concrete_verification
      partial_payload_truth := partial_payload_truth
      buss_pudlak_rescaling := buss_pudlak_rescaling
      formula_code_interpretation := formula_code_interpretation
      target_short_proofs := target_short_proofs
      source_minChecked_calibration := source_minChecked_calibration }

theorem gamma_irrational_of_core_calibrated_spec_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_spec : PartialConsistencyPayloadSpec)
    (buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem)
    (formula_code_interpretation :
      MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True))
    (source_minChecked_calibration :
      MiniHilbert.PartialConsistencySourceMinCheckedCalibration
        formula_code_interpretation) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_core_calibrated_components
    sondow_forward
    concrete_verification
    partial_payload_spec.toPayloadTruth
    buss_pudlak_rescaling
    formula_code_interpretation
    target_short_proofs
    source_minChecked_calibration

theorem gamma_irrational_of_proof_code_calibration_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_truth : PartialConsistencyPayloadTruth)
    (buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem)
    (formula_code_interpretation :
      MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True))
    (fallback_length : FormulaCode → ℕ)
    (proof_code_calibration :
      (formula_code_interpretation.localHilbertProofLengthCodeSemantics
        fallback_length).Calibration) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_rescaled_minChecked_core_inputs
    (GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs.toRescaledMinCheckedCoreInputs
      { sondow_forward := sondow_forward
        concrete_verification := concrete_verification
        partial_payload_truth := partial_payload_truth
        buss_pudlak_rescaling := buss_pudlak_rescaling
        formula_code_interpretation := formula_code_interpretation
        target_short_proofs := target_short_proofs
        fallback_length := fallback_length
        proof_code_calibration := proof_code_calibration })

theorem gamma_irrational_of_proof_code_calibration_spec_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_spec : PartialConsistencyPayloadSpec)
    (buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem)
    (formula_code_interpretation :
      MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True))
    (fallback_length : FormulaCode → ℕ)
    (proof_code_calibration :
      (formula_code_interpretation.localHilbertProofLengthCodeSemantics
        fallback_length).Calibration) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_proof_code_calibration_components
    sondow_forward
    concrete_verification
    partial_payload_spec.toPayloadTruth
    buss_pudlak_rescaling
    formula_code_interpretation
    target_short_proofs
    fallback_length
    proof_code_calibration

theorem gamma_irrational_of_pudlak_finite_consistency_package_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_truth : PartialConsistencyPayloadTruth)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (formula_code_interpretation :
      MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True))
    (fallback_length : FormulaCode → ℕ)
    (proof_code_calibration :
      (formula_code_interpretation.localHilbertProofLengthCodeSemantics
        fallback_length).Calibration) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_proof_code_calibration_components
    sondow_forward
    concrete_verification
    partial_payload_truth
    pudlak_lower_bound.toBussPudlakTimeConstructibleRescalingTheorem
    formula_code_interpretation
    target_short_proofs
    fallback_length
    proof_code_calibration

theorem gamma_irrational_of_pudlak_spec_package_components
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_spec : PartialConsistencyPayloadSpec)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (formula_code_interpretation :
      MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True))
    (fallback_length : FormulaCode → ℕ)
    (proof_code_calibration :
      (formula_code_interpretation.localHilbertProofLengthCodeSemantics
        fallback_length).Calibration) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pudlak_finite_consistency_package_components
    sondow_forward
    concrete_verification
    partial_payload_spec.toPayloadTruth
    pudlak_lower_bound
    formula_code_interpretation
    target_short_proofs
    fallback_length
    proof_code_calibration

theorem gamma_irrational_of_pudlak_spec_lower_bound_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (partial_payload_spec : PartialConsistencyPayloadSpec)
    (formula_code_interpretation :
      MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True))
    (fallback_length : FormulaCode → ℕ)
    (proof_code_calibration :
      (formula_code_interpretation.localHilbertProofLengthCodeSemantics
        fallback_length).Calibration) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pudlak_spec_package_components
    sondow_forward
    concrete_verification
    partial_payload_spec
    pudlak_lower_bound
    formula_code_interpretation
    target_short_proofs
    fallback_length
    proof_code_calibration

theorem gamma_irrational_of_default_buss_pudlak_source_calibrated_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultBussPudlakSourceCalibratedInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_source_calibrated_inputs h

theorem gamma_irrational_of_default_buss_pudlak_source_calibrated_core_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultBussPudlakSourceCalibratedCoreInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_source_calibrated_core_inputs h

theorem gamma_irrational_of_buss_pudlak_family_exact_concrete_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakFamilyExactConcreteInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_rescaled_minChecked_core_inputs
    h.toRescaledMinCheckedCoreInputs

theorem gamma_irrational_of_default_buss_pudlak_family_exact_concrete_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultBussPudlakFamilyExactConcreteInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_family_exact_concrete_inputs h

theorem gamma_irrational_of_buss_pudlak_recognition_concrete_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakRecognitionConcreteInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_rescaled_minChecked_core_inputs
    h.toRescaledMinCheckedCoreInputs

theorem gamma_irrational_of_default_buss_pudlak_recognition_concrete_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultBussPudlakRecognitionConcreteInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_recognition_concrete_inputs h

theorem gamma_irrational_of_buss_pudlak_checker_concrete_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakCheckerConcreteInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_rescaled_minChecked_core_inputs
    h.toRescaledMinCheckedCoreInputs

theorem gamma_irrational_of_default_buss_pudlak_checker_concrete_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultBussPudlakCheckerConcreteInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_checker_concrete_inputs h

theorem gamma_irrational_of_buss_pudlak_proof_object_concrete_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofObjectConcreteInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_rescaled_minChecked_core_inputs
    h.toRescaledMinCheckedCoreInputs

theorem gamma_irrational_of_default_buss_pudlak_proof_object_concrete_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultBussPudlakProofObjectConcreteInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_object_concrete_inputs h

theorem gamma_irrational_of_buss_pudlak_proof_code_calibration_concrete_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs
      Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_rescaled_minChecked_core_inputs
    h.toRescaledMinCheckedCoreInputs

theorem gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs
      Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_rescaled_minChecked_core_inputs
    h.toRescaledMinCheckedCoreInputs

theorem gamma_irrational_of_buss_pudlak_proof_code_calibration_spec_core_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityBussPudlakProofCodeCalibrationSpecCoreInputs
      Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    h.toCoreInputs

theorem gamma_irrational_of_default_buss_pudlak_proof_code_calibration_concrete_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultBussPudlakProofCodeCalibrationConcreteInputs
      Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_concrete_inputs h

theorem gamma_irrational_of_default_buss_pudlak_proof_code_calibration_core_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : GammaIrrationalityDefaultBussPudlakProofCodeCalibrationCoreInputs
      Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs h

theorem gamma_irrational_of_project_proof_length_semantics_core_and_short_proofs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectProofLengthSemanticsCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputs fallback_length target_short_proofs)

theorem gamma_irrational_of_project_proof_length_semantics_core_and_length_polynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectProofLengthSemanticsCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputsOfLengthPolynomial fallback_length hpoly)

theorem gamma_irrational_of_project_checked_code_semantics_core_and_short_proofs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedCodeSemanticsCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputs fallback_length target_short_proofs)

theorem gamma_irrational_of_project_checked_code_semantics_core_and_length_polynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityProjectCheckedCodeSemanticsCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputsOfLengthPolynomial fallback_length hpoly)

theorem gamma_irrational_of_local_formula_model_and_short_proofs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputs fallback_length target_short_proofs)

theorem gamma_irrational_of_local_formula_model_core_and_short_proofs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputs fallback_length target_short_proofs)

theorem gamma_irrational_of_local_formula_model_spec_core_and_short_proofs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelSpecCoreInputs
      Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_spec_core_inputs
    (h.toProofCodeCalibrationSpecCoreInputs
      fallback_length target_short_proofs)

theorem gamma_irrational_of_local_hilbert_proof_code_semantics_core_and_short_proofs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalHilbertProofCodeSemanticsCoreInputs
      Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputs fallback_length target_short_proofs)

theorem gamma_irrational_of_local_formula_model_and_length_polynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_local_formula_model_and_short_proofs h fallback_length
    (h.formula_code_interpretation.target_proof_family.toPolynomialShortProofFamily
      hpoly)

theorem gamma_irrational_of_local_formula_model_core_and_length_polynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelCoreInputs Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_local_formula_model_core_and_short_proofs h fallback_length
    (h.formula_code_interpretation.target_proof_family.toPolynomialShortProofFamily
      hpoly)

theorem gamma_irrational_of_local_formula_model_spec_core_and_length_polynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalFormulaCodeModelSpecCoreInputs
      Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_spec_core_inputs
    (h.toProofCodeCalibrationSpecCoreInputsOfLengthPolynomial
      fallback_length hpoly)

theorem gamma_irrational_of_local_hilbert_proof_code_semantics_core_and_length_polynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityLocalHilbertProofCodeSemanticsCoreInputs
      Ax A B halign)
    (fallback_length : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputsOfLengthPolynomial fallback_length hpoly)

theorem gamma_irrational_of_pudlak_package_local_formula_model_and_length_polynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_truth : PartialConsistencyPayloadTruth)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (formula_code_interpretation :
      MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (proof_length_local_calibration :
      MiniHilbert.FormulaCodeHilbertLocalCalibration formula_code_interpretation)
    (fallback_length : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          formula_code_interpretation.target_proof_family.length)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_local_formula_model_core_and_length_polynomial
    { sondow_forward := sondow_forward
      concrete_verification := concrete_verification
      partial_payload_truth := partial_payload_truth
      buss_pudlak_rescaling :=
        pudlak_lower_bound.toBussPudlakTimeConstructibleRescalingTheorem
      formula_code_interpretation := formula_code_interpretation
      proof_length_local_calibration := proof_length_local_calibration }
    fallback_length
    hpoly

theorem gamma_irrational_of_pudlak_spec_package_local_formula_model_and_length_polynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (partial_payload_spec : PartialConsistencyPayloadSpec)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (formula_code_interpretation :
      MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (proof_length_local_calibration :
      MiniHilbert.FormulaCodeHilbertLocalCalibration formula_code_interpretation)
    (fallback_length : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          formula_code_interpretation.target_proof_family.length)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pudlak_package_local_formula_model_and_length_polynomial
    sondow_forward
    concrete_verification
    partial_payload_spec.toPayloadTruth
    pudlak_lower_bound
    formula_code_interpretation
    proof_length_local_calibration
    fallback_length
    hpoly

theorem
    gamma_irrational_of_pudlak_spec_lower_bound_package_local_formula_model_and_length_polynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (sondow_forward : SondowForwardInputs)
    (concrete_verification : ReflectionGraftConcreteVerificationPackage)
    (pudlak_lower_bound : PudlakFiniteConsistencyLowerBoundPackage)
    (partial_payload_spec : PartialConsistencyPayloadSpec)
    (formula_code_interpretation :
      MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (proof_length_local_calibration :
      MiniHilbert.FormulaCodeHilbertLocalCalibration formula_code_interpretation)
    (fallback_length : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          formula_code_interpretation.target_proof_family.length)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_pudlak_spec_package_local_formula_model_and_length_polynomial
    sondow_forward
    concrete_verification
    partial_payload_spec
    pudlak_lower_bound
    formula_code_interpretation
    proof_length_local_calibration
    fallback_length
    hpoly

theorem gamma_irrational_of_semantic_proof_length_and_short_proofs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthInputs Ax A B halign)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputs target_short_proofs)

theorem gamma_irrational_of_semantic_proof_length_core_and_short_proofs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthCoreInputs Ax A B halign)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputs target_short_proofs)

theorem gamma_irrational_of_semantic_proof_length_and_length_polynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthInputs Ax A B halign)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputsOfLengthPolynomial hpoly)

theorem gamma_irrational_of_semantic_proof_length_core_and_length_polynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalitySemanticProofLengthCoreInputs Ax A B halign)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputsOfLengthPolynomial hpoly)

theorem gamma_irrational_of_standard_semantics_and_short_proofs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputs fallback target_short_proofs)

theorem gamma_irrational_of_standard_semantics_core_and_short_proofs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsCoreInputs Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (target_short_proofs :
      MiniHilbert.ConcretePolynomialShortProofFamily
        Ax (fun m => A m ⊓ B m) (fun _ => True)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputs fallback target_short_proofs)

theorem gamma_irrational_of_standard_semantics_and_length_polynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputsOfLengthPolynomial fallback hpoly)

theorem gamma_irrational_of_standard_semantics_core_and_length_polynomial
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityStandardFormulaCodeSemanticsCoreInputs Ax A B halign)
    (fallback : FormulaCode → ℕ)
    (hpoly :
      is_polynomial_bound
        (MiniHilbert.nat_bound_as_real
          h.formula_code_interpretation.target_proof_family.length)) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_buss_pudlak_proof_code_calibration_core_inputs
    (h.toProofCodeCalibrationCoreInputsOfLengthPolynomial fallback hpoly)

theorem irrational_of_natural_sondow_main_inputs
    (h : NaturalSondowMainInputs) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_natural_sondow_conditional_inputs h

theorem irrational_of_reflection_graft_main_inputs
    (h : ReflectionGraftMainInputs) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_reflection_graft_model_inputs h

theorem gamma_irrational_of_literature_pudlak_certificate_verified_collision
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (hsource : LiteraturePudlakTheorem5LowerBoundCertificate)
    (hpackage : StrengthenedToPartialAcceptedProjectionPackage)
    (hverify : SondowCollapseVerificationBridgePackage) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_literature_pudlak_theorem5_certificate_verified_accepted_pkg
    interp hsource hpackage hverify

theorem gamma_irrational_of_literature_pudlak_verified_collision_package
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (h : LiteraturePudlakVerifiedCollisionPackage) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_literature_pudlak_verified_collision_package interp h

theorem gamma_irrational_of_literature_pudlak_verified_collision_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : LiteraturePudlakVerifiedCollisionInputs Ax A B halign) :
    ¬ (is_rational euler_mascheroni) :=
  irrational_of_literature_pudlak_verified_collision_inputs h

theorem gamma_irrational_of_literature_pudlak_default_verified_collision_inputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    (h : LiteraturePudlakDefaultVerifiedCollisionInputs Ax A B) :
    ¬ (is_rational euler_mascheroni) :=
  gamma_irrational_of_literature_pudlak_verified_collision_inputs h

theorem godel_sondow_coupling_hypothesis_of_proof_complexity_for
    (hpc : ProofComplexityInputsFor sondowIdentityCode) :
    ¬ (is_rational euler_mascheroni) := by
  exact irrational_of_proof_complexity_inputs_for hpc

-- Legacy Gödel-Sondow contradiction endpoint, kept explicitly conditional.
-- Earlier drafts instantiated this endpoint with the two summary axioms from
-- `proof_complexity_inputs_from_axioms`.  That produces a theorem with no
-- visible hypotheses, which is misleading for audit and exposition: the real
-- mathematical content is the supplied collapse and lower-bound package.
theorem godel_sondow_coupling_hypothesis
    (hpc : ProofComplexityInputsFor sondowIdentityCode) :
    ¬ (is_rational euler_mascheroni) := by
  exact godel_sondow_coupling_hypothesis_of_proof_complexity_for hpc
