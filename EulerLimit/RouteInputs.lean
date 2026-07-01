/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.InputCore

/-!
# Gamma Irrationality Route Inputs

Input records shared by the gamma irrationality route combinators.
-/

open Filter MiniHilbert

universe u v w

structure GammaIrrationalityFormulaCodeRealizationInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  hilbert_formula_code_realization :
    MiniHilbert.HilbertRightConjElimFormulaCodeRealization Ax A B halign

structure GammaIrrationalityVerifiedFormulaCodeRealizationInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  collapse_verification : SondowCollapseVerificationBridgePackage
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  hilbert_formula_code_realization :
    MiniHilbert.HilbertRightConjElimFormulaCodeRealization Ax A B halign

def GammaIrrationalityVerifiedFormulaCodeRealizationInputs.toFormulaCodeRealizationInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityVerifiedFormulaCodeRealizationInputs Ax A B halign) :
    GammaIrrationalityFormulaCodeRealizationInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification :=
    h.collapse_verification.toReflectionGraftConcreteVerification
  partial_payload_truth :=
    h.collapse_verification.toPayloadSpec.toPayloadTruth
  partial_payload_reading :=
    h.collapse_verification.toPayloadSpec.toIntendedReading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  hilbert_formula_code_realization := h.hilbert_formula_code_realization

structure GammaIrrationalityStandardFormulaCodeSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_semantics :
    MiniHilbert.StandardFormulaCodeProofLengthSemantics
      formula_code_interpretation

structure GammaIrrationalityVerifiedStandardFormulaCodeSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  collapse_verification : SondowCollapseVerificationBridgePackage
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_semantics :
    MiniHilbert.StandardFormulaCodeProofLengthSemantics
      formula_code_interpretation

def GammaIrrationalityVerifiedStandardFormulaCodeSemanticsInputs.toStandardInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityVerifiedStandardFormulaCodeSemanticsInputs
      Ax A B halign) :
    GammaIrrationalityStandardFormulaCodeSemanticsInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification :=
    h.collapse_verification.toReflectionGraftConcreteVerification
  partial_payload_truth :=
    h.collapse_verification.toPayloadSpec.toPayloadTruth
  partial_payload_reading :=
    h.collapse_verification.toPayloadSpec.toIntendedReading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_semantics := h.proof_length_semantics

structure GammaIrrationalityStandardFormulaCodeSemanticsCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_semantics :
    MiniHilbert.StandardFormulaCodeProofLengthSemantics
      formula_code_interpretation

structure GammaIrrationalityStandardSemanticsLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_semantics :
    MiniHilbert.StandardFormulaCodeProofLengthSemantics
      formula_code_interpretation
  semantic_partial_lower_bound :
    SemanticStrongProofLengthLowerBound
      formula_code_interpretation.localCheckedCodeProofLength
      partialConsistencyCode

structure GammaIrrationalityVerifiedStandardSemanticsLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  collapse_verification : SondowCollapseVerificationBridgePackage
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_semantics :
    MiniHilbert.StandardFormulaCodeProofLengthSemantics
      formula_code_interpretation
  semantic_partial_lower_bound :
    SemanticStrongProofLengthLowerBound
      formula_code_interpretation.localCheckedCodeProofLength
      partialConsistencyCode

def GammaIrrationalityVerifiedStandardSemanticsLowerBoundInputs.toStandardSemanticsLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : ℕ → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (h : GammaIrrationalityVerifiedStandardSemanticsLowerBoundInputs
      Ax A B halign) :
    GammaIrrationalityStandardSemanticsLowerBoundInputs Ax A B halign where
  sondow_forward := h.sondow_forward
  concrete_verification :=
    h.collapse_verification.toReflectionGraftConcreteVerification
  partial_payload_truth :=
    h.collapse_verification.toPayloadSpec.toPayloadTruth
  partial_payload_reading :=
    h.collapse_verification.toPayloadSpec.toIntendedReading
  buss_pudlak_rescaling := h.buss_pudlak_rescaling
  formula_code_interpretation := h.formula_code_interpretation
  proof_length_semantics := h.proof_length_semantics
  semantic_partial_lower_bound := h.semantic_partial_lower_bound

structure GammaIrrationalityPAHilbertFamilyExactnessInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_family_exactness :
    MiniHilbert.PAHilbertProjectionFamilyExactness
      formula_code_interpretation

structure GammaIrrationalityPAHilbertFamilyExactnessSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_family_exactness :
    MiniHilbert.PAHilbertProjectionFamilyExactness
      formula_code_interpretation
  semantic_partial_lower_bound :
    SemanticStrongProofLengthLowerBound
      formula_code_interpretation.localCheckedCodeProofLength
      partialConsistencyCode

structure GammaIrrationalityPureSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  semantic_short_verification :
    EventualSemanticShortVerificationBridge
      formula_code_interpretation.localCheckedCodeProofLength
      sondowReflectionGraftCode
  semantic_partial_lower_bound :
    SemanticStrongProofLengthLowerBound
      formula_code_interpretation.localCheckedCodeProofLength
      partialConsistencyCode

structure GammaIrrationalityPolynomialProofFamilySemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_proof_family_length_polynomial :
    is_polynomial_bound
      (MiniHilbert.nat_bound_as_real
        formula_code_interpretation.target_proof_family.length)
  semantic_partial_lower_bound :
    SemanticStrongProofLengthLowerBound
      formula_code_interpretation.localCheckedCodeProofLength
      partialConsistencyCode

structure GammaIrrationalityConcreteShortProofSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  semantic_partial_lower_bound :
    SemanticStrongProofLengthLowerBound
      formula_code_interpretation.localCheckedCodeProofLength
      partialConsistencyCode

structure GammaIrrationalityConcreteShortProofSourceLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  source_minChecked_lower_bound :
    SemanticStrongNatLowerBound
      formula_code_interpretation.target_proof_family.rightConjElim.minCheckedCodeSize

structure GammaIrrationalityConcreteShortProofSourceCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  source_minChecked_lower_bound :
    SemanticStrongNatLowerBound
      formula_code_interpretation.target_proof_family.rightConjElim.minCheckedCodeSize

structure GammaIrrationalityProofCodeModelSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback_length : FormulaCode → ℕ
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  semantic_partial_lower_bound :
    SemanticStrongProofLengthLowerBound
      (formula_code_interpretation.localHilbertSemanticProofLength fallback_length)
      partialConsistencyCode

structure GammaIrrationalityBussPudlakProofCodeModelSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback_length : FormulaCode → ℕ
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  source_minChecked_lower_bound :
    SemanticStrongNatLowerBound
      formula_code_interpretation.target_proof_family.rightConjElim.minCheckedCodeSize

structure GammaIrrationalityBussPudlakRescaledMinCheckedModelInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  scale : ℕ → ℕ
  scale_properties : PolynomialCofinalScale scale
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback_length : FormulaCode → ℕ
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  rescaled_source_minChecked_lower_bound :
    SemanticStrongNatLowerBound
      (fun k : ℕ =>
        formula_code_interpretation.target_proof_family.rightConjElim.minCheckedCodeSize
          (scale k))

structure GammaIrrationalityBussPudlakRescaledMinCheckedSourceInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  scale : ℕ → ℕ
  scale_properties : PolynomialCofinalScale scale
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  rescaled_source_minChecked_lower_bound :
    SemanticStrongNatLowerBound
      (fun k : ℕ =>
        formula_code_interpretation.target_proof_family.rightConjElim.minCheckedCodeSize
          (scale k))

structure GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  scale : ℕ → ℕ
  scale_properties : PolynomialCofinalScale scale
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  rescaled_source_minChecked_lower_bound :
    SemanticStrongNatLowerBound
      (fun k : ℕ =>
        formula_code_interpretation.target_proof_family.rightConjElim.minCheckedCodeSize
          (scale k))

structure PudlakFiniteConsistencyLowerBoundPackage where
  scale : ℕ → ℕ
  scale_properties : PolynomialCofinalScale scale
  rescaled_strong_lower_bound :
    StrongRescaledPartialConsistencyLowerBound scale

structure GammaIrrationalityBussPudlakSourceCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  source_minChecked_calibration :
    MiniHilbert.PartialConsistencySourceMinCheckedCalibration
      formula_code_interpretation

structure GammaIrrationalityBussPudlakSourceCalibratedCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  source_minChecked_calibration :
    MiniHilbert.PartialConsistencySourceMinCheckedCalibration
      formula_code_interpretation

structure GammaIrrationalityBussPudlakFamilyExactConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  proof_length_family_exactness :
    MiniHilbert.PAHilbertProjectionFamilyExactness formula_code_interpretation

structure GammaIrrationalityBussPudlakRecognitionConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  proof_length_recognition :
    MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition
      formula_code_interpretation

structure GammaIrrationalityBussPudlakCheckerConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  proof_code_checker_recognition :
    MiniHilbert.PAHilbertProofCodeCheckerRecognition formula_code_interpretation

structure GammaIrrationalityBussPudlakProofObjectConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  proof_length_eq_minProofCodeSize :
    ∀ code : FormulaCode,
      ∀ hcode : MiniHilbert.FormulaCodeHilbertRelevantCode code,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          formula_code_interpretation.localHilbertProofCodeSemantics.minProofCodeSize
            code hcode

structure GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  fallback_length : FormulaCode → ℕ
  proof_code_calibration :
    (formula_code_interpretation.localHilbertProofLengthCodeSemantics
      fallback_length).Calibration

structure GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  fallback_length : FormulaCode → ℕ
  proof_code_calibration :
    (formula_code_interpretation.localHilbertProofLengthCodeSemantics
      fallback_length).Calibration

structure GammaIrrationalityBussPudlakProofCodeCalibrationSpecCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_spec : PartialConsistencyPayloadSpec
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  target_short_proofs :
    MiniHilbert.ConcretePolynomialShortProofFamily
      Ax (fun m => A m ⊓ B m) (fun _ => True)
  fallback_length : FormulaCode → ℕ
  proof_code_calibration :
    (formula_code_interpretation.localHilbertProofLengthCodeSemantics
      fallback_length).Calibration

structure GammaIrrationalityPAHilbertRecognitionInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_recognition :
    MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition
      formula_code_interpretation

structure GammaIrrationalityPAHilbertVerifierProjectLengthInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback_length : FormulaCode → ℕ
  proof_length_eq_verifierProjectLength :
    ∀ code : FormulaCode,
      MiniHilbert.FormulaCodeHilbertRelevantCode code →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          formula_code_interpretation.localProofCodeSemantics.projectLength
            fallback_length code

structure GammaIrrationalityPAHilbertSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_recognition :
    MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition
      formula_code_interpretation
  semantic_partial_lower_bound :
    SemanticStrongProofLengthLowerBound
      formula_code_interpretation.localCheckedCodeProofLength
      partialConsistencyCode

structure GammaIrrationalityPAHilbertVerifierSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback_length : FormulaCode → ℕ
  proof_length_eq_verifierProjectLength :
    ∀ code : FormulaCode,
      MiniHilbert.FormulaCodeHilbertRelevantCode code →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          formula_code_interpretation.localProofCodeSemantics.projectLength
            fallback_length code
  semantic_partial_lower_bound :
    SemanticStrongProofLengthLowerBound
      formula_code_interpretation.localCheckedCodeProofLength
      partialConsistencyCode

structure GammaIrrationalityLocalFormulaCodeModelInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_local_calibration :
    MiniHilbert.FormulaCodeHilbertLocalCalibration formula_code_interpretation

structure GammaIrrationalityLocalFormulaCodeModelCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_local_calibration :
    MiniHilbert.FormulaCodeHilbertLocalCalibration formula_code_interpretation

structure GammaIrrationalityLocalFormulaCodeModelSpecCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_spec : PartialConsistencyPayloadSpec
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_local_calibration :
    MiniHilbert.FormulaCodeHilbertLocalCalibration formula_code_interpretation

structure GammaIrrationalityLocalCalibrationSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_local_calibration :
    MiniHilbert.FormulaCodeHilbertLocalCalibration formula_code_interpretation
  semantic_partial_lower_bound :
    SemanticStrongProofLengthLowerBound
      formula_code_interpretation.localCheckedCodeProofLength
      partialConsistencyCode

structure GammaIrrationalityProjectProofLengthSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_semantics :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      formula_code_interpretation.localProofLength
      MiniHilbert.FormulaCodeHilbertRelevantCode

structure GammaIrrationalityProjectProofLengthSemanticsCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_semantics :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      formula_code_interpretation.localProofLength
      MiniHilbert.FormulaCodeHilbertRelevantCode

structure GammaIrrationalityProjectCheckedCodeSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_semantics :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      formula_code_interpretation.localCheckedCodeProofLength
      MiniHilbert.FormulaCodeHilbertRelevantCode

structure GammaIrrationalityProjectCheckedCodeSemanticsCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_semantics :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      formula_code_interpretation.localCheckedCodeProofLength
      MiniHilbert.FormulaCodeHilbertRelevantCode

structure GammaIrrationalityProjectCheckedSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_semantics :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      formula_code_interpretation.localCheckedCodeProofLength
      MiniHilbert.FormulaCodeHilbertRelevantCode
  semantic_partial_lower_bound :
    SemanticStrongProofLengthLowerBound
      formula_code_interpretation.localCheckedCodeProofLength
      partialConsistencyCode

structure GammaIrrationalityLocalHilbertProofCodeSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_eq_minProofCodeSize :
    ∀ code : FormulaCode,
      ∀ hcode : MiniHilbert.FormulaCodeHilbertRelevantCode code,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          formula_code_interpretation.localHilbertProofCodeSemantics.minProofCodeSize
            code hcode

structure GammaIrrationalityLocalHilbertProofCodeSemanticsCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_eq_minProofCodeSize :
    ∀ code : FormulaCode,
      ∀ hcode : MiniHilbert.FormulaCodeHilbertRelevantCode code,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          formula_code_interpretation.localHilbertProofCodeSemantics.minProofCodeSize
            code hcode

structure GammaIrrationalityLocalProofCodeSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  proof_length_eq_minProofCodeSize :
    ∀ code : FormulaCode,
      ∀ hcode : MiniHilbert.FormulaCodeHilbertRelevantCode code,
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          formula_code_interpretation.localHilbertProofCodeSemantics.minProofCodeSize
            code hcode
  semantic_partial_lower_bound :
    SemanticStrongProofLengthLowerBound
      formula_code_interpretation.localCheckedCodeProofLength
      partialConsistencyCode

structure GammaIrrationalitySemanticProofLengthInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  partial_payload_reading : PartialConsistencyPayloadIntendedReading
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback_length : FormulaCode → ℕ
  proof_length_eq_semanticProofLength :
    ∀ code : FormulaCode,
      MiniHilbert.FormulaCodeHilbertRelevantCode code →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          formula_code_interpretation.localHilbertSemanticProofLength
            fallback_length code

structure GammaIrrationalitySemanticProofLengthCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n)
    (halign : HilbertProjectionCodeAlignment) where
  sondow_forward : SondowForwardInputs
  concrete_verification : ReflectionGraftConcreteVerificationPackage
  partial_payload_truth : PartialConsistencyPayloadTruth
  buss_pudlak_rescaling : BussPudlakTimeConstructibleRescalingTheorem
  formula_code_interpretation :
    MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign
  fallback_length : FormulaCode → ℕ
  proof_length_eq_semanticProofLength :
    ∀ code : FormulaCode,
      MiniHilbert.FormulaCodeHilbertRelevantCode code →
        proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
          formula_code_interpretation.localHilbertSemanticProofLength
            fallback_length code
