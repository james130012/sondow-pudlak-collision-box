/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.RouteInputs

/-!
# Gamma Irrationality Route Defaults

Default route-input abbreviations using the canonical true Hilbert projection
code alignment.
-/

open Filter MiniHilbert

universe u v w

abbrev GammaIrrationalityDefaultFormulaCodeRealizationInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityFormulaCodeRealizationInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultVerifiedFormulaCodeRealizationInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityVerifiedFormulaCodeRealizationInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultStandardFormulaCodeSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityStandardFormulaCodeSemanticsInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultVerifiedStandardFormulaCodeSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityVerifiedStandardFormulaCodeSemanticsInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultStandardFormulaCodeSemanticsCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityStandardFormulaCodeSemanticsCoreInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultStandardSemanticsLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityStandardSemanticsLowerBoundInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultVerifiedStandardSemanticsLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityVerifiedStandardSemanticsLowerBoundInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultPAHilbertFamilyExactnessInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityPAHilbertFamilyExactnessInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultPAHilbertFamilyExactnessSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityPAHilbertFamilyExactnessSemanticLowerBoundInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultPureSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityPureSemanticLowerBoundInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultPolynomialProofFamilySemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityPolynomialProofFamilySemanticInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultConcreteShortProofSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityConcreteShortProofSemanticInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultConcreteShortProofSourceLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityConcreteShortProofSourceLowerBoundInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultConcreteShortProofSourceCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityConcreteShortProofSourceCoreInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultProofCodeModelSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityProofCodeModelSemanticInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultBussPudlakProofCodeModelSemanticInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityBussPudlakProofCodeModelSemanticInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultBussPudlakRescaledMinCheckedModelInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityBussPudlakRescaledMinCheckedModelInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultBussPudlakRescaledMinCheckedSourceInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityBussPudlakRescaledMinCheckedSourceInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultBussPudlakRescaledMinCheckedCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityBussPudlakRescaledMinCheckedCoreInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultBussPudlakSourceCalibratedInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityBussPudlakSourceCalibratedInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultBussPudlakSourceCalibratedCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityBussPudlakSourceCalibratedCoreInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultBussPudlakFamilyExactConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityBussPudlakFamilyExactConcreteInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultBussPudlakRecognitionConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityBussPudlakRecognitionConcreteInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultBussPudlakCheckerConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityBussPudlakCheckerConcreteInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultBussPudlakProofObjectConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityBussPudlakProofObjectConcreteInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultBussPudlakProofCodeCalibrationConcreteInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityBussPudlakProofCodeCalibrationConcreteInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultBussPudlakProofCodeCalibrationCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityBussPudlakProofCodeCalibrationCoreInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultPAHilbertRecognitionInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityPAHilbertRecognitionInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultPAHilbertVerifierProjectLengthInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityPAHilbertVerifierProjectLengthInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultPAHilbertSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityPAHilbertSemanticLowerBoundInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultPAHilbertVerifierSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityPAHilbertVerifierSemanticLowerBoundInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultLocalFormulaCodeModelInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityLocalFormulaCodeModelInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultLocalFormulaCodeModelCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityLocalFormulaCodeModelCoreInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultLocalCalibrationSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityLocalCalibrationSemanticLowerBoundInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultProjectProofLengthSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityProjectProofLengthSemanticsInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultProjectProofLengthSemanticsCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityProjectProofLengthSemanticsCoreInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultProjectCheckedCodeSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityProjectCheckedCodeSemanticsInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultProjectCheckedCodeSemanticsCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityProjectCheckedCodeSemanticsCoreInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultProjectCheckedSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityProjectCheckedSemanticLowerBoundInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultLocalHilbertProofCodeSemanticsInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityLocalHilbertProofCodeSemanticsInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultLocalHilbertProofCodeSemanticsCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityLocalHilbertProofCodeSemanticsCoreInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultLocalProofCodeSemanticLowerBoundInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalityLocalProofCodeSemanticLowerBoundInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultSemanticProofLengthInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalitySemanticProofLengthInputs
    Ax A B hilbert_projection_code_alignment_true

abbrev GammaIrrationalityDefaultSemanticProofLengthCoreInputs
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : ℕ}
    (Ax : L.BoundedFormula α n → Prop)
    (A B : ℕ → L.BoundedFormula α n) :=
  GammaIrrationalitySemanticProofLengthCoreInputs
    Ax A B hilbert_projection_code_alignment_true
