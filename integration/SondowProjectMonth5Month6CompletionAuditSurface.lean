/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth5Month6PublicKernelSurface

/-!
# Month 5/Month 6 completion audit surface

This module is the public audit endpoint for the Month 5/Month 6 route.  It
does not introduce a new proof path: it packages the combined-upper gap
certificate and the checked-code proof-length replacement certificate at the
same entrypoint as the Month 3/Month 4 public completion certificate.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth5Month6CompletionAuditSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4CompletionAuditSurface
open SondowProjectMonth5Month6PublicKernelSurface

structure Month5Month6CompletionAuditCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) where
  combined_kernel :
    LayeredPublicKernelCombinedUpperCertificate
      interp rootSide MainRationality SondowAccepted bounds

structure Month5Month6ThresholdCompletionAuditCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) where
  threshold_kernel :
    LayeredPublicKernelThresholdCertificate
      interp rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds)

structure Month5Month6CheckedCodeOnlyCompletionCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) where
  public_completion :
    PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds)
  month5_combined_gap :
    Month5CombinedUpperGapCertificate MainRationality SondowAccepted bounds
  month6_free_closure :
    _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFreeLocalCodeClosure
      interp

abbrev Month5Month6CompletionAuditStatement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  LayeredPublicKernelCombinedUpperStatement
    interp rootSide MainRationality SondowAccepted bounds

abbrev Month5Month6ThresholdCompletionAuditStatement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  LayeredPublicKernelThresholdCheckedStatement
    interp rootSide MainRationality SondowAccepted bounds
    (Month5SondowCombinedUpperBound bounds)

abbrev Month5Month6ExplicitChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
      Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      Nonempty (Month6CheckedCodeReplacementCertificate interp)

abbrev Month5Month6ProjectBaseChecklist
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds)

abbrev Month5Month6CheckedCodeOnlyChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      Nonempty
        (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFreeLocalCodeClosure
          interp)

abbrev Month6InternalizationAuditCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthInternalizationAuditCertificate
    interp

abbrev Month5Month6DecomposedInternalizationChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      Nonempty
        (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFreeLocalCodeClosure
          interp) ∧
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ExactLocalProofCodeSemanticsCertificate
            interp)

abbrev Month5Month6ResidualExactnessChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      Nonempty
        (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ExactLocalProofCodeSemanticsCertificate
          interp)

abbrev Month5Month6TwoFamilyResidualExactnessChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      Nonempty
        (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6TwoFamilyResidualExactnessCertificate
          interp)

abbrev Month5Month6ProofLengthBoundaryChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      Nonempty
        (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6TwoFamilyProofLengthBoundaryCertificate
          interp)

abbrev Month5Month6ProjectProofLengthSemanticsChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode

abbrev Month5Month6FreeClosureProjectSemanticsChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      Nonempty
        (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFreeLocalCodeClosure
          interp) ∧
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode

abbrev Month5Month6ProofLengthAxiomFrontierChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthAxiomFrontier
        interp

abbrev Month5Month6ProjectBaseEncoderBoundaryChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  Month5Month6ProjectBaseChecklist
      rootSide MainRationality SondowAccepted bounds ∧
    Nonempty
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderBoundaryCertificate
        interp)

abbrev Month5Month6ProjectBaseCheckerEncoderChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  Month5Month6ProjectBaseChecklist
      rootSide MainRationality SondowAccepted bounds ∧
    Nonempty (_root_.MiniHilbert.PAHilbertLocalCheckerExactness interp) ∧
      Nonempty
        (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderBoundaryCertificate
          interp)

abbrev Month5Month6ProjectBaseEncoderConventionChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  Month5Month6ProjectBaseChecklist
      rootSide MainRationality SondowAccepted bounds ∧
    Nonempty
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderConventionBoundaryCertificate
        interp)

abbrev Month5Month6ProjectBaseTwoFamilyLengthSemanticsChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  Month5Month6ProjectBaseChecklist
      rootSide MainRationality SondowAccepted bounds ∧
    Nonempty
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderTwoFamilyLengthSemanticsCertificate
        interp)

abbrev Month5Month6ProjectBaseSeparatedEncoderLengthChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  Month5Month6ProjectBaseChecklist
      rootSide MainRationality SondowAccepted bounds ∧
    Nonempty
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6SeparatedTwoFamilyEncoderLengthCertificate
        interp)

abbrev Month5Month6ProjectBaseFrontierSplitChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  Month5Month6ProjectBaseChecklist
      rootSide MainRationality SondowAccepted bounds ∧
    Nonempty
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFrontierSplitCertificate
        interp)

abbrev Month5Month6ProjectBaseProofCodeCheckerFrontierChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  Month5Month6ProjectBaseChecklist
      rootSide MainRationality SondowAccepted bounds ∧
    Nonempty
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofCodeCheckerFrontierCertificate
        interp)

abbrev Month5Month6ProjectBaseCheckerCalibrationFrontierChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  Month5Month6ProjectBaseChecklist
      rootSide MainRationality SondowAccepted bounds ∧
    Nonempty
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofCodeCheckerCalibrationFrontierCertificate
        interp)

abbrev Month5Month6ThresholdSearchAuditChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      Nonempty (Month5ThresholdSearchCertificate bounds) ∧
        Nonempty (Month6InternalizationAuditCertificate interp)

abbrev Month5Month6MonotoneThresholdAuditChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      Nonempty (Month5FinalExpressionMonotoneGapPersistenceCertificate
        bounds) ∧
        Nonempty (Month6InternalizationAuditCertificate interp)

abbrev Month5Month6GapDifferenceThresholdAuditChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      Nonempty (Month5FinalExpressionGapDifferencePersistenceCertificate
        bounds) ∧
        Nonempty (Month6InternalizationAuditCertificate interp)

abbrev Month5Month6EventualGapDifferenceThresholdAuditChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      Nonempty
        (Month5FinalExpressionEventualGapDifferencePersistenceCertificate
          bounds) ∧
        Nonempty (Month6InternalizationAuditCertificate interp)

abbrev Month5Month6StepGapDifferenceThresholdAuditChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) ∧
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ∧
      Nonempty
        (Month5FinalExpressionStepGapDifferencePersistenceCertificate
          bounds) ∧
        Nonempty (Month6InternalizationAuditCertificate interp)

theorem completion_audit_statement_iff_explicit_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ExplicitChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  Iff.rfl

theorem checked_code_only_certificate_nonempty_iff_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Nonempty
        (Month5Month6CheckedCodeOnlyCompletionCertificate
          interp rootSide MainRationality SondowAccepted bounds) ↔
      Month5Month6CheckedCodeOnlyChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact
      ⟨cert.public_completion,
        ⟨cert.month5_combined_gap⟩,
        ⟨cert.month6_free_closure⟩⟩
  · intro hchecklist
    rcases hchecklist with ⟨hcompletion, hgap, hfree⟩
    rcases hgap with ⟨gap⟩
    rcases hfree with ⟨free⟩
    exact ⟨{
      public_completion := hcompletion
      month5_combined_gap := gap
      month6_free_closure := free }⟩

theorem checked_code_only_checklist_iff_public_completion_and_gap
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CheckedCodeOnlyChecklist
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (Month5CombinedUpperGapCertificate
          MainRationality SondowAccepted bounds) := by
  constructor
  · intro hchecklist
    rcases hchecklist with ⟨hcompletion, hgap, _hfree⟩
    exact ⟨hcompletion, hgap⟩
  · intro hbase
    rcases hbase with ⟨hcompletion, hgap⟩
    have hfree :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFreeLocalCodeClosure
            interp) :=
      _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ProofLengthFreeLocalCodeClosure_nonempty
        interp
    exact ⟨hcompletion, hgap, hfree⟩

theorem checked_code_only_checklist_iff_project_base_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CheckedCodeOnlyChecklist
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ProjectBaseChecklist
        rootSide MainRationality SondowAccepted bounds :=
  checked_code_only_checklist_iff_public_completion_and_gap
    interp rootSide MainRationality SondowAccepted bounds

theorem month5_combined_gap_nonempty_iff_computable_gap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} :
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ↔
      Nonempty (ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds
        (Month5SondowCombinedUpperBound bounds)) :=
  month5CombinedUpperGapCertificate_nonempty_iff_computableGap_nonempty

theorem project_base_checklist_iff_public_completion_and_computable_gap
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6ProjectBaseChecklist
        rootSide MainRationality SondowAccepted bounds ↔
      PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds)) := by
  constructor
  · intro hbase
    rcases hbase with ⟨hcompletion, hgap⟩
    exact
      ⟨hcompletion,
        (month5_combined_gap_nonempty_iff_computable_gap).1 hgap⟩
  · intro hbase
    rcases hbase with ⟨hcompletion, hcomputable⟩
    exact
      ⟨hcompletion,
        (month5_combined_gap_nonempty_iff_computable_gap).2 hcomputable⟩

theorem month6_checked_replacement_iff_project_checked_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
  month6_checked_replacement_nonempty_iff_project_checked_semantics interp

theorem month6_checked_replacement_iff_proof_length_code_calibration
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback_length : _root_.FormulaCode → Nat) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      (interp.localHilbertProofLengthCodeSemantics
        fallback_length).Calibration :=
  month6_checked_replacement_nonempty_iff_proof_length_code_calibration
    interp fallback_length

theorem month6_checked_replacement_iff_local_convention_certificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      Nonempty
        (_root_.MiniHilbert.PAHilbertLocalProofCodeConventionCertificate
          interp) :=
  month6_checked_replacement_nonempty_iff_local_convention_certificate interp

theorem month6_checked_replacement_iff_internalization_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      Nonempty (Month6InternalizationAuditCertificate interp) :=
  (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ProofLengthInternalizationAudit_nonempty_iff_checkedReplacement
    interp).symm

theorem completion_audit_statement_iff_decomposed_internalization_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6DecomposedInternalizationChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    rcases hstatement with ⟨hcompletion, hgap, hreplacement⟩
    have hsplit :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_freeClosure_and_exactLocal
        interp).1 hreplacement
    exact ⟨hcompletion, ⟨hgap, hsplit⟩⟩
  · intro hchecklist
    rcases hchecklist with
      ⟨hcompletion, hgap, hfree, hexact⟩
    have hreplacement :
        Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_freeClosure_and_exactLocal
        interp).2 ⟨hfree, hexact⟩
    exact ⟨hcompletion, hgap, hreplacement⟩

theorem completion_audit_statement_iff_residual_exactness_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ResidualExactnessChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    have hdecomposed :=
      (completion_audit_statement_iff_decomposed_internalization_checklist
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hdecomposed with ⟨hcompletion, hgap, _hfree, hexact⟩
    exact ⟨hcompletion, hgap, hexact⟩
  · intro hchecklist
    rcases hchecklist with ⟨hcompletion, hgap, hexact⟩
    have hfree :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFreeLocalCodeClosure
            interp) :=
      _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ProofLengthFreeLocalCodeClosure_nonempty
        interp
    exact
      (completion_audit_statement_iff_decomposed_internalization_checklist
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hcompletion, hgap, hfree, hexact⟩

theorem completion_audit_statement_iff_two_family_residual_exactness_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6TwoFamilyResidualExactnessChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    have hresidual :=
      (completion_audit_statement_iff_residual_exactness_checklist
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hresidual with ⟨hcompletion, hgap, hexact⟩
    have htwo :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6TwoFamilyResidualExactnessCertificate
            interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ExactLocalProofCodeSemantics_nonempty_iff_twoFamilyResidualExactness
        interp).1 hexact
    exact ⟨hcompletion, hgap, htwo⟩
  · intro hchecklist
    rcases hchecklist with ⟨hcompletion, hgap, htwo⟩
    have hexact :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ExactLocalProofCodeSemanticsCertificate
            interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ExactLocalProofCodeSemantics_nonempty_iff_twoFamilyResidualExactness
        interp).2 htwo
    exact
      (completion_audit_statement_iff_residual_exactness_checklist
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hcompletion, hgap, hexact⟩

theorem completion_audit_statement_iff_proof_length_boundary_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ProofLengthBoundaryChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    have htwo :=
      (completion_audit_statement_iff_two_family_residual_exactness_checklist
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases htwo with ⟨hcompletion, hgap, hresidual⟩
    have hboundary :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6TwoFamilyProofLengthBoundaryCertificate
            interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6TwoFamilyResidualExactness_nonempty_iff_proofLengthBoundary
        interp).1 hresidual
    exact ⟨hcompletion, hgap, hboundary⟩
  · intro hchecklist
    rcases hchecklist with ⟨hcompletion, hgap, hboundary⟩
    have hresidual :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6TwoFamilyResidualExactnessCertificate
            interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6TwoFamilyResidualExactness_nonempty_iff_proofLengthBoundary
        interp).2 hboundary
    exact
      (completion_audit_statement_iff_two_family_residual_exactness_checklist
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hcompletion, hgap, hresidual⟩

theorem completion_audit_statement_iff_project_proof_length_semantics_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ProjectProofLengthSemanticsChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    rcases hstatement with ⟨hcompletion, hgap, hreplacement⟩
    have hsem :
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
      (month6_checked_replacement_iff_project_checked_semantics interp).1
        hreplacement
    exact ⟨hcompletion, hgap, hsem⟩
  · intro hchecklist
    rcases hchecklist with ⟨hcompletion, hgap, hsem⟩
    have hreplacement :
        Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
      (month6_checked_replacement_iff_project_checked_semantics interp).2
        hsem
    exact ⟨hcompletion, hgap, hreplacement⟩

theorem completion_audit_statement_iff_free_closure_project_semantics_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6FreeClosureProjectSemanticsChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    rcases hstatement with ⟨hcompletion, hgap, hreplacement⟩
    have hsplit :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_freeClosure_and_projectCheckedSemantics
        interp).1 hreplacement
    exact ⟨hcompletion, hgap, hsplit⟩
  · intro hchecklist
    rcases hchecklist with ⟨hcompletion, hgap, hsplit⟩
    have hreplacement :
        Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_freeClosure_and_projectCheckedSemantics
        interp).2 hsplit
    exact ⟨hcompletion, hgap, hreplacement⟩

theorem completion_audit_statement_iff_checked_code_only_and_project_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6CheckedCodeOnlyChecklist
        interp rootSide MainRationality SondowAccepted bounds ∧
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode := by
  constructor
  · intro hstatement
    rcases hstatement with ⟨hcompletion, hgap, hreplacement⟩
    have hsplit :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_freeClosure_and_projectCheckedSemantics
        interp).1 hreplacement
    rcases hsplit with ⟨hfree, hsemantics⟩
    exact ⟨⟨hcompletion, hgap, hfree⟩, hsemantics⟩
  · intro hsplit
    rcases hsplit with ⟨hchecked, hsemantics⟩
    rcases hchecked with ⟨hcompletion, hgap, hfree⟩
    have hreplacement :
        Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_freeClosure_and_projectCheckedSemantics
        interp).2 ⟨hfree, hsemantics⟩
    exact ⟨hcompletion, hgap, hreplacement⟩

theorem completion_audit_statement_iff_project_base_and_month6_project_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ProjectBaseChecklist
          rootSide MainRationality SondowAccepted bounds ∧
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode := by
  constructor
  · intro hstatement
    rcases hstatement with ⟨hcompletion, hgap, hreplacement⟩
    have hsemantics :
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
      (month6_checked_replacement_iff_project_checked_semantics interp).1
        hreplacement
    exact ⟨⟨hcompletion, hgap⟩, hsemantics⟩
  · intro hsplit
    rcases hsplit with ⟨hbase, hsemantics⟩
    rcases hbase with ⟨hcompletion, hgap⟩
    have hreplacement :
        Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
      (month6_checked_replacement_iff_project_checked_semantics interp).2
        hsemantics
    exact ⟨hcompletion, hgap, hreplacement⟩

theorem completion_audit_statement_iff_project_base_encoder_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ProjectBaseEncoderBoundaryChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hsemantics⟩
    have hencoder :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderBoundaryCertificate
            interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_encoderBoundary
        interp).1 hsemantics
    exact ⟨hbase, hencoder⟩
  · intro hchecklist
    rcases hchecklist with ⟨hbase, hencoder⟩
    have hsemantics :
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_encoderBoundary
        interp).2 hencoder
    exact
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hsemantics⟩

theorem completion_audit_statement_iff_project_base_encoder_convention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ProjectBaseEncoderConventionChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hsemantics⟩
    have hboundary :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderConventionBoundaryCertificate
            interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_encoderConventionBoundary
        interp).1 hsemantics
    exact ⟨hbase, hboundary⟩
  · intro hchecklist
    rcases hchecklist with ⟨hbase, hboundary⟩
    have hsemantics :
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_encoderConventionBoundary
        interp).2 hboundary
    exact
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hsemantics⟩

theorem completion_audit_statement_iff_project_base_two_family_length_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ProjectBaseTwoFamilyLengthSemanticsChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hsemantics⟩
    have htwo :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderTwoFamilyLengthSemanticsCertificate
            interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_twoFamilyLengthSemantics
        interp).1 hsemantics
    exact ⟨hbase, htwo⟩
  · intro hchecklist
    rcases hchecklist with ⟨hbase, htwo⟩
    have hsemantics :
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_twoFamilyLengthSemantics
        interp).2 htwo
    exact
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hsemantics⟩

theorem completion_audit_statement_iff_project_base_separated_encoder_length
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ProjectBaseSeparatedEncoderLengthChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hsemantics⟩
    have hseparated :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6SeparatedTwoFamilyEncoderLengthCertificate
            interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_separatedEncoderLength
        interp).1 hsemantics
    exact ⟨hbase, hseparated⟩
  · intro hchecklist
    rcases hchecklist with ⟨hbase, hseparated⟩
    have hsemantics :
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_separatedEncoderLength
        interp).2 hseparated
    exact
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hsemantics⟩

theorem completion_audit_statement_iff_project_base_frontier_split
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ProjectBaseFrontierSplitChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hsemantics⟩
    have hfrontier :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFrontierSplitCertificate
            interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_frontierSplit
        interp).1 hsemantics
    exact ⟨hbase, hfrontier⟩
  · intro hchecklist
    rcases hchecklist with ⟨hbase, hfrontier⟩
    have hsemantics :
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_frontierSplit
        interp).2 hfrontier
    exact
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hsemantics⟩

theorem completion_audit_statement_iff_project_base_proof_code_checker_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ProjectBaseProofCodeCheckerFrontierChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hsemantics⟩
    have hchecker :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofCodeCheckerFrontierCertificate
            interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_proofCodeCheckerFrontier
        interp).1 hsemantics
    exact ⟨hbase, hchecker⟩
  · intro hchecklist
    rcases hchecklist with ⟨hbase, hchecker⟩
    have hsemantics :
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_proofCodeCheckerFrontier
        interp).2 hchecker
    exact
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hsemantics⟩

theorem completion_audit_statement_iff_project_base_checker_calibration_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ProjectBaseCheckerCalibrationFrontierChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hsemantics⟩
    have hchecker :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofCodeCheckerCalibrationFrontierCertificate
            interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_checkerCalibrationFrontier
        interp).1 hsemantics
    exact ⟨hbase, hchecker⟩
  · intro hchecklist
    rcases hchecklist with ⟨hbase, hchecker⟩
    have hsemantics :
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_checkerCalibrationFrontier
        interp).2 hchecker
    exact
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hsemantics⟩

theorem completion_audit_statement_iff_public_completion_computable_gap_encoder_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderBoundaryCertificate
            interp) := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_encoder_boundary
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hencoder⟩
    have hbase' :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).1 hbase
    exact ⟨hbase', hencoder⟩
  · intro hsplit
    rcases hsplit with ⟨hbase', hencoder⟩
    have hbase :
        Month5Month6ProjectBaseChecklist
          rootSide MainRationality SondowAccepted bounds :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).2 hbase'
    exact
      (completion_audit_statement_iff_project_base_encoder_boundary
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hencoder⟩

theorem completion_audit_statement_iff_public_completion_computable_gap_encoder_convention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderConventionBoundaryCertificate
            interp) := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_encoder_convention
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hboundary⟩
    have hbase' :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).1 hbase
    exact ⟨hbase', hboundary⟩
  · intro hsplit
    rcases hsplit with ⟨hbase', hboundary⟩
    have hbase :
        Month5Month6ProjectBaseChecklist
          rootSide MainRationality SondowAccepted bounds :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).2 hbase'
    exact
      (completion_audit_statement_iff_project_base_encoder_convention
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hboundary⟩

theorem completion_audit_statement_iff_public_completion_computable_gap_two_family_length_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderTwoFamilyLengthSemanticsCertificate
            interp) := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_two_family_length_semantics
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, htwo⟩
    have hbase' :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).1 hbase
    exact ⟨hbase', htwo⟩
  · intro hsplit
    rcases hsplit with ⟨hbase', htwo⟩
    have hbase :
        Month5Month6ProjectBaseChecklist
          rootSide MainRationality SondowAccepted bounds :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).2 hbase'
    exact
      (completion_audit_statement_iff_project_base_two_family_length_semantics
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, htwo⟩

theorem completion_audit_statement_iff_public_completion_computable_gap_separated_encoder_length
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6SeparatedTwoFamilyEncoderLengthCertificate
            interp) := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_separated_encoder_length
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hseparated⟩
    have hbase' :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).1 hbase
    exact ⟨hbase', hseparated⟩
  · intro hsplit
    rcases hsplit with ⟨hbase', hseparated⟩
    have hbase :
        Month5Month6ProjectBaseChecklist
          rootSide MainRationality SondowAccepted bounds :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).2 hbase'
    exact
      (completion_audit_statement_iff_project_base_separated_encoder_length
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hseparated⟩

theorem completion_audit_statement_iff_public_completion_computable_gap_frontier_split
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFrontierSplitCertificate
            interp) := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_frontier_split
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hfrontier⟩
    have hbase' :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).1 hbase
    exact ⟨hbase', hfrontier⟩
  · intro hsplit
    rcases hsplit with ⟨hbase', hfrontier⟩
    have hbase :
        Month5Month6ProjectBaseChecklist
          rootSide MainRationality SondowAccepted bounds :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).2 hbase'
    exact
      (completion_audit_statement_iff_project_base_frontier_split
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hfrontier⟩

theorem completion_audit_statement_iff_public_completion_computable_gap_proof_code_checker_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofCodeCheckerFrontierCertificate
            interp) := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_proof_code_checker_frontier
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hchecker⟩
    have hbase' :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).1 hbase
    exact ⟨hbase', hchecker⟩
  · intro hsplit
    rcases hsplit with ⟨hbase', hchecker⟩
    have hbase :
        Month5Month6ProjectBaseChecklist
          rootSide MainRationality SondowAccepted bounds :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).2 hbase'
    exact
      (completion_audit_statement_iff_project_base_proof_code_checker_frontier
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hchecker⟩

theorem completion_audit_statement_iff_public_completion_computable_gap_checker_calibration_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofCodeCheckerCalibrationFrontierCertificate
            interp) := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_checker_calibration_frontier
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hchecker⟩
    have hbase' :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).1 hbase
    exact ⟨hbase', hchecker⟩
  · intro hsplit
    rcases hsplit with ⟨hbase', hchecker⟩
    have hbase :
        Month5Month6ProjectBaseChecklist
          rootSide MainRationality SondowAccepted bounds :=
      (project_base_checklist_iff_public_completion_and_computable_gap
        rootSide MainRationality SondowAccepted bounds).2 hbase'
    exact
      (completion_audit_statement_iff_project_base_checker_calibration_frontier
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hchecker⟩

theorem completion_audit_statement_iff_project_base_checker_encoder
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ProjectBaseCheckerEncoderChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    have hsplit :=
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).1
        hstatement
    rcases hsplit with ⟨hbase, hsemantics⟩
    have hfrontier :
        Nonempty (_root_.MiniHilbert.PAHilbertLocalCheckerExactness interp) ∧
          Nonempty
            (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderBoundaryCertificate
              interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_checker_and_encoder
        interp).1 hsemantics
    exact ⟨hbase, hfrontier⟩
  · intro hchecklist
    rcases hchecklist with ⟨hbase, hfrontier⟩
    have hsemantics :
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_checker_and_encoder
        interp).2 hfrontier
    exact
      (completion_audit_statement_iff_project_base_and_month6_project_semantics
        interp rootSide MainRationality SondowAccepted bounds).2
        ⟨hbase, hsemantics⟩

theorem completion_audit_statement_iff_proof_length_axiom_frontier_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ProofLengthAxiomFrontierChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    rcases hstatement with ⟨hcompletion, hgap, hreplacement⟩
    have hfrontier :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_proofLengthAxiomFrontier
        interp).1 hreplacement
    exact ⟨hcompletion, hgap, hfrontier⟩
  · intro hchecklist
    rcases hchecklist with ⟨hcompletion, hgap, hfrontier⟩
    have hreplacement :
        Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_proofLengthAxiomFrontier
        interp).2 hfrontier
    exact ⟨hcompletion, hgap, hreplacement⟩

theorem threshold_completion_statement_iff_threshold_search_audit_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6ThresholdCompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6ThresholdSearchAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hstatement
    rcases hstatement with ⟨hcompletion, hthreshold, hreplacement⟩
    have hcombined :
        Nonempty (Month5CombinedUpperThresholdCertificate
          MainRationality SondowAccepted bounds) := by
      rcases hthreshold with ⟨threshold⟩
      exact ⟨{ threshold_gap := threshold }⟩
    have hsplit :=
      (month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_thresholdSearch).1
        hcombined
    have haudit :
        Nonempty (Month6InternalizationAuditCertificate interp) :=
      (month6_checked_replacement_iff_internalization_audit interp).1
        hreplacement
    exact ⟨hcompletion, ⟨hsplit.1, ⟨hsplit.2, haudit⟩⟩⟩
  · intro hchecklist
    rcases hchecklist with
      ⟨hcompletion, hgap, hsearch, haudit⟩
    have hcombined :
        Nonempty (Month5CombinedUpperThresholdCertificate
          MainRationality SondowAccepted bounds) :=
      (month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_thresholdSearch).2
        ⟨hgap, hsearch⟩
    rcases hcombined with ⟨combined⟩
    have hreplacement :
        Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
      (month6_checked_replacement_iff_internalization_audit interp).2
        haudit
    exact
      ⟨hcompletion, ⟨combined.threshold_gap⟩, hreplacement⟩

theorem monotone_threshold_audit_checklist_to_threshold_completion_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (hchecklist :
      Month5Month6MonotoneThresholdAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds) :
    Month5Month6ThresholdCompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds := by
  rcases hchecklist with
    ⟨hcompletion, hgap, hmono, haudit⟩
  have hfinal :
      Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
    month5CombinedUpperGap_and_monotonePersistence_to_finalExpressionThreshold
      hgap hmono
  have hcombined :
      Nonempty (Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds) :=
    (month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_finalExpression).2
      ⟨hgap, hfinal⟩
  rcases hcombined with ⟨combined⟩
  have hreplacement :
      Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
    (month6_checked_replacement_iff_internalization_audit interp).2
      haudit
  exact ⟨hcompletion, ⟨combined.threshold_gap⟩, hreplacement⟩

theorem gap_difference_threshold_audit_checklist_to_threshold_completion_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (hchecklist :
      Month5Month6GapDifferenceThresholdAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds) :
    Month5Month6ThresholdCompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds := by
  rcases hchecklist with
    ⟨hcompletion, hgap, hdiff, haudit⟩
  have hfinal :
      Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
    month5CombinedUpperGap_and_gapDifferencePersistence_to_finalExpressionThreshold
      hgap hdiff
  have hcombined :
      Nonempty (Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds) :=
    (month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_finalExpression).2
      ⟨hgap, hfinal⟩
  rcases hcombined with ⟨combined⟩
  have hreplacement :
      Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
    (month6_checked_replacement_iff_internalization_audit interp).2
      haudit
  exact ⟨hcompletion, ⟨combined.threshold_gap⟩, hreplacement⟩

theorem eventual_gap_difference_threshold_audit_checklist_to_threshold_completion_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (hchecklist :
      Month5Month6EventualGapDifferenceThresholdAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds) :
    Month5Month6ThresholdCompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds := by
  rcases hchecklist with
    ⟨hcompletion, hgap, hdiff, haudit⟩
  have hfinal :
      Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
    month5CombinedUpperGap_and_eventualGapDifference_to_finalExpressionThreshold
      hgap hdiff
  have hcombined :
      Nonempty (Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds) :=
    (month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_finalExpression).2
      ⟨hgap, hfinal⟩
  rcases hcombined with ⟨combined⟩
  have hreplacement :
      Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
    (month6_checked_replacement_iff_internalization_audit interp).2
      haudit
  exact ⟨hcompletion, ⟨combined.threshold_gap⟩, hreplacement⟩

theorem step_gap_difference_threshold_audit_checklist_to_threshold_completion_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (hchecklist :
      Month5Month6StepGapDifferenceThresholdAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds) :
    Month5Month6ThresholdCompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds := by
  rcases hchecklist with
    ⟨hcompletion, hgap, hstep, haudit⟩
  have hfinal :
      Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
    month5CombinedUpperGap_and_stepGapDifference_to_finalExpressionThreshold
      hgap hstep
  have hcombined :
      Nonempty (Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds) :=
    (month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_finalExpression).2
      ⟨hgap, hfinal⟩
  rcases hcombined with ⟨combined⟩
  have hreplacement :
      Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
    (month6_checked_replacement_iff_internalization_audit interp).2
      haudit
  exact ⟨hcompletion, ⟨combined.threshold_gap⟩, hreplacement⟩

theorem completion_audit_nonempty_iff_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Nonempty
        (Month5Month6CompletionAuditCertificate
          interp rootSide MainRationality SondowAccepted bounds) ↔
      Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact
      (layered_public_kernel_combined_upper_nonempty_iff_statement
        interp rootSide MainRationality SondowAccepted bounds).1
        ⟨cert.combined_kernel⟩
  · intro hstatement
    rcases
      (layered_public_kernel_combined_upper_nonempty_iff_statement
        interp rootSide MainRationality SondowAccepted bounds).2
        hstatement with
      ⟨kernel⟩
    exact ⟨{ combined_kernel := kernel }⟩

theorem completion_audit_statement_iff_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Nonempty
        (Month5Month6CompletionAuditCertificate
          interp rootSide MainRationality SondowAccepted bounds) :=
  (completion_audit_nonempty_iff_statement
    interp rootSide MainRationality SondowAccepted bounds).symm

theorem threshold_completion_audit_nonempty_iff_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Nonempty
        (Month5Month6ThresholdCompletionAuditCertificate
          interp rootSide MainRationality SondowAccepted bounds) ↔
      Month5Month6ThresholdCompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact
      (layered_public_kernel_threshold_nonempty_iff_statement
        interp rootSide MainRationality SondowAccepted bounds
        (Month5SondowCombinedUpperBound bounds)).1
        ⟨cert.threshold_kernel⟩
  · intro hstatement
    rcases
      (layered_public_kernel_threshold_nonempty_iff_statement
        interp rootSide MainRationality SondowAccepted bounds
        (Month5SondowCombinedUpperBound bounds)).2
        hstatement with
      ⟨kernel⟩
    exact ⟨{ threshold_kernel := kernel }⟩

namespace Month5Month6ThresholdCompletionAuditCertificate

def toCompletionAuditCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6ThresholdCompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    Month5Month6CompletionAuditCertificate
      interp rootSide MainRationality SondowAccepted bounds where
  combined_kernel := {
    public_completion := cert.threshold_kernel.public_completion
    month5_combined_gap := {
      gap_domination := cert.threshold_kernel.month5_threshold.gap_domination }
    month6_checked_replacement :=
      cert.threshold_kernel.month6_checked_replacement }

def toMonth5CombinedUpperThresholdCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6ThresholdCompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    Month5CombinedUpperThresholdCertificate
      MainRationality SondowAccepted bounds where
  threshold_gap := cert.threshold_kernel.month5_threshold

def toMonth5FinalExpressionThresholdCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6ThresholdCompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    Month5FinalExpressionThresholdCertificate bounds :=
  (cert.toMonth5CombinedUpperThresholdCertificate).toFinalExpressionThresholdCertificate

def month5_explicit_threshold
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6ThresholdCompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) : Nat :=
  cert.threshold_kernel.month5_threshold.threshold_growth.threshold_gap.threshold

theorem month5_gap_at_or_above_explicit_threshold
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6ThresholdCompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds)
    {m : Nat}
    (hm : cert.month5_explicit_threshold ≤ m) :
    bounds.combined m < Month5LowerBoundFunction m := by
  have hgap :=
    cert.threshold_kernel.month5_threshold.strict_gap_after_threshold
      hm
  simpa [Month5SondowCombinedUpperBound, Month5UpperBoundFunction,
    month5_explicit_threshold] using hgap

theorem to_completion_audit_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6ThresholdCompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    Month5Month6CompletionAuditStatement
      interp rootSide MainRationality SondowAccepted bounds :=
  (completion_audit_nonempty_iff_statement
    interp rootSide MainRationality SondowAccepted bounds).1
    ⟨cert.toCompletionAuditCertificate⟩

end Month5Month6ThresholdCompletionAuditCertificate

theorem threshold_completion_audit_nonempty_to_completion_audit_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (h :
      Nonempty
        (Month5Month6ThresholdCompletionAuditCertificate
          interp rootSide MainRationality SondowAccepted bounds)) :
    Nonempty
      (Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) := by
  rcases h with ⟨cert⟩
  exact ⟨cert.toCompletionAuditCertificate⟩

theorem threshold_completion_audit_nonempty_to_month5_combined_threshold
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (h :
      Nonempty
        (Month5Month6ThresholdCompletionAuditCertificate
          interp rootSide MainRationality SondowAccepted bounds)) :
    Nonempty (Month5CombinedUpperThresholdCertificate
      MainRationality SondowAccepted bounds) := by
  rcases h with ⟨cert⟩
  exact ⟨cert.toMonth5CombinedUpperThresholdCertificate⟩

theorem threshold_completion_audit_nonempty_to_final_expression_threshold
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (h :
      Nonempty
        (Month5Month6ThresholdCompletionAuditCertificate
          interp rootSide MainRationality SondowAccepted bounds)) :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) := by
  rcases h with ⟨cert⟩
  exact ⟨cert.toMonth5FinalExpressionThresholdCertificate⟩

theorem threshold_completion_statement_to_completion_audit_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (h :
      Month5Month6ThresholdCompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Month5Month6CompletionAuditStatement
      interp rootSide MainRationality SondowAccepted bounds :=
  (completion_audit_nonempty_iff_statement
    interp rootSide MainRationality SondowAccepted bounds).1
    (threshold_completion_audit_nonempty_to_completion_audit_nonempty
      ((threshold_completion_audit_nonempty_iff_statement
        interp rootSide MainRationality SondowAccepted bounds).2 h))

theorem threshold_completion_statement_to_month5_combined_threshold
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (h :
      Month5Month6ThresholdCompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month5CombinedUpperThresholdCertificate
      MainRationality SondowAccepted bounds) :=
  threshold_completion_audit_nonempty_to_month5_combined_threshold
    ((threshold_completion_audit_nonempty_iff_statement
      interp rootSide MainRationality SondowAccepted bounds).2 h)

theorem threshold_completion_statement_to_final_expression_threshold
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (h :
      Month5Month6ThresholdCompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
  threshold_completion_audit_nonempty_to_final_expression_threshold
    ((threshold_completion_audit_nonempty_iff_statement
      interp rootSide MainRationality SondowAccepted bounds).2 h)

namespace Month5Month6CompletionAuditCertificate

theorem public_completion
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) :=
  cert.combined_kernel.public_completion

def month5_combined_gap
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds :=
  cert.combined_kernel.month5_combined_gap

theorem month6_checked_replacement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    Month6CheckedCodeReplacementCertificate interp :=
  cert.combined_kernel.month6_checked_replacement

theorem final_upper_eq_sondow_combined
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds)
    (m : Nat) :
    Month5UpperBoundFunction
        (Month5SondowCombinedUpperBound bounds) m =
      bounds.combined m :=
  cert.combined_kernel.upper_is_sondow_combined m

theorem final_lower_eq_canonical_cnbox
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (_cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds)
    (m : Nat) :
    Month5LowerBoundFunction m = canonicalCnBoxPABox.length m :=
  rfl

theorem month5_independent_growth_domination
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    Month5IndependentGrowthDominationCertificate
      (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
      Month5LowerBoundFunction :=
  cert.month5_combined_gap.gap_domination.independent_growth

theorem month5_combined_strict_gap_after
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds)
    (N : Nat) :
    ∃ m : Nat, N ≤ m ∧
      bounds.combined m < Month5LowerBoundFunction m :=
  cert.combined_kernel.month5_combined_strict_gap_after N

def month5_witness_against_combined_upper
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds)
    (N : Nat) :
    HasProofLengthGapWitness
      canonicalCnBoxPABox (Month5SondowCombinedUpperBound bounds) N :=
  cert.combined_kernel.month5_witness_against_combined_upper N

theorem public_gap_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) :=
  cert.month5_combined_gap.to_public_gap_instantiation

theorem not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    ¬ MainRationality :=
  cert.month5_combined_gap.not_main_rationality

theorem month6_project_checked_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    _root_.ProjectProofLengthSemantics
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength
      _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
  (month6_checked_replacement_nonempty_iff_project_checked_semantics
    interp).1
    ⟨cert.month6_checked_replacement⟩

theorem month6_local_proof_code_recognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition interp :=
  (month6_checked_replacement_nonempty_iff_local_proof_code_recognition
    interp).1
    ⟨cert.month6_checked_replacement⟩

theorem month6_family_exactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp :=
  (month6_checked_replacement_nonempty_iff_family_exactness interp).1
    ⟨cert.month6_checked_replacement⟩

theorem month6_proof_code_checker_recognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (_root_.MiniHilbert.PAHilbertProofCodeCheckerRecognition
      interp) :=
  (month6_checked_replacement_nonempty_iff_proof_code_checker_recognition
    interp).1
    ⟨cert.month6_checked_replacement⟩

theorem month6_proof_length_code_calibration
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds)
    (fallback_length : _root_.FormulaCode → Nat) :
    (interp.localHilbertProofLengthCodeSemantics
      fallback_length).Calibration :=
  (month6_checked_replacement_nonempty_iff_proof_length_code_calibration
    interp fallback_length).1
    ⟨cert.month6_checked_replacement⟩

theorem month6_local_convention_certificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty
      (_root_.MiniHilbert.PAHilbertLocalProofCodeConventionCertificate
        interp) :=
  (month6_checked_replacement_nonempty_iff_local_convention_certificate
    interp).1
    ⟨cert.month6_checked_replacement⟩

theorem month6_internalization_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month6InternalizationAuditCertificate interp) :=
  (month6_checked_replacement_iff_internalization_audit interp).1
    ⟨cert.month6_checked_replacement⟩

theorem month6_partialConsistency_exact_minLength
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minLength m :=
  cert.combined_kernel.month6_partialConsistency_exact_minLength m

theorem month6_reflectionGraft_exact_minLength
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5Month6CompletionAuditCertificate
        interp rootSide MainRationality SondowAccepted bounds)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.sondowReflectionGraftCode m) =
      interp.target_proof_family.minLength m :=
  cert.combined_kernel.month6_reflectionGraft_exact_minLength m

end Month5Month6CompletionAuditCertificate

theorem completion_audit_statement_to_checked_replacement_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (h :
      Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    LayeredPublicKernelCheckedReplacementStatement
      interp rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) :=
  combined_upper_statement_to_checked_replacement_statement
    interp rootSide MainRationality SondowAccepted bounds h

theorem completion_audit_nonempty_to_checked_replacement_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (h :
      Nonempty
        (Month5Month6CompletionAuditCertificate
          interp rootSide MainRationality SondowAccepted bounds)) :
    LayeredPublicKernelCheckedReplacementStatement
      interp rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) :=
  completion_audit_statement_to_checked_replacement_statement
    interp rootSide MainRationality SondowAccepted bounds
    ((completion_audit_nonempty_iff_statement
      interp rootSide MainRationality SondowAccepted bounds).1 h)

theorem completion_audit_nonempty_iff_project_checked_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    Nonempty
        (Month5Month6CompletionAuditCertificate
          interp rootSide MainRationality SondowAccepted bounds) →
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode := by
  intro h
  rcases h with ⟨cert⟩
  exact cert.month6_project_checked_semantics

theorem completion_audit_nonempty_to_public_gap_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (h :
      Nonempty
        (Month5Month6CompletionAuditCertificate
          interp rootSide MainRationality SondowAccepted bounds)) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) := by
  rcases h with ⟨cert⟩
  exact cert.public_gap_instantiation

theorem completion_audit_statement_to_public_gap_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (h :
      Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) :=
  completion_audit_nonempty_to_public_gap_instantiation
    ((completion_audit_nonempty_iff_statement
      interp rootSide MainRationality SondowAccepted bounds).2 h)

theorem completion_audit_nonempty_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (h :
      Nonempty
        (Month5Month6CompletionAuditCertificate
          interp rootSide MainRationality SondowAccepted bounds)) :
    ¬ MainRationality := by
  rcases h with ⟨cert⟩
  exact cert.not_main_rationality

theorem completion_audit_statement_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (h :
      Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    ¬ MainRationality :=
  completion_audit_nonempty_not_main_rationality
    ((completion_audit_nonempty_iff_statement
      interp rootSide MainRationality SondowAccepted bounds).2 h)

theorem completion_audit_statement_to_local_convention_certificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (h :
      Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty
      (_root_.MiniHilbert.PAHilbertLocalProofCodeConventionCertificate
        interp) := by
  rcases
    (completion_audit_nonempty_iff_statement
      interp rootSide MainRationality SondowAccepted bounds).2 h with
    ⟨cert⟩
  exact cert.month6_local_convention_certificate

theorem threshold_completion_statement_not_main_rationality
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (h :
      Month5Month6ThresholdCompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    ¬ MainRationality :=
  completion_audit_statement_not_main_rationality
    interp rootSide MainRationality SondowAccepted bounds
    (threshold_completion_statement_to_completion_audit_statement
      interp rootSide MainRationality SondowAccepted bounds h)

end SondowProjectMonth5Month6CompletionAuditSurface
end SondowMainCheckedCodeBridge
