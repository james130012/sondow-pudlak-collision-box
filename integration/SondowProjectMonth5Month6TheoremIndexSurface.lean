/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth5Month6CompletionAuditSurface

/-!
# Month 5/Month 6 theorem index surface

This module gives stable, paper-facing names to the Month 5/Month 6 public
closure endpoint.  It is intentionally thin: every exported theorem is a
renaming or direct projection from the completion-audit surface.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth5Month6TheoremIndexSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4CompletionAuditSurface
open SondowProjectMonth5Month6PublicKernelSurface
open SondowProjectMonth5Month6CompletionAuditSurface

abbrev PublicMonth5Month6CompletionCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6CompletionAuditCertificate
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6CheckedCodeOnlyCompletionCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6CheckedCodeOnlyCompletionCertificate
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6CompletionStatement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6CompletionAuditStatement
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ThresholdStatement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ThresholdCompletionAuditStatement
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ThresholdSearchAuditChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ThresholdSearchAuditChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6MonotoneThresholdAuditChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6MonotoneThresholdAuditChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6GapDifferenceThresholdAuditChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6GapDifferenceThresholdAuditChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6EventualGapDifferenceThresholdAuditChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6EventualGapDifferenceThresholdAuditChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6StepGapDifferenceThresholdAuditChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6StepGapDifferenceThresholdAuditChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6DecomposedInternalizationChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6DecomposedInternalizationChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ProjectBaseChecklist
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ProjectBaseChecklist
    rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6CheckedCodeOnlyChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6CheckedCodeOnlyChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ResidualExactnessChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ResidualExactnessChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6TwoFamilyResidualExactnessChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6TwoFamilyResidualExactnessChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ProofLengthBoundaryChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ProofLengthBoundaryChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ProjectProofLengthSemanticsChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ProjectProofLengthSemanticsChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6FreeClosureProjectSemanticsChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6FreeClosureProjectSemanticsChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ProofLengthAxiomFrontierChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ProofLengthAxiomFrontierChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ProjectBaseEncoderBoundaryChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ProjectBaseEncoderBoundaryChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ProjectBaseCheckerEncoderChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ProjectBaseCheckerEncoderChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ProjectBaseEncoderConventionChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ProjectBaseEncoderConventionChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ProjectBaseTwoFamilyLengthSemanticsChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ProjectBaseTwoFamilyLengthSemanticsChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ProjectBaseSeparatedEncoderLengthChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ProjectBaseSeparatedEncoderLengthChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ProjectBaseFrontierSplitChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ProjectBaseFrontierSplitChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ProjectBaseProofCodeCheckerFrontierChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ProjectBaseProofCodeCheckerFrontierChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev PublicMonth5Month6ProjectBaseCheckerCalibrationFrontierChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :=
  Month5Month6ProjectBaseCheckerCalibrationFrontierChecklist
    interp rootSide MainRationality SondowAccepted bounds

abbrev Month6InternalizationAuditCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthInternalizationAuditCertificate
    interp

abbrev Month6ExactLocalProofCodeSemanticsCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ExactLocalProofCodeSemanticsCertificate
    interp

abbrev Month6TwoFamilyResidualExactnessCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6TwoFamilyResidualExactnessCertificate
    interp

abbrev Month6TwoFamilyProofLengthBoundaryCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6TwoFamilyProofLengthBoundaryCertificate
    interp

abbrev Month6ProofLengthFreeLocalCodeClosure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFreeLocalCodeClosure
    interp

abbrev Month6ProofLengthAxiomFrontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthAxiomFrontier
    interp

abbrev Month6ProofLengthFreeEncoderData
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFreeEncoderData
    interp

abbrev Month6EncoderConventionBoundaryCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderConventionBoundaryCertificate
    interp

abbrev Month6EncoderTwoFamilyLengthSemanticsCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderTwoFamilyLengthSemanticsCertificate
    interp

abbrev Month6SeparatedTwoFamilyEncoderLengthCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6SeparatedTwoFamilyEncoderLengthCertificate
    interp

abbrev Month6SeparatedEncoderResidualExactnessCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6SeparatedEncoderResidualExactnessCertificate
    interp

abbrev Month6ProofLengthFrontierSplitCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFrontierSplitCertificate
    interp

abbrev Month6LocalRecognitionFrontierCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6LocalRecognitionFrontierCertificate
    interp

abbrev Month6ProofCodeCheckerFrontierCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofCodeCheckerFrontierCertificate
    interp

abbrev Month6ProofCodeCheckerCalibrationFrontierCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofCodeCheckerCalibrationFrontierCertificate
    interp

abbrev Month7ProofLengthFreeCheckerKernelCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month7ProofLengthFreeCheckerKernelCertificate
    interp

abbrev Month7GlobalProofLengthRealizationFrontierCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month7GlobalProofLengthRealizationFrontierCertificate
    interp

abbrev Month7ProofLengthEliminationFrontierCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month7ProofLengthEliminationFrontierCertificate
    interp

abbrev Month6LocalConventionBoundaryCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6LocalConventionBoundaryCertificate
    interp

abbrev Month6EncoderBoundaryCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6EncoderBoundaryCertificate
    interp

abbrev Month6ProofLengthConventionBoundaryCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthConventionBoundaryCertificate
    interp

theorem public_statement_iff_completion_audit_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      Month5Month6CompletionAuditStatement
        interp rootSide MainRationality SondowAccepted bounds :=
  Iff.rfl

theorem public_certificate_nonempty_iff_statement
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
        (PublicMonth5Month6CompletionCertificate
          interp rootSide MainRationality SondowAccepted bounds) ↔
      PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_nonempty_iff_statement
    interp rootSide MainRationality SondowAccepted bounds

theorem public_checked_code_only_certificate_nonempty_iff_checklist
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
        (PublicMonth5Month6CheckedCodeOnlyCompletionCertificate
          interp rootSide MainRationality SondowAccepted bounds) ↔
      PublicMonth5Month6CheckedCodeOnlyChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  checked_code_only_certificate_nonempty_iff_checklist
    interp rootSide MainRationality SondowAccepted bounds

theorem public_checked_code_only_checklist_iff_public_completion_and_gap
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CheckedCodeOnlyChecklist
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (Month5CombinedUpperGapCertificate
          MainRationality SondowAccepted bounds) :=
  checked_code_only_checklist_iff_public_completion_and_gap
    interp rootSide MainRationality SondowAccepted bounds

theorem public_checked_code_only_checklist_iff_project_base_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CheckedCodeOnlyChecklist
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ProjectBaseChecklist
        rootSide MainRationality SondowAccepted bounds :=
  checked_code_only_checklist_iff_project_base_checklist
    interp rootSide MainRationality SondowAccepted bounds

theorem public_project_base_checklist_iff_public_completion_and_computable_gap
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6ProjectBaseChecklist
        rootSide MainRationality SondowAccepted bounds ↔
      PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds)) :=
  project_base_checklist_iff_public_completion_and_computable_gap
    rootSide MainRationality SondowAccepted bounds

theorem public_threshold_statement_iff_threshold_search_audit_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6ThresholdStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ThresholdSearchAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  threshold_completion_statement_iff_threshold_search_audit_checklist
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_decomposed_internalization_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6DecomposedInternalizationChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_decomposed_internalization_checklist
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_residual_exactness_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ResidualExactnessChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_residual_exactness_checklist
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_two_family_residual_exactness_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6TwoFamilyResidualExactnessChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_two_family_residual_exactness_checklist
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_proof_length_boundary_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ProofLengthBoundaryChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_proof_length_boundary_checklist
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_project_proof_length_semantics_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ProjectProofLengthSemanticsChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_project_proof_length_semantics_checklist
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_free_closure_project_semantics_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6FreeClosureProjectSemanticsChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_free_closure_project_semantics_checklist
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_checked_code_only_and_project_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6CheckedCodeOnlyChecklist
        interp rootSide MainRationality SondowAccepted bounds ∧
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
  completion_audit_statement_iff_checked_code_only_and_project_semantics
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_project_base_and_month6_project_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ProjectBaseChecklist
          rootSide MainRationality SondowAccepted bounds ∧
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
  completion_audit_statement_iff_project_base_and_month6_project_semantics
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_project_base_encoder_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ProjectBaseEncoderBoundaryChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_project_base_encoder_boundary
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_project_base_encoder_convention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ProjectBaseEncoderConventionChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_project_base_encoder_convention
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_public_completion_computable_gap_encoder_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty (Month6EncoderBoundaryCertificate interp) :=
  completion_audit_statement_iff_public_completion_computable_gap_encoder_boundary
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_public_completion_computable_gap_encoder_convention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty (Month6EncoderConventionBoundaryCertificate interp) :=
  completion_audit_statement_iff_public_completion_computable_gap_encoder_convention
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_project_base_two_family_length_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ProjectBaseTwoFamilyLengthSemanticsChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_project_base_two_family_length_semantics
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_public_completion_computable_gap_two_family_length_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty (Month6EncoderTwoFamilyLengthSemanticsCertificate interp) :=
  completion_audit_statement_iff_public_completion_computable_gap_two_family_length_semantics
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_project_base_separated_encoder_length
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ProjectBaseSeparatedEncoderLengthChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_project_base_separated_encoder_length
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_public_completion_computable_gap_separated_encoder_length
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty (Month6SeparatedTwoFamilyEncoderLengthCertificate interp) :=
  completion_audit_statement_iff_public_completion_computable_gap_separated_encoder_length
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_project_base_frontier_split
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ProjectBaseFrontierSplitChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_project_base_frontier_split
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_public_completion_computable_gap_frontier_split
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty (Month6ProofLengthFrontierSplitCertificate interp) :=
  completion_audit_statement_iff_public_completion_computable_gap_frontier_split
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_project_base_proof_code_checker_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ProjectBaseProofCodeCheckerFrontierChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_project_base_proof_code_checker_frontier
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_public_completion_computable_gap_proof_code_checker_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty (Month6ProofCodeCheckerFrontierCertificate interp) :=
  completion_audit_statement_iff_public_completion_computable_gap_proof_code_checker_frontier
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_project_base_checker_calibration_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ProjectBaseCheckerCalibrationFrontierChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_project_base_checker_calibration_frontier
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_public_completion_computable_gap_checker_calibration_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      (PublicCompletionCertificate
          rootSide MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds) ∧
        Nonempty (ProjectComputableGapCertificate
          MainRationality SondowAccepted bounds
          (Month5SondowCombinedUpperBound bounds))) ∧
        Nonempty
          (Month6ProofCodeCheckerCalibrationFrontierCertificate interp) :=
  completion_audit_statement_iff_public_completion_computable_gap_checker_calibration_frontier
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_project_base_checker_encoder
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ProjectBaseCheckerEncoderChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_project_base_checker_encoder
    interp rootSide MainRationality SondowAccepted bounds

theorem public_statement_iff_proof_length_axiom_frontier_checklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) :
    PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds ↔
      PublicMonth5Month6ProofLengthAxiomFrontierChecklist
        interp rootSide MainRationality SondowAccepted bounds :=
  completion_audit_statement_iff_proof_length_axiom_frontier_checklist
    interp rootSide MainRationality SondowAccepted bounds

theorem public_monotone_threshold_audit_checklist_to_threshold_statement
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
      PublicMonth5Month6MonotoneThresholdAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds) :
    PublicMonth5Month6ThresholdStatement
        interp rootSide MainRationality SondowAccepted bounds :=
  monotone_threshold_audit_checklist_to_threshold_completion_statement
    interp rootSide MainRationality SondowAccepted bounds h

theorem public_gap_difference_threshold_audit_checklist_to_threshold_statement
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
      PublicMonth5Month6GapDifferenceThresholdAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds) :
    PublicMonth5Month6ThresholdStatement
        interp rootSide MainRationality SondowAccepted bounds :=
  gap_difference_threshold_audit_checklist_to_threshold_completion_statement
    interp rootSide MainRationality SondowAccepted bounds h

theorem public_eventual_gap_difference_threshold_audit_checklist_to_threshold_statement
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
      PublicMonth5Month6EventualGapDifferenceThresholdAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds) :
    PublicMonth5Month6ThresholdStatement
        interp rootSide MainRationality SondowAccepted bounds :=
  eventual_gap_difference_threshold_audit_checklist_to_threshold_completion_statement
    interp rootSide MainRationality SondowAccepted bounds h

theorem public_step_gap_difference_threshold_audit_checklist_to_threshold_statement
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
      PublicMonth5Month6StepGapDifferenceThresholdAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds) :
    PublicMonth5Month6ThresholdStatement
        interp rootSide MainRationality SondowAccepted bounds :=
  step_gap_difference_threshold_audit_checklist_to_threshold_completion_statement
    interp rootSide MainRationality SondowAccepted bounds h

theorem public_threshold_search_audit_checklist_to_public_completion
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
      PublicMonth5Month6ThresholdSearchAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds) :
    PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) :=
  h.1

theorem public_threshold_search_audit_checklist_to_combined_gap
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
      PublicMonth5Month6ThresholdSearchAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) :=
  h.2.1

theorem public_threshold_search_audit_checklist_to_threshold_search
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
      PublicMonth5Month6ThresholdSearchAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month5ThresholdSearchCertificate bounds) :=
  h.2.2.1

theorem public_threshold_search_audit_checklist_to_month6_internalization_audit
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
      PublicMonth5Month6ThresholdSearchAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month6InternalizationAuditCertificate interp) :=
  h.2.2.2

theorem public_threshold_search_audit_checklist_to_month6_exact_local_proof_code_semantics
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
      PublicMonth5Month6ThresholdSearchAuditChecklist
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month6ExactLocalProofCodeSemanticsCertificate interp) := by
  have haudit :
      Nonempty (Month6InternalizationAuditCertificate interp) :=
    public_threshold_search_audit_checklist_to_month6_internalization_audit
      interp rootSide MainRationality SondowAccepted bounds h
  have hreplacement :
      Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
    (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ProofLengthInternalizationAudit_nonempty_iff_checkedReplacement
      interp).1 haudit
  have hcal :
      Nonempty
        (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthCalibrationCertificate
          interp) :=
    (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_month6CalibrationCertificate
      interp).1 hreplacement
  exact
    (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ExactLocalProofCodeSemantics_nonempty_iff_month6CalibrationCertificate
      interp).2 hcal

theorem public_statement_to_checked_replacement_statement
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
      PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    LayeredPublicKernelCheckedReplacementStatement
      interp rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) :=
  completion_audit_statement_to_checked_replacement_statement
    interp rootSide MainRationality SondowAccepted bounds h

theorem public_statement_to_public_gap_instantiation
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
      PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) :=
  completion_audit_statement_to_public_gap_instantiation
    interp rootSide MainRationality SondowAccepted bounds h

theorem public_statement_to_local_convention_certificate
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
      PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty
      (_root_.MiniHilbert.PAHilbertLocalProofCodeConventionCertificate
        interp) :=
  completion_audit_statement_to_local_convention_certificate
    interp rootSide MainRationality SondowAccepted bounds h

theorem public_statement_not_main_rationality
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
      PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    ¬ MainRationality :=
  completion_audit_statement_not_main_rationality
    interp rootSide MainRationality SondowAccepted bounds h

theorem public_threshold_statement_to_public_statement
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
      PublicMonth5Month6ThresholdStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    PublicMonth5Month6CompletionStatement
      interp rootSide MainRationality SondowAccepted bounds :=
  threshold_completion_statement_to_completion_audit_statement
    interp rootSide MainRationality SondowAccepted bounds h

theorem public_threshold_statement_to_month5_combined_threshold
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
      PublicMonth5Month6ThresholdStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month5CombinedUpperThresholdCertificate
      MainRationality SondowAccepted bounds) := by
  rcases h with ⟨_hcompletion, hthreshold, _hreplacement⟩
  rcases hthreshold with ⟨threshold⟩
  exact ⟨{ threshold_gap := threshold }⟩

theorem public_threshold_statement_to_final_expression_threshold
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
      PublicMonth5Month6ThresholdStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
  month5CombinedUpperThresholdCertificate_nonempty_to_finalExpressionThreshold
    (public_threshold_statement_to_month5_combined_threshold
      interp rootSide MainRationality SondowAccepted bounds h)

theorem public_threshold_statement_to_verified_threshold_candidate
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
      PublicMonth5Month6ThresholdStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month5VerifiedThresholdCandidate bounds) :=
  month5CombinedUpperThresholdCertificate_nonempty_to_verifiedThresholdCandidate
    (public_threshold_statement_to_month5_combined_threshold
      interp rootSide MainRationality SondowAccepted bounds h)

theorem public_threshold_statement_to_threshold_search_certificate
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
      PublicMonth5Month6ThresholdStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month5ThresholdSearchCertificate bounds) :=
  (month5ThresholdSearchCertificate_nonempty_iff_verifiedThresholdCandidate).2
    (public_threshold_statement_to_verified_threshold_candidate
      interp rootSide MainRationality SondowAccepted bounds h)

theorem public_threshold_statement_not_main_rationality
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
      PublicMonth5Month6ThresholdStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    ¬ MainRationality :=
  threshold_completion_statement_not_main_rationality
    interp rootSide MainRationality SondowAccepted bounds h

theorem month5_gap_component_iff_computable_gap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} :
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ↔
      Nonempty (ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds
        (Month5SondowCombinedUpperBound bounds)) :=
  month5_combined_gap_nonempty_iff_computable_gap

theorem month5_independent_growth_iff_cofinal_growth
    {U L : Nat → Real} :
    Nonempty (Month5IndependentGrowthDominationCertificate U L) ↔
      Nonempty (Month5CofinalGrowthDominationCertificate U L) :=
  month5IndependentGrowthDomination_nonempty_iff_cofinal

theorem month5_threshold_growth_to_cofinal_growth
    {U L : Nat → Real}
    (h : Nonempty (Month5ThresholdGrowthDominationCertificate U L)) :
    Nonempty (Month5CofinalGrowthDominationCertificate U L) :=
  month5ThresholdGrowthDomination_nonempty_to_cofinalGrowth h

theorem month5_cofinal_and_persistence_to_threshold_growth
    {U L : Nat → Real}
    (hcofinal : Nonempty (Month5CofinalGrowthDominationCertificate U L))
    (hpersist : Nonempty (Month5GapPersistenceCertificate U L)) :
    Nonempty (Month5ThresholdGrowthDominationCertificate U L) :=
  month5Cofinal_and_persistence_to_threshold hcofinal hpersist

theorem month5_monotone_persistence_to_persistence
    {U L : Nat → Real}
    (hmono : Nonempty (Month5MonotoneGapPersistenceCertificate U L)) :
    Nonempty (Month5GapPersistenceCertificate U L) :=
  month5MonotoneGapPersistence_nonempty_to_persistence hmono

theorem month5_cofinal_and_monotone_persistence_to_threshold_growth
    {U L : Nat → Real}
    (hcofinal : Nonempty (Month5CofinalGrowthDominationCertificate U L))
    (hmono : Nonempty (Month5MonotoneGapPersistenceCertificate U L)) :
    Nonempty (Month5ThresholdGrowthDominationCertificate U L) :=
  month5Cofinal_and_monotone_persistence_to_threshold hcofinal hmono

theorem month5_gap_difference_persistence_to_persistence
    {U L : Nat → Real}
    (hdiff : Nonempty (Month5GapDifferencePersistenceCertificate U L)) :
    Nonempty (Month5GapPersistenceCertificate U L) :=
  month5GapDifferencePersistence_nonempty_to_persistence hdiff

theorem month5_cofinal_and_gap_difference_persistence_to_threshold_growth
    {U L : Nat → Real}
    (hcofinal : Nonempty (Month5CofinalGrowthDominationCertificate U L))
    (hdiff : Nonempty (Month5GapDifferencePersistenceCertificate U L)) :
    Nonempty (Month5ThresholdGrowthDominationCertificate U L) :=
  month5Cofinal_and_gap_difference_persistence_to_threshold
    hcofinal hdiff

theorem month5_cofinal_and_eventual_gap_difference_to_threshold_growth
    {U L : Nat → Real}
    (hcofinal : Nonempty (Month5CofinalGrowthDominationCertificate U L))
    (hdiff :
      Nonempty (Month5EventualGapDifferencePersistenceCertificate U L)) :
    Nonempty (Month5ThresholdGrowthDominationCertificate U L) :=
  month5Cofinal_and_eventual_gap_difference_to_threshold hcofinal hdiff

theorem month5_cofinal_and_step_gap_difference_to_threshold_growth
    {U L : Nat → Real}
    (hcofinal : Nonempty (Month5CofinalGrowthDominationCertificate U L))
    (hstep :
      Nonempty (Month5StepGapDifferencePersistenceCertificate U L)) :
    Nonempty (Month5ThresholdGrowthDominationCertificate U L) :=
  month5Cofinal_and_step_gap_difference_to_threshold hcofinal hstep

theorem month5_gap_component_to_cofinal_growth
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (h :
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds)) :
    Nonempty (Month5CofinalGrowthDominationCertificate
      (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
      Month5LowerBoundFunction) := by
  rcases h with ⟨cert⟩
  exact ⟨cert.gap_domination.independent_growth.toCofinal⟩

theorem month5_threshold_component_iff_components
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} :
    Nonempty (Month5CombinedUpperThresholdCertificate
      MainRationality SondowAccepted bounds) ↔
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds) ∧
        Nonempty (Month5ThresholdGrowthDominationCertificate
          (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
          Month5LowerBoundFunction) :=
  month5CombinedUpperThresholdCertificate_nonempty_iff_components

theorem month5_threshold_component_to_gap_component
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (h :
      Nonempty (Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds)) :
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) :=
  month5CombinedUpperThresholdCertificate_nonempty_to_combinedGap h

theorem month5_final_expression_threshold_iff_threshold_growth
    {bounds : SondowComponentBounds} :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) ↔
      Nonempty (Month5ThresholdGrowthDominationCertificate
        (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
        Month5LowerBoundFunction) :=
  month5FinalExpressionThresholdCertificate_nonempty_iff_thresholdGrowth

theorem month5_gap_component_and_persistence_to_final_expression_threshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (hgap :
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds))
    (hpersist :
      Nonempty (Month5FinalExpressionGapPersistenceCertificate bounds)) :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
  month5CombinedUpperGap_and_persistence_to_finalExpressionThreshold
    hgap hpersist

theorem month5_final_expression_monotone_persistence_to_persistence
    {bounds : SondowComponentBounds}
    (hmono :
      Nonempty (Month5FinalExpressionMonotoneGapPersistenceCertificate
        bounds)) :
    Nonempty (Month5FinalExpressionGapPersistenceCertificate bounds) :=
  month5FinalExpressionMonotoneGapPersistence_nonempty_to_persistence
    hmono

theorem month5_gap_component_and_monotone_persistence_to_final_expression_threshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (hgap :
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds))
    (hmono :
      Nonempty (Month5FinalExpressionMonotoneGapPersistenceCertificate
        bounds)) :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
  month5CombinedUpperGap_and_monotonePersistence_to_finalExpressionThreshold
    hgap hmono

theorem month5_final_expression_gap_difference_persistence_to_persistence
    {bounds : SondowComponentBounds}
    (hdiff :
      Nonempty (Month5FinalExpressionGapDifferencePersistenceCertificate
        bounds)) :
    Nonempty (Month5FinalExpressionGapPersistenceCertificate bounds) :=
  month5FinalExpressionGapDifferencePersistence_nonempty_to_persistence
    hdiff

theorem month5_gap_component_and_gap_difference_persistence_to_final_expression_threshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (hgap :
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds))
    (hdiff :
      Nonempty (Month5FinalExpressionGapDifferencePersistenceCertificate
        bounds)) :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
  month5CombinedUpperGap_and_gapDifferencePersistence_to_finalExpressionThreshold
    hgap hdiff

theorem month5_gap_component_and_eventual_gap_difference_to_final_expression_threshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (hgap :
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds))
    (hdiff :
      Nonempty
        (Month5FinalExpressionEventualGapDifferencePersistenceCertificate
          bounds)) :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
  month5CombinedUpperGap_and_eventualGapDifference_to_finalExpressionThreshold
    hgap hdiff

theorem month5_gap_component_and_step_gap_difference_to_final_expression_threshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (hgap :
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds))
    (hstep :
      Nonempty
        (Month5FinalExpressionStepGapDifferencePersistenceCertificate
          bounds)) :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
  month5CombinedUpperGap_and_stepGapDifference_to_finalExpressionThreshold
    hgap hstep

theorem month5_verified_threshold_candidate_iff_final_expression_threshold
    {bounds : SondowComponentBounds} :
    Nonempty (Month5VerifiedThresholdCandidate bounds) ↔
      Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
  month5VerifiedThresholdCandidate_nonempty_iff_finalExpressionThreshold

theorem month5_threshold_search_certificate_iff_verified_candidate
    {bounds : SondowComponentBounds} :
    Nonempty (Month5ThresholdSearchCertificate bounds) ↔
      Nonempty (Month5VerifiedThresholdCandidate bounds) :=
  month5ThresholdSearchCertificate_nonempty_iff_verifiedThresholdCandidate

theorem month5_threshold_search_certificate_iff_final_expression_threshold
    {bounds : SondowComponentBounds} :
    Nonempty (Month5ThresholdSearchCertificate bounds) ↔
      Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
  month5ThresholdSearchCertificate_nonempty_iff_finalExpressionThreshold

theorem month5_threshold_component_iff_gap_and_final_expression
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} :
    Nonempty (Month5CombinedUpperThresholdCertificate
      MainRationality SondowAccepted bounds) ↔
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds) ∧
        Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
  month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_finalExpression

theorem month5_threshold_component_iff_gap_and_verified_candidate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} :
    Nonempty (Month5CombinedUpperThresholdCertificate
      MainRationality SondowAccepted bounds) ↔
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds) ∧
        Nonempty (Month5VerifiedThresholdCandidate bounds) :=
  month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_verifiedCandidate

theorem month5_threshold_component_iff_gap_and_threshold_search
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} :
    Nonempty (Month5CombinedUpperThresholdCertificate
      MainRationality SondowAccepted bounds) ↔
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds) ∧
        Nonempty (Month5ThresholdSearchCertificate bounds) :=
  month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_thresholdSearch

theorem month6_component_iff_proof_length_code_calibration
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
  month6_checked_replacement_iff_proof_length_code_calibration
    interp fallback_length

theorem month6_component_iff_local_convention_certificate
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
  month6_checked_replacement_iff_local_convention_certificate interp

theorem month6_component_iff_internalization_audit
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

theorem month6_exact_local_proof_code_semantics_iff_local_recognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ExactLocalProofCodeSemanticsCertificate interp) ↔
      _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition interp :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ExactLocalProofCodeSemantics_nonempty_iff_localProofCodeRecognition
    interp

theorem month6_exact_local_proof_code_semantics_iff_calibration
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ExactLocalProofCodeSemanticsCertificate interp) ↔
      Nonempty
        (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthCalibrationCertificate
          interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ExactLocalProofCodeSemantics_nonempty_iff_month6CalibrationCertificate
    interp

theorem month6_exact_local_proof_code_semantics_iff_two_family_residual
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ExactLocalProofCodeSemanticsCertificate interp) ↔
      Nonempty (Month6TwoFamilyResidualExactnessCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ExactLocalProofCodeSemantics_nonempty_iff_twoFamilyResidualExactness
    interp

theorem month6_two_family_residual_iff_proof_length_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6TwoFamilyResidualExactnessCertificate interp) ↔
      Nonempty (Month6TwoFamilyProofLengthBoundaryCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6TwoFamilyResidualExactness_nonempty_iff_proofLengthBoundary
    interp

theorem month6_proof_length_boundary_iff_project_checked_code_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6TwoFamilyProofLengthBoundaryCertificate interp) ↔
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ProofLengthBoundary_nonempty_iff_projectCheckedCodeSemantics
    interp

theorem month6_component_iff_exact_local_proof_code_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      Nonempty (Month6ExactLocalProofCodeSemanticsCertificate interp) :=
  (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_month6CalibrationCertificate
    interp).trans
    (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ExactLocalProofCodeSemantics_nonempty_iff_month6CalibrationCertificate
      interp).symm

theorem month6_component_iff_two_family_residual_exactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      Nonempty (Month6TwoFamilyResidualExactnessCertificate interp) :=
  (month6_component_iff_exact_local_proof_code_semantics interp).trans
    (month6_exact_local_proof_code_semantics_iff_two_family_residual interp)

theorem month6_component_iff_proof_length_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      Nonempty (Month6TwoFamilyProofLengthBoundaryCertificate interp) :=
  (month6_component_iff_two_family_residual_exactness interp).trans
    (month6_two_family_residual_iff_proof_length_boundary interp)

theorem month6_component_iff_project_checked_code_semantics
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
  (month6_component_iff_proof_length_boundary interp).trans
    (month6_proof_length_boundary_iff_project_checked_code_semantics interp)

theorem month6_component_iff_free_closure_and_exact_local
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      Nonempty (Month6ProofLengthFreeLocalCodeClosure interp) ∧
        Nonempty (Month6ExactLocalProofCodeSemanticsCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_freeClosure_and_exactLocal
    interp

theorem month6_component_iff_free_closure_and_project_checked_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      Nonempty (Month6ProofLengthFreeLocalCodeClosure interp) ∧
        _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_freeClosure_and_projectCheckedSemantics
    interp

theorem month6_component_iff_proof_length_axiom_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      Month6ProofLengthAxiomFrontier interp :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_proofLengthAxiomFrontier
    interp

theorem month6_proof_length_free_local_code_closure_available
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthFreeLocalCodeClosure interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ProofLengthFreeLocalCodeClosure_nonempty
    interp

theorem month6_internalization_audit_iff_local_convention_certificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6InternalizationAuditCertificate interp) ↔
      Nonempty
        (_root_.MiniHilbert.PAHilbertLocalProofCodeConventionCertificate
          interp) :=
  (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.localProofCodeConventionCertificate_iff_month6InternalizationAudit
    interp).symm

theorem month6_local_convention_boundary_iff_local_convention_certificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6LocalConventionBoundaryCertificate interp) ↔
      Nonempty
        (_root_.MiniHilbert.PAHilbertLocalProofCodeConventionCertificate
          interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6LocalConventionBoundary_nonempty_iff_localConventionCertificate
    interp

theorem month6_encoder_boundary_iff_recognition_certificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderBoundaryCertificate interp) ↔
      Nonempty
        (_root_.MiniHilbert.PAHilbertProjectCheckedRecognitionCertificate
          interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6EncoderBoundary_nonempty_iff_recognitionCertificate
    interp

theorem month6_proof_length_convention_boundary_iff_encoder_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthConventionBoundaryCertificate interp) ↔
      Nonempty (Month6EncoderBoundaryCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ProofLengthConventionBoundary_nonempty_iff_encoderBoundary
    interp

theorem month6_proof_length_convention_boundary_iff_recognition_certificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthConventionBoundaryCertificate interp) ↔
      Nonempty
        (_root_.MiniHilbert.PAHilbertProjectCheckedRecognitionCertificate
          interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ProofLengthConventionBoundary_nonempty_iff_recognitionCertificate
    interp

theorem month6_local_convention_boundary_iff_checker_and_encoder
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6LocalConventionBoundaryCertificate interp) ↔
      Nonempty (_root_.MiniHilbert.PAHilbertLocalCheckerExactness interp) ∧
        Nonempty (Month6EncoderBoundaryCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6LocalConventionBoundary_nonempty_iff_checker_and_encoder
    interp

theorem month6_local_convention_boundary_iff_checker_and_length_convention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6LocalConventionBoundaryCertificate interp) ↔
      Nonempty (_root_.MiniHilbert.PAHilbertLocalCheckerExactness interp) ∧
        Nonempty (Month6ProofLengthConventionBoundaryCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6LocalConventionBoundary_nonempty_iff_checker_and_lengthConvention
    interp

theorem month6_project_checked_semantics_iff_local_convention_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6LocalConventionBoundaryCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_localConventionBoundary
    interp

theorem month6_project_checked_semantics_iff_encoder_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6EncoderBoundaryCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_encoderBoundary
    interp

theorem month6_proof_length_free_encoder_data_available
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthFreeEncoderData interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ProofLengthFreeEncoderData_nonempty
    interp

theorem month6_encoder_boundary_iff_encoder_convention_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderBoundaryCertificate interp) ↔
      Nonempty (Month6EncoderConventionBoundaryCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6EncoderBoundary_nonempty_iff_encoderConventionBoundary
    interp

theorem month6_project_checked_semantics_iff_encoder_convention_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6EncoderConventionBoundaryCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_encoderConventionBoundary
    interp

theorem month6_encoder_convention_boundary_iff_two_family_length_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderConventionBoundaryCertificate interp) ↔
      Nonempty (Month6EncoderTwoFamilyLengthSemanticsCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6EncoderConventionBoundary_nonempty_iff_twoFamilyLengthSemantics
    interp

theorem month6_encoder_boundary_iff_two_family_length_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderBoundaryCertificate interp) ↔
      Nonempty (Month6EncoderTwoFamilyLengthSemanticsCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6EncoderBoundary_nonempty_iff_twoFamilyLengthSemantics
    interp

theorem month6_project_checked_semantics_iff_two_family_length_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6EncoderTwoFamilyLengthSemanticsCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_twoFamilyLengthSemantics
    interp

theorem month6_two_family_length_semantics_iff_separated_encoder_length
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderTwoFamilyLengthSemanticsCertificate interp) ↔
      Nonempty (Month6SeparatedTwoFamilyEncoderLengthCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6EncoderTwoFamilyLengthSemantics_nonempty_iff_separatedEncoderLength
    interp

theorem month6_encoder_convention_boundary_iff_separated_encoder_length
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderConventionBoundaryCertificate interp) ↔
      Nonempty (Month6SeparatedTwoFamilyEncoderLengthCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6EncoderConventionBoundary_nonempty_iff_separatedEncoderLength
    interp

theorem month6_encoder_boundary_iff_separated_encoder_length
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderBoundaryCertificate interp) ↔
      Nonempty (Month6SeparatedTwoFamilyEncoderLengthCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6EncoderBoundary_nonempty_iff_separatedEncoderLength
    interp

theorem month6_project_checked_semantics_iff_separated_encoder_length
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6SeparatedTwoFamilyEncoderLengthCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_separatedEncoderLength
    interp

theorem month6_separated_encoder_length_iff_residual_exactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6SeparatedTwoFamilyEncoderLengthCertificate interp) ↔
      Nonempty (Month6SeparatedEncoderResidualExactnessCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6SeparatedEncoderLength_nonempty_iff_residualExactness
    interp

theorem month6_separated_encoder_residual_exactness_iff_frontier_split
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6SeparatedEncoderResidualExactnessCertificate interp) ↔
      Nonempty (Month6ProofLengthFrontierSplitCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6SeparatedEncoderResidualExactness_nonempty_iff_frontierSplit
    interp

theorem month6_separated_encoder_length_iff_frontier_split
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6SeparatedTwoFamilyEncoderLengthCertificate interp) ↔
      Nonempty (Month6ProofLengthFrontierSplitCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6SeparatedEncoderLength_nonempty_iff_frontierSplit
    interp

theorem month6_project_checked_semantics_iff_frontier_split
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6ProofLengthFrontierSplitCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_frontierSplit
    interp

theorem month6_frontier_split_iff_local_recognition_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthFrontierSplitCertificate interp) ↔
      Nonempty (Month6LocalRecognitionFrontierCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6FrontierSplit_nonempty_iff_localRecognitionFrontier
    interp

theorem month6_local_recognition_frontier_iff_proof_code_checker_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6LocalRecognitionFrontierCertificate interp) ↔
      Nonempty (Month6ProofCodeCheckerFrontierCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6LocalRecognitionFrontier_nonempty_iff_proofCodeCheckerFrontier
    interp

theorem month6_frontier_split_iff_proof_code_checker_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthFrontierSplitCertificate interp) ↔
      Nonempty (Month6ProofCodeCheckerFrontierCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6FrontierSplit_nonempty_iff_proofCodeCheckerFrontier
    interp

theorem month6_proof_code_checker_frontier_iff_checker_calibration_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofCodeCheckerFrontierCertificate interp) ↔
      Nonempty (Month6ProofCodeCheckerCalibrationFrontierCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ProofCodeCheckerFrontier_nonempty_iff_calibrationFrontier
    interp

theorem month6_frontier_split_iff_checker_calibration_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthFrontierSplitCertificate interp) ↔
      Nonempty (Month6ProofCodeCheckerCalibrationFrontierCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6FrontierSplit_nonempty_iff_calibrationFrontier
    interp

theorem month6_project_checked_semantics_iff_proof_code_checker_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6ProofCodeCheckerFrontierCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_proofCodeCheckerFrontier
    interp

theorem month6_project_checked_semantics_iff_checker_calibration_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6ProofCodeCheckerCalibrationFrontierCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_checkerCalibrationFrontier
    interp

theorem month7_checker_kernel_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month7ProofLengthFreeCheckerKernelCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month7ProofLengthFreeCheckerKernel_nonempty
    interp

theorem month7_project_checked_semantics_iff_elimination_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month7ProofLengthEliminationFrontierCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_month7ProofLengthEliminationFrontier
    interp

theorem month6_project_checked_semantics_iff_proof_length_convention_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6ProofLengthConventionBoundaryCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_proofLengthConventionBoundary
    interp

theorem month6_project_checked_semantics_iff_checker_and_encoder
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode ↔
      Nonempty (_root_.MiniHilbert.PAHilbertLocalCheckerExactness interp) ∧
        Nonempty (Month6EncoderBoundaryCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_checker_and_encoder
    interp

theorem month6_project_checked_semantics_iff_checker_and_length_convention
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode ↔
      Nonempty (_root_.MiniHilbert.PAHilbertLocalCheckerExactness interp) ∧
        Nonempty (Month6ProofLengthConventionBoundaryCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_checker_and_lengthConvention
    interp

theorem month6_local_convention_boundary_iff_internalization_audit
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6LocalConventionBoundaryCertificate interp) ↔
      Nonempty (Month6InternalizationAuditCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.localConventionBoundary_iff_month6InternalizationAudit
    interp

theorem month6_internalization_audit_of_local_convention_certificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (cert :
      _root_.MiniHilbert.PAHilbertLocalProofCodeConventionCertificate
        interp) :
    Nonempty (Month6InternalizationAuditCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6InternalizationAudit_of_localConventionCertificate
    cert

theorem month6_internalization_audit_of_local_convention_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6LocalConventionBoundaryCertificate interp) :
    Nonempty (Month6InternalizationAuditCertificate interp) :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6InternalizationAudit_of_localConventionBoundaryCertificate
    cert

theorem month6_internalization_audit_to_project_checked_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (h :
      Nonempty (Month6InternalizationAuditCertificate interp)) :
    _root_.ProjectProofLengthSemantics
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength
      _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6InternalizationAudit_nonempty_to_projectCheckedSemantics
    h

theorem public_statement_to_month6_internalization_audit
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
      PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month6InternalizationAuditCertificate interp) := by
  rcases h with ⟨_hcompletion, _hgap, hreplacement⟩
  exact (month6_component_iff_internalization_audit interp).1 hreplacement

theorem public_statement_to_month5_cofinal_growth
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
      PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month5CofinalGrowthDominationCertificate
      (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
      Month5LowerBoundFunction) := by
  rcases h with ⟨_hcompletion, hgap, _hreplacement⟩
  exact month5_gap_component_to_cofinal_growth hgap

theorem public_statement_to_month6_exact_local_proof_code_semantics
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
      PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month6ExactLocalProofCodeSemanticsCertificate interp) := by
  rcases h with ⟨_hcompletion, _hgap, hreplacement⟩
  have hcal :
      Nonempty
        (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthCalibrationCertificate
          interp) :=
    (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_month6CalibrationCertificate
      interp).1 hreplacement
  exact
    (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ExactLocalProofCodeSemantics_nonempty_iff_month6CalibrationCertificate
      interp).2 hcal

theorem public_statement_to_month6_proof_length_free_local_code_closure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds)
    (_h :
      PublicMonth5Month6CompletionStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    Nonempty (Month6ProofLengthFreeLocalCodeClosure interp) :=
  month6_proof_length_free_local_code_closure_available interp

end SondowProjectMonth5Month6TheoremIndexSurface
end SondowMainCheckedCodeBridge
