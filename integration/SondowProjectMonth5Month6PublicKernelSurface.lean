/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth3Month4CompletionAuditSurface
import BoundedArithmeticLab.CnBoxPudlakMonth5GapDominationSurface
import EulerLimit.ProofLengthCalibrationInternalizationSurface

/-!
# Month 5/Month 6 public kernel surface

This module is the project-level checklist for the next two public layers.
It deliberately keeps the Month 5 growth-gap certificate separate from the
Month 6 proof-length calibration certificate.  The only combined object here is
an audit package saying that the already-public Month 3/Month 4 completion
surface, the computable gap-domination surface, and the local proof-length
calibration surface are all present at the same entrypoint.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth5Month6PublicKernelSurface

universe u v w

open BoundedArithmeticLab
open BoundedArithmeticLab.BoundedProofPredicate
open SondowProjectMonth3Month4CompletionAuditSurface

abbrev Month6CalibrationCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Prop :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthCalibrationCertificate
    interp

abbrev Month6CheckedCodeReplacementCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Prop :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6CheckedCodeReplacementCertificate
    interp

structure LayeredPublicKernelCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  public_completion :
    PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds bound
  month5_gap_domination :
    Month5GapDominationCertificate
      MainRationality SondowAccepted bounds bound
  month6_calibration :
    Month6CalibrationCertificate interp

structure LayeredPublicKernelThresholdCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  public_completion :
    PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds bound
  month5_threshold :
    Month5GapThresholdCertificate
      MainRationality SondowAccepted bounds bound
  month6_checked_replacement :
    Month6CheckedCodeReplacementCertificate interp

structure LayeredPublicKernelCombinedUpperCertificate
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
    Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds
  month6_checked_replacement :
    Month6CheckedCodeReplacementCertificate interp

abbrev LayeredPublicKernelStatement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds bound ∧
      Nonempty (Month5GapDominationCertificate
      MainRationality SondowAccepted bounds bound) ∧
      Nonempty (Month6CalibrationCertificate interp)

abbrev LayeredPublicKernelCheckedReplacementStatement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds bound ∧
      Nonempty (Month5GapDominationCertificate
      MainRationality SondowAccepted bounds bound) ∧
      Nonempty (Month6CheckedCodeReplacementCertificate interp)

abbrev LayeredPublicKernelThresholdCheckedStatement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  PublicCompletionCertificate
      rootSide MainRationality SondowAccepted bounds bound ∧
    Nonempty (Month5GapThresholdCertificate
      MainRationality SondowAccepted bounds bound) ∧
      Nonempty (Month6CheckedCodeReplacementCertificate interp)

abbrev LayeredPublicKernelCombinedUpperStatement
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

namespace LayeredPublicKernelCertificate

theorem to_month5_public_gap_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelCertificate
        interp rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (_root_.BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  cert.month5_gap_domination.toPublicGapInstantiation

theorem to_completion_public_gap_instantiation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelCertificate
        interp rootSide MainRationality SondowAccepted bounds bound) :
    Nonempty (_root_.BoundedArithmeticLab.PublicGapCollisionInstantiation
      MainRationality) :=
  public_completion_to_public_gap_instantiation cert.public_completion

theorem month5_strict_gap_after
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelCertificate
        interp rootSide MainRationality SondowAccepted bounds bound)
    (N : Nat) :
    ∃ m : Nat, N ≤ m ∧
      Month5UpperBoundFunction bound m < Month5LowerBoundFunction m :=
  cert.month5_gap_domination.strict_gap_after N

theorem month5_witness_against_declared_upper
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelCertificate
        interp rootSide MainRationality SondowAccepted bounds bound)
    (N : Nat) :
    HasProofLengthGapWitness
      canonicalCnBoxPABox (Month5UpperBoundFunction bound) N :=
  cert.month5_gap_domination.witnessAgainstDeclaredUpper N

theorem month6_project_checked_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelCertificate
        interp rootSide MainRationality SondowAccepted bounds bound) :
    _root_.ProjectProofLengthSemantics
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength
      _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
  cert.month6_calibration.toProjectCheckedCodeSemantics

theorem month6_family_exactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelCertificate
        interp rootSide MainRationality SondowAccepted bounds bound) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp :=
  cert.month6_calibration.toFamilyExactness

theorem month6_local_proof_code_recognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelCertificate
        interp rootSide MainRationality SondowAccepted bounds bound) :
    _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition interp :=
  cert.month6_calibration.toLocalProofCodeRecognition

theorem month6_split_min_checked_exactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelCertificate
        interp rootSide MainRationality SondowAccepted bounds bound) :
    _root_.MiniHilbert.PAHilbertPartialConsistencyMinCheckedExactness interp ∧
      _root_.MiniHilbert.PAHilbertReflectionGraftMinCheckedExactness interp :=
  cert.month6_calibration.toSplitMinCheckedExactness

theorem month6_checked_code_replacement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelCertificate
        interp rootSide MainRationality SondowAccepted bounds bound) :
    Month6CheckedCodeReplacementCertificate interp :=
  _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6CheckedCodeReplacementCertificate.ofCalibration
    cert.month6_calibration

def month6_proof_code_checker_recognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelCertificate
        interp rootSide MainRationality SondowAccepted bounds bound)
    (fallback_length : _root_.FormulaCode → Nat) :
    _root_.MiniHilbert.PAHilbertProofCodeCheckerRecognition interp :=
  cert.month6_checked_code_replacement.toProofCodeCheckerRecognition
    fallback_length

theorem month6_partialConsistency_exact_minLength
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelCertificate
        interp rootSide MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minLength m :=
  cert.month6_checked_code_replacement.partialConsistency_exact_minLength m

theorem month6_reflectionGraft_exact_minLength
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelCertificate
        interp rootSide MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.sondowReflectionGraftCode m) =
      interp.target_proof_family.minLength m :=
  cert.month6_checked_code_replacement.reflectionGraft_exact_minLength m

theorem independent_not_main_rationality_routes
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelCertificate
        interp rootSide MainRationality SondowAccepted bounds bound) :
    (¬ MainRationality) ∧ (¬ MainRationality) :=
  ⟨public_completion_not_main_rationality cert.public_completion,
    cert.month5_gap_domination.not_main_rationality⟩

end LayeredPublicKernelCertificate

namespace LayeredPublicKernelThresholdCertificate

def toLayeredPublicKernelCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelThresholdCertificate
        interp rootSide MainRationality SondowAccepted bounds bound) :
    LayeredPublicKernelCertificate
      interp rootSide MainRationality SondowAccepted bounds bound where
  public_completion := cert.public_completion
  month5_gap_domination := cert.month5_threshold.gap_domination
  month6_calibration := cert.month6_checked_replacement.calibration

def month5_witness_against_declared_upper
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelThresholdCertificate
        interp rootSide MainRationality SondowAccepted bounds bound)
    (N : Nat) :
    HasProofLengthGapWitness
      canonicalCnBoxPABox (Month5UpperBoundFunction bound) N :=
  cert.month5_threshold.witnessAgainstDeclaredUpper N

theorem month6_partialConsistency_exact_minLength
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelThresholdCertificate
        interp rootSide MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minLength m :=
  cert.toLayeredPublicKernelCertificate.month6_partialConsistency_exact_minLength m

theorem month6_reflectionGraft_exact_minLength
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {rootSide : SondowProjectLocalPudlakSideInputs}
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      LayeredPublicKernelThresholdCertificate
        interp rootSide MainRationality SondowAccepted bounds bound)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.sondowReflectionGraftCode m) =
      interp.target_proof_family.minLength m :=
  cert.toLayeredPublicKernelCertificate.month6_reflectionGraft_exact_minLength m

end LayeredPublicKernelThresholdCertificate

namespace LayeredPublicKernelCombinedUpperCertificate

def toLayeredPublicKernelCertificate
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
      LayeredPublicKernelCombinedUpperCertificate
        interp rootSide MainRationality SondowAccepted bounds) :
    LayeredPublicKernelCertificate
      interp rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) where
  public_completion := cert.public_completion
  month5_gap_domination := cert.month5_combined_gap.gap_domination
  month6_calibration := cert.month6_checked_replacement.calibration

theorem upper_is_sondow_combined
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
      LayeredPublicKernelCombinedUpperCertificate
        interp rootSide MainRationality SondowAccepted bounds)
    (m : Nat) :
    Month5UpperBoundFunction
        (Month5SondowCombinedUpperBound bounds) m =
      bounds.combined m :=
  cert.month5_combined_gap.upper_is_sondow_combined m

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
      LayeredPublicKernelCombinedUpperCertificate
        interp rootSide MainRationality SondowAccepted bounds)
    (N : Nat) :
    ∃ m : Nat, N ≤ m ∧
      bounds.combined m < Month5LowerBoundFunction m :=
  cert.month5_combined_gap.strict_gap_after N

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
      LayeredPublicKernelCombinedUpperCertificate
        interp rootSide MainRationality SondowAccepted bounds)
    (N : Nat) :
    HasProofLengthGapWitness
      canonicalCnBoxPABox (Month5SondowCombinedUpperBound bounds) N :=
  cert.month5_combined_gap.witnessAgainstCombinedUpper N

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
      LayeredPublicKernelCombinedUpperCertificate
        interp rootSide MainRationality SondowAccepted bounds)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minLength m :=
  cert.toLayeredPublicKernelCertificate.month6_partialConsistency_exact_minLength m

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
      LayeredPublicKernelCombinedUpperCertificate
        interp rootSide MainRationality SondowAccepted bounds)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.sondowReflectionGraftCode m) =
      interp.target_proof_family.minLength m :=
  cert.toLayeredPublicKernelCertificate.month6_reflectionGraft_exact_minLength m

end LayeredPublicKernelCombinedUpperCertificate

theorem layered_public_kernel_nonempty_iff_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) :
    Nonempty
        (LayeredPublicKernelCertificate
          interp rootSide MainRationality SondowAccepted bounds bound) ↔
      LayeredPublicKernelStatement
        interp rootSide MainRationality SondowAccepted bounds bound := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact
      ⟨cert.public_completion,
        ⟨cert.month5_gap_domination⟩,
        ⟨cert.month6_calibration⟩⟩
  · intro hstatement
    rcases hstatement with
      ⟨hcompletion, ⟨hgap⟩, ⟨hcalibration⟩⟩
    exact
      ⟨{
        public_completion := hcompletion
        month5_gap_domination := hgap
        month6_calibration := hcalibration }⟩

theorem layered_public_kernel_statement_iff_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) :
    LayeredPublicKernelStatement
        interp rootSide MainRationality SondowAccepted bounds bound ↔
      Nonempty
        (LayeredPublicKernelCertificate
          interp rootSide MainRationality SondowAccepted bounds bound) :=
  (layered_public_kernel_nonempty_iff_statement
    interp rootSide MainRationality SondowAccepted bounds bound).symm

theorem layered_public_kernel_threshold_nonempty_iff_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) :
    Nonempty
        (LayeredPublicKernelThresholdCertificate
          interp rootSide MainRationality SondowAccepted bounds bound) ↔
      LayeredPublicKernelThresholdCheckedStatement
        interp rootSide MainRationality SondowAccepted bounds bound := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact
      ⟨cert.public_completion,
        ⟨cert.month5_threshold⟩,
        ⟨cert.month6_checked_replacement⟩⟩
  · intro hstatement
    rcases hstatement with
      ⟨hcompletion, ⟨hthreshold⟩, ⟨hreplacement⟩⟩
    exact
      ⟨{
        public_completion := hcompletion
        month5_threshold := hthreshold
        month6_checked_replacement := hreplacement }⟩

theorem layered_public_kernel_statement_iff_checked_replacement_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) :
    LayeredPublicKernelStatement
        interp rootSide MainRationality SondowAccepted bounds bound ↔
      LayeredPublicKernelCheckedReplacementStatement
        interp rootSide MainRationality SondowAccepted bounds bound := by
  constructor
  · intro h
    rcases h with ⟨hcompletion, hgap, hcalibration⟩
    exact
      ⟨hcompletion, hgap,
        (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_month6CalibrationCertificate
          interp).2 hcalibration⟩
  · intro h
    rcases h with ⟨hcompletion, hgap, hreplacement⟩
    exact
      ⟨hcompletion, hgap,
        (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.checkedCodeReplacement_nonempty_iff_month6CalibrationCertificate
          interp).1 hreplacement⟩

theorem threshold_checked_statement_to_checked_replacement_statement
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (rootSide : SondowProjectLocalPudlakSideInputs)
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real)
    (h :
      LayeredPublicKernelThresholdCheckedStatement
        interp rootSide MainRationality SondowAccepted bounds bound) :
    LayeredPublicKernelCheckedReplacementStatement
      interp rootSide MainRationality SondowAccepted bounds bound := by
  rcases h with ⟨hcompletion, hthreshold, hreplacement⟩
  exact
    ⟨hcompletion,
      month5GapThresholdCertificate_nonempty_to_gapDomination hthreshold,
      hreplacement⟩

theorem layered_public_kernel_combined_upper_nonempty_iff_statement
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
        (LayeredPublicKernelCombinedUpperCertificate
          interp rootSide MainRationality SondowAccepted bounds) ↔
      LayeredPublicKernelCombinedUpperStatement
        interp rootSide MainRationality SondowAccepted bounds := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact
      ⟨cert.public_completion,
        ⟨cert.month5_combined_gap⟩,
        ⟨cert.month6_checked_replacement⟩⟩
  · intro hstatement
    rcases hstatement with
      ⟨hcompletion, ⟨hgap⟩, ⟨hreplacement⟩⟩
    exact
      ⟨{
        public_completion := hcompletion
        month5_combined_gap := hgap
        month6_checked_replacement := hreplacement }⟩

theorem combined_upper_statement_to_checked_replacement_statement
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
      LayeredPublicKernelCombinedUpperStatement
        interp rootSide MainRationality SondowAccepted bounds) :
    LayeredPublicKernelCheckedReplacementStatement
      interp rootSide MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) := by
  rcases h with ⟨hcompletion, hcombined, hreplacement⟩
  exact
    ⟨hcompletion,
      (month5CombinedUpperGapCertificate_nonempty_iff_gapDomination_nonempty).1
        hcombined,
      hreplacement⟩

theorem month5_gap_nonempty_iff_computable_gap_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (Month5GapDominationCertificate
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound) :=
  month5GapDominationCertificate_nonempty_iff_computableGap_nonempty

theorem month6_calibration_nonempty_iff_project_checked_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty
        (Month6CalibrationCertificate interp) ↔
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode :=
  (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_month6CalibrationCertificate
    interp).symm

theorem month6_calibration_nonempty_iff_split_min_checked_exactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty
        (Month6CalibrationCertificate interp) ↔
      (_root_.MiniHilbert.PAHilbertPartialConsistencyMinCheckedExactness
          interp ∧
        _root_.MiniHilbert.PAHilbertReflectionGraftMinCheckedExactness
          interp) :=
  (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.splitMinCheckedExactness_iff_month6CalibrationCertificate
    interp).symm

theorem month6_checked_replacement_nonempty_iff_project_checked_semantics
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
  (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.projectCheckedCodeSemantics_iff_checkedCodeReplacementCertificate
    interp).symm

theorem month6_checked_replacement_nonempty_iff_local_proof_code_recognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition interp :=
  (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.localProofCodeRecognition_iff_checkedCodeReplacementCertificate
    interp).symm

theorem month6_checked_replacement_nonempty_iff_family_exactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp :=
  (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.familyExactness_iff_checkedCodeReplacementCertificate
    interp).symm

theorem month6_checked_replacement_nonempty_iff_proof_code_checker_recognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      Nonempty (_root_.MiniHilbert.PAHilbertProofCodeCheckerRecognition interp) :=
  (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.proofCodeCheckerRecognition_iff_checkedCodeReplacementCertificate
    interp).symm

theorem month6_checked_replacement_nonempty_iff_proof_length_code_calibration
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
  (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.proofLengthCodeCalibration_iff_checkedCodeReplacementCertificate
    interp fallback_length).symm

theorem month6_checked_replacement_nonempty_iff_local_convention_certificate
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
  (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.localProofCodeConventionCertificate_iff_checkedCodeReplacementCertificate
    interp).symm

end SondowProjectMonth5Month6PublicKernelSurface
end SondowMainCheckedCodeBridge
