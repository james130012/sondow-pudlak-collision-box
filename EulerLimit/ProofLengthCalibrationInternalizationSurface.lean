/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.ProjectionBridge

/-!
# Month 6 proof-length calibration internalization surface

This module packages the narrow proof-length calibration that remains after the
MiniHilbert checked-code model has been built.  It does not claim a global
construction of `proof_length`; it states that the two project-relevant code
families agree with the local checked-code semantics, and exposes equivalences
to the existing split exactness certificates.
-/

noncomputable section

namespace MiniHilbert
namespace Month6ProofLengthCalibrationInternalizationSurface

universe u v w

structure Month6MiniHilbertMinimaCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {code : Nat → L.BoundedFormula α n}
    (family : ConcreteProofFamily Ax code) : Prop where
  minChecked_eq_minCode :
    ∀ m : Nat, family.minCheckedCodeSize m = family.minCodeSize m
  minChecked_eq_minLength :
    ∀ m : Nat, family.minCheckedCodeSize m = family.minLength m

namespace Month6MiniHilbertMinimaCertificate

theorem ofConcreteProofFamily
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {code : Nat → L.BoundedFormula α n}
    (family : ConcreteProofFamily Ax code) :
    Month6MiniHilbertMinimaCertificate family where
  minChecked_eq_minCode := family.minCheckedCodeSize_eq_minCodeSize
  minChecked_eq_minLength := family.minCheckedCodeSize_eq_minLength

theorem checked_minima_are_length_minima
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {code : Nat → L.BoundedFormula α n}
    {family : ConcreteProofFamily Ax code}
    (cert : Month6MiniHilbertMinimaCertificate family)
    (m : Nat) :
    family.minCheckedCodeSize m = family.minLength m :=
  cert.minChecked_eq_minLength m

end Month6MiniHilbertMinimaCertificate

structure Month6ProofLengthCalibrationCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  local_calibration :
    FormulaCodeHilbertLocalCalibration interp

namespace Month6ProofLengthCalibrationCertificate

theorem ofLocalCalibration
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hcal : FormulaCodeHilbertLocalCalibration interp) :
    Month6ProofLengthCalibrationCertificate interp where
  local_calibration := hcal

theorem toLocalProofCodeRecognition
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthCalibrationCertificate interp) :
    PAHilbertLocalProofCodeRecognition interp :=
  PAHilbertLocalProofCodeRecognition.ofFormulaCodeHilbertLocalCalibration
    cert.local_calibration

theorem toProjectCheckedCodeSemantics
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthCalibrationCertificate interp) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode :=
  interp.projectCheckedCodeSemantics_of_localHilbertProofCodeSemantics
    cert.local_calibration.to_localHilbertProofCodeSemantics

theorem toFamilyExactness
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthCalibrationCertificate interp) :
    PAHilbertProjectionFamilyExactness interp :=
  (interp.projectCheckedCodeSemantics_iff_familyExactness).1
    cert.toProjectCheckedCodeSemantics

theorem toSplitMinCheckedExactness
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthCalibrationCertificate interp) :
    PAHilbertPartialConsistencyMinCheckedExactness interp ∧
      PAHilbertReflectionGraftMinCheckedExactness interp :=
  (interp.projectCheckedCodeSemantics_iff_splitMinCheckedExactness).1
    cert.toProjectCheckedCodeSemantics

theorem partialConsistency_exact
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthCalibrationCertificate interp)
    (m : Nat) :
    proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minCheckedCodeSize m :=
  cert.toFamilyExactness.partialConsistency_exact m

theorem reflectionGraft_exact
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthCalibrationCertificate interp)
    (m : Nat) :
    proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) =
      interp.target_proof_family.minCheckedCodeSize m :=
  cert.toFamilyExactness.reflectionGraft_exact m

end Month6ProofLengthCalibrationCertificate

theorem projectCheckedCodeSemantics_iff_month6CalibrationCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6ProofLengthCalibrationCertificate interp) := by
  constructor
  · intro hsem
    exact
      ⟨Month6ProofLengthCalibrationCertificate.ofLocalCalibration
        (FormulaCodeHilbertLocalCalibration.of_projectCheckedCodeProofLengthSemantics
          interp hsem)⟩
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.toProjectCheckedCodeSemantics

theorem splitMinCheckedExactness_iff_month6CalibrationCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    (PAHilbertPartialConsistencyMinCheckedExactness interp ∧
        PAHilbertReflectionGraftMinCheckedExactness interp) ↔
      Nonempty (Month6ProofLengthCalibrationCertificate interp) := by
  exact (interp.splitMinCheckedExactness_iff_projectCheckedCodeSemantics).trans
    (projectCheckedCodeSemantics_iff_month6CalibrationCertificate interp)

theorem familyExactness_iff_month6CalibrationCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertProjectionFamilyExactness interp ↔
      Nonempty (Month6ProofLengthCalibrationCertificate interp) := by
  exact (interp.familyExactness_iff_projectCheckedCodeSemantics).trans
    (projectCheckedCodeSemantics_iff_month6CalibrationCertificate interp)

theorem localProofCodeRecognition_iff_month6CalibrationCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertLocalProofCodeRecognition interp ↔
      Nonempty (Month6ProofLengthCalibrationCertificate interp) := by
  exact (interp.localProofCodeRecognition_iff_localCalibration).trans
    ⟨fun hcal =>
      ⟨Month6ProofLengthCalibrationCertificate.ofLocalCalibration hcal⟩,
      fun hcert => by
        rcases hcert with ⟨cert⟩
        exact cert.local_calibration⟩

structure Month6ExactLocalProofCodeSemanticsCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  proof_length_eq_minProofCodeSize :
    ∀ code : FormulaCode, ∀ hcode : FormulaCodeHilbertRelevantCode code,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize code =
        interp.localHilbertProofCodeSemantics.minProofCodeSize code hcode

structure Month6TwoFamilyResidualExactnessCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  partialConsistency_exact :
    ∀ m : Nat,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) =
        interp.localHilbertProofCodeSemantics.minProofCodeSize
          (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
  reflectionGraft_exact :
    ∀ m : Nat,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode m) =
        interp.localHilbertProofCodeSemantics.minProofCodeSize
          (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)

structure Month6TwoFamilyProofLengthBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  partialConsistency_eq_localChecked :
    ∀ m : Nat,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) =
        interp.localCheckedCodeProofLength (partialConsistencyCode m)
  reflectionGraft_eq_localChecked :
    ∀ m : Nat,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode m) =
        interp.localCheckedCodeProofLength (sondowReflectionGraftCode m)

namespace Month6ExactLocalProofCodeSemanticsCertificate

def ofLocalProofCodeRecognition
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (hrec : PAHilbertLocalProofCodeRecognition interp) :
    Month6ExactLocalProofCodeSemanticsCertificate interp where
  proof_length_eq_minProofCodeSize :=
    hrec.proof_length_eq_minProofCodeSize

theorem toLocalProofCodeRecognition
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ExactLocalProofCodeSemanticsCertificate interp) :
    PAHilbertLocalProofCodeRecognition interp where
  proof_length_eq_minProofCodeSize :=
    cert.proof_length_eq_minProofCodeSize

theorem toLocalCalibration
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ExactLocalProofCodeSemanticsCertificate interp) :
    FormulaCodeHilbertLocalCalibration interp :=
  cert.toLocalProofCodeRecognition.toFormulaCodeHilbertLocalCalibration

def toCalibrationCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ExactLocalProofCodeSemanticsCertificate interp) :
    Month6ProofLengthCalibrationCertificate interp :=
  Month6ProofLengthCalibrationCertificate.ofLocalCalibration
    cert.toLocalCalibration

def toTwoFamilyResidualExactnessCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ExactLocalProofCodeSemanticsCertificate interp) :
    Month6TwoFamilyResidualExactnessCertificate interp where
  partialConsistency_exact := by
    intro m
    exact cert.proof_length_eq_minProofCodeSize
      (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
  reflectionGraft_exact := by
    intro m
    exact cert.proof_length_eq_minProofCodeSize
      (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)

end Month6ExactLocalProofCodeSemanticsCertificate

namespace Month6TwoFamilyResidualExactnessCertificate

def toProofLengthBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6TwoFamilyResidualExactnessCertificate interp) :
    Month6TwoFamilyProofLengthBoundaryCertificate interp where
  partialConsistency_eq_localChecked := by
    intro m
    rw [cert.partialConsistency_exact m]
    exact_mod_cast interp.localHilbertProofCodeSemantics_min_eq_localChecked
      (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
  reflectionGraft_eq_localChecked := by
    intro m
    rw [cert.reflectionGraft_exact m]
    exact_mod_cast interp.localHilbertProofCodeSemantics_min_eq_localChecked
      (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)

def toExactLocalProofCodeSemanticsCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6TwoFamilyResidualExactnessCertificate interp) :
    Month6ExactLocalProofCodeSemanticsCertificate interp where
  proof_length_eq_minProofCodeSize := by
    intro code hcode
    rcases hcode with ⟨m, hcode_eq⟩ | ⟨m, hcode_eq⟩
    · subst hcode_eq
      exact cert.partialConsistency_exact m
    · subst hcode_eq
      exact cert.reflectionGraft_exact m

end Month6TwoFamilyResidualExactnessCertificate

namespace Month6TwoFamilyProofLengthBoundaryCertificate

def toTwoFamilyResidualExactnessCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6TwoFamilyProofLengthBoundaryCertificate interp) :
    Month6TwoFamilyResidualExactnessCertificate interp where
  partialConsistency_exact := by
    intro m
    rw [cert.partialConsistency_eq_localChecked m]
    exact_mod_cast (interp.localHilbertProofCodeSemantics_min_eq_localChecked
      (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)).symm
  reflectionGraft_exact := by
    intro m
    rw [cert.reflectionGraft_eq_localChecked m]
    exact_mod_cast (interp.localHilbertProofCodeSemantics_min_eq_localChecked
      (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)).symm

end Month6TwoFamilyProofLengthBoundaryCertificate

theorem month6ExactLocalProofCodeSemantics_nonempty_iff_localProofCodeRecognition
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ExactLocalProofCodeSemanticsCertificate interp) ↔
      PAHilbertLocalProofCodeRecognition interp := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact cert.toLocalProofCodeRecognition
  · intro hrec
    exact
      ⟨Month6ExactLocalProofCodeSemanticsCertificate.ofLocalProofCodeRecognition
        hrec⟩

theorem month6ExactLocalProofCodeSemantics_nonempty_iff_month6CalibrationCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ExactLocalProofCodeSemanticsCertificate interp) ↔
      Nonempty (Month6ProofLengthCalibrationCertificate interp) :=
    (month6ExactLocalProofCodeSemantics_nonempty_iff_localProofCodeRecognition
    interp).trans
    (localProofCodeRecognition_iff_month6CalibrationCertificate interp)

theorem month6ExactLocalProofCodeSemantics_nonempty_iff_twoFamilyResidualExactness
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ExactLocalProofCodeSemanticsCertificate interp) ↔
      Nonempty (Month6TwoFamilyResidualExactnessCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toTwoFamilyResidualExactnessCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toExactLocalProofCodeSemanticsCertificate⟩

theorem month6TwoFamilyResidualExactness_nonempty_iff_proofLengthBoundary
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6TwoFamilyResidualExactnessCertificate interp) ↔
      Nonempty (Month6TwoFamilyProofLengthBoundaryCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toProofLengthBoundaryCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toTwoFamilyResidualExactnessCertificate⟩

theorem month6ProofLengthBoundary_nonempty_iff_projectCheckedCodeSemantics
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6TwoFamilyProofLengthBoundaryCertificate interp) ↔
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    refine ⟨?_⟩
    intro code hcode
    rcases hcode with ⟨m, hcode_eq⟩ | ⟨m, hcode_eq⟩
    · subst hcode_eq
      exact cert.partialConsistency_eq_localChecked m
    · subst hcode_eq
      exact cert.reflectionGraft_eq_localChecked m
  · intro hsem
    exact ⟨{
      partialConsistency_eq_localChecked := by
        intro m
        exact hsem.proof_length_eq
          (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
      reflectionGraft_eq_localChecked := by
        intro m
        exact hsem.proof_length_eq
          (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) }⟩

structure Month6ProofLengthFreeLocalCodeClosure
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  checker_exactness :
    PAHilbertLocalCheckerExactness interp
  target_minima :
    Month6MiniHilbertMinimaCertificate interp.target_proof_family
  source_minima :
    Month6MiniHilbertMinimaCertificate
      interp.target_proof_family.rightConjElim
  source_minProofCodeSize_eq_minChecked :
    ∀ m : Nat,
      interp.localHilbertProofCodeSemantics.minProofCodeSize
          (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩) =
        interp.target_proof_family.rightConjElim.minCheckedCodeSize m
  target_minProofCodeSize_eq_minChecked :
    ∀ m : Nat,
      interp.localHilbertProofCodeSemantics.minProofCodeSize
          (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) =
        interp.target_proof_family.minCheckedCodeSize m
  rightConjElim_minProofCodeSize_le_add_two :
    ∀ m : Nat,
      interp.localHilbertProofCodeSemantics.minProofCodeSize
          (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩) ≤
        interp.localHilbertProofCodeSemantics.minProofCodeSize
          (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) + 2

namespace Month6ProofLengthFreeLocalCodeClosure

theorem ofInterpretation
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Month6ProofLengthFreeLocalCodeClosure interp where
  checker_exactness := interp.localHilbertCheckerExactness
  target_minima :=
    Month6MiniHilbertMinimaCertificate.ofConcreteProofFamily
      interp.target_proof_family
  source_minima :=
    Month6MiniHilbertMinimaCertificate.ofConcreteProofFamily
      interp.target_proof_family.rightConjElim
  source_minProofCodeSize_eq_minChecked :=
    interp.localHilbertProofCodeSemantics_source_min_eq
  target_minProofCodeSize_eq_minChecked :=
    interp.localHilbertProofCodeSemantics_target_min_eq
  rightConjElim_minProofCodeSize_le_add_two :=
    interp.localHilbertProofCodeSemantics_rightConjElim_le_add_two

end Month6ProofLengthFreeLocalCodeClosure

theorem month6ProofLengthFreeLocalCodeClosure_nonempty
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthFreeLocalCodeClosure interp) :=
  ⟨Month6ProofLengthFreeLocalCodeClosure.ofInterpretation interp⟩

abbrev Month6ProofLengthAxiomFrontier
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop :=
  Nonempty (Month6ProofLengthFreeLocalCodeClosure interp) ∧
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode

structure Month6CheckedCodeReplacementCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) : Prop where
  calibration :
    Month6ProofLengthCalibrationCertificate interp
  target_minima :
    Month6MiniHilbertMinimaCertificate interp.target_proof_family
  source_minima :
    Month6MiniHilbertMinimaCertificate
      interp.target_proof_family.rightConjElim

namespace Month6ProofLengthFreeLocalCodeClosure

def toCheckedCodeReplacementCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (closure : Month6ProofLengthFreeLocalCodeClosure interp)
    (exact : Month6ExactLocalProofCodeSemanticsCertificate interp) :
    Month6CheckedCodeReplacementCertificate interp where
  calibration := exact.toCalibrationCertificate
  target_minima := closure.target_minima
  source_minima := closure.source_minima

end Month6ProofLengthFreeLocalCodeClosure

namespace Month6CheckedCodeReplacementCertificate

def ofCalibration
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (calibration : Month6ProofLengthCalibrationCertificate interp) :
    Month6CheckedCodeReplacementCertificate interp where
  calibration := calibration
  target_minima :=
    Month6MiniHilbertMinimaCertificate.ofConcreteProofFamily
      interp.target_proof_family
  source_minima :=
    Month6MiniHilbertMinimaCertificate.ofConcreteProofFamily
      interp.target_proof_family.rightConjElim

theorem toProjectCheckedCodeSemantics
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6CheckedCodeReplacementCertificate interp) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode :=
  cert.calibration.toProjectCheckedCodeSemantics

theorem toSplitMinCheckedExactness
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6CheckedCodeReplacementCertificate interp) :
    PAHilbertPartialConsistencyMinCheckedExactness interp ∧
      PAHilbertReflectionGraftMinCheckedExactness interp :=
  cert.calibration.toSplitMinCheckedExactness

theorem toFamilyExactness
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6CheckedCodeReplacementCertificate interp) :
    PAHilbertProjectionFamilyExactness interp :=
  cert.calibration.toFamilyExactness

def toProofCodeCheckerRecognition
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6CheckedCodeReplacementCertificate interp)
    (fallback_length : FormulaCode → Nat) :
    PAHilbertProofCodeCheckerRecognition interp :=
  cert.calibration.toLocalProofCodeRecognition.toProofCodeCheckerRecognition
    fallback_length

theorem partialConsistency_exact_minCodeSize
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6CheckedCodeReplacementCertificate interp)
    (m : Nat) :
    proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minCodeSize m := by
  rw [cert.calibration.partialConsistency_exact m,
    cert.source_minima.minChecked_eq_minCode m]

theorem partialConsistency_exact_minLength
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6CheckedCodeReplacementCertificate interp)
    (m : Nat) :
    proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minLength m := by
  rw [cert.calibration.partialConsistency_exact m,
    cert.source_minima.minChecked_eq_minLength m]

theorem reflectionGraft_exact_minCodeSize
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6CheckedCodeReplacementCertificate interp)
    (m : Nat) :
    proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) =
      interp.target_proof_family.minCodeSize m := by
  rw [cert.calibration.reflectionGraft_exact m,
    cert.target_minima.minChecked_eq_minCode m]

theorem reflectionGraft_exact_minLength
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6CheckedCodeReplacementCertificate interp)
    (m : Nat) :
    proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
        (sondowReflectionGraftCode m) =
      interp.target_proof_family.minLength m := by
  rw [cert.calibration.reflectionGraft_exact m,
    cert.target_minima.minChecked_eq_minLength m]

end Month6CheckedCodeReplacementCertificate

theorem checkedCodeReplacement_nonempty_iff_month6CalibrationCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      Nonempty (Month6ProofLengthCalibrationCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.calibration⟩
  · intro h
    rcases h with ⟨calibration⟩
    exact ⟨Month6CheckedCodeReplacementCertificate.ofCalibration calibration⟩

theorem checkedCodeReplacement_nonempty_iff_freeClosure_and_exactLocal
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      Nonempty (Month6ProofLengthFreeLocalCodeClosure interp) ∧
        Nonempty (Month6ExactLocalProofCodeSemanticsCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact
      ⟨⟨Month6ProofLengthFreeLocalCodeClosure.ofInterpretation interp⟩,
        ⟨Month6ExactLocalProofCodeSemanticsCertificate.ofLocalProofCodeRecognition
          cert.calibration.toLocalProofCodeRecognition⟩⟩
  · intro h
    rcases h with ⟨⟨closure⟩, ⟨exact⟩⟩
    exact ⟨closure.toCheckedCodeReplacementCertificate exact⟩

theorem checkedCodeReplacement_nonempty_iff_freeClosure_and_projectCheckedSemantics
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      Nonempty (Month6ProofLengthFreeLocalCodeClosure interp) ∧
        ProjectProofLengthSemantics
          ProofSystem.PA ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode := by
  constructor
  · intro h
    have hsplit :=
      (checkedCodeReplacement_nonempty_iff_freeClosure_and_exactLocal
        interp).1 h
    rcases hsplit with ⟨hfree, hexact⟩
    have hresidual :
        Nonempty (Month6TwoFamilyResidualExactnessCertificate interp) :=
      (month6ExactLocalProofCodeSemantics_nonempty_iff_twoFamilyResidualExactness
        interp).1 hexact
    have hboundary :
        Nonempty (Month6TwoFamilyProofLengthBoundaryCertificate interp) :=
      (month6TwoFamilyResidualExactness_nonempty_iff_proofLengthBoundary
        interp).1 hresidual
    exact
      ⟨hfree,
        (month6ProofLengthBoundary_nonempty_iff_projectCheckedCodeSemantics
          interp).1 hboundary⟩
  · intro h
    rcases h with ⟨hfree, hsemantics⟩
    have hboundary :
        Nonempty (Month6TwoFamilyProofLengthBoundaryCertificate interp) :=
      (month6ProofLengthBoundary_nonempty_iff_projectCheckedCodeSemantics
        interp).2 hsemantics
    have hresidual :
        Nonempty (Month6TwoFamilyResidualExactnessCertificate interp) :=
      (month6TwoFamilyResidualExactness_nonempty_iff_proofLengthBoundary
        interp).2 hboundary
    have hexact :
        Nonempty (Month6ExactLocalProofCodeSemanticsCertificate interp) :=
      (month6ExactLocalProofCodeSemantics_nonempty_iff_twoFamilyResidualExactness
        interp).2 hresidual
    exact
      (checkedCodeReplacement_nonempty_iff_freeClosure_and_exactLocal
        interp).2 ⟨hfree, hexact⟩

theorem checkedCodeReplacement_nonempty_iff_proofLengthAxiomFrontier
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6CheckedCodeReplacementCertificate interp) ↔
      Month6ProofLengthAxiomFrontier interp :=
  checkedCodeReplacement_nonempty_iff_freeClosure_and_projectCheckedSemantics
    interp

theorem projectCheckedCodeSemantics_iff_checkedCodeReplacementCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
  (projectCheckedCodeSemantics_iff_month6CalibrationCertificate interp).trans
    (checkedCodeReplacement_nonempty_iff_month6CalibrationCertificate interp).symm

theorem splitMinCheckedExactness_iff_checkedCodeReplacementCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    (PAHilbertPartialConsistencyMinCheckedExactness interp ∧
        PAHilbertReflectionGraftMinCheckedExactness interp) ↔
      Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
  (splitMinCheckedExactness_iff_month6CalibrationCertificate interp).trans
    (checkedCodeReplacement_nonempty_iff_month6CalibrationCertificate interp).symm

theorem localProofCodeRecognition_iff_checkedCodeReplacementCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertLocalProofCodeRecognition interp ↔
      Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
  (localProofCodeRecognition_iff_month6CalibrationCertificate interp).trans
    (checkedCodeReplacement_nonempty_iff_month6CalibrationCertificate interp).symm

theorem familyExactness_iff_checkedCodeReplacementCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    PAHilbertProjectionFamilyExactness interp ↔
      Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
  (familyExactness_iff_month6CalibrationCertificate interp).trans
    (checkedCodeReplacement_nonempty_iff_month6CalibrationCertificate interp).symm

theorem proofCodeCheckerRecognition_iff_checkedCodeReplacementCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (PAHilbertProofCodeCheckerRecognition interp) ↔
      Nonempty (Month6CheckedCodeReplacementCertificate interp) := by
  constructor
  · intro hcheck
    rcases hcheck with ⟨hcheck⟩
    have hlocal : PAHilbertLocalProofCodeRecognition interp :=
      (interp.localProofCodeRecognition_iff_projectCheckedRecognition).2
        hcheck.toProjectCheckedRecognition
    exact
      (localProofCodeRecognition_iff_checkedCodeReplacementCertificate
        interp).1 hlocal
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact ⟨cert.toProofCodeCheckerRecognition (fun _ => 0)⟩

theorem proofLengthCodeCalibration_iff_checkedCodeReplacementCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign)
    (fallback_length : FormulaCode → Nat) :
    (interp.localHilbertProofLengthCodeSemantics fallback_length).Calibration ↔
      Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
  (interp.proofCodeCheckerRecognition_iff_proofLengthCodeCalibration
    fallback_length).symm.trans
    (proofCodeCheckerRecognition_iff_checkedCodeReplacementCertificate interp)

theorem localProofCodeConventionCertificate_iff_checkedCodeReplacementCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (PAHilbertLocalProofCodeConventionCertificate interp) ↔
      Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
  (interp.localProofCodeConventionCertificate_iff_familyExactness).trans
    (familyExactness_iff_checkedCodeReplacementCertificate interp)

structure Month6LocalConventionBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  checker_exactness :
    PAHilbertLocalCheckerExactness interp
  encoder_certificate :
    PAHilbertProjectCheckedRecognitionCertificate interp

structure Month6EncoderBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  convention : PAHilbertProofLengthConvention
  encoder_equivalence :
    FormulaCodeHilbertCheckedCodeEncoderEquivalence interp convention

structure Month6ProofLengthFreeEncoderData
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  length : FormulaCode → Nat
  length_eq_localChecked :
    ∀ code : FormulaCode, FormulaCodeHilbertRelevantCode code →
      length code = interp.localCheckedCodeProofLength code

structure Month6EncoderConventionBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  encoder_data : Month6ProofLengthFreeEncoderData interp
  length_semantics :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      encoder_data.length FormulaCodeHilbertRelevantCode

structure Month6EncoderTwoFamilyLengthSemanticsCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  encoder_data : Month6ProofLengthFreeEncoderData interp
  partialConsistency_eq_length :
    ∀ m : Nat,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) =
        encoder_data.length (partialConsistencyCode m)
  reflectionGraft_eq_length :
    ∀ m : Nat,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode m) =
        encoder_data.length (sondowReflectionGraftCode m)

structure Month6SeparatedTwoFamilyEncoderLengthCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  encoder_data : Month6ProofLengthFreeEncoderData interp
  two_family_boundary : Month6TwoFamilyProofLengthBoundaryCertificate interp

structure Month6SeparatedEncoderResidualExactnessCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  encoder_data : Month6ProofLengthFreeEncoderData interp
  residual_exactness : Month6TwoFamilyResidualExactnessCertificate interp

structure Month6ProofLengthFrontierSplitCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  local_closure : Month6ProofLengthFreeLocalCodeClosure interp
  encoder_data : Month6ProofLengthFreeEncoderData interp
  exact_local_semantics : Month6ExactLocalProofCodeSemanticsCertificate interp

structure Month6LocalRecognitionFrontierCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  local_closure : Month6ProofLengthFreeLocalCodeClosure interp
  encoder_data : Month6ProofLengthFreeEncoderData interp
  local_recognition : PAHilbertLocalProofCodeRecognition interp

structure Month6ProofCodeCheckerFrontierCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  local_closure : Month6ProofLengthFreeLocalCodeClosure interp
  encoder_data : Month6ProofLengthFreeEncoderData interp
  checker_recognition : PAHilbertProofCodeCheckerRecognition interp

structure Month6ProofCodeCheckerCalibrationFrontierCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  local_closure : Month6ProofLengthFreeLocalCodeClosure interp
  encoder_data : Month6ProofLengthFreeEncoderData interp
  fallback_length : FormulaCode → Nat
  checker_calibration :
    (interp.localHilbertProofLengthCodeSemantics fallback_length).Calibration

structure Month6ProofLengthConventionBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  convention : PAHilbertProofLengthConvention
  length_semantics :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      convention.length FormulaCodeHilbertRelevantCode
  encoder_equivalence :
    FormulaCodeHilbertCheckedCodeEncoderEquivalence interp convention

namespace Month6ProofLengthFreeEncoderData

def canonical
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Month6ProofLengthFreeEncoderData interp where
  length := interp.localCheckedCodeProofLength
  length_eq_localChecked := by
    intro _code _hcode
    rfl

def toEncoderEquivalence
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (data : Month6ProofLengthFreeEncoderData interp)
    (hsem :
      ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        data.length FormulaCodeHilbertRelevantCode) :
    FormulaCodeHilbertCheckedCodeEncoderEquivalence interp
      (PAHilbertProofLengthConvention.ofProjectProofLengthSemantics
        data.length hsem) where
  length_eq_localChecked := data.length_eq_localChecked

end Month6ProofLengthFreeEncoderData

theorem month6ProofLengthFreeEncoderData_nonempty
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthFreeEncoderData interp) :=
  ⟨Month6ProofLengthFreeEncoderData.canonical interp⟩

namespace Month6EncoderBoundaryCertificate

def ofRecognitionCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : PAHilbertProjectCheckedRecognitionCertificate interp) :
    Month6EncoderBoundaryCertificate interp where
  convention := cert.convention
  encoder_equivalence := cert.encoder_equivalence

def toRecognitionCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6EncoderBoundaryCertificate interp) :
    PAHilbertProjectCheckedRecognitionCertificate interp where
  convention := cert.convention
  encoder_equivalence := cert.encoder_equivalence

def toProjectCheckedRecognition
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6EncoderBoundaryCertificate interp) :
    PAHilbertProjectCheckedProofLengthRecognition interp :=
  cert.toRecognitionCertificate.toProjectCheckedRecognition

def toProofLengthConventionBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6EncoderBoundaryCertificate interp) :
    Month6ProofLengthConventionBoundaryCertificate interp where
  convention := cert.convention
  length_semantics := cert.convention.toProjectProofLengthSemantics
  encoder_equivalence := cert.encoder_equivalence

def toEncoderConventionBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6EncoderBoundaryCertificate interp) :
    Month6EncoderConventionBoundaryCertificate interp where
  encoder_data := {
    length := cert.convention.length
    length_eq_localChecked := cert.encoder_equivalence.length_eq_localChecked }
  length_semantics := cert.convention.toProjectProofLengthSemantics

end Month6EncoderBoundaryCertificate

namespace Month6EncoderConventionBoundaryCertificate

def toEncoderBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6EncoderConventionBoundaryCertificate interp) :
    Month6EncoderBoundaryCertificate interp where
  convention :=
    PAHilbertProofLengthConvention.ofProjectProofLengthSemantics
      cert.encoder_data.length cert.length_semantics
  encoder_equivalence :=
    cert.encoder_data.toEncoderEquivalence cert.length_semantics

def toTwoFamilyLengthSemanticsCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6EncoderConventionBoundaryCertificate interp) :
    Month6EncoderTwoFamilyLengthSemanticsCertificate interp where
  encoder_data := cert.encoder_data
  partialConsistency_eq_length := by
    intro m
    exact cert.length_semantics.proof_length_eq
      (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
  reflectionGraft_eq_length := by
    intro m
    exact cert.length_semantics.proof_length_eq
      (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)

end Month6EncoderConventionBoundaryCertificate

namespace Month6EncoderTwoFamilyLengthSemanticsCertificate

def toEncoderConventionBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6EncoderTwoFamilyLengthSemanticsCertificate interp) :
    Month6EncoderConventionBoundaryCertificate interp where
  encoder_data := cert.encoder_data
  length_semantics := {
    proof_length_eq := by
      intro code hcode
      rcases hcode with ⟨m, hcode_eq⟩ | ⟨m, hcode_eq⟩
      · subst hcode_eq
        exact cert.partialConsistency_eq_length m
      · subst hcode_eq
        exact cert.reflectionGraft_eq_length m }

def toSeparatedTwoFamilyEncoderLengthCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6EncoderTwoFamilyLengthSemanticsCertificate interp) :
    Month6SeparatedTwoFamilyEncoderLengthCertificate interp where
  encoder_data := cert.encoder_data
  two_family_boundary := {
    partialConsistency_eq_localChecked := by
      intro m
      rw [cert.partialConsistency_eq_length m]
      exact_mod_cast cert.encoder_data.length_eq_localChecked
        (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
    reflectionGraft_eq_localChecked := by
      intro m
      rw [cert.reflectionGraft_eq_length m]
      exact_mod_cast cert.encoder_data.length_eq_localChecked
        (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) }

end Month6EncoderTwoFamilyLengthSemanticsCertificate

namespace Month6SeparatedTwoFamilyEncoderLengthCertificate

def toSeparatedEncoderResidualExactnessCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6SeparatedTwoFamilyEncoderLengthCertificate interp) :
    Month6SeparatedEncoderResidualExactnessCertificate interp where
  encoder_data := cert.encoder_data
  residual_exactness :=
    cert.two_family_boundary.toTwoFamilyResidualExactnessCertificate

def toEncoderTwoFamilyLengthSemanticsCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6SeparatedTwoFamilyEncoderLengthCertificate interp) :
    Month6EncoderTwoFamilyLengthSemanticsCertificate interp where
  encoder_data := cert.encoder_data
  partialConsistency_eq_length := by
    intro m
    rw [cert.two_family_boundary.partialConsistency_eq_localChecked m]
    exact_mod_cast (cert.encoder_data.length_eq_localChecked
      (partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)).symm
  reflectionGraft_eq_length := by
    intro m
    rw [cert.two_family_boundary.reflectionGraft_eq_localChecked m]
    exact_mod_cast (cert.encoder_data.length_eq_localChecked
      (sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)).symm

end Month6SeparatedTwoFamilyEncoderLengthCertificate

namespace Month6SeparatedEncoderResidualExactnessCertificate

def toSeparatedTwoFamilyEncoderLengthCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6SeparatedEncoderResidualExactnessCertificate interp) :
    Month6SeparatedTwoFamilyEncoderLengthCertificate interp where
  encoder_data := cert.encoder_data
  two_family_boundary :=
    cert.residual_exactness.toProofLengthBoundaryCertificate

def toFrontierSplitCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6SeparatedEncoderResidualExactnessCertificate interp) :
    Month6ProofLengthFrontierSplitCertificate interp where
  local_closure := Month6ProofLengthFreeLocalCodeClosure.ofInterpretation interp
  encoder_data := cert.encoder_data
  exact_local_semantics :=
    cert.residual_exactness.toExactLocalProofCodeSemanticsCertificate

end Month6SeparatedEncoderResidualExactnessCertificate

namespace Month6ProofLengthFrontierSplitCertificate

def toLocalRecognitionFrontierCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthFrontierSplitCertificate interp) :
    Month6LocalRecognitionFrontierCertificate interp where
  local_closure := cert.local_closure
  encoder_data := cert.encoder_data
  local_recognition := cert.exact_local_semantics.toLocalProofCodeRecognition

def toProofCodeCheckerFrontierCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthFrontierSplitCertificate interp) :
    Month6ProofCodeCheckerFrontierCertificate interp where
  local_closure := cert.local_closure
  encoder_data := cert.encoder_data
  checker_recognition :=
    cert.exact_local_semantics.toLocalProofCodeRecognition
      |>.toProofCodeCheckerRecognition (fun _ => 0)

def toSeparatedEncoderResidualExactnessCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthFrontierSplitCertificate interp) :
    Month6SeparatedEncoderResidualExactnessCertificate interp where
  encoder_data := cert.encoder_data
  residual_exactness :=
    cert.exact_local_semantics.toTwoFamilyResidualExactnessCertificate

theorem toProjectCheckedCodeSemantics
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthFrontierSplitCertificate interp) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode :=
  cert.exact_local_semantics.toCalibrationCertificate.toProjectCheckedCodeSemantics

end Month6ProofLengthFrontierSplitCertificate

namespace Month6LocalRecognitionFrontierCertificate

def toFrontierSplitCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6LocalRecognitionFrontierCertificate interp) :
    Month6ProofLengthFrontierSplitCertificate interp where
  local_closure := cert.local_closure
  encoder_data := cert.encoder_data
  exact_local_semantics :=
    Month6ExactLocalProofCodeSemanticsCertificate.ofLocalProofCodeRecognition
      cert.local_recognition

def toProofCodeCheckerFrontierCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6LocalRecognitionFrontierCertificate interp) :
    Month6ProofCodeCheckerFrontierCertificate interp where
  local_closure := cert.local_closure
  encoder_data := cert.encoder_data
  checker_recognition :=
    cert.local_recognition.toProofCodeCheckerRecognition (fun _ => 0)

end Month6LocalRecognitionFrontierCertificate

namespace Month6ProofCodeCheckerFrontierCertificate

def toLocalRecognitionFrontierCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofCodeCheckerFrontierCertificate interp) :
    Month6LocalRecognitionFrontierCertificate interp where
  local_closure := cert.local_closure
  encoder_data := cert.encoder_data
  local_recognition :=
    (FormulaCodeHilbertInterpretation.localProofCodeRecognition_iff_projectCheckedRecognition
      interp).2 cert.checker_recognition.toProjectCheckedRecognition

def toFrontierSplitCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofCodeCheckerFrontierCertificate interp) :
    Month6ProofLengthFrontierSplitCertificate interp :=
  cert.toLocalRecognitionFrontierCertificate.toFrontierSplitCertificate

def toProofCodeCheckerCalibrationFrontierCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofCodeCheckerFrontierCertificate interp) :
    Month6ProofCodeCheckerCalibrationFrontierCertificate interp where
  local_closure := cert.local_closure
  encoder_data := cert.encoder_data
  fallback_length := cert.checker_recognition.fallback_length
  checker_calibration :=
    cert.checker_recognition.toProofLengthCodeCalibration
      cert.checker_recognition.fallback_length

end Month6ProofCodeCheckerFrontierCertificate

namespace Month6ProofCodeCheckerCalibrationFrontierCertificate

def toProofCodeCheckerFrontierCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofCodeCheckerCalibrationFrontierCertificate interp) :
    Month6ProofCodeCheckerFrontierCertificate interp where
  local_closure := cert.local_closure
  encoder_data := cert.encoder_data
  checker_recognition :=
    PAHilbertProofCodeCheckerRecognition.ofProofLengthCodeCalibration
      cert.fallback_length cert.checker_calibration

def toFrontierSplitCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofCodeCheckerCalibrationFrontierCertificate interp) :
    Month6ProofLengthFrontierSplitCertificate interp :=
  cert.toProofCodeCheckerFrontierCertificate.toFrontierSplitCertificate

end Month6ProofCodeCheckerCalibrationFrontierCertificate

namespace Month6ProofLengthConventionBoundaryCertificate

def toEncoderBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthConventionBoundaryCertificate interp) :
    Month6EncoderBoundaryCertificate interp where
  convention := cert.convention
  encoder_equivalence := cert.encoder_equivalence

def toRecognitionCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthConventionBoundaryCertificate interp) :
    PAHilbertProjectCheckedRecognitionCertificate interp :=
  cert.toEncoderBoundaryCertificate.toRecognitionCertificate

def toProjectCheckedRecognition
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthConventionBoundaryCertificate interp) :
    PAHilbertProjectCheckedProofLengthRecognition interp :=
  cert.toEncoderBoundaryCertificate.toProjectCheckedRecognition

end Month6ProofLengthConventionBoundaryCertificate

theorem month6EncoderBoundary_nonempty_iff_recognitionCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderBoundaryCertificate interp) ↔
      Nonempty (PAHilbertProjectCheckedRecognitionCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toRecognitionCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨Month6EncoderBoundaryCertificate.ofRecognitionCertificate cert⟩

theorem month6EncoderBoundary_nonempty_iff_encoderConventionBoundary
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderBoundaryCertificate interp) ↔
      Nonempty (Month6EncoderConventionBoundaryCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toEncoderConventionBoundaryCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toEncoderBoundaryCertificate⟩

theorem month6EncoderConventionBoundary_nonempty_iff_twoFamilyLengthSemantics
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderConventionBoundaryCertificate interp) ↔
      Nonempty (Month6EncoderTwoFamilyLengthSemanticsCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toTwoFamilyLengthSemanticsCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toEncoderConventionBoundaryCertificate⟩

theorem month6EncoderBoundary_nonempty_iff_twoFamilyLengthSemantics
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderBoundaryCertificate interp) ↔
      Nonempty (Month6EncoderTwoFamilyLengthSemanticsCertificate interp) :=
  (month6EncoderBoundary_nonempty_iff_encoderConventionBoundary
    interp).trans
    (month6EncoderConventionBoundary_nonempty_iff_twoFamilyLengthSemantics
      interp)

theorem month6EncoderTwoFamilyLengthSemantics_nonempty_iff_separatedEncoderLength
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderTwoFamilyLengthSemanticsCertificate interp) ↔
      Nonempty (Month6SeparatedTwoFamilyEncoderLengthCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toSeparatedTwoFamilyEncoderLengthCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toEncoderTwoFamilyLengthSemanticsCertificate⟩

theorem month6EncoderConventionBoundary_nonempty_iff_separatedEncoderLength
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderConventionBoundaryCertificate interp) ↔
      Nonempty (Month6SeparatedTwoFamilyEncoderLengthCertificate interp) :=
  (month6EncoderConventionBoundary_nonempty_iff_twoFamilyLengthSemantics
    interp).trans
    (month6EncoderTwoFamilyLengthSemantics_nonempty_iff_separatedEncoderLength
      interp)

theorem month6EncoderBoundary_nonempty_iff_separatedEncoderLength
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6EncoderBoundaryCertificate interp) ↔
      Nonempty (Month6SeparatedTwoFamilyEncoderLengthCertificate interp) :=
  (month6EncoderBoundary_nonempty_iff_twoFamilyLengthSemantics interp).trans
    (month6EncoderTwoFamilyLengthSemantics_nonempty_iff_separatedEncoderLength
      interp)

theorem month6SeparatedEncoderLength_nonempty_iff_residualExactness
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6SeparatedTwoFamilyEncoderLengthCertificate interp) ↔
      Nonempty (Month6SeparatedEncoderResidualExactnessCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toSeparatedEncoderResidualExactnessCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toSeparatedTwoFamilyEncoderLengthCertificate⟩

theorem month6SeparatedEncoderResidualExactness_nonempty_iff_frontierSplit
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6SeparatedEncoderResidualExactnessCertificate interp) ↔
      Nonempty (Month6ProofLengthFrontierSplitCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toFrontierSplitCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toSeparatedEncoderResidualExactnessCertificate⟩

theorem month6SeparatedEncoderLength_nonempty_iff_frontierSplit
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6SeparatedTwoFamilyEncoderLengthCertificate interp) ↔
      Nonempty (Month6ProofLengthFrontierSplitCertificate interp) :=
  (month6SeparatedEncoderLength_nonempty_iff_residualExactness interp).trans
    (month6SeparatedEncoderResidualExactness_nonempty_iff_frontierSplit
      interp)

theorem month6FrontierSplit_nonempty_iff_localRecognitionFrontier
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthFrontierSplitCertificate interp) ↔
      Nonempty (Month6LocalRecognitionFrontierCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toLocalRecognitionFrontierCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toFrontierSplitCertificate⟩

theorem month6LocalRecognitionFrontier_nonempty_iff_proofCodeCheckerFrontier
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6LocalRecognitionFrontierCertificate interp) ↔
      Nonempty (Month6ProofCodeCheckerFrontierCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toProofCodeCheckerFrontierCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toLocalRecognitionFrontierCertificate⟩

theorem month6FrontierSplit_nonempty_iff_proofCodeCheckerFrontier
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthFrontierSplitCertificate interp) ↔
      Nonempty (Month6ProofCodeCheckerFrontierCertificate interp) :=
  (month6FrontierSplit_nonempty_iff_localRecognitionFrontier interp).trans
    (month6LocalRecognitionFrontier_nonempty_iff_proofCodeCheckerFrontier
      interp)

theorem month6ProofCodeCheckerFrontier_nonempty_iff_calibrationFrontier
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofCodeCheckerFrontierCertificate interp) ↔
      Nonempty
        (Month6ProofCodeCheckerCalibrationFrontierCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toProofCodeCheckerCalibrationFrontierCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toProofCodeCheckerFrontierCertificate⟩

theorem month6FrontierSplit_nonempty_iff_calibrationFrontier
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthFrontierSplitCertificate interp) ↔
      Nonempty
        (Month6ProofCodeCheckerCalibrationFrontierCertificate interp) :=
  (month6FrontierSplit_nonempty_iff_proofCodeCheckerFrontier interp).trans
    (month6ProofCodeCheckerFrontier_nonempty_iff_calibrationFrontier
      interp)

theorem month6ProofLengthConventionBoundary_nonempty_iff_encoderBoundary
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthConventionBoundaryCertificate interp) ↔
      Nonempty (Month6EncoderBoundaryCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toEncoderBoundaryCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toProofLengthConventionBoundaryCertificate⟩

theorem month6ProofLengthConventionBoundary_nonempty_iff_recognitionCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthConventionBoundaryCertificate interp) ↔
      Nonempty (PAHilbertProjectCheckedRecognitionCertificate interp) :=
  (month6ProofLengthConventionBoundary_nonempty_iff_encoderBoundary
    interp).trans
    (month6EncoderBoundary_nonempty_iff_recognitionCertificate interp)

namespace Month6LocalConventionBoundaryCertificate

def ofLocalConventionCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : PAHilbertLocalProofCodeConventionCertificate interp) :
    Month6LocalConventionBoundaryCertificate interp where
  checker_exactness := cert.checker_exactness
  encoder_certificate := cert.encoder_certificate

def toEncoderBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6LocalConventionBoundaryCertificate interp) :
    Month6EncoderBoundaryCertificate interp :=
  Month6EncoderBoundaryCertificate.ofRecognitionCertificate
    cert.encoder_certificate

def toLocalConventionCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6LocalConventionBoundaryCertificate interp) :
    PAHilbertLocalProofCodeConventionCertificate interp where
  checker_exactness := cert.checker_exactness
  encoder_certificate := cert.encoder_certificate

theorem toLocalProofCodeRecognition
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6LocalConventionBoundaryCertificate interp) :
    PAHilbertLocalProofCodeRecognition interp :=
  cert.toLocalConventionCertificate.toLocalProofCodeRecognition

end Month6LocalConventionBoundaryCertificate

theorem month6LocalConventionBoundary_nonempty_iff_localConventionCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6LocalConventionBoundaryCertificate interp) ↔
      Nonempty (PAHilbertLocalProofCodeConventionCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toLocalConventionCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact
      ⟨Month6LocalConventionBoundaryCertificate.ofLocalConventionCertificate
        cert⟩

theorem month6LocalConventionBoundary_nonempty_iff_checker_and_encoder
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6LocalConventionBoundaryCertificate interp) ↔
      Nonempty (PAHilbertLocalCheckerExactness interp) ∧
        Nonempty (Month6EncoderBoundaryCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨⟨cert.checker_exactness⟩,
      ⟨cert.toEncoderBoundaryCertificate⟩⟩
  · intro h
    rcases h with ⟨⟨checker⟩, ⟨encoder⟩⟩
    exact ⟨{
      checker_exactness := checker
      encoder_certificate := encoder.toRecognitionCertificate }⟩

theorem month6LocalConventionBoundary_nonempty_iff_checker_and_lengthConvention
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6LocalConventionBoundaryCertificate interp) ↔
      Nonempty (PAHilbertLocalCheckerExactness interp) ∧
        Nonempty (Month6ProofLengthConventionBoundaryCertificate interp) := by
  constructor
  · intro h
    have hsplit :=
      (month6LocalConventionBoundary_nonempty_iff_checker_and_encoder
        interp).1 h
    rcases hsplit with ⟨hchecker, hencoder⟩
    exact
      ⟨hchecker,
        (month6ProofLengthConventionBoundary_nonempty_iff_encoderBoundary
          interp).2 hencoder⟩
  · intro h
    rcases h with ⟨hchecker, hlength⟩
    exact
      (month6LocalConventionBoundary_nonempty_iff_checker_and_encoder
        interp).2
        ⟨hchecker,
          (month6ProofLengthConventionBoundary_nonempty_iff_encoderBoundary
            interp).1 hlength⟩

structure Month6ProofLengthInternalizationAuditCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) where
  replacement :
    Month6CheckedCodeReplacementCertificate interp
  project_checked_semantics :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode
  local_proof_code_recognition :
    PAHilbertLocalProofCodeRecognition interp
  family_exactness :
    PAHilbertProjectionFamilyExactness interp
  split_min_checked_exactness :
    PAHilbertPartialConsistencyMinCheckedExactness interp ∧
      PAHilbertReflectionGraftMinCheckedExactness interp
  local_convention_certificate :
    Nonempty (PAHilbertLocalProofCodeConventionCertificate interp)
  target_minChecked_eq_minCode :
    ∀ m : Nat,
      interp.target_proof_family.minCheckedCodeSize m =
        interp.target_proof_family.minCodeSize m
  target_minChecked_eq_minLength :
    ∀ m : Nat,
      interp.target_proof_family.minCheckedCodeSize m =
        interp.target_proof_family.minLength m
  source_minChecked_eq_minCode :
    ∀ m : Nat,
      interp.target_proof_family.rightConjElim.minCheckedCodeSize m =
        interp.target_proof_family.rightConjElim.minCodeSize m
  source_minChecked_eq_minLength :
    ∀ m : Nat,
      interp.target_proof_family.rightConjElim.minCheckedCodeSize m =
        interp.target_proof_family.rightConjElim.minLength m
  partialConsistency_exact_minCodeSize :
    ∀ m : Nat,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) =
        interp.target_proof_family.rightConjElim.minCodeSize m
  partialConsistency_exact_minLength :
    ∀ m : Nat,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (partialConsistencyCode m) =
        interp.target_proof_family.rightConjElim.minLength m
  reflectionGraft_exact_minCodeSize :
    ∀ m : Nat,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode m) =
        interp.target_proof_family.minCodeSize m
  reflectionGraft_exact_minLength :
    ∀ m : Nat,
      proof_length ProofSystem.PA ProofLengthMeasure.symbolSize
          (sondowReflectionGraftCode m) =
        interp.target_proof_family.minLength m

namespace Month6ProofLengthInternalizationAuditCertificate

def ofCheckedReplacement
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6CheckedCodeReplacementCertificate interp) :
    Month6ProofLengthInternalizationAuditCertificate interp where
  replacement := cert
  project_checked_semantics := cert.toProjectCheckedCodeSemantics
  local_proof_code_recognition :=
    cert.calibration.toLocalProofCodeRecognition
  family_exactness := cert.toFamilyExactness
  split_min_checked_exactness := cert.toSplitMinCheckedExactness
  local_convention_certificate :=
    (localProofCodeConventionCertificate_iff_checkedCodeReplacementCertificate
      interp).2 ⟨cert⟩
  target_minChecked_eq_minCode :=
    cert.target_minima.minChecked_eq_minCode
  target_minChecked_eq_minLength :=
    cert.target_minima.minChecked_eq_minLength
  source_minChecked_eq_minCode :=
    cert.source_minima.minChecked_eq_minCode
  source_minChecked_eq_minLength :=
    cert.source_minima.minChecked_eq_minLength
  partialConsistency_exact_minCodeSize :=
    cert.partialConsistency_exact_minCodeSize
  partialConsistency_exact_minLength :=
    cert.partialConsistency_exact_minLength
  reflectionGraft_exact_minCodeSize :=
    cert.reflectionGraft_exact_minCodeSize
  reflectionGraft_exact_minLength :=
    cert.reflectionGraft_exact_minLength

noncomputable def ofLocalConventionCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : PAHilbertLocalProofCodeConventionCertificate interp) :
    Month6ProofLengthInternalizationAuditCertificate interp := by
  have hreplacement :
      Nonempty (Month6CheckedCodeReplacementCertificate interp) :=
    (localProofCodeConventionCertificate_iff_checkedCodeReplacementCertificate
      interp).1 ⟨cert⟩
  rcases hreplacement with ⟨replacement⟩
  exact ofCheckedReplacement replacement

noncomputable def ofLocalConventionBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6LocalConventionBoundaryCertificate interp) :
    Month6ProofLengthInternalizationAuditCertificate interp :=
  ofLocalConventionCertificate cert.toLocalConventionCertificate

def toCheckedReplacement
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthInternalizationAuditCertificate interp) :
    Month6CheckedCodeReplacementCertificate interp :=
  cert.replacement

def proofCodeCheckerRecognition
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthInternalizationAuditCertificate interp)
    (fallback_length : FormulaCode → Nat) :
    PAHilbertProofCodeCheckerRecognition interp :=
  cert.replacement.toProofCodeCheckerRecognition fallback_length

theorem proofLengthCodeCalibration
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthInternalizationAuditCertificate interp)
    (fallback_length : FormulaCode → Nat) :
    (interp.localHilbertProofLengthCodeSemantics
      fallback_length).Calibration :=
  (proofLengthCodeCalibration_iff_checkedCodeReplacementCertificate
    interp fallback_length).2 ⟨cert.replacement⟩

theorem localConventionCertificate_is_boundary
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthInternalizationAuditCertificate interp) :
    Nonempty (PAHilbertLocalProofCodeConventionCertificate interp) :=
  cert.local_convention_certificate

theorem localConventionBoundary_is_boundary
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6ProofLengthInternalizationAuditCertificate interp) :
    Nonempty (Month6LocalConventionBoundaryCertificate interp) :=
  (month6LocalConventionBoundary_nonempty_iff_localConventionCertificate
    interp).2 cert.local_convention_certificate

end Month6ProofLengthInternalizationAuditCertificate

theorem month6ProofLengthInternalizationAudit_nonempty_iff_checkedReplacement
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6ProofLengthInternalizationAuditCertificate interp) ↔
      Nonempty (Month6CheckedCodeReplacementCertificate interp) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toCheckedReplacement⟩
  · intro h
    rcases h with ⟨cert⟩
    exact
      ⟨Month6ProofLengthInternalizationAuditCertificate.ofCheckedReplacement
        cert⟩

theorem projectCheckedCodeSemantics_iff_month6InternalizationAudit
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6ProofLengthInternalizationAuditCertificate interp) :=
  (projectCheckedCodeSemantics_iff_checkedCodeReplacementCertificate
    interp).trans
    (month6ProofLengthInternalizationAudit_nonempty_iff_checkedReplacement
      interp).symm

theorem localProofCodeConventionCertificate_iff_month6InternalizationAudit
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (PAHilbertLocalProofCodeConventionCertificate interp) ↔
      Nonempty (Month6ProofLengthInternalizationAuditCertificate interp) :=
  (localProofCodeConventionCertificate_iff_checkedCodeReplacementCertificate
    interp).trans
    (month6ProofLengthInternalizationAudit_nonempty_iff_checkedReplacement
      interp).symm

theorem localConventionBoundary_iff_month6InternalizationAudit
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month6LocalConventionBoundaryCertificate interp) ↔
      Nonempty (Month6ProofLengthInternalizationAuditCertificate interp) :=
  (month6LocalConventionBoundary_nonempty_iff_localConventionCertificate
    interp).trans
    (localProofCodeConventionCertificate_iff_month6InternalizationAudit
      interp)

theorem projectCheckedCodeSemantics_iff_localConventionBoundary
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6LocalConventionBoundaryCertificate interp) :=
  (projectCheckedCodeSemantics_iff_month6InternalizationAudit
    interp).trans
    (localConventionBoundary_iff_month6InternalizationAudit interp).symm

theorem projectCheckedCodeSemantics_iff_encoderBoundary
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6EncoderBoundaryCertificate interp) := by
  constructor
  · intro hsemantics
    have hboundary :
        Nonempty (Month6LocalConventionBoundaryCertificate interp) :=
      (projectCheckedCodeSemantics_iff_localConventionBoundary interp).1
        hsemantics
    exact
      (month6LocalConventionBoundary_nonempty_iff_checker_and_encoder
        interp).1 hboundary |>.2
  · intro hencoder
    rcases hencoder with ⟨encoder⟩
    exact encoder.toProjectCheckedRecognition.toProjectProofLengthSemantics

theorem projectCheckedCodeSemantics_iff_encoderConventionBoundary
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6EncoderConventionBoundaryCertificate interp) := by
  constructor
  · intro hsemantics
    exact ⟨{
      encoder_data := Month6ProofLengthFreeEncoderData.canonical interp
      length_semantics := hsemantics }⟩
  · intro hboundary
    rcases hboundary with ⟨cert⟩
    refine ⟨?_⟩
    intro code hcode
    rw [cert.length_semantics.proof_length_eq code hcode]
    exact_mod_cast cert.encoder_data.length_eq_localChecked code hcode

theorem projectCheckedCodeSemantics_iff_twoFamilyLengthSemantics
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6EncoderTwoFamilyLengthSemanticsCertificate interp) :=
  (projectCheckedCodeSemantics_iff_encoderConventionBoundary interp).trans
    (month6EncoderConventionBoundary_nonempty_iff_twoFamilyLengthSemantics
      interp)

theorem projectCheckedCodeSemantics_iff_separatedEncoderLength
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6SeparatedTwoFamilyEncoderLengthCertificate interp) :=
  (projectCheckedCodeSemantics_iff_twoFamilyLengthSemantics interp).trans
    (month6EncoderTwoFamilyLengthSemantics_nonempty_iff_separatedEncoderLength
      interp)

theorem projectCheckedCodeSemantics_iff_frontierSplit
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6ProofLengthFrontierSplitCertificate interp) :=
  (projectCheckedCodeSemantics_iff_separatedEncoderLength interp).trans
    (month6SeparatedEncoderLength_nonempty_iff_frontierSplit interp)

theorem projectCheckedCodeSemantics_iff_proofCodeCheckerFrontier
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6ProofCodeCheckerFrontierCertificate interp) :=
  (projectCheckedCodeSemantics_iff_frontierSplit interp).trans
    (month6FrontierSplit_nonempty_iff_proofCodeCheckerFrontier interp)

theorem projectCheckedCodeSemantics_iff_checkerCalibrationFrontier
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty
        (Month6ProofCodeCheckerCalibrationFrontierCertificate interp) :=
  (projectCheckedCodeSemantics_iff_proofCodeCheckerFrontier interp).trans
    (month6ProofCodeCheckerFrontier_nonempty_iff_calibrationFrontier
      interp)

theorem projectCheckedCodeSemantics_iff_proofLengthConventionBoundary
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty (Month6ProofLengthConventionBoundaryCertificate interp) :=
  (projectCheckedCodeSemantics_iff_encoderBoundary interp).trans
    (month6ProofLengthConventionBoundary_nonempty_iff_encoderBoundary
      interp).symm

theorem projectCheckedCodeSemantics_iff_checker_and_encoder
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty (PAHilbertLocalCheckerExactness interp) ∧
        Nonempty (Month6EncoderBoundaryCertificate interp) :=
  (projectCheckedCodeSemantics_iff_localConventionBoundary interp).trans
    (month6LocalConventionBoundary_nonempty_iff_checker_and_encoder
      interp)

theorem projectCheckedCodeSemantics_iff_checker_and_lengthConvention
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    (interp : FormulaCodeHilbertInterpretation Ax A B halign) :
    ProjectProofLengthSemantics
        ProofSystem.PA ProofLengthMeasure.symbolSize
        interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode ↔
      Nonempty (PAHilbertLocalCheckerExactness interp) ∧
        Nonempty (Month6ProofLengthConventionBoundaryCertificate interp) :=
  (projectCheckedCodeSemantics_iff_localConventionBoundary interp).trans
    (month6LocalConventionBoundary_nonempty_iff_checker_and_lengthConvention
      interp)

theorem month6InternalizationAudit_of_localConventionCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : PAHilbertLocalProofCodeConventionCertificate interp) :
    Nonempty (Month6ProofLengthInternalizationAuditCertificate interp) :=
  ⟨Month6ProofLengthInternalizationAuditCertificate.ofLocalConventionCertificate
    cert⟩

theorem month6InternalizationAudit_of_localConventionBoundaryCertificate
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month6LocalConventionBoundaryCertificate interp) :
    Nonempty (Month6ProofLengthInternalizationAuditCertificate interp) :=
  ⟨Month6ProofLengthInternalizationAuditCertificate.ofLocalConventionBoundaryCertificate
    cert⟩

theorem month6InternalizationAudit_nonempty_to_projectCheckedSemantics
    {L : FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : HilbertProjectionCodeAlignment}
    {interp : FormulaCodeHilbertInterpretation Ax A B halign}
    (h :
      Nonempty (Month6ProofLengthInternalizationAuditCertificate interp)) :
    ProjectProofLengthSemantics
      ProofSystem.PA ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength FormulaCodeHilbertRelevantCode := by
  rcases h with ⟨cert⟩
  exact cert.project_checked_semantics

end Month6ProofLengthCalibrationInternalizationSurface
end MiniHilbert
