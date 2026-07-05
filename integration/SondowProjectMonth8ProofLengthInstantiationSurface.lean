/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth7FinalCollisionSurface

/-!
# Month 8 proof-length instantiation surface

This module refines the Month 7 proof-length residual frontier.  The old
frontier carried a fallback function and a local code calibration.  Month 8
replaces that public shape by a fallback-free local-recognition residual plus a
fully internal proof-object/checker interface.

The result is not yet a global elimination of `proof_length`: the remaining
project-level obligations are the strengthened-family exactness witness and the
local recognition statement identifying PA symbol-size proof length with the
closed MiniHilbert proof-code minimum on the two project families.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth8ProofLengthInstantiationSurface

universe u v w

open SondowProjectMonth7FinalCollisionSurface

/-- The proof-object/checker part of the Month 8 interface.  This package is
constructible from the local `FormulaCodeHilbertInterpretation`; it contains no
global proof-length calibration field. -/
structure Month8ConcreteProofObjectCheckerInterface
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Prop where
  proof_code_projection :
    _root_.MiniHilbert.LocalHilbertProofCodeProjectionModel interp
  checker_exactness :
    _root_.MiniHilbert.PAHilbertLocalCheckerExactness interp
  free_local_code_closure :
    _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFreeLocalCodeClosure
      interp

namespace Month8ConcreteProofObjectCheckerInterface

theorem ofInterpretation
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Month8ConcreteProofObjectCheckerInterface interp where
  proof_code_projection :=
    interp.localHilbertProofCodeProjectionModel
  checker_exactness :=
    interp.localHilbertCheckerExactness
  free_local_code_closure :=
    _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthFreeLocalCodeClosure.ofInterpretation
      interp

theorem source_minProofCodeSize_eq_minChecked
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (iface : Month8ConcreteProofObjectCheckerInterface interp)
    (m : Nat) :
    interp.localHilbertProofCodeSemantics.minProofCodeSize
        (_root_.partialConsistencyCode m) (Or.inl ⟨m, rfl⟩) =
      interp.target_proof_family.rightConjElim.minCheckedCodeSize m :=
  iface.proof_code_projection.source_exact m

theorem target_minProofCodeSize_eq_minChecked
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (iface : Month8ConcreteProofObjectCheckerInterface interp)
    (m : Nat) :
    interp.localHilbertProofCodeSemantics.minProofCodeSize
        (_root_.sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) =
      interp.target_proof_family.minCheckedCodeSize m :=
  iface.proof_code_projection.target_exact m

theorem source_minProofCodeSize_le_target_add_two
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (iface : Month8ConcreteProofObjectCheckerInterface interp)
    (m : Nat) :
    interp.localHilbertProofCodeSemantics.minProofCodeSize
        (_root_.partialConsistencyCode m) (Or.inl ⟨m, rfl⟩) ≤
      interp.localHilbertProofCodeSemantics.minProofCodeSize
        (_root_.sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) + 2 :=
  iface.proof_code_projection.source_le_target_add_two m

theorem minProofCodeSize_eq_localChecked
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (iface : Month8ConcreteProofObjectCheckerInterface interp)
    (code : _root_.FormulaCode)
    (hcode : _root_.MiniHilbert.FormulaCodeHilbertRelevantCode code) :
    interp.localHilbertProofCodeSemantics.minProofCodeSize code hcode =
      interp.localCheckedCodeProofLength code :=
  iface.checker_exactness.minProofCodeSize_eq_localChecked code hcode

end Month8ConcreteProofObjectCheckerInterface

/-- Month 8 removes the arbitrary fallback function from the public residual.
The remaining local field is the exact recognition statement for the two local
Hilbert proof-code families. -/
structure Month8FallbackFreeProofLengthResidualFrontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Type where
  exact_family_lengths :
    _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths
  proof_object_checker :
    Month8ConcreteProofObjectCheckerInterface interp
  local_recognition :
    _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition interp

namespace Month8FallbackFreeProofLengthResidualFrontier

def ofFamilyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (h :
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp) :
    Month8FallbackFreeProofLengthResidualFrontier interp where
  exact_family_lengths := h.1
  proof_object_checker :=
    Month8ConcreteProofObjectCheckerInterface.ofInterpretation interp
  local_recognition :=
    ((_root_.MiniHilbert.FormulaCodeHilbertInterpretation.localProofCodeRecognition_iff_projectCheckedRecognition
      interp).trans
      (_root_.MiniHilbert.FormulaCodeHilbertInterpretation.projectCheckedRecognition_iff_familyExactness
        interp)).2 h.2

theorem toProjectCheckedRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (h : Month8FallbackFreeProofLengthResidualFrontier interp) :
    _root_.MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition interp :=
  (_root_.MiniHilbert.FormulaCodeHilbertInterpretation.localProofCodeRecognition_iff_projectCheckedRecognition
    interp).1 h.local_recognition

theorem toFamilyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (h : Month8FallbackFreeProofLengthResidualFrontier interp) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp :=
  h.toProjectCheckedRecognition.toFamilyExactness

theorem source_exact_minChecked
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (h : Month8FallbackFreeProofLengthResidualFrontier interp)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.partialConsistencyCode m) =
      interp.target_proof_family.rightConjElim.minCheckedCodeSize m :=
  h.toFamilyExactness.partialConsistency_exact m

theorem target_exact_minChecked
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (h : Month8FallbackFreeProofLengthResidualFrontier interp)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.sondowReflectionGraftCode m) =
      interp.target_proof_family.minCheckedCodeSize m :=
  h.toFamilyExactness.reflectionGraft_exact m

def toMonth7ProofLengthResidual
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (h : Month8FallbackFreeProofLengthResidualFrontier interp) :
    Month8ProofLengthResidualFrontier interp where
  exact_family_lengths := h.exact_family_lengths
  fallback := fun _ => 0
  local_code_calibration :=
    h.local_recognition.toLocalPAHilbertCodeCalibration (fun _ => 0)

end Month8FallbackFreeProofLengthResidualFrontier

def month8_old_proof_length_residual_to_fallback_free
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (h : Month8ProofLengthResidualFrontier interp) :
    Month8FallbackFreeProofLengthResidualFrontier interp where
  exact_family_lengths := h.exact_family_lengths
  proof_object_checker :=
    Month8ConcreteProofObjectCheckerInterface.ofInterpretation interp
  local_recognition :=
    _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition.ofLocalPAHilbertCodeCalibration
      h.fallback h.local_code_calibration

theorem month8_proof_length_residual_nonempty_iff_fallback_free
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign} :
    Nonempty (Month8ProofLengthResidualFrontier interp) ↔
      Nonempty (Month8FallbackFreeProofLengthResidualFrontier interp) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨month8_old_proof_length_residual_to_fallback_free h⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toMonth7ProofLengthResidual⟩

theorem month8_local_recognition_iff_family_exactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition interp ↔
      _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp :=
  (_root_.MiniHilbert.FormulaCodeHilbertInterpretation.localProofCodeRecognition_iff_projectCheckedRecognition
    interp).trans
    (_root_.MiniHilbert.FormulaCodeHilbertInterpretation.projectCheckedRecognition_iff_familyExactness
      interp)

theorem month8_local_recognition_iff_exact_local_proof_code_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition interp ↔
      Nonempty
        (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ExactLocalProofCodeSemanticsCertificate
          interp) :=
  (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.month6ExactLocalProofCodeSemantics_nonempty_iff_localProofCodeRecognition
    interp).symm

theorem month8_fallback_free_residual_nonempty_iff_local_recognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign} :
    Nonempty (Month8FallbackFreeProofLengthResidualFrontier interp) ↔
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition interp := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.exact_family_lengths, h.local_recognition⟩
  · intro h
    exact
      ⟨{ exact_family_lengths := h.1
         proof_object_checker :=
          Month8ConcreteProofObjectCheckerInterface.ofInterpretation interp
         local_recognition := h.2 }⟩

theorem month8_fallback_free_residual_nonempty_iff_family_exactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign} :
    Nonempty (Month8FallbackFreeProofLengthResidualFrontier interp) ↔
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp := by
  constructor
  · intro h
    rcases
      (month8_fallback_free_residual_nonempty_iff_local_recognition).1 h with
      ⟨hexact, hrec⟩
    exact
      ⟨hexact, (month8_local_recognition_iff_family_exactness interp).1 hrec⟩
  · intro h
    exact
      (month8_fallback_free_residual_nonempty_iff_local_recognition).2
        ⟨h.1, (month8_local_recognition_iff_family_exactness interp).2 h.2⟩

theorem month8_fallback_free_residual_nonempty_iff_exact_local_proof_code_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign} :
    Nonempty (Month8FallbackFreeProofLengthResidualFrontier interp) ↔
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ExactLocalProofCodeSemanticsCertificate
            interp) := by
  constructor
  · intro h
    rcases
      (month8_fallback_free_residual_nonempty_iff_local_recognition).1 h with
      ⟨hexact, hrec⟩
    exact
      ⟨hexact,
        (month8_local_recognition_iff_exact_local_proof_code_semantics
          interp).1 hrec⟩
  · intro h
    exact
      (month8_fallback_free_residual_nonempty_iff_local_recognition).2
        ⟨h.1,
          (month8_local_recognition_iff_exact_local_proof_code_semantics
            interp).2 h.2⟩

theorem month8_proof_length_residual_nonempty_iff_family_exactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign} :
    Nonempty (Month8ProofLengthResidualFrontier interp) ↔
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp :=
  month8_proof_length_residual_nonempty_iff_fallback_free.trans
    month8_fallback_free_residual_nonempty_iff_family_exactness

theorem month8_proof_length_residual_nonempty_iff_exact_local_proof_code_semantics
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign} :
    Nonempty (Month8ProofLengthResidualFrontier interp) ↔
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ExactLocalProofCodeSemanticsCertificate
            interp) :=
  month8_proof_length_residual_nonempty_iff_fallback_free.trans
    month8_fallback_free_residual_nonempty_iff_exact_local_proof_code_semantics

def month8_fallback_free_residuals_to_month7_final_core
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual : Month8FallbackFreeProofLengthResidualFrontier interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds) :
    Month7FinalCollisionCoreInputs interp bounds :=
  month8_residual_frontiers_to_month7_final_core
    proof_residual.toMonth7ProofLengthResidual payload_residual

def month8_family_exactness_and_payload_to_month7_final_core
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual :
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds) :
    Month7FinalCollisionCoreInputs interp bounds :=
  month8_fallback_free_residuals_to_month7_final_core
    (Month8FallbackFreeProofLengthResidualFrontier.ofFamilyExactness
      proof_residual)
    payload_residual

def month8_family_exactness_and_payload_to_generic_collision_inputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual :
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds) :
    GenericRationalCollisionInputs :=
  month7_final_collision_core_inputs_to_generic_collision_inputs
    (month8_family_exactness_and_payload_to_month7_final_core
      proof_residual payload_residual)

theorem month8_family_exactness_and_payload_generic_measured_eq_project_box
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual :
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds) :
    (month8_family_exactness_and_payload_to_generic_collision_inputs
        proof_residual payload_residual).measured =
      sondowProjectLocalPudlakCollisionBox :=
  rfl

theorem month8_fallback_free_residuals_not_rational
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual : Month8FallbackFreeProofLengthResidualFrontier interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  month7_final_collision_core_inputs_not_rational
    (month8_fallback_free_residuals_to_month7_final_core
      proof_residual payload_residual)

theorem month8_family_exactness_and_payload_not_rational
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual :
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  month7_final_collision_core_inputs_not_rational
    (month8_family_exactness_and_payload_to_month7_final_core
      proof_residual payload_residual)

theorem month8_fallback_free_residuals_not_rational_eq_generic_skeleton
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual : Month8FallbackFreeProofLengthResidualFrontier interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds) :
    month8_fallback_free_residuals_not_rational
        proof_residual payload_residual =
      (month7_final_collision_core_inputs_to_generic_collision_inputs
        (month8_fallback_free_residuals_to_month7_final_core
          proof_residual payload_residual)).not_rational :=
  rfl

theorem month8_family_exactness_and_payload_not_rational_eq_generic_skeleton
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual :
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds) :
    month8_family_exactness_and_payload_not_rational
        proof_residual payload_residual =
      (month8_family_exactness_and_payload_to_generic_collision_inputs
        proof_residual payload_residual).not_rational :=
  rfl

theorem month8_family_exactness_and_payload_not_rational_eq_generic_core
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual :
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds) :
    month8_family_exactness_and_payload_not_rational
        proof_residual payload_residual =
      GenericRationalCollisionInputs.not_rational
        (month8_family_exactness_and_payload_to_generic_collision_inputs
          proof_residual payload_residual) :=
  rfl

theorem month8_family_exactness_and_payload_contradiction
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual :
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  month8_family_exactness_and_payload_not_rational
    proof_residual payload_residual hrat

theorem month8_fallback_free_residuals_contradiction
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual : Month8FallbackFreeProofLengthResidualFrontier interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  month8_fallback_free_residuals_not_rational
    proof_residual payload_residual hrat

theorem month7_final_core_nonempty_iff_month8_fallback_free_residuals_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month7FinalCollisionCoreInputs interp bounds) ↔
      Nonempty (Month8FallbackFreeProofLengthResidualFrontier interp) ∧
        Nonempty (Month8PayloadLiteratureResidualFrontier.{u} bounds) := by
  constructor
  · intro h
    rcases
      (month7_final_core_nonempty_iff_month8_residual_frontiers_nonempty).1
        h with
      ⟨hproof, hpayload⟩
    exact
      ⟨(month8_proof_length_residual_nonempty_iff_fallback_free).1
          hproof,
        hpayload⟩
  · intro h
    rcases h with ⟨hproof, hpayload⟩
    exact
      (month7_final_core_nonempty_iff_month8_residual_frontiers_nonempty).2
        ⟨(month8_proof_length_residual_nonempty_iff_fallback_free).2
            hproof,
          hpayload⟩

theorem month7_minimal_theorem_surface_nonempty_iff_month8_fallback_free_residuals_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month7MinimalTheoremSurface interp bounds) ↔
      Nonempty (Month8FallbackFreeProofLengthResidualFrontier interp) ∧
        Nonempty (Month8PayloadLiteratureResidualFrontier.{u} bounds) :=
  (Month7MinimalTheoremSurface.nonempty_iff_final_core_inputs_nonempty).trans
    month7_final_core_nonempty_iff_month8_fallback_free_residuals_nonempty

theorem month7_minimal_theorem_surface_nonempty_iff_month8_family_exactness_and_payload
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month7MinimalTheoremSurface interp bounds) ↔
      (_root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp) ∧
        Nonempty (Month8PayloadLiteratureResidualFrontier.{u} bounds) := by
  constructor
  · intro h
    rcases
      (month7_minimal_theorem_surface_nonempty_iff_month8_fallback_free_residuals_nonempty).1
        h with
      ⟨hproof, hpayload⟩
    exact
      ⟨(month8_fallback_free_residual_nonempty_iff_family_exactness).1
          hproof,
        hpayload⟩
  · intro h
    exact
      (month7_minimal_theorem_surface_nonempty_iff_month8_fallback_free_residuals_nonempty).2
        ⟨(month8_fallback_free_residual_nonempty_iff_family_exactness).2
            h.1,
          h.2⟩

/-- Public Month 8 checklist: the proof-length residual is now fallback-free,
and the final Month 7 theorem surface is recovered from the same payload and
literature frontier. -/
structure Month8ProofLengthInstantiationChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (bounds : BoundedArithmeticLab.SondowComponentBounds) :
    Type where
  proof_residual :
    Month8FallbackFreeProofLengthResidualFrontier interp
  payload_residual :
    Month8PayloadLiteratureResidualFrontier.{u} bounds
  minimal_surface :
    Month7MinimalTheoremSurface interp bounds
  minimal_surface_eq :
    minimal_surface =
      Month7MinimalTheoremSurface.ofFinalCoreInputs
        (month8_fallback_free_residuals_to_month7_final_core
          proof_residual payload_residual)

structure Month8RemainingProofLengthCertificateBoundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (bounds : BoundedArithmeticLab.SondowComponentBounds) :
    Type where
  family_exactness :
    _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
      _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp
  payload_literature :
    Nonempty (Month8PayloadLiteratureResidualFrontier.{u} bounds)

structure Month8ConcreteMinProofCodeSizeBoundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (bounds : BoundedArithmeticLab.SondowComponentBounds) :
    Type where
  exact_family_lengths :
    _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths
  proof_object_checker :
    Month8ConcreteProofObjectCheckerInterface interp
  exact_local_proof_code :
    Nonempty
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ExactLocalProofCodeSemanticsCertificate
        interp)
  payload_literature :
    Nonempty (Month8PayloadLiteratureResidualFrontier.{u} bounds)

namespace Month8ConcreteMinProofCodeSizeBoundary

theorem proof_length_eq_minProofCodeSize
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds)
    (code : _root_.FormulaCode)
    (hcode : _root_.MiniHilbert.FormulaCodeHilbertRelevantCode code) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize code =
      interp.localHilbertProofCodeSemantics.minProofCodeSize code hcode := by
  rcases h.exact_local_proof_code with ⟨cert⟩
  exact cert.proof_length_eq_minProofCodeSize code hcode

theorem partialConsistency_exact_minProofCodeSize
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.partialConsistencyCode m) =
      interp.localHilbertProofCodeSemantics.minProofCodeSize
        (_root_.partialConsistencyCode m) (Or.inl ⟨m, rfl⟩) :=
  h.proof_length_eq_minProofCodeSize
    (_root_.partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)

theorem reflectionGraft_exact_minProofCodeSize
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.sondowReflectionGraftCode m) =
      interp.localHilbertProofCodeSemantics.minProofCodeSize
        (_root_.sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩) :=
  h.proof_length_eq_minProofCodeSize
    (_root_.sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)

theorem toLocalProofCodeRecognition
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds) :
    _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition interp := by
  rcases h.exact_local_proof_code with ⟨cert⟩
  exact cert.toLocalProofCodeRecognition

theorem toFamilyExactness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds) :
    _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp :=
  (month8_local_recognition_iff_family_exactness interp).1
    h.toLocalProofCodeRecognition

def toFallbackFreeResidual
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds) :
    Month8FallbackFreeProofLengthResidualFrontier interp where
  exact_family_lengths := h.exact_family_lengths
  proof_object_checker := h.proof_object_checker
  local_recognition := h.toLocalProofCodeRecognition

def toRemainingProofLengthCertificateBoundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds) :
    Month8RemainingProofLengthCertificateBoundary interp bounds where
  family_exactness := ⟨h.exact_family_lengths, h.toFamilyExactness⟩
  payload_literature := h.payload_literature

def payloadWitness
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds) :
    Month8PayloadLiteratureResidualFrontier.{u} bounds :=
  Classical.choice h.payload_literature

def toFinalCoreInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds) :
    Month7FinalCollisionCoreInputs interp bounds :=
  month8_fallback_free_residuals_to_month7_final_core
    h.toFallbackFreeResidual h.payloadWitness

def toGenericCollisionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds) :
    GenericRationalCollisionInputs :=
  month7_final_collision_core_inputs_to_generic_collision_inputs
    h.toFinalCoreInputs

theorem generic_measured_eq_project_box
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds) :
    h.toGenericCollisionInputs.measured =
      sondowProjectLocalPudlakCollisionBox :=
  rfl

theorem not_rational
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toGenericCollisionInputs.not_rational

theorem not_rational_eq_generic_core
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds) :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational
        h.toGenericCollisionInputs :=
  rfl

theorem contradiction
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ConcreteMinProofCodeSizeBoundary interp bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.not_rational hrat

end Month8ConcreteMinProofCodeSizeBoundary

theorem month8_remaining_certificate_boundary_nonempty_iff_concrete_minProofCodeSize_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month8RemainingProofLengthCertificateBoundary interp bounds) ↔
      Nonempty (Month8ConcreteMinProofCodeSizeBoundary interp bounds) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    have hlocal :
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ExactLocalProofCodeSemanticsCertificate
            interp) :=
      (month8_local_recognition_iff_exact_local_proof_code_semantics
        interp).1
        ((month8_local_recognition_iff_family_exactness interp).2
          h.family_exactness.2)
    exact
      ⟨{ exact_family_lengths := h.family_exactness.1
         proof_object_checker :=
          Month8ConcreteProofObjectCheckerInterface.ofInterpretation interp
         exact_local_proof_code := hlocal
         payload_literature := h.payload_literature }⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.toRemainingProofLengthCertificateBoundary⟩

namespace Month8ProofLengthInstantiationChecklist

def ofFallbackFreeResiduals
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual :
      Month8FallbackFreeProofLengthResidualFrontier interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds) :
    Month8ProofLengthInstantiationChecklist interp bounds where
  proof_residual := proof_residual
  payload_residual := payload_residual
  minimal_surface :=
    Month7MinimalTheoremSurface.ofFinalCoreInputs
      (month8_fallback_free_residuals_to_month7_final_core
        proof_residual payload_residual)
  minimal_surface_eq := rfl

theorem nonempty_iff_fallback_free_residuals_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month8ProofLengthInstantiationChecklist interp bounds) ↔
      Nonempty (Month8FallbackFreeProofLengthResidualFrontier interp) ∧
        Nonempty (Month8PayloadLiteratureResidualFrontier.{u} bounds) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨⟨h.proof_residual⟩, ⟨h.payload_residual⟩⟩
  · intro h
    rcases h with ⟨⟨proof_residual⟩, ⟨payload_residual⟩⟩
    exact
      ⟨ofFallbackFreeResiduals proof_residual payload_residual⟩

theorem nonempty_iff_family_exactness_and_payload
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month8ProofLengthInstantiationChecklist interp bounds) ↔
      (_root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        _root_.MiniHilbert.PAHilbertProjectionFamilyExactness interp) ∧
        Nonempty (Month8PayloadLiteratureResidualFrontier.{u} bounds) := by
  constructor
  · intro h
    rcases (nonempty_iff_fallback_free_residuals_nonempty).1 h with
      ⟨hproof, hpayload⟩
    exact
      ⟨(month8_fallback_free_residual_nonempty_iff_family_exactness).1
          hproof,
        hpayload⟩
  · intro h
    exact
      (nonempty_iff_fallback_free_residuals_nonempty).2
        ⟨(month8_fallback_free_residual_nonempty_iff_family_exactness).2
            h.1,
          h.2⟩

theorem nonempty_iff_remaining_certificate_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month8ProofLengthInstantiationChecklist interp bounds) ↔
      Nonempty
        (Month8RemainingProofLengthCertificateBoundary interp bounds) := by
  constructor
  · intro h
    rcases (nonempty_iff_family_exactness_and_payload).1 h with
      ⟨hfamily, hpayload⟩
    exact
      ⟨{ family_exactness := hfamily
         payload_literature := hpayload }⟩
  · intro h
    rcases h with ⟨h⟩
    exact
      (nonempty_iff_family_exactness_and_payload).2
        ⟨h.family_exactness, h.payload_literature⟩

theorem nonempty_iff_concrete_minProofCodeSize_boundary
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month8ProofLengthInstantiationChecklist interp bounds) ↔
      Nonempty (Month8ConcreteMinProofCodeSizeBoundary interp bounds) := by
  constructor
  · intro h
    rcases (nonempty_iff_fallback_free_residuals_nonempty).1 h with
      ⟨hproof, hpayload⟩
    rcases
      (month8_fallback_free_residual_nonempty_iff_exact_local_proof_code_semantics).1
        hproof with
      ⟨hexact, hlocal⟩
    exact
      ⟨{ exact_family_lengths := hexact
         proof_object_checker :=
          Month8ConcreteProofObjectCheckerInterface.ofInterpretation interp
         exact_local_proof_code := hlocal
         payload_literature := hpayload }⟩
  · intro h
    rcases h with ⟨h⟩
    have hproof :
        Nonempty (Month8FallbackFreeProofLengthResidualFrontier interp) :=
      (month8_fallback_free_residual_nonempty_iff_exact_local_proof_code_semantics).2
        ⟨h.exact_family_lengths, h.exact_local_proof_code⟩
    exact
      (nonempty_iff_fallback_free_residuals_nonempty).2
        ⟨hproof, h.payload_literature⟩

theorem nonempty_iff_month7_minimal_surface_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month8ProofLengthInstantiationChecklist interp bounds) ↔
      Nonempty (Month7MinimalTheoremSurface interp bounds) :=
  nonempty_iff_fallback_free_residuals_nonempty.trans
    month7_minimal_theorem_surface_nonempty_iff_month8_fallback_free_residuals_nonempty.symm

def toFinalCoreInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ProofLengthInstantiationChecklist interp bounds) :
    Month7FinalCollisionCoreInputs interp bounds :=
  month8_fallback_free_residuals_to_month7_final_core
    h.proof_residual h.payload_residual

def toGenericCollisionInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ProofLengthInstantiationChecklist interp bounds) :
    GenericRationalCollisionInputs :=
  month7_final_collision_core_inputs_to_generic_collision_inputs
    h.toFinalCoreInputs

theorem generic_measured_eq_project_box
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ProofLengthInstantiationChecklist interp bounds) :
    h.toGenericCollisionInputs.measured =
      sondowProjectLocalPudlakCollisionBox :=
  rfl

theorem not_rational
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ProofLengthInstantiationChecklist interp bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.minimal_surface.not_rational

theorem not_rational_eq_generic_core
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ProofLengthInstantiationChecklist interp bounds) :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational
        h.toGenericCollisionInputs := by
  have hcore :
      h.minimal_surface.final_core_inputs = h.toFinalCoreInputs := by
    simpa [toFinalCoreInputs, Month7MinimalTheoremSurface.ofFinalCoreInputs] using
      congrArg Month7MinimalTheoremSurface.final_core_inputs
        h.minimal_surface_eq
  calc
    h.not_rational =
        month7_final_collision_core_inputs_not_rational
          h.minimal_surface.final_core_inputs := rfl
    _ =
        (month7_final_collision_core_inputs_to_generic_collision_inputs
          h.minimal_surface.final_core_inputs).not_rational :=
          h.minimal_surface.generic_boundary_eq
    _ =
        GenericRationalCollisionInputs.not_rational
          h.toGenericCollisionInputs := by
          rw [hcore]

theorem contradiction
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month8ProofLengthInstantiationChecklist interp bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.not_rational hrat

end Month8ProofLengthInstantiationChecklist

theorem month8_proof_length_instantiation_goal_closure
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    (Nonempty (Month8ProofLengthResidualFrontier interp) ↔
      _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths ∧
        Nonempty
          (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ExactLocalProofCodeSemanticsCertificate
            interp)) ∧
      (Nonempty (Month8ProofLengthInstantiationChecklist interp bounds) ↔
        Nonempty (Month8ConcreteMinProofCodeSizeBoundary interp bounds)) ∧
        (∀ h : Month8ConcreteMinProofCodeSizeBoundary interp bounds,
          h.not_rational =
            GenericRationalCollisionInputs.not_rational
              h.toGenericCollisionInputs) :=
  ⟨month8_proof_length_residual_nonempty_iff_exact_local_proof_code_semantics,
    Month8ProofLengthInstantiationChecklist.nonempty_iff_concrete_minProofCodeSize_boundary,
    fun h => h.not_rational_eq_generic_core⟩

end SondowProjectMonth8ProofLengthInstantiationSurface
end SondowMainCheckedCodeBridge

end
