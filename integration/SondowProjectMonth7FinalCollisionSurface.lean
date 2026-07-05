/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth7AxiomEliminationFrontierSurface
import integration.SondowProjectPudlakCollision

/-!
# Month 7 final collision surface

This module connects the Month 7 proof-length/payload frontier to the existing
project-local Sondow-Pudlak collision core.  It does not remove the remaining
frontier assumptions; it proves that the exact-family local-code frontier is
already shaped correctly for the final collision input.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth7FinalCollisionSurface

universe u v w

open SondowProjectMonth7AxiomEliminationFrontierSurface

structure Month7PublicResidualInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (bounds : BoundedArithmeticLab.SondowComponentBounds) :
    Type where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  proof_length_audit :
    Nonempty
      (_root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6ProofLengthInternalizationAuditCertificate
        interp)
  minimal_closure :
    Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds)
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  exact_family_lengths :
    _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths
  fallback :
    _root_.FormulaCode → Nat
  local_code_calibration :
    (let model :=
      interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration)

def month7_public_residual_inputs_to_local_code_payload
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7PublicResidualInputs interp bounds) :
    Month7ExactFamilyLocalCodePudlakPayloadVector interp bounds where
  proof_length_audit := h.proof_length_audit
  minimal_closure := h.minimal_closure
  strengthened_payload_truth := h.strengthened_payload_truth
  exact_family_lengths := h.exact_family_lengths
  fallback := h.fallback
  local_code_calibration := h.local_code_calibration

def month7_public_residual_inputs_to_literature_frontier_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7PublicResidualInputs interp bounds) :
    Month7LiteraturePudlakCollisionFrontierVector interp bounds where
  literature_lower_bound := h.literature_lower_bound
  local_code_payload :=
    month7_public_residual_inputs_to_local_code_payload h

def month7_literature_frontier_vector_to_public_residual_inputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7LiteraturePudlakCollisionFrontierVector interp bounds) :
    Month7PublicResidualInputs interp bounds where
  literature_lower_bound := h.literature_lower_bound
  proof_length_audit := h.local_code_payload.proof_length_audit
  minimal_closure := h.local_code_payload.minimal_closure
  strengthened_payload_truth := h.local_code_payload.strengthened_payload_truth
  exact_family_lengths := h.local_code_payload.exact_family_lengths
  fallback := h.local_code_payload.fallback
  local_code_calibration := h.local_code_payload.local_code_calibration

theorem month7_public_residual_inputs_nonempty_iff_literature_frontier_vector_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month7PublicResidualInputs interp bounds) ↔
      Nonempty
        (Month7LiteraturePudlakCollisionFrontierVector interp bounds) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact
      ⟨month7_public_residual_inputs_to_literature_frontier_vector h⟩
  · intro h
    rcases h with ⟨h⟩
    exact
      ⟨month7_literature_frontier_vector_to_public_residual_inputs h⟩

structure Month7FinalCollisionCoreInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (bounds : BoundedArithmeticLab.SondowComponentBounds) :
    Type where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  minimal_closure :
    Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds)
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  exact_family_lengths :
    _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths
  fallback :
    _root_.FormulaCode → Nat
  local_code_calibration :
    (let model :=
      interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration)

def month7_public_residual_inputs_to_final_collision_core_inputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7PublicResidualInputs interp bounds) :
    Month7FinalCollisionCoreInputs interp bounds where
  literature_lower_bound := h.literature_lower_bound
  minimal_closure := h.minimal_closure
  strengthened_payload_truth := h.strengthened_payload_truth
  exact_family_lengths := h.exact_family_lengths
  fallback := h.fallback
  local_code_calibration := h.local_code_calibration

def month7_final_collision_core_inputs_to_strengthened_to_partial_transfer
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7FinalCollisionCoreInputs interp bounds) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer := by
  have hcanonical :
      Nonempty _root_.StrengthenedToPartialCanonicalRecognitionCertificate :=
    (_root_.strengthenedToPartialExactFamilyLengths_iff_canonicalCertificate).1
      h.exact_family_lengths
  rcases hcanonical with ⟨hcert⟩
  exact
    ((hcert.toConcreteRecognition.toConcreteProjectionCalibration
      hcert.convention.fallback).toAcceptedCalibration
      (_root_.PartialToStrengthenedAcceptedProjection.ofStrengthenedPayloadTruth
        h.strengthened_payload_truth)).toTransfer

def month7_final_collision_core_inputs_to_partial_to_graft_transfer
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7FinalCollisionCoreInputs interp bounds) :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer :=
  (_root_.MiniHilbert.PAHilbertProjectionFamilyExactness.ofLocalPAHilbertCodeCalibration
    h.fallback h.local_code_calibration).toStrongLowerBoundTransfer

theorem month7_final_collision_core_inputs_to_collapse_conclusion
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7FinalCollisionCoreInputs interp bounds) :
    SondowProjectLocalS21CollapseConclusion := by
  rcases h.minimal_closure with ⟨cert⟩
  exact cert.toCollapseConclusion

def month7_final_collision_core_inputs_to_collision_inputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7FinalCollisionCoreInputs interp bounds) :
    SondowProjectLocalPudlakCollisionInputs where
  project_upper :=
    month7_final_collision_core_inputs_to_collapse_conclusion h
  pudlak_lower_bound :=
    h.literature_lower_bound.toPudlakFiniteConsistencyLowerBoundPackage
      (month7_final_collision_core_inputs_to_strengthened_to_partial_transfer
        h)
  transfer_to_graft :=
    month7_final_collision_core_inputs_to_partial_to_graft_transfer h

def month7_final_collision_core_inputs_to_generic_collision_inputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7FinalCollisionCoreInputs interp bounds) :
    GenericRationalCollisionInputs :=
  (month7_final_collision_core_inputs_to_collision_inputs
    h).toGenericRationalCollisionInputs

theorem month7_final_collision_core_inputs_not_rational
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7FinalCollisionCoreInputs interp bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  (month7_final_collision_core_inputs_to_generic_collision_inputs h).not_rational

theorem month7_final_collision_core_inputs_audited_collision_core
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7FinalCollisionCoreInputs interp bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  (month7_final_collision_core_inputs_to_generic_collision_inputs
    h).audited_collision_core

theorem month7_final_collision_core_inputs_not_rational_eq_generic_skeleton
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7FinalCollisionCoreInputs interp bounds) :
    month7_final_collision_core_inputs_not_rational h =
      (month7_final_collision_core_inputs_to_generic_collision_inputs
        h).not_rational :=
  rfl

theorem month7_final_collision_core_inputs_audited_collision_core_eq_generic_skeleton
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7FinalCollisionCoreInputs interp bounds) :
    month7_final_collision_core_inputs_audited_collision_core h =
      (month7_final_collision_core_inputs_to_generic_collision_inputs
        h).audited_collision_core :=
  rfl

theorem month7_final_collision_core_inputs_contradiction
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7FinalCollisionCoreInputs interp bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  month7_final_collision_core_inputs_not_rational h hrat

def month7_literature_pudlak_collision_frontier_vector_to_collision_inputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      Month7LiteraturePudlakCollisionFrontierVector interp bounds) :
    SondowProjectLocalPudlakCollisionInputs where
  project_upper :=
    month7_exact_family_local_code_pudlak_payload_vector_to_collapse_conclusion
      h.local_code_payload
  pudlak_lower_bound :=
    h.literature_lower_bound.toPudlakFiniteConsistencyLowerBoundPackage
      (month7_exact_family_local_code_pudlak_payload_vector_to_strengthened_to_partial_transfer
        h.local_code_payload)
  transfer_to_graft :=
    month7_exact_family_local_code_pudlak_payload_vector_to_partial_to_graft_transfer
      h.local_code_payload

theorem month7_literature_pudlak_collision_frontier_vector_not_rational
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      Month7LiteraturePudlakCollisionFrontierVector interp bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  (month7_literature_pudlak_collision_frontier_vector_to_collision_inputs
    h).not_rational

theorem month7_literature_pudlak_collision_frontier_vector_audited_collision_core
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      Month7LiteraturePudlakCollisionFrontierVector interp bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  (month7_literature_pudlak_collision_frontier_vector_to_collision_inputs
    h).audited_collision_core

theorem month7_literature_pudlak_collision_frontier_vector_contradiction
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h :
      Month7LiteraturePudlakCollisionFrontierVector interp bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  month7_literature_pudlak_collision_frontier_vector_not_rational h hrat

def month7_public_residual_inputs_to_collision_inputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7PublicResidualInputs interp bounds) :
    SondowProjectLocalPudlakCollisionInputs :=
  month7_literature_pudlak_collision_frontier_vector_to_collision_inputs
    (month7_public_residual_inputs_to_literature_frontier_vector h)

theorem month7_public_residual_inputs_not_rational
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7PublicResidualInputs interp bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  month7_literature_pudlak_collision_frontier_vector_not_rational
    (month7_public_residual_inputs_to_literature_frontier_vector h)

theorem month7_public_residual_inputs_audited_collision_core
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7PublicResidualInputs interp bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  month7_literature_pudlak_collision_frontier_vector_audited_collision_core
    (month7_public_residual_inputs_to_literature_frontier_vector h)

theorem month7_public_residual_inputs_contradiction
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7PublicResidualInputs interp bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  month7_public_residual_inputs_not_rational h hrat

structure Month7CompletionChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (bounds : BoundedArithmeticLab.SondowComponentBounds) :
    Type where
  public_residual_inputs :
    Month7PublicResidualInputs interp bounds
  final_core_inputs :
    Month7FinalCollisionCoreInputs interp bounds
  final_core_eq :
    final_core_inputs =
      month7_public_residual_inputs_to_final_collision_core_inputs
        public_residual_inputs
  generic_boundary_eq :
    month7_final_collision_core_inputs_not_rational final_core_inputs =
      (month7_final_collision_core_inputs_to_generic_collision_inputs
        final_core_inputs).not_rational

namespace Month7CompletionChecklist

def ofPublicResidualInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7PublicResidualInputs interp bounds) :
    Month7CompletionChecklist interp bounds where
  public_residual_inputs := h
  final_core_inputs :=
    month7_public_residual_inputs_to_final_collision_core_inputs h
  final_core_eq := rfl
  generic_boundary_eq := rfl

theorem nonempty_iff_public_residual_inputs_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month7CompletionChecklist interp bounds) ↔
      Nonempty (Month7PublicResidualInputs interp bounds) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.public_residual_inputs⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨ofPublicResidualInputs h⟩

theorem not_rational
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7CompletionChecklist interp bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  month7_final_collision_core_inputs_not_rational h.final_core_inputs

theorem contradiction
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7CompletionChecklist interp bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.not_rational hrat

end Month7CompletionChecklist

structure Month7MinimalTheoremSurface
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (bounds : BoundedArithmeticLab.SondowComponentBounds) :
    Type where
  final_core_inputs :
    Month7FinalCollisionCoreInputs interp bounds
  generic_boundary_eq :
    month7_final_collision_core_inputs_not_rational final_core_inputs =
      (month7_final_collision_core_inputs_to_generic_collision_inputs
        final_core_inputs).not_rational

namespace Month7MinimalTheoremSurface

def ofFinalCoreInputs
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7FinalCollisionCoreInputs interp bounds) :
    Month7MinimalTheoremSurface interp bounds where
  final_core_inputs := h
  generic_boundary_eq := rfl

def ofCompletionChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7CompletionChecklist interp bounds) :
    Month7MinimalTheoremSurface interp bounds where
  final_core_inputs := h.final_core_inputs
  generic_boundary_eq := h.generic_boundary_eq

theorem nonempty_iff_final_core_inputs_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month7MinimalTheoremSurface interp bounds) ↔
      Nonempty (Month7FinalCollisionCoreInputs interp bounds) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.final_core_inputs⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨ofFinalCoreInputs h⟩

theorem not_rational
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7MinimalTheoremSurface interp bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  month7_final_collision_core_inputs_not_rational h.final_core_inputs

theorem contradiction
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7MinimalTheoremSurface interp bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.not_rational hrat

end Month7MinimalTheoremSurface

structure Month8ProofLengthResidualFrontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Type where
  exact_family_lengths :
    _root_.StrengthenedToPartialProjectProofLengthExactFamilyLengths
  fallback :
    _root_.FormulaCode → Nat
  local_code_calibration :
    (let model :=
      interp.localPAHilbertProofLengthCodeSemanticsForProjection fallback
     model.code_model.Calibration)

structure Month8PayloadLiteratureResidualFrontier
    (bounds : BoundedArithmeticLab.SondowComponentBounds) :
    Type where
  literature_lower_bound :
    _root_.LiteraturePudlakTheorem5LowerBoundCertificate
  minimal_closure :
    Nonempty (SondowCLineMinimalClosureCertificate.{u} bounds)
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth

def month7_final_core_to_month8_proof_length_residual_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7FinalCollisionCoreInputs interp bounds) :
    Month8ProofLengthResidualFrontier interp where
  exact_family_lengths := h.exact_family_lengths
  fallback := h.fallback
  local_code_calibration := h.local_code_calibration

def month7_final_core_to_month8_payload_literature_residual_frontier
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7FinalCollisionCoreInputs interp bounds) :
    Month8PayloadLiteratureResidualFrontier.{u} bounds where
  literature_lower_bound := h.literature_lower_bound
  minimal_closure := h.minimal_closure
  strengthened_payload_truth := h.strengthened_payload_truth

def month8_residual_frontiers_to_month7_final_core
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual : Month8ProofLengthResidualFrontier interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds) :
    Month7FinalCollisionCoreInputs interp bounds where
  literature_lower_bound := payload_residual.literature_lower_bound
  minimal_closure := payload_residual.minimal_closure
  strengthened_payload_truth := payload_residual.strengthened_payload_truth
  exact_family_lengths := proof_residual.exact_family_lengths
  fallback := proof_residual.fallback
  local_code_calibration := proof_residual.local_code_calibration

theorem month7_final_core_nonempty_iff_month8_residual_frontiers_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month7FinalCollisionCoreInputs interp bounds) ↔
      Nonempty (Month8ProofLengthResidualFrontier interp) ∧
        Nonempty (Month8PayloadLiteratureResidualFrontier.{u} bounds) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact
      ⟨⟨month7_final_core_to_month8_proof_length_residual_frontier
          h⟩,
       ⟨month7_final_core_to_month8_payload_literature_residual_frontier
          h⟩⟩
  · intro h
    rcases h with ⟨⟨proof_residual⟩, ⟨payload_residual⟩⟩
    exact
      ⟨month8_residual_frontiers_to_month7_final_core
        proof_residual payload_residual⟩

theorem month7_minimal_theorem_surface_nonempty_iff_month8_residual_frontiers_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month7MinimalTheoremSurface interp bounds) ↔
      Nonempty (Month8ProofLengthResidualFrontier interp) ∧
        Nonempty (Month8PayloadLiteratureResidualFrontier.{u} bounds) :=
  (Month7MinimalTheoremSurface.nonempty_iff_final_core_inputs_nonempty).trans
    month7_final_core_nonempty_iff_month8_residual_frontiers_nonempty

theorem month8_residual_frontiers_not_rational
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (proof_residual : Month8ProofLengthResidualFrontier interp)
    (payload_residual :
      Month8PayloadLiteratureResidualFrontier.{u} bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  month7_final_collision_core_inputs_not_rational
    (month8_residual_frontiers_to_month7_final_core
      proof_residual payload_residual)

structure Month7PreMergeAuditCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (bounds : BoundedArithmeticLab.SondowComponentBounds) :
    Type where
  completion_checklist :
    Month7CompletionChecklist interp bounds
  minimal_surface :
    Month7MinimalTheoremSurface interp bounds
  minimal_surface_eq :
    minimal_surface =
      Month7MinimalTheoremSurface.ofCompletionChecklist
        completion_checklist

namespace Month7PreMergeAuditCertificate

def ofCompletionChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7CompletionChecklist interp bounds) :
    Month7PreMergeAuditCertificate interp bounds where
  completion_checklist := h
  minimal_surface := Month7MinimalTheoremSurface.ofCompletionChecklist h
  minimal_surface_eq := rfl

theorem nonempty_iff_completion_checklist_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month7PreMergeAuditCertificate interp bounds) ↔
      Nonempty (Month7CompletionChecklist interp bounds) := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact ⟨h.completion_checklist⟩
  · intro h
    rcases h with ⟨h⟩
    exact ⟨ofCompletionChecklist h⟩

theorem nonempty_iff_public_residual_inputs_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month7PreMergeAuditCertificate interp bounds) ↔
      Nonempty (Month7PublicResidualInputs interp bounds) :=
  (nonempty_iff_completion_checklist_nonempty).trans
    Month7CompletionChecklist.nonempty_iff_public_residual_inputs_nonempty

theorem nonempty_iff_literature_frontier_vector_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month7PreMergeAuditCertificate interp bounds) ↔
      Nonempty (Month7LiteraturePudlakCollisionFrontierVector interp bounds) :=
  (nonempty_iff_public_residual_inputs_nonempty).trans
    month7_public_residual_inputs_nonempty_iff_literature_frontier_vector_nonempty

theorem minimal_surface_nonempty_of_premerge_audit_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds} :
    Nonempty (Month7PreMergeAuditCertificate interp bounds) →
      Nonempty (Month7MinimalTheoremSurface interp bounds) := by
  intro h
  rcases h with ⟨h⟩
  exact ⟨h.minimal_surface⟩

theorem not_rational
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7PreMergeAuditCertificate interp bounds) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.minimal_surface.not_rational

theorem contradiction
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (h : Month7PreMergeAuditCertificate interp bounds)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.not_rational hrat

end Month7PreMergeAuditCertificate

end SondowProjectMonth7FinalCollisionSurface
end SondowMainCheckedCodeBridge
