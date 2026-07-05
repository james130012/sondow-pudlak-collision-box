/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth5Month6TheoremIndexSurface
import integration.SondowProjectS21Kernel

/-!
# Month 7 axiom-elimination frontier surface

This module separates the Month 7 proof-length and payload residuals into
auditable frontiers.  The checker kernel is proof-length-free; the global
realization frontier is exactly where the abstract `proof_length` coordinate
still enters.  On the payload side, the partial-consistency truth input is
exposed through the existing structured payload-spec certificate.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth7AxiomEliminationFrontierSurface

universe u v w

open SondowProjectMonth5Month6TheoremIndexSurface

abbrev Month7ProofLengthFreeCheckerKernelCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  SondowProjectMonth5Month6TheoremIndexSurface.Month7ProofLengthFreeCheckerKernelCertificate
    interp

abbrev Month7ProofLengthEliminationFrontierCertificate
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :=
  SondowProjectMonth5Month6TheoremIndexSurface.Month7ProofLengthEliminationFrontierCertificate
    interp

abbrev Month7PartialPayloadSpecFrontierCertificate :=
  PartialConsistencyPayloadSpecCertificate

abbrev Month7PartialPayloadSpecTraceFrontierCertificate :=
  PartialConsistencyPayloadSpecTraceCertificate

structure Month7PayloadFrontierCertificate where
  partial_payload_spec :
    Month7PartialPayloadSpecFrontierCertificate
  strengthened_payload_truth :
    _root_.StrengthenedPartialConsistencyPayloadTruth

namespace Month7PayloadFrontierCertificate

theorem partialPayloadTruth
    (cert : Month7PayloadFrontierCertificate) :
    _root_.PartialConsistencyPayloadTruth :=
  cert.partial_payload_spec.toPayloadTruth

theorem partialAcceptedTruth
    (cert : Month7PayloadFrontierCertificate) :
    _root_.PartialConsistencyAcceptedTruth :=
  cert.partial_payload_spec.toAcceptedTruth

theorem strengthenedAcceptedTruth
    (cert : Month7PayloadFrontierCertificate) :
    _root_.StrengthenedPartialConsistencyAcceptedTruth :=
  cert.strengthened_payload_truth.toAcceptedTruth

end Month7PayloadFrontierCertificate

theorem partial_payload_truth_nonempty_of_month7_payload_spec_frontier
    (h :
      Nonempty Month7PartialPayloadSpecFrontierCertificate) :
    Nonempty _root_.PartialConsistencyPayloadTruth :=
  partialConsistencyPayloadTruth_nonempty_ofPayloadSpecCertificate h

theorem partial_payload_spec_frontier_iff_accepted_code_truth
    :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate ↔
      Nonempty Month7PartialPayloadSpecFrontierCertificate :=
  _root_.SondowMainCheckedCodeBridge.partialConsistencyAcceptedCodeTruthCertificate_nonempty_iff_payloadSpecCertificate_nonempty

theorem partial_payload_spec_frontier_iff_payload_semantics
    :
    Nonempty PartialConsistencyPayloadSemanticsCertificate ↔
      Nonempty Month7PartialPayloadSpecFrontierCertificate :=
  _root_.SondowMainCheckedCodeBridge.partialConsistencyPayloadSemanticsCertificate_nonempty_iff_payloadSpecCertificate_nonempty

theorem partial_payload_spec_frontier_iff_finite_consistency_reading
    :
    Nonempty PartialConsistencyFiniteConsistencyReadingCertificate ↔
      Nonempty Month7PartialPayloadSpecFrontierCertificate :=
  _root_.SondowMainCheckedCodeBridge.partialConsistencyFiniteConsistencyReadingCertificate_nonempty_iff_payloadSpecCertificate_nonempty

theorem partial_payload_spec_trace_frontier_iff_payload_spec_and_trace
    :
    Nonempty Month7PartialPayloadSpecTraceFrontierCertificate ↔
      Nonempty Month7PartialPayloadSpecFrontierCertificate ∧
        Nonempty
          (_root_.S21VerifierTraceSoundness
            _root_.partialConsistencyCode) :=
  partialConsistencyPayloadSpecTraceCertificate_nonempty_iff_payloadSpecAndTraceSoundness_nonempty

theorem strengthened_payload_truth_iff_accepted_truth
    :
    _root_.StrengthenedPartialConsistencyPayloadTruth ↔
      _root_.StrengthenedPartialConsistencyAcceptedTruth :=
  _root_.strengthenedPartialConsistencyAcceptedTruth_iff_payloadTruth.symm

theorem month7_payload_frontier_nonempty_iff
    :
    Nonempty Month7PayloadFrontierCertificate ↔
      Nonempty Month7PartialPayloadSpecFrontierCertificate ∧
        _root_.StrengthenedPartialConsistencyPayloadTruth := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact
      ⟨⟨cert.partial_payload_spec⟩,
        cert.strengthened_payload_truth⟩
  · intro h
    rcases h with ⟨⟨partial_spec⟩, strengthened_truth⟩
    exact
      ⟨{ partial_payload_spec := partial_spec
         strengthened_payload_truth := strengthened_truth }⟩

theorem month7_payload_frontier_nonempty_iff_partial_spec_and_strengthened_accepted
    :
    Nonempty Month7PayloadFrontierCertificate ↔
      Nonempty Month7PartialPayloadSpecFrontierCertificate ∧
        _root_.StrengthenedPartialConsistencyAcceptedTruth := by
  constructor
  · intro h
    rcases (month7_payload_frontier_nonempty_iff).1 h with
      ⟨partial_spec, strengthened_truth⟩
    exact
      ⟨partial_spec,
        (strengthened_payload_truth_iff_accepted_truth).1
          strengthened_truth⟩
  · intro h
    rcases h with ⟨partial_spec, strengthened_accepted⟩
    exact
      (month7_payload_frontier_nonempty_iff).2
        ⟨partial_spec,
          (strengthened_payload_truth_iff_accepted_truth).2
            strengthened_accepted⟩

theorem month7_payload_frontier_nonempty_iff_partial_accepted_code_and_strengthened_accepted
    :
    Nonempty Month7PayloadFrontierCertificate ↔
      Nonempty PartialConsistencyAcceptedCodeTruthCertificate ∧
        _root_.StrengthenedPartialConsistencyAcceptedTruth := by
  constructor
  · intro h
    rcases
      (month7_payload_frontier_nonempty_iff_partial_spec_and_strengthened_accepted).1
        h with
      ⟨partial_spec, strengthened_accepted⟩
    exact
      ⟨(partial_payload_spec_frontier_iff_accepted_code_truth).2
          partial_spec,
        strengthened_accepted⟩
  · intro h
    rcases h with ⟨accepted_code, strengthened_accepted⟩
    exact
      (month7_payload_frontier_nonempty_iff_partial_spec_and_strengthened_accepted).2
        ⟨(partial_payload_spec_frontier_iff_accepted_code_truth).1
            accepted_code,
          strengthened_accepted⟩

structure Month7AxiomEliminationFrontierChecklist
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Type where
  proof_length_free_checker :
    Month7ProofLengthFreeCheckerKernelCertificate interp
  proof_length_realization :
    Month7ProofLengthEliminationFrontierCertificate interp
  payload_frontier :
    Month7PayloadFrontierCertificate

structure Month7OpenAssumptionVector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Prop where
  project_checked :
    _root_.ProjectProofLengthSemantics
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      interp.localCheckedCodeProofLength
      _root_.MiniHilbert.FormulaCodeHilbertRelevantCode
  partial_accepted_code :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate
  strengthened_accepted :
    _root_.StrengthenedPartialConsistencyAcceptedTruth

structure Month7LocalRecognitionOpenAssumptionVector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Prop where
  local_recognition :
    _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition interp
  partial_accepted_code :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate
  strengthened_accepted :
    _root_.StrengthenedPartialConsistencyAcceptedTruth

structure Month7LocalRecognitionCertificateOpenVector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Prop where
  local_recognition_certificate :
    _root_.MiniHilbert.PAHilbertLocalProofCodeRecognitionCertificate interp
  partial_accepted_code :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate
  strengthened_accepted :
    _root_.StrengthenedPartialConsistencyAcceptedTruth

structure Month7EncoderRecognitionOpenVector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Prop where
  encoder_recognition :
    _root_.MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition interp
  partial_accepted_code :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate
  strengthened_accepted :
    _root_.StrengthenedPartialConsistencyAcceptedTruth

structure Month7ProjectCheckedEquationOpenVector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Prop where
  proof_length_eq_project_checked :
    ∀ code : _root_.FormulaCode,
      _root_.MiniHilbert.FormulaCodeHilbertRelevantCode code →
        _root_.proof_length
            _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize code =
          interp.projectCheckedProofLength code
  partial_accepted_code :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate
  strengthened_accepted :
    _root_.StrengthenedPartialConsistencyAcceptedTruth

structure Month7ProofCodeCheckerOpenVector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Prop where
  proof_code_checker :
    Nonempty (_root_.MiniHilbert.PAHilbertProofCodeCheckerRecognition interp)
  partial_accepted_code :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate
  strengthened_accepted :
    _root_.StrengthenedPartialConsistencyAcceptedTruth

structure Month7CheckerProjectLengthEquationOpenVector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Prop where
  checker_project_length_equation :
    ∃ fallback_length : _root_.FormulaCode → Nat,
      ∀ code : _root_.FormulaCode,
        _root_.MiniHilbert.FormulaCodeHilbertRelevantCode code →
          _root_.proof_length
              _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize code =
            interp.localProofCodeSemantics.projectLength fallback_length code
  partial_accepted_code :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate
  strengthened_accepted :
    _root_.StrengthenedPartialConsistencyAcceptedTruth

structure Month7CanonicalCheckerProjectLengthEquationOpenVector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Prop where
  proof_length_eq_canonical_checker_project_length :
    ∀ code : _root_.FormulaCode,
      _root_.MiniHilbert.FormulaCodeHilbertRelevantCode code →
        _root_.proof_length
            _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize code =
          interp.localProofCodeSemantics.projectLength (fun _ => 0) code
  partial_accepted_code :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate
  strengthened_accepted :
    _root_.StrengthenedPartialConsistencyAcceptedTruth

structure Month7CanonicalProofLengthCodeCalibrationOpenVector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Prop where
  canonical_calibration :
    (interp.localHilbertProofLengthCodeSemantics (fun _ => 0)).Calibration
  partial_accepted_code :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate
  strengthened_accepted :
    _root_.StrengthenedPartialConsistencyAcceptedTruth

namespace Month7AxiomEliminationFrontierChecklist

theorem partialPayloadTruth
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month7AxiomEliminationFrontierChecklist interp) :
    _root_.PartialConsistencyPayloadTruth :=
  cert.payload_frontier.partialPayloadTruth

theorem strengthenedPayloadTruth
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (cert : Month7AxiomEliminationFrontierChecklist interp) :
    _root_.StrengthenedPartialConsistencyPayloadTruth :=
  cert.payload_frontier.strengthened_payload_truth

end Month7AxiomEliminationFrontierChecklist

theorem month7_checker_kernel_nonempty
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month7ProofLengthFreeCheckerKernelCertificate interp) :=
  SondowProjectMonth5Month6TheoremIndexSurface.month7_checker_kernel_nonempty
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
  SondowProjectMonth5Month6TheoremIndexSurface.month7_project_checked_semantics_iff_elimination_frontier
    interp

theorem month7_project_checked_semantics_iff_local_proof_code_recognition
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
      _root_.MiniHilbert.PAHilbertLocalProofCodeRecognition interp := by
  constructor
  · intro hsemantics
    exact
      (interp.localProofCodeRecognition_iff_projectCheckedRecognition).2
        (_root_.MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition.ofProjectProofLengthSemantics
          hsemantics)
  · intro hrec
    exact
      ((interp.localProofCodeRecognition_iff_projectCheckedRecognition).1
        hrec).toProjectProofLengthSemantics

theorem month7_axiom_elimination_frontier_checklist_nonempty_iff
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month7AxiomEliminationFrontierChecklist interp) ↔
      Nonempty (Month7ProofLengthEliminationFrontierCertificate interp) ∧
        Nonempty Month7PayloadFrontierCertificate := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact
      ⟨⟨cert.proof_length_realization⟩,
        ⟨cert.payload_frontier⟩⟩
  · intro h
    rcases h with ⟨⟨proof_length_frontier⟩, ⟨payload_frontier⟩⟩
    exact
      ⟨{ proof_length_free_checker :=
            proof_length_frontier.checker_kernel
         proof_length_realization :=
            proof_length_frontier
         payload_frontier := payload_frontier }⟩

theorem month7_axiom_elimination_frontier_checklist_nonempty_iff_project_checked_and_payload
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month7AxiomEliminationFrontierChecklist interp) ↔
      _root_.ProjectProofLengthSemantics
          _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
          interp.localCheckedCodeProofLength
          _root_.MiniHilbert.FormulaCodeHilbertRelevantCode ∧
        Nonempty Month7PayloadFrontierCertificate := by
  constructor
  · intro h
    rcases
      (month7_axiom_elimination_frontier_checklist_nonempty_iff
        interp).1 h with
      ⟨proof_length_frontier, payload_frontier⟩
    exact
      ⟨(month7_project_checked_semantics_iff_elimination_frontier
          interp).2 proof_length_frontier,
        payload_frontier⟩
  · intro h
    rcases h with ⟨project_checked, payload_frontier⟩
    exact
      (month7_axiom_elimination_frontier_checklist_nonempty_iff
        interp).2
        ⟨(month7_project_checked_semantics_iff_elimination_frontier
            interp).1 project_checked,
          payload_frontier⟩

theorem month7_axiom_elimination_frontier_checklist_nonempty_iff_open_assumption_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month7AxiomEliminationFrontierChecklist interp) ↔
      Month7OpenAssumptionVector interp := by
  constructor
  · intro h
    rcases
      (month7_axiom_elimination_frontier_checklist_nonempty_iff_project_checked_and_payload
        interp).1 h with
      ⟨project_checked, payload_frontier⟩
    rcases
      (month7_payload_frontier_nonempty_iff_partial_accepted_code_and_strengthened_accepted).1
        payload_frontier with
      ⟨partial_accepted_code, strengthened_accepted⟩
    exact
      { project_checked := project_checked
        partial_accepted_code := partial_accepted_code
        strengthened_accepted := strengthened_accepted }
  · intro h
    exact
      (month7_axiom_elimination_frontier_checklist_nonempty_iff_project_checked_and_payload
        interp).2
        ⟨h.project_checked,
          (month7_payload_frontier_nonempty_iff_partial_accepted_code_and_strengthened_accepted).2
            ⟨h.partial_accepted_code, h.strengthened_accepted⟩⟩

theorem month7_open_assumption_vector_iff_local_recognition_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Month7OpenAssumptionVector interp ↔
      Month7LocalRecognitionOpenAssumptionVector interp := by
  constructor
  · intro h
    exact
      { local_recognition :=
          (month7_project_checked_semantics_iff_local_proof_code_recognition
            interp).1 h.project_checked
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }
  · intro h
    exact
      { project_checked :=
          (month7_project_checked_semantics_iff_local_proof_code_recognition
            interp).2 h.local_recognition
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }

theorem month7_axiom_elimination_frontier_checklist_nonempty_iff_local_recognition_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month7AxiomEliminationFrontierChecklist interp) ↔
      Month7LocalRecognitionOpenAssumptionVector interp :=
  (month7_axiom_elimination_frontier_checklist_nonempty_iff_open_assumption_vector
    interp).trans
    (month7_open_assumption_vector_iff_local_recognition_vector interp)

theorem month7_local_recognition_vector_iff_certificate_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Month7LocalRecognitionOpenAssumptionVector interp ↔
      Month7LocalRecognitionCertificateOpenVector interp := by
  constructor
  · intro h
    exact
      { local_recognition_certificate :=
          (interp.localProofCodeRecognition_iff_encoderCertificate).1
            h.local_recognition
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }
  · intro h
    exact
      { local_recognition :=
          (interp.localProofCodeRecognition_iff_encoderCertificate).2
            h.local_recognition_certificate
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }

theorem month7_axiom_elimination_frontier_checklist_nonempty_iff_local_certificate_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month7AxiomEliminationFrontierChecklist interp) ↔
      Month7LocalRecognitionCertificateOpenVector interp :=
  (month7_axiom_elimination_frontier_checklist_nonempty_iff_local_recognition_vector
    interp).trans
    (month7_local_recognition_vector_iff_certificate_vector interp)

theorem month7_local_certificate_vector_iff_encoder_recognition_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Month7LocalRecognitionCertificateOpenVector interp ↔
      Month7EncoderRecognitionOpenVector interp := by
  constructor
  · intro h
    exact
      { encoder_recognition :=
          h.local_recognition_certificate.encoder_recognition
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }
  · intro h
    exact
      { local_recognition_certificate :=
          { checker_exactness := interp.localHilbertCheckerExactness
            encoder_recognition := h.encoder_recognition }
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }

theorem month7_axiom_elimination_frontier_checklist_nonempty_iff_encoder_recognition_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month7AxiomEliminationFrontierChecklist interp) ↔
      Month7EncoderRecognitionOpenVector interp :=
  (month7_axiom_elimination_frontier_checklist_nonempty_iff_local_certificate_vector
    interp).trans
    (month7_local_certificate_vector_iff_encoder_recognition_vector interp)

theorem month7_encoder_recognition_vector_iff_project_checked_equation_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Month7EncoderRecognitionOpenVector interp ↔
      Month7ProjectCheckedEquationOpenVector interp := by
  constructor
  · intro h
    exact
      { proof_length_eq_project_checked :=
          (_root_.MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition.iff_projectCheckedProofLength
            interp).1 h.encoder_recognition
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }
  · intro h
    exact
      { encoder_recognition :=
          (_root_.MiniHilbert.PAHilbertProjectCheckedProofLengthRecognition.iff_projectCheckedProofLength
            interp).2 h.proof_length_eq_project_checked
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }

theorem month7_axiom_elimination_frontier_checklist_nonempty_iff_project_checked_equation_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month7AxiomEliminationFrontierChecklist interp) ↔
      Month7ProjectCheckedEquationOpenVector interp :=
  (month7_axiom_elimination_frontier_checklist_nonempty_iff_encoder_recognition_vector
    interp).trans
    (month7_encoder_recognition_vector_iff_project_checked_equation_vector
      interp)

theorem month7_encoder_recognition_vector_iff_proof_code_checker_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Month7EncoderRecognitionOpenVector interp ↔
      Month7ProofCodeCheckerOpenVector interp := by
  constructor
  · intro h
    exact
      { proof_code_checker :=
          (interp.projectCheckedRecognition_iff_proofCodeChecker).1
            h.encoder_recognition
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }
  · intro h
    exact
      { encoder_recognition :=
          (interp.projectCheckedRecognition_iff_proofCodeChecker).2
            h.proof_code_checker
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }

theorem month7_project_checked_equation_vector_iff_proof_code_checker_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Month7ProjectCheckedEquationOpenVector interp ↔
      Month7ProofCodeCheckerOpenVector interp :=
  (month7_encoder_recognition_vector_iff_project_checked_equation_vector
    interp).symm.trans
    (month7_encoder_recognition_vector_iff_proof_code_checker_vector
      interp)

theorem month7_axiom_elimination_frontier_checklist_nonempty_iff_proof_code_checker_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month7AxiomEliminationFrontierChecklist interp) ↔
      Month7ProofCodeCheckerOpenVector interp :=
  (month7_axiom_elimination_frontier_checklist_nonempty_iff_encoder_recognition_vector
    interp).trans
    (month7_encoder_recognition_vector_iff_proof_code_checker_vector
      interp)

theorem month7_proof_code_checker_vector_iff_checker_project_length_equation_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Month7ProofCodeCheckerOpenVector interp ↔
      Month7CheckerProjectLengthEquationOpenVector interp := by
  constructor
  · intro h
    rcases h.proof_code_checker with ⟨checker⟩
    exact
      { checker_project_length_equation :=
          ⟨checker.fallback_length,
            checker.proof_length_eq_checker_projectLength⟩
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }
  · intro h
    rcases h.checker_project_length_equation with
      ⟨fallback_length, proof_length_eq_checker_project_length⟩
    exact
      { proof_code_checker :=
          ⟨{ fallback_length := fallback_length
             proof_length_eq_checker_projectLength :=
               proof_length_eq_checker_project_length }⟩
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }

theorem month7_axiom_elimination_frontier_checklist_nonempty_iff_checker_project_length_equation_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month7AxiomEliminationFrontierChecklist interp) ↔
      Month7CheckerProjectLengthEquationOpenVector interp :=
  (month7_axiom_elimination_frontier_checklist_nonempty_iff_proof_code_checker_vector
    interp).trans
    (month7_proof_code_checker_vector_iff_checker_project_length_equation_vector
      interp)

theorem month7_encoder_recognition_vector_iff_canonical_checker_project_length_equation_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Month7EncoderRecognitionOpenVector interp ↔
      Month7CanonicalCheckerProjectLengthEquationOpenVector interp := by
  constructor
  · intro h
    exact
      { proof_length_eq_canonical_checker_project_length :=
          (interp.projectCheckedRecognition_iff_localProofCodeProjectLength
            (fun _ => 0)).1 h.encoder_recognition
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }
  · intro h
    exact
      { encoder_recognition :=
          (interp.projectCheckedRecognition_iff_localProofCodeProjectLength
            (fun _ => 0)).2
            h.proof_length_eq_canonical_checker_project_length
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }

theorem month7_axiom_elimination_frontier_checklist_nonempty_iff_canonical_checker_project_length_equation_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month7AxiomEliminationFrontierChecklist interp) ↔
      Month7CanonicalCheckerProjectLengthEquationOpenVector interp :=
  (month7_axiom_elimination_frontier_checklist_nonempty_iff_encoder_recognition_vector
    interp).trans
    (month7_encoder_recognition_vector_iff_canonical_checker_project_length_equation_vector
      interp)

theorem month7_proof_code_checker_vector_iff_canonical_calibration_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Month7ProofCodeCheckerOpenVector interp ↔
      Month7CanonicalProofLengthCodeCalibrationOpenVector interp := by
  constructor
  · intro h
    exact
      { canonical_calibration :=
          (interp.proofCodeCheckerRecognition_iff_proofLengthCodeCalibration
            (fun _ => 0)).1 h.proof_code_checker
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }
  · intro h
    exact
      { proof_code_checker :=
          (interp.proofCodeCheckerRecognition_iff_proofLengthCodeCalibration
            (fun _ => 0)).2 h.canonical_calibration
        partial_accepted_code := h.partial_accepted_code
        strengthened_accepted := h.strengthened_accepted }

theorem month7_axiom_elimination_frontier_checklist_nonempty_iff_canonical_calibration_vector
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign) :
    Nonempty (Month7AxiomEliminationFrontierChecklist interp) ↔
      Month7CanonicalProofLengthCodeCalibrationOpenVector interp :=
  (month7_axiom_elimination_frontier_checklist_nonempty_iff_proof_code_checker_vector
    interp).trans
    (month7_proof_code_checker_vector_iff_canonical_calibration_vector
      interp)

end SondowProjectMonth7AxiomEliminationFrontierSurface
end SondowMainCheckedCodeBridge
