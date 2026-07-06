/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth11PAHilbertCheckerSurface
import integration.SondowProjectMonth9Month10ProofLengthGapFrontier

/-!
# Month 9-10 / Month 11 exact proof-gap handoff

This file is deliberately downstream of the Month 11-12 PA/Hilbert checker
surface.  It does not add new checker machinery.  It packages the final
project-level certificates from the PA/Hilbert side into the Month 9-10
finite-search no-small-code interface and, with the existing projection and
upper-route data, into the Month 9-10 project endpoint.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth9Month10Month11ExactProofGapHandoff

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth11PAHilbertCheckerSurface
open SondowProjectMonth9Month10ProofLengthGapFrontier

/-- Adapter input for the current exact proof-gap PA/Hilbert checker route.
The three project-level certificates are the fields of `input`: actual
proof-length search gap, powered-scale strictness, and proof-length-to-scale
calibration. -/
structure Month9Month10Month11ExactProofGapHandoff
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  input :
    ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapCheckerCoreInput
      scale_data

namespace Month9Month10Month11ExactProofGapHandoff

def certificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate scale_data :=
  h.input.toCertificate

def closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure
      scale_data :=
  h.input.toClosure

def canonicalCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  h.input.toCanonicalCalibratedExactnessCore

def noSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  h.input.toComputableFiniteSearchNoSmallCore

def checkerSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data :=
  h.closure.checkerSemantics

def finiteEnumeration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    InternalPudlakTheorem5CheckerFiniteEnumeration h.checkerSemantics :=
  h.closure.finiteEnumeration

def rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      h.checkerSemantics h.finiteEnumeration :=
  h.closure.rejectionExtractor

theorem proofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness h.checkerSemantics :=
  h.closure.proofLengthExactness

theorem actualProofLengthGap_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    Nonempty
      (ComputableSearchGapCertificate
        (fun n : Nat =>
          _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n))) :=
  ⟨h.input.proof_length_gap⟩

theorem timeConstructiblePower_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    ∀ {a b : Nat}, a < b →
      scale_data.time_constructible_bound a ^ scale_data.exponent <
        scale_data.time_constructible_bound b ^ scale_data.exponent :=
  h.input.timeConstructiblePower_strict

theorem scale_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b :=
  concretePAHilbert_scale_strict_of_timeConstructiblePower_strict
    scale_data h.timeConstructiblePower_strict

theorem proof_length_eq_scale
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (scale_data.scale n : Real) :=
  h.input.proof_length_eq_scale

theorem transported_gap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    ((h.input.toFinalExactCheckerCoreInput
        |>.toStrictScaleSingletonExactProofLengthGapInput
        |>.transportedGap).gap_for_polynomial_upper f hf).witness N =
      (h.input.proof_length_gap.gap_for_polynomial_upper f hf).witness N :=
  h.input.transported_gap_witness_eq f hf N

theorem certificate_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    Nonempty
      (ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate
        scale_data) :=
  ⟨h.certificate⟩

theorem closure_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    Nonempty
      (ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure
        scale_data) :=
  ⟨h.closure⟩

theorem canonicalCore_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore :=
  ⟨h.canonicalCore⟩

theorem noSmallCore_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    Nonempty
      InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  ⟨h.noSmallCore⟩

theorem feeds_month9_month10_checker_bridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  h.input.feeds_month9_month10_checker_bridge

def toCheckerExtractorComputableSearchChecklist
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) :
    Month9Month10CheckerExtractorComputableSearchChecklist.{0} where
  scale_data := scale_data
  checker := h.checkerSemantics
  enumeration := h.finiteEnumeration
  extractor := h.rejectionExtractor
  exactness := h.proofLengthExactness
  strengthened_to_partial := strengthened_to_partial
  transfer_to_graft := transfer_to_graft
  computable_gap := project_gap

def toCheckerExtractorComputableSearchChecklistOfConstantPieces
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) :
    Month9Month10CheckerExtractorComputableSearchChecklist.{0} :=
  h.toCheckerExtractorComputableSearchChecklist
    (InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
      strengthened_to_partial)
    (InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
      partial_to_graft)
    project_gap

def toProjectEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorProjectEndpointInputs.{0} where
  checker_checklist :=
    h.toCheckerExtractorComputableSearchChecklistOfConstantPieces
      strengthened_to_partial partial_to_graft project_gap
  strengthened_to_partial := strengthened_to_partial
  partial_to_graft := partial_to_graft
  project_upper := project_upper

theorem project_endpoint_frontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (h.toProjectEndpointInputs strengthened_to_partial partial_to_graft
      project_gap project_upper).EndpointFrontier :=
  (h.toProjectEndpointInputs strengthened_to_partial partial_to_graft
    project_gap project_upper).endpoint_frontier

theorem not_rational_of_project_data
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  (h.toProjectEndpointInputs strengthened_to_partial partial_to_graft
    project_gap project_upper).not_rational

structure Audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) : Prop where
  actualProofLengthGap :
    Nonempty
      (ComputableSearchGapCertificate
        (fun n : Nat =>
          _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n)))
  timeConstructiblePowerStrict :
    ∀ {a b : Nat}, a < b →
      scale_data.time_constructible_bound a ^ scale_data.exponent <
        scale_data.time_constructible_bound b ^ scale_data.exponent
  scaleStrict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  proofLengthEqScale :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (scale_data.scale n : Real)
  certificate :
    Nonempty
      (ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate
        scale_data)
  closure :
    Nonempty
      (ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure
        scale_data)
  canonicalCore :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore
  noSmallCore :
    Nonempty
      InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}
  feedsMonth9Month10 :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) ∧
      Nonempty
        InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}

theorem audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    Audit h where
  actualProofLengthGap := h.actualProofLengthGap_nonempty
  timeConstructiblePowerStrict := h.timeConstructiblePower_strict
  scaleStrict := h.scale_strict
  proofLengthEqScale := h.proof_length_eq_scale
  certificate := h.certificate_nonempty
  closure := h.closure_nonempty
  canonicalCore := h.canonicalCore_nonempty
  noSmallCore := h.noSmallCore_nonempty
  feedsMonth9Month10 := h.feeds_month9_month10_checker_bridge

end Month9Month10Month11ExactProofGapHandoff

/-- Corrected Month 9-10 / Month 11 handoff.  The checker side only has to
produce the computable finite-search no-small-code core; Month 9-10 then gets
an actual PA proof-length gap by calibration, without the inconsistent
`proof_length = scale` requirement. -/
structure Month9Month10Month11NoSmallCoreHandoff : Type 1 where
  core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}

namespace Month9Month10Month11NoSmallCoreHandoff

def scale_data
    (h : Month9Month10Month11NoSmallCoreHandoff) :
    InternalPudlakTheorem5ScaleData :=
  h.core.scale_data

def proofLengthFrontier
    (h : Month9Month10Month11NoSmallCoreHandoff) :
    Month9Month10ComputableNoSmallProofLengthFrontier.{0} where
  core := h.core

def actualProofLengthGap
    (h : Month9Month10Month11NoSmallCoreHandoff) :
    ComputableSearchGapCertificate
      (actualProofLengthMeasured h.scale_data) :=
  h.proofLengthFrontier.actual_proof_length_gap

def checkedLowerBoundCore
    (h : Month9Month10Month11NoSmallCoreHandoff) :
    InternalPudlakTheorem5CheckedLowerBoundCore :=
  h.proofLengthFrontier.checkedLowerBoundCore

def toCheckedLowerBoundCoreChecklist
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) :
    Month9Month10CheckedLowerBoundCoreChecklist where
  theorem5_checked_core := h.checkedLowerBoundCore
  strengthened_to_partial := strengthened_to_partial
  transfer_to_graft := transfer_to_graft
  computable_gap := project_gap

def toCheckedLowerBoundCoreChecklistOfConstantPieces
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) :
    Month9Month10CheckedLowerBoundCoreChecklist :=
  h.toCheckedLowerBoundCoreChecklist
    (InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
      strengthened_to_partial)
    (InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
      partial_to_graft)
    project_gap

theorem actual_gap_witness_eq_core
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((h.actualProofLengthGap.gap_for_polynomial_upper U hU).witness N) =
      h.core.computable_search_exclusion.witness U hU N :=
  rfl

structure Audit
    (h : Month9Month10Month11NoSmallCoreHandoff) : Prop where
  proofLengthFrontier :
    h.proofLengthFrontier.Audit
  actualProofLengthGap :
    Nonempty
      (ComputableSearchGapCertificate
        (actualProofLengthMeasured h.scale_data))
  checkedCore :
    Nonempty InternalPudlakTheorem5CheckedLowerBoundCore
  checkedLowerBound :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      h.scale_data h.checkedLowerBoundCore.checkedLength
  noSmallCore :
    Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}

theorem audit
    (h : Month9Month10Month11NoSmallCoreHandoff) :
    Audit h where
  proofLengthFrontier := h.proofLengthFrontier.audit
  actualProofLengthGap := ⟨h.actualProofLengthGap⟩
  checkedCore := ⟨h.checkedLowerBoundCore⟩
  checkedLowerBound := h.proofLengthFrontier.checked_lower_bound
  noSmallCore := ⟨h.core⟩

theorem project_closure
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty InternalPudlakTheorem5CheckedLowerBoundCore ∧
      Nonempty InternalPudlakTheorem5LowerBoundCore ∧
        Nonempty IntrinsicPudlakTheorem5PowerBoundMachine ∧
          Nonempty InternalPudlakTheorem5PowerBoundMachine ∧
            Nonempty InternalPudlakTheorem5Machine ∧
              Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
                (h.toCheckedLowerBoundCoreChecklist
                    strengthened_to_partial transfer_to_graft project_gap
                  |>.toProjectChecklist project_upper).not_rational =
                  GenericRationalCollisionInputs.not_rational
                    (h.toCheckedLowerBoundCoreChecklist
                      strengthened_to_partial transfer_to_graft project_gap
                    |>.toProjectChecklist project_upper).toGenericCollisionInputs := by
  rcases month9_month10_checked_lower_bound_core_closure
      (h.toCheckedLowerBoundCoreChecklist
        strengthened_to_partial transfer_to_graft project_gap)
      project_upper with
    ⟨h_checked, h_lower, h_intrinsic, h_power, h_machine, h_package,
      _h_exact, _h_code, h_generic⟩
  exact
    ⟨h_checked, h_lower, h_intrinsic, h_power, h_machine, h_package,
      h_generic⟩

def toProjectChecklist
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ProjectCollisionChecklist :=
  (h.toCheckedLowerBoundCoreChecklist
    strengthened_to_partial transfer_to_graft project_gap).toProjectChecklist
    project_upper

theorem project_collision_witness_n_eq_max
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((h.toProjectChecklist
        strengthened_to_partial transfer_to_graft project_gap project_upper)
      |>.projectCollisionWitnessOfRationality hrat).n =
      max
        ((h.toProjectChecklist
            strengthened_to_partial transfer_to_graft project_gap project_upper)
          |>.upperTailOfRationality hrat).upperN
        (((h.toProjectChecklist
            strengthened_to_partial transfer_to_graft project_gap project_upper)
          |>.witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            ((h.toProjectChecklist
              strengthened_to_partial transfer_to_graft project_gap project_upper)
              |>.upperTailOfRationality hrat).U
            ((h.toProjectChecklist
              strengthened_to_partial transfer_to_graft project_gap project_upper)
              |>.upperTailOfRationality hrat).polynomial)
          |>.threshold) :=
  (h.toProjectChecklist
    strengthened_to_partial transfer_to_graft project_gap project_upper)
    |>.projectCollisionWitness_n_eq_max hrat

theorem project_computed_n_contradiction
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.toProjectChecklist
    strengthened_to_partial transfer_to_graft project_gap project_upper)
    |>.computed_n_contradiction hrat

theorem project_not_rational_eq_generic_core
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (h.toProjectChecklist
        strengthened_to_partial transfer_to_graft project_gap project_upper
      |>.not_rational) =
      GenericRationalCollisionInputs.not_rational
        (h.toProjectChecklist
          strengthened_to_partial transfer_to_graft project_gap project_upper
          |>.toGenericCollisionInputs) :=
  (h.toProjectChecklist
    strengthened_to_partial transfer_to_graft project_gap project_upper)
    |>.not_rational_eq_generic_core

theorem project_computed_witness_closure
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      ((h.toProjectChecklist
          strengthened_to_partial transfer_to_graft project_gap project_upper)
        |>.projectCollisionWitnessOfRationality hrat).n =
        max
          ((h.toProjectChecklist
              strengthened_to_partial transfer_to_graft project_gap project_upper)
            |>.upperTailOfRationality hrat).upperN
          (((h.toProjectChecklist
              strengthened_to_partial transfer_to_graft project_gap project_upper)
            |>.witness_checklist.computable_gap
            |>.gap_for_polynomial_upper
              ((h.toProjectChecklist
                strengthened_to_partial transfer_to_graft project_gap project_upper)
                |>.upperTailOfRationality hrat).U
              ((h.toProjectChecklist
                strengthened_to_partial transfer_to_graft project_gap project_upper)
                |>.upperTailOfRationality hrat).polynomial)
            |>.threshold)) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False) ∧
        (h.toProjectChecklist
            strengthened_to_partial transfer_to_graft project_gap project_upper
          |>.not_rational) =
          GenericRationalCollisionInputs.not_rational
            (h.toProjectChecklist
              strengthened_to_partial transfer_to_graft project_gap project_upper
              |>.toGenericCollisionInputs) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hrat
    exact
      h.project_collision_witness_n_eq_max
        strengthened_to_partial transfer_to_graft project_gap project_upper hrat
  · intro hrat
    exact
      h.project_computed_n_contradiction
        strengthened_to_partial transfer_to_graft project_gap project_upper hrat
  · exact
      h.project_not_rational_eq_generic_core
        strengthened_to_partial transfer_to_graft project_gap project_upper

theorem project_closure_of_constant_pieces
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Nonempty InternalPudlakTheorem5CheckedLowerBoundCore ∧
      Nonempty InternalPudlakTheorem5LowerBoundCore ∧
        Nonempty IntrinsicPudlakTheorem5PowerBoundMachine ∧
          Nonempty InternalPudlakTheorem5PowerBoundMachine ∧
            Nonempty InternalPudlakTheorem5Machine ∧
              Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
                (h.toCheckedLowerBoundCoreChecklistOfConstantPieces
                    strengthened_to_partial partial_to_graft project_gap
                  |>.toProjectChecklist project_upper).not_rational =
                  GenericRationalCollisionInputs.not_rational
                    (h.toCheckedLowerBoundCoreChecklistOfConstantPieces
                      strengthened_to_partial partial_to_graft project_gap
                    |>.toProjectChecklist project_upper).toGenericCollisionInputs :=
  h.project_closure
    (InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
      strengthened_to_partial)
    (InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
      partial_to_graft)
    project_gap
    project_upper

theorem not_rational_of_constant_pieces
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  (h.toCheckedLowerBoundCoreChecklistOfConstantPieces
    strengthened_to_partial partial_to_graft project_gap
    |>.toProjectChecklist project_upper).not_rational

theorem closure
    (h : Month9Month10Month11NoSmallCoreHandoff) :
    h.Audit ∧
      h.proofLengthFrontier.Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured h.scale_data)) ∧
          Nonempty InternalPudlakTheorem5CheckedLowerBoundCore ∧
            Nonempty
              InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  ⟨h.audit,
    h.proofLengthFrontier.audit,
    ⟨h.actualProofLengthGap⟩,
    ⟨h.checkedLowerBoundCore⟩,
    ⟨h.core⟩⟩

end Month9Month10Month11NoSmallCoreHandoff

theorem month9_month10_month11_no_small_core_handoff_closure
    (h : Month9Month10Month11NoSmallCoreHandoff) :
    h.Audit ∧
      h.proofLengthFrontier.Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured h.scale_data)) ∧
          Nonempty InternalPudlakTheorem5CheckedLowerBoundCore ∧
            Nonempty
              InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  h.closure

/-! ## Minimal residual endpoint for the corrected no-small-core route -/

/-- Minimal Month 9-10 endpoint after the exact-scale route has been ruled out.
It keeps the real proof-complexity input as `handoff.core` and exposes only the
project transfer, gap, and upper-route data still needed to compute the final
collision witness. -/
structure Month9Month10NoSmallCoreResidualEndpoint : Type 1 where
  handoff : Month9Month10Month11NoSmallCoreHandoff
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  transfer_to_graft :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer
  project_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox
  project_upper : SondowProjectLocalS21CollapseConclusion

namespace Month9Month10NoSmallCoreResidualEndpoint

def toProjectChecklist
    (h : Month9Month10NoSmallCoreResidualEndpoint) :
    Month9Month10ProjectCollisionChecklist :=
  h.handoff.toProjectChecklist
    h.strengthened_to_partial h.transfer_to_graft h.project_gap
    h.project_upper

noncomputable def computedCollisionNOfRationality
    (h : Month9Month10NoSmallCoreResidualEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  (h.toProjectChecklist.projectCollisionWitnessOfRationality hrat).n

theorem computedCollisionN_eq_max
    (h : Month9Month10NoSmallCoreResidualEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      max (h.toProjectChecklist.upperTailOfRationality hrat).upperN
        ((h.toProjectChecklist.witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            (h.toProjectChecklist.upperTailOfRationality hrat).U
            (h.toProjectChecklist.upperTailOfRationality hrat).polynomial)
          |>.threshold) :=
  h.handoff.project_collision_witness_n_eq_max
    h.strengthened_to_partial h.transfer_to_graft h.project_gap
    h.project_upper hrat

theorem computed_n_contradiction
    (h : Month9Month10NoSmallCoreResidualEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.handoff.project_computed_n_contradiction
    h.strengthened_to_partial h.transfer_to_graft h.project_gap
    h.project_upper hrat

theorem computedCollisionN_project_upper_lower_trace
    (h : Month9Month10NoSmallCoreResidualEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let upper := h.toProjectChecklist.upperTailOfRationality hrat
    upper.U (h.computedCollisionNOfRationality hrat) <
        sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat) ∧
      sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat) ≤
        upper.U (h.computedCollisionNOfRationality hrat) ∧
      False := by
  let witness := h.toProjectChecklist.projectCollisionWitnessOfRationality hrat
  have hlower :
      (h.toProjectChecklist.upperTailOfRationality hrat).U witness.n <
        sondowProjectLocalPudlakCollisionBox witness.n :=
    witness.lower_at_n
  have hupper :
      sondowProjectLocalPudlakCollisionBox witness.n ≤
        (h.toProjectChecklist.upperTailOfRationality hrat).U witness.n :=
    witness.upper_at_n
  dsimp [computedCollisionNOfRationality, witness] at hlower hupper ⊢
  exact ⟨hlower, hupper, (not_lt_of_ge hupper) hlower⟩

theorem not_rational
    (h : Month9Month10NoSmallCoreResidualEndpoint) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toProjectChecklist.not_rational

theorem not_rational_eq_generic_core
    (h : Month9Month10NoSmallCoreResidualEndpoint) :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational
        h.toProjectChecklist.toGenericCollisionInputs :=
  h.handoff.project_not_rational_eq_generic_core
    h.strengthened_to_partial h.transfer_to_graft h.project_gap
    h.project_upper

theorem project_closure
    (h : Month9Month10NoSmallCoreResidualEndpoint) :
    Nonempty InternalPudlakTheorem5CheckedLowerBoundCore ∧
      Nonempty InternalPudlakTheorem5LowerBoundCore ∧
        Nonempty IntrinsicPudlakTheorem5PowerBoundMachine ∧
          Nonempty InternalPudlakTheorem5PowerBoundMachine ∧
            Nonempty InternalPudlakTheorem5Machine ∧
              Nonempty _root_.PudlakFiniteConsistencyLowerBoundPackage ∧
                h.toProjectChecklist.not_rational =
                  GenericRationalCollisionInputs.not_rational
                    h.toProjectChecklist.toGenericCollisionInputs :=
  h.handoff.project_closure
    h.strengthened_to_partial h.transfer_to_graft h.project_gap
    h.project_upper

theorem computed_witness_closure
    (h : Month9Month10NoSmallCoreResidualEndpoint) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        max (h.toProjectChecklist.upperTailOfRationality hrat).upperN
          ((h.toProjectChecklist.witness_checklist.computable_gap
            |>.gap_for_polynomial_upper
              (h.toProjectChecklist.upperTailOfRationality hrat).U
              (h.toProjectChecklist.upperTailOfRationality hrat).polynomial)
            |>.threshold)) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False) ∧
        h.not_rational =
          GenericRationalCollisionInputs.not_rational
            h.toProjectChecklist.toGenericCollisionInputs :=
  ⟨h.computedCollisionN_eq_max,
    h.computed_n_contradiction,
    h.not_rational_eq_generic_core⟩

structure Audit
    (h : Month9Month10NoSmallCoreResidualEndpoint) : Prop where
  handoffAudit : h.handoff.Audit
  handoffClosure :
    h.handoff.proofLengthFrontier.Audit
  projectChecklist :
    Nonempty Month9Month10ProjectCollisionChecklist
  computedWitnessFormula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        max (h.toProjectChecklist.upperTailOfRationality hrat).upperN
          ((h.toProjectChecklist.witness_checklist.computable_gap
            |>.gap_for_polynomial_upper
              (h.toProjectChecklist.upperTailOfRationality hrat).U
              (h.toProjectChecklist.upperTailOfRationality hrat).polynomial)
            |>.threshold)
  contradictionAtComputedWitness :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni
  notRationalEqGeneric :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational
        h.toProjectChecklist.toGenericCollisionInputs

theorem audit
    (h : Month9Month10NoSmallCoreResidualEndpoint) :
    Audit h where
  handoffAudit := h.handoff.audit
  handoffClosure := h.handoff.proofLengthFrontier.audit
  projectChecklist := ⟨h.toProjectChecklist⟩
  computedWitnessFormula := h.computedCollisionN_eq_max
  contradictionAtComputedWitness := h.computed_n_contradiction
  endpointNotRational := h.not_rational
  notRationalEqGeneric := h.not_rational_eq_generic_core

theorem closure
    (h : Month9Month10NoSmallCoreResidualEndpoint) :
    h.Audit ∧
      h.handoff.Audit ∧
        Nonempty Month9Month10ProjectCollisionChecklist ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            h.computedCollisionNOfRationality hrat =
              max (h.toProjectChecklist.upperTailOfRationality hrat).upperN
                ((h.toProjectChecklist.witness_checklist.computable_gap
                  |>.gap_for_polynomial_upper
                    (h.toProjectChecklist.upperTailOfRationality hrat).U
                    (h.toProjectChecklist.upperTailOfRationality hrat).polynomial)
                  |>.threshold)) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨h.audit,
    h.handoff.audit,
    ⟨h.toProjectChecklist⟩,
    h.computedCollisionN_eq_max,
    h.computed_n_contradiction,
    h.not_rational⟩

end Month9Month10NoSmallCoreResidualEndpoint

/-- Same minimal endpoint, but with the two transfer fields given as constant
projection certificates.  This is the preferred residual target for eliminating
the remaining payload assumptions one layer at a time. -/
structure Month9Month10NoSmallCoreConstantProjectionResidualEndpoint :
    Type 1 where
  handoff : Month9Month10Month11NoSmallCoreHandoff
  strengthened_to_partial :
    _root_.StrengthenedToPartialConsistencyConstantProjection
  partial_to_graft : _root_.PAConjunctionEliminationConstantCost
  project_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox
  project_upper : SondowProjectLocalS21CollapseConclusion

namespace Month9Month10NoSmallCoreConstantProjectionResidualEndpoint

def strengthenedTransfer
    (h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint) :
    _root_.StrengthenedToPartialConsistencyLowerBoundTransfer :=
  InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
    h.strengthened_to_partial

def transferToGraft
    (h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint) :
    _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer :=
  InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
    h.partial_to_graft

def toResidualEndpoint
    (h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint) :
    Month9Month10NoSmallCoreResidualEndpoint where
  handoff := h.handoff
  strengthened_to_partial := h.strengthenedTransfer
  transfer_to_graft := h.transferToGraft
  project_gap := h.project_gap
  project_upper := h.project_upper

def toProjectChecklist
    (h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint) :
    Month9Month10ProjectCollisionChecklist :=
  h.toResidualEndpoint.toProjectChecklist

noncomputable def computedCollisionNOfRationality
    (h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  h.toResidualEndpoint.computedCollisionNOfRationality hrat

theorem computedCollisionN_eq_max
    (h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      max (h.toProjectChecklist.upperTailOfRationality hrat).upperN
        ((h.toProjectChecklist.witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            (h.toProjectChecklist.upperTailOfRationality hrat).U
            (h.toProjectChecklist.upperTailOfRationality hrat).polynomial)
          |>.threshold) :=
  h.toResidualEndpoint.computedCollisionN_eq_max hrat

theorem computed_n_contradiction
    (h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.toResidualEndpoint.computed_n_contradiction hrat

theorem not_rational
    (h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toResidualEndpoint.not_rational

theorem computed_witness_closure
    (h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        max (h.toProjectChecklist.upperTailOfRationality hrat).upperN
          ((h.toProjectChecklist.witness_checklist.computable_gap
            |>.gap_for_polynomial_upper
              (h.toProjectChecklist.upperTailOfRationality hrat).U
              (h.toProjectChecklist.upperTailOfRationality hrat).polynomial)
            |>.threshold)) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False) ∧
        h.not_rational =
          GenericRationalCollisionInputs.not_rational
            h.toProjectChecklist.toGenericCollisionInputs :=
  h.toResidualEndpoint.computed_witness_closure

theorem closure
    (h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint) :
    h.toResidualEndpoint.Audit ∧
      Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection ∧
        Nonempty _root_.PAConjunctionEliminationConstantCost ∧
          Nonempty Month9Month10ProjectCollisionChecklist ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              h.computedCollisionNOfRationality hrat =
                max (h.toProjectChecklist.upperTailOfRationality hrat).upperN
                  ((h.toProjectChecklist.witness_checklist.computable_gap
                    |>.gap_for_polynomial_upper
                      (h.toProjectChecklist.upperTailOfRationality hrat).U
                      (h.toProjectChecklist.upperTailOfRationality hrat).polynomial)
                    |>.threshold)) ∧
              (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                False) ∧
                ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨h.toResidualEndpoint.audit,
    ⟨h.strengthened_to_partial⟩,
    ⟨h.partial_to_graft⟩,
    ⟨h.toProjectChecklist⟩,
    h.computedCollisionN_eq_max,
    h.computed_n_contradiction,
    h.not_rational⟩

structure ResidualDataAudit
    (h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint) :
    Prop where
  noSmallCore :
    Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}
  strengthenedProjection :
    Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection
  partialProjection :
    Nonempty _root_.PAConjunctionEliminationConstantCost
  projectGap :
    Nonempty
      (ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
  projectUpper :
    Nonempty SondowProjectLocalS21CollapseConclusion
  projectChecklist :
    Nonempty Month9Month10ProjectCollisionChecklist
  computedWitnessFormula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        max (h.toProjectChecklist.upperTailOfRationality hrat).upperN
          ((h.toProjectChecklist.witness_checklist.computable_gap
            |>.gap_for_polynomial_upper
              (h.toProjectChecklist.upperTailOfRationality hrat).U
              (h.toProjectChecklist.upperTailOfRationality hrat).polynomial)
            |>.threshold)
  contradictionAtComputedWitness :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem residual_data_audit
    (h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint) :
    ResidualDataAudit h where
  noSmallCore := ⟨h.handoff.core⟩
  strengthenedProjection := ⟨h.strengthened_to_partial⟩
  partialProjection := ⟨h.partial_to_graft⟩
  projectGap := ⟨h.project_gap⟩
  projectUpper := ⟨h.project_upper⟩
  projectChecklist := ⟨h.toProjectChecklist⟩
  computedWitnessFormula := h.computedCollisionN_eq_max
  contradictionAtComputedWitness := h.computed_n_contradiction
  endpointNotRational := h.not_rational

theorem residual_data_closure
    (h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint) :
    h.ResidualDataAudit ∧
      Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} ∧
        Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection ∧
          Nonempty _root_.PAConjunctionEliminationConstantCost ∧
            Nonempty
              (ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
              Nonempty SondowProjectLocalS21CollapseConclusion ∧
                Nonempty Month9Month10ProjectCollisionChecklist ∧
                  (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                    h.computedCollisionNOfRationality hrat =
                      max (h.toProjectChecklist.upperTailOfRationality hrat).upperN
                        ((h.toProjectChecklist.witness_checklist.computable_gap
                          |>.gap_for_polynomial_upper
                            (h.toProjectChecklist.upperTailOfRationality hrat).U
                            (h.toProjectChecklist.upperTailOfRationality hrat).polynomial)
                          |>.threshold)) ∧
                    (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                      False) ∧
                      ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨h.residual_data_audit,
    ⟨h.handoff.core⟩,
    ⟨h.strengthened_to_partial⟩,
    ⟨h.partial_to_graft⟩,
    ⟨h.project_gap⟩,
    ⟨h.project_upper⟩,
    ⟨h.toProjectChecklist⟩,
    h.computedCollisionN_eq_max,
    h.computed_n_contradiction,
    h.not_rational⟩

end Month9Month10NoSmallCoreConstantProjectionResidualEndpoint

/-! ## Payload-spec adapters into the corrected no-small-core endpoint -/

namespace Month9Month10DualPayloadSpecResidualAdapter

def residualEndpoint
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{0}) :
    Month9Month10NoSmallCoreConstantProjectionResidualEndpoint where
  handoff := {
    core :=
      h.toProjectEndpointInputs.checker_checklist
        |>.theorem5_computable_search_core
  }
  strengthened_to_partial :=
    h.lower_inputs.strengthened_to_partial_projection
  partial_to_graft := h.partial_to_graft_projection
  project_gap := h.computable_gap
  project_upper := h.project_upper

theorem residual_data_closure
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{0}) :
    (residualEndpoint h).ResidualDataAudit ∧
      Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} ∧
        Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection ∧
          Nonempty _root_.PAConjunctionEliminationConstantCost ∧
            Nonempty
              (ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
              Nonempty SondowProjectLocalS21CollapseConclusion ∧
                Nonempty Month9Month10ProjectCollisionChecklist ∧
                  (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                    (residualEndpoint h).computedCollisionNOfRationality hrat =
                      max
                        (residualEndpoint h
                          |>.toProjectChecklist
                          |>.upperTailOfRationality hrat).upperN
                        ((residualEndpoint h
                          |>.toProjectChecklist
                          |>.witness_checklist.computable_gap
                          |>.gap_for_polynomial_upper
                            (residualEndpoint h
                              |>.toProjectChecklist
                              |>.upperTailOfRationality hrat).U
                            (residualEndpoint h
                              |>.toProjectChecklist
                              |>.upperTailOfRationality hrat).polynomial)
                          |>.threshold)) ∧
                    (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                      False) ∧
                      ¬ _root_.is_rational _root_.euler_mascheroni :=
  (residualEndpoint h).residual_data_closure

theorem computed_witness_closure
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{0}) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (residualEndpoint h).computedCollisionNOfRationality hrat =
        max
          (residualEndpoint h
            |>.toProjectChecklist
            |>.upperTailOfRationality hrat).upperN
          ((residualEndpoint h
            |>.toProjectChecklist
            |>.witness_checklist.computable_gap
            |>.gap_for_polynomial_upper
              (residualEndpoint h
                |>.toProjectChecklist
                |>.upperTailOfRationality hrat).U
              (residualEndpoint h
                |>.toProjectChecklist
                |>.upperTailOfRationality hrat).polynomial)
            |>.threshold)) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False) ∧
        (residualEndpoint h
          |>.not_rational) =
          GenericRationalCollisionInputs.not_rational
            (residualEndpoint h
              |>.toProjectChecklist
              |>.toGenericCollisionInputs) :=
  (residualEndpoint h).computed_witness_closure

structure ResidualAdapterAudit
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{0}) :
    Prop where
  dualAudit : h.Audit
  residualAudit :
    (residualEndpoint h).ResidualDataAudit
  payloadSpec :
    Nonempty PartialConsistencyPayloadSpecCertificate
  strengthenedPayloadSpec :
    Nonempty Month9Month10StrengthenedPayloadSpecCertificate
  residualClosure :
    (residualEndpoint h).ResidualDataAudit ∧
      Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} ∧
        Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection ∧
          Nonempty _root_.PAConjunctionEliminationConstantCost ∧
            Nonempty
              (ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
              Nonempty SondowProjectLocalS21CollapseConclusion ∧
                Nonempty Month9Month10ProjectCollisionChecklist ∧
                  (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                    (residualEndpoint h).computedCollisionNOfRationality hrat =
                      max
                        (residualEndpoint h
                          |>.toProjectChecklist
                          |>.upperTailOfRationality hrat).upperN
                        ((residualEndpoint h
                          |>.toProjectChecklist
                          |>.witness_checklist.computable_gap
                          |>.gap_for_polynomial_upper
                            (residualEndpoint h
                              |>.toProjectChecklist
                              |>.upperTailOfRationality hrat).U
                            (residualEndpoint h
                              |>.toProjectChecklist
                              |>.upperTailOfRationality hrat).polynomial)
                          |>.threshold)) ∧
                    (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                      False) ∧
                      ¬ _root_.is_rational _root_.euler_mascheroni

theorem residual_adapter_audit
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{0}) :
    ResidualAdapterAudit h where
  dualAudit := h.audit
  residualAudit :=
    (residualEndpoint h).residual_data_audit
  payloadSpec := h.upper_inputs.payloadSpec_nonempty
  strengthenedPayloadSpec := h.lower_inputs.strengthenedSpec_nonempty
  residualClosure := residual_data_closure h

/-- The computed-witness formula exposed by the corrected no-small-core
residual endpoint.  Keeping this as a named proposition makes downstream
audits independent of the older exact-scale endpoint. -/
abbrev ComputedWitnessFormula
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{0}) :
    Prop :=
  ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
    (residualEndpoint h).computedCollisionNOfRationality hrat =
      max
        (residualEndpoint h
          |>.toProjectChecklist
          |>.upperTailOfRationality hrat).upperN
        ((residualEndpoint h
          |>.toProjectChecklist
          |>.witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            (residualEndpoint h
              |>.toProjectChecklist
              |>.upperTailOfRationality hrat).U
            (residualEndpoint h
              |>.toProjectChecklist
              |>.upperTailOfRationality hrat).polynomial)
          |>.threshold)

theorem computed_witness_formula
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{0}) :
    ComputedWitnessFormula h :=
  (computed_witness_closure h).1

theorem contradiction_at_computed_witness
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{0}) :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False :=
  (computed_witness_closure h).2.1

theorem endpoint_not_rational_eq_generic_core
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{0}) :
    (residualEndpoint h
      |>.not_rational) =
      GenericRationalCollisionInputs.not_rational
        (residualEndpoint h
          |>.toProjectChecklist
          |>.toGenericCollisionInputs) :=
  (computed_witness_closure h).2.2

/-- Fine-grained audit package for the dual payload-spec route.  It records the
ordinary payload, strengthened payload, checker-length calibration, corrected
no-small-core endpoint, and computed witness equation in one probeable object. -/
structure PayloadSpecResidualFineAudit
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{0}) :
    Prop where
  upperAudit :
    h.upper_inputs.Audit
  strengthenedLowerAudit :
    h.lower_inputs.Audit
  dualEndpointAudit :
    h.Audit
  residualAdapterAudit :
    ResidualAdapterAudit h
  residualDataAudit :
    (residualEndpoint h).ResidualDataAudit
  ordinaryAcceptedTruth :
    Nonempty _root_.PartialConsistencyAcceptedTruth
  ordinaryPayloadTruth :
    Nonempty _root_.PartialConsistencyPayloadTruth
  strengthenedAcceptedTruth :
    _root_.StrengthenedPartialConsistencyAcceptedTruth
  strengthenedPayloadTruth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthenedConstantProjection :
    Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection
  partialToGraftProjection :
    Nonempty _root_.PAConjunctionEliminationConstantCost
  computableGap :
    Nonempty
      (ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
  lengthCalibration :
    Nonempty
      (InternalPudlakTheorem5CheckerFamilyLengthCalibration h.checker)
  noSmallCore :
    Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}
  projectChecklist :
    Nonempty Month9Month10ProjectCollisionChecklist
  computedWitnessFormula :
    ComputedWitnessFormula h
  contradictionAtComputedWitness :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  endpointNotRationalEqGenericCore :
    (residualEndpoint h
      |>.not_rational) =
      GenericRationalCollisionInputs.not_rational
        (residualEndpoint h
          |>.toProjectChecklist
          |>.toGenericCollisionInputs)
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem payload_spec_residual_fine_audit
    (h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{0}) :
    PayloadSpecResidualFineAudit h where
  upperAudit := h.upper_inputs.audit
  strengthenedLowerAudit := h.lower_inputs.audit
  dualEndpointAudit := h.audit
  residualAdapterAudit := residual_adapter_audit h
  residualDataAudit := (residualEndpoint h).residual_data_audit
  ordinaryAcceptedTruth := h.upper_inputs.acceptedTruth_nonempty
  ordinaryPayloadTruth := h.upper_inputs.payloadTruth_nonempty
  strengthenedAcceptedTruth := h.lower_inputs.strengthenedAcceptedTruth
  strengthenedPayloadTruth := h.lower_inputs.strengthenedPayloadTruth
  strengthenedConstantProjection := h.lower_inputs.constantProjection_nonempty
  partialToGraftProjection := ⟨h.partial_to_graft_projection⟩
  computableGap := ⟨h.computable_gap⟩
  lengthCalibration := ⟨h.length_calibration⟩
  noSmallCore := ⟨(residualEndpoint h).handoff.core⟩
  projectChecklist := ⟨(residualEndpoint h).toProjectChecklist⟩
  computedWitnessFormula := computed_witness_formula h
  contradictionAtComputedWitness :=
    contradiction_at_computed_witness h
  endpointNotRationalEqGenericCore :=
    endpoint_not_rational_eq_generic_core h
  endpointNotRational := (residualEndpoint h).not_rational

end Month9Month10DualPayloadSpecResidualAdapter

namespace Month9Month10SplitPayloadSpecResidualAdapter

def residualEndpoint
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0}) :
    Month9Month10NoSmallCoreConstantProjectionResidualEndpoint :=
  Month9Month10DualPayloadSpecResidualAdapter.residualEndpoint
    h.toDualPayloadSpecCalibratedEndpointInputs

theorem residual_data_closure
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0}) :
    (residualEndpoint h).ResidualDataAudit ∧
      Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} ∧
        Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection ∧
          Nonempty _root_.PAConjunctionEliminationConstantCost ∧
            Nonempty
              (ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
              Nonempty SondowProjectLocalS21CollapseConclusion ∧
                Nonempty Month9Month10ProjectCollisionChecklist ∧
                  (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                    (residualEndpoint h).computedCollisionNOfRationality hrat =
                      max
                        (residualEndpoint h
                          |>.toProjectChecklist
                          |>.upperTailOfRationality hrat).upperN
                        ((residualEndpoint h
                          |>.toProjectChecklist
                          |>.witness_checklist.computable_gap
                          |>.gap_for_polynomial_upper
                            (residualEndpoint h
                              |>.toProjectChecklist
                              |>.upperTailOfRationality hrat).U
                            (residualEndpoint h
                              |>.toProjectChecklist
                              |>.upperTailOfRationality hrat).polynomial)
                          |>.threshold)) ∧
                    (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                      False) ∧
                      ¬ _root_.is_rational _root_.euler_mascheroni :=
  Month9Month10DualPayloadSpecResidualAdapter.residual_data_closure
    h.toDualPayloadSpecCalibratedEndpointInputs

theorem computed_witness_closure
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0}) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (residualEndpoint h).computedCollisionNOfRationality hrat =
        max
          (residualEndpoint h
            |>.toProjectChecklist
            |>.upperTailOfRationality hrat).upperN
          ((residualEndpoint h
            |>.toProjectChecklist
            |>.witness_checklist.computable_gap
            |>.gap_for_polynomial_upper
              (residualEndpoint h
                |>.toProjectChecklist
                |>.upperTailOfRationality hrat).U
              (residualEndpoint h
                |>.toProjectChecklist
                |>.upperTailOfRationality hrat).polynomial)
            |>.threshold)) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False) ∧
        (residualEndpoint h
          |>.not_rational) =
          GenericRationalCollisionInputs.not_rational
            (residualEndpoint h
              |>.toProjectChecklist
              |>.toGenericCollisionInputs) :=
  Month9Month10DualPayloadSpecResidualAdapter.computed_witness_closure
    h.toDualPayloadSpecCalibratedEndpointInputs

/-- Computed-witness formula for the split payload-spec route.  This is the
same residual endpoint as the dual adapter, but its audit keeps the accepted
projection and constant-overhead projection separate. -/
abbrev ComputedWitnessFormula
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0}) :
    Prop :=
  ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
    (residualEndpoint h).computedCollisionNOfRationality hrat =
      max
        (residualEndpoint h
          |>.toProjectChecklist
          |>.upperTailOfRationality hrat).upperN
        ((residualEndpoint h
          |>.toProjectChecklist
          |>.witness_checklist.computable_gap
          |>.gap_for_polynomial_upper
            (residualEndpoint h
              |>.toProjectChecklist
              |>.upperTailOfRationality hrat).U
            (residualEndpoint h
              |>.toProjectChecklist
              |>.upperTailOfRationality hrat).polynomial)
          |>.threshold)

theorem computed_witness_formula
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0}) :
    ComputedWitnessFormula h :=
  (computed_witness_closure h).1

theorem contradiction_at_computed_witness
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0}) :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False :=
  (computed_witness_closure h).2.1

theorem endpoint_not_rational_eq_generic_core
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0}) :
    (residualEndpoint h
      |>.not_rational) =
      GenericRationalCollisionInputs.not_rational
        (residualEndpoint h
          |>.toProjectChecklist
          |>.toGenericCollisionInputs) :=
  (computed_witness_closure h).2.2

/-- Fine-grained audit package for the split payload-spec route.  This is the
handoff object a reviewer can inspect to see that the lower-bound transfer uses
the accepted projection while the computable residual endpoint keeps the
fixed-overhead projection needed for explicit witness extraction. -/
structure SplitPayloadSpecResidualFineAudit
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0}) :
    Prop where
  splitEndpointAudit :
    h.Audit
  lowerSplitAudit :
    h.lower_split.Audit
  dualFineAudit :
    Month9Month10DualPayloadSpecResidualAdapter.PayloadSpecResidualFineAudit
      h.toDualPayloadSpecCalibratedEndpointInputs
  residualDataAudit :
    (residualEndpoint h).ResidualDataAudit
  acceptedProjectionPackage :
    Nonempty _root_.StrengthenedToPartialAcceptedProjectionPackage
  acceptedProjectionMatchesSpec :
    h.lower_split.accepted_projection_package.accepted_projection =
      _root_.PartialToStrengthenedAcceptedProjection.ofStrengthenedAcceptedTruth
        h.lower_split.lower_inputs.strengthenedAcceptedTruth
  acceptedTransfer :
    Nonempty _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  constantProjection :
    Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection
  constantTransfer :
    Nonempty _root_.StrengthenedToPartialConsistencyLowerBoundTransfer
  partialToGraftProjection :
    Nonempty _root_.PAConjunctionEliminationConstantCost
  computableGap :
    Nonempty
      (ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
  noSmallCore :
    Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}
  computedWitnessFormula :
    ComputedWitnessFormula h
  contradictionAtComputedWitness :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  endpointNotRationalEqGenericCore :
    (residualEndpoint h
      |>.not_rational) =
      GenericRationalCollisionInputs.not_rational
        (residualEndpoint h
          |>.toProjectChecklist
          |>.toGenericCollisionInputs)
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem split_payload_spec_residual_fine_audit
    (h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0}) :
    SplitPayloadSpecResidualFineAudit h where
  splitEndpointAudit := h.audit
  lowerSplitAudit := h.lower_split.audit
  dualFineAudit :=
    Month9Month10DualPayloadSpecResidualAdapter.payload_spec_residual_fine_audit
      h.toDualPayloadSpecCalibratedEndpointInputs
  residualDataAudit := (residualEndpoint h).residual_data_audit
  acceptedProjectionPackage :=
    h.lower_split.acceptedProjectionPackage_nonempty
  acceptedProjectionMatchesSpec :=
    h.lower_split.accepted_projection_matches_spec
  acceptedTransfer :=
    h.lower_split.acceptedProjectionTransfer_nonempty
  constantProjection :=
    h.lower_split.constantProjection_nonempty
  constantTransfer :=
    h.lower_split.constantProjectionTransfer_nonempty
  partialToGraftProjection := ⟨h.partial_to_graft_projection⟩
  computableGap := ⟨h.computable_gap⟩
  noSmallCore := ⟨(residualEndpoint h).handoff.core⟩
  computedWitnessFormula := computed_witness_formula h
  contradictionAtComputedWitness :=
    contradiction_at_computed_witness h
  endpointNotRationalEqGenericCore :=
    endpoint_not_rational_eq_generic_core h
  endpointNotRational := (residualEndpoint h).not_rational

end Month9Month10SplitPayloadSpecResidualAdapter

/-! ## Negative audit for the old exact-scale endpoint -/

def scaleGapOfFinalThreeCertificateEndpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    ComputableSearchGapCertificate (scaleMeasured scale_data) :=
  transportComputableSearchGap endpoint.proof_length_eq_scale
    endpoint.proof_length_gap

theorem scaleGapOfFinalThreeCertificateEndpoint_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((scaleGapOfFinalThreeCertificateEndpoint endpoint)
      |>.gap_for_polynomial_upper U hU).witness N =
      (endpoint.proof_length_gap.gap_for_polynomial_upper U hU).witness N :=
  rfl

/-- The old final three-certificate endpoint is not instantiable under the
current `scale_polynomial_bound` field.  Its proof-length gap plus
`proof_length = scale` transports into an impossible search gap for the
polynomially bounded scale. -/
theorem no_final_three_certificate_endpoint_for_internal_scale
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    False :=
  no_scale_search_gap_for_internal_scale scale_data
    (scaleGapOfFinalThreeCertificateEndpoint endpoint)

/-- Stronger form of the same negative audit: the old final endpoint's exact
calibration to the polynomially bounded scale is already incompatible with the
current strong proof-length lower-bound target for `powerBoundRawCode`. -/
theorem no_final_three_certificate_endpoint_strong_lower_bound_for_internal_scale
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data) :
    ¬ _root_.StrongProofLengthLowerBound
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      scale_data.powerBoundRawCode :=
  no_internal_power_bound_strong_lower_bound_of_proof_length_eq_scale
    endpoint.proof_length_eq_scale

theorem no_final_three_certificate_deliverables_for_internal_scale
    {scale_data : InternalPudlakTheorem5ScaleData}
    (deliverables :
      ConcretePAHilbertPowerBoundFinalThreeCertificateDeliverables
        scale_data) :
    False :=
  no_final_three_certificate_endpoint_for_internal_scale
    deliverables.endpoint

/-- Handoff wrapper for the final Month 11-12 three-certificate deliverables.
This is the preferred downstream interface: it consumes the materialized
deliverables generated from `FinalThreeCertificateEndpoint`, then exposes both
the Month 9-10 checker-extractor route and the proof-length frontier route. -/
structure Month9Month10Month11ThreeCertificateHandoff
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 3 where
  deliverables :
    ConcretePAHilbertPowerBoundFinalThreeCertificateDeliverables
      scale_data

namespace Month9Month10Month11ThreeCertificateHandoff

def endpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data :=
  h.deliverables.endpoint

def closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
      scale_data :=
  h.deliverables.closure

def canonicalCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    PAHilbertCanonicalCalibratedExactnessCore :=
  h.deliverables.canonicalCore

def checkerSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data :=
  h.closure.checkerSemantics

def finiteEnumeration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    InternalPudlakTheorem5CheckerFiniteEnumeration h.checkerSemantics :=
  h.closure.finiteEnumeration

def rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      h.checkerSemantics h.finiteEnumeration :=
  h.deliverables.rejectionExtractor

theorem proofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    InternalPudlakTheorem5CheckerProofLengthExactness h.checkerSemantics :=
  h.deliverables.proofLengthExactness

def computableSearchProfile
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
      scale_data :=
  h.deliverables.computableSearchProfile

def noSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  h.deliverables.noSmallCore

theorem acceptedCodeExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        formulaCode
        code) :
    PAHilbertFormulaCodeDerivable
      concretePAHilbertTheorem5DerivabilitySemantics
      formulaCode :=
  h.deliverables.acceptedCodeExactness formulaCode code haccepted

theorem transported_gap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    ((h.endpoint.toScaleStrictSizeExactProofGapInput
        |>.toStrictScaleSingletonExactProofLengthGapInput
        |>.transportedGap).gap_for_polynomial_upper f hf).witness N =
      (h.endpoint.proof_length_gap.gap_for_polynomial_upper f hf).witness N :=
  h.deliverables.transportedGapWitnessEq f hf N

def toProofLengthGapFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    Month9Month10ActualProofLengthGapFrontier scale_data where
  actual_proof_length_gap :=
    h.endpoint.proof_length_gap
  proof_length_eq_scale :=
    h.endpoint.proof_length_eq_scale
  scale_strict :=
    h.endpoint.scale_strict

theorem proofLengthFrontierClosure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    h.toProofLengthGapFrontier.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
      Nonempty (ComputableSearchGapCertificate (scaleMeasured scale_data)) ∧
      Nonempty InternalPudlakTheorem5CheckedLowerBoundCore :=
  month9_month10_actual_proof_length_gap_frontier_closure
    h.toProofLengthGapFrontier

theorem actualProofLengthGap_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    Nonempty
      (ComputableSearchGapCertificate
        (actualProofLengthMeasured scale_data)) :=
  ⟨h.endpoint.proof_length_gap⟩

theorem scaleStrict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b :=
  h.endpoint.scale_strict

theorem proof_length_eq_scale
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (scale_data.scale n : Real) :=
  h.endpoint.proof_length_eq_scale

theorem generated_components_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    Nonempty
        (InternalPudlakTheorem5CheckerFiniteEnumeration h.checkerSemantics) ∧
      Nonempty
        (InternalPudlakTheorem5CheckerComputableRejectionExtractor
          h.checkerSemantics h.finiteEnumeration) ∧
        Nonempty
          (InternalPudlakTheorem5CheckerProofLengthExactness
            h.checkerSemantics) ∧
          Nonempty
            (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
              scale_data) ∧
            Nonempty
              InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  ⟨⟨h.finiteEnumeration⟩,
    ⟨h.rejectionExtractor⟩,
    ⟨h.proofLengthExactness⟩,
    ⟨h.computableSearchProfile⟩,
    ⟨h.noSmallCore⟩⟩

def toCheckerExtractorComputableSearchChecklist
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) :
    Month9Month10CheckerExtractorComputableSearchChecklist.{0} where
  scale_data := scale_data
  checker := h.checkerSemantics
  enumeration := h.finiteEnumeration
  extractor := h.rejectionExtractor
  exactness := h.proofLengthExactness
  strengthened_to_partial := strengthened_to_partial
  transfer_to_graft := transfer_to_graft
  computable_gap := project_gap

def toCheckerExtractorComputableSearchChecklistOfConstantPieces
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) :
    Month9Month10CheckerExtractorComputableSearchChecklist.{0} :=
  h.toCheckerExtractorComputableSearchChecklist
    (InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
      strengthened_to_partial)
    (InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
      partial_to_graft)
    project_gap

def toProjectEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorProjectEndpointInputs.{0} where
  checker_checklist :=
    h.toCheckerExtractorComputableSearchChecklistOfConstantPieces
      strengthened_to_partial partial_to_graft project_gap
  strengthened_to_partial := strengthened_to_partial
  partial_to_graft := partial_to_graft
  project_upper := project_upper

theorem project_endpoint_frontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (h.toProjectEndpointInputs strengthened_to_partial partial_to_graft
      project_gap project_upper).EndpointFrontier :=
  (h.toProjectEndpointInputs strengthened_to_partial partial_to_graft
    project_gap project_upper).endpoint_frontier

theorem not_rational_of_project_data
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  (h.toProjectEndpointInputs strengthened_to_partial partial_to_graft
    project_gap project_upper).not_rational

structure Audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) : Prop where
  proofLengthFrontier :
    h.toProofLengthGapFrontier.Audit
  actualProofLengthGap :
    Nonempty
      (ComputableSearchGapCertificate
        (actualProofLengthMeasured scale_data))
  scaleStrict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  proofLengthEqScale :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (scale_data.scale n : Real)
  closure :
    Nonempty
      (ConcretePAHilbertPowerBoundFinalScaleStrictSizeExactProofGapClosure
        scale_data)
  canonicalCore :
    Nonempty PAHilbertCanonicalCalibratedExactnessCore
  finiteEnumeration :
    Nonempty
      (InternalPudlakTheorem5CheckerFiniteEnumeration h.checkerSemantics)
  rejectionExtractor :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableRejectionExtractor
        h.checkerSemantics h.finiteEnumeration)
  proofLengthExactness :
    Nonempty
      (InternalPudlakTheorem5CheckerProofLengthExactness
        h.checkerSemantics)
  computableSearchProfile :
    Nonempty
      (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data)
  noSmallCore :
    Nonempty
      InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}

theorem audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    Audit h where
  proofLengthFrontier := h.toProofLengthGapFrontier.audit
  actualProofLengthGap := h.actualProofLengthGap_nonempty
  scaleStrict := h.scaleStrict
  proofLengthEqScale := h.proof_length_eq_scale
  closure := ⟨h.closure⟩
  canonicalCore := ⟨h.canonicalCore⟩
  finiteEnumeration := ⟨h.finiteEnumeration⟩
  rejectionExtractor := ⟨h.rejectionExtractor⟩
  proofLengthExactness := ⟨h.proofLengthExactness⟩
  computableSearchProfile := ⟨h.computableSearchProfile⟩
  noSmallCore := ⟨h.noSmallCore⟩

end Month9Month10Month11ThreeCertificateHandoff

theorem no_month9_month10_month11_three_certificate_handoff_for_internal_scale
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    False :=
  no_final_three_certificate_deliverables_for_internal_scale
    h.deliverables

def threeCertificateEndpointOfTimeConstructibleBoundStrict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (actual_proof_length_gap :
      ComputableSearchGapCertificate
        (actualProofLengthMeasured scale_data))
    (proof_length_eq_scale :
      ∀ n : Nat,
        actualProofLengthMeasured scale_data n =
          scaleMeasured scale_data n)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0) :
    ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint
      scale_data where
  scale_strict :=
    Month9Month10ActualProofLengthGapFrontier.scale_strict_of_timeConstructibleBound_strict
      time_bound_strict exponent_ne_zero
  proof_length_gap :=
    actual_proof_length_gap
  proof_length_eq_scale := by
    intro n
    exact proof_length_eq_scale n

def threeCertificateDeliverablesOfTimeConstructibleBoundStrict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (actual_proof_length_gap :
      ComputableSearchGapCertificate
        (actualProofLengthMeasured scale_data))
    (proof_length_eq_scale :
      ∀ n : Nat,
        actualProofLengthMeasured scale_data n =
          scaleMeasured scale_data n)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0) :
    ConcretePAHilbertPowerBoundFinalThreeCertificateDeliverables
      scale_data :=
  (threeCertificateEndpointOfTimeConstructibleBoundStrict
      actual_proof_length_gap proof_length_eq_scale
      time_bound_strict exponent_ne_zero).toDeliverables

def threeCertificateHandoffOfTimeConstructibleBoundStrict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (actual_proof_length_gap :
      ComputableSearchGapCertificate
        (actualProofLengthMeasured scale_data))
    (proof_length_eq_scale :
      ∀ n : Nat,
        actualProofLengthMeasured scale_data n =
          scaleMeasured scale_data n)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0) :
    Month9Month10Month11ThreeCertificateHandoff scale_data where
  deliverables :=
    threeCertificateDeliverablesOfTimeConstructibleBoundStrict
      actual_proof_length_gap proof_length_eq_scale
      time_bound_strict exponent_ne_zero

theorem month9_month10_month11_timeConstructibleBoundStrict_handoff_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (actual_proof_length_gap :
      ComputableSearchGapCertificate
        (actualProofLengthMeasured scale_data))
    (proof_length_eq_scale :
      ∀ n : Nat,
        actualProofLengthMeasured scale_data n =
          scaleMeasured scale_data n)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0) :
    (threeCertificateHandoffOfTimeConstructibleBoundStrict
        actual_proof_length_gap proof_length_eq_scale
        time_bound_strict exponent_ne_zero).Audit ∧
      Nonempty
        (ConcretePAHilbertPowerBoundFinalThreeCertificateDeliverables
          scale_data) ∧
        Nonempty
          (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
            scale_data) ∧
          Nonempty
            InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  let h :=
    threeCertificateHandoffOfTimeConstructibleBoundStrict
      actual_proof_length_gap proof_length_eq_scale
      time_bound_strict exponent_ne_zero
  ⟨h.audit,
    ⟨h.deliverables⟩,
    ⟨h.computableSearchProfile⟩,
    ⟨h.noSmallCore⟩⟩

def threeCertificateHandoffOfScaleGapFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (frontier : Month9Month10ScaleGapFrontier scale_data) :
    Month9Month10Month11ThreeCertificateHandoff scale_data where
  deliverables :=
    ({
      scale_strict := frontier.scale_strict
      proof_length_gap := frontier.actual_proof_length_gap
      proof_length_eq_scale := frontier.proof_length_eq_scale
    } : ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint
      scale_data).toDeliverables

theorem month9_month10_month11_scale_gap_frontier_handoff_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (frontier : Month9Month10ScaleGapFrontier scale_data) :
    (threeCertificateHandoffOfScaleGapFrontier frontier).Audit ∧
      frontier.toActualProofLengthGapFrontier.Audit ∧
        Nonempty (ComputableSearchGapCertificate (scaleMeasured scale_data)) ∧
          Nonempty
            (ComputableSearchGapCertificate
              (actualProofLengthMeasured scale_data)) ∧
            Nonempty
              (ConcretePAHilbertPowerBoundFinalThreeCertificateDeliverables
                scale_data) ∧
              Nonempty
                (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
                  scale_data) ∧
                Nonempty
                  InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  let h := threeCertificateHandoffOfScaleGapFrontier frontier
  ⟨h.audit,
    frontier.toActualProofLengthGapFrontier.audit,
    ⟨frontier.scale_gap⟩,
    ⟨frontier.actual_proof_length_gap⟩,
    ⟨h.deliverables⟩,
    ⟨h.computableSearchProfile⟩,
    ⟨h.noSmallCore⟩⟩

def threeCertificateHandoffOfProofLengthScaleExactnessFrontier
    (exactness :
      Month9Month10ProofLengthScaleExactnessFrontier.{q})
    (scale_gap :
      ComputableSearchGapCertificate
        (scaleMeasured exactness.scale_data))
    (scale_strict :
      ∀ {a b : Nat}, a < b →
        exactness.scale_data.scale a < exactness.scale_data.scale b) :
    Month9Month10Month11ThreeCertificateHandoff
      exactness.scale_data :=
  threeCertificateHandoffOfScaleGapFrontier
    (exactness.toScaleGapFrontier scale_gap scale_strict)

theorem month9_month10_month11_proof_length_scale_exactness_handoff_closure
    (exactness :
      Month9Month10ProofLengthScaleExactnessFrontier.{q})
    (scale_gap :
      ComputableSearchGapCertificate
        (scaleMeasured exactness.scale_data))
    (scale_strict :
      ∀ {a b : Nat}, a < b →
        exactness.scale_data.scale a < exactness.scale_data.scale b) :
    (threeCertificateHandoffOfProofLengthScaleExactnessFrontier
        exactness scale_gap scale_strict).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (scaleMeasured exactness.scale_data)) ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured exactness.scale_data)) ∧
          Nonempty
            (ConcretePAHilbertPowerBoundFinalThreeCertificateDeliverables
              exactness.scale_data) ∧
            Nonempty
              (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
                exactness.scale_data) ∧
              Nonempty
                InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  let frontier := exactness.toScaleGapFrontier scale_gap scale_strict
  let h := threeCertificateHandoffOfScaleGapFrontier frontier
  ⟨h.audit,
    ⟨scale_gap⟩,
    ⟨frontier.actual_proof_length_gap⟩,
    ⟨h.deliverables⟩,
    ⟨h.computableSearchProfile⟩,
    ⟨h.noSmallCore⟩⟩

def threeCertificateHandoffOfProofLengthExactnessAndTimeBoundStrict
    (exactness :
      Month9Month10ProofLengthScaleExactnessFrontier.{q})
    (scale_gap :
      ComputableSearchGapCertificate
        (scaleMeasured exactness.scale_data))
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        exactness.scale_data.time_constructible_bound a <
          exactness.scale_data.time_constructible_bound b)
    (exponent_ne_zero : exactness.scale_data.exponent ≠ 0) :
    Month9Month10Month11ThreeCertificateHandoff
      exactness.scale_data :=
  threeCertificateHandoffOfProofLengthScaleExactnessFrontier
    exactness scale_gap
    (Month9Month10ActualProofLengthGapFrontier.scale_strict_of_timeConstructibleBound_strict
      time_bound_strict exponent_ne_zero)

theorem month9_month10_month11_proof_length_exactness_time_bound_handoff_closure
    (exactness :
      Month9Month10ProofLengthScaleExactnessFrontier.{q})
    (scale_gap :
      ComputableSearchGapCertificate
        (scaleMeasured exactness.scale_data))
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        exactness.scale_data.time_constructible_bound a <
          exactness.scale_data.time_constructible_bound b)
    (exponent_ne_zero : exactness.scale_data.exponent ≠ 0) :
    (threeCertificateHandoffOfProofLengthExactnessAndTimeBoundStrict
        exactness scale_gap time_bound_strict exponent_ne_zero).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (scaleMeasured exactness.scale_data)) ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured exactness.scale_data)) ∧
          Nonempty
            (ConcretePAHilbertPowerBoundFinalThreeCertificateDeliverables
              exactness.scale_data) ∧
            Nonempty
              (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
                exactness.scale_data) ∧
              Nonempty
                InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  month9_month10_month11_proof_length_scale_exactness_handoff_closure
    exactness scale_gap
    (Month9Month10ActualProofLengthGapFrontier.scale_strict_of_timeConstructibleBound_strict
      time_bound_strict exponent_ne_zero)

theorem month9_month10_month11_exact_proof_gap_handoff_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ExactProofGapHandoff scale_data) :
    h.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (fun n : Nat =>
            _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (scale_data.powerBoundRawCode n))) ∧
        (∀ {a b : Nat}, a < b →
          scale_data.time_constructible_bound a ^ scale_data.exponent <
            scale_data.time_constructible_bound b ^ scale_data.exponent) ∧
          (∀ n : Nat,
            _root_.proof_length _root_.ProofSystem.PA
                _root_.ProofLengthMeasure.symbolSize
                (scale_data.powerBoundRawCode n) =
              (scale_data.scale n : Real)) ∧
            Nonempty
              InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  ⟨h.audit,
    h.actualProofLengthGap_nonempty,
    h.timeConstructiblePower_strict,
    h.proof_length_eq_scale,
    h.noSmallCore_nonempty⟩

theorem month9_month10_month11_three_certificate_handoff_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    h.Audit ∧
      h.toProofLengthGapFrontier.Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured scale_data)) ∧
          (∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b) ∧
            (∀ n : Nat,
              _root_.proof_length _root_.ProofSystem.PA
                  _root_.ProofLengthMeasure.symbolSize
                  (scale_data.powerBoundRawCode n) =
                (scale_data.scale n : Real)) ∧
              Nonempty
                (InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
                  scale_data) ∧
                Nonempty
                  InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} :=
  ⟨h.audit,
    h.toProofLengthGapFrontier.audit,
    h.actualProofLengthGap_nonempty,
    h.scaleStrict,
    h.proof_length_eq_scale,
    ⟨h.computableSearchProfile⟩,
    ⟨h.noSmallCore⟩⟩

/-! ## Corrected Month 9-10 route checklist -/

/-- Project-level checklist for the corrected Month 9-10 route.  It records
that the old exact-scale three-certificate endpoint is blocked by the
polynomial scale audit, while the corrected no-small-core residual endpoint
still exposes a computed collision witness through both payload-spec adapters. -/
structure Month9Month10CorrectedNoSmallCoreProjectChecklist : Prop where
  oldExactScaleEndpointBlocked :
    ∀ {scale_data : InternalPudlakTheorem5ScaleData},
      ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint scale_data →
        False
  oldExactScaleDeliverablesBlocked :
    ∀ {scale_data : InternalPudlakTheorem5ScaleData},
      ConcretePAHilbertPowerBoundFinalThreeCertificateDeliverables
        scale_data →
        False
  oldExactScaleHandoffBlocked :
    ∀ {scale_data : InternalPudlakTheorem5ScaleData},
      Month9Month10Month11ThreeCertificateHandoff scale_data → False
  dualResidualFineAudit :
    ∀ h : Month9Month10DualPayloadSpecCalibratedEndpointInputs.{0},
      Month9Month10DualPayloadSpecResidualAdapter.PayloadSpecResidualFineAudit h
  splitResidualFineAudit :
    ∀ h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0},
      Month9Month10SplitPayloadSpecResidualAdapter.SplitPayloadSpecResidualFineAudit h
  splitComputedWitnessClosure :
    ∀ h : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0},
      Month9Month10SplitPayloadSpecResidualAdapter.ComputedWitnessFormula h ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False) ∧
          (Month9Month10SplitPayloadSpecResidualAdapter.residualEndpoint h
            |>.not_rational) =
            GenericRationalCollisionInputs.not_rational
              (Month9Month10SplitPayloadSpecResidualAdapter.residualEndpoint h
                |>.toProjectChecklist
                |>.toGenericCollisionInputs)
  splitEndpointNotRational :
    ∀ _ : Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0},
      ¬ _root_.is_rational _root_.euler_mascheroni

theorem month9_month10_corrected_no_small_core_project_checklist :
    Month9Month10CorrectedNoSmallCoreProjectChecklist where
  oldExactScaleEndpointBlocked :=
    fun endpoint =>
      no_final_three_certificate_endpoint_for_internal_scale endpoint
  oldExactScaleDeliverablesBlocked :=
    fun deliverables =>
      no_final_three_certificate_deliverables_for_internal_scale
        deliverables
  oldExactScaleHandoffBlocked :=
    fun h =>
      no_month9_month10_month11_three_certificate_handoff_for_internal_scale h
  dualResidualFineAudit :=
    fun h =>
      Month9Month10DualPayloadSpecResidualAdapter.payload_spec_residual_fine_audit h
  splitResidualFineAudit :=
    fun h =>
      Month9Month10SplitPayloadSpecResidualAdapter.split_payload_spec_residual_fine_audit h
  splitComputedWitnessClosure :=
    fun h =>
      Month9Month10SplitPayloadSpecResidualAdapter.computed_witness_closure h
  splitEndpointNotRational :=
    fun h =>
      Month9Month10NoSmallCoreConstantProjectionResidualEndpoint.not_rational
        (Month9Month10SplitPayloadSpecResidualAdapter.residualEndpoint h)

/-! ## Accepted-payload frontier for removing raw payload assumptions -/

/-- Corrected Month 9-10 route stated from accepted-code payload evidence.
This frontier keeps the public inputs on the checker/accepted-certificate side:
ordinary partial consistency is supplied as `PartialConsistencyAcceptedTruth`,
and strengthened consistency is supplied as
`StrengthenedPartialConsistencyAcceptedTruth`.  The raw payload specifications
are constructed internally only to reuse the existing checked endpoint. -/
structure Month9Month10AcceptedPayloadCorrectedRouteInputs :
    Type 1 where
  scale_data : InternalPudlakTheorem5ScaleData
  checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data
  enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker
  extractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checker enumeration
  length_calibration :
    InternalPudlakTheorem5CheckerFamilyLengthCalibration checker
  verifier : SondowProjectLocalReflectionGraftVerifier
  partial_accepted_truth : _root_.PartialConsistencyAcceptedTruth
  strengthened_accepted_truth :
    _root_.StrengthenedPartialConsistencyAcceptedTruth
  projection_principle : _root_.PAProofLengthProjectionPrinciple
  strengthened_to_partial_projection :
    _root_.StrengthenedToPartialConsistencyConstantProjection
  partial_to_graft_projection :
    _root_.PAConjunctionEliminationConstantCost
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace Month9Month10AcceptedPayloadCorrectedRouteInputs

def partialAcceptedCodeTruthCertificate
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    PartialConsistencyAcceptedCodeTruthCertificate where
  accepted_truth := h.partial_accepted_truth

def partialPayloadSpecCertificate
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    PartialConsistencyPayloadSpecCertificate :=
  h.partialAcceptedCodeTruthCertificate.toPayloadSpecCertificate

def strengthenedPayloadSpecCertificate
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    Month9Month10StrengthenedPayloadSpecCertificate :=
  Month9Month10StrengthenedPayloadSpecCertificate.ofAcceptedTruth
    h.strengthened_accepted_truth

def upperInputs
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    Month9Month10PayloadSpecUpperInputs where
  verifier := h.verifier
  payload_spec := h.partialPayloadSpecCertificate

def lowerInputs
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    Month9Month10StrengthenedPayloadLowerInputs where
  strengthened_spec := h.strengthenedPayloadSpecCertificate
  strengthened_to_partial_projection :=
    h.strengthened_to_partial_projection

def lowerSplit
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    Month9Month10StrengthenedPayloadProjectionSplitInputs :=
  Month9Month10StrengthenedPayloadProjectionSplitInputs.ofProjectionPrinciple
    h.lowerInputs h.projection_principle

def toSplitPayloadSpecCalibratedEndpointInputs
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0} where
  scale_data := h.scale_data
  checker := h.checker
  enumeration := h.enumeration
  extractor := h.extractor
  length_calibration := h.length_calibration
  lower_split := h.lowerSplit
  partial_to_graft_projection := h.partial_to_graft_projection
  computable_gap := h.computable_gap
  upper_inputs := h.upperInputs

abbrev ComputedWitnessFormula
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) : Prop :=
  Month9Month10SplitPayloadSpecResidualAdapter.ComputedWitnessFormula
    h.toSplitPayloadSpecCalibratedEndpointInputs

theorem computed_witness_formula
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    h.ComputedWitnessFormula :=
  Month9Month10SplitPayloadSpecResidualAdapter.computed_witness_formula
    h.toSplitPayloadSpecCalibratedEndpointInputs

theorem contradiction_at_computed_witness
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False :=
  Month9Month10SplitPayloadSpecResidualAdapter.contradiction_at_computed_witness
    h.toSplitPayloadSpecCalibratedEndpointInputs

theorem endpoint_not_rational
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  Month9Month10NoSmallCoreConstantProjectionResidualEndpoint.not_rational
    (Month9Month10SplitPayloadSpecResidualAdapter.residualEndpoint
      h.toSplitPayloadSpecCalibratedEndpointInputs)

theorem endpoint_not_rational_eq_generic_core
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    (Month9Month10SplitPayloadSpecResidualAdapter.residualEndpoint
        h.toSplitPayloadSpecCalibratedEndpointInputs
      |>.not_rational) =
      GenericRationalCollisionInputs.not_rational
        (Month9Month10SplitPayloadSpecResidualAdapter.residualEndpoint
          h.toSplitPayloadSpecCalibratedEndpointInputs
          |>.toProjectChecklist
          |>.toGenericCollisionInputs) :=
  Month9Month10SplitPayloadSpecResidualAdapter.endpoint_not_rational_eq_generic_core
    h.toSplitPayloadSpecCalibratedEndpointInputs

/-- Accepted-payload audit for the corrected route.  This is the interface
that the PA/Hilbert checker line should target next: produce the two accepted
truth packages and the existing projection/gap/checker certificates, then this
audit reconstructs the previous split residual endpoint. -/
structure Audit
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    Prop where
  partialAcceptedTruth :
    _root_.PartialConsistencyAcceptedTruth
  partialAcceptedCodeTruthCertificate :
    Nonempty PartialConsistencyAcceptedCodeTruthCertificate
  partialPayloadSpecCertificate :
    Nonempty PartialConsistencyPayloadSpecCertificate
  strengthenedAcceptedTruth :
    _root_.StrengthenedPartialConsistencyAcceptedTruth
  strengthenedPayloadSpecCertificate :
    Nonempty Month9Month10StrengthenedPayloadSpecCertificate
  splitEndpoint :
    Nonempty Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0}
  splitFineAudit :
    Month9Month10SplitPayloadSpecResidualAdapter.SplitPayloadSpecResidualFineAudit
      h.toSplitPayloadSpecCalibratedEndpointInputs
  correctedChecklist :
    Month9Month10CorrectedNoSmallCoreProjectChecklist
  computedWitnessFormula :
    h.ComputedWitnessFormula
  contradictionAtComputedWitness :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  endpointNotRationalEqGenericCore :
    (Month9Month10SplitPayloadSpecResidualAdapter.residualEndpoint
        h.toSplitPayloadSpecCalibratedEndpointInputs
      |>.not_rational) =
      GenericRationalCollisionInputs.not_rational
        (Month9Month10SplitPayloadSpecResidualAdapter.residualEndpoint
          h.toSplitPayloadSpecCalibratedEndpointInputs
          |>.toProjectChecklist
          |>.toGenericCollisionInputs)
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    h.Audit where
  partialAcceptedTruth := h.partial_accepted_truth
  partialAcceptedCodeTruthCertificate :=
    ⟨h.partialAcceptedCodeTruthCertificate⟩
  partialPayloadSpecCertificate :=
    ⟨h.partialPayloadSpecCertificate⟩
  strengthenedAcceptedTruth := h.strengthened_accepted_truth
  strengthenedPayloadSpecCertificate :=
    ⟨h.strengthenedPayloadSpecCertificate⟩
  splitEndpoint :=
    ⟨h.toSplitPayloadSpecCalibratedEndpointInputs⟩
  splitFineAudit :=
    Month9Month10SplitPayloadSpecResidualAdapter.split_payload_spec_residual_fine_audit
      h.toSplitPayloadSpecCalibratedEndpointInputs
  correctedChecklist :=
    month9_month10_corrected_no_small_core_project_checklist
  computedWitnessFormula := h.computed_witness_formula
  contradictionAtComputedWitness :=
    h.contradiction_at_computed_witness
  endpointNotRationalEqGenericCore :=
    h.endpoint_not_rational_eq_generic_core
  endpointNotRational := h.endpoint_not_rational

theorem closure
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    h.Audit ∧
      Nonempty PartialConsistencyAcceptedCodeTruthCertificate ∧
        Nonempty PartialConsistencyPayloadSpecCertificate ∧
          Nonempty Month9Month10StrengthenedPayloadSpecCertificate ∧
            Nonempty Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0} ∧
              h.ComputedWitnessFormula ∧
                (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                  False) ∧
                  ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨h.audit,
    ⟨h.partialAcceptedCodeTruthCertificate⟩,
    ⟨h.partialPayloadSpecCertificate⟩,
    ⟨h.strengthenedPayloadSpecCertificate⟩,
    ⟨h.toSplitPayloadSpecCalibratedEndpointInputs⟩,
    h.computed_witness_formula,
    h.contradiction_at_computed_witness,
    h.endpoint_not_rational⟩

end Month9Month10AcceptedPayloadCorrectedRouteInputs

theorem month9_month10_accepted_payload_corrected_route_closure
    (h : Month9Month10AcceptedPayloadCorrectedRouteInputs) :
    h.Audit ∧
      Nonempty PartialConsistencyAcceptedCodeTruthCertificate ∧
        Nonempty PartialConsistencyPayloadSpecCertificate ∧
          Nonempty Month9Month10StrengthenedPayloadSpecCertificate ∧
            Nonempty Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0} ∧
              h.ComputedWitnessFormula ∧
                (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                  False) ∧
                  ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.closure

/-- Exact footprint of the two remaining payload axioms in the corrected route.
The current root `accepted_certificate` predicate unfolds the ordinary and
strengthened finite-consistency families directly to the raw payload
predicates.  This checklist makes the replacement target precise: a later
payload-free checker layer must replace these two branches, not the collision
core. -/
structure Month9Month10PayloadAxiomFootprintChecklist : Prop where
  ordinaryAcceptedIffPayload :
    ∀ n : Nat,
      _root_.accepted_certificate (_root_.partialConsistencyCode n) ↔
        _root_.partial_consistency_payload n
  strengthenedAcceptedIffPayload :
    ∀ n : Nat,
      _root_.accepted_certificate
          (_root_.strengthenedPartialConsistencyCode n) ↔
        _root_.strengthened_partial_consistency_payload n
  ordinaryAcceptedTruthToPayloadTruth :
    _root_.PartialConsistencyAcceptedTruth →
      _root_.PartialConsistencyPayloadTruth
  ordinaryPayloadTruthToAcceptedTruth :
    _root_.PartialConsistencyPayloadTruth →
      _root_.PartialConsistencyAcceptedTruth
  strengthenedAcceptedTruthToPayloadTruth :
    _root_.StrengthenedPartialConsistencyAcceptedTruth →
      _root_.StrengthenedPartialConsistencyPayloadTruth
  strengthenedPayloadTruthToAcceptedTruth :
    _root_.StrengthenedPartialConsistencyPayloadTruth →
      _root_.StrengthenedPartialConsistencyAcceptedTruth
  acceptedPayloadCorrectedRouteClosure :
    ∀ h : Month9Month10AcceptedPayloadCorrectedRouteInputs,
      h.Audit ∧
        Nonempty PartialConsistencyAcceptedCodeTruthCertificate ∧
          Nonempty PartialConsistencyPayloadSpecCertificate ∧
            Nonempty Month9Month10StrengthenedPayloadSpecCertificate ∧
              Nonempty Month9Month10SplitPayloadSpecCalibratedEndpointInputs.{0} ∧
                h.ComputedWitnessFormula ∧
                  (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                    False) ∧
                    ¬ _root_.is_rational _root_.euler_mascheroni

theorem month9_month10_payload_axiom_footprint_checklist :
    Month9Month10PayloadAxiomFootprintChecklist where
  ordinaryAcceptedIffPayload :=
    _root_.accepted_certificate_partialConsistencyCode_iff
  strengthenedAcceptedIffPayload :=
    _root_.accepted_certificate_strengthenedPartialConsistencyCode_iff
  ordinaryAcceptedTruthToPayloadTruth :=
    _root_.PartialConsistencyAcceptedTruth.toPayloadTruth
  ordinaryPayloadTruthToAcceptedTruth :=
    _root_.PartialConsistencyPayloadTruth.toAcceptedTruth
  strengthenedAcceptedTruthToPayloadTruth :=
    _root_.StrengthenedPartialConsistencyAcceptedTruth.toPayloadTruth
  strengthenedPayloadTruthToAcceptedTruth :=
    _root_.StrengthenedPartialConsistencyPayloadTruth.toAcceptedTruth
  acceptedPayloadCorrectedRouteClosure :=
    month9_month10_accepted_payload_corrected_route_closure

/-! ## Payload-free checker acceptance frontier -/

/-- Checker-side accepted-code family with no reference to the root
`accepted_certificate` predicate.  This is the target interface for replacing
the two payload branches of `accepted_certificate` by a PA/Hilbert checker
realization. -/
structure Month9Month10PayloadFreeCheckerAcceptedFamily
    (checker : PAHilbertChecker)
    (family : Nat → _root_.FormulaCode) : Type where
  proofCode : Nat → Nat
  acceptedCode :
    ∀ n : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (family n) (proofCode n)

namespace Month9Month10PayloadFreeCheckerAcceptedFamily

structure Audit
    {checker : PAHilbertChecker}
    {family : Nat → _root_.FormulaCode}
    (h : Month9Month10PayloadFreeCheckerAcceptedFamily checker family) :
    Prop where
  proofCodeFunction :
    Nonempty (Nat → Nat)
  acceptedCode :
    ∀ n : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (family n) (h.proofCode n)

theorem audit
    {checker : PAHilbertChecker}
    {family : Nat → _root_.FormulaCode}
    (h : Month9Month10PayloadFreeCheckerAcceptedFamily checker family) :
    h.Audit where
  proofCodeFunction := ⟨h.proofCode⟩
  acceptedCode := h.acceptedCode

end Month9Month10PayloadFreeCheckerAcceptedFamily

/-- Payload-free accepted-code evidence for the two finite-consistency families
that Month 9-10 needs.  It is deliberately stated only in terms of
`PAHilbertAcceptedProofCodeForFormulaCode`, not the root accepted-certificate
predicate. -/
structure Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance :
    Type where
  checker : PAHilbertChecker
  ordinary :
    Month9Month10PayloadFreeCheckerAcceptedFamily
      checker _root_.partialConsistencyCode
  strengthened :
    Month9Month10PayloadFreeCheckerAcceptedFamily
      checker _root_.strengthenedPartialConsistencyCode

namespace Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance

structure Audit
    (h : Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance) :
    Prop where
  ordinaryAudit :
    h.ordinary.Audit
  strengthenedAudit :
    h.strengthened.Audit
  ordinaryAcceptedCode :
    ∀ n : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
        h.checker (_root_.partialConsistencyCode n)
        (h.ordinary.proofCode n)
  strengthenedAcceptedCode :
    ∀ n : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
        h.checker (_root_.strengthenedPartialConsistencyCode n)
        (h.strengthened.proofCode n)

theorem audit
    (h : Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance) :
    h.Audit where
  ordinaryAudit := h.ordinary.audit
  strengthenedAudit := h.strengthened.audit
  ordinaryAcceptedCode := h.ordinary.acceptedCode
  strengthenedAcceptedCode := h.strengthened.acceptedCode

/-- Axiom-clean closure for the checker-side accepted-code layer.  This theorem
does not mention the root `accepted_certificate`; it only records executable
PA/Hilbert accepted proof-code evidence for the ordinary and strengthened
finite-consistency families. -/
theorem axiom_clean_closure
    (h : Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance) :
    h.Audit ∧
      Nonempty
        (Month9Month10PayloadFreeCheckerAcceptedFamily
          h.checker _root_.partialConsistencyCode) ∧
        Nonempty
          (Month9Month10PayloadFreeCheckerAcceptedFamily
            h.checker _root_.strengthenedPartialConsistencyCode) ∧
          (∀ n : Nat,
            PAHilbertAcceptedProofCodeForFormulaCode
              h.checker (_root_.partialConsistencyCode n)
              (h.ordinary.proofCode n)) ∧
            (∀ n : Nat,
              PAHilbertAcceptedProofCodeForFormulaCode
                h.checker (_root_.strengthenedPartialConsistencyCode n)
                (h.strengthened.proofCode n)) :=
  ⟨h.audit,
    ⟨h.ordinary⟩,
    ⟨h.strengthened⟩,
    h.ordinary.acceptedCode,
    h.strengthened.acceptedCode⟩

end Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance

theorem month9_month10_payload_free_checker_acceptance_axiom_clean_closure
    (h : Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance) :
    h.Audit ∧
      Nonempty
        (Month9Month10PayloadFreeCheckerAcceptedFamily
          h.checker _root_.partialConsistencyCode) ∧
        Nonempty
          (Month9Month10PayloadFreeCheckerAcceptedFamily
            h.checker _root_.strengthenedPartialConsistencyCode) ∧
          (∀ n : Nat,
            PAHilbertAcceptedProofCodeForFormulaCode
              h.checker (_root_.partialConsistencyCode n)
              (h.ordinary.proofCode n)) ∧
            (∀ n : Nat,
              PAHilbertAcceptedProofCodeForFormulaCode
                h.checker (_root_.strengthenedPartialConsistencyCode n)
                (h.strengthened.proofCode n)) :=
  h.axiom_clean_closure

/-- The exact soundness bridge still needed to turn payload-free checker
acceptance into the existing root accepted-certificate truths.  Supplying this
bridge is strictly narrower than supplying raw payload truth: it only has to
show that accepted PA/Hilbert proof codes imply root accepted certificates for
the two standard families. -/
structure Month9Month10CheckerAcceptedRootBridge
    (h : Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance) :
    Prop where
  ordinarySound :
    ∀ n : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
          h.checker (_root_.partialConsistencyCode n)
          (h.ordinary.proofCode n) →
        _root_.accepted_certificate (_root_.partialConsistencyCode n)
  strengthenedSound :
    ∀ n : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
          h.checker (_root_.strengthenedPartialConsistencyCode n)
          (h.strengthened.proofCode n) →
        _root_.accepted_certificate
          (_root_.strengthenedPartialConsistencyCode n)

namespace Month9Month10CheckerAcceptedRootBridge

theorem ordinaryAcceptedTruth
    {h : Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (bridge : Month9Month10CheckerAcceptedRootBridge h) :
    _root_.PartialConsistencyAcceptedTruth where
  accepted_all := by
    intro n
    exact bridge.ordinarySound n (h.ordinary.acceptedCode n)

theorem strengthenedAcceptedTruth
    {h : Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (bridge : Month9Month10CheckerAcceptedRootBridge h) :
    _root_.StrengthenedPartialConsistencyAcceptedTruth where
  accepted_all := by
    intro n
    exact bridge.strengthenedSound n (h.strengthened.acceptedCode n)

end Month9Month10CheckerAcceptedRootBridge

/-- Payload-free checker frontier plus the minimal bridge to the root
accepted-certificate vocabulary.  Its closure gives the two accepted-truth
packages needed by the accepted-payload route without using the raw
accepted-to-payload conversions. -/
structure Month9Month10PayloadFreeCheckerAcceptanceFrontier : Type where
  checker_acceptance :
    Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance
  root_bridge :
    Month9Month10CheckerAcceptedRootBridge checker_acceptance

namespace Month9Month10PayloadFreeCheckerAcceptanceFrontier

theorem ordinaryAcceptedTruth
    (h : Month9Month10PayloadFreeCheckerAcceptanceFrontier) :
    _root_.PartialConsistencyAcceptedTruth :=
  h.root_bridge.ordinaryAcceptedTruth

theorem strengthenedAcceptedTruth
    (h : Month9Month10PayloadFreeCheckerAcceptanceFrontier) :
    _root_.StrengthenedPartialConsistencyAcceptedTruth :=
  h.root_bridge.strengthenedAcceptedTruth

structure Audit
    (h : Month9Month10PayloadFreeCheckerAcceptanceFrontier) :
    Prop where
  checkerAcceptanceAudit :
    h.checker_acceptance.Audit
  rootBridge :
    Month9Month10CheckerAcceptedRootBridge h.checker_acceptance
  ordinaryAcceptedTruth :
    _root_.PartialConsistencyAcceptedTruth
  strengthenedAcceptedTruth :
    _root_.StrengthenedPartialConsistencyAcceptedTruth
  ordinaryAcceptedAll :
    ∀ n : Nat,
      _root_.accepted_certificate (_root_.partialConsistencyCode n)
  strengthenedAcceptedAll :
    ∀ n : Nat,
      _root_.accepted_certificate
        (_root_.strengthenedPartialConsistencyCode n)

theorem audit
    (h : Month9Month10PayloadFreeCheckerAcceptanceFrontier) :
    h.Audit where
  checkerAcceptanceAudit := h.checker_acceptance.audit
  rootBridge := h.root_bridge
  ordinaryAcceptedTruth := h.ordinaryAcceptedTruth
  strengthenedAcceptedTruth := h.strengthenedAcceptedTruth
  ordinaryAcceptedAll := h.ordinaryAcceptedTruth.accepted_all
  strengthenedAcceptedAll := h.strengthenedAcceptedTruth.accepted_all

theorem closure
    (h : Month9Month10PayloadFreeCheckerAcceptanceFrontier) :
    h.Audit ∧
      _root_.PartialConsistencyAcceptedTruth ∧
        _root_.StrengthenedPartialConsistencyAcceptedTruth ∧
          (∀ n : Nat,
            _root_.accepted_certificate (_root_.partialConsistencyCode n)) ∧
            (∀ n : Nat,
              _root_.accepted_certificate
                (_root_.strengthenedPartialConsistencyCode n)) :=
  ⟨h.audit,
    h.ordinaryAcceptedTruth,
    h.strengthenedAcceptedTruth,
    h.ordinaryAcceptedTruth.accepted_all,
    h.strengthenedAcceptedTruth.accepted_all⟩

end Month9Month10PayloadFreeCheckerAcceptanceFrontier

theorem month9_month10_payload_free_checker_acceptance_frontier_closure
    (h : Month9Month10PayloadFreeCheckerAcceptanceFrontier) :
    h.Audit ∧
      _root_.PartialConsistencyAcceptedTruth ∧
        _root_.StrengthenedPartialConsistencyAcceptedTruth ∧
          (∀ n : Nat,
            _root_.accepted_certificate (_root_.partialConsistencyCode n)) ∧
            (∀ n : Nat,
              _root_.accepted_certificate
                (_root_.strengthenedPartialConsistencyCode n)) :=
  h.closure

/-! ## Direct upper-tail collision route -/

/-- Direct computable collision route from a project-gap certificate and an
explicit upper tail under rationality.  It deliberately bypasses
`Month9Month10ProjectCollisionChecklist`; that checklist is still useful for
constructing the upper tail from project-local Sondow data, but the collision
core itself only needs these two fields. -/
structure Month9Month10DirectUpperTailSearchCollisionRoute : Type where
  gap :
    ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox
  upper_under_rationality :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat,
          ∀ n : Nat, upperN ≤ n →
            sondowProjectLocalPudlakCollisionBox n ≤ U n

namespace Month9Month10DirectUpperTailSearchCollisionRoute

def toGenericCollisionInputs
    (h : Month9Month10DirectUpperTailSearchCollisionRoute) :
    GenericRationalCollisionInputs :=
  h.gap.toGenericRationalCollisionInputs h.upper_under_rationality

noncomputable def upperTailOfRationality
    (h : Month9Month10DirectUpperTailSearchCollisionRoute)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox :=
  h.gap.upperTailCertificateOfRationality
    h.upper_under_rationality hrat

noncomputable def computedWitnessOfRationality
    (h : Month9Month10DirectUpperTailSearchCollisionRoute)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      (h.upperTailOfRationality hrat).U
      sondowProjectLocalPudlakCollisionBox :=
  h.gap.collisionWitness (h.upperTailOfRationality hrat)

noncomputable def computedCollisionNOfRationality
    (h : Month9Month10DirectUpperTailSearchCollisionRoute)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  (h.computedWitnessOfRationality hrat).n

theorem computedCollisionN_eq_searchGapWitness
    (h : Month9Month10DirectUpperTailSearchCollisionRoute)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      (h.gap.gap_for_polynomial_upper
        (h.upperTailOfRationality hrat).U
        (h.upperTailOfRationality hrat).polynomial).witness
          (h.upperTailOfRationality hrat).upperN :=
  rfl

theorem computedCollisionN_ge_upperN
    (h : Month9Month10DirectUpperTailSearchCollisionRoute)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.upperTailOfRationality hrat).upperN ≤
      h.computedCollisionNOfRationality hrat :=
  (h.computedWitnessOfRationality hrat).n_ge_upper

theorem lower_at_computedCollisionN
    (h : Month9Month10DirectUpperTailSearchCollisionRoute)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.upperTailOfRationality hrat).U
        (h.computedCollisionNOfRationality hrat) <
      sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat) :=
  (h.computedWitnessOfRationality hrat).lower_at_n

theorem upper_at_computedCollisionN
    (h : Month9Month10DirectUpperTailSearchCollisionRoute)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    sondowProjectLocalPudlakCollisionBox
        (h.computedCollisionNOfRationality hrat) ≤
      (h.upperTailOfRationality hrat).U
        (h.computedCollisionNOfRationality hrat) :=
  (h.computedWitnessOfRationality hrat).upper_at_n

theorem computed_n_contradiction
    (h : Month9Month10DirectUpperTailSearchCollisionRoute)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.computedWitnessOfRationality hrat).contradiction

theorem not_rational
    (h : Month9Month10DirectUpperTailSearchCollisionRoute) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat => h.computed_n_contradiction hrat

theorem not_rational_eq_generic_core
    (h : Month9Month10DirectUpperTailSearchCollisionRoute) :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational h.toGenericCollisionInputs :=
  h.gap.not_rational_eq_generic_core h.upper_under_rationality

structure Audit
    (h : Month9Month10DirectUpperTailSearchCollisionRoute) : Prop where
  computableSearchGap :
    Nonempty
      (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox)
  genericInputs :
    Nonempty GenericRationalCollisionInputs
  computedWitnessFormula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        (h.gap.gap_for_polynomial_upper
          (h.upperTailOfRationality hrat).U
          (h.upperTailOfRationality hrat).polynomial).witness
            (h.upperTailOfRationality hrat).upperN
  computedNGeUpperN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (h.upperTailOfRationality hrat).upperN ≤
        h.computedCollisionNOfRationality hrat
  lowerAtComputedN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (h.upperTailOfRationality hrat).U
          (h.computedCollisionNOfRationality hrat) <
        sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat)
  upperAtComputedN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat) ≤
        (h.upperTailOfRationality hrat).U
          (h.computedCollisionNOfRationality hrat)
  contradictionAtComputedN :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  notRationalEqGenericCore :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational h.toGenericCollisionInputs
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    (h : Month9Month10DirectUpperTailSearchCollisionRoute) :
    h.Audit where
  computableSearchGap := ⟨h.gap⟩
  genericInputs := ⟨h.toGenericCollisionInputs⟩
  computedWitnessFormula := h.computedCollisionN_eq_searchGapWitness
  computedNGeUpperN := h.computedCollisionN_ge_upperN
  lowerAtComputedN := h.lower_at_computedCollisionN
  upperAtComputedN := h.upper_at_computedCollisionN
  contradictionAtComputedN := h.computed_n_contradiction
  notRationalEqGenericCore := h.not_rational_eq_generic_core
  endpointNotRational := h.not_rational

theorem closure
    (h : Month9Month10DirectUpperTailSearchCollisionRoute) :
    h.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
        Nonempty GenericRationalCollisionInputs ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            h.computedCollisionNOfRationality hrat =
              (h.gap.gap_for_polynomial_upper
                (h.upperTailOfRationality hrat).U
                (h.upperTailOfRationality hrat).polynomial).witness
                  (h.upperTailOfRationality hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              h.not_rational =
                GenericRationalCollisionInputs.not_rational
                  h.toGenericCollisionInputs :=
  ⟨h.audit,
    ⟨h.gap⟩,
    ⟨h.toGenericCollisionInputs⟩,
    h.computedCollisionN_eq_searchGapWitness,
    h.computed_n_contradiction,
    h.not_rational_eq_generic_core⟩

end Month9Month10DirectUpperTailSearchCollisionRoute

theorem month9_month10_direct_upper_tail_search_collision_closure
    (h : Month9Month10DirectUpperTailSearchCollisionRoute) :
    h.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
        Nonempty GenericRationalCollisionInputs ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            h.computedCollisionNOfRationality hrat =
              (h.gap.gap_for_polynomial_upper
                (h.upperTailOfRationality hrat).U
                (h.upperTailOfRationality hrat).polynomial).witness
                  (h.upperTailOfRationality hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              h.not_rational =
                GenericRationalCollisionInputs.not_rational
                  h.toGenericCollisionInputs :=
  h.closure

/-! ## Proof-length-free measured collision route -/

/-- Abstract upper provider for any measured box.  This is the proof-length-free
form of the Sondow-side input: under rationality, the selected measured
quantity has an eventual polynomial upper bound. -/
structure Month9Month10AbstractMeasuredUpperProvider
    (measured : Nat → Real) : Type where
  upper_under_rationality :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat,
          ∀ n : Nat, upperN ≤ n → measured n ≤ U n

namespace Month9Month10AbstractMeasuredUpperProvider

structure Audit
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredUpperProvider measured) : Prop where
  upperUnderRationality :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat,
          ∀ n : Nat, upperN ≤ n → measured n ≤ U n

theorem audit
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredUpperProvider measured) :
    h.Audit where
  upperUnderRationality := h.upper_under_rationality

theorem closure
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredUpperProvider measured) :
    h.Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :=
  ⟨h.audit, h.upper_under_rationality⟩

/-- Transport an eventual polynomial upper provider across pointwise equality of
measured functions. -/
def transportEq
    {measuredA measuredB : Nat → Real}
    (heq : ∀ n : Nat, measuredA n = measuredB n)
    (h : Month9Month10AbstractMeasuredUpperProvider measuredA) :
    Month9Month10AbstractMeasuredUpperProvider measuredB where
  upper_under_rationality := by
    intro hrat
    rcases h.upper_under_rationality hrat with ⟨U, hU, upperN, htail⟩
    refine ⟨U, hU, upperN, ?_⟩
    intro n hn
    simpa [heq n] using htail n hn

theorem transportEq_closure
    {measuredA measuredB : Nat → Real}
    (heq : ∀ n : Nat, measuredA n = measuredB n)
    (h : Month9Month10AbstractMeasuredUpperProvider measuredA) :
    (transportEq heq h).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n → measuredB n ≤ U n) :=
  (transportEq heq h).closure

/-- Transport an eventual polynomial upper provider along a pointwise
domination relation.  If `measuredB ≤ measuredA` and `measuredA` has an upper
tail, then `measuredB` has the same upper tail. -/
def transportLE
    {measuredA measuredB : Nat → Real}
    (hle : ∀ n : Nat, measuredB n ≤ measuredA n)
    (h : Month9Month10AbstractMeasuredUpperProvider measuredA) :
    Month9Month10AbstractMeasuredUpperProvider measuredB where
  upper_under_rationality := by
    intro hrat
    rcases h.upper_under_rationality hrat with ⟨U, hU, upperN, htail⟩
    refine ⟨U, hU, upperN, ?_⟩
    intro n hn
    exact le_trans (hle n) (htail n hn)

theorem transportLE_closure
    {measuredA measuredB : Nat → Real}
    (hle : ∀ n : Nat, measuredB n ≤ measuredA n)
    (h : Month9Month10AbstractMeasuredUpperProvider measuredA) :
    (transportLE hle h).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n → measuredB n ≤ U n) :=
  (transportLE hle h).closure

end Month9Month10AbstractMeasuredUpperProvider

/-- Explicit upper provider for any measured box.  This is the computable
version of `Month9Month10AbstractMeasuredUpperProvider`: under rationality it
returns the actual polynomial upper function and its cutoff as a
`PolynomialUpperTailCertificate`, rather than only an existential package. -/
structure Month9Month10ExplicitMeasuredUpperProvider
    (measured : Nat → Real) : Type where
  upperTailOfRationality :
    _root_.is_rational _root_.euler_mascheroni →
      PolynomialUpperTailCertificate measured

namespace Month9Month10ExplicitMeasuredUpperProvider

/-- Forget the explicit upper certificate to the legacy existential upper
provider interface.  This is a one-way compatibility bridge; the reverse
direction is exactly where `Classical.choose` would otherwise enter. -/
def toAbstract
    {measured : Nat → Real}
    (h : Month9Month10ExplicitMeasuredUpperProvider measured) :
    Month9Month10AbstractMeasuredUpperProvider measured where
  upper_under_rationality := by
    intro hrat
    let upper := h.upperTailOfRationality hrat
    exact ⟨upper.U, upper.polynomial, upper.upperN, upper.upper_after⟩

theorem toAbstract_closure
    {measured : Nat → Real}
    (h : Month9Month10ExplicitMeasuredUpperProvider measured) :
    (h.toAbstract).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n → measured n ≤ U n) :=
  h.toAbstract.closure

/-- Transport an explicit upper provider across pointwise equality of measured
functions, preserving the selected upper function and cutoff. -/
def transportEq
    {measuredA measuredB : Nat → Real}
    (heq : ∀ n : Nat, measuredA n = measuredB n)
    (h : Month9Month10ExplicitMeasuredUpperProvider measuredA) :
    Month9Month10ExplicitMeasuredUpperProvider measuredB where
  upperTailOfRationality := by
    intro hrat
    let upper := h.upperTailOfRationality hrat
    exact {
      U := upper.U
      polynomial := upper.polynomial
      upperN := upper.upperN
      upper_after := by
        intro n hn
        rw [← heq n]
        exact upper.upper_after n hn }

/-- Transport an explicit upper provider along a pointwise domination relation.
If `measuredB ≤ measuredA`, the same explicit upper certificate for
`measuredA` is an upper certificate for `measuredB`. -/
def transportLE
    {measuredA measuredB : Nat → Real}
    (hle : ∀ n : Nat, measuredB n ≤ measuredA n)
    (h : Month9Month10ExplicitMeasuredUpperProvider measuredA) :
    Month9Month10ExplicitMeasuredUpperProvider measuredB where
  upperTailOfRationality := by
    intro hrat
    let upper := h.upperTailOfRationality hrat
    exact {
      U := upper.U
      polynomial := upper.polynomial
      upperN := upper.upperN
      upper_after := by
        intro n hn
        exact le_trans (hle n) (upper.upper_after n hn) }

theorem transportEq_toAbstract
    {measuredA measuredB : Nat → Real}
    (heq : ∀ n : Nat, measuredA n = measuredB n)
    (h : Month9Month10ExplicitMeasuredUpperProvider measuredA) :
    (transportEq heq h).toAbstract =
      Month9Month10AbstractMeasuredUpperProvider.transportEq heq h.toAbstract :=
  rfl

theorem transportLE_toAbstract
    {measuredA measuredB : Nat → Real}
    (hle : ∀ n : Nat, measuredB n ≤ measuredA n)
    (h : Month9Month10ExplicitMeasuredUpperProvider measuredA) :
    (transportLE hle h).toAbstract =
      Month9Month10AbstractMeasuredUpperProvider.transportLE hle h.toAbstract :=
  rfl

end Month9Month10ExplicitMeasuredUpperProvider

/-- The Sondow/S²₁ collapse conclusion is exactly an abstract measured upper
provider for the project-local Pudlak collision box.  The accepted-certificate
side condition carried by the collapse is retained upstream; this provider only
exports the eventual polynomial upper inequality needed by the collision core. -/
def projectBoxUpperProviderOfS21Collapse
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10AbstractMeasuredUpperProvider
      sondowProjectLocalPudlakCollisionBox where
  upper_under_rationality := by
    intro hrat
    rcases project_upper hrat with ⟨U, hU, upperN, hupper⟩
    exact
      ⟨U, hU, upperN, fun n hn => by
        rcases hupper n hn with ⟨_haccepted, hle⟩
        exact hle⟩

theorem projectBoxUpperProviderOfS21Collapse_closure
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (projectBoxUpperProviderOfS21Collapse project_upper).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              sondowProjectLocalPudlakCollisionBox n ≤ U n) :=
  (projectBoxUpperProviderOfS21Collapse project_upper).closure

/-- Direct computable collision endpoint over an arbitrary measured box.  The
root project proof-length box is absent from this statement; it only reappears
through a later instantiation/transport bridge. -/
structure Month9Month10AbstractMeasuredDirectCollisionEndpoint
    (measured : Nat → Real) : Type where
  gap : ComputableSearchGapCertificate measured
  upper_provider : Month9Month10AbstractMeasuredUpperProvider measured

namespace Month9Month10AbstractMeasuredDirectCollisionEndpoint

def toGenericCollisionInputs
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured) :
    GenericRationalCollisionInputs :=
  h.gap.toGenericRationalCollisionInputs
    h.upper_provider.upper_under_rationality

noncomputable def upperTailOfRationality
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate measured :=
  h.gap.upperTailCertificateOfRationality
    h.upper_provider.upper_under_rationality hrat

noncomputable def computedWitnessOfRationality
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      (h.upperTailOfRationality hrat).U measured :=
  h.gap.collisionWitness (h.upperTailOfRationality hrat)

noncomputable def computedCollisionNOfRationality
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  (h.computedWitnessOfRationality hrat).n

theorem computedCollisionN_eq_searchGapWitness
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      (h.gap.gap_for_polynomial_upper
        (h.upperTailOfRationality hrat).U
        (h.upperTailOfRationality hrat).polynomial).witness
          (h.upperTailOfRationality hrat).upperN :=
  rfl

theorem computedCollisionN_ge_upperN
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.upperTailOfRationality hrat).upperN ≤
      h.computedCollisionNOfRationality hrat :=
  (h.computedWitnessOfRationality hrat).n_ge_upper

theorem lower_at_computedCollisionN
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.upperTailOfRationality hrat).U
        (h.computedCollisionNOfRationality hrat) <
      measured (h.computedCollisionNOfRationality hrat) :=
  (h.computedWitnessOfRationality hrat).lower_at_n

theorem upper_at_computedCollisionN
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    measured (h.computedCollisionNOfRationality hrat) ≤
      (h.upperTailOfRationality hrat).U
        (h.computedCollisionNOfRationality hrat) :=
  (h.computedWitnessOfRationality hrat).upper_at_n

theorem computed_n_contradiction
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.computedWitnessOfRationality hrat).contradiction

theorem not_rational
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat => h.computed_n_contradiction hrat

theorem not_rational_eq_generic_core
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured) :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational h.toGenericCollisionInputs :=
  h.gap.not_rational_eq_generic_core
    h.upper_provider.upper_under_rationality

structure Audit
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured) :
    Prop where
  upperProviderAudit : h.upper_provider.Audit
  computableSearchGap : Nonempty (ComputableSearchGapCertificate measured)
  genericInputs : Nonempty GenericRationalCollisionInputs
  computedWitnessFormula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        (h.gap.gap_for_polynomial_upper
          (h.upperTailOfRationality hrat).U
          (h.upperTailOfRationality hrat).polynomial).witness
            (h.upperTailOfRationality hrat).upperN
  computedNGeUpperN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (h.upperTailOfRationality hrat).upperN ≤
        h.computedCollisionNOfRationality hrat
  lowerAtComputedN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (h.upperTailOfRationality hrat).U
          (h.computedCollisionNOfRationality hrat) <
        measured (h.computedCollisionNOfRationality hrat)
  upperAtComputedN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      measured (h.computedCollisionNOfRationality hrat) ≤
        (h.upperTailOfRationality hrat).U
          (h.computedCollisionNOfRationality hrat)
  contradictionAtComputedN :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  notRationalEqGenericCore :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational h.toGenericCollisionInputs
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured) :
    h.Audit where
  upperProviderAudit := h.upper_provider.audit
  computableSearchGap := ⟨h.gap⟩
  genericInputs := ⟨h.toGenericCollisionInputs⟩
  computedWitnessFormula := h.computedCollisionN_eq_searchGapWitness
  computedNGeUpperN := h.computedCollisionN_ge_upperN
  lowerAtComputedN := h.lower_at_computedCollisionN
  upperAtComputedN := h.upper_at_computedCollisionN
  contradictionAtComputedN := h.computed_n_contradiction
  notRationalEqGenericCore := h.not_rational_eq_generic_core
  endpointNotRational := h.not_rational

theorem closure
    {measured : Nat → Real}
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured) :
    h.Audit ∧
      h.upper_provider.Audit ∧
        Nonempty (ComputableSearchGapCertificate measured) ∧
          Nonempty GenericRationalCollisionInputs ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              h.computedCollisionNOfRationality hrat =
                (h.gap.gap_for_polynomial_upper
                  (h.upperTailOfRationality hrat).U
                  (h.upperTailOfRationality hrat).polynomial).witness
                    (h.upperTailOfRationality hrat).upperN) ∧
              (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                False) ∧
                h.not_rational =
                  GenericRationalCollisionInputs.not_rational
                    h.toGenericCollisionInputs :=
  ⟨h.audit,
    h.upper_provider.audit,
    ⟨h.gap⟩,
    ⟨h.toGenericCollisionInputs⟩,
    h.computedCollisionN_eq_searchGapWitness,
    h.computed_n_contradiction,
    h.not_rational_eq_generic_core⟩

end Month9Month10AbstractMeasuredDirectCollisionEndpoint

theorem month9_month10_abstract_measured_direct_collision_closure
    (measured : Nat → Real)
    (h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured) :
    h.Audit ∧
      h.upper_provider.Audit ∧
        Nonempty (ComputableSearchGapCertificate measured) ∧
          Nonempty GenericRationalCollisionInputs ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              h.computedCollisionNOfRationality hrat =
                (h.gap.gap_for_polynomial_upper
                  (h.upperTailOfRationality hrat).U
                  (h.upperTailOfRationality hrat).polynomial).witness
                    (h.upperTailOfRationality hrat).upperN) ∧
              (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                False) ∧
                h.not_rational =
                  GenericRationalCollisionInputs.not_rational
                    h.toGenericCollisionInputs :=
  h.closure

/-- Minimal audit checklist for the proof-length-free collision kernel.  This
is the layer a checker-side measured box can instantiate before any transport
back to the root project proof-length box is attempted. -/
structure Month9Month10ProofLengthFreeMeasuredCollisionKernelChecklist :
    Prop where
  upperProviderClosure :
    ∀ measured : Nat → Real,
      ∀ h : Month9Month10AbstractMeasuredUpperProvider measured,
        h.Audit ∧
          (_root_.is_rational _root_.euler_mascheroni →
            ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
              ∃ upperN : Nat,
                ∀ n : Nat, upperN ≤ n → measured n ≤ U n)
  upperProviderEqTransport :
    ∀ measuredA measuredB : Nat → Real,
      ∀ heq : ∀ n : Nat, measuredA n = measuredB n,
        ∀ h : Month9Month10AbstractMeasuredUpperProvider measuredA,
          (Month9Month10AbstractMeasuredUpperProvider.transportEq
            heq h).Audit ∧
            (_root_.is_rational _root_.euler_mascheroni →
              ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
                ∃ upperN : Nat,
                  ∀ n : Nat, upperN ≤ n → measuredB n ≤ U n)
  upperProviderLETransport :
    ∀ measuredA measuredB : Nat → Real,
      ∀ hle : ∀ n : Nat, measuredB n ≤ measuredA n,
        ∀ h : Month9Month10AbstractMeasuredUpperProvider measuredA,
          (Month9Month10AbstractMeasuredUpperProvider.transportLE
            hle h).Audit ∧
            (_root_.is_rational _root_.euler_mascheroni →
              ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
                ∃ upperN : Nat,
                  ∀ n : Nat, upperN ≤ n → measuredB n ≤ U n)
  directCollisionClosure :
    ∀ measured : Nat → Real,
      ∀ h : Month9Month10AbstractMeasuredDirectCollisionEndpoint measured,
        h.Audit ∧
          h.upper_provider.Audit ∧
            Nonempty (ComputableSearchGapCertificate measured) ∧
              Nonempty GenericRationalCollisionInputs ∧
                (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                  h.computedCollisionNOfRationality hrat =
                    (h.gap.gap_for_polynomial_upper
                      (h.upperTailOfRationality hrat).U
                      (h.upperTailOfRationality hrat).polynomial).witness
                        (h.upperTailOfRationality hrat).upperN) ∧
                  (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                    False) ∧
                    h.not_rational =
                      GenericRationalCollisionInputs.not_rational
                        h.toGenericCollisionInputs

theorem month9_month10_proof_length_free_measured_collision_kernel_checklist :
    Month9Month10ProofLengthFreeMeasuredCollisionKernelChecklist where
  upperProviderClosure := by
    intro measured h
    exact h.closure
  upperProviderEqTransport := by
    intro measuredA measuredB heq h
    exact
      Month9Month10AbstractMeasuredUpperProvider.transportEq_closure
        heq h
  upperProviderLETransport := by
    intro measuredA measuredB hle h
    exact
      Month9Month10AbstractMeasuredUpperProvider.transportLE_closure
        hle h
  directCollisionClosure := by
    intro measured h
    exact month9_month10_abstract_measured_direct_collision_closure measured h

/-! ## Checker-side measured route before proof-length calibration -/

/-- The checker-side measured box for a theorem-5 power-bound raw family:
the minimum accepted proof-code size computed by the supplied checker
semantics.  This is the concrete measured object immediately before it is
calibrated to root `proof_length`. -/
noncomputable def month9_month10_checkedProofCodeMeasured
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Nat → Real :=
  fun n =>
    (sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ :
      Real)

theorem month9_month10_checkedProofCodeMeasured_eq_minProofCodeSize
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (n : Nat) :
    month9_month10_checkedProofCodeMeasured scale_data sem n =
      (sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ :
        Real) :=
  rfl

/-- Pure checker-side extraction of a computable gap for the measured function
`minProofCodeSize`.  This kernel uses only the finite-search exclusion
certificate, before any PA `proof_length` calibration is consulted. -/
def month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search) :
    ComputableSearchGapCertificate
      (month9_month10_checkedProofCodeMeasured scale_data sem) where
  gap_for_polynomial_upper := by
    intro U hU
    exact {
      witness := fun N => cert.witness U hU N
      witness_ge := fun N => cert.witness_ge U hU N
      strict_at_witness := by
        intro N
        have hgt := cert.minProofCodeSize_gt_at_witness U hU N
        simpa [month9_month10_checkedProofCodeMeasured] using hgt
    }

theorem month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
      cert |>.gap_for_polynomial_upper U hU).witness N) =
      cert.witness U hU N :=
  rfl

/-- Proof-length-free checklist for the checked-gap kernel alone.  It deliberately
does not mention `actualProofLengthMeasured`; the only measured object here is
the checker-computed `minProofCodeSize`. -/
structure Month9Month10ProofLengthFreeCheckedGapKernelChecklist : Prop where
  checkedGapClosure :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ sem :
        _root_.ProofCodeSemantics.{0}
          (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
        ∀ search : InternalPudlakTheorem5SmallCodeSearch scale_data sem,
          ∀ _cert :
            InternalPudlakTheorem5ComputableFiniteSearchExclusion
              scale_data sem search,
            Nonempty
              (ComputableSearchGapCertificate
                (month9_month10_checkedProofCodeMeasured scale_data sem))
  checkedGapWitnessEq :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ sem :
        _root_.ProofCodeSemantics.{0}
          (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
        ∀ search : InternalPudlakTheorem5SmallCodeSearch scale_data sem,
          ∀ cert :
            InternalPudlakTheorem5ComputableFiniteSearchExclusion
              scale_data sem search,
            ∀ U : Nat → Real,
              ∀ hU : _root_.is_polynomial_bound U,
                ∀ N : Nat,
                  ((month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
                    cert |>.gap_for_polynomial_upper U hU).witness N) =
                    cert.witness U hU N

theorem month9_month10_proof_length_free_checked_gap_kernel_checklist :
    Month9Month10ProofLengthFreeCheckedGapKernelChecklist where
  checkedGapClosure := by
    intro scale_data sem search cert
    exact
      ⟨month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
        cert⟩
  checkedGapWitnessEq := by
    intro scale_data sem search cert U hU N
    exact
      month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion_witness_eq
        cert U hU N

/-! ## Proof-length-free generated checked gap -/

/-- Minimal proof-length-free source for the checked lower gap.  It contains only
the theorem-5 measured family, the finite search space, and the computable
finite-search exclusion certificate.  In particular, it does not mention root
`proof_length` or the heavier checker exactness core. -/
structure PAHilbertProofLengthFreeLowerGapSource : Type 1 where
  scale_data : InternalPudlakTheorem5ScaleData
  proof_code_semantics :
    _root_.ProofCodeSemantics.{0}
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
  small_code_search :
    InternalPudlakTheorem5SmallCodeSearch
      scale_data proof_code_semantics
  computable_search_exclusion :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      scale_data proof_code_semantics small_code_search

namespace PAHilbertProofLengthFreeLowerGapSource

def measured (source : PAHilbertProofLengthFreeLowerGapSource) :
    Nat → Real :=
  month9_month10_checkedProofCodeMeasured
    source.scale_data source.proof_code_semantics

/-- Checked measured gap generated directly from the proof-length-free finite
search exclusion certificate. -/
def checkedGap (source : PAHilbertProofLengthFreeLowerGapSource) :
    ComputableSearchGapCertificate
      source.measured :=
  month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
    source.computable_search_exclusion

theorem checkedGap_witness_eq
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((source.checkedGap
      |>.gap_for_polynomial_upper U hU).witness N) =
      source.computable_search_exclusion.witness U hU N :=
  rfl

theorem checkedGap_witness_ge
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    N ≤
      ((source.checkedGap
        |>.gap_for_polynomial_upper U hU).witness N) :=
  (source.checkedGap
    |>.gap_for_polynomial_upper U hU).witness_ge N

theorem checkedGap_strict_at_cert_witness
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    U (source.computable_search_exclusion.witness U hU N) <
      source.measured
        (source.computable_search_exclusion.witness U hU N) := by
  simpa [month9_month10_checkedProofCodeMeasured,
    PAHilbertProofLengthFreeLowerGapSource.measured]
    using
      source.computable_search_exclusion.minProofCodeSize_gt_at_witness
        U hU N

theorem closure
    (source : PAHilbertProofLengthFreeLowerGapSource) :
    Nonempty (ComputableSearchGapCertificate source.measured) ∧
      (∀ U : Nat → Real,
        ∀ hU : _root_.is_polynomial_bound U,
          ∀ N : Nat,
            ((source.checkedGap
              |>.gap_for_polynomial_upper U hU).witness N) =
              source.computable_search_exclusion.witness U hU N) ∧
        (∀ U : Nat → Real,
          ∀ hU : _root_.is_polynomial_bound U,
            ∀ N : Nat,
              U (source.computable_search_exclusion.witness U hU N) <
                source.measured
                  (source.computable_search_exclusion.witness U hU N)) :=
  ⟨⟨source.checkedGap⟩,
    source.checkedGap_witness_eq,
    source.checkedGap_strict_at_cert_witness⟩

end PAHilbertProofLengthFreeLowerGapSource

/-- The checker computable-search profile is exactly the proof-length-free lower
gap source needed by the checked collision kernel. -/
def lowerGapSourceOfCheckerComputableSearchProfile
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) :
    PAHilbertProofLengthFreeLowerGapSource where
  scale_data := scale_data
  proof_code_semantics := profile.proof_code_semantics
  small_code_search := profile.small_code_search
  computable_search_exclusion := profile.computable_search_exclusion

theorem lowerGapSourceOfCheckerComputableSearchProfile_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((lowerGapSourceOfCheckerComputableSearchProfile profile).checkedGap
      |>.gap_for_polynomial_upper U hU).witness N) =
      profile.computable_search_exclusion.witness U hU N :=
  rfl

theorem lowerGapSourceOfCheckerComputableSearchProfile_strict_at_profile_witness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    U (profile.computable_search_exclusion.witness U hU N) <
      month9_month10_checkedProofCodeMeasured
        scale_data profile.proof_code_semantics
        (profile.computable_search_exclusion.witness U hU N) :=
  (lowerGapSourceOfCheckerComputableSearchProfile profile)
    |>.checkedGap_strict_at_cert_witness U hU N

/-! ## Project-length replacement for the checked measured route -/

/-- The theorem-5 power-bound family measured by the concrete
`ProofCodeSemantics.projectLength` replacement for root `proof_length`.

The fallback is present because `projectLength` is a total formula-code
semantics.  It is definitionally irrelevant on the theorem-5 raw family, where
`powerBoundRawCode n` is tagged as relevant by construction. -/
noncomputable def month9_month10_checkerProjectLengthMeasured
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (fallback : _root_.FormulaCode → Nat) :
    Nat → Real :=
  fun n =>
    sem.projectLength fallback (scale_data.powerBoundRawCode n)

/-- On the theorem-5 power-bound raw family, the checker-defined project length
is exactly the checked minimum proof-code size already used by the
proof-length-free kernel. -/
theorem month9_month10_checkerProjectLengthMeasured_eq_checkedProofCodeMeasured
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (fallback : _root_.FormulaCode → Nat) (n : Nat) :
    month9_month10_checkerProjectLengthMeasured scale_data sem fallback n =
      month9_month10_checkedProofCodeMeasured scale_data sem n := by
  rw [month9_month10_checkerProjectLengthMeasured,
    _root_.ProofCodeSemantics.projectLength_eq_minProofCodeSize]
  rfl

/-- Transport a checked computable gap certificate to the
`ProofCodeSemantics.projectLength` replacement route.  This is the local bridge
needed before any root `proof_length` calibration is consulted. -/
def month9_month10_checkerProjectLengthGapOfCheckedGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (fallback : _root_.FormulaCode → Nat)
    (gap :
      ComputableSearchGapCertificate
        (month9_month10_checkedProofCodeMeasured scale_data sem)) :
    ComputableSearchGapCertificate
      (month9_month10_checkerProjectLengthMeasured scale_data sem fallback) :=
  transportComputableSearchGap
    (fun n =>
      (month9_month10_checkerProjectLengthMeasured_eq_checkedProofCodeMeasured
        scale_data sem fallback n).symm)
    gap

theorem month9_month10_checkerProjectLengthGapOfCheckedGap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (fallback : _root_.FormulaCode → Nat)
    (gap :
      ComputableSearchGapCertificate
        (month9_month10_checkedProofCodeMeasured scale_data sem))
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((month9_month10_checkerProjectLengthGapOfCheckedGap fallback gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      (gap.gap_for_polynomial_upper U hU).witness N :=
  rfl

/-- Audit checklist for replacing the checked measured route by the concrete
checker project-length semantics on exactly the theorem-5 raw-code family. -/
structure Month9Month10CheckerProjectLengthReplacementChecklist : Prop where
  projectLengthEqChecked :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ sem :
        _root_.ProofCodeSemantics.{0}
          (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
        ∀ fallback : _root_.FormulaCode → Nat,
          ∀ n : Nat,
            month9_month10_checkerProjectLengthMeasured
                scale_data sem fallback n =
              month9_month10_checkedProofCodeMeasured scale_data sem n
  checkedGapTransportsToProjectLength :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ sem :
        _root_.ProofCodeSemantics.{0}
          (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
        ∀ fallback : _root_.FormulaCode → Nat,
          ∀ gap : ComputableSearchGapCertificate
            (month9_month10_checkedProofCodeMeasured scale_data sem),
            Nonempty
              { projectGap : ComputableSearchGapCertificate
                  (month9_month10_checkerProjectLengthMeasured
                    scale_data sem fallback) //
                ∀ U : Nat → Real,
                  ∀ hU : _root_.is_polynomial_bound U,
                    ∀ N : Nat,
                      (projectGap.gap_for_polynomial_upper U hU).witness N =
                        (gap.gap_for_polynomial_upper U hU).witness N }

theorem month9_month10_checker_project_length_replacement_checklist :
    Month9Month10CheckerProjectLengthReplacementChecklist where
  projectLengthEqChecked := by
    intro scale_data sem fallback n
    exact
      month9_month10_checkerProjectLengthMeasured_eq_checkedProofCodeMeasured
        scale_data sem fallback n
  checkedGapTransportsToProjectLength := by
    intro scale_data sem fallback gap
    exact
      ⟨⟨month9_month10_checkerProjectLengthGapOfCheckedGap fallback gap, by
        intro U hU N
        exact
          month9_month10_checkerProjectLengthGapOfCheckedGap_witness_eq
            fallback gap U hU N⟩⟩

/-- Checked-measured direct endpoint.  It is still proof-length-free: it only
knows the checker minimum, a computable search gap for that measured function,
and a rationality upper tail for that same measured function. -/
structure Month9Month10CheckedMeasuredDirectCollisionEndpoint
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 2 where
  sem :
    _root_.ProofCodeSemantics.{0}
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
  gap :
    ComputableSearchGapCertificate
      (month9_month10_checkedProofCodeMeasured scale_data sem)
  upper_provider :
    Month9Month10AbstractMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured scale_data sem)

namespace Month9Month10CheckedMeasuredDirectCollisionEndpoint

def toAbstractMeasuredEndpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedMeasuredDirectCollisionEndpoint scale_data) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (month9_month10_checkedProofCodeMeasured scale_data h.sem) where
  gap := h.gap
  upper_provider := h.upper_provider

noncomputable def computedCollisionNOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedMeasuredDirectCollisionEndpoint scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  h.toAbstractMeasuredEndpoint.computedCollisionNOfRationality hrat

theorem computedCollisionN_eq_searchGapWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedMeasuredDirectCollisionEndpoint scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      (h.gap.gap_for_polynomial_upper
        (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
          (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN :=
  h.toAbstractMeasuredEndpoint.computedCollisionN_eq_searchGapWitness hrat

theorem computed_n_contradiction
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedMeasuredDirectCollisionEndpoint scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.toAbstractMeasuredEndpoint.computed_n_contradiction hrat

theorem not_rational
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedMeasuredDirectCollisionEndpoint scale_data) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toAbstractMeasuredEndpoint.not_rational

theorem not_rational_eq_generic_core
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedMeasuredDirectCollisionEndpoint scale_data) :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational
        h.toAbstractMeasuredEndpoint.toGenericCollisionInputs :=
  h.toAbstractMeasuredEndpoint.not_rational_eq_generic_core

structure Audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedMeasuredDirectCollisionEndpoint scale_data) :
    Prop where
  abstractMeasuredAudit : h.toAbstractMeasuredEndpoint.Audit
  checkedMeasuredFormula :
    ∀ n : Nat,
      month9_month10_checkedProofCodeMeasured scale_data h.sem n =
        (h.sem.minProofCodeSize (scale_data.powerBoundRawCode n)
          ⟨n, rfl⟩ : Real)
  computedWitnessFormula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        (h.gap.gap_for_polynomial_upper
          (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
          (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
            (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN
  contradictionAtComputedN :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  notRationalEqGenericCore :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational
        h.toAbstractMeasuredEndpoint.toGenericCollisionInputs
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedMeasuredDirectCollisionEndpoint scale_data) :
    h.Audit where
  abstractMeasuredAudit := h.toAbstractMeasuredEndpoint.audit
  checkedMeasuredFormula :=
    month9_month10_checkedProofCodeMeasured_eq_minProofCodeSize
      scale_data h.sem
  computedWitnessFormula := h.computedCollisionN_eq_searchGapWitness
  contradictionAtComputedN := h.computed_n_contradiction
  notRationalEqGenericCore := h.not_rational_eq_generic_core
  endpointNotRational := h.not_rational

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedMeasuredDirectCollisionEndpoint scale_data) :
    h.Audit ∧
      h.toAbstractMeasuredEndpoint.Audit ∧
        (∀ n : Nat,
          month9_month10_checkedProofCodeMeasured scale_data h.sem n =
            (h.sem.minProofCodeSize (scale_data.powerBoundRawCode n)
              ⟨n, rfl⟩ : Real)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            h.computedCollisionNOfRationality hrat =
              (h.gap.gap_for_polynomial_upper
                (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
                  (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨h.audit,
    h.toAbstractMeasuredEndpoint.audit,
    month9_month10_checkedProofCodeMeasured_eq_minProofCodeSize
      scale_data h.sem,
    h.computedCollisionN_eq_searchGapWitness,
    h.computed_n_contradiction,
    h.not_rational⟩

end Month9Month10CheckedMeasuredDirectCollisionEndpoint

theorem month9_month10_checked_measured_direct_collision_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedMeasuredDirectCollisionEndpoint scale_data) :
    h.Audit ∧
      h.toAbstractMeasuredEndpoint.Audit ∧
        (∀ n : Nat,
          month9_month10_checkedProofCodeMeasured scale_data h.sem n =
            (h.sem.minProofCodeSize (scale_data.powerBoundRawCode n)
              ⟨n, rfl⟩ : Real)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            h.computedCollisionNOfRationality hrat =
              (h.gap.gap_for_polynomial_upper
                (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
                  (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.closure

/-- Checker-search collision endpoint: the lower side is not an arbitrary checked
gap anymore, but the computable finite-search exclusion certificate itself. -/
structure Month9Month10CheckedSearchCollisionEndpoint
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 2 where
  sem :
    _root_.ProofCodeSemantics.{0}
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
  search : InternalPudlakTheorem5SmallCodeSearch scale_data sem
  cert :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      scale_data sem search
  upper_provider :
    Month9Month10AbstractMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured scale_data sem)

namespace Month9Month10CheckedSearchCollisionEndpoint

def gap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedSearchCollisionEndpoint scale_data) :
    ComputableSearchGapCertificate
      (month9_month10_checkedProofCodeMeasured scale_data h.sem) :=
  month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion h.cert

def toDirectEndpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedSearchCollisionEndpoint scale_data) :
    Month9Month10CheckedMeasuredDirectCollisionEndpoint scale_data where
  sem := h.sem
  gap := h.gap
  upper_provider := h.upper_provider

noncomputable def computedCollisionNOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedSearchCollisionEndpoint scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  h.toDirectEndpoint.computedCollisionNOfRationality hrat

theorem computedCollisionN_eq_certWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedSearchCollisionEndpoint scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      h.cert.witness
        (h.toDirectEndpoint.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).U
        (h.toDirectEndpoint.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).polynomial
        (h.toDirectEndpoint.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).upperN := by
  calc
    h.computedCollisionNOfRationality hrat =
        (h.gap.gap_for_polynomial_upper
          (h.toDirectEndpoint.toAbstractMeasuredEndpoint
            |>.upperTailOfRationality hrat).U
          (h.toDirectEndpoint.toAbstractMeasuredEndpoint
            |>.upperTailOfRationality hrat).polynomial).witness
            (h.toDirectEndpoint.toAbstractMeasuredEndpoint
              |>.upperTailOfRationality hrat).upperN :=
      h.toDirectEndpoint.computedCollisionN_eq_searchGapWitness hrat
    _ = h.cert.witness
        (h.toDirectEndpoint.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).U
        (h.toDirectEndpoint.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).polynomial
        (h.toDirectEndpoint.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).upperN :=
      month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion_witness_eq
        h.cert
        (h.toDirectEndpoint.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).U
        (h.toDirectEndpoint.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).polynomial
        (h.toDirectEndpoint.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).upperN

theorem computed_n_contradiction
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedSearchCollisionEndpoint scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.toDirectEndpoint.computed_n_contradiction hrat

theorem not_rational
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedSearchCollisionEndpoint scale_data) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toDirectEndpoint.not_rational

theorem not_rational_eq_generic_core
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedSearchCollisionEndpoint scale_data) :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational
        h.toDirectEndpoint.toAbstractMeasuredEndpoint.toGenericCollisionInputs :=
  h.toDirectEndpoint.not_rational_eq_generic_core

structure Audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedSearchCollisionEndpoint scale_data) :
    Prop where
  directEndpointAudit : h.toDirectEndpoint.Audit
  checkedGapKernel :
    Nonempty
      (ComputableSearchGapCertificate
        (month9_month10_checkedProofCodeMeasured scale_data h.sem))
  computedWitnessFormula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        h.cert.witness
          (h.toDirectEndpoint.toAbstractMeasuredEndpoint
            |>.upperTailOfRationality hrat).U
          (h.toDirectEndpoint.toAbstractMeasuredEndpoint
            |>.upperTailOfRationality hrat).polynomial
          (h.toDirectEndpoint.toAbstractMeasuredEndpoint
            |>.upperTailOfRationality hrat).upperN
  contradictionAtComputedN :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  notRationalEqGenericCore :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational
        h.toDirectEndpoint.toAbstractMeasuredEndpoint.toGenericCollisionInputs
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedSearchCollisionEndpoint scale_data) :
    h.Audit where
  directEndpointAudit := h.toDirectEndpoint.audit
  checkedGapKernel := ⟨h.gap⟩
  computedWitnessFormula := h.computedCollisionN_eq_certWitness
  contradictionAtComputedN := h.computed_n_contradiction
  notRationalEqGenericCore := h.not_rational_eq_generic_core
  endpointNotRational := h.not_rational

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedSearchCollisionEndpoint scale_data) :
    h.Audit ∧
      h.toDirectEndpoint.Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (month9_month10_checkedProofCodeMeasured scale_data h.sem)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            h.computedCollisionNOfRationality hrat =
              h.cert.witness
                (h.toDirectEndpoint.toAbstractMeasuredEndpoint
                  |>.upperTailOfRationality hrat).U
                (h.toDirectEndpoint.toAbstractMeasuredEndpoint
                  |>.upperTailOfRationality hrat).polynomial
                (h.toDirectEndpoint.toAbstractMeasuredEndpoint
                  |>.upperTailOfRationality hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨h.audit,
    h.toDirectEndpoint.audit,
    ⟨h.gap⟩,
    h.computedCollisionN_eq_certWitness,
    h.computed_n_contradiction,
    h.not_rational⟩

/-- Full finite-search trace for the checked-search endpoint.  The computed
collision index is the same index carried by the computable finite-search
certificate, and the endpoint exposes the cutoff, candidate rejection, no-small
proof-code inequality, checked minimum-size lower bound, and final checked
upper/lower contradiction at that index. -/
theorem full_lower_search_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10CheckedSearchCollisionEndpoint scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let upper := h.toDirectEndpoint.toAbstractMeasuredEndpoint
      |>.upperTailOfRationality hrat
    let w :=
      h.cert.computedLowerSearchWitness
        upper.U upper.polynomial upper.upperN
    let n := h.computedCollisionNOfRationality hrat
    n = w.n ∧
      w.n = h.cert.witness upper.U upper.polynomial upper.upperN ∧
      w.K = h.cert.cutoff upper.U upper.polynomial upper.upperN ∧
      upper.upperN ≤ w.n ∧
      upper.U w.n < (w.K : Real) ∧
      (∀ c : h.sem.Code, c ∈ h.search.candidates w.n w.K →
        ¬ h.sem.checks c (scale_data.powerBoundRawCode w.n)) ∧
      (∀ c : h.sem.Code,
        h.sem.checks c (scale_data.powerBoundRawCode w.n) →
          upper.U w.n < (h.sem.size c : Real)) ∧
      (h.sem.minProofCodeSize
          (scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) >
        upper.U w.n ∧
      upper.U n <
        month9_month10_checkedProofCodeMeasured scale_data h.sem n ∧
      month9_month10_checkedProofCodeMeasured scale_data h.sem n ≤
        upper.U n ∧
      False := by
  let endpoint := h.toDirectEndpoint.toAbstractMeasuredEndpoint
  let upper := endpoint.upperTailOfRationality hrat
  let w :=
    h.cert.computedLowerSearchWitness
      upper.U upper.polynomial upper.upperN
  let n := h.computedCollisionNOfRationality hrat
  have hcomputed :
      n = h.cert.witness upper.U upper.polynomial upper.upperN := by
    simpa [n, upper, endpoint]
      using h.computedCollisionN_eq_certWitness hrat
  have hwitness :
      w.n = h.cert.witness upper.U upper.polynomial upper.upperN := by
    change
      (h.cert.computedLowerSearchWitness
        upper.U upper.polynomial upper.upperN).n =
        h.cert.witness upper.U upper.polynomial upper.upperN
    rfl
  have hK :
      w.K = h.cert.cutoff upper.U upper.polynomial upper.upperN := by
    change
      (h.cert.computedLowerSearchWitness
        upper.U upper.polynomial upper.upperN).K =
        h.cert.cutoff upper.U upper.polynomial upper.upperN
    rfl
  have hn : n = w.n :=
    hcomputed.trans hwitness.symm
  have hlower :
      upper.U n <
        month9_month10_checkedProofCodeMeasured scale_data h.sem n := by
    simpa [n, upper, endpoint,
      Month9Month10CheckedSearchCollisionEndpoint.computedCollisionNOfRationality,
      Month9Month10CheckedSearchCollisionEndpoint.toDirectEndpoint,
      Month9Month10CheckedMeasuredDirectCollisionEndpoint.computedCollisionNOfRationality]
      using endpoint.lower_at_computedCollisionN hrat
  have hupper :
      month9_month10_checkedProofCodeMeasured scale_data h.sem n ≤
        upper.U n := by
    simpa [n, upper, endpoint,
      Month9Month10CheckedSearchCollisionEndpoint.computedCollisionNOfRationality,
      Month9Month10CheckedSearchCollisionEndpoint.toDirectEndpoint,
      Month9Month10CheckedMeasuredDirectCollisionEndpoint.computedCollisionNOfRationality]
      using endpoint.upper_at_computedCollisionN hrat
  have hfalse : False := by
    exact (not_lt_of_ge hupper) hlower
  exact
    ⟨hn,
      hwitness,
      hK,
      w.n_ge,
      w.cutoff_gt,
      w.rejects_candidates,
      w.no_small_at_n,
      w.minProofCodeSize_gt,
      hlower,
      hupper,
      hfalse⟩

end Month9Month10CheckedSearchCollisionEndpoint

/-- Collision endpoint whose lower side is generated by the proof-length-free
lower-gap source itself.  The only remaining input is the Sondow upper provider
for the same checked measured object. -/
def checkedSearchCollisionEndpointOfLowerGapSource
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          source.scale_data source.proof_code_semantics)) :
    Month9Month10CheckedSearchCollisionEndpoint source.scale_data where
  sem := source.proof_code_semantics
  search := source.small_code_search
  cert := source.computable_search_exclusion
  upper_provider := upper_provider

theorem checkedSearchCollisionEndpointOfLowerGapSource_computedN_eq_certWitness
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          source.scale_data source.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (checkedSearchCollisionEndpointOfLowerGapSource
        source upper_provider).computedCollisionNOfRationality hrat =
      source.computable_search_exclusion.witness
        ((checkedSearchCollisionEndpointOfLowerGapSource
            source upper_provider)
          |>.toDirectEndpoint
          |>.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).U
        ((checkedSearchCollisionEndpointOfLowerGapSource
            source upper_provider)
          |>.toDirectEndpoint
          |>.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).polynomial
        ((checkedSearchCollisionEndpointOfLowerGapSource
            source upper_provider)
          |>.toDirectEndpoint
          |>.toAbstractMeasuredEndpoint
          |>.upperTailOfRationality hrat).upperN :=
  rfl

theorem checkedSearchCollisionEndpointOfLowerGapSource_closure
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          source.scale_data source.proof_code_semantics)) :
    Nonempty
      (ComputableSearchGapCertificate
        (month9_month10_checkedProofCodeMeasured
          source.scale_data source.proof_code_semantics)) ∧
      (∀ U : Nat → Real,
        ∀ hU : _root_.is_polynomial_bound U,
          ∀ N : Nat,
            ((source.checkedGap
              |>.gap_for_polynomial_upper U hU).witness N) =
              source.computable_search_exclusion.witness U hU N) ∧
        (∀ U : Nat → Real,
          ∀ hU : _root_.is_polynomial_bound U,
            ∀ N : Nat,
              U (source.computable_search_exclusion.witness U hU N) <
                month9_month10_checkedProofCodeMeasured
                  source.scale_data source.proof_code_semantics
                  (source.computable_search_exclusion.witness U hU N)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (checkedSearchCollisionEndpointOfLowerGapSource
              source upper_provider).computedCollisionNOfRationality hrat =
              source.computable_search_exclusion.witness
                ((checkedSearchCollisionEndpointOfLowerGapSource
                    source upper_provider)
                  |>.toDirectEndpoint
                  |>.toAbstractMeasuredEndpoint
                  |>.upperTailOfRationality hrat).U
                ((checkedSearchCollisionEndpointOfLowerGapSource
                    source upper_provider)
                  |>.toDirectEndpoint
                  |>.toAbstractMeasuredEndpoint
                  |>.upperTailOfRationality hrat).polynomial
                ((checkedSearchCollisionEndpointOfLowerGapSource
                    source upper_provider)
                  |>.toDirectEndpoint
                  |>.toAbstractMeasuredEndpoint
                  |>.upperTailOfRationality hrat).upperN) ∧
            ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨⟨source.checkedGap⟩,
    source.checkedGap_witness_eq,
    source.checkedGap_strict_at_cert_witness,
    checkedSearchCollisionEndpointOfLowerGapSource_computedN_eq_certWitness
      source upper_provider,
    (checkedSearchCollisionEndpointOfLowerGapSource
      source upper_provider).not_rational⟩

/-- The polynomial upper tail selected under rationality for the proof-length-free
lower-gap source. -/
noncomputable def lowerGapSourceUpperTailOfRationality
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          source.scale_data source.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate source.measured :=
  (checkedSearchCollisionEndpointOfLowerGapSource source upper_provider)
    |>.toDirectEndpoint
    |>.toAbstractMeasuredEndpoint
    |>.upperTailOfRationality hrat

/-- The actual computed natural-number witness for the proof-length-free lower
gap source.  It is the finite-search exclusion witness evaluated at the upper
route's polynomial and threshold. -/
noncomputable def lowerGapSourceComputedNOfRationality
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          source.scale_data source.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  source.computable_search_exclusion.witness
    (lowerGapSourceUpperTailOfRationality
      source upper_provider hrat).U
    (lowerGapSourceUpperTailOfRationality
      source upper_provider hrat).polynomial
    (lowerGapSourceUpperTailOfRationality
      source upper_provider hrat).upperN

theorem lowerGapSourceComputedN_eq_endpointComputedN
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          source.scale_data source.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    lowerGapSourceComputedNOfRationality source upper_provider hrat =
      (checkedSearchCollisionEndpointOfLowerGapSource
        source upper_provider).computedCollisionNOfRationality hrat :=
  rfl

theorem lowerGapSourceComputedN_ge_upperN
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          source.scale_data source.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (lowerGapSourceUpperTailOfRationality
      source upper_provider hrat).upperN ≤
      lowerGapSourceComputedNOfRationality source upper_provider hrat :=
  source.computable_search_exclusion.witness_ge
    (lowerGapSourceUpperTailOfRationality
      source upper_provider hrat).U
    (lowerGapSourceUpperTailOfRationality
      source upper_provider hrat).polynomial
    (lowerGapSourceUpperTailOfRationality
      source upper_provider hrat).upperN

theorem lowerGapSource_lower_at_computedN
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          source.scale_data source.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (lowerGapSourceUpperTailOfRationality
      source upper_provider hrat).U
        (lowerGapSourceComputedNOfRationality source upper_provider hrat) <
      source.measured
        (lowerGapSourceComputedNOfRationality source upper_provider hrat) :=
  source.checkedGap_strict_at_cert_witness
    (lowerGapSourceUpperTailOfRationality
      source upper_provider hrat).U
    (lowerGapSourceUpperTailOfRationality
      source upper_provider hrat).polynomial
    (lowerGapSourceUpperTailOfRationality
      source upper_provider hrat).upperN

theorem lowerGapSource_upper_at_computedN
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          source.scale_data source.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    source.measured
        (lowerGapSourceComputedNOfRationality source upper_provider hrat) ≤
      (lowerGapSourceUpperTailOfRationality
        source upper_provider hrat).U
        (lowerGapSourceComputedNOfRationality source upper_provider hrat) :=
  (lowerGapSourceUpperTailOfRationality source upper_provider hrat).upper_after
    (lowerGapSourceComputedNOfRationality source upper_provider hrat)
    (lowerGapSourceComputedN_ge_upperN source upper_provider hrat)

theorem lowerGapSource_contradiction_at_computedN
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          source.scale_data source.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (not_lt_of_ge
    (lowerGapSource_upper_at_computedN source upper_provider hrat))
    (lowerGapSource_lower_at_computedN source upper_provider hrat)

theorem lowerGapSource_computedN_trace_closure
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          source.scale_data source.proof_code_semantics)) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let upper := lowerGapSourceUpperTailOfRationality
        source upper_provider hrat
      let n := lowerGapSourceComputedNOfRationality
        source upper_provider hrat
      n =
          (checkedSearchCollisionEndpointOfLowerGapSource
            source upper_provider).computedCollisionNOfRationality hrat ∧
        upper.upperN ≤ n ∧
          upper.U n < source.measured n ∧
            source.measured n ≤ upper.U n ∧
              False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  refine ⟨?_, ?_⟩
  · intro hrat
    exact
      ⟨lowerGapSourceComputedN_eq_endpointComputedN
          source upper_provider hrat,
        lowerGapSourceComputedN_ge_upperN source upper_provider hrat,
        lowerGapSource_lower_at_computedN source upper_provider hrat,
        lowerGapSource_upper_at_computedN source upper_provider hrat,
        lowerGapSource_contradiction_at_computedN
          source upper_provider hrat⟩
  · intro hrat
    exact lowerGapSource_contradiction_at_computedN
      source upper_provider hrat

/-- Checked-search collision endpoint generated directly from a checker
computable-search profile. -/
def checkedSearchCollisionEndpointOfCheckerComputableSearchProfile
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data profile.proof_code_semantics)) :
    Month9Month10CheckedSearchCollisionEndpoint scale_data :=
  checkedSearchCollisionEndpointOfLowerGapSource
    (lowerGapSourceOfCheckerComputableSearchProfile profile)
    upper_provider

noncomputable def checkerProfileUpperTailOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data profile.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate
      (month9_month10_checkedProofCodeMeasured
        scale_data profile.proof_code_semantics) :=
  lowerGapSourceUpperTailOfRationality
    (lowerGapSourceOfCheckerComputableSearchProfile profile)
    upper_provider hrat

noncomputable def checkerProfileComputedNOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data profile.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  profile.computable_search_exclusion.witness
    (checkerProfileUpperTailOfRationality
      profile upper_provider hrat).U
    (checkerProfileUpperTailOfRationality
      profile upper_provider hrat).polynomial
    (checkerProfileUpperTailOfRationality
      profile upper_provider hrat).upperN

theorem checkerProfileComputedN_eq_endpointComputedN
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data profile.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    checkerProfileComputedNOfRationality profile upper_provider hrat =
      (checkedSearchCollisionEndpointOfCheckerComputableSearchProfile
        profile upper_provider).computedCollisionNOfRationality hrat :=
  rfl

theorem checkerProfile_lower_at_computedN
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data profile.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (checkerProfileUpperTailOfRationality
      profile upper_provider hrat).U
        (checkerProfileComputedNOfRationality profile upper_provider hrat) <
      month9_month10_checkedProofCodeMeasured
        scale_data profile.proof_code_semantics
        (checkerProfileComputedNOfRationality profile upper_provider hrat) :=
  lowerGapSource_lower_at_computedN
    (lowerGapSourceOfCheckerComputableSearchProfile profile)
    upper_provider hrat

theorem checkerProfile_upper_at_computedN
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data profile.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    month9_month10_checkedProofCodeMeasured
        scale_data profile.proof_code_semantics
        (checkerProfileComputedNOfRationality profile upper_provider hrat) ≤
      (checkerProfileUpperTailOfRationality
        profile upper_provider hrat).U
        (checkerProfileComputedNOfRationality profile upper_provider hrat) :=
  lowerGapSource_upper_at_computedN
    (lowerGapSourceOfCheckerComputableSearchProfile profile)
    upper_provider hrat

theorem checkerProfile_contradiction_at_computedN
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data profile.proof_code_semantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (not_lt_of_ge
    (checkerProfile_upper_at_computedN profile upper_provider hrat))
    (checkerProfile_lower_at_computedN profile upper_provider hrat)

theorem checkerProfile_computedN_trace_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data profile.proof_code_semantics)) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let upper := checkerProfileUpperTailOfRationality
        profile upper_provider hrat
      let n := checkerProfileComputedNOfRationality
        profile upper_provider hrat
      n =
          (checkedSearchCollisionEndpointOfCheckerComputableSearchProfile
            profile upper_provider).computedCollisionNOfRationality hrat ∧
        upper.upperN ≤ n ∧
          upper.U n <
            month9_month10_checkedProofCodeMeasured
              scale_data profile.proof_code_semantics n ∧
            month9_month10_checkedProofCodeMeasured
                scale_data profile.proof_code_semantics n ≤
              upper.U n ∧
              False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [
    checkerProfileUpperTailOfRationality,
    checkerProfileComputedNOfRationality,
    checkedSearchCollisionEndpointOfCheckerComputableSearchProfile]
    using
      lowerGapSource_computedN_trace_closure
        (lowerGapSourceOfCheckerComputableSearchProfile profile)
        upper_provider

/-- A concrete checker rejection extractor directly supplies the proof-length-free
lower-gap source. -/
def lowerGapSourceOfCheckerComputableRejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration) :
    PAHilbertProofLengthFreeLowerGapSource :=
  lowerGapSourceOfCheckerComputableSearchProfile
    extractor.toCheckerComputableSearchProfile

noncomputable def rejectionExtractorUpperTailOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate
      (month9_month10_checkedProofCodeMeasured
        scale_data checker.toProofCodeSemantics) :=
  checkerProfileUpperTailOfRationality
    extractor.toCheckerComputableSearchProfile upper_provider hrat

noncomputable def rejectionExtractorComputedNOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  extractor.witness
    (rejectionExtractorUpperTailOfRationality
      extractor upper_provider hrat).U
    (rejectionExtractorUpperTailOfRationality
      extractor upper_provider hrat).polynomial
    (rejectionExtractorUpperTailOfRationality
      extractor upper_provider hrat).upperN

theorem rejectionExtractorComputedN_eq_checkerProfileComputedN
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    rejectionExtractorComputedNOfRationality extractor upper_provider hrat =
      checkerProfileComputedNOfRationality
        extractor.toCheckerComputableSearchProfile upper_provider hrat :=
  rfl

theorem rejectionExtractor_lower_at_computedN
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (rejectionExtractorUpperTailOfRationality
      extractor upper_provider hrat).U
        (rejectionExtractorComputedNOfRationality
          extractor upper_provider hrat) <
      month9_month10_checkedProofCodeMeasured
        scale_data checker.toProofCodeSemantics
        (rejectionExtractorComputedNOfRationality
          extractor upper_provider hrat) :=
  checkerProfile_lower_at_computedN
    extractor.toCheckerComputableSearchProfile upper_provider hrat

theorem rejectionExtractor_upper_at_computedN
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    month9_month10_checkedProofCodeMeasured
        scale_data checker.toProofCodeSemantics
        (rejectionExtractorComputedNOfRationality
          extractor upper_provider hrat) ≤
      (rejectionExtractorUpperTailOfRationality
        extractor upper_provider hrat).U
        (rejectionExtractorComputedNOfRationality
          extractor upper_provider hrat) :=
  checkerProfile_upper_at_computedN
    extractor.toCheckerComputableSearchProfile upper_provider hrat

theorem rejectionExtractor_contradiction_at_computedN
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (not_lt_of_ge
    (rejectionExtractor_upper_at_computedN
      extractor upper_provider hrat))
    (rejectionExtractor_lower_at_computedN
      extractor upper_provider hrat)

theorem rejectionExtractor_computedN_trace_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let upper := rejectionExtractorUpperTailOfRationality
        extractor upper_provider hrat
      let n := rejectionExtractorComputedNOfRationality
        extractor upper_provider hrat
      n =
          checkerProfileComputedNOfRationality
            extractor.toCheckerComputableSearchProfile
            upper_provider hrat ∧
        upper.upperN ≤ n ∧
          upper.U n <
            month9_month10_checkedProofCodeMeasured
              scale_data checker.toProofCodeSemantics n ∧
            month9_month10_checkedProofCodeMeasured
                scale_data checker.toProofCodeSemantics n ≤
              upper.U n ∧
              False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [
    rejectionExtractorUpperTailOfRationality,
    rejectionExtractorComputedNOfRationality]
    using
      checkerProfile_computedN_trace_closure
        extractor.toCheckerComputableSearchProfile upper_provider

/-- Fully explicit search witness once the upper route has supplied a concrete
polynomial upper tail.  This is the computable endpoint below rationality
choice: the witness is the rejection extractor evaluated at the upper
polynomial and its threshold. -/
def rejectionExtractorComputedNOfUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) : Nat :=
  extractor.witness upper.U upper.polynomial upper.upperN

theorem rejectionExtractorComputedNOfUpper_ge_upperN
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    upper.upperN ≤ rejectionExtractorComputedNOfUpper extractor upper :=
  extractor.witness_ge upper.U upper.polynomial upper.upperN

def rejectionExtractorLowerSearchWitnessOfUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    InternalPudlakTheorem5ComputedLowerSearchWitness
      scale_data checker.toProofCodeSemantics enumeration.toSmallCodeSearch
      upper.U upper.polynomial upper.upperN :=
  extractor.computedLowerSearchWitness
    upper.U upper.polynomial upper.upperN

theorem rejectionExtractorLowerSearchWitnessOfUpper_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    (rejectionExtractorLowerSearchWitnessOfUpper extractor upper).n =
      rejectionExtractorComputedNOfUpper extractor upper :=
  rfl

theorem rejectionExtractorLowerSearchWitnessOfUpper_K_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    (rejectionExtractorLowerSearchWitnessOfUpper extractor upper).K =
      extractor.cutoff upper.U upper.polynomial upper.upperN :=
  rfl

theorem rejectionExtractorLowerSearchWitnessOfUpper_minProofCodeSize_gt
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    (checker.toProofCodeSemantics.minProofCodeSize
        (scale_data.powerBoundRawCode
          (rejectionExtractorComputedNOfUpper extractor upper))
        ⟨rejectionExtractorComputedNOfUpper extractor upper, rfl⟩ :
      Real) >
      upper.U (rejectionExtractorComputedNOfUpper extractor upper) := by
  have h :=
    (rejectionExtractorLowerSearchWitnessOfUpper
      extractor upper).minProofCodeSize_gt
  rw [rejectionExtractorLowerSearchWitnessOfUpper_n_eq extractor upper] at h
  simpa [gt_iff_lt] using h

theorem rejectionExtractorLowerSearchWitnessOfUpper_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    let w := rejectionExtractorLowerSearchWitnessOfUpper extractor upper
    w.n = rejectionExtractorComputedNOfUpper extractor upper ∧
      w.K = extractor.cutoff upper.U upper.polynomial upper.upperN ∧
      upper.upperN ≤ w.n ∧
      upper.U w.n < (w.K : Real) ∧
      (∀ c : checker.Code, c ∈ enumeration.candidates w.n w.K →
        ¬ checker.checks c (scale_data.powerBoundRawCode w.n)) ∧
      (∀ c : checker.Code,
        checker.checks c (scale_data.powerBoundRawCode w.n) →
          upper.U w.n < (checker.size c : Real)) ∧
      (checker.toProofCodeSemantics.minProofCodeSize
          (scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) >
        upper.U w.n := by
  dsimp only
  refine ⟨
    rejectionExtractorLowerSearchWitnessOfUpper_n_eq extractor upper,
    rejectionExtractorLowerSearchWitnessOfUpper_K_eq extractor upper,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_⟩
  · exact (rejectionExtractorLowerSearchWitnessOfUpper extractor upper).n_ge
  · exact (rejectionExtractorLowerSearchWitnessOfUpper extractor upper).cutoff_gt
  · intro c hmem
    exact
      (rejectionExtractorLowerSearchWitnessOfUpper
        extractor upper).rejects_candidates c hmem
  · intro c hchecks
    exact
      (rejectionExtractorLowerSearchWitnessOfUpper
        extractor upper).no_small_at_n c hchecks
  · exact
      (rejectionExtractorLowerSearchWitnessOfUpper
        extractor upper).minProofCodeSize_gt

theorem rejectionExtractor_noSmallCode_at_computedNOfUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (c : checker.Code)
    (hchecks :
      checker.checks c
        (scale_data.powerBoundRawCode
          (rejectionExtractorComputedNOfUpper extractor upper))) :
    upper.U (rejectionExtractorComputedNOfUpper extractor upper) <
      (checker.size c : Real) := by
  have hwitness :
      extractor.toComputableFiniteSearchExclusion.witness
          upper.U upper.polynomial upper.upperN =
        extractor.witness upper.U upper.polynomial upper.upperN :=
    InternalPudlakTheorem5CheckerComputableRejectionExtractor.toComputableFiniteSearchExclusion_witness_eq
      extractor upper.U upper.polynomial upper.upperN
  have hchecks' :
      checker.checks c
        (scale_data.powerBoundRawCode
          (extractor.toComputableFiniteSearchExclusion.witness
            upper.U upper.polynomial upper.upperN)) := by
    rw [hwitness]
    simpa [rejectionExtractorComputedNOfUpper] using hchecks
  have hsmall :=
    extractor.toComputableFiniteSearchExclusion
      |>.noSmallAtWitness upper.U upper.polynomial upper.upperN c hchecks'
  rw [hwitness] at hsmall
  simpa [rejectionExtractorComputedNOfUpper,
    InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics_size_eq]
    using hsmall

theorem rejectionExtractor_rejects_smallCode_at_computedNOfUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (c : checker.Code)
    (hsize :
      (checker.size c : Real) ≤
        upper.U (rejectionExtractorComputedNOfUpper extractor upper)) :
    ¬ checker.checks c
        (scale_data.powerBoundRawCode
          (rejectionExtractorComputedNOfUpper extractor upper)) := by
  intro hchecks
  exact
    (not_lt_of_ge hsize)
      (rejectionExtractor_noSmallCode_at_computedNOfUpper
        extractor upper c hchecks)

theorem rejectionExtractor_lower_at_computedNOfUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    upper.U (rejectionExtractorComputedNOfUpper extractor upper) <
      month9_month10_checkedProofCodeMeasured
        scale_data checker.toProofCodeSemantics
        (rejectionExtractorComputedNOfUpper extractor upper) := by
  have hlower :=
    extractor.toComputableFiniteSearchExclusion
      |>.minProofCodeSize_gt_at_witness
        upper.U upper.polynomial upper.upperN
  rw [
    InternalPudlakTheorem5CheckerComputableRejectionExtractor.toComputableFiniteSearchExclusion_witness_eq
      extractor upper.U upper.polynomial upper.upperN] at hlower
  simpa [rejectionExtractorComputedNOfUpper,
    month9_month10_checkedProofCodeMeasured] using hlower

theorem rejectionExtractor_upper_at_computedNOfUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    month9_month10_checkedProofCodeMeasured
        scale_data checker.toProofCodeSemantics
        (rejectionExtractorComputedNOfUpper extractor upper) ≤
      upper.U (rejectionExtractorComputedNOfUpper extractor upper) :=
  upper.upper_after
    (rejectionExtractorComputedNOfUpper extractor upper)
    (rejectionExtractorComputedNOfUpper_ge_upperN extractor upper)

theorem rejectionExtractor_contradiction_at_computedNOfUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    False :=
  (not_lt_of_ge
    (rejectionExtractor_upper_at_computedNOfUpper extractor upper))
    (rejectionExtractor_lower_at_computedNOfUpper extractor upper)

/-- The explicit extractor endpoint in one audit target: the computed witness is
past the upper threshold, every accepting proof code is larger than the upper
window, all codes inside the window are rejected, and the upper/lower
inequalities collide at that same witness. -/
theorem rejectionExtractor_computedNOfUpper_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    let n := rejectionExtractorComputedNOfUpper extractor upper
    upper.upperN ≤ n ∧
      (∀ c : checker.Code,
        checker.checks c (scale_data.powerBoundRawCode n) →
          upper.U n < (checker.size c : Real)) ∧
      (∀ c : checker.Code,
        (checker.size c : Real) ≤ upper.U n →
          ¬ checker.checks c (scale_data.powerBoundRawCode n)) ∧
      upper.U n <
        month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics n ∧
      month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics n ≤
        upper.U n ∧
      False := by
  dsimp only
  refine ⟨
    rejectionExtractorComputedNOfUpper_ge_upperN extractor upper,
    ?_,
    ?_,
    rejectionExtractor_lower_at_computedNOfUpper extractor upper,
    rejectionExtractor_upper_at_computedNOfUpper extractor upper,
    rejectionExtractor_contradiction_at_computedNOfUpper extractor upper⟩
  · intro c hchecks
    exact
      rejectionExtractor_noSmallCode_at_computedNOfUpper
        extractor upper c hchecks
  · intro c hsize
    exact
      rejectionExtractor_rejects_smallCode_at_computedNOfUpper
        extractor upper c hsize

/-- Proof-length-free handoff for the part of the Month 9-10/11-12 route that
actually computes the lower-search witness.  It intentionally contains no root
`proof_length` field: the only data are the checker, the finite enumeration,
and the computable rejection extractor. -/
structure Month9Month10ProofLengthFreeExtractorHandoff
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 1 where
  checkerSemantics :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data
  finiteEnumeration :
    InternalPudlakTheorem5CheckerFiniteEnumeration checkerSemantics
  rejectionExtractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checkerSemantics finiteEnumeration

namespace Month9Month10ProofLengthFreeExtractorHandoff

def toLowerGapSource
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data) :
    PAHilbertProofLengthFreeLowerGapSource where
  scale_data := scale_data
  proof_code_semantics := h.checkerSemantics.toProofCodeSemantics
  small_code_search := h.finiteEnumeration.toSmallCodeSearch
  computable_search_exclusion :=
    h.rejectionExtractor.toComputableFiniteSearchExclusion

def computableFiniteSearchExclusion
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data) :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      scale_data h.checkerSemantics.toProofCodeSemantics
      h.finiteEnumeration.toSmallCodeSearch :=
  h.rejectionExtractor.toComputableFiniteSearchExclusion

theorem finiteSearchExclusion
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data) :
    InternalPudlakTheorem5FiniteSearchExclusion
      scale_data h.checkerSemantics.toProofCodeSemantics
      h.finiteEnumeration.toSmallCodeSearch :=
  h.computableFiniteSearchExclusion.toFiniteSearchExclusion

theorem noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data) :
    InternalPudlakTheorem5NoSmallProofCodes
      scale_data h.checkerSemantics.toProofCodeSemantics :=
  h.computableFiniteSearchExclusion.toNoSmallProofCodes

theorem minProofCodeSizeLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data) :
    ∀ f : Nat → Real, _root_.is_polynomial_bound f →
      ∃ᶠ n in Filter.atTop,
        (h.checkerSemantics.toProofCodeSemantics.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n :=
  InternalPudlakTheorem5NoSmallProofCodes.toProofCodeLowerBound
    h.noSmallProofCodes

def checkedMeasuredGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data) :
    ComputableSearchGapCertificate
      (month9_month10_checkedProofCodeMeasured
        scale_data h.checkerSemantics.toProofCodeSemantics) :=
  month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
    h.computableFiniteSearchExclusion

theorem checkedMeasuredGap_witness_eq_rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((h.checkedMeasuredGap |>.gap_for_polynomial_upper U hU).witness N) =
      h.rejectionExtractor.witness U hU N := by
  calc
    ((h.checkedMeasuredGap |>.gap_for_polynomial_upper U hU).witness N)
        = h.computableFiniteSearchExclusion.witness U hU N := by
          exact
            month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion_witness_eq
              h.computableFiniteSearchExclusion U hU N
    _ = h.rejectionExtractor.witness U hU N := by
        exact h.rejectionExtractor.toComputableFiniteSearchExclusion_witness_eq
          U hU N

/-- Proof-length-free lower-bound machine extracted from the checker
rejection extractor.  This is the theorem-5 lower-bound content before any root
`proof_length` calibration is used: finite-search exclusion, no-small proof
codes, a min-proof-code-size lower bound, and a computable checked gap whose
witness is definitionally the rejection-extractor witness. -/
theorem proofLengthFree_lower_bound_machine_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data) :
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data h.checkerSemantics.toProofCodeSemantics
        h.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data h.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (h.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data h.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((h.checkedMeasuredGap |>.gap_for_polynomial_upper U hU).witness N) =
          h.rejectionExtractor.witness U hU N) :=
  ⟨h.finiteSearchExclusion,
    h.noSmallProofCodes,
    h.minProofCodeSizeLowerBound,
    ⟨h.checkedMeasuredGap⟩,
    h.checkedMeasuredGap_witness_eq_rejectionExtractor⟩

def computedNOfUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics)) : Nat :=
  rejectionExtractorComputedNOfUpper h.rejectionExtractor upper

def lowerSearchWitnessOfUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics)) :
    InternalPudlakTheorem5ComputedLowerSearchWitness
      scale_data h.checkerSemantics.toProofCodeSemantics
      h.finiteEnumeration.toSmallCodeSearch
      upper.U upper.polynomial upper.upperN :=
  rejectionExtractorLowerSearchWitnessOfUpper h.rejectionExtractor upper

theorem computedNOfUpper_eq_rejectionExtractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics)) :
    h.computedNOfUpper upper =
      h.rejectionExtractor.witness
        upper.U upper.polynomial upper.upperN :=
  rfl

theorem lowerSearchWitnessOfUpper_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics)) :
    let w := h.lowerSearchWitnessOfUpper upper
    w.n = h.computedNOfUpper upper ∧
      w.K = h.rejectionExtractor.cutoff
        upper.U upper.polynomial upper.upperN ∧
      upper.upperN ≤ w.n ∧
      upper.U w.n < (w.K : Real) ∧
      (∀ c : h.checkerSemantics.Code,
        c ∈ h.finiteEnumeration.candidates w.n w.K →
          ¬ h.checkerSemantics.checks c
            (scale_data.powerBoundRawCode w.n)) ∧
      (∀ c : h.checkerSemantics.Code,
        h.checkerSemantics.checks c
          (scale_data.powerBoundRawCode w.n) →
          upper.U w.n < (h.checkerSemantics.size c : Real)) ∧
      (h.checkerSemantics.toProofCodeSemantics.minProofCodeSize
          (scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) >
        upper.U w.n := by
  simpa [computedNOfUpper, lowerSearchWitnessOfUpper]
    using
      rejectionExtractorLowerSearchWitnessOfUpper_closure
        h.rejectionExtractor upper

theorem computedNOfUpper_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics)) :
    let n := h.computedNOfUpper upper
    upper.upperN ≤ n ∧
      (∀ c : h.checkerSemantics.Code,
        h.checkerSemantics.checks c (scale_data.powerBoundRawCode n) →
          upper.U n < (h.checkerSemantics.size c : Real)) ∧
      (∀ c : h.checkerSemantics.Code,
        (h.checkerSemantics.size c : Real) ≤ upper.U n →
          ¬ h.checkerSemantics.checks c
            (scale_data.powerBoundRawCode n)) ∧
      upper.U n <
        month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics n ∧
      month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics n ≤
        upper.U n ∧
      False := by
  simpa [computedNOfUpper]
    using
      rejectionExtractor_computedNOfUpper_closure
        h.rejectionExtractor upper

noncomputable def upperTailOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate
      (month9_month10_checkedProofCodeMeasured
        scale_data h.checkerSemantics.toProofCodeSemantics) :=
  rejectionExtractorUpperTailOfRationality
    h.rejectionExtractor upper_provider hrat

noncomputable def computedNOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  h.computedNOfUpper
    (h.upperTailOfRationality upper_provider hrat)

theorem computedNOfRationality_eq_rejectionExtractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedNOfRationality upper_provider hrat =
      rejectionExtractorComputedNOfRationality
        h.rejectionExtractor upper_provider hrat :=
  rfl

theorem lowerSearchWitnessOfRationality_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let upper := h.upperTailOfRationality upper_provider hrat
    let w := h.lowerSearchWitnessOfUpper upper
    w.n = h.computedNOfRationality upper_provider hrat ∧
      w.K = h.rejectionExtractor.cutoff
        upper.U upper.polynomial upper.upperN ∧
      upper.upperN ≤ w.n ∧
      upper.U w.n < (w.K : Real) ∧
      (∀ c : h.checkerSemantics.Code,
        c ∈ h.finiteEnumeration.candidates w.n w.K →
          ¬ h.checkerSemantics.checks c
            (scale_data.powerBoundRawCode w.n)) ∧
      (∀ c : h.checkerSemantics.Code,
        h.checkerSemantics.checks c
          (scale_data.powerBoundRawCode w.n) →
          upper.U w.n < (h.checkerSemantics.size c : Real)) ∧
      (h.checkerSemantics.toProofCodeSemantics.minProofCodeSize
          (scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) >
        upper.U w.n := by
  simpa [computedNOfRationality]
    using
      h.lowerSearchWitnessOfUpper_closure
        (h.upperTailOfRationality upper_provider hrat)

theorem computedNOfRationality_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let upper := h.upperTailOfRationality upper_provider hrat
    let n := h.computedNOfRationality upper_provider hrat
    upper.upperN ≤ n ∧
      (∀ c : h.checkerSemantics.Code,
        h.checkerSemantics.checks c (scale_data.powerBoundRawCode n) →
          upper.U n < (h.checkerSemantics.size c : Real)) ∧
      (∀ c : h.checkerSemantics.Code,
        (h.checkerSemantics.size c : Real) ≤ upper.U n →
          ¬ h.checkerSemantics.checks c
            (scale_data.powerBoundRawCode n)) ∧
      upper.U n <
        month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics n ∧
      month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics n ≤
        upper.U n ∧
      False := by
  simpa [computedNOfRationality]
    using
      h.computedNOfUpper_closure
        (h.upperTailOfRationality upper_provider hrat)

theorem not_rational
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  intro hrat
  exact (h.computedNOfRationality_closure upper_provider hrat).2.2.2.2.2

theorem not_rational_with_witness_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics)) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let upper := h.upperTailOfRationality upper_provider hrat
      let n := h.computedNOfRationality upper_provider hrat
      upper.upperN ≤ n ∧
        upper.U n <
          month9_month10_checkedProofCodeMeasured
            scale_data h.checkerSemantics.toProofCodeSemantics n ∧
        month9_month10_checkedProofCodeMeasured
            scale_data h.checkerSemantics.toProofCodeSemantics n ≤
          upper.U n ∧
        False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  refine ⟨?_, h.not_rational upper_provider⟩
  intro hrat
  have hclosure := h.computedNOfRationality_closure upper_provider hrat
  exact ⟨hclosure.1, hclosure.2.2.2.1,
    hclosure.2.2.2.2.1, hclosure.2.2.2.2.2⟩

/-- Full proof-length-free theorem-5 trace at the rationality-computed
candidate.  The same natural number `w.n` is simultaneously the rejection
extractor witness, the finite-search lower witness, the checked lower-gap
witness, and the upper-tail contradiction witness.  This is the audit form that
prevents the proof from silently switching between different `n`s. -/
theorem proofLengthFree_full_lower_search_collision_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics)) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let upper := h.upperTailOfRationality upper_provider hrat
      let w := h.lowerSearchWitnessOfUpper upper
      w.n = h.computedNOfRationality upper_provider hrat ∧
        w.K = h.rejectionExtractor.cutoff
          upper.U upper.polynomial upper.upperN ∧
        upper.upperN ≤ w.n ∧
        upper.U w.n < (w.K : Real) ∧
        (∀ c : h.checkerSemantics.Code,
          c ∈ h.finiteEnumeration.candidates w.n w.K →
            ¬ h.checkerSemantics.checks c
              (scale_data.powerBoundRawCode w.n)) ∧
        (∀ c : h.checkerSemantics.Code,
          h.checkerSemantics.checks c
            (scale_data.powerBoundRawCode w.n) →
            upper.U w.n < (h.checkerSemantics.size c : Real)) ∧
        (h.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) >
          upper.U w.n ∧
        upper.U w.n <
          month9_month10_checkedProofCodeMeasured
            scale_data h.checkerSemantics.toProofCodeSemantics w.n ∧
        month9_month10_checkedProofCodeMeasured
            scale_data h.checkerSemantics.toProofCodeSemantics w.n ≤
          upper.U w.n ∧
        False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  refine ⟨?_, h.not_rational upper_provider⟩
  intro hrat
  let upper := h.upperTailOfRationality upper_provider hrat
  let w := h.lowerSearchWitnessOfUpper upper
  rcases h.lowerSearchWitnessOfRationality_closure upper_provider hrat with
    ⟨hn, hK, hge, hcut, hreject, hnoSmall, hmin⟩
  rcases h.computedNOfRationality_closure upper_provider hrat with
    ⟨_hge, _hnoSmall, _hrejectSmall, hlower, hupper, hfalse⟩
  have hlower_w :
      upper.U w.n <
        month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics w.n := by
    simpa [upper, w, hn] using hlower
  have hupper_w :
      month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics w.n ≤
        upper.U w.n := by
    simpa [upper, w, hn] using hupper
  exact
    ⟨hn, hK, hge, hcut, hreject, hnoSmall, hmin,
      hlower_w, hupper_w, hfalse⟩

/-- The same computable lower gap, transported from checked minimum proof-code
size to the `ProofCodeSemantics.projectLength` measurement.  This remains
proof-length-free: it uses only the checker/extractor finite-search certificate
and the definitional equality between project length and checked minimum on the
theorem-5 raw-code family. -/
def projectLengthGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (fallback : _root_.FormulaCode → Nat) :
    ComputableSearchGapCertificate
      (month9_month10_checkerProjectLengthMeasured
        scale_data h.checkerSemantics.toProofCodeSemantics fallback) :=
  month9_month10_checkerProjectLengthGapOfCheckedGap
    fallback h.toLowerGapSource.checkedGap

theorem projectLengthGap_witness_eq_rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((h.projectLengthGap fallback |>.gap_for_polynomial_upper U hU).witness N) =
      h.rejectionExtractor.witness U hU N := by
  calc
    ((h.projectLengthGap fallback |>.gap_for_polynomial_upper U hU).witness N)
        = ((h.toLowerGapSource.checkedGap |>.gap_for_polynomial_upper U hU).witness N) := by
          exact
            month9_month10_checkerProjectLengthGapOfCheckedGap_witness_eq
              fallback h.toLowerGapSource.checkedGap U hU N
    _ = h.rejectionExtractor.witness U hU N := by
        calc
          ((h.toLowerGapSource.checkedGap |>.gap_for_polynomial_upper U hU).witness N)
              = h.rejectionExtractor.toComputableFiniteSearchExclusion.witness U hU N := by
                exact
                  PAHilbertProofLengthFreeLowerGapSource.checkedGap_witness_eq
                    h.toLowerGapSource U hU N
          _ = h.rejectionExtractor.witness U hU N := by
              exact
                h.rejectionExtractor.toComputableFiniteSearchExclusion_witness_eq
                  U hU N

/-- Transport a checked-measured Sondow upper provider to the checker
`projectLength` route.  The upper function and threshold are preserved by
pointwise equality. -/
def projectLengthUpperProviderOfChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics)) :
    Month9Month10AbstractMeasuredUpperProvider
      (month9_month10_checkerProjectLengthMeasured
        scale_data h.checkerSemantics.toProofCodeSemantics fallback) :=
  Month9Month10AbstractMeasuredUpperProvider.transportEq
    (fun n =>
      (month9_month10_checkerProjectLengthMeasured_eq_checkedProofCodeMeasured
        scale_data h.checkerSemantics.toProofCodeSemantics fallback n).symm)
    upper_provider

/-- Transport a checked-measured explicit upper provider to the checker
`projectLength` route.  This is the no-`choose` counterpart of
`projectLengthUpperProviderOfChecked`: it preserves the selected polynomial
upper function and cutoff under rationality. -/
noncomputable def projectLengthExplicitUpperProviderOfChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (upper_provider :
      Month9Month10ExplicitMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics)) :
    Month9Month10ExplicitMeasuredUpperProvider
      (month9_month10_checkerProjectLengthMeasured
        scale_data h.checkerSemantics.toProofCodeSemantics fallback) :=
  Month9Month10ExplicitMeasuredUpperProvider.transportEq
    (fun n =>
      (month9_month10_checkerProjectLengthMeasured_eq_checkedProofCodeMeasured
        scale_data h.checkerSemantics.toProofCodeSemantics fallback n).symm)
    upper_provider

theorem projectLengthExplicitUpperProviderOfChecked_upperN
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (upper_provider :
      Month9Month10ExplicitMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((h.projectLengthExplicitUpperProviderOfChecked fallback upper_provider)
      |>.upperTailOfRationality hrat).upperN =
      (upper_provider.upperTailOfRationality hrat).upperN :=
  rfl

/-- Direct computable collision endpoint over the checker-induced project-length
measurement.  This is the proof-length-free endpoint parallel to the checked
minimum route, before any transport to root `proof_length` is attempted. -/
def projectLengthDirectEndpointOfCheckedUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics)) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (month9_month10_checkerProjectLengthMeasured
        scale_data h.checkerSemantics.toProofCodeSemantics fallback) where
  gap := h.projectLengthGap fallback
  upper_provider :=
    h.projectLengthUpperProviderOfChecked fallback upper_provider

theorem projectLengthDirectEndpoint_computedN_eq_rejectionExtractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let endpoint :=
      h.projectLengthDirectEndpointOfCheckedUpper fallback upper_provider
    endpoint.computedCollisionNOfRationality hrat =
      h.rejectionExtractor.witness
        (endpoint.upperTailOfRationality hrat).U
        (endpoint.upperTailOfRationality hrat).polynomial
        (endpoint.upperTailOfRationality hrat).upperN := by
  let endpoint :=
    h.projectLengthDirectEndpointOfCheckedUpper fallback upper_provider
  have hcomputed :
      endpoint.computedCollisionNOfRationality hrat =
        (endpoint.gap.gap_for_polynomial_upper
          (endpoint.upperTailOfRationality hrat).U
          (endpoint.upperTailOfRationality hrat).polynomial).witness
            (endpoint.upperTailOfRationality hrat).upperN :=
    endpoint.computedCollisionN_eq_searchGapWitness hrat
  have hwitness :
      ((h.projectLengthGap fallback |>.gap_for_polynomial_upper
          (endpoint.upperTailOfRationality hrat).U
          (endpoint.upperTailOfRationality hrat).polynomial).witness
            (endpoint.upperTailOfRationality hrat).upperN) =
        h.rejectionExtractor.witness
          (endpoint.upperTailOfRationality hrat).U
          (endpoint.upperTailOfRationality hrat).polynomial
          (endpoint.upperTailOfRationality hrat).upperN :=
    h.projectLengthGap_witness_eq_rejectionExtractor fallback
      (endpoint.upperTailOfRationality hrat).U
      (endpoint.upperTailOfRationality hrat).polynomial
      (endpoint.upperTailOfRationality hrat).upperN
  exact hcomputed.trans (by
    simpa [endpoint, projectLengthDirectEndpointOfCheckedUpper] using hwitness)

theorem projectLengthDirectEndpoint_full_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ProofLengthFreeExtractorHandoff scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let endpoint :=
      h.projectLengthDirectEndpointOfCheckedUpper fallback upper_provider
    let n := endpoint.computedCollisionNOfRationality hrat
    endpoint.computedCollisionNOfRationality hrat =
        h.rejectionExtractor.witness
          (endpoint.upperTailOfRationality hrat).U
          (endpoint.upperTailOfRationality hrat).polynomial
          (endpoint.upperTailOfRationality hrat).upperN ∧
      (endpoint.upperTailOfRationality hrat).upperN ≤ n ∧
        (endpoint.upperTailOfRationality hrat).U n <
          month9_month10_checkerProjectLengthMeasured
            scale_data h.checkerSemantics.toProofCodeSemantics fallback n ∧
          month9_month10_checkerProjectLengthMeasured
            scale_data h.checkerSemantics.toProofCodeSemantics fallback n ≤
            (endpoint.upperTailOfRationality hrat).U n ∧
            False := by
  let endpoint :=
    h.projectLengthDirectEndpointOfCheckedUpper fallback upper_provider
  let n := endpoint.computedCollisionNOfRationality hrat
  exact
    ⟨h.projectLengthDirectEndpoint_computedN_eq_rejectionExtractorWitness
        fallback upper_provider hrat,
      endpoint.computedCollisionN_ge_upperN hrat,
      endpoint.lower_at_computedCollisionN hrat,
      endpoint.upper_at_computedCollisionN hrat,
      endpoint.computed_n_contradiction hrat⟩

end Month9Month10ProofLengthFreeExtractorHandoff

/-! ## Executable calibrated rejection search to proof-length-free machine -/

/-- Forget the calibrated proof-length layer and expose the theorem-5 search
kernel generated directly by an executable calibrated rejection sweep.  This
uses the concrete PA/Hilbert checker, the supplied finite enumeration, and the
Boolean rejection search, but does not use root `proof_length` exactness. -/
def executableRejectionSearchToProofLengthFreeExtractorHandoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (input :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    Month9Month10ProofLengthFreeExtractorHandoff scale_data where
  checkerSemantics :=
    concretePAHilbertPowerBoundCalibratedCheckerSemantics
      scale_data lengthCodeAt
  finiteEnumeration :=
    enumeration.toFiniteEnumeration
  rejectionExtractor :=
    input.toCheckerExtractor

/-- The executable calibrated rejection search already supplies the full
proof-length-free theorem-5 lower-bound machine.  The final witness is the
search witness, not a later proof-length calibration witness. -/
theorem executableRejectionSearch_proofLengthFree_lower_bound_machine_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (input :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    let handoff : Month9Month10ProofLengthFreeExtractorHandoff scale_data :=
      executableRejectionSearchToProofLengthFreeExtractorHandoff input
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data handoff.checkerSemantics.toProofCodeSemantics
        handoff.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data handoff.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (handoff.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data handoff.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((handoff.checkedMeasuredGap
          |>.gap_for_polynomial_upper U hU).witness N) =
          input.witness U hU N) := by
  dsimp
  have hclosure :=
    (executableRejectionSearchToProofLengthFreeExtractorHandoff input)
      |>.proofLengthFree_lower_bound_machine_closure
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.1,
      hclosure.2.2.2.1,
      by
        intro U hU N
        calc
          (((executableRejectionSearchToProofLengthFreeExtractorHandoff input)
              |>.checkedMeasuredGap
              |>.gap_for_polynomial_upper U hU).witness N) =
              input.toCheckerExtractor.witness U hU N :=
            hclosure.2.2.2.2 U hU N
          _ = input.witness U hU N := rfl⟩

/-- Exact finite-search-exclusion trace for the executable calibrated rejection
search.  This is the public audit form of task B: the Month 9-10
`ComputableFiniteSearchExclusion` generated from the executable PA/Hilbert
Boolean sweep keeps the same `witness` and `cutoff`, and its rejection clause is
exactly rejection of the calibrated finite enumeration at that same pair. -/
theorem executableRejectionSearch_computableFiniteSearchExclusion_exact_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (input :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    let handoff : Month9Month10ProofLengthFreeExtractorHandoff scale_data :=
      executableRejectionSearchToProofLengthFreeExtractorHandoff input
    let cert :=
      handoff.rejectionExtractor.toComputableFiniteSearchExclusion
    (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      cert.witness f hf N = input.witness f hf N ∧
        cert.cutoff f hf N = input.cutoff f hf N ∧
          N ≤ input.witness f hf N ∧
            f (input.witness f hf N) < (input.cutoff f hf N : Real)) ∧
      (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
        ∀ code : handoff.checkerSemantics.Code,
          code ∈
              handoff.finiteEnumeration.candidates
                (input.witness f hf N) (input.cutoff f hf N) →
            ¬ handoff.checkerSemantics.checks code
              (scale_data.powerBoundRawCode (input.witness f hf N))) := by
  dsimp [executableRejectionSearchToProofLengthFreeExtractorHandoff]
  refine ⟨?_, ?_⟩
  · intro f hf N
    exact
      ⟨rfl, rfl,
        input.witness_ge f hf N,
        input.cutoff_gt f hf N⟩
  · intro f hf N code hmem
    exact input.toCheckerExtractor.rejects_candidates f hf N code hmem

/-- Full computed lower-search trace from the executable calibrated rejection
search.  This is the concrete proof-length-free audit form: the same `n`
computed from the upper tail is the executable search witness, the lower-search
witness, and the checked-measured contradiction witness. -/
theorem executableRejectionSearch_proofLengthFree_full_lower_search_collision_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (input :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured scale_data
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data lengthCodeAt).toProofCodeSemantics)) :
    let handoff : Month9Month10ProofLengthFreeExtractorHandoff scale_data :=
      executableRejectionSearchToProofLengthFreeExtractorHandoff input
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let upper := handoff.upperTailOfRationality upper_provider hrat
      let w := handoff.lowerSearchWitnessOfUpper upper
      w.n = handoff.computedNOfRationality upper_provider hrat ∧
        w.K = input.cutoff upper.U upper.polynomial upper.upperN ∧
        upper.upperN ≤ w.n ∧
        upper.U w.n < (w.K : Real) ∧
        (∀ c : handoff.checkerSemantics.Code,
          c ∈ handoff.finiteEnumeration.candidates w.n w.K →
            ¬ handoff.checkerSemantics.checks c
              (scale_data.powerBoundRawCode w.n)) ∧
        (∀ c : handoff.checkerSemantics.Code,
          handoff.checkerSemantics.checks c
            (scale_data.powerBoundRawCode w.n) →
            upper.U w.n < (handoff.checkerSemantics.size c : Real)) ∧
        (handoff.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) >
          upper.U w.n ∧
        upper.U w.n <
          month9_month10_checkedProofCodeMeasured scale_data
            handoff.checkerSemantics.toProofCodeSemantics w.n ∧
        month9_month10_checkedProofCodeMeasured scale_data
            handoff.checkerSemantics.toProofCodeSemantics w.n ≤
          upper.U w.n ∧
        False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let handoff :=
    executableRejectionSearchToProofLengthFreeExtractorHandoff input
  have htrace :=
    handoff.proofLengthFree_full_lower_search_collision_trace
      upper_provider
  refine ⟨?_, htrace.2⟩
  intro hrat
  let upper := handoff.upperTailOfRationality upper_provider hrat
  let w := handoff.lowerSearchWitnessOfUpper upper
  rcases htrace.1 hrat with
    ⟨hn, hK, hge, hcut, hreject, hnoSmall, hmin, hlower, hupper,
      hfalse⟩
  have hK' :
      w.K = input.cutoff upper.U upper.polynomial upper.upperN := by
    calc
      w.K =
          handoff.rejectionExtractor.cutoff
            upper.U upper.polynomial upper.upperN := hK
      _ = input.cutoff upper.U upper.polynomial upper.upperN := rfl
  exact
    ⟨hn, hK', hge, hcut, hreject, hnoSmall, hmin,
      hlower, hupper, hfalse⟩

/-- Project-length endpoint trace generated directly from executable calibrated
rejection search.  This stays below the root proof-length bridge: the computed
collision witness is already the executable search witness for the
checker-induced `projectLength` measurement. -/
theorem executableRejectionSearch_projectLengthDirectEndpoint_full_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (input :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (fallback : _root_.FormulaCode → Nat)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured scale_data
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data lengthCodeAt).toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let handoff :=
      executableRejectionSearchToProofLengthFreeExtractorHandoff input
    let endpoint :=
      handoff.projectLengthDirectEndpointOfCheckedUpper
        fallback upper_provider
    let n := endpoint.computedCollisionNOfRationality hrat
    endpoint.computedCollisionNOfRationality hrat =
        input.witness
          (endpoint.upperTailOfRationality hrat).U
          (endpoint.upperTailOfRationality hrat).polynomial
          (endpoint.upperTailOfRationality hrat).upperN ∧
      (endpoint.upperTailOfRationality hrat).upperN ≤ n ∧
        (endpoint.upperTailOfRationality hrat).U n <
          month9_month10_checkerProjectLengthMeasured scale_data
            (concretePAHilbertPowerBoundCalibratedCheckerSemantics
              scale_data lengthCodeAt).toProofCodeSemantics fallback n ∧
          month9_month10_checkerProjectLengthMeasured scale_data
            (concretePAHilbertPowerBoundCalibratedCheckerSemantics
              scale_data lengthCodeAt).toProofCodeSemantics fallback n ≤
            (endpoint.upperTailOfRationality hrat).U n ∧
            False := by
  dsimp
  let handoff :=
    executableRejectionSearchToProofLengthFreeExtractorHandoff input
  let endpoint :=
    handoff.projectLengthDirectEndpointOfCheckedUpper fallback upper_provider
  have htrace :=
    handoff.projectLengthDirectEndpoint_full_trace
      fallback upper_provider hrat
  rcases htrace with ⟨hn, hge, hlower, hupper, hfalse⟩
  have hn' :
      endpoint.computedCollisionNOfRationality hrat =
        input.witness
          (endpoint.upperTailOfRationality hrat).U
          (endpoint.upperTailOfRationality hrat).polynomial
          (endpoint.upperTailOfRationality hrat).upperN := by
    calc
      endpoint.computedCollisionNOfRationality hrat =
          handoff.rejectionExtractor.witness
            (endpoint.upperTailOfRationality hrat).U
            (endpoint.upperTailOfRationality hrat).polynomial
            (endpoint.upperTailOfRationality hrat).upperN := hn
      _ = input.witness
            (endpoint.upperTailOfRationality hrat).U
            (endpoint.upperTailOfRationality hrat).polynomial
            (endpoint.upperTailOfRationality hrat).upperN := rfl
  exact ⟨hn', hge, hlower, hupper, hfalse⟩

/-! ## Canonical PA/Hilbert search core to proof-length-free lower-bound machine -/

/-- Proof-length-free PA/Hilbert checker/search core.  This is the canonical
checker exactness data needed for the theorem-5 lower-search machine, with the
root proof-length calibration deliberately left out. -/
structure PAHilbertCanonicalSearchExactnessCore : Type 2 where
  checker : PAHilbertChecker
  semantics : PAHilbertDerivabilitySemantics
  recognizerExactness :
    PAHilbertAxiomRecognizerExactness checker.recognizer semantics
  canonicalInterface :
    PAHilbertCanonicalCheckerInterface checker semantics
  scale_data : InternalPudlakTheorem5ScaleData
  checkerSemantics :
    InternalPudlakTheorem5CheckerSemantics.{0} scale_data
  finiteEnumeration :
    InternalPudlakTheorem5CheckerFiniteEnumeration checkerSemantics
  rejectionExtractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      checkerSemantics finiteEnumeration

namespace PAHilbertCanonicalSearchExactnessCore

/-- Forget the PA/Hilbert syntax layer and expose exactly the finite-search
data consumed by the Month 9-10 proof-length-free lower-bound machine. -/
def toProofLengthFreeExtractorHandoff
    (core : PAHilbertCanonicalSearchExactnessCore) :
    Month9Month10ProofLengthFreeExtractorHandoff core.scale_data where
  checkerSemantics :=
    core.checkerSemantics
  finiteEnumeration :=
    core.finiteEnumeration
  rejectionExtractor :=
    core.rejectionExtractor

theorem accepted_decoded_code_to_formulaCode_derivable
    (core : PAHilbertCanonicalSearchExactnessCore)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        core.checker formulaCode code) :
    PAHilbertFormulaCodeDerivable core.semantics formulaCode :=
  core.canonicalInterface.accepted_decoded_code_to_formulaCode_derivable
    formulaCode code haccepted

/-- The proof-length-free PA/Hilbert search core already supplies the internal
finite-search lower-bound machine.  The conclusion is the theorem-5 lower
content before any root `proof_length` calibration is used. -/
theorem proofLengthFree_lower_bound_machine_closure
    (core : PAHilbertCanonicalSearchExactnessCore) :
    InternalPudlakTheorem5FiniteSearchExclusion
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        core.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        core.scale_data core.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (core.scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            core.scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((core.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) =
          core.rejectionExtractor.witness U hU N) :=
  core.toProofLengthFreeExtractorHandoff
    |>.proofLengthFree_lower_bound_machine_closure

/-- Full computed lower-search collision trace from the proof-length-free
PA/Hilbert search core.  This records that the same `n` is used by the
lower-search witness, the checked gap, and the final contradiction. -/
theorem proofLengthFree_full_lower_search_collision_trace
    (core : PAHilbertCanonicalSearchExactnessCore)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          core.scale_data core.checkerSemantics.toProofCodeSemantics)) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let upper :=
        core.toProofLengthFreeExtractorHandoff.upperTailOfRationality
          upper_provider hrat
      let w :=
        core.toProofLengthFreeExtractorHandoff.lowerSearchWitnessOfUpper
          upper
      w.n =
          core.toProofLengthFreeExtractorHandoff.computedNOfRationality
            upper_provider hrat ∧
        w.K = core.rejectionExtractor.cutoff
          upper.U upper.polynomial upper.upperN ∧
        upper.upperN ≤ w.n ∧
        upper.U w.n < (w.K : Real) ∧
        (∀ c : core.checkerSemantics.Code,
          c ∈ core.finiteEnumeration.candidates w.n w.K →
            ¬ core.checkerSemantics.checks c
              (core.scale_data.powerBoundRawCode w.n)) ∧
        (∀ c : core.checkerSemantics.Code,
          core.checkerSemantics.checks c
            (core.scale_data.powerBoundRawCode w.n) →
            upper.U w.n < (core.checkerSemantics.size c : Real)) ∧
        (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (core.scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) >
          upper.U w.n ∧
        upper.U w.n <
          month9_month10_checkedProofCodeMeasured
            core.scale_data core.checkerSemantics.toProofCodeSemantics w.n ∧
        month9_month10_checkedProofCodeMeasured
            core.scale_data core.checkerSemantics.toProofCodeSemantics w.n ≤
          upper.U w.n ∧
        False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni :=
  core.toProofLengthFreeExtractorHandoff
    |>.proofLengthFree_full_lower_search_collision_trace upper_provider

end PAHilbertCanonicalSearchExactnessCore

/-- Compatibility projection from the older calibrated core to the new
proof-length-free search core.  The new core is the one whose theorems should
be used for proof-length-free audit probes. -/
def canonicalCalibratedCoreToCanonicalSearchExactnessCore
    (core : PAHilbertCanonicalCalibratedExactnessCore) :
    PAHilbertCanonicalSearchExactnessCore where
  checker :=
    core.checker
  semantics :=
    core.semantics
  recognizerExactness :=
    core.recognizerExactness
  canonicalInterface :=
    core.canonicalInterface
  scale_data :=
    core.scale_data
  checkerSemantics :=
    core.checkerSemantics
  finiteEnumeration :=
    core.finiteEnumeration
  rejectionExtractor :=
    core.rejectionExtractor

/-- Direct canonical search core from executable calibrated rejection search.
This bypasses the older calibrated core, so the proof-length-free lower-search
route does not mention root proof-length exactness. -/
def executableRejectionSearchToCanonicalSearchExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (input :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    PAHilbertCanonicalSearchExactnessCore where
  checker :=
    concretePAHilbertPowerBoundChecker scale_data
  semantics :=
    concretePAHilbertTheorem5DerivabilitySemantics
  recognizerExactness :=
    concretePAHilbertTheorem5AxiomRecognizerExactness
  canonicalInterface :=
    concretePAHilbertPowerBoundCanonicalCheckerInterface scale_data
  scale_data :=
    scale_data
  checkerSemantics :=
    concretePAHilbertPowerBoundCalibratedCheckerSemantics
      scale_data lengthCodeAt
  finiteEnumeration :=
    enumeration.toFiniteEnumeration
  rejectionExtractor :=
    input.toCheckerExtractor

theorem executableRejectionSearchToCanonicalSearchExactnessCore_handoff_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (input :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    PAHilbertCanonicalSearchExactnessCore.toProofLengthFreeExtractorHandoff
        (executableRejectionSearchToCanonicalSearchExactnessCore input) =
      executableRejectionSearchToProofLengthFreeExtractorHandoff input :=
  rfl

theorem executableRejectionSearch_canonicalSearchCore_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (input :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    Nonempty PAHilbertCanonicalSearchExactnessCore :=
  ⟨executableRejectionSearchToCanonicalSearchExactnessCore input⟩

theorem executableRejectionSearch_canonicalSearchCore_lower_bound_machine_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (input :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    let core := executableRejectionSearchToCanonicalSearchExactnessCore input
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data core.checkerSemantics.toProofCodeSemantics
        core.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data core.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((core.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) =
          input.witness U hU N) := by
  let core := executableRejectionSearchToCanonicalSearchExactnessCore input
  have hclosure := core.proofLengthFree_lower_bound_machine_closure
  dsimp [core, executableRejectionSearchToCanonicalSearchExactnessCore] at hclosure ⊢
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.1,
      hclosure.2.2.2.1,
      by
        intro U hU N
        exact (hclosure.2.2.2.2 U hU N).trans rfl⟩

/-- Direct proof-length-free canonical search core from the singleton-gap
calibrated rejection route.  This packages the empty-at-witness singleton
enumeration and its computable gap extractor as the canonical lower-search
machine input, without going through the root `proof_length` calibration. -/
def singletonGapRejectionInputToCanonicalSearchExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapRejectionInput
        scale_data lengthCodeAt) :
    PAHilbertCanonicalSearchExactnessCore where
  checker :=
    concretePAHilbertPowerBoundChecker scale_data
  semantics :=
    concretePAHilbertTheorem5DerivabilitySemantics
  recognizerExactness :=
    concretePAHilbertTheorem5AxiomRecognizerExactness
  canonicalInterface :=
    concretePAHilbertPowerBoundCanonicalCheckerInterface scale_data
  scale_data :=
    scale_data
  checkerSemantics :=
    concretePAHilbertPowerBoundCalibratedCheckerSemantics
      scale_data lengthCodeAt
  finiteEnumeration :=
    input.finiteEnumeration
  rejectionExtractor :=
    input.toCheckerExtractor

/-- The singleton-gap rejection route now directly inhabits the canonical
proof-length-free search core. -/
theorem singletonGapRejectionInput_canonicalSearchCore_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapRejectionInput
        scale_data lengthCodeAt) :
    Nonempty PAHilbertCanonicalSearchExactnessCore :=
  ⟨singletonGapRejectionInputToCanonicalSearchExactnessCore input⟩

/-- Exact witness/cutoff trace for the singleton-gap route after it has been
installed as the canonical proof-length-free search core. -/
theorem singletonGapRejectionInput_canonicalSearchCore_gap_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapRejectionInput
        scale_data lengthCodeAt) :
    let core := singletonGapRejectionInputToCanonicalSearchExactnessCore input
    (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      core.rejectionExtractor.witness f hf N =
          (input.gap.gap_for_polynomial_upper f hf).witness N ∧
        core.rejectionExtractor.cutoff f hf N =
          lengthCodeAt
            ((input.gap.gap_for_polynomial_upper f hf).witness N) ∧
          N ≤ (input.gap.gap_for_polynomial_upper f hf).witness N ∧
            f ((input.gap.gap_for_polynomial_upper f hf).witness N) <
              (lengthCodeAt
                ((input.gap.gap_for_polynomial_upper f hf).witness N) :
                  Real)) ∧
      (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
        core.finiteEnumeration.candidates
          (core.rejectionExtractor.witness f hf N)
          (core.rejectionExtractor.cutoff f hf N) = []) ∧
        (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
          ∀ code : core.checkerSemantics.Code,
          code ∈
            core.finiteEnumeration.candidates
              (core.rejectionExtractor.witness f hf N)
              (core.rejectionExtractor.cutoff f hf N) →
            ¬ core.checkerSemantics.checks code
              (scale_data.powerBoundRawCode
                (core.rejectionExtractor.witness f hf N))) := by
  dsimp [singletonGapRejectionInputToCanonicalSearchExactnessCore]
  refine ⟨?_, ?_, ?_⟩
  · exact (input.toCheckerExtractor_gap_trace).1
  · intro f hf N
    exact input.toCheckerExtractor_candidates_at_witness_empty f hf N
  · exact (input.toCheckerExtractor_gap_trace).2

/-- Singleton-gap rejection gives the full proof-length-free lower-bound
machine closure, with the checked-gap witness definitionally following the
original computable gap certificate. -/
theorem singletonGapRejectionInput_canonicalSearchCore_lower_bound_machine_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (input :
      ConcretePAHilbertPowerBoundSingletonGapRejectionInput
        scale_data lengthCodeAt) :
    let core := singletonGapRejectionInputToCanonicalSearchExactnessCore input
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data core.checkerSemantics.toProofCodeSemantics
        core.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data core.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((core.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) =
          (input.gap.gap_for_polynomial_upper U hU).witness N) := by
  let core := singletonGapRejectionInputToCanonicalSearchExactnessCore input
  have hclosure := core.proofLengthFree_lower_bound_machine_closure
  have htrace := singletonGapRejectionInput_canonicalSearchCore_gap_trace input
  dsimp [core, singletonGapRejectionInputToCanonicalSearchExactnessCore] at hclosure htrace ⊢
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.1,
      hclosure.2.2.2.1,
      by
        intro U hU N
        exact (hclosure.2.2.2.2 U hU N).trans
          ((htrace.1 U hU N).1)⟩

noncomputable def computableSearchGapCertificateOfWitnessExists
    {measured : Nat → Real}
    (hexists :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ U n < measured n) :
    ComputableSearchGapCertificate measured where
  gap_for_polynomial_upper := by
    intro U hU
    exact
      { witness := fun N => Classical.choose (hexists U hU N)
        witness_ge := by
          intro N
          exact (Classical.choose_spec (hexists U hU N)).1
        strict_at_witness := by
          intro N
          exact (Classical.choose_spec (hexists U hU N)).2 }

theorem computableSearchGapCertificateOfWitnessExists_witness_spec
    {measured : Nat → Real}
    (hexists :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ U n < measured n)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    N ≤
        ((computableSearchGapCertificateOfWitnessExists hexists)
          |>.gap_for_polynomial_upper U hU).witness N ∧
      U (((computableSearchGapCertificateOfWitnessExists hexists)
          |>.gap_for_polynomial_upper U hU).witness N) <
        measured
          (((computableSearchGapCertificateOfWitnessExists hexists)
            |>.gap_for_polynomial_upper U hU).witness N) :=
  ⟨((computableSearchGapCertificateOfWitnessExists hexists)
      |>.gap_for_polynomial_upper U hU).witness_ge N,
    ((computableSearchGapCertificateOfWitnessExists hexists)
      |>.gap_for_polynomial_upper U hU).strict_at_witness N⟩

noncomputable def computableSearchGapCertificateOfFrequentlyStrict
    {measured : Nat → Real}
    (hfreq :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∃ᶠ n in Filter.atTop, U n < measured n) :
    ComputableSearchGapCertificate measured :=
  computableSearchGapCertificateOfWitnessExists (fun U hU =>
    Filter.frequently_atTop.mp (hfreq U hU))

theorem computableSearchGapCertificateOfFrequentlyStrict_witness_spec
    {measured : Nat → Real}
    (hfreq :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∃ᶠ n in Filter.atTop, U n < measured n)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    N ≤
        ((computableSearchGapCertificateOfFrequentlyStrict hfreq)
          |>.gap_for_polynomial_upper U hU).witness N ∧
      U (((computableSearchGapCertificateOfFrequentlyStrict hfreq)
          |>.gap_for_polynomial_upper U hU).witness N) <
        measured
          (((computableSearchGapCertificateOfFrequentlyStrict hfreq)
            |>.gap_for_polynomial_upper U hU).witness N) :=
  computableSearchGapCertificateOfWitnessExists_witness_spec
    (fun U hU => Filter.frequently_atTop.mp (hfreq U hU)) U hU N

/-- Proof-length-free strict-scale singleton-gap input.  Compared with the
older calibrated singleton route, this deliberately removes the root
`proof_length` exactness field: strict scale growth gives raw-code injectivity,
and the computable calibrated-size gap supplies the rejection extractor. -/
structure ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  lengthCodeAt : Nat → Nat
  scale_strict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  gap :
    ComputableSearchGapCertificate
      (fun n : Nat => (lengthCodeAt n : Real))

namespace ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput

theorem scale_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data) :
    Function.Injective scale_data.scale := by
  intro a b hscale_eq
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have hstrict :
        scale_data.scale a < scale_data.scale b :=
      input.scale_strict hlt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)
  · exact heq
  · have hstrict :
        scale_data.scale b < scale_data.scale a :=
      input.scale_strict hgt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)

theorem powerBoundRawCode_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data) :
    Function.Injective scale_data.powerBoundRawCode :=
  concretePAHilbert_powerBoundRawCode_injective_of_scale_injective
    scale_data input.scale_injective

def toSingletonGapRejectionInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data) :
    ConcretePAHilbertPowerBoundSingletonGapRejectionInput
      scale_data input.lengthCodeAt where
  powerBoundRawCode_injective :=
    input.powerBoundRawCode_injective
  gap :=
    input.gap

def toCanonicalSearchExactnessCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data) :
    PAHilbertCanonicalSearchExactnessCore :=
  singletonGapRejectionInputToCanonicalSearchExactnessCore
    input.toSingletonGapRejectionInput

theorem canonicalSearchCore_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data) :
    Nonempty PAHilbertCanonicalSearchExactnessCore :=
  ⟨input.toCanonicalSearchExactnessCore⟩

noncomputable def ofFrequentlyStrictLength
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (hfreq :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∃ᶠ n in Filter.atTop, U n < (lengthCodeAt n : Real)) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
      scale_data where
  lengthCodeAt :=
    lengthCodeAt
  scale_strict :=
    scale_strict
  gap :=
    computableSearchGapCertificateOfFrequentlyStrict hfreq

theorem ofFrequentlyStrictLength_gap_witness_spec
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (hfreq :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∃ᶠ n in Filter.atTop, U n < (lengthCodeAt n : Real))
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    let input :=
      ofFrequentlyStrictLength
        (scale_data := scale_data) lengthCodeAt scale_strict hfreq
    N ≤ (input.gap.gap_for_polynomial_upper U hU).witness N ∧
      U ((input.gap.gap_for_polynomial_upper U hU).witness N) <
        (lengthCodeAt
          ((input.gap.gap_for_polynomial_upper U hU).witness N) : Real) := by
  simpa [ofFrequentlyStrictLength] using
    computableSearchGapCertificateOfFrequentlyStrict_witness_spec
      hfreq U hU N

noncomputable def ofCheckedPowerBoundLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (hchecked :
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
        scale_data lengthCodeAt) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
      scale_data :=
  ofFrequentlyStrictLength lengthCodeAt scale_strict
    (fun U hU =>
      (hchecked U hU).mono (fun _ hn => by
        simpa [gt_iff_lt] using hn))

theorem ofCheckedPowerBoundLowerBound_gap_witness_spec
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (hchecked :
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
        scale_data lengthCodeAt)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    let input :=
      ofCheckedPowerBoundLowerBound
        (scale_data := scale_data) lengthCodeAt scale_strict hchecked
    N ≤ (input.gap.gap_for_polynomial_upper U hU).witness N ∧
      U ((input.gap.gap_for_polynomial_upper U hU).witness N) <
        (lengthCodeAt
          ((input.gap.gap_for_polynomial_upper U hU).witness N) : Real) := by
  simpa [ofCheckedPowerBoundLowerBound] using
    ofFrequentlyStrictLength_gap_witness_spec
      (scale_data := scale_data) lengthCodeAt scale_strict
      (fun U hU =>
        (hchecked U hU).mono (fun _ hn => by
          simpa [gt_iff_lt] using hn))
      U hU N

theorem canonicalSearchCore_gap_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data) :
    let core := input.toCanonicalSearchExactnessCore
    (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      core.rejectionExtractor.witness f hf N =
          (input.gap.gap_for_polynomial_upper f hf).witness N ∧
        core.rejectionExtractor.cutoff f hf N =
          input.lengthCodeAt
            ((input.gap.gap_for_polynomial_upper f hf).witness N) ∧
          N ≤ (input.gap.gap_for_polynomial_upper f hf).witness N ∧
            f ((input.gap.gap_for_polynomial_upper f hf).witness N) <
              (input.lengthCodeAt
                ((input.gap.gap_for_polynomial_upper f hf).witness N) :
                  Real)) ∧
      (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
        core.finiteEnumeration.candidates
          (core.rejectionExtractor.witness f hf N)
          (core.rejectionExtractor.cutoff f hf N) = []) ∧
        (∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
          ∀ code : core.checkerSemantics.Code,
          code ∈
            core.finiteEnumeration.candidates
              (core.rejectionExtractor.witness f hf N)
              (core.rejectionExtractor.cutoff f hf N) →
            ¬ core.checkerSemantics.checks code
              (scale_data.powerBoundRawCode
                (core.rejectionExtractor.witness f hf N))) := by
  dsimp [toCanonicalSearchExactnessCore,
    singletonGapRejectionInputToCanonicalSearchExactnessCore,
    toSingletonGapRejectionInput]
  refine ⟨?_, ?_, ?_⟩
  · exact (input.toSingletonGapRejectionInput.toCheckerExtractor_gap_trace).1
  · intro f hf N
    exact
      input.toSingletonGapRejectionInput
        |>.toCheckerExtractor_candidates_at_witness_empty f hf N
  · exact (input.toSingletonGapRejectionInput.toCheckerExtractor_gap_trace).2

theorem proofLengthFree_lower_bound_machine_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data) :
    let core := input.toCanonicalSearchExactnessCore
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data core.checkerSemantics.toProofCodeSemantics
        core.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data core.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((core.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) =
          (input.gap.gap_for_polynomial_upper U hU).witness N) := by
  have hclosure :=
    singletonGapRejectionInput_canonicalSearchCore_lower_bound_machine_closure
      input.toSingletonGapRejectionInput
  simpa [toCanonicalSearchExactnessCore, toSingletonGapRejectionInput] using
    hclosure

/-- Full proof-length-free lower-search trace for a strict-scale singleton-gap
input, with the computed natural number pinned directly to the input gap
witness.  This removes one more witness-calibration layer from the final
auditable `N`: the lower-search witness, the canonical-search computed `N`,
and the original gap witness are the same number. -/
theorem proofLengthFree_full_lower_search_collision_trace_with_gapWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data
          input.toCanonicalSearchExactnessCore.checkerSemantics.toProofCodeSemantics)) :
    let core := input.toCanonicalSearchExactnessCore
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let handoff := core.toProofLengthFreeExtractorHandoff
      let upper := handoff.upperTailOfRationality upper_provider hrat
      let w := handoff.lowerSearchWitnessOfUpper upper
      w.n = handoff.computedNOfRationality upper_provider hrat ∧
        handoff.computedNOfRationality upper_provider hrat =
          (input.gap.gap_for_polynomial_upper
            upper.U upper.polynomial).witness upper.upperN ∧
        w.K =
          input.lengthCodeAt
            ((input.gap.gap_for_polynomial_upper
              upper.U upper.polynomial).witness upper.upperN) ∧
        upper.upperN ≤ w.n ∧
        upper.U w.n < (w.K : Real) ∧
        (∀ c : core.checkerSemantics.Code,
          c ∈ core.finiteEnumeration.candidates w.n w.K →
            ¬ core.checkerSemantics.checks c
              (scale_data.powerBoundRawCode w.n)) ∧
        (∀ c : core.checkerSemantics.Code,
          core.checkerSemantics.checks c
            (scale_data.powerBoundRawCode w.n) →
            upper.U w.n < (core.checkerSemantics.size c : Real)) ∧
        (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) >
          upper.U w.n ∧
        upper.U w.n <
          month9_month10_checkedProofCodeMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics w.n ∧
        month9_month10_checkedProofCodeMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics w.n ≤
          upper.U w.n ∧
        False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  let core := input.toCanonicalSearchExactnessCore
  let handoff := core.toProofLengthFreeExtractorHandoff
  have htrace := core.proofLengthFree_full_lower_search_collision_trace
    upper_provider
  have hgap_trace := input.canonicalSearchCore_gap_trace
  refine ⟨?_, htrace.2⟩
  intro hrat
  let upper := handoff.upperTailOfRationality upper_provider hrat
  let w := handoff.lowerSearchWitnessOfUpper upper
  rcases htrace.1 hrat with
    ⟨hn, hK, hge, hcut, hreject, hnoSmall, hmin, hlower,
      hupper, hfalse⟩
  have hcomputed_gap :
      handoff.computedNOfRationality upper_provider hrat =
        (input.gap.gap_for_polynomial_upper
          upper.U upper.polynomial).witness upper.upperN := by
    calc
      handoff.computedNOfRationality upper_provider hrat =
          handoff.rejectionExtractor.witness
            upper.U upper.polynomial upper.upperN := by
            simpa [
              Month9Month10ProofLengthFreeExtractorHandoff.computedNOfRationality,
              upper, handoff] using
              handoff.computedNOfUpper_eq_rejectionExtractorWitness upper
      _ = (input.gap.gap_for_polynomial_upper
            upper.U upper.polynomial).witness upper.upperN := by
            simpa [handoff,
              PAHilbertCanonicalSearchExactnessCore.toProofLengthFreeExtractorHandoff] using
              (hgap_trace.1 upper.U upper.polynomial upper.upperN).1
  have hK_gap :
      w.K =
        input.lengthCodeAt
          ((input.gap.gap_for_polynomial_upper
            upper.U upper.polynomial).witness upper.upperN) := by
    calc
      w.K =
          handoff.rejectionExtractor.cutoff
            upper.U upper.polynomial upper.upperN := hK
      _ = input.lengthCodeAt
            ((input.gap.gap_for_polynomial_upper
              upper.U upper.polynomial).witness upper.upperN) := by
            simpa [handoff,
              PAHilbertCanonicalSearchExactnessCore.toProofLengthFreeExtractorHandoff] using
              (hgap_trace.1 upper.U upper.polynomial upper.upperN).2.1
  exact
    ⟨hn, hcomputed_gap, hK_gap, hge, hcut, hreject, hnoSmall,
      hmin, hlower, hupper, hfalse⟩

/-- Project-length direct endpoint for a strict-scale singleton-gap input,
with the endpoint collision number pinned directly to the original input gap
witness.  This is the clean `projectLength` form needed by an explicit `bigN`
certificate: no root `proof_length` bridge is used. -/
theorem projectLengthDirectEndpoint_full_trace_with_gapWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data
          input.toCanonicalSearchExactnessCore.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let core := input.toCanonicalSearchExactnessCore
    let handoff := core.toProofLengthFreeExtractorHandoff
    let endpoint :=
      handoff.projectLengthDirectEndpointOfCheckedUpper
        fallback upper_provider
    let upper := endpoint.upperTailOfRationality hrat
    let n := endpoint.computedCollisionNOfRationality hrat
    n =
        (input.gap.gap_for_polynomial_upper
          upper.U upper.polynomial).witness upper.upperN ∧
      endpoint.computedCollisionNOfRationality hrat =
        handoff.rejectionExtractor.witness
          upper.U upper.polynomial upper.upperN ∧
      upper.upperN ≤ n ∧
        upper.U n <
          month9_month10_checkerProjectLengthMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics fallback n ∧
          month9_month10_checkerProjectLengthMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics fallback n ≤
            upper.U n ∧
          False := by
  let core := input.toCanonicalSearchExactnessCore
  let handoff := core.toProofLengthFreeExtractorHandoff
  let endpoint :=
    handoff.projectLengthDirectEndpointOfCheckedUpper fallback upper_provider
  let upper := endpoint.upperTailOfRationality hrat
  let n := endpoint.computedCollisionNOfRationality hrat
  rcases handoff.projectLengthDirectEndpoint_full_trace
      fallback upper_provider hrat with
    ⟨hn_rejection, hge, hlower, hupper, hfalse⟩
  have hgap_trace := input.canonicalSearchCore_gap_trace
  have hn_gap :
      n =
        (input.gap.gap_for_polynomial_upper
          upper.U upper.polynomial).witness upper.upperN := by
    calc
      n =
          handoff.rejectionExtractor.witness
            upper.U upper.polynomial upper.upperN := hn_rejection
      _ = (input.gap.gap_for_polynomial_upper
            upper.U upper.polynomial).witness upper.upperN := by
            simpa [handoff,
              PAHilbertCanonicalSearchExactnessCore.toProofLengthFreeExtractorHandoff] using
              (hgap_trace.1 upper.U upper.polynomial upper.upperN).1
  exact ⟨hn_gap, hn_rejection, hge, hlower, hupper, hfalse⟩

/-- Explicit-upper project-length certificate for a strict-scale singleton-gap
input.  This is the evaluator-facing form: once a concrete polynomial upper
tail is supplied, the collision index is exactly the original input-gap
witness at `upper.upperN`, and the project-length lower and upper estimates
collide at that number. -/
theorem projectLengthExplicitUpper_gapWitnessCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkerProjectLengthMeasured
          scale_data
          input.toCanonicalSearchExactnessCore.checkerSemantics.toProofCodeSemantics
          fallback)) :
    let core := input.toCanonicalSearchExactnessCore
    let handoff := core.toProofLengthFreeExtractorHandoff
    let measured :=
      month9_month10_checkerProjectLengthMeasured
        scale_data core.checkerSemantics.toProofCodeSemantics fallback
    let projectGap := handoff.projectLengthGap fallback
    let bigN :=
      (input.gap.gap_for_polynomial_upper
        upper.U upper.polynomial).witness upper.upperN
    (projectGap.gap_for_polynomial_upper
        upper.U upper.polynomial).witness upper.upperN = bigN ∧
      handoff.rejectionExtractor.witness
          upper.U upper.polynomial upper.upperN = bigN ∧
        upper.upperN ≤ bigN ∧
          upper.U bigN < measured bigN ∧
            measured bigN ≤ upper.U bigN ∧
              False := by
  dsimp
  let core := input.toCanonicalSearchExactnessCore
  let handoff := core.toProofLengthFreeExtractorHandoff
  let measured :=
    month9_month10_checkerProjectLengthMeasured
      scale_data core.checkerSemantics.toProofCodeSemantics fallback
  let projectGap := handoff.projectLengthGap fallback
  let bigN :=
    (input.gap.gap_for_polynomial_upper
      upper.U upper.polynomial).witness upper.upperN
  have hproject_rejection :
      (projectGap.gap_for_polynomial_upper
          upper.U upper.polynomial).witness upper.upperN =
        handoff.rejectionExtractor.witness
          upper.U upper.polynomial upper.upperN := by
    simpa [projectGap] using
      handoff.projectLengthGap_witness_eq_rejectionExtractor
        fallback upper.U upper.polynomial upper.upperN
  have hgap_trace := input.canonicalSearchCore_gap_trace
  have hproject_gap :
      (projectGap.gap_for_polynomial_upper
          upper.U upper.polynomial).witness upper.upperN = bigN := by
    calc
      (projectGap.gap_for_polynomial_upper
          upper.U upper.polynomial).witness upper.upperN =
          handoff.rejectionExtractor.witness
            upper.U upper.polynomial upper.upperN := hproject_rejection
      _ = bigN := by
          simpa [bigN, handoff,
            PAHilbertCanonicalSearchExactnessCore.toProofLengthFreeExtractorHandoff] using
            (hgap_trace.1 upper.U upper.polynomial upper.upperN).1
  have hrejection_gap :
      handoff.rejectionExtractor.witness
          upper.U upper.polynomial upper.upperN = bigN :=
    hproject_rejection.symm.trans hproject_gap
  have hge : upper.upperN ≤ bigN := by
    simpa [hproject_gap] using
      (projectGap.gap_for_polynomial_upper
        upper.U upper.polynomial).witness_ge upper.upperN
  have hlower : upper.U bigN < measured bigN := by
    have hstrict :=
      (projectGap.gap_for_polynomial_upper
        upper.U upper.polynomial).strict_at_witness upper.upperN
    rw [hproject_gap] at hstrict
    simpa [projectGap, handoff, core,
      toCanonicalSearchExactnessCore,
      singletonGapRejectionInputToCanonicalSearchExactnessCore,
      toSingletonGapRejectionInput,
      PAHilbertCanonicalSearchExactnessCore.toProofLengthFreeExtractorHandoff,
      measured] using hstrict
  have hupper : measured bigN ≤ upper.U bigN := by
    simpa [core, toCanonicalSearchExactnessCore,
      singletonGapRejectionInputToCanonicalSearchExactnessCore,
      toSingletonGapRejectionInput, measured] using
      upper.upper_after bigN hge
  exact
    ⟨hproject_gap,
      hrejection_gap,
      hge,
      hlower,
      hupper,
      (not_lt_of_ge hupper) hlower⟩

/-- Provider-level version of
`projectLengthExplicitUpper_gapWitnessCertificate`.  Under rationality, an
explicit project-length upper provider selects the upper certificate, and the
computed collision index is still exactly the original strict singleton gap
witness. -/
theorem projectLengthExplicitUpperProvider_gapWitnessCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (upper_provider :
      Month9Month10ExplicitMeasuredUpperProvider
        (month9_month10_checkerProjectLengthMeasured
          scale_data
          input.toCanonicalSearchExactnessCore.checkerSemantics.toProofCodeSemantics
          fallback))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let core := input.toCanonicalSearchExactnessCore
    let handoff := core.toProofLengthFreeExtractorHandoff
    let measured :=
      month9_month10_checkerProjectLengthMeasured
        scale_data core.checkerSemantics.toProofCodeSemantics fallback
    let upper := upper_provider.upperTailOfRationality hrat
    let projectGap := handoff.projectLengthGap fallback
    let bigN :=
      (input.gap.gap_for_polynomial_upper
        upper.U upper.polynomial).witness upper.upperN
    (projectGap.gap_for_polynomial_upper
        upper.U upper.polynomial).witness upper.upperN = bigN ∧
      handoff.rejectionExtractor.witness
          upper.U upper.polynomial upper.upperN = bigN ∧
        upper.upperN ≤ bigN ∧
          upper.U bigN < measured bigN ∧
            measured bigN ≤ upper.U bigN ∧
              False := by
  dsimp
  exact
    input.projectLengthExplicitUpper_gapWitnessCertificate fallback
      (upper_provider.upperTailOfRationality hrat)

/-- The strict singleton project-length route closes rationality directly from
an explicit upper provider.  This is the proof-length-free endpoint used for
the computable-`N` route: no root `proof_length` or payload bridge appears in
the statement. -/
theorem projectLengthExplicitUpperProvider_not_rational
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (upper_provider :
      Month9Month10ExplicitMeasuredUpperProvider
        (month9_month10_checkerProjectLengthMeasured
          scale_data
          input.toCanonicalSearchExactnessCore.checkerSemantics.toProofCodeSemantics
          fallback)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  intro hrat
  exact
    (input.projectLengthExplicitUpperProvider_gapWitnessCertificate
      fallback upper_provider hrat).2.2.2.2.2

/-- Checked-upper-provider version of the strict singleton project-length
certificate.  The explicit checked-measured upper provider is transported to
checker `projectLength`, preserving the selected upper cutoff; the final
collision index remains the original singleton gap witness. -/
theorem projectLengthExplicitCheckedUpperProvider_gapWitnessCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (upper_provider :
      Month9Month10ExplicitMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data
          input.toCanonicalSearchExactnessCore.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let core := input.toCanonicalSearchExactnessCore
    let handoff := core.toProofLengthFreeExtractorHandoff
    let project_upper_provider :=
      handoff.projectLengthExplicitUpperProviderOfChecked fallback
        upper_provider
    let measured :=
      month9_month10_checkerProjectLengthMeasured
        scale_data core.checkerSemantics.toProofCodeSemantics fallback
    let upper := project_upper_provider.upperTailOfRationality hrat
    let projectGap := handoff.projectLengthGap fallback
    let bigN :=
      (input.gap.gap_for_polynomial_upper
        upper.U upper.polynomial).witness upper.upperN
    (projectGap.gap_for_polynomial_upper
        upper.U upper.polynomial).witness upper.upperN = bigN ∧
      handoff.rejectionExtractor.witness
          upper.U upper.polynomial upper.upperN = bigN ∧
        upper.upperN ≤ bigN ∧
          upper.U bigN < measured bigN ∧
            measured bigN ≤ upper.U bigN ∧
              False := by
  dsimp
  exact
    input.projectLengthExplicitUpperProvider_gapWitnessCertificate
      fallback
      (input.toCanonicalSearchExactnessCore.toProofLengthFreeExtractorHandoff
        |>.projectLengthExplicitUpperProviderOfChecked fallback
          upper_provider)
      hrat

/-- Strict singleton project-length closure from an explicit checked-measured
upper provider.  This is closer to the upstream theorem-5 checked target data
than the project-length-provider endpoint and still avoids root `proof_length`
and payload assumptions. -/
theorem projectLengthExplicitCheckedUpperProvider_not_rational
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (upper_provider :
      Month9Month10ExplicitMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data
          input.toCanonicalSearchExactnessCore.checkerSemantics.toProofCodeSemantics)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  intro hrat
  exact
    (input.projectLengthExplicitCheckedUpperProvider_gapWitnessCertificate
      fallback upper_provider hrat).2.2.2.2.2

theorem proofLengthFree_closure_toCheckedPowerBoundLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data input.lengthCodeAt := by
  intro f hf
  let core := input.toCanonicalSearchExactnessCore
  have hclosure := input.proofLengthFree_lower_bound_machine_closure
  have hlower :=
    hclosure.2.2.1 f hf
  exact hlower.mono (fun n hn => by
    have hmin_nat :
        core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ =
          input.lengthCodeAt n := by
      simpa [core, toCanonicalSearchExactnessCore,
        singletonGapRejectionInputToCanonicalSearchExactnessCore,
        toSingletonGapRejectionInput,
        InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
        using
          concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
            scale_data input.lengthCodeAt n input.powerBoundRawCode_injective
    have hmin_real :
        (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) =
          (input.lengthCodeAt n : Real) := by
      exact_mod_cast hmin_nat
    rw [hmin_real] at hn
    simpa [gt_iff_lt] using hn)

theorem ofFrequentlyStrictLength_lower_bound_machine_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (hfreq :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∃ᶠ n in Filter.atTop, U n < (lengthCodeAt n : Real)) :
    let input :=
      ofFrequentlyStrictLength
        (scale_data := scale_data) lengthCodeAt scale_strict hfreq
    let core := input.toCanonicalSearchExactnessCore
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data core.checkerSemantics.toProofCodeSemantics
        core.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data core.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((core.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) =
          ((computableSearchGapCertificateOfFrequentlyStrict hfreq
              |>.gap_for_polynomial_upper U hU).witness N)) := by
  simpa [ofFrequentlyStrictLength] using
    (ofFrequentlyStrictLength
      (scale_data := scale_data) lengthCodeAt scale_strict hfreq)
      |>.proofLengthFree_lower_bound_machine_closure

theorem ofFrequentlyStrictLength_closure_toCheckedPowerBoundLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (hfreq :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∃ᶠ n in Filter.atTop, U n < (lengthCodeAt n : Real)) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data lengthCodeAt :=
  (ofFrequentlyStrictLength
    (scale_data := scale_data) lengthCodeAt scale_strict hfreq)
    |>.proofLengthFree_closure_toCheckedPowerBoundLowerBound

theorem ofCheckedPowerBoundLowerBound_lower_bound_machine_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (hchecked :
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
        scale_data lengthCodeAt) :
    let input :=
      ofCheckedPowerBoundLowerBound
        (scale_data := scale_data) lengthCodeAt scale_strict hchecked
    let core := input.toCanonicalSearchExactnessCore
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data core.checkerSemantics.toProofCodeSemantics
        core.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data core.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((core.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) =
          (input.gap.gap_for_polynomial_upper U hU).witness N) := by
  simpa [ofCheckedPowerBoundLowerBound] using
    (ofCheckedPowerBoundLowerBound
      (scale_data := scale_data) lengthCodeAt scale_strict hchecked)
      |>.proofLengthFree_lower_bound_machine_closure

theorem ofCheckedPowerBoundLowerBound_closure_preserves_checkedLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (hchecked :
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
        scale_data lengthCodeAt) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data lengthCodeAt :=
  (ofCheckedPowerBoundLowerBound
    (scale_data := scale_data) lengthCodeAt scale_strict hchecked)
    |>.proofLengthFree_closure_toCheckedPowerBoundLowerBound

/-- Exact proof-length-free equivalence for the current checked target.  Under
strict scale growth, proving the checked lower bound is the same as producing a
strict-scale singleton search input with that calibrated length.  The reverse
direction uses the lower-machine closure and the singleton minimum-size
calibration, so this is an audit check that the search-input route has not
weakened the checked lower-bound target. -/
theorem checkedPowerBoundLowerBound_iff_nonempty_strictScaleSearchInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
        scale_data lengthCodeAt ↔
      Nonempty
        { input :
            ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
              scale_data //
          input.lengthCodeAt = lengthCodeAt } := by
  constructor
  · intro hchecked
    exact
      ⟨⟨ofCheckedPowerBoundLowerBound
          (scale_data := scale_data) lengthCodeAt scale_strict hchecked,
        rfl⟩⟩
  · intro hinput
    rcases hinput with ⟨input, hlength⟩
    have hchecked :=
      input.proofLengthFree_closure_toCheckedPowerBoundLowerBound
    simpa [hlength] using hchecked

theorem checkedPowerBoundLowerBound_to_strictScaleSearchInput_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (hchecked :
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
        scale_data lengthCodeAt) :
    Nonempty
      { input :
          ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
            scale_data //
        input.lengthCodeAt = lengthCodeAt } :=
  (checkedPowerBoundLowerBound_iff_nonempty_strictScaleSearchInput
    (scale_data := scale_data) lengthCodeAt scale_strict).mp hchecked

theorem strictScaleSearchInput_nonempty_to_checkedPowerBoundLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (hinput :
      Nonempty
        { input :
            ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
              scale_data //
          input.lengthCodeAt = lengthCodeAt }) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data lengthCodeAt :=
  (checkedPowerBoundLowerBound_iff_nonempty_strictScaleSearchInput
    (scale_data := scale_data) lengthCodeAt scale_strict).mpr hinput

end ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput

/-- For the calibrated PA/Hilbert singleton semantics, no-small proof codes are
exactly the checked lower-bound target, provided the theorem-5 raw-code family
is injective.  This is the local mathematical core behind the proof-length-free
route: every accepted code for `powerBoundRawCode n` is the canonical code `n`,
so "every accepted code is larger than `f n`" is equivalent to
`lengthCodeAt n > f n`. -/
theorem concretePAHilbertPowerBoundCalibrated_noSmallProofCodes_iff_checkedPowerBoundLowerBound_of_injective
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    InternalPudlakTheorem5NoSmallProofCodes
        scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics ↔
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
        scale_data lengthCodeAt := by
  constructor
  · intro hno f hf
    have hlower :=
      InternalPudlakTheorem5NoSmallProofCodes.toProofCodeLowerBound
        hno f hf
    exact hlower.mono (fun n hn => by
      have hmin_nat :
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
              scale_data lengthCodeAt).toProofCodeSemantics.minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ =
            lengthCodeAt n := by
        simpa [InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt] using
          concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
            scale_data lengthCodeAt n hinjective
      have hmin_real :
          ((concretePAHilbertPowerBoundCalibratedCheckerSemantics
              scale_data lengthCodeAt).toProofCodeSemantics.minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) =
            (lengthCodeAt n : Real) := by
        exact_mod_cast hmin_nat
      rw [hmin_real] at hn
      exact hn)
  · intro hchecked f hf
    exact (hchecked f hf).mono (fun n hn c hchecks => by
      have haccepted :
          PAHilbertAcceptedProofCodeForFormulaCode
            (concretePAHilbertPowerBoundChecker scale_data)
            (scale_data.powerBoundRawCode n) c := by
        simpa [InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
          concretePAHilbertPowerBoundCalibratedCheckerSemantics] using hchecks
      have hc_eq : c = n :=
        concretePAHilbertPowerBound_acceptedProofCode_to_code_eq_of_injective
          hinjective haccepted
      subst c
      simpa [InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
        concretePAHilbertPowerBoundCalibratedCheckerSemantics] using hn)

namespace ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput

theorem noSmallProofCodes_iff_checkedPowerBoundLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data) :
    InternalPudlakTheorem5NoSmallProofCodes
        scale_data
        input.toCanonicalSearchExactnessCore.checkerSemantics.toProofCodeSemantics ↔
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
        scale_data input.lengthCodeAt := by
  simpa [toCanonicalSearchExactnessCore,
    singletonGapRejectionInputToCanonicalSearchExactnessCore,
    toSingletonGapRejectionInput] using
    concretePAHilbertPowerBoundCalibrated_noSmallProofCodes_iff_checkedPowerBoundLowerBound_of_injective
      scale_data input.lengthCodeAt input.powerBoundRawCode_injective

theorem noSmallProofCodes_to_checkedPowerBoundLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data)
    (hno :
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data
        input.toCanonicalSearchExactnessCore.checkerSemantics.toProofCodeSemantics) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data input.lengthCodeAt :=
  input.noSmallProofCodes_iff_checkedPowerBoundLowerBound.mp hno

theorem checkedPowerBoundLowerBound_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
        scale_data)
    (hchecked :
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
        scale_data input.lengthCodeAt) :
    InternalPudlakTheorem5NoSmallProofCodes
      scale_data
      input.toCanonicalSearchExactnessCore.checkerSemantics.toProofCodeSemantics :=
  input.noSmallProofCodes_iff_checkedPowerBoundLowerBound.mpr hchecked

end ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput

/-- Polynomial bounds are closed under taking the pointwise maximum with zero.
This lets the theorem-5 lower bound produce eventually positive proof lengths
while preserving the original polynomial test function. -/
theorem is_polynomial_bound_max_zero
    {f : Nat → Real} (hf : _root_.is_polynomial_bound f) :
    _root_.is_polynomial_bound (fun n : Nat => max (f n) 0) := by
  rcases hf.nonneg_coefficient with ⟨C, k, hC, hbound⟩
  refine ⟨C, k, ?_⟩
  intro n
  have hbase_nonneg : 0 ≤ (n : Real) + 1 := by positivity
  have hpoly_nonneg : 0 ≤ C * ((n : Real) + 1) ^ k :=
    mul_nonneg hC (pow_nonneg hbase_nonneg k)
  exact max_le (hbound n) hpoly_nonneg

/-- Nat-valued upper rounding of the actual theorem-5 PA proof length on the
power-bound raw-code family.  This is a witness route, not the final concrete
PA/Hilbert calibration: the length family is still defined from the abstract
root `proof_length`. -/
noncomputable def actualProofLengthFloorSuccCodeAt
    (scale_data : InternalPudlakTheorem5ScaleData) : Nat → Nat :=
  fun n =>
    Int.toNat
      (Int.floor
          (_root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n)) + 1)

theorem actualProofLength_lt_actualProofLengthFloorSuccCodeAt
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat)
    (hpos :
      0 <
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n)) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode n) <
      (actualProofLengthFloorSuccCodeAt scale_data n : Real) := by
  let x : Real :=
    _root_.proof_length _root_.ProofSystem.PA
      _root_.ProofLengthMeasure.symbolSize
      (scale_data.powerBoundRawCode n)
  have hfloor_lt : x < ((Int.floor x + 1 : Int) : Real) := by
    rw [Int.cast_add, Int.cast_one]
    exact Int.lt_floor_add_one x
  have hfloor_nonneg : 0 ≤ Int.floor x :=
    Int.floor_nonneg.mpr (le_of_lt hpos)
  have hfloor_succ_nonneg : 0 ≤ Int.floor x + 1 :=
    Int.add_nonneg hfloor_nonneg (by norm_num)
  have htoNat_int :
      (((Int.floor x + 1).toNat : Nat) : Int) =
        Int.floor x + 1 :=
    Int.toNat_of_nonneg hfloor_succ_nonneg
  have htoNat_real :
      (((Int.floor x + 1).toNat : Nat) : Real) =
        ((Int.floor x + 1 : Int) : Real) := by
    exact_mod_cast htoNat_int
  change x < (actualProofLengthFloorSuccCodeAt scale_data n : Real)
  exact hfloor_lt.trans_eq (by
    simpa [actualProofLengthFloorSuccCodeAt, x] using htoNat_real.symm)

/-- The theorem-5 external power-bound lower bound directly yields a checked
lower bound for the Nat-valued upper rounding of actual PA proof length.  This
removes the pointwise equality calibration assumption from the lower-bound
transport: no `proof_length = lengthCodeAt` hypothesis is used. -/
theorem powerBoundLowerBound_to_checkedPowerBoundLowerBound_actualProofLengthFloorSucc
    (scale_data : InternalPudlakTheorem5ScaleData)
    (hlower : scale_data.PowerBoundLowerBound) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data (actualProofLengthFloorSuccCodeAt scale_data) := by
  intro f hf
  let f_nonneg : Nat → Real := fun n => max (f n) 0
  have hf_nonneg : _root_.is_polynomial_bound f_nonneg :=
    is_polynomial_bound_max_zero hf
  exact
    (hlower.frequently_beats_every_polynomial f_nonneg hf_nonneg).mono
      (fun n hn => by
        have hn_internal :
            f_nonneg n <
              _root_.proof_length _root_.ProofSystem.PA
                _root_.ProofLengthMeasure.symbolSize
                (scale_data.powerBoundRawCode n) := by
          simpa [f_nonneg, InternalPudlakTheorem5ScaleData.powerBoundRawCode]
            using hn
        have hf_lt_proof :
            f n <
              _root_.proof_length _root_.ProofSystem.PA
                _root_.ProofLengthMeasure.symbolSize
                (scale_data.powerBoundRawCode n) :=
          lt_of_le_of_lt (le_max_left (f n) (0 : Real)) hn_internal
        have hpos :
            0 <
              _root_.proof_length _root_.ProofSystem.PA
                _root_.ProofLengthMeasure.symbolSize
                (scale_data.powerBoundRawCode n) :=
          lt_of_le_of_lt (le_max_right (f n) (0 : Real)) hn_internal
        exact
          hf_lt_proof.trans
            (actualProofLength_lt_actualProofLengthFloorSuccCodeAt
              scale_data n hpos))

theorem checkedPowerBoundLowerBound_actualProofLengthFloorSucc_to_powerBoundLowerBound
    (scale_data : InternalPudlakTheorem5ScaleData)
    (hchecked :
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
        scale_data (actualProofLengthFloorSuccCodeAt scale_data)) :
    scale_data.PowerBoundLowerBound where
  frequently_beats_every_polynomial := by
    intro f hf
    let g : Nat → Real := fun n => max (f n + 1) 0 + 1
    have hf_add_one :
        _root_.is_polynomial_bound (fun n : Nat => f n + 1) :=
      _root_.is_polynomial_bound_add_const hf (by norm_num)
    have hg : _root_.is_polynomial_bound g := by
      dsimp [g]
      exact
        _root_.is_polynomial_bound_add_const
          (is_polynomial_bound_max_zero hf_add_one) (by norm_num)
    exact
      (hchecked g hg).mono
        (fun n hn => by
          let x : Real :=
            _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize
              (scale_data.powerBoundRawCode n)
          let z : Int := Int.floor x + 1
          let y : Nat := z.toNat
          have hy_eq :
              actualProofLengthFloorSuccCodeAt scale_data n = y := by
            rfl
          have hy_gt_g : g n < (y : Real) := by
            simpa [hy_eq] using hn
          have hone_le_g : (1 : Real) ≤ g n := by
            have hmax_nonneg : 0 ≤ max (f n + 1) 0 :=
              le_max_right (f n + 1) (0 : Real)
            dsimp [g]
            linarith
          have hy_gt_one : (1 : Real) < (y : Real) :=
            lt_of_le_of_lt hone_le_g hy_gt_g
          have hy_ne_zero : y ≠ 0 := by
            intro hy0
            rw [hy0] at hy_gt_one
            norm_num at hy_gt_one
          have hz_pos : 0 < z := by
            by_contra hz_not_pos
            have hz_nonpos : z ≤ 0 := le_of_not_gt hz_not_pos
            have hy0 : y = 0 := by
              simpa [y] using (Int.toNat_eq_zero.mpr hz_nonpos)
            exact hy_ne_zero hy0
          have htoNat_int : ((y : Nat) : Int) = z := by
            simpa [y] using Int.toNat_of_nonneg (le_of_lt hz_pos)
          have htoNat_real : (y : Real) = (z : Real) := by
            exact_mod_cast htoNat_int
          have hf_two_le_g : f n + 2 ≤ g n := by
            have hf_one_le_max : f n + 1 ≤ max (f n + 1) 0 :=
              le_max_left (f n + 1) (0 : Real)
            dsimp [g]
            linarith
          have hf_two_lt_z : f n + 2 < (z : Real) :=
            lt_of_le_of_lt hf_two_le_g (hy_gt_g.trans_eq htoNat_real)
          have hfloor_gt_f_one :
              f n + 1 < (Int.floor x : Real) := by
            have hz_expand :
                (z : Real) = (Int.floor x : Real) + 1 := by
              simp [z, Int.cast_add, Int.cast_one]
            rw [hz_expand] at hf_two_lt_z
            linarith
          have hx_gt_f : f n < x := by
            have hfloor_le_x : (Int.floor x : Real) ≤ x :=
              Int.floor_le x
            linarith
          simpa [x, InternalPudlakTheorem5ScaleData.powerBoundRawCode]
            using hx_gt_f)

theorem powerBoundLowerBound_iff_checkedPowerBoundLowerBound_actualProofLengthFloorSucc
    (scale_data : InternalPudlakTheorem5ScaleData) :
    scale_data.PowerBoundLowerBound ↔
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
        scale_data (actualProofLengthFloorSuccCodeAt scale_data) :=
  ⟨powerBoundLowerBound_to_checkedPowerBoundLowerBound_actualProofLengthFloorSucc
      scale_data,
    checkedPowerBoundLowerBound_actualProofLengthFloorSucc_to_powerBoundLowerBound
      scale_data⟩

/-- External theorem-5 lower bound to strict-scale singleton search input with
no pointwise proof-length equality hypothesis.  The selected Nat length is the
upper rounding of actual PA proof length, so this is still rooted in the
abstract `proof_length`, but the old equality-calibration residual has been
removed from this transport. -/
theorem powerBoundLowerBound_to_strictScaleSearchInput_nonempty_actualProofLengthFloorSucc
    (scale_data : InternalPudlakTheorem5ScaleData)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (hlower : scale_data.PowerBoundLowerBound) :
    Nonempty
      { input :
          ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
            scale_data //
        input.lengthCodeAt = actualProofLengthFloorSuccCodeAt scale_data } :=
  ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput.checkedPowerBoundLowerBound_to_strictScaleSearchInput_nonempty
    (scale_data := scale_data)
    (actualProofLengthFloorSuccCodeAt scale_data) scale_strict
    (powerBoundLowerBound_to_checkedPowerBoundLowerBound_actualProofLengthFloorSucc
      scale_data hlower)

/-- Direct lower-machine closure from theorem-5 external power-bound lower
bound using the upper-rounded actual proof length.  This is the same
proof-length-free PA/Hilbert singleton search machine as before, but it no
longer needs a separate hypothesis equating root `proof_length` with a
preselected `lengthCodeAt`; that Nat family is built from the actual
proof-length values. -/
theorem powerBoundLowerBound_to_proofLengthFree_lower_bound_machine_closure_actualProofLengthFloorSucc
    (scale_data : InternalPudlakTheorem5ScaleData)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (hlower : scale_data.PowerBoundLowerBound) :
    let lengthCodeAt := actualProofLengthFloorSuccCodeAt scale_data
    let hchecked :=
      powerBoundLowerBound_to_checkedPowerBoundLowerBound_actualProofLengthFloorSucc
        scale_data hlower
    let input :=
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput.ofCheckedPowerBoundLowerBound
        (scale_data := scale_data) lengthCodeAt scale_strict hchecked
    let core := input.toCanonicalSearchExactnessCore
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data core.checkerSemantics.toProofCodeSemantics
        core.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data core.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((core.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) =
          (input.gap.gap_for_polynomial_upper U hU).witness N) :=
  ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput.ofCheckedPowerBoundLowerBound_lower_bound_machine_closure
    (scale_data := scale_data)
    (actualProofLengthFloorSuccCodeAt scale_data) scale_strict
    (powerBoundLowerBound_to_checkedPowerBoundLowerBound_actualProofLengthFloorSucc
      scale_data hlower)

/-- One-sided replacement for the old equality calibration.  To transport
Pudlak's root proof-length lower bound to a Nat-valued checked length, it is
enough that the checked length dominates root `proof_length` on the theorem-5
raw-code family.  No pointwise equality is required. -/
theorem powerBoundLowerBound_to_checkedPowerBoundLowerBound_of_proofLengthLe
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (proof_length_le_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) ≤
          (lengthCodeAt n : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data lengthCodeAt := by
  intro f hf
  exact
    (hlower.frequently_beats_every_polynomial f hf).mono
      (fun n hn => by
        have hle :
            _root_.proof_length _root_.ProofSystem.PA
                _root_.ProofLengthMeasure.symbolSize
                (scale_data.toLiteratureScaleData.powerBoundRawCode n) ≤
              (lengthCodeAt n : Real) := by
          simpa [InternalPudlakTheorem5ScaleData.powerBoundRawCode]
            using proof_length_le_lengthCodeAt n
        exact lt_of_lt_of_le hn hle)

/-- Concrete checker version of the one-sided residual.  If the actual
theorem-5 proof length is bounded above by the checker-computed minimum proof
code size at every index, the external power-bound lower bound transfers to the
checker minimum-size lower bound. -/
theorem powerBoundLowerBound_to_checkedPowerBoundLowerBound_minProofCodeSize_of_actualLe_checkedMeasured
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (actual_le_checked :
      ∀ n : Nat,
        actualProofLengthMeasured scale_data n ≤
          month9_month10_checkedProofCodeMeasured scale_data sem n)
    (hlower : scale_data.PowerBoundLowerBound) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data
      (fun n : Nat =>
        sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩) := by
  intro f hf
  exact
    (hlower.frequently_beats_every_polynomial f hf).mono
      (fun n hn => by
        have hle :
            _root_.proof_length _root_.ProofSystem.PA
                _root_.ProofLengthMeasure.symbolSize
                (scale_data.toLiteratureScaleData.powerBoundRawCode n) ≤
              ((sem.minProofCodeSize
                (scale_data.powerBoundRawCode n) ⟨n, rfl⟩) : Real) := by
          calc
            _root_.proof_length _root_.ProofSystem.PA
                _root_.ProofLengthMeasure.symbolSize
                (scale_data.toLiteratureScaleData.powerBoundRawCode n)
                = actualProofLengthMeasured scale_data n := by
                    rfl
            _ ≤ month9_month10_checkedProofCodeMeasured scale_data sem n :=
                    actual_le_checked n
            _ = ((sem.minProofCodeSize
                    (scale_data.powerBoundRawCode n) ⟨n, rfl⟩) : Real) :=
                    rfl
        exact lt_of_lt_of_le hn hle)

/-- Same one-sided residual, stated against the checker-induced project length.
The project-length measurement is already definitionally the checker minimum on
the theorem-5 raw-code family, so this is the exact single-sided local target
for eliminating the root `proof_length` bridge. -/
theorem powerBoundLowerBound_to_checkedPowerBoundLowerBound_minProofCodeSize_of_actualLe_projectLength
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (fallback : _root_.FormulaCode → Nat)
    (actual_le_projectLength :
      ∀ n : Nat,
        actualProofLengthMeasured scale_data n ≤
          month9_month10_checkerProjectLengthMeasured
            scale_data sem fallback n)
    (hlower : scale_data.PowerBoundLowerBound) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data
      (fun n : Nat =>
        sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩) :=
  powerBoundLowerBound_to_checkedPowerBoundLowerBound_minProofCodeSize_of_actualLe_checkedMeasured
    scale_data sem
    (fun n => by
      calc
        actualProofLengthMeasured scale_data n
            ≤ month9_month10_checkerProjectLengthMeasured
                scale_data sem fallback n :=
              actual_le_projectLength n
        _ = month9_month10_checkedProofCodeMeasured scale_data sem n :=
              month9_month10_checkerProjectLengthMeasured_eq_checkedProofCodeMeasured
                scale_data sem fallback n)
    hlower

theorem powerBoundLowerBound_to_strictScaleSearchInput_nonempty_of_proofLengthLe
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (proof_length_le_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) ≤
          (lengthCodeAt n : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    Nonempty
      { input :
          ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
            scale_data //
        input.lengthCodeAt = lengthCodeAt } :=
  ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput.checkedPowerBoundLowerBound_to_strictScaleSearchInput_nonempty
    (scale_data := scale_data) lengthCodeAt scale_strict
    (powerBoundLowerBound_to_checkedPowerBoundLowerBound_of_proofLengthLe
      scale_data lengthCodeAt proof_length_le_lengthCodeAt hlower)

/-- Lower-machine closure under the one-sided proof-length domination residual.
This is strictly weaker than the older equality-calibration route and is the
right target for a concrete checker soundness theorem. -/
theorem powerBoundLowerBound_to_proofLengthFree_lower_bound_machine_closure_of_proofLengthLe
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (proof_length_le_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) ≤
          (lengthCodeAt n : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    let hchecked :=
      powerBoundLowerBound_to_checkedPowerBoundLowerBound_of_proofLengthLe
        scale_data lengthCodeAt proof_length_le_lengthCodeAt hlower
    let input :=
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput.ofCheckedPowerBoundLowerBound
        (scale_data := scale_data) lengthCodeAt scale_strict hchecked
    let core := input.toCanonicalSearchExactnessCore
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data core.checkerSemantics.toProofCodeSemantics
        core.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data core.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((core.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) =
          (input.gap.gap_for_polynomial_upper U hU).witness N) :=
  ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput.ofCheckedPowerBoundLowerBound_lower_bound_machine_closure
    (scale_data := scale_data) lengthCodeAt scale_strict
    (powerBoundLowerBound_to_checkedPowerBoundLowerBound_of_proofLengthLe
      scale_data lengthCodeAt proof_length_le_lengthCodeAt hlower)

/-- Project-length domination version of the lower-bound transfer.  The only
root residual is the one-sided statement that actual PA proof length is bounded
by the checker-induced `projectLength`; the rest is the existing
proof-length-free checker route. -/
theorem powerBoundLowerBound_to_proofLengthFree_lower_bound_machine_closure_of_actualLe_projectLength
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (fallback : _root_.FormulaCode → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (actual_le_projectLength :
      ∀ n : Nat,
        actualProofLengthMeasured scale_data n ≤
          month9_month10_checkerProjectLengthMeasured
            scale_data sem fallback n)
    (hlower : scale_data.PowerBoundLowerBound) :
    let lengthCodeAt :=
      fun n : Nat =>
        sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩
    let hchecked :=
      powerBoundLowerBound_to_checkedPowerBoundLowerBound_minProofCodeSize_of_actualLe_projectLength
        scale_data sem fallback actual_le_projectLength hlower
    let input :=
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput.ofCheckedPowerBoundLowerBound
        (scale_data := scale_data) lengthCodeAt scale_strict hchecked
    let core := input.toCanonicalSearchExactnessCore
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data core.checkerSemantics.toProofCodeSemantics
        core.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data core.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((core.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) =
          (input.gap.gap_for_polynomial_upper U hU).witness N) :=
  ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput.ofCheckedPowerBoundLowerBound_lower_bound_machine_closure
    (scale_data := scale_data)
    (fun n : Nat =>
      sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩)
    scale_strict
    (powerBoundLowerBound_to_checkedPowerBoundLowerBound_minProofCodeSize_of_actualLe_projectLength
      scale_data sem fallback actual_le_projectLength hlower)

/-- Exactness certificates imply the one-sided project-length domination needed
above.  This lemma deliberately uses only the already-proved local equality from
checker exactness to project length, then weakens it to `≤`. -/
theorem actualLeProjectLength_of_checkerProofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics scale_data}
    (exactness : InternalPudlakTheorem5CheckerProofLengthExactness checker)
    (fallback : _root_.FormulaCode → Nat) :
    ∀ n : Nat,
      actualProofLengthMeasured scale_data n ≤
        month9_month10_checkerProjectLengthMeasured
          scale_data checker.toProofCodeSemantics fallback n := by
  intro n
  have heq :
      actualProofLengthMeasured scale_data n =
        month9_month10_checkerProjectLengthMeasured
          scale_data checker.toProofCodeSemantics fallback n := by
    calc
      actualProofLengthMeasured scale_data n =
          _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) := rfl
      _ = (checker.minProofCodeSizeAt n : Real) :=
          exactness.at_powerBoundRawCode n
      _ = month9_month10_checkedProofCodeMeasured scale_data
            checker.toProofCodeSemantics n := by
          rfl
      _ = month9_month10_checkerProjectLengthMeasured scale_data
            checker.toProofCodeSemantics fallback n :=
          (month9_month10_checkerProjectLengthMeasured_eq_checkedProofCodeMeasured
            scale_data checker.toProofCodeSemantics fallback n).symm
  exact le_of_eq heq

/-- Local checker soundness-to-domination bridge.  If every proof code accepted
by the checker for the theorem-5 raw formula has size at least the root actual
PA proof length, then the root actual length is bounded by the checker minimum
proof-code size.  This is the concrete local obligation left after removing the
older equality calibration. -/
theorem actualLeCheckedMeasured_of_allCheckedCode_size_ge_actual
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (checked_code_size_ge_actual :
      ∀ n : Nat, ∀ c : sem.Code,
        sem.checks c (scale_data.powerBoundRawCode n) →
          actualProofLengthMeasured scale_data n ≤ (sem.size c : Real)) :
    ∀ n : Nat,
      actualProofLengthMeasured scale_data n ≤
        month9_month10_checkedProofCodeMeasured scale_data sem n := by
  intro n
  rcases sem.hasProofCodeOfSize_minProofCodeSize
      (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩ with
    ⟨c, hchecks, hsize_le_min⟩
  have hactual_le_size :
      actualProofLengthMeasured scale_data n ≤ (sem.size c : Real) :=
    checked_code_size_ge_actual n c hchecks
  have hsize_le_min :
      (sem.size c : Real) ≤
        (sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) := by
    exact_mod_cast hsize_le_min
  exact hactual_le_size.trans hsize_le_min

/-- Checker proof-length exactness implies the local all-accepted-code
soundness domination above.  This uses the already-proved minimum-size property
of `ProofCodeSemantics`; no new proof-length machinery is introduced. -/
theorem allCheckedCode_size_ge_actual_of_checkerProofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics scale_data}
    (exactness : InternalPudlakTheorem5CheckerProofLengthExactness checker) :
    ∀ n : Nat, ∀ c : checker.toProofCodeSemantics.Code,
      checker.toProofCodeSemantics.checks c (scale_data.powerBoundRawCode n) →
        actualProofLengthMeasured scale_data n ≤
          (checker.toProofCodeSemantics.size c : Real) := by
  intro n c hchecks
  let sem := checker.toProofCodeSemantics
  have hactual_eq_min :
      actualProofLengthMeasured scale_data n =
        (sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) := by
    simpa [actualProofLengthMeasured, sem,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt] using
      exactness.at_powerBoundRawCode n
  have hmin_le_size_nat :
      sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ ≤
        sem.size c :=
    sem.minProofCodeSize_le_of_hasProofCodeOfSize
      (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩
      ⟨c, hchecks, le_rfl⟩
  have hmin_le_size :
      (sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
        (sem.size c : Real) := by
    exact_mod_cast hmin_le_size_nat
  exact hactual_eq_min.le.trans hmin_le_size

theorem powerBoundLowerBound_to_checkedPowerBoundLowerBound_minProofCodeSize_of_allCheckedCode_size_ge_actual
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (checked_code_size_ge_actual :
      ∀ n : Nat, ∀ c : sem.Code,
        sem.checks c (scale_data.powerBoundRawCode n) →
          actualProofLengthMeasured scale_data n ≤ (sem.size c : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data
      (fun n : Nat =>
        sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩) :=
  powerBoundLowerBound_to_checkedPowerBoundLowerBound_minProofCodeSize_of_actualLe_checkedMeasured
    scale_data sem
    (actualLeCheckedMeasured_of_allCheckedCode_size_ge_actual
      scale_data sem checked_code_size_ge_actual)
    hlower

/-- Lower-machine closure from the local all-accepted-code soundness
domination.  This is the most local current residual: prove accepted checker
codes are genuine PA proof objects whose measured size cannot be below root PA
proof length, and Pudlak's lower bound reaches the proof-length-free search
machine. -/
theorem powerBoundLowerBound_to_proofLengthFree_lower_bound_machine_closure_of_allCheckedCode_size_ge_actual
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (checked_code_size_ge_actual :
      ∀ n : Nat, ∀ c : sem.Code,
        sem.checks c (scale_data.powerBoundRawCode n) →
          actualProofLengthMeasured scale_data n ≤ (sem.size c : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    let lengthCodeAt :=
      fun n : Nat =>
        sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩
    let hchecked :=
      powerBoundLowerBound_to_checkedPowerBoundLowerBound_minProofCodeSize_of_allCheckedCode_size_ge_actual
        scale_data sem checked_code_size_ge_actual hlower
    let input :=
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput.ofCheckedPowerBoundLowerBound
        (scale_data := scale_data) lengthCodeAt scale_strict hchecked
    let core := input.toCanonicalSearchExactnessCore
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data core.checkerSemantics.toProofCodeSemantics
        core.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data core.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((core.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) =
          (input.gap.gap_for_polynomial_upper U hU).witness N) :=
  powerBoundLowerBound_to_proofLengthFree_lower_bound_machine_closure_of_actualLe_projectLength
    scale_data sem (fun _ => 0) scale_strict
    (fun n =>
      calc
        actualProofLengthMeasured scale_data n
            ≤ month9_month10_checkedProofCodeMeasured scale_data sem n :=
              actualLeCheckedMeasured_of_allCheckedCode_size_ge_actual
                scale_data sem checked_code_size_ge_actual n
        _ = month9_month10_checkerProjectLengthMeasured
              scale_data sem (fun _ => 0) n :=
              (month9_month10_checkerProjectLengthMeasured_eq_checkedProofCodeMeasured
                scale_data sem (fun _ => 0) n).symm)
    hlower

namespace Month9Month10Month11ThreeCertificateHandoff

theorem actual_le_projectLength
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (fallback : _root_.FormulaCode → Nat) :
    ∀ n : Nat,
      actualProofLengthMeasured scale_data n ≤
        month9_month10_checkerProjectLengthMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics fallback n :=
  actualLeProjectLength_of_checkerProofLengthExactness
    h.proofLengthExactness fallback

/-- Existing three-certificate handoff, routed through the weaker one-sided
project-length domination bridge.  This shows the downstream lower machine only
needs the handoff's checker project length to dominate actual proof length; the
older equality calibration is stronger than necessary. -/
theorem powerBoundLowerBound_to_projectLengthDominated_lower_bound_machine_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (hlower : scale_data.PowerBoundLowerBound) :
    let sem := h.checkerSemantics.toProofCodeSemantics
    let lengthCodeAt :=
      fun n : Nat =>
        sem.minProofCodeSize (scale_data.powerBoundRawCode n) ⟨n, rfl⟩
    let hchecked :=
      powerBoundLowerBound_to_checkedPowerBoundLowerBound_minProofCodeSize_of_actualLe_projectLength
        scale_data sem fallback (h.actual_le_projectLength fallback) hlower
    let input :=
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput.ofCheckedPowerBoundLowerBound
        (scale_data := scale_data) lengthCodeAt h.scaleStrict hchecked
    let core := input.toCanonicalSearchExactnessCore
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data core.checkerSemantics.toProofCodeSemantics
        core.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data core.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((core.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) =
          (input.gap.gap_for_polynomial_upper U hU).witness N) :=
  powerBoundLowerBound_to_proofLengthFree_lower_bound_machine_closure_of_actualLe_projectLength
    scale_data h.checkerSemantics.toProofCodeSemantics fallback h.scaleStrict
    (h.actual_le_projectLength fallback) hlower

end Month9Month10Month11ThreeCertificateHandoff

/-- Exact residual bridge between the external theorem-5 power-bound statement
and the checked lower-bound target.  Once the family calibration
`proof_length(powerBoundRawCode n) = lengthCodeAt n` is supplied, Pudlak's
power-bound lower bound and the checked lower bound are definitionally the same
frequent lower-bound assertion.  This theorem deliberately exposes the remaining
root `proof_length` residual instead of hiding it in a larger package. -/
theorem powerBoundLowerBound_iff_checkedPowerBoundLowerBound_of_proofLengthEq
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :
    scale_data.PowerBoundLowerBound ↔
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
        scale_data lengthCodeAt := by
  constructor
  · intro hlower f hf
    exact
      (hlower.frequently_beats_every_polynomial f hf).mono
        (fun n hn => by
          have heq :
              _root_.proof_length _root_.ProofSystem.PA
                  _root_.ProofLengthMeasure.symbolSize
                  (scale_data.toLiteratureScaleData.powerBoundRawCode n) =
                (lengthCodeAt n : Real) := by
            simpa [InternalPudlakTheorem5ScaleData.powerBoundRawCode]
              using proof_length_eq_lengthCodeAt n
          rw [heq] at hn
          exact hn)
  · intro hchecked
    exact
      { frequently_beats_every_polynomial := by
          intro f hf
          exact
            (hchecked f hf).mono
              (fun n hn => by
                have heq :
                    _root_.proof_length _root_.ProofSystem.PA
                        _root_.ProofLengthMeasure.symbolSize
                        (scale_data.toLiteratureScaleData.powerBoundRawCode n) =
                      (lengthCodeAt n : Real) := by
                  simpa [InternalPudlakTheorem5ScaleData.powerBoundRawCode]
                    using proof_length_eq_lengthCodeAt n
                rw [heq]
                exact hn) }

theorem powerBoundLowerBound_to_checkedPowerBoundLowerBound_of_proofLengthEq
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data lengthCodeAt :=
  (powerBoundLowerBound_iff_checkedPowerBoundLowerBound_of_proofLengthEq
    scale_data lengthCodeAt proof_length_eq_lengthCodeAt).mp hlower

theorem checkedPowerBoundLowerBound_to_powerBoundLowerBound_of_proofLengthEq
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (hchecked :
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
        scale_data lengthCodeAt) :
    scale_data.PowerBoundLowerBound :=
  (powerBoundLowerBound_iff_checkedPowerBoundLowerBound_of_proofLengthEq
    scale_data lengthCodeAt proof_length_eq_lengthCodeAt).mpr hchecked

/-- Under the explicit proof-length calibration, the external theorem-5
power-bound lower-bound statement is equivalent to the proof-length-free
strict-scale singleton search-input route.  This packages the remaining hard
gap as the calibration
`proof_length(powerBoundRawCode n) = lengthCodeAt n`; the search-input side
itself is the clean PA/Hilbert checker route and does not add a new
`proof_length` field. -/
theorem powerBoundLowerBound_iff_nonempty_strictScaleSearchInput_of_proofLengthEq
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :
    scale_data.PowerBoundLowerBound ↔
      Nonempty
        { input :
            ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
              scale_data //
          input.lengthCodeAt = lengthCodeAt } := by
  have hchecked_search :
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
          scale_data lengthCodeAt ↔
        Nonempty
          { input :
              ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
                scale_data //
            input.lengthCodeAt = lengthCodeAt } :=
    ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput.checkedPowerBoundLowerBound_iff_nonempty_strictScaleSearchInput
      (scale_data := scale_data) lengthCodeAt scale_strict
  exact
    (powerBoundLowerBound_iff_checkedPowerBoundLowerBound_of_proofLengthEq
      scale_data lengthCodeAt proof_length_eq_lengthCodeAt).trans
      hchecked_search

theorem powerBoundLowerBound_to_strictScaleSearchInput_nonempty_of_proofLengthEq
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    Nonempty
      { input :
          ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
            scale_data //
        input.lengthCodeAt = lengthCodeAt } :=
  (powerBoundLowerBound_iff_nonempty_strictScaleSearchInput_of_proofLengthEq
    scale_data lengthCodeAt scale_strict proof_length_eq_lengthCodeAt).mp hlower

theorem strictScaleSearchInput_nonempty_to_powerBoundLowerBound_of_proofLengthEq
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (hinput :
      Nonempty
        { input :
            ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput
              scale_data //
          input.lengthCodeAt = lengthCodeAt }) :
    scale_data.PowerBoundLowerBound :=
  (powerBoundLowerBound_iff_nonempty_strictScaleSearchInput_of_proofLengthEq
    scale_data lengthCodeAt scale_strict proof_length_eq_lengthCodeAt).mpr hinput

/-- Direct bridge from the theorem-5 external power-bound lower-bound statement
to the proof-length-free lower-bound machine, with the sole residual written as
the explicit proof-length calibration.  The produced machine closure is the
same PA/Hilbert strict-scale singleton route used above: finite-search
exclusion, no-small proof codes, frequent minimum-code lower bound, and a
computable checked gap certificate. -/
theorem powerBoundLowerBound_to_proofLengthFree_lower_bound_machine_closure_of_proofLengthEq
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    let hchecked :=
      powerBoundLowerBound_to_checkedPowerBoundLowerBound_of_proofLengthEq
        scale_data lengthCodeAt proof_length_eq_lengthCodeAt hlower
    let input :=
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput.ofCheckedPowerBoundLowerBound
        (scale_data := scale_data) lengthCodeAt scale_strict hchecked
    let core := input.toCanonicalSearchExactnessCore
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data core.checkerSemantics.toProofCodeSemantics
        core.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data core.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (core.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data core.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((core.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) =
          (input.gap.gap_for_polynomial_upper U hU).witness N) :=
  ConcretePAHilbertPowerBoundStrictScaleSingletonGapSearchInput.ofCheckedPowerBoundLowerBound_lower_bound_machine_closure
    (scale_data := scale_data) lengthCodeAt scale_strict
    (powerBoundLowerBound_to_checkedPowerBoundLowerBound_of_proofLengthEq
      scale_data lengthCodeAt proof_length_eq_lengthCodeAt hlower)

namespace Month9Month10Month11ThreeCertificateHandoff

/-- Direct proof-length-free projection of the final three-certificate handoff.
This is the point where the generated checker, finite enumeration, and
rejection extractor are handed to the Month 9-10 lower-search machine without
using the root `proof_length` calibration. -/
def toProofLengthFreeExtractorHandoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    Month9Month10ProofLengthFreeExtractorHandoff scale_data where
  checkerSemantics :=
    h.checkerSemantics
  finiteEnumeration :=
    h.finiteEnumeration
  rejectionExtractor :=
    h.rejectionExtractor

theorem proofLengthFree_lower_bound_machine_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    InternalPudlakTheorem5FiniteSearchExclusion
        scale_data h.checkerSemantics.toProofCodeSemantics
        h.finiteEnumeration.toSmallCodeSearch ∧
      InternalPudlakTheorem5NoSmallProofCodes
        scale_data h.checkerSemantics.toProofCodeSemantics ∧
      (∀ f : Nat → Real, _root_.is_polynomial_bound f →
        ∃ᶠ n in Filter.atTop,
          (h.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            scale_data h.checkerSemantics.toProofCodeSemantics)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((h.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) =
          h.rejectionExtractor.witness U hU N) :=
  h.toProofLengthFreeExtractorHandoff
    |>.proofLengthFree_lower_bound_machine_closure

/-- Full proof-length-free collision trace for the final three-certificate
handoff.  The same generated rejection extractor controls the lower-search
witness and the checked-measured contradiction; root `proof_length` is not used
in this closure. -/
theorem proofLengthFree_full_lower_search_collision_trace
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data h.checkerSemantics.toProofCodeSemantics)) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let upper :=
        h.toProofLengthFreeExtractorHandoff.upperTailOfRationality
          upper_provider hrat
      let w :=
        h.toProofLengthFreeExtractorHandoff.lowerSearchWitnessOfUpper
          upper
      w.n =
          h.toProofLengthFreeExtractorHandoff.computedNOfRationality
            upper_provider hrat ∧
        w.K = h.rejectionExtractor.cutoff
          upper.U upper.polynomial upper.upperN ∧
        upper.upperN ≤ w.n ∧
        upper.U w.n < (w.K : Real) ∧
        (∀ c : h.checkerSemantics.Code,
          c ∈ h.finiteEnumeration.candidates w.n w.K →
            ¬ h.checkerSemantics.checks c
              (scale_data.powerBoundRawCode w.n)) ∧
        (∀ c : h.checkerSemantics.Code,
          h.checkerSemantics.checks c
            (scale_data.powerBoundRawCode w.n) →
            upper.U w.n < (h.checkerSemantics.size c : Real)) ∧
        (h.checkerSemantics.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ : Real) >
          upper.U w.n ∧
        upper.U w.n <
          month9_month10_checkedProofCodeMeasured
            scale_data h.checkerSemantics.toProofCodeSemantics w.n ∧
        month9_month10_checkedProofCodeMeasured
            scale_data h.checkerSemantics.toProofCodeSemantics w.n ≤
          upper.U w.n ∧
        False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toProofLengthFreeExtractorHandoff
    |>.proofLengthFree_full_lower_search_collision_trace upper_provider

end Month9Month10Month11ThreeCertificateHandoff

/-- The only place where a checker minimum becomes root proof length on the
theorem-5 raw family.  Keeping this as a separate bridge prevents the checked
collision kernel from depending on `proof_length`. -/
structure Month9Month10CheckedMeasuredToActualProofLengthBridge
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Prop where
  checked_eq_actual :
    ∀ n : Nat,
      month9_month10_checkedProofCodeMeasured scale_data sem n =
        actualProofLengthMeasured scale_data n

namespace Month9Month10CheckedMeasuredToActualProofLengthBridge

def ofCheckerProofLengthFamilyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
      scale_data checker.toProofCodeSemantics where
  checked_eq_actual := by
    intro n
    simpa [month9_month10_checkedProofCodeMeasured,
      actualProofLengthMeasured,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
      using (family.proof_length_eq_minProofCodeSizeAt n).symm

def ofCheckerProofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
      scale_data checker.toProofCodeSemantics :=
  ofCheckerProofLengthFamilyExactness
    (InternalPudlakTheorem5CheckerProofLengthFamilyExactness.ofCheckerProofLengthExactness
      exactness)

theorem ofCheckerProofLengthExactness_checked_eq_actual
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker)
    (n : Nat) :
    (ofCheckerProofLengthExactness exactness).checked_eq_actual n =
      (by
        simpa [month9_month10_checkedProofCodeMeasured,
          actualProofLengthMeasured,
          InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
          using (exactness.at_powerBoundRawCode n).symm) :=
  rfl

def transportGapToActualProofLength
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data sem)
    (gap :
      ComputableSearchGapCertificate
        (month9_month10_checkedProofCodeMeasured scale_data sem)) :
    ComputableSearchGapCertificate (actualProofLengthMeasured scale_data) :=
  transportComputableSearchGap bridge.checked_eq_actual gap

def transportUpperToActualProofLength
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data sem)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured scale_data sem)) :
    Month9Month10AbstractMeasuredUpperProvider
      (actualProofLengthMeasured scale_data) :=
  Month9Month10AbstractMeasuredUpperProvider.transportEq
    bridge.checked_eq_actual upper_provider

def transportUpperToCheckedMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data sem)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    Month9Month10AbstractMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured scale_data sem) :=
  Month9Month10AbstractMeasuredUpperProvider.transportEq
    (fun n => (bridge.checked_eq_actual n).symm) upper_provider

theorem transportGapToActualProofLength_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data sem)
    (gap :
      ComputableSearchGapCertificate
        (month9_month10_checkedProofCodeMeasured scale_data sem))
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((bridge.transportGapToActualProofLength gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      (gap.gap_for_polynomial_upper U hU).witness N :=
  rfl

theorem transportUpperToActualProofLength_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data sem)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured scale_data sem)) :
    (bridge.transportUpperToActualProofLength upper_provider).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              actualProofLengthMeasured scale_data n ≤ U n) :=
  (bridge.transportUpperToActualProofLength upper_provider).closure

theorem transportUpperToCheckedMeasured_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data sem)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    (bridge.transportUpperToCheckedMeasured upper_provider).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              month9_month10_checkedProofCodeMeasured scale_data sem n ≤ U n) :=
  (bridge.transportUpperToCheckedMeasured upper_provider).closure

end Month9Month10CheckedMeasuredToActualProofLengthBridge

/-! ## Calibrated proof-length exactness as checked/actual transport -/

/-- For the concrete calibrated PA/Hilbert checker, the calibrated
proof-length input is exactly the checked-measured-to-actual bridge restated
pointwise on `powerBoundRawCode`. -/
def calibratedProofLengthInputOfCheckedMeasuredToActualBridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics) :
    ConcretePAHilbertPowerBoundCalibratedProofLengthInput
      scale_data lengthCodeAt where
  proof_length_eq_minProofCodeSizeAt := by
    intro n
    simpa [month9_month10_checkedProofCodeMeasured,
      actualProofLengthMeasured,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
      using (bridge.checked_eq_actual n).symm

/-- Conversely, the calibrated proof-length input supplies exactly the
checked-measured-to-actual bridge for the concrete calibrated checker. -/
def checkedMeasuredToActualBridgeOfCalibratedProofLengthInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (proof_length :
      ConcretePAHilbertPowerBoundCalibratedProofLengthInput
        scale_data lengthCodeAt) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt).toProofCodeSemantics :=
  Month9Month10CheckedMeasuredToActualProofLengthBridge.ofCheckerProofLengthExactness
    proof_length.toCheckerExactness

/-- Equivalence audit for the concrete calibrated proof-length residual.  The
remaining proof-length blocker can be attacked as either the calibrated
proof-length input or the checked/actual transport bridge; they are the same
obligation. -/
theorem calibratedProofLengthInput_iff_checkedMeasuredToActualBridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat} :
    Nonempty
        (ConcretePAHilbertPowerBoundCalibratedProofLengthInput
          scale_data lengthCodeAt) ↔
      Nonempty
        (Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data lengthCodeAt).toProofCodeSemantics) := by
  constructor
  · intro h
    rcases h with ⟨proof_length⟩
    exact
      ⟨checkedMeasuredToActualBridgeOfCalibratedProofLengthInput
        proof_length⟩
  · intro h
    rcases h with ⟨bridge⟩
    exact
      ⟨calibratedProofLengthInputOfCheckedMeasuredToActualBridge
        bridge⟩

namespace Month9Month10Month11ThreeCertificateHandoff

def checkedMeasuredToActualBridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
      scale_data h.checkerSemantics.toProofCodeSemantics :=
  Month9Month10CheckedMeasuredToActualProofLengthBridge.ofCheckerProofLengthExactness
    h.proofLengthExactness

def transportedActualGapFromChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    ComputableSearchGapCertificate (actualProofLengthMeasured scale_data) :=
  h.checkedMeasuredToActualBridge.transportGapToActualProofLength
    h.toProofLengthFreeExtractorHandoff.checkedMeasuredGap

theorem transportedActualGapFromChecked_witness_eq_rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((h.transportedActualGapFromChecked
        |>.gap_for_polynomial_upper U hU).witness N) =
      h.rejectionExtractor.witness U hU N := by
  calc
    ((h.transportedActualGapFromChecked
        |>.gap_for_polynomial_upper U hU).witness N)
        =
          ((h.toProofLengthFreeExtractorHandoff.checkedMeasuredGap
            |>.gap_for_polynomial_upper U hU).witness N) := by
            simpa [transportedActualGapFromChecked] using
              h.checkedMeasuredToActualBridge
                |>.transportGapToActualProofLength_witness_eq
                  h.toProofLengthFreeExtractorHandoff.checkedMeasuredGap U hU N
    _ = h.rejectionExtractor.witness U hU N :=
        h.toProofLengthFreeExtractorHandoff
          |>.checkedMeasuredGap_witness_eq_rejectionExtractor U hU N

theorem transportedActualGapFromChecked_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data) :
    Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
      (∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        ((h.transportedActualGapFromChecked
          |>.gap_for_polynomial_upper U hU).witness N) =
          h.rejectionExtractor.witness U hU N) :=
  ⟨⟨h.transportedActualGapFromChecked⟩,
    h.transportedActualGapFromChecked_witness_eq_rejectionExtractor⟩

end Month9Month10Month11ThreeCertificateHandoff

/-- Transport any project-box upper route to the theorem-5 checked source
measurement using an additive projection
`source <= projectBox + overhead`.  The resulting upper function is
`U + overhead`, still polynomial by `shiftedUpper_polynomial`. -/
def checkedUpperProviderOfProjectBoxUpperAndAdditiveProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    Month9Month10AbstractMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured scale_data sem) where
  upper_under_rationality := by
    intro hrat
    rcases project_box_upper_provider.upper_under_rationality hrat with
      ⟨U, hU, upperN, hupper⟩
    refine
      ⟨projection.shiftedUpper U,
        projection.shiftedUpper_polynomial U hU,
        upperN,
        ?_⟩
    intro n hn
    have hsource := projection.source_le_project_add n
    have hproject := hupper n hn
    have hchecked :
        (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
          U n + projection.overhead :=
      by nlinarith
    simpa [
      month9_month10_checkedProofCodeMeasured,
      InternalPudlakTheorem5AdditiveProjectBoxProjection.shiftedUpper]
      using hchecked

theorem checkedUpperProviderOfProjectBoxUpperAndAdditiveProjection_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    (checkedUpperProviderOfProjectBoxUpperAndAdditiveProjection
      projection project_box_upper_provider).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              month9_month10_checkedProofCodeMeasured scale_data sem n ≤ U n) :=
  (checkedUpperProviderOfProjectBoxUpperAndAdditiveProjection
    projection project_box_upper_provider).closure

/-- S²₁-collapse specialization of the project-box upper transport.  The
accepted-certificate side condition stays inside
`projectBoxUpperProviderOfS21Collapse`; the additive projection itself only
uses the exported project-box upper tail. -/
def checkedUpperProviderOfProjectUpperAndAdditiveProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10AbstractMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured scale_data sem) :=
  checkedUpperProviderOfProjectBoxUpperAndAdditiveProjection
    projection (projectBoxUpperProviderOfS21Collapse project_upper)

theorem checkedUpperProviderOfProjectUpperAndAdditiveProjection_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (checkedUpperProviderOfProjectUpperAndAdditiveProjection
      projection project_upper).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              month9_month10_checkedProofCodeMeasured scale_data sem n ≤ U n) :=
  (checkedUpperProviderOfProjectUpperAndAdditiveProjection
    projection project_upper).closure

/-- Full upper-provider adapter from an already-isolated project-box upper route
to the corrected actual route. -/
def actualUpperProviderOfProjectBoxUpperAndAdditiveProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data sem)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    Month9Month10AbstractMeasuredUpperProvider
      (actualProofLengthMeasured scale_data) :=
  bridge.transportUpperToActualProofLength
    (checkedUpperProviderOfProjectBoxUpperAndAdditiveProjection
      projection project_box_upper_provider)

theorem actualUpperProviderOfProjectBoxUpperAndAdditiveProjection_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data sem)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    (actualUpperProviderOfProjectBoxUpperAndAdditiveProjection
      projection bridge project_box_upper_provider).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              actualProofLengthMeasured scale_data n ≤ U n) :=
  (actualUpperProviderOfProjectBoxUpperAndAdditiveProjection
    projection bridge project_box_upper_provider).closure

/-- Full upper-provider adapter for the corrected actual route: first use the
additive project-box projection to move the Sondow project upper tail to the
checked theorem-5 source measurement, then use the checker/actual proof-length
bridge to state the same upper tail over `actualProofLengthMeasured`. -/
def actualUpperProviderOfProjectUpperAndAdditiveProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data sem)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10AbstractMeasuredUpperProvider
      (actualProofLengthMeasured scale_data) :=
  actualUpperProviderOfProjectBoxUpperAndAdditiveProjection
    projection bridge (projectBoxUpperProviderOfS21Collapse project_upper)

theorem actualUpperProviderOfProjectUpperAndAdditiveProjection_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data sem)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (actualUpperProviderOfProjectUpperAndAdditiveProjection
      projection bridge project_upper).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              actualProofLengthMeasured scale_data n ≤ U n) :=
  (actualUpperProviderOfProjectUpperAndAdditiveProjection
    projection bridge project_upper).closure

structure Month9Month10CheckedMeasuredKernelChecklist : Prop where
  checkedMeasuredClosure :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ h : Month9Month10CheckedMeasuredDirectCollisionEndpoint scale_data,
        h.Audit ∧
          h.toAbstractMeasuredEndpoint.Audit ∧
            (∀ n : Nat,
              month9_month10_checkedProofCodeMeasured scale_data h.sem n =
                (h.sem.minProofCodeSize (scale_data.powerBoundRawCode n)
                  ⟨n, rfl⟩ : Real)) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                h.computedCollisionNOfRationality hrat =
                  (h.gap.gap_for_polynomial_upper
                    (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                    (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
                      (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
                (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                  False) ∧
                  ¬ _root_.is_rational _root_.euler_mascheroni
  checkedToActualTransport :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ sem :
        _root_.ProofCodeSemantics.{0}
          (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
        ∀ bridge :
          Month9Month10CheckedMeasuredToActualProofLengthBridge
            scale_data sem,
          ∀ gap :
            ComputableSearchGapCertificate
              (month9_month10_checkedProofCodeMeasured scale_data sem),
            Nonempty
              (ComputableSearchGapCertificate
                (actualProofLengthMeasured scale_data)) ∧
              (∀ U : Nat → Real,
                ∀ hU : _root_.is_polynomial_bound U,
                  ∀ N : Nat,
                    ((bridge.transportGapToActualProofLength gap)
                      |>.gap_for_polynomial_upper U hU).witness N =
                      (gap.gap_for_polynomial_upper U hU).witness N)
  checkedUpperToActualTransport :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ sem :
        _root_.ProofCodeSemantics.{0}
          (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
        ∀ bridge :
          Month9Month10CheckedMeasuredToActualProofLengthBridge
            scale_data sem,
          ∀ upper_provider :
            Month9Month10AbstractMeasuredUpperProvider
              (month9_month10_checkedProofCodeMeasured scale_data sem),
            (bridge.transportUpperToActualProofLength
              upper_provider).Audit ∧
              (_root_.is_rational _root_.euler_mascheroni →
                ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
                  ∃ upperN : Nat,
                    ∀ n : Nat, upperN ≤ n →
                      actualProofLengthMeasured scale_data n ≤ U n)
  actualUpperToCheckedTransport :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ sem :
        _root_.ProofCodeSemantics.{0}
          (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
        ∀ bridge :
          Month9Month10CheckedMeasuredToActualProofLengthBridge
            scale_data sem,
          ∀ upper_provider :
            Month9Month10AbstractMeasuredUpperProvider
              (actualProofLengthMeasured scale_data),
            (bridge.transportUpperToCheckedMeasured
              upper_provider).Audit ∧
              (_root_.is_rational _root_.euler_mascheroni →
                ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
                  ∃ upperN : Nat,
                    ∀ n : Nat, upperN ≤ n →
                      month9_month10_checkedProofCodeMeasured
                        scale_data sem n ≤ U n)

theorem month9_month10_checked_measured_kernel_checklist :
    Month9Month10CheckedMeasuredKernelChecklist where
  checkedMeasuredClosure := by
    intro scale_data h
    exact h.closure
  checkedToActualTransport := by
    intro scale_data sem bridge gap
    exact
      ⟨⟨bridge.transportGapToActualProofLength gap⟩,
        bridge.transportGapToActualProofLength_witness_eq gap⟩
  checkedUpperToActualTransport := by
    intro scale_data sem bridge upper_provider
    exact
      bridge.transportUpperToActualProofLength_closure upper_provider
  actualUpperToCheckedTransport := by
    intro scale_data sem bridge upper_provider
    exact
      bridge.transportUpperToCheckedMeasured_closure upper_provider

/-! ## No-small-core proof-length exactness factorization -/

namespace Month9Month10Month11NoSmallCoreHandoff

def proofCodeSemantics
    (h : Month9Month10Month11NoSmallCoreHandoff) :
    _root_.ProofCodeSemantics.{0}
      (InternalPudlakTheorem5PowerBoundRelevantCode h.scale_data) :=
  h.core.proof_length_model.proof_code_semantics

/-- Checked-measured search gap extracted directly from the no-small-code
search core, before any `proof_length` calibration is used. -/
def checkedMeasuredGap
    (h : Month9Month10Month11NoSmallCoreHandoff) :
    ComputableSearchGapCertificate
      (month9_month10_checkedProofCodeMeasured
        h.scale_data (proofCodeSemantics h)) := by
  simpa [proofCodeSemantics, scale_data] using
    (month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
      h.core.computable_search_exclusion)

theorem checkedMeasuredGap_witness_eq_core
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((checkedMeasuredGap h |>.gap_for_polynomial_upper U hU).witness N) =
      h.core.computable_search_exclusion.witness U hU N :=
  rfl

/-- The proof-length exactness bridge for the no-small-core route.  This is the
single calibration point turning checker minimum size into actual PA
`proof_length` on the theorem-5 raw family. -/
def checkedMeasuredToActualBridge
    (h : Month9Month10Month11NoSmallCoreHandoff) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
      h.scale_data (proofCodeSemantics h) where
  checked_eq_actual := by
    intro n
    have hcal := h.proofLengthFrontier.proof_length_eq_minProofCodeSize n
    simpa [month9_month10_checkedProofCodeMeasured,
      proofCodeSemantics, actualProofLengthMeasured, scale_data,
      proofLengthFrontier,
      Month9Month10ComputableNoSmallProofLengthFrontier.scale_data,
      InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.proof_code_semantics]
      using hcal.symm

def transportedActualGapFromChecked
    (h : Month9Month10Month11NoSmallCoreHandoff) :
    ComputableSearchGapCertificate
      (actualProofLengthMeasured h.scale_data) :=
  (checkedMeasuredToActualBridge h).transportGapToActualProofLength
    (checkedMeasuredGap h)

theorem transportedActualGapFromChecked_witness_eq_core
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((transportedActualGapFromChecked h |>.gap_for_polynomial_upper
      U hU).witness N) =
      h.core.computable_search_exclusion.witness U hU N := by
  calc
    ((transportedActualGapFromChecked h |>.gap_for_polynomial_upper
        U hU).witness N)
        = ((checkedMeasuredGap h |>.gap_for_polynomial_upper U hU).witness N) := by
          simpa [transportedActualGapFromChecked] using
            ((checkedMeasuredToActualBridge h)
              |>.transportGapToActualProofLength_witness_eq
                (checkedMeasuredGap h) U hU N)
    _ = h.core.computable_search_exclusion.witness U hU N :=
        checkedMeasuredGap_witness_eq_core h U hU N

theorem transportedActualGapFromChecked_witness_eq_actual
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((transportedActualGapFromChecked h |>.gap_for_polynomial_upper
      U hU).witness N) =
      ((h.actualProofLengthGap.gap_for_polynomial_upper U hU).witness N) := by
  calc
    ((transportedActualGapFromChecked h |>.gap_for_polynomial_upper
        U hU).witness N)
        = h.core.computable_search_exclusion.witness U hU N :=
          transportedActualGapFromChecked_witness_eq_core h U hU N
    _ = ((h.actualProofLengthGap.gap_for_polynomial_upper U hU).witness N) :=
          (h.actual_gap_witness_eq_core U hU N).symm

structure ProofLengthExactnessFactorAudit
    (h : Month9Month10Month11NoSmallCoreHandoff) : Prop where
  checkedMeasuredSearchGap :
    Nonempty
      (ComputableSearchGapCertificate
        (month9_month10_checkedProofCodeMeasured
          h.scale_data (proofCodeSemantics h)))
  checkedToActualBridge :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
      h.scale_data (proofCodeSemantics h)
  transportedActualGap :
    Nonempty
      (ComputableSearchGapCertificate
        (actualProofLengthMeasured h.scale_data))
  checkedWitnessEqCore :
    ∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
      ((checkedMeasuredGap h |>.gap_for_polynomial_upper U hU).witness N) =
        h.core.computable_search_exclusion.witness U hU N
  transportedWitnessEqCore :
    ∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
      ((transportedActualGapFromChecked h |>.gap_for_polynomial_upper
        U hU).witness N) =
        h.core.computable_search_exclusion.witness U hU N
  transportedWitnessEqActual :
    ∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
      ((transportedActualGapFromChecked h |>.gap_for_polynomial_upper
        U hU).witness N) =
        ((h.actualProofLengthGap.gap_for_polynomial_upper U hU).witness N)

theorem proofLengthExactnessFactorAudit
    (h : Month9Month10Month11NoSmallCoreHandoff) :
    ProofLengthExactnessFactorAudit h where
  checkedMeasuredSearchGap := ⟨checkedMeasuredGap h⟩
  checkedToActualBridge := checkedMeasuredToActualBridge h
  transportedActualGap := ⟨transportedActualGapFromChecked h⟩
  checkedWitnessEqCore := checkedMeasuredGap_witness_eq_core h
  transportedWitnessEqCore := transportedActualGapFromChecked_witness_eq_core h
  transportedWitnessEqActual :=
    transportedActualGapFromChecked_witness_eq_actual h

theorem proof_length_exactness_factor_closure
    (h : Month9Month10Month11NoSmallCoreHandoff) :
    ProofLengthExactnessFactorAudit h ∧
      Nonempty
        (ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured
            h.scale_data (proofCodeSemantics h))) ∧
        Month9Month10CheckedMeasuredToActualProofLengthBridge
          h.scale_data (proofCodeSemantics h) ∧
          Nonempty
            (ComputableSearchGapCertificate
              (actualProofLengthMeasured h.scale_data)) ∧
            (∀ U : Nat → Real,
              ∀ hU : _root_.is_polynomial_bound U,
                ∀ N : Nat,
                  ((transportedActualGapFromChecked h |>.gap_for_polynomial_upper
                    U hU).witness N) =
                    ((h.actualProofLengthGap.gap_for_polynomial_upper
                      U hU).witness N)) :=
  ⟨proofLengthExactnessFactorAudit h,
    ⟨checkedMeasuredGap h⟩,
    checkedMeasuredToActualBridge h,
    ⟨transportedActualGapFromChecked h⟩,
    transportedActualGapFromChecked_witness_eq_actual h⟩

end Month9Month10Month11NoSmallCoreHandoff

/-! ## Actual proof-length measured endpoint -/

/-- Direct endpoint over the actual PA proof-length measurement of the theorem-5
raw family.  This endpoint is narrower than the project reflection-graft
endpoint: it only computes a contradiction when the upper route is already
stated over `actualProofLengthMeasured scale_data`.  The bridge from the
project Sondow upper route remains a separate projection certificate. -/
structure Month9Month10ActualProofLengthDirectCollisionEndpoint
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  gap :
    ComputableSearchGapCertificate (actualProofLengthMeasured scale_data)
  upper_provider :
    Month9Month10AbstractMeasuredUpperProvider
      (actualProofLengthMeasured scale_data)

namespace Month9Month10ActualProofLengthDirectCollisionEndpoint

def toAbstractMeasuredEndpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (actualProofLengthMeasured scale_data) where
  gap := h.gap
  upper_provider := h.upper_provider

noncomputable def computedCollisionNOfRationality
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  h.toAbstractMeasuredEndpoint.computedCollisionNOfRationality hrat

theorem computedCollisionN_eq_searchGapWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      (h.gap.gap_for_polynomial_upper
        (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
          (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN :=
  h.toAbstractMeasuredEndpoint.computedCollisionN_eq_searchGapWitness hrat

theorem computedCollisionN_ge_upperN
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN ≤
      h.computedCollisionNOfRationality hrat :=
  h.toAbstractMeasuredEndpoint.computedCollisionN_ge_upperN hrat

theorem lower_at_computedCollisionN
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (h.computedCollisionNOfRationality hrat) <
      actualProofLengthMeasured scale_data
        (h.computedCollisionNOfRationality hrat) :=
  h.toAbstractMeasuredEndpoint.lower_at_computedCollisionN hrat

theorem upper_at_computedCollisionN
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    actualProofLengthMeasured scale_data
        (h.computedCollisionNOfRationality hrat) ≤
      (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (h.computedCollisionNOfRationality hrat) :=
  h.toAbstractMeasuredEndpoint.upper_at_computedCollisionN hrat

theorem computed_n_contradiction
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.toAbstractMeasuredEndpoint.computed_n_contradiction hrat

theorem not_rational
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toAbstractMeasuredEndpoint.not_rational

theorem not_rational_eq_generic_core
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data) :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational
        h.toAbstractMeasuredEndpoint.toGenericCollisionInputs :=
  h.toAbstractMeasuredEndpoint.not_rational_eq_generic_core

structure Audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data) :
    Prop where
  abstractMeasuredAudit : h.toAbstractMeasuredEndpoint.Audit
  actualProofLengthGap :
    Nonempty
      (ComputableSearchGapCertificate (actualProofLengthMeasured scale_data))
  upperProviderAudit : h.upper_provider.Audit
  computedWitnessFormula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        (h.gap.gap_for_polynomial_upper
          (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
          (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
            (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN
  lowerAtComputedN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
          (h.computedCollisionNOfRationality hrat) <
        actualProofLengthMeasured scale_data
          (h.computedCollisionNOfRationality hrat)
  upperAtComputedN :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      actualProofLengthMeasured scale_data
          (h.computedCollisionNOfRationality hrat) ≤
        (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
          (h.computedCollisionNOfRationality hrat)
  contradictionAtComputedN :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  notRationalEqGenericCore :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational
        h.toAbstractMeasuredEndpoint.toGenericCollisionInputs
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data) :
    h.Audit where
  abstractMeasuredAudit := h.toAbstractMeasuredEndpoint.audit
  actualProofLengthGap := ⟨h.gap⟩
  upperProviderAudit := h.upper_provider.audit
  computedWitnessFormula := h.computedCollisionN_eq_searchGapWitness
  lowerAtComputedN := h.lower_at_computedCollisionN
  upperAtComputedN := h.upper_at_computedCollisionN
  contradictionAtComputedN := h.computed_n_contradiction
  notRationalEqGenericCore := h.not_rational_eq_generic_core
  endpointNotRational := h.not_rational

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data) :
    h.Audit ∧
      h.toAbstractMeasuredEndpoint.Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured scale_data)) ∧
          h.upper_provider.Audit ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              h.computedCollisionNOfRationality hrat =
                (h.gap.gap_for_polynomial_upper
                  (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                  (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
                    (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                    (h.computedCollisionNOfRationality hrat) <
                  actualProofLengthMeasured scale_data
                    (h.computedCollisionNOfRationality hrat)) ∧
                (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                  actualProofLengthMeasured scale_data
                      (h.computedCollisionNOfRationality hrat) ≤
                    (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                      (h.computedCollisionNOfRationality hrat)) ∧
                  (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                    False) ∧
                    ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨h.audit,
    h.toAbstractMeasuredEndpoint.audit,
    ⟨h.gap⟩,
    h.upper_provider.audit,
    h.computedCollisionN_eq_searchGapWitness,
    h.lower_at_computedCollisionN,
    h.upper_at_computedCollisionN,
    h.computed_n_contradiction,
    h.not_rational⟩

end Month9Month10ActualProofLengthDirectCollisionEndpoint

theorem month9_month10_actual_proof_length_direct_collision_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data) :
    h.Audit ∧
      h.toAbstractMeasuredEndpoint.Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured scale_data)) ∧
          h.upper_provider.Audit ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              h.computedCollisionNOfRationality hrat =
                (h.gap.gap_for_polynomial_upper
                  (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                  (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
                    (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                    (h.computedCollisionNOfRationality hrat) <
                  actualProofLengthMeasured scale_data
                    (h.computedCollisionNOfRationality hrat)) ∧
                (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                  actualProofLengthMeasured scale_data
                      (h.computedCollisionNOfRationality hrat) ≤
                    (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                      (h.computedCollisionNOfRationality hrat)) ∧
                  (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                    False) ∧
                    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.closure

namespace Month9Month10Month11ThreeCertificateHandoff

/-- Final three-certificate handoff assembled with an arbitrary actual
proof-length upper provider.  This isolates the actual-gap/rejection-witness
transport from any particular source of the upper tail. -/
def actualEndpointOfActualUpperProvider
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data where
  gap := h.transportedActualGapFromChecked
  upper_provider := upper_provider

theorem actualEndpointOfActualUpperProvider_computedN_eq_rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let endpoint :=
      h.actualEndpointOfActualUpperProvider upper_provider
    endpoint.computedCollisionNOfRationality hrat =
      h.rejectionExtractor.witness
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN := by
  let endpoint := h.actualEndpointOfActualUpperProvider upper_provider
  have hcomputed :
      endpoint.computedCollisionNOfRationality hrat =
        (endpoint.gap.gap_for_polynomial_upper
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
            (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN :=
    endpoint.computedCollisionN_eq_searchGapWitness hrat
  have hwitness :
      ((h.transportedActualGapFromChecked |>.gap_for_polynomial_upper
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
            (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) =
        h.rejectionExtractor.witness
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN :=
    h.transportedActualGapFromChecked_witness_eq_rejectionExtractor
      (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
      (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
      (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN
  exact hcomputed.trans (by
    simpa [endpoint, actualEndpointOfActualUpperProvider] using hwitness)

theorem actualEndpointOfActualUpperProvider_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    let endpoint :=
      h.actualEndpointOfActualUpperProvider upper_provider
    endpoint.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
        endpoint.upper_provider.Audit ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            endpoint.computedCollisionNOfRationality hrat =
              h.rejectionExtractor.witness
                (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
                (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni := by
  let endpoint := h.actualEndpointOfActualUpperProvider upper_provider
  exact
    ⟨endpoint.audit,
      ⟨endpoint.gap⟩,
      endpoint.upper_provider.audit,
      h.actualEndpointOfActualUpperProvider_computedN_eq_rejectionExtractor
        upper_provider,
      endpoint.computed_n_contradiction,
      endpoint.not_rational⟩

/-- Three-certificate actual endpoint assembled from an already-isolated
project-box upper provider.  This is the payload-free upper-source boundary for
the actual proof-length collision route. -/
def actualEndpointOfProjectBoxUpperAndAdditiveProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data h.checkerSemantics.toProofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data :=
  h.actualEndpointOfActualUpperProvider
    (actualUpperProviderOfProjectBoxUpperAndAdditiveProjection
      projection h.checkedMeasuredToActualBridge project_box_upper_provider)

theorem actualEndpointOfProjectBoxUpperAndAdditiveProjection_computedN_eq_rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data h.checkerSemantics.toProofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let endpoint :=
      h.actualEndpointOfProjectBoxUpperAndAdditiveProjection
        projection project_box_upper_provider
    endpoint.computedCollisionNOfRationality hrat =
      h.rejectionExtractor.witness
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN := by
  simpa [actualEndpointOfProjectBoxUpperAndAdditiveProjection] using
    h.actualEndpointOfActualUpperProvider_computedN_eq_rejectionExtractor
      (actualUpperProviderOfProjectBoxUpperAndAdditiveProjection
        projection h.checkedMeasuredToActualBridge project_box_upper_provider)
      hrat

theorem actualEndpointOfProjectBoxUpperAndAdditiveProjection_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data h.checkerSemantics.toProofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    let endpoint :=
      h.actualEndpointOfProjectBoxUpperAndAdditiveProjection
        projection project_box_upper_provider
    endpoint.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
        endpoint.upper_provider.Audit ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            endpoint.computedCollisionNOfRationality hrat =
              h.rejectionExtractor.witness
                (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
                (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [actualEndpointOfProjectBoxUpperAndAdditiveProjection] using
    h.actualEndpointOfActualUpperProvider_closure
      (actualUpperProviderOfProjectBoxUpperAndAdditiveProjection
        projection h.checkedMeasuredToActualBridge project_box_upper_provider)

/-- Final three-certificate handoff assembled into the actual proof-length
endpoint using the existing checked/actual bridge and additive project-box
upper projection. -/
def actualEndpointOfProjectUpperAndAdditiveProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data h.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data :=
  h.actualEndpointOfProjectBoxUpperAndAdditiveProjection
    projection (projectBoxUpperProviderOfS21Collapse project_upper)

theorem actualEndpointOfProjectUpperAndAdditiveProjection_computedN_eq_rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data h.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let endpoint :=
      h.actualEndpointOfProjectUpperAndAdditiveProjection
        projection project_upper
    endpoint.computedCollisionNOfRationality hrat =
      h.rejectionExtractor.witness
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN := by
  simpa [actualEndpointOfProjectUpperAndAdditiveProjection] using
    h.actualEndpointOfProjectBoxUpperAndAdditiveProjection_computedN_eq_rejectionExtractor
      projection (projectBoxUpperProviderOfS21Collapse project_upper) hrat

theorem actualEndpointOfProjectUpperAndAdditiveProjection_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10Month11ThreeCertificateHandoff scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data h.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      h.actualEndpointOfProjectUpperAndAdditiveProjection
        projection project_upper
    endpoint.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
        endpoint.upper_provider.Audit ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            endpoint.computedCollisionNOfRationality hrat =
              h.rejectionExtractor.witness
                (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
                (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [actualEndpointOfProjectUpperAndAdditiveProjection] using
    h.actualEndpointOfProjectBoxUpperAndAdditiveProjection_closure
      projection (projectBoxUpperProviderOfS21Collapse project_upper)

end Month9Month10Month11ThreeCertificateHandoff

def Month9Month10Month11NoSmallCoreHandoff.toActualProofLengthDirectEndpoint
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured h.scale_data)) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint h.scale_data where
  gap := h.actualProofLengthGap
  upper_provider := upper_provider

def Month9Month10Month11NoSmallCoreHandoff.actualEndpointOfProjectBoxUpperAndAdditiveProjection
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        h.scale_data h.proofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint h.scale_data :=
  h.toActualProofLengthDirectEndpoint
    (actualUpperProviderOfProjectBoxUpperAndAdditiveProjection
      projection h.checkedMeasuredToActualBridge project_box_upper_provider)

namespace Month9Month10Month11NoSmallCoreHandoff

theorem actualEndpointOfProjectBoxUpperAndAdditiveProjection_computedN_eq_core
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        h.scale_data h.proofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let endpoint :=
      h.actualEndpointOfProjectBoxUpperAndAdditiveProjection
        projection project_box_upper_provider
    endpoint.computedCollisionNOfRationality hrat =
      h.core.computable_search_exclusion.witness
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN := by
  let endpoint :=
    h.actualEndpointOfProjectBoxUpperAndAdditiveProjection
      projection project_box_upper_provider
  have hcomputed :
      endpoint.computedCollisionNOfRationality hrat =
        (endpoint.gap.gap_for_polynomial_upper
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
            (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN :=
    endpoint.computedCollisionN_eq_searchGapWitness hrat
  have hwitness :
      ((h.actualProofLengthGap.gap_for_polynomial_upper
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
            (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) =
        h.core.computable_search_exclusion.witness
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
          (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN :=
    h.actual_gap_witness_eq_core
      (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
      (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
      (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN
  exact hcomputed.trans (by
    simpa [endpoint,
      actualEndpointOfProjectBoxUpperAndAdditiveProjection,
      Month9Month10Month11NoSmallCoreHandoff.toActualProofLengthDirectEndpoint]
      using hwitness)

theorem actualEndpointOfProjectBoxUpperAndAdditiveProjection_closure
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        h.scale_data h.proofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    let endpoint :=
      h.actualEndpointOfProjectBoxUpperAndAdditiveProjection
        projection project_box_upper_provider
    endpoint.Audit ∧
      endpoint.toAbstractMeasuredEndpoint.Audit ∧
        h.proofLengthFrontier.Audit ∧
          Nonempty
            (ComputableSearchGapCertificate
              (actualProofLengthMeasured h.scale_data)) ∧
            endpoint.upper_provider.Audit ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                endpoint.computedCollisionNOfRationality hrat =
                  h.core.computable_search_exclusion.witness
                    (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                    (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
                    (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
                (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                  False) ∧
                  ¬ _root_.is_rational _root_.euler_mascheroni := by
  let endpoint :=
    h.actualEndpointOfProjectBoxUpperAndAdditiveProjection
      projection project_box_upper_provider
  exact
    ⟨endpoint.audit,
      endpoint.toAbstractMeasuredEndpoint.audit,
      h.proofLengthFrontier.audit,
      ⟨endpoint.gap⟩,
      endpoint.upper_provider.audit,
      h.actualEndpointOfProjectBoxUpperAndAdditiveProjection_computedN_eq_core
        projection project_box_upper_provider,
      endpoint.computed_n_contradiction,
      endpoint.not_rational⟩

end Month9Month10Month11NoSmallCoreHandoff

namespace ConcretePAHilbertPowerBoundCalibratedFourPieceInput

def toNoSmallCoreHandoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input : ConcretePAHilbertPowerBoundCalibratedFourPieceInput
      scale_data) :
    Month9Month10Month11NoSmallCoreHandoff where
  core := input.toComputableFiniteSearchNoSmallCore

theorem actualProofLengthGap_witness_eq_rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input : ConcretePAHilbertPowerBoundCalibratedFourPieceInput
      scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((((toNoSmallCoreHandoff input).actualProofLengthGap
        |>.gap_for_polynomial_upper U hU).witness N) =
      input.rejectionExtractor.witness U hU N) :=
  rfl

def actualEndpointOfProjectBoxUpperAndAdditiveProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input : ConcretePAHilbertPowerBoundCalibratedFourPieceInput
      scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data input.checkerSemantics.toProofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data :=
  toNoSmallCoreHandoff input
    |>.actualEndpointOfProjectBoxUpperAndAdditiveProjection
      projection project_box_upper_provider

theorem actualEndpointOfProjectBoxUpperAndAdditiveProjection_computedN_eq_rejectionExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input : ConcretePAHilbertPowerBoundCalibratedFourPieceInput
      scale_data)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data input.checkerSemantics.toProofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let endpoint :=
      actualEndpointOfProjectBoxUpperAndAdditiveProjection input
        projection project_box_upper_provider
    endpoint.computedCollisionNOfRationality hrat =
      input.rejectionExtractor.witness
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN := by
  let h := toNoSmallCoreHandoff input
  let endpoint :=
    actualEndpointOfProjectBoxUpperAndAdditiveProjection input
      projection project_box_upper_provider
  have hcore :=
    h.actualEndpointOfProjectBoxUpperAndAdditiveProjection_computedN_eq_core
      projection project_box_upper_provider hrat
  have hwitness :
      h.core.computable_search_exclusion.witness
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN =
      input.rejectionExtractor.witness
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN := by
    rfl
  exact hcore.trans hwitness

end ConcretePAHilbertPowerBoundCalibratedFourPieceInput

/-! ## Executable calibrated rejection search to actual proof-length endpoint -/

/-- Assemble the calibrated four-piece package from the executable rejection
search and the single proof-length exactness input.  This is the exact point
where the proof-length-free executable search layer enters the actual
proof-length transport layer. -/
def calibratedFourPieceInputOfExecutableRejectionSearch
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (proof_length :
      ConcretePAHilbertPowerBoundCalibratedProofLengthInput
        scale_data lengthCodeAt) :
    ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data where
  lengthCodeAt := lengthCodeAt
  enumeration := enumeration
  rejection_search := search
  proof_length := proof_length

/-- Actual proof-length endpoint from executable calibrated rejection search,
proof-length exactness, an additive project-box projection, and an already
isolated project-box upper provider. -/
noncomputable def executableRejectionSearchActualEndpointOfProjectBoxUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (proof_length :
      ConcretePAHilbertPowerBoundCalibratedProofLengthInput
        scale_data lengthCodeAt)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data :=
  open ConcretePAHilbertPowerBoundCalibratedFourPieceInput in
  actualEndpointOfProjectBoxUpperAndAdditiveProjection
    (calibratedFourPieceInputOfExecutableRejectionSearch
      search proof_length)
      projection project_box_upper_provider

/-- Closure of the actual proof-length endpoint generated from executable
calibrated rejection search.  The computed collision witness remains exactly
the executable search witness; the only root proof-length dependency is the
explicit `proof_length` exactness input used to assemble the four-piece package. -/
theorem executableRejectionSearch_actualEndpointOfProjectBoxUpper_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (proof_length :
      ConcretePAHilbertPowerBoundCalibratedProofLengthInput
        scale_data lengthCodeAt)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    let endpoint :=
      executableRejectionSearchActualEndpointOfProjectBoxUpper
        search proof_length projection project_box_upper_provider
    endpoint.Audit ∧
      endpoint.toAbstractMeasuredEndpoint.Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured scale_data)) ∧
          endpoint.upper_provider.Audit ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              endpoint.computedCollisionNOfRationality hrat =
                search.witness
                  (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                  (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
                  (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
              (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni := by
  let input :=
    calibratedFourPieceInputOfExecutableRejectionSearch
      search proof_length
  let endpoint :=
    executableRejectionSearchActualEndpointOfProjectBoxUpper
      search proof_length projection project_box_upper_provider
  rcases endpoint.closure with
    ⟨haudit, habstract, hgap, hupperAudit, _hcomputed,
      _hlower, _hupper, hfalse, hnot⟩
  have hwitness :
      ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        endpoint.computedCollisionNOfRationality hrat =
          search.witness
            (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
            (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
            (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN := by
    intro hrat
    have hcomputed :=
      open ConcretePAHilbertPowerBoundCalibratedFourPieceInput in
      actualEndpointOfProjectBoxUpperAndAdditiveProjection_computedN_eq_rejectionExtractor
        input
        projection project_box_upper_provider hrat
    calc
      endpoint.computedCollisionNOfRationality hrat =
          input.rejectionExtractor.witness
            (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
            (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
            (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN := by
        simpa [endpoint,
          executableRejectionSearchActualEndpointOfProjectBoxUpper]
          using hcomputed
      _ = search.witness
            (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
            (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
            (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN := rfl
  exact
    ⟨haudit, habstract, hgap, hupperAudit, hwitness, hfalse, hnot⟩

/-- S²₁ project-upper specialization of the executable-search actual endpoint. -/
noncomputable def executableRejectionSearchActualEndpointOfProjectUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (proof_length :
      ConcretePAHilbertPowerBoundCalibratedProofLengthInput
        scale_data lengthCodeAt)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data :=
  executableRejectionSearchActualEndpointOfProjectBoxUpper
    search proof_length projection
    (projectBoxUpperProviderOfS21Collapse project_upper)

/-- Closure of the S²₁ project-upper executable-search actual endpoint. -/
theorem executableRejectionSearch_actualEndpointOfProjectUpper_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (proof_length :
      ConcretePAHilbertPowerBoundCalibratedProofLengthInput
        scale_data lengthCodeAt)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      executableRejectionSearchActualEndpointOfProjectUpper
        search proof_length projection project_upper
    endpoint.Audit ∧
      endpoint.toAbstractMeasuredEndpoint.Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured scale_data)) ∧
          endpoint.upper_provider.Audit ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              endpoint.computedCollisionNOfRationality hrat =
                search.witness
                  (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                  (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
                  (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
              (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [executableRejectionSearchActualEndpointOfProjectUpper] using
    executableRejectionSearch_actualEndpointOfProjectBoxUpper_closure
      search proof_length projection
      (projectBoxUpperProviderOfS21Collapse project_upper)

/-- Four-piece package assembled from executable calibrated rejection search
and the equivalent checked/actual transport bridge. -/
def calibratedFourPieceInputOfExecutableRejectionSearchBridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics) :
    ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data :=
  calibratedFourPieceInputOfExecutableRejectionSearch search
    (calibratedProofLengthInputOfCheckedMeasuredToActualBridge bridge)

/-- Actual proof-length endpoint from executable calibrated rejection search
where the proof-length residual is supplied as the equivalent checked/actual
transport bridge. -/
noncomputable def executableRejectionSearchBridgeActualEndpointOfProjectBoxUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data :=
  executableRejectionSearchActualEndpointOfProjectBoxUpper search
    (calibratedProofLengthInputOfCheckedMeasuredToActualBridge bridge)
    projection project_box_upper_provider

/-- Closure of the bridge-form executable-search actual endpoint.  This is the
same actual proof-length endpoint as above, but its only proof-length residual
is the checked/actual transport bridge. -/
theorem executableRejectionSearchBridge_actualEndpointOfProjectBoxUpper_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    let endpoint :=
      executableRejectionSearchBridgeActualEndpointOfProjectBoxUpper
        search bridge projection project_box_upper_provider
    endpoint.Audit ∧
      endpoint.toAbstractMeasuredEndpoint.Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured scale_data)) ∧
          endpoint.upper_provider.Audit ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              endpoint.computedCollisionNOfRationality hrat =
                search.witness
                  (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                  (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
                  (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
              (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [executableRejectionSearchBridgeActualEndpointOfProjectBoxUpper]
    using
      executableRejectionSearch_actualEndpointOfProjectBoxUpper_closure
        search
        (calibratedProofLengthInputOfCheckedMeasuredToActualBridge bridge)
        projection project_box_upper_provider

/-- S²₁ project-upper specialization of the bridge-form executable-search
actual endpoint. -/
noncomputable def executableRejectionSearchBridgeActualEndpointOfProjectUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data :=
  executableRejectionSearchBridgeActualEndpointOfProjectBoxUpper
    search bridge projection
    (projectBoxUpperProviderOfS21Collapse project_upper)

/-- Closure of the S²₁ project-upper bridge-form executable-search actual
endpoint. -/
theorem executableRejectionSearchBridge_actualEndpointOfProjectUpper_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      executableRejectionSearchBridgeActualEndpointOfProjectUpper
        search bridge projection project_upper
    endpoint.Audit ∧
      endpoint.toAbstractMeasuredEndpoint.Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured scale_data)) ∧
          endpoint.upper_provider.Audit ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              endpoint.computedCollisionNOfRationality hrat =
                search.witness
                  (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                  (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
                  (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
              (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [executableRejectionSearchBridgeActualEndpointOfProjectUpper] using
    executableRejectionSearchBridge_actualEndpointOfProjectBoxUpper_closure
      search bridge projection
      (projectBoxUpperProviderOfS21Collapse project_upper)

namespace PAHilbertCanonicalCalibratedExactnessCore

def toNoSmallCoreHandoff
    (core : PAHilbertCanonicalCalibratedExactnessCore) :
    Month9Month10Month11NoSmallCoreHandoff where
  core := core.toComputableFiniteSearchNoSmallCore

theorem actualProofLengthGap_witness_eq_rejectionExtractor
    (core : PAHilbertCanonicalCalibratedExactnessCore)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((((toNoSmallCoreHandoff core).actualProofLengthGap
        |>.gap_for_polynomial_upper U hU).witness N) =
      core.rejectionExtractor.witness U hU N) :=
  rfl

def actualEndpointOfProjectBoxUpperAndAdditiveProjection
    (core : PAHilbertCanonicalCalibratedExactnessCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint core.scale_data :=
  toNoSmallCoreHandoff core
    |>.actualEndpointOfProjectBoxUpperAndAdditiveProjection
      projection project_box_upper_provider

theorem actualEndpointOfProjectBoxUpperAndAdditiveProjection_computedN_eq_rejectionExtractor
    (core : PAHilbertCanonicalCalibratedExactnessCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (project_box_upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        sondowProjectLocalPudlakCollisionBox)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let endpoint :=
      actualEndpointOfProjectBoxUpperAndAdditiveProjection core
        projection project_box_upper_provider
    endpoint.computedCollisionNOfRationality hrat =
      core.rejectionExtractor.witness
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN := by
  let h := toNoSmallCoreHandoff core
  let endpoint :=
    actualEndpointOfProjectBoxUpperAndAdditiveProjection core
      projection project_box_upper_provider
  have hcore :=
    h.actualEndpointOfProjectBoxUpperAndAdditiveProjection_computedN_eq_core
      projection project_box_upper_provider hrat
  have hwitness :
      h.core.computable_search_exclusion.witness
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN =
      core.rejectionExtractor.witness
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial
        (endpoint.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN := by
    rfl
  exact hcore.trans hwitness

end PAHilbertCanonicalCalibratedExactnessCore

theorem month9_month10_no_small_core_handoff_actual_proof_length_endpoint_closure
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured h.scale_data)) :
    (h.toActualProofLengthDirectEndpoint upper_provider).Audit ∧
      (h.toActualProofLengthDirectEndpoint
        upper_provider).toAbstractMeasuredEndpoint.Audit ∧
        h.proofLengthFrontier.Audit ∧
          Nonempty
            (ComputableSearchGapCertificate
              (actualProofLengthMeasured h.scale_data)) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              (h.toActualProofLengthDirectEndpoint
                upper_provider).computedCollisionNOfRationality hrat =
                ((h.actualProofLengthGap.gap_for_polynomial_upper
                  ((h.toActualProofLengthDirectEndpoint upper_provider)
                    |>.toAbstractMeasuredEndpoint
                    |>.upperTailOfRationality hrat).U
                  ((h.toActualProofLengthDirectEndpoint upper_provider)
                    |>.toAbstractMeasuredEndpoint
                    |>.upperTailOfRationality hrat).polynomial).witness
                    ((h.toActualProofLengthDirectEndpoint upper_provider)
                      |>.toAbstractMeasuredEndpoint
                      |>.upperTailOfRationality hrat).upperN)) ∧
              (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                False) ∧
                ¬ _root_.is_rational _root_.euler_mascheroni :=
  let endpoint := h.toActualProofLengthDirectEndpoint upper_provider
  ⟨endpoint.audit,
    endpoint.toAbstractMeasuredEndpoint.audit,
    h.proofLengthFrontier.audit,
    ⟨h.actualProofLengthGap⟩,
    endpoint.computedCollisionN_eq_searchGapWitness,
    endpoint.computed_n_contradiction,
    endpoint.not_rational⟩

/-- Project-facing Month 9-10 computed-witness checklist.  It records all
currently verified routes to a computed collision witness while keeping their
interfaces separated: generic measured, checker-measured, actual proof-length,
and final project reflection-graft residual. -/
structure Month9Month10ComputedWitnessRouteChecklist : Prop where
  proofLengthFreeMeasuredKernel :
    Month9Month10ProofLengthFreeMeasuredCollisionKernelChecklist
  checkedMeasuredKernel :
    Month9Month10CheckedMeasuredKernelChecklist
  checkedSearchEndpointClosure :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ h : Month9Month10CheckedSearchCollisionEndpoint scale_data,
        h.Audit ∧
          h.toDirectEndpoint.Audit ∧
            Nonempty
              (ComputableSearchGapCertificate
                (month9_month10_checkedProofCodeMeasured scale_data h.sem)) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                h.computedCollisionNOfRationality hrat =
                  h.cert.witness
                    (h.toDirectEndpoint.toAbstractMeasuredEndpoint
                      |>.upperTailOfRationality hrat).U
                    (h.toDirectEndpoint.toAbstractMeasuredEndpoint
                      |>.upperTailOfRationality hrat).polynomial
                    (h.toDirectEndpoint.toAbstractMeasuredEndpoint
                      |>.upperTailOfRationality hrat).upperN) ∧
                (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                  False) ∧
                  ¬ _root_.is_rational _root_.euler_mascheroni
  actualProofLengthEndpointClosure :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ h :
        Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data,
        h.Audit ∧
          h.toAbstractMeasuredEndpoint.Audit ∧
            Nonempty
              (ComputableSearchGapCertificate
                (actualProofLengthMeasured scale_data)) ∧
              h.upper_provider.Audit ∧
                (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                  h.computedCollisionNOfRationality hrat =
                    (h.gap.gap_for_polynomial_upper
                      (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                      (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
                        (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
                  (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                    (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                        (h.computedCollisionNOfRationality hrat) <
                      actualProofLengthMeasured scale_data
                        (h.computedCollisionNOfRationality hrat)) ∧
                    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                      actualProofLengthMeasured scale_data
                          (h.computedCollisionNOfRationality hrat) ≤
                        (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                          (h.computedCollisionNOfRationality hrat)) ∧
                      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                        False) ∧
                        ¬ _root_.is_rational _root_.euler_mascheroni
  noSmallCoreActualEndpointClosure :
    ∀ h : Month9Month10Month11NoSmallCoreHandoff,
      ∀ upper_provider :
        Month9Month10AbstractMeasuredUpperProvider
          (actualProofLengthMeasured h.scale_data),
        (h.toActualProofLengthDirectEndpoint upper_provider).Audit ∧
          (h.toActualProofLengthDirectEndpoint
            upper_provider).toAbstractMeasuredEndpoint.Audit ∧
            h.proofLengthFrontier.Audit ∧
              Nonempty
                (ComputableSearchGapCertificate
                  (actualProofLengthMeasured h.scale_data)) ∧
                (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                  (h.toActualProofLengthDirectEndpoint
                    upper_provider).computedCollisionNOfRationality hrat =
                    ((h.actualProofLengthGap.gap_for_polynomial_upper
                      ((h.toActualProofLengthDirectEndpoint upper_provider)
                        |>.toAbstractMeasuredEndpoint
                        |>.upperTailOfRationality hrat).U
                      ((h.toActualProofLengthDirectEndpoint upper_provider)
                        |>.toAbstractMeasuredEndpoint
                        |>.upperTailOfRationality hrat).polynomial).witness
                        ((h.toActualProofLengthDirectEndpoint upper_provider)
                          |>.toAbstractMeasuredEndpoint
                          |>.upperTailOfRationality hrat).upperN)) ∧
                  (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                    False) ∧
                    ¬ _root_.is_rational _root_.euler_mascheroni
  projectResidualComputedWitness :
    ∀ h : Month9Month10NoSmallCoreResidualEndpoint,
      h.Audit ∧
        h.handoff.Audit ∧
          Nonempty Month9Month10ProjectCollisionChecklist ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              h.computedCollisionNOfRationality hrat =
                max (h.toProjectChecklist.upperTailOfRationality hrat).upperN
                  ((h.toProjectChecklist.witness_checklist.computable_gap
                    |>.gap_for_polynomial_upper
                      (h.toProjectChecklist.upperTailOfRationality hrat).U
                      (h.toProjectChecklist.upperTailOfRationality hrat).polynomial)
                    |>.threshold)) ∧
              (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                False) ∧
                ¬ _root_.is_rational _root_.euler_mascheroni
  constantProjectionResidualComputedWitness :
    ∀ h : Month9Month10NoSmallCoreConstantProjectionResidualEndpoint,
      h.toResidualEndpoint.Audit ∧
        Nonempty _root_.StrengthenedToPartialConsistencyConstantProjection ∧
          Nonempty _root_.PAConjunctionEliminationConstantCost ∧
            Nonempty Month9Month10ProjectCollisionChecklist ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                h.computedCollisionNOfRationality hrat =
                  max (h.toProjectChecklist.upperTailOfRationality hrat).upperN
                    ((h.toProjectChecklist.witness_checklist.computable_gap
                      |>.gap_for_polynomial_upper
                        (h.toProjectChecklist.upperTailOfRationality hrat).U
                        (h.toProjectChecklist.upperTailOfRationality hrat).polynomial)
                      |>.threshold)) ∧
                (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                  False) ∧
                  ¬ _root_.is_rational _root_.euler_mascheroni

theorem month9_month10_computed_witness_route_checklist :
    Month9Month10ComputedWitnessRouteChecklist where
  proofLengthFreeMeasuredKernel :=
    month9_month10_proof_length_free_measured_collision_kernel_checklist
  checkedMeasuredKernel :=
    month9_month10_checked_measured_kernel_checklist
  checkedSearchEndpointClosure := by
    intro scale_data h
    exact h.closure
  actualProofLengthEndpointClosure := by
    intro scale_data h
    exact h.closure
  noSmallCoreActualEndpointClosure := by
    intro h upper_provider
    exact
      month9_month10_no_small_core_handoff_actual_proof_length_endpoint_closure
        h upper_provider
  projectResidualComputedWitness := by
    intro h
    exact h.closure
  constantProjectionResidualComputedWitness := by
    intro h
    exact h.closure

def month9_month10_project_gap_transfer_to_direct_upper_tail_route
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{0})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10DirectUpperTailSearchCollisionRoute where
  gap := h.toComputableSearchGapCertificate
  upper_under_rationality := h.upperUnderRationality project_upper

theorem month9_month10_project_gap_transfer_factors_through_direct_upper_tail
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{0})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (month9_month10_project_gap_transfer_to_direct_upper_tail_route
      h project_upper).not_rational =
      h.search_not_rational project_upper :=
  rfl

/-! ## Payload-free upper-provider endpoint -/

/-- Payload-free upper provider for the shared project collision box.  It
packages exactly the upper-tail data needed by the direct collision endpoint,
without committing to the old project-checklist constructor that unfolds the
partial-consistency payload vocabulary. -/
structure Month9Month10PayloadFreeUpperProvider : Type where
  upper_under_rationality :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat,
          ∀ n : Nat, upperN ≤ n →
            sondowProjectLocalPudlakCollisionBox n ≤ U n

namespace Month9Month10PayloadFreeUpperProvider

structure Audit
    (h : Month9Month10PayloadFreeUpperProvider) : Prop where
  upperUnderRationality :
    _root_.is_rational _root_.euler_mascheroni →
      ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
        ∃ upperN : Nat,
          ∀ n : Nat, upperN ≤ n →
            sondowProjectLocalPudlakCollisionBox n ≤ U n

theorem audit
    (h : Month9Month10PayloadFreeUpperProvider) :
    h.Audit where
  upperUnderRationality := h.upper_under_rationality

theorem closure
    (h : Month9Month10PayloadFreeUpperProvider) :
    h.Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              sondowProjectLocalPudlakCollisionBox n ≤ U n) :=
  ⟨h.audit, h.upper_under_rationality⟩

end Month9Month10PayloadFreeUpperProvider

/-- Explicit payload-free upper provider for the shared project collision box.
This is the no-choose downstream shape of the Sondow/S²₁ upper route: once
rationality is assumed, it returns the concrete polynomial upper function and
cutoff as a `PolynomialUpperTailCertificate`. -/
abbrev Month9Month10PayloadFreeExplicitUpperProvider : Type :=
  Month9Month10ExplicitMeasuredUpperProvider
    sondowProjectLocalPudlakCollisionBox

namespace Month9Month10PayloadFreeExplicitUpperProvider

/-- Forget an explicit payload-free upper provider to the older existential
payload-free upper-provider surface. -/
def toPayloadFreeUpperProvider
    (h : Month9Month10PayloadFreeExplicitUpperProvider) :
    Month9Month10PayloadFreeUpperProvider where
  upper_under_rationality := by
    intro hrat
    let upper := h.upperTailOfRationality hrat
    exact ⟨upper.U, upper.polynomial, upper.upperN, upper.upper_after⟩

theorem toPayloadFreeUpperProvider_closure
    (h : Month9Month10PayloadFreeExplicitUpperProvider) :
    (h.toPayloadFreeUpperProvider).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              sondowProjectLocalPudlakCollisionBox n ≤ U n) :=
  h.toPayloadFreeUpperProvider.closure

end Month9Month10PayloadFreeExplicitUpperProvider

/-- Type-level Sondow/S²₁ upper tail certificate for the project collision box.
Unlike `SondowProjectLocalS21CollapseConclusion`, this keeps the upper function
and cutoff as data, so the downstream witness number can be evaluated. -/
structure SondowProjectLocalS21ExplicitUpperTail : Type where
  U : Nat → Real
  polynomial : _root_.is_polynomial_bound U
  upperN : Nat
  accepted_after :
    ∀ n : Nat, upperN ≤ n →
      _root_.accepted_certificate (_root_.sondowReflectionGraftCode n)
  upper_after :
    ∀ n : Nat, upperN ≤ n →
      sondowProjectLocalPudlakCollisionBox n ≤ U n

namespace SondowProjectLocalS21ExplicitUpperTail

def toPolynomialUpperTailCertificate
    (upper : SondowProjectLocalS21ExplicitUpperTail) :
    PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox where
  U := upper.U
  polynomial := upper.polynomial
  upperN := upper.upperN
  upper_after := upper.upper_after

end SondowProjectLocalS21ExplicitUpperTail

/-- Type-level Sondow/S²₁ upper provider.  This is the calculable replacement
for the old propositional collapse conclusion when a concrete `N` is desired. -/
structure SondowProjectLocalS21ExplicitUpperProvider : Type where
  upperTailOfRationality :
    _root_.is_rational _root_.euler_mascheroni →
      SondowProjectLocalS21ExplicitUpperTail

namespace SondowProjectLocalS21ExplicitUpperProvider

/-- Forget the type-level explicit Sondow/S²₁ upper provider to the old
propositional collapse conclusion. -/
def toCollapseConclusion
    (project_upper : SondowProjectLocalS21ExplicitUpperProvider) :
    SondowProjectLocalS21CollapseConclusion := by
  intro hrat
  let upper := project_upper.upperTailOfRationality hrat
  exact
    ⟨upper.U,
      upper.polynomial,
      upper.upperN,
      fun n hn => ⟨upper.accepted_after n hn, upper.upper_after n hn⟩⟩

/-- Forget the type-level explicit Sondow/S²₁ upper provider to the payload-free
explicit upper provider used by the collision endpoint. -/
def toPayloadFreeExplicitUpperProvider
    (project_upper : SondowProjectLocalS21ExplicitUpperProvider) :
    Month9Month10PayloadFreeExplicitUpperProvider where
  upperTailOfRationality := fun hrat =>
    (project_upper.upperTailOfRationality hrat).toPolynomialUpperTailCertificate

theorem toPayloadFreeExplicitUpperProvider_closure
    (project_upper : SondowProjectLocalS21ExplicitUpperProvider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let upper :=
      project_upper.toPayloadFreeExplicitUpperProvider.upperTailOfRationality
        hrat
    _root_.is_polynomial_bound upper.U ∧
      (∀ n : Nat, upper.upperN ≤ n →
        sondowProjectLocalPudlakCollisionBox n ≤ upper.U n) := by
  dsimp [toPayloadFreeExplicitUpperProvider,
    SondowProjectLocalS21ExplicitUpperTail.toPolynomialUpperTailCertificate]
  constructor
  · exact (project_upper.upperTailOfRationality hrat).polynomial
  · exact (project_upper.upperTailOfRationality hrat).upper_after

end SondowProjectLocalS21ExplicitUpperProvider

/-- Endpoint form of the Month 9-10 direct route after splitting the upper
provider from the lower/gap certificate.  This is the clean surface for the next
provider replacement: produce a payload-free upper provider and a computable
project gap, then the computed collision witness follows. -/
structure Month9Month10PayloadFreeUpperDirectCollisionEndpoint : Type where
  gap :
    ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox
  upper_provider : Month9Month10PayloadFreeUpperProvider

namespace Month9Month10PayloadFreeUpperDirectCollisionEndpoint

def toDirectRoute
    (h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint) :
    Month9Month10DirectUpperTailSearchCollisionRoute where
  gap := h.gap
  upper_under_rationality := h.upper_provider.upper_under_rationality

noncomputable def computedCollisionNOfRationality
    (h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  h.toDirectRoute.computedCollisionNOfRationality hrat

theorem computedCollisionN_eq_direct
    (h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      h.toDirectRoute.computedCollisionNOfRationality hrat :=
  rfl

theorem computedCollisionN_eq_searchGapWitness
    (h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      (h.gap.gap_for_polynomial_upper
        (h.toDirectRoute.upperTailOfRationality hrat).U
        (h.toDirectRoute.upperTailOfRationality hrat).polynomial).witness
          (h.toDirectRoute.upperTailOfRationality hrat).upperN :=
  h.toDirectRoute.computedCollisionN_eq_searchGapWitness hrat

theorem computedCollisionN_upper_lower_trace
    (h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let upper := h.toDirectRoute.upperTailOfRationality hrat
    upper.U (h.computedCollisionNOfRationality hrat) <
        sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat) ∧
      sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat) ≤
        upper.U (h.computedCollisionNOfRationality hrat) ∧
      False := by
  have hlower := h.toDirectRoute.lower_at_computedCollisionN hrat
  have hupper := h.toDirectRoute.upper_at_computedCollisionN hrat
  dsimp [computedCollisionNOfRationality]
  exact ⟨hlower, ⟨hupper, (not_lt_of_ge hupper) hlower⟩⟩

theorem computed_n_contradiction
    (h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.toDirectRoute.computed_n_contradiction hrat

theorem not_rational
    (h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toDirectRoute.not_rational

theorem not_rational_eq_generic_core
    (h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint) :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational
        h.toDirectRoute.toGenericCollisionInputs :=
  h.toDirectRoute.not_rational_eq_generic_core

structure Audit
    (h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint) :
    Prop where
  upperProviderAudit :
    h.upper_provider.Audit
  directRouteAudit :
    h.toDirectRoute.Audit
  computableSearchGap :
    Nonempty
      (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox)
  computedWitnessFormula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        (h.gap.gap_for_polynomial_upper
          (h.toDirectRoute.upperTailOfRationality hrat).U
          (h.toDirectRoute.upperTailOfRationality hrat).polynomial).witness
            (h.toDirectRoute.upperTailOfRationality hrat).upperN
  computedWitnessUpperLowerTrace :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let upper := h.toDirectRoute.upperTailOfRationality hrat
      upper.U (h.computedCollisionNOfRationality hrat) <
          sondowProjectLocalPudlakCollisionBox
            (h.computedCollisionNOfRationality hrat) ∧
        sondowProjectLocalPudlakCollisionBox
            (h.computedCollisionNOfRationality hrat) ≤
          upper.U (h.computedCollisionNOfRationality hrat) ∧
        False
  contradictionAtComputedN :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  notRationalEqGenericCore :
    h.not_rational =
      GenericRationalCollisionInputs.not_rational
        h.toDirectRoute.toGenericCollisionInputs
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    (h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint) :
    h.Audit where
  upperProviderAudit := h.upper_provider.audit
  directRouteAudit := h.toDirectRoute.audit
  computableSearchGap := ⟨h.gap⟩
  computedWitnessFormula := h.computedCollisionN_eq_searchGapWitness
  computedWitnessUpperLowerTrace := h.computedCollisionN_upper_lower_trace
  contradictionAtComputedN := h.computed_n_contradiction
  notRationalEqGenericCore := h.not_rational_eq_generic_core
  endpointNotRational := h.not_rational

theorem closure
    (h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint) :
    h.Audit ∧
      h.upper_provider.Audit ∧
        h.toDirectRoute.Audit ∧
          Nonempty
            (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              h.computedCollisionNOfRationality hrat =
                (h.gap.gap_for_polynomial_upper
                  (h.toDirectRoute.upperTailOfRationality hrat).U
                  (h.toDirectRoute.upperTailOfRationality hrat).polynomial).witness
                    (h.toDirectRoute.upperTailOfRationality hrat).upperN) ∧
              (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                False) ∧
                ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨h.audit,
    h.upper_provider.audit,
    h.toDirectRoute.audit,
    ⟨h.gap⟩,
    h.computedCollisionN_eq_searchGapWitness,
    h.computed_n_contradiction,
    h.not_rational⟩

end Month9Month10PayloadFreeUpperDirectCollisionEndpoint

theorem month9_month10_payload_free_upper_direct_collision_closure
    (h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint) :
    h.Audit ∧
      h.upper_provider.Audit ∧
        h.toDirectRoute.Audit ∧
          Nonempty
            (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              h.computedCollisionNOfRationality hrat =
                (h.gap.gap_for_polynomial_upper
                  (h.toDirectRoute.upperTailOfRationality hrat).U
                  (h.toDirectRoute.upperTailOfRationality hrat).polynomial).witness
                    (h.toDirectRoute.upperTailOfRationality hrat).upperN) ∧
              (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                False) ∧
                ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.closure

/-- Direct endpoint using an explicit payload-free upper provider.  This avoids
the downstream `upperTailCertificateOfRationality` choice path entirely: the
upper certificate under rationality is selected by `upper_provider` itself. -/
structure Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint : Type where
  gap :
    ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox
  upper_provider : Month9Month10PayloadFreeExplicitUpperProvider

namespace Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint

def upperTailOfRationality
    (h : Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate sondowProjectLocalPudlakCollisionBox :=
  h.upper_provider.upperTailOfRationality hrat

def computedWitnessOfRationality
    (h : Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      (h.upperTailOfRationality hrat).U
      sondowProjectLocalPudlakCollisionBox :=
  h.gap.collisionWitness (h.upperTailOfRationality hrat)

def computedCollisionNOfRationality
    (h : Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  (h.computedWitnessOfRationality hrat).n

theorem computedCollisionN_eq_searchGapWitness
    (h : Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      (h.gap.gap_for_polynomial_upper
        (h.upperTailOfRationality hrat).U
        (h.upperTailOfRationality hrat).polynomial).witness
          (h.upperTailOfRationality hrat).upperN :=
  rfl

theorem computedCollisionN_upper_lower_trace
    (h : Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let upper := h.upperTailOfRationality hrat
    upper.U (h.computedCollisionNOfRationality hrat) <
        sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat) ∧
      sondowProjectLocalPudlakCollisionBox
          (h.computedCollisionNOfRationality hrat) ≤
        upper.U (h.computedCollisionNOfRationality hrat) ∧
      False := by
  dsimp [computedCollisionNOfRationality, computedWitnessOfRationality,
    upperTailOfRationality]
  let upper := h.upper_provider.upperTailOfRationality hrat
  let witness := h.gap.collisionWitness upper
  have hlower :
      upper.U witness.n < sondowProjectLocalPudlakCollisionBox witness.n :=
    witness.lower_at_n
  have hupper :
      sondowProjectLocalPudlakCollisionBox witness.n ≤ upper.U witness.n :=
    witness.upper_at_n
  exact ⟨hlower, hupper, (not_lt_of_ge hupper) hlower⟩

theorem computed_n_contradiction
    (h : Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  h.gap.collisionWitness_contradiction (h.upperTailOfRationality hrat)

theorem not_rational
    (h : Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat => h.computed_n_contradiction hrat

def toPayloadFreeEndpoint
    (h : Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint) :
    Month9Month10PayloadFreeUpperDirectCollisionEndpoint where
  gap := h.gap
  upper_provider := h.upper_provider.toPayloadFreeUpperProvider

structure Audit
    (h : Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint) :
    Prop where
  explicitUpperProviderClosure :
    h.upper_provider.toPayloadFreeUpperProvider.Audit
  computableSearchGap :
    Nonempty
      (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox)
  computedWitnessFormula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      h.computedCollisionNOfRationality hrat =
        (h.gap.gap_for_polynomial_upper
          (h.upperTailOfRationality hrat).U
          (h.upperTailOfRationality hrat).polynomial).witness
            (h.upperTailOfRationality hrat).upperN
  computedWitnessUpperLowerTrace :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let upper := h.upperTailOfRationality hrat
      upper.U (h.computedCollisionNOfRationality hrat) <
          sondowProjectLocalPudlakCollisionBox
            (h.computedCollisionNOfRationality hrat) ∧
        sondowProjectLocalPudlakCollisionBox
            (h.computedCollisionNOfRationality hrat) ≤
          upper.U (h.computedCollisionNOfRationality hrat) ∧
        False
  contradictionAtComputedN :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    (h : Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint) :
    h.Audit where
  explicitUpperProviderClosure :=
    h.upper_provider.toPayloadFreeUpperProvider.audit
  computableSearchGap := ⟨h.gap⟩
  computedWitnessFormula := h.computedCollisionN_eq_searchGapWitness
  computedWitnessUpperLowerTrace := h.computedCollisionN_upper_lower_trace
  contradictionAtComputedN := h.computed_n_contradiction
  endpointNotRational := h.not_rational

theorem closure
    (h : Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint) :
    h.Audit ∧
      h.upper_provider.toPayloadFreeUpperProvider.Audit ∧
        Nonempty
          (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            h.computedCollisionNOfRationality hrat =
              (h.gap.gap_for_polynomial_upper
                (h.upperTailOfRationality hrat).U
                (h.upperTailOfRationality hrat).polynomial).witness
                  (h.upperTailOfRationality hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨h.audit,
    h.upper_provider.toPayloadFreeUpperProvider.audit,
    ⟨h.gap⟩,
    h.computedCollisionN_eq_searchGapWitness,
    h.computed_n_contradiction,
    h.not_rational⟩

end Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint

theorem month9_month10_payload_free_explicit_upper_direct_collision_closure
    (h : Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint) :
    h.Audit ∧
      h.upper_provider.toPayloadFreeUpperProvider.Audit ∧
        Nonempty
          (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            h.computedCollisionNOfRationality hrat =
              (h.gap.gap_for_polynomial_upper
                (h.upperTailOfRationality hrat).U
                (h.upperTailOfRationality hrat).polynomial).witness
                  (h.upperTailOfRationality hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.closure

/-- Build the payload-free upper provider directly from the Sondow project-local
upper route.  This strips the accepted-certificate payload component and keeps
only the polynomial proof-length upper tail needed by the collision core. -/
def month9_month10_project_upper_to_payload_free_upper_provider
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10PayloadFreeUpperProvider where
  upper_under_rationality := by
    intro hrat
    rcases project_upper hrat with ⟨U, hU, upperN, hupper⟩
    exact
      ⟨U, hU, upperN, fun n hn => by
        exact (hupper n hn).2⟩

theorem month9_month10_project_upper_to_payload_free_upper_provider_closure
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (month9_month10_project_upper_to_payload_free_upper_provider
      project_upper).Audit ∧
      (_root_.is_rational _root_.euler_mascheroni →
        ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
          ∃ upperN : Nat,
            ∀ n : Nat, upperN ≤ n →
              sondowProjectLocalPudlakCollisionBox n ≤ U n) :=
  (month9_month10_project_upper_to_payload_free_upper_provider
    project_upper).closure

/-- Explicit endpoint built from the Sondow project-local upper route and a
computable tail search gap.  This is the direct no-choose S21-to-witness
surface: after the boundary conversion, `N` is computed from the explicit
upper certificate. -/
def month9_month10_payload_free_explicit_endpoint_of_tail_gap
    (gap :
      ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21ExplicitUpperProvider) :
    Month9Month10PayloadFreeExplicitUpperDirectCollisionEndpoint where
  gap := gap
  upper_provider :=
    project_upper.toPayloadFreeExplicitUpperProvider

theorem month9_month10_payload_free_explicit_endpoint_of_tail_gap_closure
    (gap :
      ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21ExplicitUpperProvider) :
    (month9_month10_payload_free_explicit_endpoint_of_tail_gap
      gap project_upper).Audit ∧
      ((month9_month10_payload_free_explicit_endpoint_of_tail_gap
        gap project_upper).upper_provider.toPayloadFreeUpperProvider).Audit ∧
        Nonempty
          (ComputableSearchGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (month9_month10_payload_free_explicit_endpoint_of_tail_gap
              gap project_upper).computedCollisionNOfRationality hrat =
              (gap.gap_for_polynomial_upper
                ((month9_month10_payload_free_explicit_endpoint_of_tail_gap
                  gap project_upper).upperTailOfRationality hrat).U
                ((month9_month10_payload_free_explicit_endpoint_of_tail_gap
                  gap project_upper).upperTailOfRationality hrat).polynomial).witness
                  ((month9_month10_payload_free_explicit_endpoint_of_tail_gap
                    gap project_upper).upperTailOfRationality hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni :=
  (month9_month10_payload_free_explicit_endpoint_of_tail_gap
    gap project_upper).closure

/-- Build the payload-free direct endpoint from a tail-threshold computable gap
and a payload-free upper provider.  This is the clean adapter: it does not look
inside the older Sondow project-local upper constructor. -/
def month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
    (tail_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (upper_provider : Month9Month10PayloadFreeUpperProvider) :
    Month9Month10PayloadFreeUpperDirectCollisionEndpoint where
  gap := tail_gap.toComputableSearchGapCertificate
  upper_provider := upper_provider

theorem month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider_computed_n_eq_max
    (tail_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (upper_provider : Month9Month10PayloadFreeUpperProvider)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
      tail_gap upper_provider).computedCollisionNOfRationality hrat =
      max
        ((month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
          tail_gap upper_provider).toDirectRoute
          |>.upperTailOfRationality hrat).upperN
        ((tail_gap.gap_for_polynomial_upper
          ((month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
            tail_gap upper_provider).toDirectRoute
            |>.upperTailOfRationality hrat).U
          ((month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
            tail_gap upper_provider).toDirectRoute
            |>.upperTailOfRationality hrat).polynomial).threshold) :=
  rfl

theorem month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider_closure
    (tail_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (upper_provider : Month9Month10PayloadFreeUpperProvider) :
    (month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
      tail_gap upper_provider).Audit ∧
      (month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
        tail_gap upper_provider).upper_provider.Audit ∧
        (month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
          tail_gap upper_provider).toDirectRoute.Audit ∧
          Nonempty
            (ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
            Nonempty
              (ComputableSearchGapCertificate
                sondowProjectLocalPudlakCollisionBox) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                (month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
                  tail_gap upper_provider).computedCollisionNOfRationality hrat =
                  max
                    ((month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
                      tail_gap upper_provider).toDirectRoute
                      |>.upperTailOfRationality hrat).upperN
                    ((tail_gap.gap_for_polynomial_upper
                      ((month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
                        tail_gap upper_provider).toDirectRoute
                        |>.upperTailOfRationality hrat).U
                      ((month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
                        tail_gap upper_provider).toDirectRoute
                        |>.upperTailOfRationality hrat).polynomial).threshold)) ∧
                (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                  False) ∧
                  ¬ _root_.is_rational _root_.euler_mascheroni :=
  let endpoint :=
    month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
      tail_gap upper_provider
  ⟨endpoint.audit,
    endpoint.upper_provider.audit,
    endpoint.toDirectRoute.audit,
    ⟨tail_gap⟩,
    ⟨tail_gap.toComputableSearchGapCertificate⟩,
    month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider_computed_n_eq_max
      tail_gap upper_provider,
    endpoint.computed_n_contradiction,
    endpoint.not_rational⟩

/-- Build the payload-free direct endpoint from the older Sondow project-local
upper route.  Axiom auditing intentionally keeps this adapter separate: the
old upper route may still mention payload-level conventions. -/
def month9_month10_payload_free_endpoint_of_tail_gap
    (tail_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10PayloadFreeUpperDirectCollisionEndpoint :=
  month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
    tail_gap
    (month9_month10_project_upper_to_payload_free_upper_provider
      project_upper)

theorem month9_month10_payload_free_endpoint_of_tail_gap_computed_n_eq_max
    (tail_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (month9_month10_payload_free_endpoint_of_tail_gap
      tail_gap project_upper).computedCollisionNOfRationality hrat =
      max
        ((month9_month10_payload_free_endpoint_of_tail_gap
          tail_gap project_upper).toDirectRoute
          |>.upperTailOfRationality hrat).upperN
        ((tail_gap.gap_for_polynomial_upper
          ((month9_month10_payload_free_endpoint_of_tail_gap
            tail_gap project_upper).toDirectRoute
            |>.upperTailOfRationality hrat).U
          ((month9_month10_payload_free_endpoint_of_tail_gap
            tail_gap project_upper).toDirectRoute
            |>.upperTailOfRationality hrat).polynomial).threshold) :=
  rfl

theorem month9_month10_payload_free_endpoint_of_tail_gap_closure
    (tail_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (month9_month10_payload_free_endpoint_of_tail_gap
      tail_gap project_upper).Audit ∧
      (month9_month10_payload_free_endpoint_of_tail_gap
        tail_gap project_upper).upper_provider.Audit ∧
        (month9_month10_payload_free_endpoint_of_tail_gap
          tail_gap project_upper).toDirectRoute.Audit ∧
          Nonempty
            (ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
            Nonempty
              (ComputableSearchGapCertificate
                sondowProjectLocalPudlakCollisionBox) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                (month9_month10_payload_free_endpoint_of_tail_gap
                  tail_gap project_upper).computedCollisionNOfRationality hrat =
                  max
                    ((month9_month10_payload_free_endpoint_of_tail_gap
                      tail_gap project_upper).toDirectRoute
                      |>.upperTailOfRationality hrat).upperN
                    ((tail_gap.gap_for_polynomial_upper
                      ((month9_month10_payload_free_endpoint_of_tail_gap
                        tail_gap project_upper).toDirectRoute
                        |>.upperTailOfRationality hrat).U
                      ((month9_month10_payload_free_endpoint_of_tail_gap
                        tail_gap project_upper).toDirectRoute
                        |>.upperTailOfRationality hrat).polynomial).threshold)) ∧
                (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                  False) ∧
                  ¬ _root_.is_rational _root_.euler_mascheroni :=
  month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider_closure
    tail_gap
    (month9_month10_project_upper_to_payload_free_upper_provider
      project_upper)

def month9_month10_legacy_project_gap_transfer_upper_provider
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{0})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10PayloadFreeUpperProvider where
  upper_under_rationality := h.upperUnderRationality project_upper

def month9_month10_legacy_project_gap_transfer_payload_free_endpoint
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{0})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10PayloadFreeUpperDirectCollisionEndpoint where
  gap := h.toComputableSearchGapCertificate
  upper_provider :=
    month9_month10_legacy_project_gap_transfer_upper_provider
      h project_upper

theorem month9_month10_legacy_project_gap_transfer_payload_free_endpoint_factors
    (h : Month9Month10ProjectGapTransferComputableSearchChecklist.{0})
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (month9_month10_legacy_project_gap_transfer_payload_free_endpoint
      h project_upper).not_rational =
      h.search_not_rational project_upper :=
  rfl

/-- Project-level checklist for the payload-axiom-free Month 9-10 kernel
surface.  It combines the checker-side finite-consistency accepted-code layer
with the direct upper-tail collision endpoint.  This checklist intentionally
does not mention the legacy root `accepted_certificate` bridge or the old
project-checklist upper constructor, because those are precisely the places
where the payload axioms re-enter. -/
structure Month9Month10PayloadAxiomFreeCollisionKernelChecklist :
    Prop where
  checkerAcceptanceClean :
    ∀ h : Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance,
      h.Audit ∧
        Nonempty
          (Month9Month10PayloadFreeCheckerAcceptedFamily
            h.checker _root_.partialConsistencyCode) ∧
          Nonempty
            (Month9Month10PayloadFreeCheckerAcceptedFamily
              h.checker _root_.strengthenedPartialConsistencyCode) ∧
            (∀ n : Nat,
              PAHilbertAcceptedProofCodeForFormulaCode
                h.checker (_root_.partialConsistencyCode n)
                (h.ordinary.proofCode n)) ∧
              (∀ n : Nat,
                PAHilbertAcceptedProofCodeForFormulaCode
                  h.checker (_root_.strengthenedPartialConsistencyCode n)
                  (h.strengthened.proofCode n))
  upperProviderClosure :
    ∀ h : Month9Month10PayloadFreeUpperProvider,
      h.Audit ∧
        (_root_.is_rational _root_.euler_mascheroni →
          ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
            ∃ upperN : Nat,
              ∀ n : Nat, upperN ≤ n →
                sondowProjectLocalPudlakCollisionBox n ≤ U n)
  directCollisionClosure :
    ∀ h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint,
      h.Audit ∧
        h.upper_provider.Audit ∧
          h.toDirectRoute.Audit ∧
            Nonempty
              (ComputableSearchGapCertificate
                sondowProjectLocalPudlakCollisionBox) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                h.computedCollisionNOfRationality hrat =
                  (h.gap.gap_for_polynomial_upper
                    (h.toDirectRoute.upperTailOfRationality hrat).U
                    (h.toDirectRoute.upperTailOfRationality hrat).polynomial).witness
                      (h.toDirectRoute.upperTailOfRationality hrat).upperN) ∧
                (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                  False) ∧
                  ¬ _root_.is_rational _root_.euler_mascheroni

theorem month9_month10_payload_axiom_free_collision_kernel_checklist :
    Month9Month10PayloadAxiomFreeCollisionKernelChecklist where
  checkerAcceptanceClean :=
    month9_month10_payload_free_checker_acceptance_axiom_clean_closure
  upperProviderClosure :=
    Month9Month10PayloadFreeUpperProvider.closure
  directCollisionClosure :=
    month9_month10_payload_free_upper_direct_collision_closure

/-- Clean computed-witness checklist for the current Month 9-10 route.  Unlike
`Month9Month10ComputedWitnessRouteChecklist`, this one deliberately excludes
legacy project residual endpoints that unfold payload axioms.  Its project
route is the payload-free direct upper-tail endpoint. -/
structure Month9Month10CleanComputedWitnessRouteChecklist : Prop where
  proofLengthFreeMeasuredKernel :
    Month9Month10ProofLengthFreeMeasuredCollisionKernelChecklist
  checkedMeasuredKernel :
    Month9Month10CheckedMeasuredKernelChecklist
  actualProofLengthEndpointClosure :
    ∀ scale_data : InternalPudlakTheorem5ScaleData,
      ∀ h :
        Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data,
        h.Audit ∧
          h.toAbstractMeasuredEndpoint.Audit ∧
            Nonempty
              (ComputableSearchGapCertificate
                (actualProofLengthMeasured scale_data)) ∧
              h.upper_provider.Audit ∧
                (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                  h.computedCollisionNOfRationality hrat =
                    (h.gap.gap_for_polynomial_upper
                      (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                      (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).polynomial).witness
                        (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).upperN) ∧
                  (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                    (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                        (h.computedCollisionNOfRationality hrat) <
                      actualProofLengthMeasured scale_data
                        (h.computedCollisionNOfRationality hrat)) ∧
                    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                      actualProofLengthMeasured scale_data
                          (h.computedCollisionNOfRationality hrat) ≤
                        (h.toAbstractMeasuredEndpoint.upperTailOfRationality hrat).U
                          (h.computedCollisionNOfRationality hrat)) ∧
                      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                        False) ∧
                        ¬ _root_.is_rational _root_.euler_mascheroni
  noSmallCoreActualEndpointClosure :
    ∀ h : Month9Month10Month11NoSmallCoreHandoff,
      ∀ upper_provider :
        Month9Month10AbstractMeasuredUpperProvider
          (actualProofLengthMeasured h.scale_data),
        (h.toActualProofLengthDirectEndpoint upper_provider).Audit ∧
          (h.toActualProofLengthDirectEndpoint
            upper_provider).toAbstractMeasuredEndpoint.Audit ∧
            h.proofLengthFrontier.Audit ∧
              Nonempty
                (ComputableSearchGapCertificate
                  (actualProofLengthMeasured h.scale_data)) ∧
                (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                  (h.toActualProofLengthDirectEndpoint
                    upper_provider).computedCollisionNOfRationality hrat =
                    ((h.actualProofLengthGap.gap_for_polynomial_upper
                      ((h.toActualProofLengthDirectEndpoint upper_provider)
                        |>.toAbstractMeasuredEndpoint
                        |>.upperTailOfRationality hrat).U
                      ((h.toActualProofLengthDirectEndpoint upper_provider)
                        |>.toAbstractMeasuredEndpoint
                        |>.upperTailOfRationality hrat).polynomial).witness
                        ((h.toActualProofLengthDirectEndpoint upper_provider)
                          |>.toAbstractMeasuredEndpoint
                          |>.upperTailOfRationality hrat).upperN)) ∧
                  (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                    False) ∧
                    ¬ _root_.is_rational _root_.euler_mascheroni
  payloadFreeProjectDirectClosure :
    ∀ h : Month9Month10PayloadFreeUpperDirectCollisionEndpoint,
      h.Audit ∧
        h.upper_provider.Audit ∧
          h.toDirectRoute.Audit ∧
            Nonempty
              (ComputableSearchGapCertificate
                sondowProjectLocalPudlakCollisionBox) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                h.computedCollisionNOfRationality hrat =
                  (h.gap.gap_for_polynomial_upper
                    (h.toDirectRoute.upperTailOfRationality hrat).U
                    (h.toDirectRoute.upperTailOfRationality hrat).polynomial).witness
                      (h.toDirectRoute.upperTailOfRationality hrat).upperN) ∧
                (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                  False) ∧
                  ¬ _root_.is_rational _root_.euler_mascheroni
  tailGapPayloadFreeEndpointClosure :
    ∀ tail_gap :
        ComputableGapCertificate sondowProjectLocalPudlakCollisionBox,
      ∀ upper_provider : Month9Month10PayloadFreeUpperProvider,
        (month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
          tail_gap upper_provider).Audit ∧
          (month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
            tail_gap upper_provider).upper_provider.Audit ∧
            (month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
              tail_gap upper_provider).toDirectRoute.Audit ∧
              Nonempty
                (ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) ∧
                Nonempty
                  (ComputableSearchGapCertificate
                    sondowProjectLocalPudlakCollisionBox) ∧
                  (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                    (month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
                      tail_gap upper_provider).computedCollisionNOfRationality hrat =
                      max
                        ((month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
                          tail_gap upper_provider).toDirectRoute
                          |>.upperTailOfRationality hrat).upperN
                        ((tail_gap.gap_for_polynomial_upper
                          ((month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
                            tail_gap upper_provider).toDirectRoute
                            |>.upperTailOfRationality hrat).U
                          ((month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider
                            tail_gap upper_provider).toDirectRoute
                            |>.upperTailOfRationality hrat).polynomial).threshold)) ∧
                    (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                      False) ∧
                      ¬ _root_.is_rational _root_.euler_mascheroni
  payloadAxiomFreeProjectKernel :
    Month9Month10PayloadAxiomFreeCollisionKernelChecklist

theorem month9_month10_clean_computed_witness_route_checklist :
    Month9Month10CleanComputedWitnessRouteChecklist where
  proofLengthFreeMeasuredKernel :=
    month9_month10_proof_length_free_measured_collision_kernel_checklist
  checkedMeasuredKernel :=
    month9_month10_checked_measured_kernel_checklist
  actualProofLengthEndpointClosure := by
    intro scale_data h
    exact h.closure
  noSmallCoreActualEndpointClosure := by
    intro h upper_provider
    exact
      month9_month10_no_small_core_handoff_actual_proof_length_endpoint_closure
        h upper_provider
  payloadFreeProjectDirectClosure := by
    intro h
    exact h.closure
  tailGapPayloadFreeEndpointClosure := by
    intro tail_gap upper_provider
    exact
      month9_month10_payload_free_endpoint_of_tail_gap_and_upper_provider_closure
        tail_gap upper_provider
  payloadAxiomFreeProjectKernel :=
    month9_month10_payload_axiom_free_collision_kernel_checklist

end SondowProjectMonth9Month10Month11ExactProofGapHandoff
end SondowMainCheckedCodeBridge

end
