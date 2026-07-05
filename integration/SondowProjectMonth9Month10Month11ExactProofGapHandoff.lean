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

/-- Transport the Sondow project-box upper route to the theorem-5 checked
source measurement using an additive projection
`source <= projectBox + overhead`.  The resulting upper function is
`U + overhead`, still polynomial by `shiftedUpper_polynomial`. -/
def checkedUpperProviderOfProjectUpperAndAdditiveProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection scale_data sem)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10AbstractMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured scale_data sem) where
  upper_under_rationality := by
    intro hrat
    rcases
        (projectBoxUpperProviderOfS21Collapse project_upper)
          |>.upper_under_rationality hrat with
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
  bridge.transportUpperToActualProofLength
    (checkedUpperProviderOfProjectUpperAndAdditiveProjection
      projection project_upper)

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

def Month9Month10Month11NoSmallCoreHandoff.toActualProofLengthDirectEndpoint
    (h : Month9Month10Month11NoSmallCoreHandoff)
    (upper_provider :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured h.scale_data)) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint h.scale_data where
  gap := h.actualProofLengthGap
  upper_provider := upper_provider

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
