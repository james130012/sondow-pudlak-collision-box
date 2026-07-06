/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import integration.SondowProjectMonth9Month10InternalPudlakWitnessSurface

/-!
# Month 9-10 proof-length gap frontier

This file is deliberately upstream of the Month 11-12 PA/Hilbert checker
surface.  It records the exact project-level certificate target needed from
that checker work, without importing or depending on the in-progress checker
file.

The key bridge is:

* an actual computable search gap for PA `proof_length` on the theorem-5 raw
  family;
* exact calibration of that `proof_length` to the chosen scale;
* strict growth of the scale.

Together these produce the existing Month 9-10 checked lower-bound core.  The
project-level collision still additionally needs the Sondow/Pudlak project gap
certificate, which stays separate on purpose.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth9Month10ProofLengthGapFrontier

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open Filter

universe q

/-- The actual PA proof-length measurement on the theorem-5 power-bound raw
formula family. -/
def actualProofLengthMeasured
    (scale_data : InternalPudlakTheorem5ScaleData) : Nat → Real :=
  fun n =>
    _root_.proof_length _root_.ProofSystem.PA
      _root_.ProofLengthMeasure.symbolSize
      (scale_data.powerBoundRawCode n)

/-- The Nat-valued scale viewed as a real-valued lower-bound target. -/
def scaleMeasured
    (scale_data : InternalPudlakTheorem5ScaleData) : Nat → Real :=
  fun n => (scale_data.scale n : Real)

/-- Transport a search gap across pointwise equality of measured functions,
without changing the computed witness. -/
def transportSearchStrictGap
    {U measuredA measuredB : Nat → Real}
    (heq : ∀ n : Nat, measuredA n = measuredB n)
    (gap : SearchStrictGapCertificate U measuredA) :
    SearchStrictGapCertificate U measuredB where
  witness := gap.witness
  witness_ge := gap.witness_ge
  strict_at_witness := by
    intro N
    rw [← heq (gap.witness N)]
    exact gap.strict_at_witness N

theorem transportSearchStrictGap_witness_eq
    {U measuredA measuredB : Nat → Real}
    (heq : ∀ n : Nat, measuredA n = measuredB n)
    (gap : SearchStrictGapCertificate U measuredA) (N : Nat) :
    (transportSearchStrictGap heq gap).witness N = gap.witness N :=
  rfl

theorem transportSearchStrictGap_strict_at_witness
    {U measuredA measuredB : Nat → Real}
    (heq : ∀ n : Nat, measuredA n = measuredB n)
    (gap : SearchStrictGapCertificate U measuredA) (N : Nat) :
    U ((transportSearchStrictGap heq gap).witness N) <
      measuredB ((transportSearchStrictGap heq gap).witness N) :=
  (transportSearchStrictGap heq gap).strict_at_witness N

/-- Transport a computable search-gap provider across pointwise equality of
measured functions.  This is the exact adapter needed once a checker proves
`proof_length(powerBoundRawCode n) = scale n`. -/
def transportComputableSearchGap
    {measuredA measuredB : Nat → Real}
    (heq : ∀ n : Nat, measuredA n = measuredB n)
    (gap : ComputableSearchGapCertificate measuredA) :
    ComputableSearchGapCertificate measuredB where
  gap_for_polynomial_upper := fun U hU =>
    transportSearchStrictGap heq (gap.gap_for_polynomial_upper U hU)

theorem transportComputableSearchGap_witness_eq
    {measuredA measuredB : Nat → Real}
    (heq : ∀ n : Nat, measuredA n = measuredB n)
    (gap : ComputableSearchGapCertificate measuredA)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((transportComputableSearchGap heq gap).gap_for_polynomial_upper
        U hU).witness N =
      (gap.gap_for_polynomial_upper U hU).witness N :=
  rfl

/-- A polynomially bounded measured function cannot itself carry a search-gap
certificate against every polynomial upper bound.  The witness `U n =
measured n + 1` is polynomially bounded and forces the contradiction
`measured w + 1 < measured w`.

This is a negative audit lemma: it keeps the Month 9-10 target on actual
proof length, not on the polynomially bounded theorem-5 scale. -/
theorem no_computable_search_gap_of_polynomial_bound
    {measured : Nat → Real} (hpoly : _root_.is_polynomial_bound measured) :
    ComputableSearchGapCertificate measured → False := by
  intro gap
  let U : Nat → Real := fun n => measured n + 1
  have hU : _root_.is_polynomial_bound U := by
    have hlin :=
      hpoly.linear_rescale (C := 1) (D := 1)
        (by norm_num) (by norm_num)
    simpa [U] using hlin
  let w := (gap.gap_for_polynomial_upper U hU).witness 0
  have hstrict :=
    (gap.gap_for_polynomial_upper U hU).strict_at_witness 0
  change measured w + 1 < measured w at hstrict
  nlinarith

theorem no_scale_search_gap_for_internal_scale
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ComputableSearchGapCertificate (scaleMeasured scale_data) → False :=
  no_computable_search_gap_of_polynomial_bound
    scale_data.scale_polynomial_bound

/-- If actual proof length is pointwise equal to a polynomially bounded
measurement, the current strong lower-bound statement cannot hold for that
formula family.  The strong statement yields a strict gap above the polynomial
upper `measured`; the pointwise equality gives the matching global upper bound. -/
theorem no_strong_proof_length_lower_bound_of_polynomial_exact_upper
    {φ : Nat → _root_.FormulaCode} {measured : Nat → Real}
    (hpoly : _root_.is_polynomial_bound measured)
    (heq : ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize (φ n) = measured n) :
    ¬ _root_.StrongProofLengthLowerBound
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize φ := by
  intro hstrong
  have hgap :=
    _root_.EventualLowerBound.toProofLengthGap
      (_root_.StrongProofLengthLowerBound.toEventualLowerBound hstrong)
      measured hpoly
  exact _root_.collisionCore_from_lower_upper_gap hgap 0
    (fun n _ => le_of_eq (heq n))

/-- Specialization to the theorem-5 power-bound family.  With the current
`scale_polynomial_bound` field, an exact calibration
`proof_length(powerBoundRawCode n) = scale n` rules out the strong proof-length
lower bound for `powerBoundRawCode`. -/
theorem no_internal_power_bound_strong_lower_bound_of_proof_length_eq_scale
    {scale_data : InternalPudlakTheorem5ScaleData}
    (proof_length_eq_scale :
      ∀ n : Nat,
        actualProofLengthMeasured scale_data n =
          scaleMeasured scale_data n) :
    ¬ _root_.StrongProofLengthLowerBound
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      scale_data.powerBoundRawCode := by
  exact no_strong_proof_length_lower_bound_of_polynomial_exact_upper
    (φ := scale_data.powerBoundRawCode)
    (measured := scaleMeasured scale_data)
    (by
      change _root_.is_polynomial_bound
        (fun n : Nat => (scale_data.scale n : Real))
      exact scale_data.scale_polynomial_bound)
    (by
      intro n
      simpa [actualProofLengthMeasured] using proof_length_eq_scale n)

/-- The correct Month 9-10 measured object is actual PA proof length.  A
computable finite-search/no-small-code core gives the search gap directly,
using its lower-search witness and proof-length calibration; no equality
between proof length and the polynomially bounded scale is required. -/
def actualProofLengthGapOfComputableFiniteSearchNoSmallCore
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    ComputableSearchGapCertificate
      (actualProofLengthMeasured core.scale_data) where
  gap_for_polynomial_upper := by
    intro U hU
    exact {
      witness := fun N =>
        core.computable_search_exclusion.witness U hU N
      witness_ge := fun N =>
        core.computable_search_exclusion.witness_ge U hU N
      strict_at_witness := by
        intro N
        let w :=
          core.computable_search_exclusion.computedLowerSearchWitness U hU N
        have hmin :
            U w.n <
              (core.proof_code_semantics.minProofCodeSize
                (core.scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩ :
                  Real) :=
          w.minProofCodeSize_gt
        have hcal :=
          core.toProofLengthCodeSemanticsCore.proof_length_eq_minProofCodeSize
            (core.scale_data.powerBoundRawCode w.n) ⟨w.n, rfl⟩
        have hw :
            w.n = core.computable_search_exclusion.witness U hU N :=
          rfl
        unfold actualProofLengthMeasured
        rw [← hw]
        rw [hcal]
        exact hmin
    }

theorem actualProofLengthGapOfComputableFiniteSearchNoSmallCore_witness_eq
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((actualProofLengthGapOfComputableFiniteSearchNoSmallCore core)
        |>.gap_for_polynomial_upper U hU).witness N =
      core.computable_search_exclusion.witness U hU N :=
  rfl

theorem actualProofLengthGapOfComputableFiniteSearchNoSmallCore_strict_at_witness
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q})
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    U (((actualProofLengthGapOfComputableFiniteSearchNoSmallCore core)
        |>.gap_for_polynomial_upper U hU).witness N) <
      actualProofLengthMeasured core.scale_data
        (((actualProofLengthGapOfComputableFiniteSearchNoSmallCore core)
          |>.gap_for_polynomial_upper U hU).witness N) :=
  ((actualProofLengthGapOfComputableFiniteSearchNoSmallCore core)
    |>.gap_for_polynomial_upper U hU).strict_at_witness N

/-- Consistent proof-length frontier: it packages the computable no-small-code
core as an actual proof-length gap plus the existing checked lower-bound core.
Unlike `Month9Month10ActualProofLengthGapFrontier`, this frontier does not ask
for `proof_length = scale`; that equality is incompatible with the current
polynomial-bound field on `scale`. -/
structure Month9Month10ComputableNoSmallProofLengthFrontier :
    Type (q + 1) where
  core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}

namespace Month9Month10ComputableNoSmallProofLengthFrontier

def scale_data
    (h : Month9Month10ComputableNoSmallProofLengthFrontier.{q}) :
    InternalPudlakTheorem5ScaleData :=
  h.core.scale_data

def actual_proof_length_gap
    (h : Month9Month10ComputableNoSmallProofLengthFrontier.{q}) :
    ComputableSearchGapCertificate
      (actualProofLengthMeasured h.scale_data) :=
  actualProofLengthGapOfComputableFiniteSearchNoSmallCore h.core

def checkedLowerBoundCore
    (h : Month9Month10ComputableNoSmallProofLengthFrontier.{q}) :
    InternalPudlakTheorem5CheckedLowerBoundCore :=
  h.core.toProofLengthCodeSemanticsCore.toCheckedLowerBoundCore

theorem checkedLength_eq_minProofCodeSize
    (h : Month9Month10ComputableNoSmallProofLengthFrontier.{q})
    (n : Nat) :
    h.checkedLowerBoundCore.checkedLength n =
      h.core.proof_code_semantics.minProofCodeSize
        (h.scale_data.powerBoundRawCode n) ⟨n, rfl⟩ :=
  rfl

theorem proof_length_eq_minProofCodeSize
    (h : Month9Month10ComputableNoSmallProofLengthFrontier.{q})
    (n : Nat) :
    actualProofLengthMeasured h.scale_data n =
      (h.core.proof_code_semantics.minProofCodeSize
        (h.scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) := by
  unfold actualProofLengthMeasured scale_data
  exact
    h.core.toProofLengthCodeSemanticsCore.proof_length_eq_minProofCodeSize
      (h.core.scale_data.powerBoundRawCode n) ⟨n, rfl⟩

theorem checked_lower_bound
    (h : Month9Month10ComputableNoSmallProofLengthFrontier.{q}) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      h.scale_data h.checkedLowerBoundCore.checkedLength :=
  h.checkedLowerBoundCore.checked_lower_bound

theorem actual_gap_witness_eq_core
    (h : Month9Month10ComputableNoSmallProofLengthFrontier.{q})
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((h.actual_proof_length_gap.gap_for_polynomial_upper U hU).witness N) =
      h.core.computable_search_exclusion.witness U hU N :=
  rfl

structure Audit
    (h : Month9Month10ComputableNoSmallProofLengthFrontier.{q}) :
    Prop where
  actualProofLengthGap :
    Nonempty
      (ComputableSearchGapCertificate
        (actualProofLengthMeasured h.scale_data))
  checkedCore :
    Nonempty InternalPudlakTheorem5CheckedLowerBoundCore
  checkedLowerBound :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      h.scale_data h.checkedLowerBoundCore.checkedLength
  proofLengthEqMinProofCodeSize :
    ∀ n : Nat,
      actualProofLengthMeasured h.scale_data n =
        (h.core.proof_code_semantics.minProofCodeSize
          (h.scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real)

theorem audit
    (h : Month9Month10ComputableNoSmallProofLengthFrontier.{q}) :
    Audit h where
  actualProofLengthGap := ⟨h.actual_proof_length_gap⟩
  checkedCore := ⟨h.checkedLowerBoundCore⟩
  checkedLowerBound := h.checked_lower_bound
  proofLengthEqMinProofCodeSize := h.proof_length_eq_minProofCodeSize

theorem closure
    (h : Month9Month10ComputableNoSmallProofLengthFrontier.{q}) :
    h.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured h.scale_data)) ∧
      Nonempty InternalPudlakTheorem5CheckedLowerBoundCore ∧
      InternalPudlakTheorem5CheckedPowerBoundLowerBound
        h.scale_data h.checkedLowerBoundCore.checkedLength :=
  ⟨h.audit,
    ⟨h.actual_proof_length_gap⟩,
    ⟨h.checkedLowerBoundCore⟩,
    h.checked_lower_bound⟩

end Month9Month10ComputableNoSmallProofLengthFrontier

/-- Month 9-10 frontier for the final proof-length lower-gap handoff.  This is
not a theorem-5 literature certificate and not a PA/Hilbert checker; it is the
smallest Month 9-10-side target that the checker layer must instantiate. -/
structure Month9Month10ActualProofLengthGapFrontier
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  actual_proof_length_gap :
    ComputableSearchGapCertificate
      (actualProofLengthMeasured scale_data)
  proof_length_eq_scale :
    ∀ n : Nat,
      actualProofLengthMeasured scale_data n =
        scaleMeasured scale_data n
  scale_strict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b

namespace Month9Month10ActualProofLengthGapFrontier

theorem scale_strict_of_timeConstructibleBound_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0) :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b := by
  intro a b hab
  rw [scale_data.scale_eq a, scale_data.scale_eq b]
  exact
    pow_lt_pow_left₀
      (time_bound_strict hab)
      (Nat.zero_le (scale_data.time_constructible_bound a))
      exponent_ne_zero

def ofTimeConstructibleBoundStrict
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
    Month9Month10ActualProofLengthGapFrontier scale_data where
  actual_proof_length_gap := actual_proof_length_gap
  proof_length_eq_scale := proof_length_eq_scale
  scale_strict :=
    scale_strict_of_timeConstructibleBound_strict
      time_bound_strict exponent_ne_zero

theorem ofTimeConstructibleBoundStrict_scale_strict_apply
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
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    {a b : Nat} (hab : a < b) :
    (ofTimeConstructibleBoundStrict
      actual_proof_length_gap proof_length_eq_scale
      time_bound_strict exponent_ne_zero).scale_strict hab =
      scale_strict_of_timeConstructibleBound_strict
        time_bound_strict exponent_ne_zero hab :=
  rfl

def scale_search_gap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data) :
    ComputableSearchGapCertificate (scaleMeasured scale_data) :=
  transportComputableSearchGap h.proof_length_eq_scale
    h.actual_proof_length_gap

theorem scale_search_gap_witness_eq_actual
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((h.scale_search_gap.gap_for_polynomial_upper U hU).witness N) =
      (h.actual_proof_length_gap.gap_for_polynomial_upper U hU).witness N :=
  rfl

theorem scale_search_gap_strict_at_witness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    U ((h.scale_search_gap.gap_for_polynomial_upper U hU).witness N) <
      scaleMeasured scale_data
        ((h.scale_search_gap.gap_for_polynomial_upper U hU).witness N) :=
  (h.scale_search_gap.gap_for_polynomial_upper U hU).strict_at_witness N

theorem scale_checked_lower_bound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data) :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data scale_data.scale := by
  intro f hf
  exact
    Filter.frequently_atTop.2
      (fun N =>
        ⟨(h.scale_search_gap.gap_for_polynomial_upper f hf).witness N,
          (h.scale_search_gap.gap_for_polynomial_upper f hf).witness_ge N,
          by
            simpa [scaleMeasured] using
              (h.scale_search_gap.gap_for_polynomial_upper f hf).strict_at_witness N⟩)

def toCheckedLowerBoundCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data) :
    InternalPudlakTheorem5CheckedLowerBoundCore where
  scale_data := scale_data
  checkedLength := scale_data.scale
  checked_lower_bound := h.scale_checked_lower_bound
  proof_length_exact := by
    intro n
    exact h.proof_length_eq_scale n

theorem checked_exactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data) (n : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode n) =
      (h.toCheckedLowerBoundCore.checkedLength n : Real) :=
  h.toCheckedLowerBoundCore.proof_length_exact n

theorem scale_strict_statement
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data) :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b :=
  h.scale_strict

def toCheckedLowerBoundCoreChecklist
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyLowerBoundTransfer)
    (transfer_to_graft :
      _root_.PartialConsistencyToReflectionGraftLowerBoundTransfer)
    (project_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox) :
    Month9Month10CheckedLowerBoundCoreChecklist where
  theorem5_checked_core := h.toCheckedLowerBoundCore
  strengthened_to_partial := strengthened_to_partial
  transfer_to_graft := transfer_to_graft
  computable_gap := project_gap

def toCheckedLowerBoundCoreChecklistOfConstantPieces
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data)
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

theorem checked_frontier_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data) :
    Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
      Nonempty (ComputableSearchGapCertificate (scaleMeasured scale_data)) ∧
        InternalPudlakTheorem5CheckedPowerBoundLowerBound
          scale_data scale_data.scale ∧
          Nonempty InternalPudlakTheorem5CheckedLowerBoundCore ∧
            (∀ n : Nat,
              _root_.proof_length _root_.ProofSystem.PA
                  _root_.ProofLengthMeasure.symbolSize
                  (scale_data.powerBoundRawCode n) =
                (scale_data.scale n : Real)) ∧
              (∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b) :=
  ⟨⟨h.actual_proof_length_gap⟩,
    ⟨h.scale_search_gap⟩,
    h.scale_checked_lower_bound,
    ⟨h.toCheckedLowerBoundCore⟩,
    h.proof_length_eq_scale,
    h.scale_strict⟩

theorem checked_frontier_project_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data)
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

theorem checked_frontier_project_closure_of_constant_pieces
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data)
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
  h.checked_frontier_project_closure
    (InternalPudlakTheorem5TransferPieces.strengthenedToPartialTransferOfConstant
      strengthened_to_partial)
    (InternalPudlakTheorem5TransferPieces.partialToGraftTransferOfConstant
      partial_to_graft)
    project_gap
    project_upper

theorem not_rational_of_constant_pieces
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data)
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

structure Audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data) : Prop where
  actualProofLengthGap :
    Nonempty
      (ComputableSearchGapCertificate
        (actualProofLengthMeasured scale_data))
  transportedScaleGap :
    Nonempty (ComputableSearchGapCertificate (scaleMeasured scale_data))
  proofLengthEqScale :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (scale_data.scale n : Real)
  scaleStrict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b
  checkedLowerBound :
    InternalPudlakTheorem5CheckedPowerBoundLowerBound
      scale_data scale_data.scale
  checkedCore :
    Nonempty InternalPudlakTheorem5CheckedLowerBoundCore

theorem audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data) :
    Audit h where
  actualProofLengthGap := ⟨h.actual_proof_length_gap⟩
  transportedScaleGap := ⟨h.scale_search_gap⟩
  proofLengthEqScale := h.proof_length_eq_scale
  scaleStrict := h.scale_strict
  checkedLowerBound := h.scale_checked_lower_bound
  checkedCore := ⟨h.toCheckedLowerBoundCore⟩

end Month9Month10ActualProofLengthGapFrontier

/-- Negative audit for the older exact-scale frontier.  With the current
`scale_polynomial_bound` field, transporting an actual proof-length gap across
`proof_length = scale` would create an impossible gap for the polynomially
bounded scale. -/
theorem no_actual_proof_length_gap_frontier_for_internal_scale
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data) :
    False :=
  no_scale_search_gap_for_internal_scale scale_data h.scale_search_gap

/-- Frontier that starts from a gap for the calibrated scale itself.  Once
`proof_length(powerBoundRawCode n) = scale n` is available, this produces the
actual proof-length gap required by the final three-certificate endpoint. -/
structure Month9Month10ScaleGapFrontier
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  scale_gap :
    ComputableSearchGapCertificate (scaleMeasured scale_data)
  proof_length_eq_scale :
    ∀ n : Nat,
      actualProofLengthMeasured scale_data n =
        scaleMeasured scale_data n
  scale_strict :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b

namespace Month9Month10ScaleGapFrontier

def actual_proof_length_gap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ScaleGapFrontier scale_data) :
    ComputableSearchGapCertificate
      (actualProofLengthMeasured scale_data) :=
  transportComputableSearchGap
    (fun n => (h.proof_length_eq_scale n).symm)
    h.scale_gap

theorem actual_proof_length_gap_witness_eq_scale
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ScaleGapFrontier scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((h.actual_proof_length_gap.gap_for_polynomial_upper U hU).witness N) =
      (h.scale_gap.gap_for_polynomial_upper U hU).witness N :=
  rfl

def toActualProofLengthGapFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ScaleGapFrontier scale_data) :
    Month9Month10ActualProofLengthGapFrontier scale_data where
  actual_proof_length_gap :=
    h.actual_proof_length_gap
  proof_length_eq_scale :=
    h.proof_length_eq_scale
  scale_strict :=
    h.scale_strict

def ofTimeConstructibleBoundStrict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (scale_gap :
      ComputableSearchGapCertificate (scaleMeasured scale_data))
    (proof_length_eq_scale :
      ∀ n : Nat,
        actualProofLengthMeasured scale_data n =
          scaleMeasured scale_data n)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0) :
    Month9Month10ScaleGapFrontier scale_data where
  scale_gap := scale_gap
  proof_length_eq_scale := proof_length_eq_scale
  scale_strict :=
    Month9Month10ActualProofLengthGapFrontier.scale_strict_of_timeConstructibleBound_strict
      time_bound_strict exponent_ne_zero

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ScaleGapFrontier scale_data) :
    Nonempty (ComputableSearchGapCertificate (scaleMeasured scale_data)) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
        h.toActualProofLengthGapFrontier.Audit ∧
          Nonempty InternalPudlakTheorem5CheckedLowerBoundCore :=
  ⟨⟨h.scale_gap⟩,
    ⟨h.actual_proof_length_gap⟩,
    h.toActualProofLengthGapFrontier.audit,
    ⟨h.toActualProofLengthGapFrontier.toCheckedLowerBoundCore⟩⟩

end Month9Month10ScaleGapFrontier

theorem no_scale_gap_frontier_for_internal_scale
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ScaleGapFrontier scale_data) :
    False :=
  no_scale_search_gap_for_internal_scale scale_data h.scale_gap

/-- Proof-length-to-scale exactness frontier.  It separates the hard equality
`proof_length(powerBoundRawCode n) = scale n` into the already-standard
`ProofLengthCodeSemantics.Calibration` plus a checker-native exactness theorem
for `minProofCodeSize`. -/
structure Month9Month10ProofLengthScaleExactnessFrontier : Type (q + 1) where
  core : InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q}
  minProofCodeSize_eq_scale :
    ∀ n : Nat,
      core.proof_code_semantics.minProofCodeSize
        (core.scale_data.powerBoundRawCode n) ⟨n, rfl⟩ =
        core.scale_data.scale n

namespace Month9Month10ProofLengthScaleExactnessFrontier

def scale_data
    (h : Month9Month10ProofLengthScaleExactnessFrontier.{q}) :
    InternalPudlakTheorem5ScaleData :=
  h.core.scale_data

theorem proof_length_eq_scale
    (h : Month9Month10ProofLengthScaleExactnessFrontier.{q}) :
    ∀ n : Nat,
      actualProofLengthMeasured h.scale_data n =
        scaleMeasured h.scale_data n := by
  intro n
  unfold actualProofLengthMeasured scaleMeasured
  change
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (h.core.scale_data.powerBoundRawCode n) =
      (h.core.scale_data.scale n : Real)
  have hcal :=
    h.core.proof_length_eq_minProofCodeSize
      (h.core.scale_data.powerBoundRawCode n) ⟨n, rfl⟩
  rw [hcal]
  exact_mod_cast h.minProofCodeSize_eq_scale n

theorem proof_length_eq_scale_at
    (h : Month9Month10ProofLengthScaleExactnessFrontier.{q})
    (n : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (h.scale_data.powerBoundRawCode n) =
      (h.scale_data.scale n : Real) :=
  h.proof_length_eq_scale n

def toScaleGapFrontier
    (h : Month9Month10ProofLengthScaleExactnessFrontier.{q})
    (scale_gap :
      ComputableSearchGapCertificate (scaleMeasured h.scale_data))
    (scale_strict :
      ∀ {a b : Nat}, a < b →
        h.scale_data.scale a < h.scale_data.scale b) :
    Month9Month10ScaleGapFrontier h.scale_data where
  scale_gap := scale_gap
  proof_length_eq_scale := h.proof_length_eq_scale
  scale_strict := scale_strict

theorem toScaleGapFrontier_closure
    (h : Month9Month10ProofLengthScaleExactnessFrontier.{q})
    (scale_gap :
      ComputableSearchGapCertificate (scaleMeasured h.scale_data))
    (scale_strict :
      ∀ {a b : Nat}, a < b →
        h.scale_data.scale a < h.scale_data.scale b) :
    Nonempty
        (ComputableSearchGapCertificate (scaleMeasured h.scale_data)) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured h.scale_data)) ∧
        (Month9Month10ScaleGapFrontier.toActualProofLengthGapFrontier
          (h.toScaleGapFrontier scale_gap scale_strict)).Audit ∧
          Nonempty InternalPudlakTheorem5CheckedLowerBoundCore :=
  (h.toScaleGapFrontier scale_gap scale_strict).closure

end Month9Month10ProofLengthScaleExactnessFrontier

theorem month9_month10_actual_proof_length_gap_frontier_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (h : Month9Month10ActualProofLengthGapFrontier scale_data) :
    h.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
      Nonempty (ComputableSearchGapCertificate (scaleMeasured scale_data)) ∧
      Nonempty InternalPudlakTheorem5CheckedLowerBoundCore :=
  ⟨h.audit,
    ⟨h.actual_proof_length_gap⟩,
    ⟨h.scale_search_gap⟩,
    ⟨h.toCheckedLowerBoundCore⟩⟩

theorem month9_month10_timeConstructibleBoundStrict_frontier_closure
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
    (Month9Month10ActualProofLengthGapFrontier.ofTimeConstructibleBoundStrict
        actual_proof_length_gap proof_length_eq_scale
        time_bound_strict exponent_ne_zero).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
      Nonempty (ComputableSearchGapCertificate (scaleMeasured scale_data)) ∧
      Nonempty InternalPudlakTheorem5CheckedLowerBoundCore :=
  month9_month10_actual_proof_length_gap_frontier_closure
    (Month9Month10ActualProofLengthGapFrontier.ofTimeConstructibleBoundStrict
      actual_proof_length_gap proof_length_eq_scale
      time_bound_strict exponent_ne_zero)

end SondowProjectMonth9Month10ProofLengthGapFrontier
end SondowMainCheckedCodeBridge

end
