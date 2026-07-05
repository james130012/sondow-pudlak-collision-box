/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectComputableGapCertificate

/-!
# Month 5 gap domination surface

This module separates the final growth gap from the Pudlak lower-bound
certificate.  The lower-bound certificate supplies `ProofLengthGap`; the
Month 5 surface names the upper function, the measured lower function, and the
standalone strict-gap certificate used by the collision core.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

abbrev Month5UpperBoundFunction (bound : Nat → Real) : Nat → Real :=
  bound

abbrev Month5SondowCombinedUpperBound
    (bounds : SondowComponentBounds) : Nat → Real :=
  bounds.combined

noncomputable abbrev Month5LowerBoundFunction : Nat → Real :=
  canonicalCnBoxPABox.length

theorem month5SondowCombinedUpperBound_poly
    (bounds : SondowComponentBounds) :
    IsPolynomialBound (Month5SondowCombinedUpperBound bounds) :=
  bounds.combined_poly

theorem month5UpperBoundFunction_combined_eq
    (bounds : SondowComponentBounds) (n : Nat) :
    Month5UpperBoundFunction
        (Month5SondowCombinedUpperBound bounds) n =
      bounds.combined n :=
  rfl

structure EventualStrictCnBoxGap (U L : Nat → Real) : Prop where
  gap_after : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ U n < L n

structure CofinalStrictCnBoxGap (U L : Nat → Real) : Prop where
  gap_after : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ U n < L n

structure ThresholdStrictCnBoxGap (U L : Nat → Real) where
  threshold : Nat
  gap_at_or_above : ∀ n : Nat, threshold ≤ n → U n < L n

structure StrictGapPersistence (U L : Nat → Real) : Prop where
  persists :
    ∀ m n : Nat, m ≤ n → U m < L m → U n < L n

structure Month5CofinalGrowthDominationCertificate
    (U L : Nat → Real) : Prop where
  cofinal_gap : CofinalStrictCnBoxGap U L

structure Month5GapPersistenceCertificate
    (U L : Nat → Real) : Prop where
  persistence : StrictGapPersistence U L

structure Month5IndependentGrowthDominationCertificate
    (U L : Nat → Real) : Prop where
  strict_gap : EventualStrictCnBoxGap U L

structure Month5ThresholdGrowthDominationCertificate
    (U L : Nat → Real) where
  threshold_gap : ThresholdStrictCnBoxGap U L

structure Month5FinalExpressionThresholdCertificate
    (bounds : SondowComponentBounds) where
  threshold : Nat
  gap_at_or_above :
    ∀ n : Nat, threshold ≤ n →
      bounds.combined n < canonicalCnBoxPABox.length n

structure Month5FinalExpressionGapPersistenceCertificate
    (bounds : SondowComponentBounds) : Prop where
  persistence :
    StrictGapPersistence
      (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
      Month5LowerBoundFunction

structure Month5MonotoneGapPersistenceCertificate
    (U L : Nat → Real) : Prop where
  upper_antitone : Antitone U
  lower_monotone : Monotone L

structure Month5FinalExpressionMonotoneGapPersistenceCertificate
    (bounds : SondowComponentBounds) : Prop where
  upper_antitone :
    Antitone
      (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
  lower_monotone : Monotone Month5LowerBoundFunction

structure Month5GapDifferencePersistenceCertificate
    (U L : Nat → Real) : Prop where
  gap_difference_monotone : Monotone (fun n : Nat => L n - U n)

structure Month5FinalExpressionGapDifferencePersistenceCertificate
    (bounds : SondowComponentBounds) : Prop where
  gap_difference_monotone :
    Monotone (fun n : Nat =>
      Month5LowerBoundFunction n -
        Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds) n)

structure Month5EventualGapDifferencePersistenceCertificate
    (U L : Nat → Real) where
  start : Nat
  gap_difference_monotone_at_or_above :
    ∀ m n : Nat, start ≤ m → m ≤ n → L m - U m ≤ L n - U n

structure Month5FinalExpressionEventualGapDifferencePersistenceCertificate
    (bounds : SondowComponentBounds) where
  start : Nat
  gap_difference_monotone_at_or_above :
    ∀ m n : Nat, start ≤ m → m ≤ n →
      Month5LowerBoundFunction m -
        Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds) m ≤
      Month5LowerBoundFunction n -
        Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds) n

structure Month5StepGapDifferencePersistenceCertificate
    (U L : Nat → Real) where
  start : Nat
  step_gap_difference_monotone :
    ∀ n : Nat, start ≤ n →
      L n - U n ≤ L (n + 1) - U (n + 1)

structure Month5FinalExpressionStepGapDifferencePersistenceCertificate
    (bounds : SondowComponentBounds) where
  start : Nat
  step_gap_difference_monotone :
    ∀ n : Nat, start ≤ n →
      Month5LowerBoundFunction n -
        Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds) n ≤
      Month5LowerBoundFunction (n + 1) -
        Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds)
          (n + 1)

theorem strictGapPersistence_of_antitone_monotone
    {U L : Nat → Real}
    (hU : Antitone U) (hL : Monotone L) :
    StrictGapPersistence U L := by
  refine ⟨?_⟩
  intro m n hmn hgap
  exact lt_of_le_of_lt (hU hmn) (lt_of_lt_of_le hgap (hL hmn))

theorem strictGapPersistence_of_gap_difference_monotone
    {U L : Nat → Real}
    (hdelta : Monotone (fun n : Nat => L n - U n)) :
    StrictGapPersistence U L := by
  refine ⟨?_⟩
  intro m n hmn hgap
  have hpos_m : 0 < L m - U m := sub_pos.mpr hgap
  have hle : L m - U m ≤ L n - U n := hdelta hmn
  have hpos_n : 0 < L n - U n := lt_of_lt_of_le hpos_m hle
  exact sub_pos.mp hpos_n

def Month5MonotoneGapPersistenceCertificate.toGapPersistenceCertificate
    {U L : Nat → Real}
    (cert : Month5MonotoneGapPersistenceCertificate U L) :
    Month5GapPersistenceCertificate U L where
  persistence :=
    strictGapPersistence_of_antitone_monotone
      cert.upper_antitone cert.lower_monotone

def Month5FinalExpressionMonotoneGapPersistenceCertificate.toGapPersistenceCertificate
    {bounds : SondowComponentBounds}
    (cert : Month5FinalExpressionMonotoneGapPersistenceCertificate bounds) :
    Month5FinalExpressionGapPersistenceCertificate bounds where
  persistence :=
    strictGapPersistence_of_antitone_monotone
      cert.upper_antitone cert.lower_monotone

def Month5GapDifferencePersistenceCertificate.toGapPersistenceCertificate
    {U L : Nat → Real}
    (cert : Month5GapDifferencePersistenceCertificate U L) :
    Month5GapPersistenceCertificate U L where
  persistence :=
    strictGapPersistence_of_gap_difference_monotone
      cert.gap_difference_monotone

def Month5FinalExpressionGapDifferencePersistenceCertificate.toGapPersistenceCertificate
    {bounds : SondowComponentBounds}
    (cert : Month5FinalExpressionGapDifferencePersistenceCertificate bounds) :
    Month5FinalExpressionGapPersistenceCertificate bounds where
  persistence :=
    strictGapPersistence_of_gap_difference_monotone
      cert.gap_difference_monotone

def Month5GapDifferencePersistenceCertificate.toEventualGapDifferencePersistenceCertificate
    {U L : Nat → Real}
    (cert : Month5GapDifferencePersistenceCertificate U L) :
    Month5EventualGapDifferencePersistenceCertificate U L where
  start := 0
  gap_difference_monotone_at_or_above := by
    intro m n _hmn_start hmn
    exact cert.gap_difference_monotone hmn

def Month5FinalExpressionGapDifferencePersistenceCertificate.toEventualGapDifferencePersistenceCertificate
    {bounds : SondowComponentBounds}
    (cert : Month5FinalExpressionGapDifferencePersistenceCertificate bounds) :
    Month5FinalExpressionEventualGapDifferencePersistenceCertificate bounds where
  start := 0
  gap_difference_monotone_at_or_above := by
    intro m n _hmn_start hmn
    exact cert.gap_difference_monotone hmn

def Month5FinalExpressionEventualGapDifferencePersistenceCertificate.toEventualGapDifferencePersistenceCertificate
    {bounds : SondowComponentBounds}
    (cert : Month5FinalExpressionEventualGapDifferencePersistenceCertificate
      bounds) :
    Month5EventualGapDifferencePersistenceCertificate
      (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
      Month5LowerBoundFunction where
  start := cert.start
  gap_difference_monotone_at_or_above :=
    cert.gap_difference_monotone_at_or_above

theorem eventual_gap_difference_of_step_gap_difference
    {U L : Nat → Real} {start : Nat}
    (hstep :
      ∀ n : Nat, start ≤ n →
        L n - U n ≤ L (n + 1) - U (n + 1)) :
    ∀ m n : Nat, start ≤ m → m ≤ n → L m - U m ≤ L n - U n := by
  intro m n hstart hmn
  induction hmn with
  | refl => rfl
  | step hmn ih =>
      exact le_trans ih (hstep _ (le_trans hstart hmn))

def Month5StepGapDifferencePersistenceCertificate.toEventualGapDifferencePersistenceCertificate
    {U L : Nat → Real}
    (cert : Month5StepGapDifferencePersistenceCertificate U L) :
    Month5EventualGapDifferencePersistenceCertificate U L where
  start := cert.start
  gap_difference_monotone_at_or_above :=
    eventual_gap_difference_of_step_gap_difference
      cert.step_gap_difference_monotone

def Month5FinalExpressionStepGapDifferencePersistenceCertificate.toEventualGapDifferencePersistenceCertificate
    {bounds : SondowComponentBounds}
    (cert : Month5FinalExpressionStepGapDifferencePersistenceCertificate
      bounds) :
    Month5FinalExpressionEventualGapDifferencePersistenceCertificate bounds where
  start := cert.start
  gap_difference_monotone_at_or_above :=
    eventual_gap_difference_of_step_gap_difference
      cert.step_gap_difference_monotone

theorem month5MonotoneGapPersistence_nonempty_to_persistence
    {U L : Nat → Real}
    (hmono : Nonempty (Month5MonotoneGapPersistenceCertificate U L)) :
    Nonempty (Month5GapPersistenceCertificate U L) := by
  rcases hmono with ⟨cert⟩
  exact ⟨cert.toGapPersistenceCertificate⟩

theorem month5GapDifferencePersistence_nonempty_to_persistence
    {U L : Nat → Real}
    (hdiff : Nonempty (Month5GapDifferencePersistenceCertificate U L)) :
    Nonempty (Month5GapPersistenceCertificate U L) := by
  rcases hdiff with ⟨cert⟩
  exact ⟨cert.toGapPersistenceCertificate⟩

theorem month5FinalExpressionGapDifferencePersistence_nonempty_to_persistence
    {bounds : SondowComponentBounds}
    (hdiff :
      Nonempty (Month5FinalExpressionGapDifferencePersistenceCertificate
        bounds)) :
    Nonempty (Month5FinalExpressionGapPersistenceCertificate bounds) := by
  rcases hdiff with ⟨cert⟩
  exact ⟨cert.toGapPersistenceCertificate⟩

theorem month5FinalExpressionGapDifferencePersistence_nonempty_to_eventual
    {bounds : SondowComponentBounds}
    (hdiff :
      Nonempty (Month5FinalExpressionGapDifferencePersistenceCertificate
        bounds)) :
    Nonempty
      (Month5FinalExpressionEventualGapDifferencePersistenceCertificate
        bounds) := by
  rcases hdiff with ⟨cert⟩
  exact ⟨cert.toEventualGapDifferencePersistenceCertificate⟩

theorem month5FinalExpressionEventualGapDifferencePersistence_nonempty_to_generic
    {bounds : SondowComponentBounds}
    (hdiff :
      Nonempty
        (Month5FinalExpressionEventualGapDifferencePersistenceCertificate
          bounds)) :
    Nonempty
      (Month5EventualGapDifferencePersistenceCertificate
        (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
        Month5LowerBoundFunction) := by
  rcases hdiff with ⟨cert⟩
  exact ⟨cert.toEventualGapDifferencePersistenceCertificate⟩

theorem month5StepGapDifferencePersistence_nonempty_to_eventual
    {U L : Nat → Real}
    (hstep : Nonempty (Month5StepGapDifferencePersistenceCertificate U L)) :
    Nonempty (Month5EventualGapDifferencePersistenceCertificate U L) := by
  rcases hstep with ⟨cert⟩
  exact ⟨cert.toEventualGapDifferencePersistenceCertificate⟩

theorem month5FinalExpressionStepGapDifferencePersistence_nonempty_to_eventual
    {bounds : SondowComponentBounds}
    (hstep :
      Nonempty
        (Month5FinalExpressionStepGapDifferencePersistenceCertificate
          bounds)) :
    Nonempty
      (Month5FinalExpressionEventualGapDifferencePersistenceCertificate
        bounds) := by
  rcases hstep with ⟨cert⟩
  exact ⟨cert.toEventualGapDifferencePersistenceCertificate⟩

theorem month5FinalExpressionMonotoneGapPersistence_nonempty_to_persistence
    {bounds : SondowComponentBounds}
    (hmono :
      Nonempty (Month5FinalExpressionMonotoneGapPersistenceCertificate
        bounds)) :
    Nonempty (Month5FinalExpressionGapPersistenceCertificate bounds) := by
  rcases hmono with ⟨cert⟩
  exact ⟨cert.toGapPersistenceCertificate⟩

def Month5FinalExpressionGapVerifier
    (bounds : SondowComponentBounds) (candidate : Nat) : Prop :=
  ∀ n : Nat, candidate ≤ n →
    bounds.combined n < canonicalCnBoxPABox.length n

structure Month5VerifiedThresholdCandidate
    (bounds : SondowComponentBounds) where
  candidate : Nat
  verifier : Month5FinalExpressionGapVerifier bounds candidate

structure Month5ThresholdSearchSpecification
    (bounds : SondowComponentBounds) where
  accepts : Nat → Prop
  accepts_decidable : ∀ candidate : Nat, Decidable (accepts candidate)
  accepts_sound :
    ∀ candidate : Nat, accepts candidate →
      Month5FinalExpressionGapVerifier bounds candidate

structure Month5ThresholdSearchCertificate
    (bounds : SondowComponentBounds) where
  search_spec : Month5ThresholdSearchSpecification bounds
  candidate : Nat
  candidate_accepted : search_spec.accepts candidate

theorem isPolynomialBound_of_pointwise_eq
    {f g : Nat → Real}
    (hf : IsPolynomialBound f)
    (hgf : ∀ n : Nat, g n = f n) :
    IsPolynomialBound g := by
  rcases hf with ⟨c, k, hf_bound⟩
  exact ⟨c, k, fun n => by
    rw [hgf n]
    exact hf_bound n⟩

def CofinalStrictCnBoxGap.toEventualStrictCnBoxGap
    {U L : Nat → Real}
    (hgap : CofinalStrictCnBoxGap U L) :
    EventualStrictCnBoxGap U L where
  gap_after := hgap.gap_after

def EventualStrictCnBoxGap.toCofinalStrictCnBoxGap
    {U L : Nat → Real}
    (hgap : EventualStrictCnBoxGap U L) :
    CofinalStrictCnBoxGap U L where
  gap_after := hgap.gap_after

theorem cofinalStrictCnBoxGap_iff_eventualStrictCnBoxGap
    {U L : Nat → Real} :
    CofinalStrictCnBoxGap U L ↔ EventualStrictCnBoxGap U L :=
  ⟨CofinalStrictCnBoxGap.toEventualStrictCnBoxGap,
    EventualStrictCnBoxGap.toCofinalStrictCnBoxGap⟩

theorem cofinalStrictCnBoxGap_and_persistence_to_threshold
    {U L : Nat → Real}
    (hgap : CofinalStrictCnBoxGap U L)
    (hpersist : StrictGapPersistence U L) :
    Nonempty (ThresholdStrictCnBoxGap U L) := by
  rcases hgap.gap_after 0 with ⟨threshold, _hzero, hlt⟩
  exact ⟨{
    threshold := threshold
    gap_at_or_above := by
      intro n hn
      exact hpersist.persists threshold n hn hlt }⟩

theorem cofinalStrictCnBoxGap_and_eventual_gap_difference_to_threshold
    {U L : Nat → Real}
    (hgap : CofinalStrictCnBoxGap U L)
    (hdiff : Month5EventualGapDifferencePersistenceCertificate U L) :
    Nonempty (ThresholdStrictCnBoxGap U L) := by
  rcases hgap.gap_after hdiff.start with ⟨threshold, hstart, hlt⟩
  exact ⟨{
    threshold := threshold
    gap_at_or_above := by
      intro n hn
      have hpos_threshold : 0 < L threshold - U threshold :=
        sub_pos.mpr hlt
      have hle : L threshold - U threshold ≤ L n - U n :=
        hdiff.gap_difference_monotone_at_or_above
          threshold n hstart hn
      have hpos_n : 0 < L n - U n :=
        lt_of_lt_of_le hpos_threshold hle
      exact sub_pos.mp hpos_n }⟩

def EventualStrictCnBoxGap.transport
    {U L U' L' : Nat → Real}
    (hgap : EventualStrictCnBoxGap U L)
    (hU : ∀ n : Nat, U' n = U n)
    (hL : ∀ n : Nat, L' n = L n) :
    EventualStrictCnBoxGap U' L' where
  gap_after := by
    intro N
    rcases hgap.gap_after N with ⟨n, hn_ge, hlt⟩
    exact ⟨n, hn_ge, by simpa [hU n, hL n] using hlt⟩

theorem eventualStrictCnBoxGap_iff_of_pointwise_eq
    {U L U' L' : Nat → Real}
    (hU : ∀ n : Nat, U' n = U n)
    (hL : ∀ n : Nat, L' n = L n) :
    EventualStrictCnBoxGap U L ↔ EventualStrictCnBoxGap U' L' :=
  ⟨fun hgap => hgap.transport hU hL,
    fun hgap => hgap.transport (fun n => (hU n).symm) (fun n => (hL n).symm)⟩

def ThresholdStrictCnBoxGap.transport
    {U L U' L' : Nat → Real}
    (hgap : ThresholdStrictCnBoxGap U L)
    (hU : ∀ n : Nat, U' n = U n)
    (hL : ∀ n : Nat, L' n = L n) :
    ThresholdStrictCnBoxGap U' L' where
  threshold := hgap.threshold
  gap_at_or_above := by
    intro n hn
    simpa [hU n, hL n] using hgap.gap_at_or_above n hn

theorem thresholdStrictCnBoxGap_iff_of_pointwise_eq
    {U L U' L' : Nat → Real}
    (hU : ∀ n : Nat, U' n = U n)
    (hL : ∀ n : Nat, L' n = L n) :
    Nonempty (ThresholdStrictCnBoxGap U L) ↔
      Nonempty (ThresholdStrictCnBoxGap U' L') :=
  ⟨fun hgap => by
      rcases hgap with ⟨hgap⟩
      exact ⟨hgap.transport hU hL⟩,
    fun hgap => by
      rcases hgap with ⟨hgap⟩
      exact ⟨hgap.transport (fun n => (hU n).symm)
        (fun n => (hL n).symm)⟩⟩

def Month5CofinalGrowthDominationCertificate.transport
    {U L U' L' : Nat → Real}
    (cert : Month5CofinalGrowthDominationCertificate U L)
    (hU : ∀ n : Nat, U' n = U n)
    (hL : ∀ n : Nat, L' n = L n) :
    Month5CofinalGrowthDominationCertificate U' L' where
  cofinal_gap :=
    (cert.cofinal_gap.toEventualStrictCnBoxGap.transport hU hL)
      |>.toCofinalStrictCnBoxGap

def Month5ThresholdGrowthDominationCertificate.transport
    {U L U' L' : Nat → Real}
    (cert : Month5ThresholdGrowthDominationCertificate U L)
    (hU : ∀ n : Nat, U' n = U n)
    (hL : ∀ n : Nat, L' n = L n) :
    Month5ThresholdGrowthDominationCertificate U' L' where
  threshold_gap := cert.threshold_gap.transport hU hL

def ThresholdStrictCnBoxGap.toEventualStrictCnBoxGap
    {U L : Nat → Real}
    (hgap : ThresholdStrictCnBoxGap U L) :
    EventualStrictCnBoxGap U L where
  gap_after := by
    intro N
    refine ⟨max N hgap.threshold, Nat.le_max_left N hgap.threshold, ?_⟩
    exact hgap.gap_at_or_above
      (max N hgap.threshold) (Nat.le_max_right N hgap.threshold)

def ThresholdStrictCnBoxGap.toCofinalStrictCnBoxGap
    {U L : Nat → Real}
    (hgap : ThresholdStrictCnBoxGap U L) :
    CofinalStrictCnBoxGap U L :=
  hgap.toEventualStrictCnBoxGap.toCofinalStrictCnBoxGap

theorem Month5CofinalGrowthDominationCertificate.toThreshold_nonempty
    {U L : Nat → Real}
    (cert : Month5CofinalGrowthDominationCertificate U L)
    (hpersist : Month5GapPersistenceCertificate U L) :
    Nonempty (Month5ThresholdGrowthDominationCertificate U L) := by
  rcases
    cofinalStrictCnBoxGap_and_persistence_to_threshold
      cert.cofinal_gap hpersist.persistence with
    ⟨threshold⟩
  exact ⟨{ threshold_gap := threshold }⟩

def Month5ThresholdGrowthDominationCertificate.toIndependent
    {U L : Nat → Real}
    (cert : Month5ThresholdGrowthDominationCertificate U L) :
    Month5IndependentGrowthDominationCertificate U L where
  strict_gap := cert.threshold_gap.toEventualStrictCnBoxGap

def Month5ThresholdGrowthDominationCertificate.toCofinal
    {U L : Nat → Real}
    (cert : Month5ThresholdGrowthDominationCertificate U L) :
    Month5CofinalGrowthDominationCertificate U L where
  cofinal_gap := cert.threshold_gap.toCofinalStrictCnBoxGap

def Month5IndependentGrowthDominationCertificate.toCofinal
    {U L : Nat → Real}
    (cert : Month5IndependentGrowthDominationCertificate U L) :
    Month5CofinalGrowthDominationCertificate U L where
  cofinal_gap := cert.strict_gap.toCofinalStrictCnBoxGap

def Month5CofinalGrowthDominationCertificate.toIndependent
    {U L : Nat → Real}
    (cert : Month5CofinalGrowthDominationCertificate U L) :
    Month5IndependentGrowthDominationCertificate U L where
  strict_gap := cert.cofinal_gap.toEventualStrictCnBoxGap

theorem month5IndependentGrowthDomination_nonempty_iff_cofinal
    {U L : Nat → Real} :
    Nonempty (Month5IndependentGrowthDominationCertificate U L) ↔
      Nonempty (Month5CofinalGrowthDominationCertificate U L) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toCofinal⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toIndependent⟩

theorem month5Cofinal_and_persistence_to_threshold
    {U L : Nat → Real}
    (hcofinal : Nonempty (Month5CofinalGrowthDominationCertificate U L))
    (hpersist : Nonempty (Month5GapPersistenceCertificate U L)) :
    Nonempty (Month5ThresholdGrowthDominationCertificate U L) := by
  rcases hcofinal with ⟨cofinal⟩
  rcases hpersist with ⟨persist⟩
  exact cofinal.toThreshold_nonempty persist

theorem month5Cofinal_and_monotone_persistence_to_threshold
    {U L : Nat → Real}
    (hcofinal : Nonempty (Month5CofinalGrowthDominationCertificate U L))
    (hmono : Nonempty (Month5MonotoneGapPersistenceCertificate U L)) :
    Nonempty (Month5ThresholdGrowthDominationCertificate U L) :=
  month5Cofinal_and_persistence_to_threshold hcofinal
    (month5MonotoneGapPersistence_nonempty_to_persistence hmono)

theorem month5Cofinal_and_gap_difference_persistence_to_threshold
    {U L : Nat → Real}
    (hcofinal : Nonempty (Month5CofinalGrowthDominationCertificate U L))
    (hdiff : Nonempty (Month5GapDifferencePersistenceCertificate U L)) :
    Nonempty (Month5ThresholdGrowthDominationCertificate U L) :=
  month5Cofinal_and_persistence_to_threshold hcofinal
    (month5GapDifferencePersistence_nonempty_to_persistence hdiff)

theorem month5Cofinal_and_eventual_gap_difference_to_threshold
    {U L : Nat → Real}
    (hcofinal : Nonempty (Month5CofinalGrowthDominationCertificate U L))
    (hdiff :
      Nonempty (Month5EventualGapDifferencePersistenceCertificate U L)) :
    Nonempty (Month5ThresholdGrowthDominationCertificate U L) := by
  rcases hcofinal with ⟨cofinal⟩
  rcases hdiff with ⟨diff⟩
  rcases
    cofinalStrictCnBoxGap_and_eventual_gap_difference_to_threshold
      cofinal.cofinal_gap diff with
    ⟨threshold⟩
  exact ⟨{ threshold_gap := threshold }⟩

theorem month5GapDifferencePersistence_nonempty_to_eventual
    {U L : Nat → Real}
    (hdiff : Nonempty (Month5GapDifferencePersistenceCertificate U L)) :
    Nonempty (Month5EventualGapDifferencePersistenceCertificate U L) := by
  rcases hdiff with ⟨cert⟩
  exact ⟨cert.toEventualGapDifferencePersistenceCertificate⟩

theorem month5Cofinal_and_step_gap_difference_to_threshold
    {U L : Nat → Real}
    (hcofinal : Nonempty (Month5CofinalGrowthDominationCertificate U L))
    (hstep : Nonempty (Month5StepGapDifferencePersistenceCertificate U L)) :
    Nonempty (Month5ThresholdGrowthDominationCertificate U L) :=
  month5Cofinal_and_eventual_gap_difference_to_threshold
    hcofinal
    (month5StepGapDifferencePersistence_nonempty_to_eventual hstep)

def Month5ThresholdGrowthDominationCertificate.toEventualStrictCnBoxGap
    {U L : Nat → Real}
    (cert : Month5ThresholdGrowthDominationCertificate U L) :
    EventualStrictCnBoxGap U L :=
  cert.threshold_gap.toEventualStrictCnBoxGap

def EventualStrictCnBoxGap.toProofLengthGapWitness
    {U L : Nat → Real}
    (hgap : EventualStrictCnBoxGap U L)
    (hL : L = Month5LowerBoundFunction)
    (N : Nat) :
    HasProofLengthGapWitness canonicalCnBoxPABox U N := by
  rcases hgap.gap_after N with ⟨n, hn_ge, hlt⟩
  refine ⟨{ n := n, n_ge := hn_ge, gap_pos := ?_ }⟩
  simpa [hL, Month5LowerBoundFunction] using hlt

def ProofLengthGap.toEventualStrictCnBoxGap
    (hgap : CanonicalCnBoxProofLengthGap)
    (U : Nat → Real) (hU : IsPolynomialBound U) :
    EventualStrictCnBoxGap U Month5LowerBoundFunction where
  gap_after := by
    intro N
    rcases hgap U hU N with ⟨witness⟩
    exact ⟨witness.n, witness.n_ge, witness.gap_pos⟩

def Month5ThresholdGrowthDominationCertificate.toProofLengthGapWitness
    {U : Nat → Real}
    (cert :
      Month5ThresholdGrowthDominationCertificate U Month5LowerBoundFunction)
    (N : Nat) :
    HasProofLengthGapWitness canonicalCnBoxPABox U N :=
  cert.toEventualStrictCnBoxGap.toProofLengthGapWitness rfl N

namespace Month5FinalExpressionThresholdCertificate

def toVerifiedThresholdCandidate
    {bounds : SondowComponentBounds}
    (cert : Month5FinalExpressionThresholdCertificate bounds) :
    Month5VerifiedThresholdCandidate bounds where
  candidate := cert.threshold
  verifier := cert.gap_at_or_above

def toThresholdGrowthDominationCertificate
    {bounds : SondowComponentBounds}
    (cert : Month5FinalExpressionThresholdCertificate bounds) :
    Month5ThresholdGrowthDominationCertificate
      (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
      Month5LowerBoundFunction where
  threshold_gap := {
    threshold := cert.threshold
    gap_at_or_above := by
      intro n hn
      simpa [Month5UpperBoundFunction, Month5SondowCombinedUpperBound,
        Month5LowerBoundFunction]
        using cert.gap_at_or_above n hn }

def toEventualStrictCnBoxGap
    {bounds : SondowComponentBounds}
    (cert : Month5FinalExpressionThresholdCertificate bounds) :
    EventualStrictCnBoxGap
      (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
      Month5LowerBoundFunction :=
  cert.toThresholdGrowthDominationCertificate.toEventualStrictCnBoxGap

def witnessAgainstCombinedUpper
    {bounds : SondowComponentBounds}
    (cert : Month5FinalExpressionThresholdCertificate bounds)
    (N : Nat) :
    HasProofLengthGapWitness
      canonicalCnBoxPABox (Month5SondowCombinedUpperBound bounds) N :=
  cert.toThresholdGrowthDominationCertificate.toProofLengthGapWitness N

end Month5FinalExpressionThresholdCertificate

namespace Month5VerifiedThresholdCandidate

def toFinalExpressionThresholdCertificate
    {bounds : SondowComponentBounds}
    (candidate : Month5VerifiedThresholdCandidate bounds) :
    Month5FinalExpressionThresholdCertificate bounds where
  threshold := candidate.candidate
  gap_at_or_above := candidate.verifier

def toThresholdGrowthDominationCertificate
    {bounds : SondowComponentBounds}
    (candidate : Month5VerifiedThresholdCandidate bounds) :
    Month5ThresholdGrowthDominationCertificate
      (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
      Month5LowerBoundFunction :=
  candidate.toFinalExpressionThresholdCertificate.toThresholdGrowthDominationCertificate

def witnessAgainstCombinedUpper
    {bounds : SondowComponentBounds}
    (candidate : Month5VerifiedThresholdCandidate bounds)
    (N : Nat) :
    HasProofLengthGapWitness
      canonicalCnBoxPABox (Month5SondowCombinedUpperBound bounds) N :=
  candidate.toFinalExpressionThresholdCertificate.witnessAgainstCombinedUpper N

def toThresholdSearchCertificate
    {bounds : SondowComponentBounds}
    (candidate : Month5VerifiedThresholdCandidate bounds) :
    Month5ThresholdSearchCertificate bounds where
  search_spec := {
    accepts := fun k => k = candidate.candidate
    accepts_decidable := fun _ => inferInstance
    accepts_sound := by
      intro k hk
      simpa [hk] using candidate.verifier }
  candidate := candidate.candidate
  candidate_accepted := rfl

end Month5VerifiedThresholdCandidate

namespace Month5ThresholdSearchCertificate

def toVerifiedThresholdCandidate
    {bounds : SondowComponentBounds}
    (cert : Month5ThresholdSearchCertificate bounds) :
    Month5VerifiedThresholdCandidate bounds where
  candidate := cert.candidate
  verifier :=
    cert.search_spec.accepts_sound cert.candidate cert.candidate_accepted

def toFinalExpressionThresholdCertificate
    {bounds : SondowComponentBounds}
    (cert : Month5ThresholdSearchCertificate bounds) :
    Month5FinalExpressionThresholdCertificate bounds :=
  cert.toVerifiedThresholdCandidate.toFinalExpressionThresholdCertificate

def toThresholdGrowthDominationCertificate
    {bounds : SondowComponentBounds}
    (cert : Month5ThresholdSearchCertificate bounds) :
    Month5ThresholdGrowthDominationCertificate
      (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
      Month5LowerBoundFunction :=
  cert.toVerifiedThresholdCandidate.toThresholdGrowthDominationCertificate

def witnessAgainstCombinedUpper
    {bounds : SondowComponentBounds}
    (cert : Month5ThresholdSearchCertificate bounds)
    (N : Nat) :
    HasProofLengthGapWitness
      canonicalCnBoxPABox (Month5SondowCombinedUpperBound bounds) N :=
  cert.toVerifiedThresholdCandidate.witnessAgainstCombinedUpper N

end Month5ThresholdSearchCertificate

theorem month5VerifiedThresholdCandidate_nonempty_iff_finalExpressionThreshold
    {bounds : SondowComponentBounds} :
    Nonempty (Month5VerifiedThresholdCandidate bounds) ↔
      Nonempty (Month5FinalExpressionThresholdCertificate bounds) := by
  constructor
  · intro h
    rcases h with ⟨candidate⟩
    exact ⟨candidate.toFinalExpressionThresholdCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toVerifiedThresholdCandidate⟩

theorem month5ThresholdSearchCertificate_nonempty_iff_verifiedThresholdCandidate
    {bounds : SondowComponentBounds} :
    Nonempty (Month5ThresholdSearchCertificate bounds) ↔
      Nonempty (Month5VerifiedThresholdCandidate bounds) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toVerifiedThresholdCandidate⟩
  · intro h
    rcases h with ⟨candidate⟩
    exact ⟨candidate.toThresholdSearchCertificate⟩

theorem month5ThresholdSearchCertificate_nonempty_iff_finalExpressionThreshold
    {bounds : SondowComponentBounds} :
    Nonempty (Month5ThresholdSearchCertificate bounds) ↔
      Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
  month5ThresholdSearchCertificate_nonempty_iff_verifiedThresholdCandidate.trans
    month5VerifiedThresholdCandidate_nonempty_iff_finalExpressionThreshold

theorem month5FinalExpressionThresholdCertificate_nonempty_iff_thresholdGrowth
    {bounds : SondowComponentBounds} :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) ↔
      Nonempty (Month5ThresholdGrowthDominationCertificate
        (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
        Month5LowerBoundFunction) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toThresholdGrowthDominationCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨{
      threshold := cert.threshold_gap.threshold
      gap_at_or_above := by
        intro n hn
        have hgap := cert.threshold_gap.gap_at_or_above n hn
        simpa [Month5UpperBoundFunction, Month5SondowCombinedUpperBound,
          Month5LowerBoundFunction] using hgap }⟩

structure Month5GapDominationCertificate
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  computable_gap :
    ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound
  upper_eq_declared :
    Month5UpperBoundFunction bound = bound
  lower_eq_declared :
    Month5LowerBoundFunction = canonicalCnBoxPABox.length
  upper_polynomial :
    IsPolynomialBound (Month5UpperBoundFunction bound)
  independent_growth :
    Month5IndependentGrowthDominationCertificate
      (Month5UpperBoundFunction bound) Month5LowerBoundFunction

namespace Month5GapDominationCertificate

noncomputable def ofComputableGap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound) :
    Month5GapDominationCertificate
      MainRationality SondowAccepted bounds bound where
  computable_gap := cert
  upper_eq_declared := rfl
  lower_eq_declared := rfl
  upper_polynomial := cert.bundle.bound_poly
  independent_growth := {
    strict_gap :=
      ProofLengthGap.toEventualStrictCnBoxGap cert.proofLengthGap
        (Month5UpperBoundFunction bound) cert.bundle.bound_poly }

def toComputableGap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound) :
    ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound :=
  cert.computable_gap

def strictGap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound) :
    EventualStrictCnBoxGap
      (Month5UpperBoundFunction bound) Month5LowerBoundFunction :=
  cert.independent_growth.strict_gap

def cofinalGap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound) :
    CofinalStrictCnBoxGap
      (Month5UpperBoundFunction bound) Month5LowerBoundFunction :=
  cert.strictGap.toCofinalStrictCnBoxGap

def witnessAgainstDeclaredUpper
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound)
    (N : Nat) :
    HasProofLengthGapWitness
      canonicalCnBoxPABox (Month5UpperBoundFunction bound) N :=
  cert.strictGap.toProofLengthGapWitness rfl N

theorem upper_is_declared_bound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (_cert :
      Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    Month5UpperBoundFunction bound n = bound n :=
  rfl

theorem lower_is_canonical_length
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (_cert :
      Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    Month5LowerBoundFunction n = canonicalCnBoxPABox.length n :=
  rfl

theorem strict_gap_after
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound)
    (N : Nat) :
    ∃ n : Nat, N ≤ n ∧
      Month5UpperBoundFunction bound n < Month5LowerBoundFunction n :=
  cert.strictGap.gap_after N

theorem cofinal_gap_after
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound)
    (N : Nat) :
    ∃ n : Nat, N ≤ n ∧
      Month5UpperBoundFunction bound n < Month5LowerBoundFunction n :=
  cert.cofinalGap.gap_after N

theorem strict_gap_is_independent_field
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound) :
    EventualStrictCnBoxGap
      (Month5UpperBoundFunction bound) Month5LowerBoundFunction :=
  cert.independent_growth.strict_gap

theorem cofinal_gap_is_independent_field
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound) :
    CofinalStrictCnBoxGap
      (Month5UpperBoundFunction bound) Month5LowerBoundFunction :=
  cert.independent_growth.toCofinal.cofinal_gap

theorem toPublicGapInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) :=
  ⟨cert.computable_gap.toPublicGapCollisionInstantiation⟩

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  cert.computable_gap.not_main_rationality

end Month5GapDominationCertificate

theorem month5GapDominationCertificate_nonempty_iff_computableGap_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (Month5GapDominationCertificate
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toComputableGap⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨Month5GapDominationCertificate.ofComputableGap cert⟩

theorem month5GapDominationCertificate_nonempty_to_publicGapInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      Nonempty (Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) := by
  rcases h with ⟨cert⟩
  exact cert.toPublicGapInstantiation

theorem month5GapDominationCertificate_nonempty_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      Nonempty (Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound)) :
    ¬ MainRationality := by
  rcases h with ⟨cert⟩
  exact cert.not_main_rationality

structure Month5GapThresholdCertificate
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  gap_domination :
    Month5GapDominationCertificate
      MainRationality SondowAccepted bounds bound
  threshold_growth :
    Month5ThresholdGrowthDominationCertificate
      (Month5UpperBoundFunction bound) Month5LowerBoundFunction

namespace Month5GapThresholdCertificate

def toGapDomination
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapThresholdCertificate
        MainRationality SondowAccepted bounds bound) :
    Month5GapDominationCertificate
      MainRationality SondowAccepted bounds bound :=
  cert.gap_domination

theorem strict_gap_after_threshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapThresholdCertificate
        MainRationality SondowAccepted bounds bound)
    {n : Nat}
    (hn : cert.threshold_growth.threshold_gap.threshold ≤ n) :
    Month5UpperBoundFunction bound n < Month5LowerBoundFunction n :=
  cert.threshold_growth.threshold_gap.gap_at_or_above n hn

def witnessAgainstDeclaredUpper
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapThresholdCertificate
        MainRationality SondowAccepted bounds bound)
    (N : Nat) :
    HasProofLengthGapWitness
      canonicalCnBoxPABox (Month5UpperBoundFunction bound) N :=
  cert.threshold_growth.toProofLengthGapWitness N

theorem to_public_gap_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapThresholdCertificate
        MainRationality SondowAccepted bounds bound) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) :=
  cert.gap_domination.toPublicGapInstantiation

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert :
      Month5GapThresholdCertificate
        MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  cert.gap_domination.not_main_rationality

end Month5GapThresholdCertificate

theorem month5GapThresholdCertificate_nonempty_iff_components
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (Month5GapThresholdCertificate
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (Month5GapDominationCertificate
        MainRationality SondowAccepted bounds bound) ∧
        Nonempty (Month5ThresholdGrowthDominationCertificate
          (Month5UpperBoundFunction bound) Month5LowerBoundFunction) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨⟨cert.gap_domination⟩, ⟨cert.threshold_growth⟩⟩
  · intro h
    rcases h with ⟨⟨gap⟩, ⟨threshold⟩⟩
    exact ⟨{
      gap_domination := gap
      threshold_growth := threshold }⟩

theorem month5GapThresholdCertificate_nonempty_to_gapDomination
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h :
      Nonempty (Month5GapThresholdCertificate
        MainRationality SondowAccepted bounds bound)) :
    Nonempty (Month5GapDominationCertificate
      MainRationality SondowAccepted bounds bound) :=
  (month5GapThresholdCertificate_nonempty_iff_components).1 h |>.1

theorem month5ThresholdGrowthDomination_nonempty_to_cofinalGrowth
    {U L : Nat → Real}
    (h : Nonempty (Month5ThresholdGrowthDominationCertificate U L)) :
    Nonempty (Month5CofinalGrowthDominationCertificate U L) := by
  rcases h with ⟨cert⟩
  exact ⟨cert.toCofinal⟩

structure Month5CombinedUpperGapCertificate
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) where
  gap_domination :
    Month5GapDominationCertificate
      MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds)

namespace Month5CombinedUpperGapCertificate

def toGapDomination
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds) :
    Month5GapDominationCertificate
      MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) :=
  cert.gap_domination

theorem upper_is_sondow_combined
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (_cert :
      Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds)
    (n : Nat) :
    Month5UpperBoundFunction
        (Month5SondowCombinedUpperBound bounds) n =
      bounds.combined n :=
  rfl

theorem upper_polynomial
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (_cert :
      Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds) :
    IsPolynomialBound (Month5SondowCombinedUpperBound bounds) :=
  month5SondowCombinedUpperBound_poly bounds

theorem strict_gap_after
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds)
    (N : Nat) :
    ∃ n : Nat, N ≤ n ∧
      bounds.combined n < Month5LowerBoundFunction n := by
  rcases cert.gap_domination.strict_gap_after N with
    ⟨n, hn_ge, hlt⟩
  exact ⟨n, hn_ge, by simpa [Month5SondowCombinedUpperBound] using hlt⟩

def witnessAgainstCombinedUpper
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds)
    (N : Nat) :
    HasProofLengthGapWitness
      canonicalCnBoxPABox (Month5SondowCombinedUpperBound bounds) N :=
  cert.gap_domination.witnessAgainstDeclaredUpper N

theorem to_public_gap_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) :=
  cert.gap_domination.toPublicGapInstantiation

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds) :
    ¬ MainRationality :=
  cert.gap_domination.not_main_rationality

end Month5CombinedUpperGapCertificate

theorem month5CombinedUpperGapCertificate_nonempty_iff_gapDomination_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} :
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ↔
      Nonempty (Month5GapDominationCertificate
        MainRationality SondowAccepted bounds
        (Month5SondowCombinedUpperBound bounds)) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toGapDomination⟩
  · intro h
    rcases h with ⟨gap⟩
    exact ⟨{ gap_domination := gap }⟩

theorem month5CombinedUpperGapCertificate_nonempty_iff_computableGap_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} :
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) ↔
      Nonempty (ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds
        (Month5SondowCombinedUpperBound bounds)) :=
  month5CombinedUpperGapCertificate_nonempty_iff_gapDomination_nonempty.trans
    month5GapDominationCertificate_nonempty_iff_computableGap_nonempty

structure Month5CombinedUpperThresholdCertificate
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) where
  threshold_gap :
    Month5GapThresholdCertificate
      MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds)

namespace Month5CombinedUpperThresholdCertificate

def toGapThreshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds) :
    Month5GapThresholdCertificate
      MainRationality SondowAccepted bounds
      (Month5SondowCombinedUpperBound bounds) :=
  cert.threshold_gap

def toCombinedUpperGap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds) :
    Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds where
  gap_domination := cert.threshold_gap.gap_domination

def explicit_threshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds) : Nat :=
  cert.threshold_gap.threshold_growth.threshold_gap.threshold

theorem strict_gap_at_or_above_threshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds)
    {n : Nat}
    (hn : cert.explicit_threshold ≤ n) :
    bounds.combined n < Month5LowerBoundFunction n := by
  have hgap := cert.threshold_gap.strict_gap_after_threshold hn
  simpa [Month5SondowCombinedUpperBound, Month5UpperBoundFunction,
    explicit_threshold] using hgap

def toFinalExpressionThresholdCertificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds) :
    Month5FinalExpressionThresholdCertificate bounds where
  threshold := cert.explicit_threshold
  gap_at_or_above := by
    intro n hn
    have hgap := cert.strict_gap_at_or_above_threshold hn
    simpa [Month5LowerBoundFunction] using hgap

def toVerifiedThresholdCandidate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds) :
    Month5VerifiedThresholdCandidate bounds :=
  cert.toFinalExpressionThresholdCertificate.toVerifiedThresholdCandidate

theorem strict_gap_after
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds)
    (N : Nat) :
    ∃ n : Nat, N ≤ n ∧
      bounds.combined n < Month5LowerBoundFunction n :=
  cert.toCombinedUpperGap.strict_gap_after N

def witnessAgainstCombinedUpper
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds)
    (N : Nat) :
    HasProofLengthGapWitness
      canonicalCnBoxPABox (Month5SondowCombinedUpperBound bounds) N :=
  cert.threshold_gap.witnessAgainstDeclaredUpper N

theorem to_public_gap_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) :=
  cert.threshold_gap.to_public_gap_instantiation

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (cert :
      Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds) :
    ¬ MainRationality :=
  cert.threshold_gap.not_main_rationality

end Month5CombinedUpperThresholdCertificate

theorem month5CombinedUpperThresholdCertificate_nonempty_iff_gapThreshold_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} :
    Nonempty (Month5CombinedUpperThresholdCertificate
      MainRationality SondowAccepted bounds) ↔
      Nonempty (Month5GapThresholdCertificate
        MainRationality SondowAccepted bounds
        (Month5SondowCombinedUpperBound bounds)) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toGapThreshold⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨{ threshold_gap := cert }⟩

theorem month5CombinedUpperThresholdCertificate_nonempty_to_combinedGap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (h :
      Nonempty (Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds)) :
    Nonempty (Month5CombinedUpperGapCertificate
      MainRationality SondowAccepted bounds) := by
  rcases h with ⟨cert⟩
  exact ⟨cert.toCombinedUpperGap⟩

theorem month5CombinedUpperThresholdCertificate_nonempty_iff_components
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} :
    Nonempty (Month5CombinedUpperThresholdCertificate
      MainRationality SondowAccepted bounds) ↔
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds) ∧
        Nonempty (Month5ThresholdGrowthDominationCertificate
          (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
          Month5LowerBoundFunction) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨⟨cert.toCombinedUpperGap⟩,
      ⟨cert.threshold_gap.threshold_growth⟩⟩
  · intro h
    rcases h with ⟨⟨gap⟩, ⟨threshold⟩⟩
    exact ⟨{
      threshold_gap := {
        gap_domination := gap.gap_domination
        threshold_growth := threshold } }⟩

theorem month5CombinedUpperThresholdCertificate_nonempty_to_finalExpressionThreshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (h :
      Nonempty (Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds)) :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) := by
  rcases h with ⟨cert⟩
  exact ⟨cert.toFinalExpressionThresholdCertificate⟩

theorem month5CombinedUpperThresholdCertificate_nonempty_to_verifiedThresholdCandidate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (h :
      Nonempty (Month5CombinedUpperThresholdCertificate
        MainRationality SondowAccepted bounds)) :
    Nonempty (Month5VerifiedThresholdCandidate bounds) := by
  rcases h with ⟨cert⟩
  exact ⟨cert.toVerifiedThresholdCandidate⟩

theorem month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_finalExpression
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} :
    Nonempty (Month5CombinedUpperThresholdCertificate
      MainRationality SondowAccepted bounds) ↔
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds) ∧
        Nonempty (Month5FinalExpressionThresholdCertificate bounds) := by
  constructor
  · intro h
    exact
      ⟨month5CombinedUpperThresholdCertificate_nonempty_to_combinedGap h,
        month5CombinedUpperThresholdCertificate_nonempty_to_finalExpressionThreshold h⟩
  · intro h
    rcases h with ⟨hgap, hfinal⟩
    rcases hgap with ⟨gap⟩
    have hthreshold :
        Nonempty (Month5ThresholdGrowthDominationCertificate
          (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
          Month5LowerBoundFunction) :=
      (month5FinalExpressionThresholdCertificate_nonempty_iff_thresholdGrowth).1
        hfinal
    rcases hthreshold with ⟨threshold⟩
    exact ⟨{
      threshold_gap := {
        gap_domination := gap.gap_domination
        threshold_growth := threshold } }⟩

theorem month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_verifiedCandidate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} :
    Nonempty (Month5CombinedUpperThresholdCertificate
      MainRationality SondowAccepted bounds) ↔
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds) ∧
        Nonempty (Month5VerifiedThresholdCandidate bounds) := by
  constructor
  · intro h
    exact
      ⟨month5CombinedUpperThresholdCertificate_nonempty_to_combinedGap h,
        month5CombinedUpperThresholdCertificate_nonempty_to_verifiedThresholdCandidate h⟩
  · intro h
    rcases h with ⟨hgap, hcandidate⟩
    have hfinal :
        Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
      (month5VerifiedThresholdCandidate_nonempty_iff_finalExpressionThreshold).1
        hcandidate
    exact
      (month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_finalExpression).2
        ⟨hgap, hfinal⟩

theorem month5CombinedUpperGap_and_persistence_to_finalExpressionThreshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (hgap :
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds))
    (hpersist :
      Nonempty (Month5FinalExpressionGapPersistenceCertificate bounds)) :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) := by
  rcases hgap with ⟨gap⟩
  rcases hpersist with ⟨persist⟩
  have hcofinal :
      Month5CofinalGrowthDominationCertificate
        (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
        Month5LowerBoundFunction :=
    gap.gap_domination.independent_growth.toCofinal
  have hthreshold :
      Nonempty (Month5ThresholdGrowthDominationCertificate
        (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
        Month5LowerBoundFunction) :=
    hcofinal.toThreshold_nonempty { persistence := persist.persistence }
  exact
    (month5FinalExpressionThresholdCertificate_nonempty_iff_thresholdGrowth).2
      hthreshold

theorem month5CombinedUpperGap_and_monotonePersistence_to_finalExpressionThreshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (hgap :
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds))
    (hmono :
      Nonempty (Month5FinalExpressionMonotoneGapPersistenceCertificate
        bounds)) :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
  month5CombinedUpperGap_and_persistence_to_finalExpressionThreshold
    hgap
    (month5FinalExpressionMonotoneGapPersistence_nonempty_to_persistence
      hmono)

theorem month5CombinedUpperGap_and_gapDifferencePersistence_to_finalExpressionThreshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (hgap :
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds))
    (hdiff :
      Nonempty (Month5FinalExpressionGapDifferencePersistenceCertificate
        bounds)) :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) :=
  month5CombinedUpperGap_and_persistence_to_finalExpressionThreshold
    hgap
    (month5FinalExpressionGapDifferencePersistence_nonempty_to_persistence
      hdiff)

theorem month5CombinedUpperGap_and_eventualGapDifference_to_finalExpressionThreshold
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds}
    (hgap :
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds))
    (hdiff :
      Nonempty
        (Month5FinalExpressionEventualGapDifferencePersistenceCertificate
          bounds)) :
    Nonempty (Month5FinalExpressionThresholdCertificate bounds) := by
  rcases hgap with ⟨gap⟩
  have hcofinal :
      Nonempty (Month5CofinalGrowthDominationCertificate
        (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
        Month5LowerBoundFunction) :=
    ⟨gap.gap_domination.independent_growth.toCofinal⟩
  have hthreshold :
      Nonempty (Month5ThresholdGrowthDominationCertificate
        (Month5UpperBoundFunction (Month5SondowCombinedUpperBound bounds))
        Month5LowerBoundFunction) :=
    month5Cofinal_and_eventual_gap_difference_to_threshold
      hcofinal
      (month5FinalExpressionEventualGapDifferencePersistence_nonempty_to_generic
        hdiff)
  exact
    (month5FinalExpressionThresholdCertificate_nonempty_iff_thresholdGrowth).2
      hthreshold

theorem month5CombinedUpperGap_and_stepGapDifference_to_finalExpressionThreshold
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
  month5CombinedUpperGap_and_eventualGapDifference_to_finalExpressionThreshold
    hgap
    (month5FinalExpressionStepGapDifferencePersistence_nonempty_to_eventual
      hstep)

theorem month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_thresholdSearch
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} :
    Nonempty (Month5CombinedUpperThresholdCertificate
      MainRationality SondowAccepted bounds) ↔
      Nonempty (Month5CombinedUpperGapCertificate
        MainRationality SondowAccepted bounds) ∧
        Nonempty (Month5ThresholdSearchCertificate bounds) := by
  exact
    month5CombinedUpperThresholdCertificate_nonempty_iff_gap_and_verifiedCandidate.trans
      (Iff.rfl.and
        month5ThresholdSearchCertificate_nonempty_iff_verifiedThresholdCandidate.symm)

end BoundedProofPredicate
end BoundedArithmeticLab
