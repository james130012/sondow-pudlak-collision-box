import integration.SondowProjectBigNCleanSubmissionRoute
import integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectBigNParameterClosureAudit

open Filter
open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint
open SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint
open SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface

universe u v w

/--
Frontier-level clean submission route.

This removes the two separate parameters of
`cleanUpperProvider_submissionRoute`,

* `input : ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput ...`
* `upper_provider : ...checkedMeasuredUpperProviderType`,

from the theorem surface.  They are replaced by one upstream frontier object
that keeps the checker-side tail-gap data and the Sondow-side checked upper
provider in the same measured coordinate.

This is a parameter-surface closure, not a full mathematical closure of the
tail-gap theorem: the frontier still contains a `tail_gap` field.
-/
theorem cleanTailGapFrontier_submissionRoute
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      frontier.computedCollisionNOfRationality hrat =
        max
          (checkedSearchUpperTail
            frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
            frontier.concreteLengthCodeFrontier.checkedUpperProvider
            hrat).upperN
          (frontier.tail_gap.gap_for_polynomial_upper
            (checkedSearchUpperTail
              frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
              frontier.concreteLengthCodeFrontier.checkedUpperProvider
              hrat).U
            (checkedSearchUpperTail
              frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
              frontier.concreteLengthCodeFrontier.checkedUpperProvider
              hrat).polynomial).threshold) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨frontier.computedCollisionN_eq_tailGapMax,
    frontier.closure.2.2.2⟩

/--
Eventual-strict-length route.

This removes the explicit `tail_gap` parameter by constructing it with
`ComputableGapCertificate.ofEventuallyStrict`.  The remaining mathematical
load-bearing input is the proof-code growth statement

`∀ U, is_polynomial_bound U -> ∀ᶠ m in atTop, U m < lengthCodeAt m`.

Therefore this theorem is cleaner than a raw `tail_gap` input, but it is still
conditional on the proof-complexity lower-bound theorem.
-/
theorem eventuallyStrictLength_noTailGap_submissionRoute
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (local_interpretation :
      _root_.MiniHilbert.LocalFormulaCodeHilbertInterpretation A B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (eventually_strict_length :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∀ᶠ m in atTop, U m < (lengthCodeAt m : Real))
    (lengthCodeAt_eq_conj_source :
      ∀ m : Nat,
        lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m))
    (left_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real left_family.length))
    (right_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real right_family.length)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  projectLengthPayloadFreeExplicitEndpoint_tailGapThreshold_not_rational_of_eventuallyStrictLength_noFallback
    left_family right_family local_interpretation lengthCodeAt
    time_bound_strict exponent_ne_zero eventually_strict_length
    lengthCodeAt_eq_conj_source left_length_polynomial right_length_polynomial

/--
Singleton monomial lower-bound route.

This is the cleanest current theorem surface for the project-length target:
it does not expose `tail_gap`, `upper_provider`, or
`eventually_strict_length`.  The remaining mathematical input is the explicit
monomial domination statement

`thresholdOfMonomial coeff degree <= n ->
  coeff * (n + 1)^degree < minCheckedCodeSize n`.

The returned first component keeps the formula-level `bigN` normalization:
the certified index is exactly the displayed monomial threshold evaluated at
the generated upper-data `(coeff, degree)`.
-/
theorem singletonMonomialLowerBound_submissionRoute
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (left_data : ProjectLengthNatPowerUpperData left_family.length)
    (right_data : ProjectLengthNatPowerUpperData right_family.length)
    (left_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real left_family.length))
    (right_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (thresholdOfMonomial : Nat → Nat → Nat)
    (monomial_lt_lengthCodeAt_after :
      ∀ coeff degree n : Nat,
        thresholdOfMonomial coeff degree ≤ n →
          coeff * (n + 1) ^ degree <
            ((left_family.conjIntro right_family)
              |>.rightConjElim
              |>.minCheckedCodeSize n)) :
    (let upper_data :=
        projectLengthConjIntroLengthAddTwoNatPowerUpperData
          left_family right_family left_data right_data;
      projectLengthConjSourceCandidateRejectionProviderBigN_noFallback
          left_family right_family left_data right_data thresholdOfMonomial =
        thresholdOfMonomial upper_data.coeff upper_data.degree) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  refine
    ⟨projectLengthConjSourceCandidateRejectionProviderBigN_noFallback_eq_thresholdOfMonomial
        left_family right_family left_data right_data thresholdOfMonomial,
      ?_⟩
  intro _hrat
  exact
    (projectLengthConjSourceSingletonSearchLowerBoundBigNCertificate_noFallback
      left_family right_family time_bound_strict exponent_ne_zero
      left_data right_data left_length_polynomial right_length_polynomial
      thresholdOfMonomial monomial_lt_lengthCodeAt_after).2.2.2.2.2

end SondowProjectBigNParameterClosureAudit
end SondowMainCheckedCodeBridge
