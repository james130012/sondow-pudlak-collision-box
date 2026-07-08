import integration.SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectBigNCleanSubmissionRoute

open SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint

/-- Submission-facing clean checker route.

This is the proof-length-axiom-free final-collision checklist.  Its axiom
profile should contain only Lean/Mathlib logical dependencies, not the project
residuals `proof_length`, `partial_consistency_payload`, or
`strengthened_partial_consistency_payload`.
-/
theorem cleanCheckerFinalCollisionChecklist :
    ProofLengthAxiomFreeCheckerFinalCollisionChecklist :=
  proof_length_axiom_free_checker_final_collision_checklist

/-- Submission-facing lower-bound machine for the clean checker route. -/
theorem cleanCheckerLowerBoundMachineChecklist :
    ProofLengthAxiomFreeCheckerLowerBoundMachineChecklist :=
  proof_length_axiom_free_checker_lower_bound_machine_checklist

/-- Clean formula-level big-`N` handoff.

For the proof-length-axiom-free checker route, the computed collision number is
not merely existential: under the rational branch it is the explicit
`max upperN threshold` witness attached to the tail-gap certificate.  This is
the clean replacement for presenting the large-`N` formula through the old root
`proof_length` endpoint.
-/
theorem cleanComputedBigN_eq_tailGapMax
    {scale_data :
      SondowProjectMonth9Month10InternalPudlakWitnessSurface.InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput
        scale_data)
    (upper_provider :
      input.toSearchInput.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
      upper_provider).computedCollisionNOfRationality hrat =
      max
        (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
          input.toSearchInput.toProofLengthFreeMonth12Candidate
          upper_provider hrat).upperN
        (input.tail_gap.gap_for_polynomial_upper
          (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
            input.toSearchInput.toProofLengthFreeMonth12Candidate
            upper_provider hrat).U
          (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
            input.toSearchInput.toProofLengthFreeMonth12Candidate
            upper_provider hrat).polynomial).threshold :=
  ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput.computedCollisionN_eq_tailGapMax
    input upper_provider hrat

/-- Clean proof-level/collision-level submission route.

This is the main theorem for the current manuscript.  It produces the computed
collision number as the exact `max upperN threshold` value supplied by the clean
upper tail and the clean tail-gap certificate, and the same route proves the
rationality-branch contradiction.  It intentionally does not depend on the
legacy half-denominator formula-level big-`N` theorem.
-/
theorem cleanUpperProvider_submissionRoute
    {scale_data :
      SondowProjectMonth9Month10InternalPudlakWitnessSurface.InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput
        scale_data)
    (upper_provider :
      input.toSearchInput.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
        upper_provider).computedCollisionNOfRationality hrat =
        max
          (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
            input.toSearchInput.toProofLengthFreeMonth12Candidate
            upper_provider hrat).upperN
          (input.tail_gap.gap_for_polynomial_upper
            (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
              input.toSearchInput.toProofLengthFreeMonth12Candidate
              upper_provider hrat).U
            (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
              input.toSearchInput.toProofLengthFreeMonth12Candidate
              upper_provider hrat).polynomial).threshold) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨cleanComputedBigN_eq_tailGapMax input upper_provider,
    (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
      upper_provider).not_rational⟩

/-- Clean half-denominator display form.

This bridge does not use the old root `proof_length` endpoint.  Instead it
records the exact condition needed to display the clean computed number with
the half-denominator coefficient: the clean upper tail must have cutoff
`17 * max 3 ((rat.q.den + 1) / 2) + 8`.  Under that condition, the final clean
computed big-`N` is the explicit maximum of this half-denominator cutoff and the
tail-gap threshold.
-/
theorem cleanComputedBigN_eq_halfDenFormulaMax
    {scale_data :
      SondowProjectMonth9Month10InternalPudlakWitnessSurface.InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput
        scale_data)
    (upper_provider :
      input.toSearchInput.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType)
    (rat : MainSondowRationalParameter)
    (hrat : _root_.is_rational _root_.euler_mascheroni)
    (hupperN :
      (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
        input.toSearchInput.toProofLengthFreeMonth12Candidate
        upper_provider hrat).upperN =
        17 * (max 3 ((rat.q.den + 1) / 2)) + 8) :
    (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
      upper_provider).computedCollisionNOfRationality hrat =
      max
        (17 * (max 3 ((rat.q.den + 1) / 2)) + 8)
        (input.tail_gap.gap_for_polynomial_upper
          (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
            input.toSearchInput.toProofLengthFreeMonth12Candidate
            upper_provider hrat).U
          (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
            input.toSearchInput.toProofLengthFreeMonth12Candidate
            upper_provider hrat).polynomial).threshold := by
  rw [cleanComputedBigN_eq_tailGapMax input upper_provider hrat, hupperN]

/-- Clean half-denominator upper-provider package.

This is the submission-facing interface for future formula-level refinements:
the upper-provider itself must be on the proof-length-axiom-free checker route,
and its selected cutoff must be the half-denominator formula.  The package does
not import the old project-length formula theorem, because that theorem's axiom
profile still contains the project residuals.
-/
structure CleanHalfDenUpperProvider
    {scale_data :
      SondowProjectMonth9Month10InternalPudlakWitnessSurface.InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput
        scale_data)
    (rat : MainSondowRationalParameter) : Type where
  upper_provider :
    input.toSearchInput.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType
  upperN_eq :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
        input.toSearchInput.toProofLengthFreeMonth12Candidate
        upper_provider hrat).upperN =
        17 * (max 3 ((rat.q.den + 1) / 2)) + 8

/-- Clean half-denominator display theorem from a clean upper-provider package.

This is the formula-display endpoint that can be safely cited: its dependencies
are those of the clean checker route plus the explicit clean provider input,
not the legacy `proof_length`/payload project constants.
-/
theorem cleanHalfDenUpperProvider_computedBigN_eq_formulaMax
    {scale_data :
      SondowProjectMonth9Month10InternalPudlakWitnessSurface.InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput
        scale_data)
    (rat : MainSondowRationalParameter)
    (halfden : CleanHalfDenUpperProvider input rat)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
      halfden.upper_provider).computedCollisionNOfRationality hrat =
      max
        (17 * (max 3 ((rat.q.den + 1) / 2)) + 8)
        (input.tail_gap.gap_for_polynomial_upper
          (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
            input.toSearchInput.toProofLengthFreeMonth12Candidate
            halfden.upper_provider hrat).U
          (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
            input.toSearchInput.toProofLengthFreeMonth12Candidate
            halfden.upper_provider hrat).polynomial).threshold :=
  cleanComputedBigN_eq_halfDenFormulaMax
    input halfden.upper_provider rat hrat (halfden.upperN_eq hrat)

/-- Clean provider theorem: once the proof-length-axiom-free provider is
supplied, the checked route proves the target non-rationality statement without
using the old root proof-length or payload axioms. -/
theorem cleanProvider_not_rational
    (h : ProofLengthAxiomFreeInternalTheorem5Provider) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.not_rational

/-- Clean half-denominator submission route.

With a clean half-denominator upper-provider package, the final theorem exposes
both the visible formula-level collision number and the contradiction on the
rationality branch.  This is the route to keep as the main manuscript theorem
unless and until the upstream half-denominator provider is rebuilt without the
legacy project constants.
-/
theorem cleanHalfDenUpperProvider_submissionRoute
    {scale_data :
      SondowProjectMonth9Month10InternalPudlakWitnessSurface.InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput
        scale_data)
    (rat : MainSondowRationalParameter)
    (halfden : CleanHalfDenUpperProvider input rat) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
        halfden.upper_provider).computedCollisionNOfRationality hrat =
        max
          (17 * (max 3 ((rat.q.den + 1) / 2)) + 8)
          (input.tail_gap.gap_for_polynomial_upper
            (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
              input.toSearchInput.toProofLengthFreeMonth12Candidate
              halfden.upper_provider hrat).U
            (SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.checkedSearchUpperTail
              input.toSearchInput.toProofLengthFreeMonth12Candidate
              halfden.upper_provider hrat).polynomial).threshold) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨cleanHalfDenUpperProvider_computedBigN_eq_formulaMax input rat halfden,
    cleanProvider_not_rational
      (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
        halfden.upper_provider)⟩

end SondowProjectBigNCleanSubmissionRoute
end SondowMainCheckedCodeBridge
