import integration.SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint

/-!
# Month 11-12 project-length target-upper endpoint

This file connects the proof-length-free checked-target upper route to the
checker-defined `ProofCodeSemantics.projectLength` measurement.  It deliberately
does not use the legacy `sondowProjectLocalPudlakCollisionBox`, whose definition
unfolds to root `proof_length`.
-/

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10ProofLengthGapFrontier
open SondowProjectMonth9Month10Month11ExactProofGapHandoff
open SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface
open SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint

/-! ## Project-length measured object -/

/-- The theorem-5 power-bound family measured by the concrete checker
`projectLength` semantics.  This is the replacement measured object for the
root `proof_length` box on the theorem-5 raw-code family. -/
noncomputable def checkerProjectLengthMeasured
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data)
    (fallback : _root_.FormulaCode → Nat) : Nat → Real :=
  fun n =>
    checker.toProofCodeSemantics.projectLength fallback
      (scale_data.powerBoundRawCode n)

theorem checkerProjectLengthMeasured_eq_checked
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (fallback : _root_.FormulaCode → Nat) (n : Nat) :
    checkerProjectLengthMeasured scale_data checker fallback n =
      month9_month10_checkedProofCodeMeasured
        scale_data checker.toProofCodeSemantics n := by
  rw [checkerProjectLengthMeasured,
    _root_.ProofCodeSemantics.projectLength_eq_minProofCodeSize]
  rfl

/-- Transport the finite-search lower gap from checked `minProofCodeSize` to
the checker `projectLength` measured object. -/
def checkerProjectLengthGapOfExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration) :
    ComputableSearchGapCertificate
      (checkerProjectLengthMeasured scale_data checker fallback) :=
  transportComputableSearchGap
    (fun n =>
      (checkerProjectLengthMeasured_eq_checked
        (scale_data := scale_data) (checker := checker) fallback n).symm)
    (month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
      extractor.toComputableFiniteSearchExclusion)

theorem checkerProjectLengthGapOfExtractor_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((checkerProjectLengthGapOfExtractor fallback extractor)
      |>.gap_for_polynomial_upper U hU).witness N =
      extractor.witness U hU N :=
  rfl

/-- Transport any checked upper provider to the checker `projectLength`
measured object. -/
def checkerProjectLengthUpperProviderOfChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (fallback : _root_.FormulaCode → Nat)
    (checked_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    Month9Month10AbstractMeasuredUpperProvider
      (checkerProjectLengthMeasured scale_data checker fallback) :=
  Month9Month10AbstractMeasuredUpperProvider.transportEq
    (fun n =>
      (checkerProjectLengthMeasured_eq_checked
        (scale_data := scale_data) (checker := checker) fallback n).symm)
    checked_upper

/-- Direct collision endpoint over checker `projectLength`, once the Sondow
upper side has already been expressed as a checked upper provider. -/
def checkerProjectLengthDirectEndpointOfCheckedUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (checked_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured scale_data checker fallback) where
  gap := checkerProjectLengthGapOfExtractor fallback extractor
  upper_provider :=
    checkerProjectLengthUpperProviderOfChecked fallback checked_upper

theorem checkerProjectLengthDirectEndpoint_computed_n_eq_extractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (checked_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (checkerProjectLengthDirectEndpointOfCheckedUpper
        fallback extractor checked_upper).computedCollisionNOfRationality
        hrat =
      extractor.witness
        ((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).upperTailOfRationality hrat).U
        ((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).upperTailOfRationality
            hrat).polynomial
        ((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).upperTailOfRationality
            hrat).upperN := by
  calc
    (checkerProjectLengthDirectEndpointOfCheckedUpper
        fallback extractor checked_upper).computedCollisionNOfRationality
          hrat =
        (((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).gap).gap_for_polynomial_upper
          ((checkerProjectLengthDirectEndpointOfCheckedUpper
            fallback extractor checked_upper).upperTailOfRationality hrat).U
          ((checkerProjectLengthDirectEndpointOfCheckedUpper
            fallback extractor checked_upper).upperTailOfRationality
              hrat).polynomial).witness
          ((checkerProjectLengthDirectEndpointOfCheckedUpper
            fallback extractor checked_upper).upperTailOfRationality
              hrat).upperN :=
      (checkerProjectLengthDirectEndpointOfCheckedUpper
        fallback extractor checked_upper).computedCollisionN_eq_searchGapWitness
          hrat
    _ = extractor.witness
        ((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).upperTailOfRationality hrat).U
        ((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).upperTailOfRationality
            hrat).polynomial
        ((checkerProjectLengthDirectEndpointOfCheckedUpper
          fallback extractor checked_upper).upperTailOfRationality
            hrat).upperN := by
      rfl

/-! ## Checked-target upper endpoint -/

/-- Project-length endpoint from an abstract checked target projection and an
upper provider for that target.  This is the clean Sondow-upper replacement
shape: no legacy project proof-length box is mentioned. -/
def projectLengthEndpointOfCheckedTargetUpper
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {targetMeasured : Nat → Nat}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        targetMeasured)
    (upper_provider :
      InternalPudlakTheorem5CheckedTargetUpperProvider targetMeasured) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        core.scale_data core.checkerSemantics fallback) :=
  checkerProjectLengthDirectEndpointOfCheckedUpper
    fallback core.rejectionExtractor
    (checkedUpperProviderOfCheckedTargetProjectionAndUpper
      projection upper_provider)

theorem projectLengthEndpointOfCheckedTargetUpper_computed_n_eq
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {targetMeasured : Nat → Nat}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        targetMeasured)
    (upper_provider :
      InternalPudlakTheorem5CheckedTargetUpperProvider targetMeasured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthEndpointOfCheckedTargetUpper
        core fallback projection upper_provider).computedCollisionNOfRationality
        hrat =
      core.rejectionExtractor.witness
        ((projectLengthEndpointOfCheckedTargetUpper
          core fallback projection upper_provider).upperTailOfRationality
            hrat).U
        ((projectLengthEndpointOfCheckedTargetUpper
          core fallback projection upper_provider).upperTailOfRationality
            hrat).polynomial
        ((projectLengthEndpointOfCheckedTargetUpper
          core fallback projection upper_provider).upperTailOfRationality
            hrat).upperN := by
  exact
    checkerProjectLengthDirectEndpoint_computed_n_eq_extractorWitness
      fallback core.rejectionExtractor
      (checkedUpperProviderOfCheckedTargetProjectionAndUpper
        projection upper_provider)
      hrat

theorem projectLengthEndpointOfCheckedTargetUpper_closure
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {targetMeasured : Nat → Nat}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        targetMeasured)
    (upper_provider :
      InternalPudlakTheorem5CheckedTargetUpperProvider targetMeasured) :
    (projectLengthEndpointOfCheckedTargetUpper
      core fallback projection upper_provider).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            core.scale_data core.checkerSemantics fallback)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          ((projectLengthEndpointOfCheckedTargetUpper
              core fallback projection upper_provider)
            ).computedCollisionNOfRationality hrat =
            core.rejectionExtractor.witness
              (((projectLengthEndpointOfCheckedTargetUpper
                core fallback projection upper_provider)
                  ).upperTailOfRationality hrat).U
              (((projectLengthEndpointOfCheckedTargetUpper
                core fallback projection upper_provider)
                  ).upperTailOfRationality hrat).polynomial
              (((projectLengthEndpointOfCheckedTargetUpper
                core fallback projection upper_provider)
                  ).upperTailOfRationality hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨(projectLengthEndpointOfCheckedTargetUpper
      core fallback projection upper_provider).audit,
    ⟨(projectLengthEndpointOfCheckedTargetUpper
      core fallback projection upper_provider).gap⟩,
    projectLengthEndpointOfCheckedTargetUpper_computed_n_eq
      core fallback projection upper_provider,
    (projectLengthEndpointOfCheckedTargetUpper
      core fallback projection upper_provider).computed_n_contradiction,
    (projectLengthEndpointOfCheckedTargetUpper
      core fallback projection upper_provider).not_rational⟩

/-! ## Concrete proof-family checked-target endpoint -/

/-- Concrete-proof-family instantiation of the project-length endpoint.  This
is the payload-free checked-target route: the upper side is a concrete
MiniHilbert proof-family size bound rather than the legacy local-Hilbert payload
box. -/
def projectLengthEndpointOfConcreteProofFamilyTargetUpper
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        target_family)
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        core.scale_data core.checkerSemantics fallback) :=
  projectLengthEndpointOfCheckedTargetUpper
    core fallback projection.toCheckedTargetProjection
    upper_provider.toCheckedTargetUpperProvider

theorem projectLengthEndpointOfConcreteProofFamilyTargetUpper_computed_n_eq
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        target_family)
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthEndpointOfConcreteProofFamilyTargetUpper
        core fallback projection upper_provider).computedCollisionNOfRationality
        hrat =
      core.rejectionExtractor.witness
        ((projectLengthEndpointOfConcreteProofFamilyTargetUpper
          core fallback projection upper_provider).upperTailOfRationality
            hrat).U
        ((projectLengthEndpointOfConcreteProofFamilyTargetUpper
          core fallback projection upper_provider).upperTailOfRationality
            hrat).polynomial
        ((projectLengthEndpointOfConcreteProofFamilyTargetUpper
          core fallback projection upper_provider).upperTailOfRationality
            hrat).upperN := by
  simpa [projectLengthEndpointOfConcreteProofFamilyTargetUpper] using
    projectLengthEndpointOfCheckedTargetUpper_computed_n_eq
      core fallback projection.toCheckedTargetProjection
      upper_provider.toCheckedTargetUpperProvider hrat

theorem projectLengthEndpointOfConcreteProofFamilyTargetUpper_closure
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        target_family)
    (upper_provider :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetUpperProvider
        target_family) :
    (projectLengthEndpointOfConcreteProofFamilyTargetUpper
      core fallback projection upper_provider).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            core.scale_data core.checkerSemantics fallback)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          ((projectLengthEndpointOfConcreteProofFamilyTargetUpper
              core fallback projection upper_provider)
            ).computedCollisionNOfRationality hrat =
            core.rejectionExtractor.witness
              (((projectLengthEndpointOfConcreteProofFamilyTargetUpper
                core fallback projection upper_provider)
                  ).upperTailOfRationality hrat).U
              (((projectLengthEndpointOfConcreteProofFamilyTargetUpper
                core fallback projection upper_provider)
                  ).upperTailOfRationality hrat).polynomial
              (((projectLengthEndpointOfConcreteProofFamilyTargetUpper
                core fallback projection upper_provider)
                  ).upperTailOfRationality hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [projectLengthEndpointOfConcreteProofFamilyTargetUpper] using
    projectLengthEndpointOfCheckedTargetUpper_closure
      core fallback projection.toCheckedTargetProjection
      upper_provider.toCheckedTargetUpperProvider

/-- Concrete-proof-family project-length endpoint when the target proof-family
length is already known polynomially bounded. -/
def projectLengthEndpointOfConcreteProofFamilyLengthPolynomial
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        target_family)
    (hpoly :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real target_family.length)) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        core.scale_data core.checkerSemantics fallback) :=
  projectLengthEndpointOfConcreteProofFamilyTargetUpper
    core fallback projection
    (concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial
      hpoly)

theorem projectLengthEndpointOfConcreteProofFamilyLengthPolynomial_computed_n_eq
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        target_family)
    (hpoly :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real target_family.length))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthEndpointOfConcreteProofFamilyLengthPolynomial
        core fallback projection hpoly).computedCollisionNOfRationality
        hrat =
      core.rejectionExtractor.witness
        ((projectLengthEndpointOfConcreteProofFamilyLengthPolynomial
          core fallback projection hpoly).upperTailOfRationality hrat).U
        ((projectLengthEndpointOfConcreteProofFamilyLengthPolynomial
          core fallback projection hpoly).upperTailOfRationality
            hrat).polynomial
        ((projectLengthEndpointOfConcreteProofFamilyLengthPolynomial
          core fallback projection hpoly).upperTailOfRationality hrat).upperN := by
  simpa [projectLengthEndpointOfConcreteProofFamilyLengthPolynomial] using
    projectLengthEndpointOfConcreteProofFamilyTargetUpper_computed_n_eq
      core fallback projection
      (concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial
        hpoly)
      hrat

theorem projectLengthEndpointOfConcreteProofFamilyLengthPolynomial_closure
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (projection :
      InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        target_family)
    (hpoly :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real target_family.length)) :
    (projectLengthEndpointOfConcreteProofFamilyLengthPolynomial
      core fallback projection hpoly).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            core.scale_data core.checkerSemantics fallback)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          ((projectLengthEndpointOfConcreteProofFamilyLengthPolynomial
              core fallback projection hpoly)
            ).computedCollisionNOfRationality hrat =
            core.rejectionExtractor.witness
              (((projectLengthEndpointOfConcreteProofFamilyLengthPolynomial
                core fallback projection hpoly)
                  ).upperTailOfRationality hrat).U
              (((projectLengthEndpointOfConcreteProofFamilyLengthPolynomial
                core fallback projection hpoly)
                  ).upperTailOfRationality hrat).polynomial
              (((projectLengthEndpointOfConcreteProofFamilyLengthPolynomial
                core fallback projection hpoly)
                  ).upperTailOfRationality hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [projectLengthEndpointOfConcreteProofFamilyLengthPolynomial] using
    projectLengthEndpointOfConcreteProofFamilyTargetUpper_closure
      core fallback projection
      (concreteProofFamilyCheckedTargetUpperProviderOfLengthPolynomial
        hpoly)

/-! ## Concrete length-code frontier project-length endpoint -/

/-- Project-length endpoint from the smallest concrete length-code theorem-5
frontier.  The remaining proof obligations are exactly the two fields of that
frontier: source-code exactness against the right-conjunction family and a
polynomial length bound for the target concrete proof family. -/
def projectLengthEndpointOfConcreteLengthCodeTargetFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier
        scale_data target_family) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        scale_data frontier.lower_search.checkerSemantics fallback) :=
  projectLengthEndpointOfConcreteProofFamilyLengthPolynomial
    frontier.lower_search.toCanonicalSearchCore
    fallback frontier.projection frontier.target_length_polynomial

theorem projectLengthEndpointOfConcreteLengthCodeTargetFrontier_computed_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier
        scale_data target_family)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthEndpointOfConcreteLengthCodeTargetFrontier
        fallback frontier).computedCollisionNOfRationality hrat =
      frontier.lower_search.rejectionExtractor.witness
        ((projectLengthEndpointOfConcreteLengthCodeTargetFrontier
          fallback frontier).upperTailOfRationality hrat).U
        ((projectLengthEndpointOfConcreteLengthCodeTargetFrontier
          fallback frontier).upperTailOfRationality hrat).polynomial
        ((projectLengthEndpointOfConcreteLengthCodeTargetFrontier
          fallback frontier).upperTailOfRationality hrat).upperN := by
  simpa [projectLengthEndpointOfConcreteLengthCodeTargetFrontier,
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput.toCanonicalSearchCore] using
    projectLengthEndpointOfConcreteProofFamilyLengthPolynomial_computed_n_eq
      frontier.lower_search.toCanonicalSearchCore
      fallback frontier.projection frontier.target_length_polynomial hrat

theorem projectLengthEndpointOfConcreteLengthCodeTargetFrontier_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier
        scale_data target_family) :
    (projectLengthEndpointOfConcreteLengthCodeTargetFrontier
      fallback frontier).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            scale_data frontier.lower_search.checkerSemantics fallback)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          ((projectLengthEndpointOfConcreteLengthCodeTargetFrontier
              fallback frontier)
            ).computedCollisionNOfRationality hrat =
            frontier.lower_search.rejectionExtractor.witness
              (((projectLengthEndpointOfConcreteLengthCodeTargetFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).U
              (((projectLengthEndpointOfConcreteLengthCodeTargetFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).polynomial
              (((projectLengthEndpointOfConcreteLengthCodeTargetFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [projectLengthEndpointOfConcreteLengthCodeTargetFrontier,
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput.toCanonicalSearchCore] using
    projectLengthEndpointOfConcreteProofFamilyLengthPolynomial_closure
      frontier.lower_search.toCanonicalSearchCore
      fallback frontier.projection frontier.target_length_polynomial

/-! ## Conj-intro frontier project-length endpoints -/

/-- Project-length endpoint from the conj-intro target frontier.  The target
polynomial bound is generated from the two component proof-family length
bounds. -/
def projectLengthEndpointOfConjIntroLengthCodeTargetFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        scale_data frontier.lower_search.checkerSemantics fallback) :=
  projectLengthEndpointOfConcreteLengthCodeTargetFrontier
    fallback frontier.concreteLengthCodeFrontier

theorem projectLengthEndpointOfConjIntroLengthCodeTargetFrontier_computed_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthEndpointOfConjIntroLengthCodeTargetFrontier
        fallback frontier).computedCollisionNOfRationality hrat =
      frontier.lower_search.rejectionExtractor.witness
        ((projectLengthEndpointOfConjIntroLengthCodeTargetFrontier
          fallback frontier).upperTailOfRationality hrat).U
        ((projectLengthEndpointOfConjIntroLengthCodeTargetFrontier
          fallback frontier).upperTailOfRationality hrat).polynomial
        ((projectLengthEndpointOfConjIntroLengthCodeTargetFrontier
          fallback frontier).upperTailOfRationality hrat).upperN := by
  simpa [projectLengthEndpointOfConjIntroLengthCodeTargetFrontier,
    Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier.concreteLengthCodeFrontier] using
    projectLengthEndpointOfConcreteLengthCodeTargetFrontier_computed_n_eq
      fallback frontier.concreteLengthCodeFrontier hrat

theorem projectLengthEndpointOfConjIntroLengthCodeTargetFrontier_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    (projectLengthEndpointOfConjIntroLengthCodeTargetFrontier
      fallback frontier).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            scale_data frontier.lower_search.checkerSemantics fallback)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          ((projectLengthEndpointOfConjIntroLengthCodeTargetFrontier
              fallback frontier)
            ).computedCollisionNOfRationality hrat =
            frontier.lower_search.rejectionExtractor.witness
              (((projectLengthEndpointOfConjIntroLengthCodeTargetFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).U
              (((projectLengthEndpointOfConjIntroLengthCodeTargetFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).polynomial
              (((projectLengthEndpointOfConjIntroLengthCodeTargetFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [projectLengthEndpointOfConjIntroLengthCodeTargetFrontier,
    Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier.concreteLengthCodeFrontier] using
    projectLengthEndpointOfConcreteLengthCodeTargetFrontier_closure
      fallback frontier.concreteLengthCodeFrontier

/-! ## Canonical conj-intro project-length endpoints -/

/-- Project-length endpoint from the canonical conj-intro target-search
frontier.  The theorem-5 source equality is definitional at this layer. -/
def projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10CanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        scale_data frontier.lowerSearch.checkerSemantics fallback) :=
  projectLengthEndpointOfConjIntroLengthCodeTargetFrontier
    fallback frontier.conjIntroLengthCodeFrontier

theorem projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier_computed_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10CanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier
        fallback frontier).computedCollisionNOfRationality hrat =
      frontier.lowerSearch.rejectionExtractor.witness
        ((projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier
          fallback frontier).upperTailOfRationality hrat).U
        ((projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier
          fallback frontier).upperTailOfRationality hrat).polynomial
        ((projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier
          fallback frontier).upperTailOfRationality hrat).upperN := by
  simpa [projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier,
    Month9Month10CanonicalConjIntroTargetSearchFrontier.conjIntroLengthCodeFrontier] using
    projectLengthEndpointOfConjIntroLengthCodeTargetFrontier_computed_n_eq
      fallback frontier.conjIntroLengthCodeFrontier hrat

theorem projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10CanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    (projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier
      fallback frontier).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            scale_data frontier.lowerSearch.checkerSemantics fallback)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          ((projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier
              fallback frontier)
            ).computedCollisionNOfRationality hrat =
            frontier.lowerSearch.rejectionExtractor.witness
              (((projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).U
              (((projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).polynomial
              (((projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier,
    Month9Month10CanonicalConjIntroTargetSearchFrontier.conjIntroLengthCodeFrontier] using
    projectLengthEndpointOfConjIntroLengthCodeTargetFrontier_closure
      fallback frontier.conjIntroLengthCodeFrontier

/-! ## Time-bound canonical project-length endpoint -/

/-- Project-length endpoint from the time-bound canonical frontier.  The scale
strictness field has been replaced by strictness of the primitive
time-constructible bound plus nonzero exponent. -/
def projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        scale_data frontier.canonicalFrontier.lowerSearch.checkerSemantics
        fallback) :=
  projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier
    fallback frontier.canonicalFrontier

theorem projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier_computed_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier
        fallback frontier).computedCollisionNOfRationality hrat =
      frontier.canonicalFrontier.lowerSearch.rejectionExtractor.witness
        ((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier
          fallback frontier).upperTailOfRationality hrat).U
        ((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier
          fallback frontier).upperTailOfRationality hrat).polynomial
        ((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier
          fallback frontier).upperTailOfRationality hrat).upperN := by
  simpa [projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier,
    Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier.canonicalFrontier] using
    projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier_computed_n_eq
      fallback frontier.canonicalFrontier hrat

theorem projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    (projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier
      fallback frontier).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            scale_data frontier.canonicalFrontier.lowerSearch.checkerSemantics
            fallback)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          ((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier
              fallback frontier)
            ).computedCollisionNOfRationality hrat =
            frontier.canonicalFrontier.lowerSearch.rejectionExtractor.witness
              (((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).U
              (((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).polynomial
              (((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetSearchFrontier,
    Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier.canonicalFrontier] using
    projectLengthEndpointOfCanonicalConjIntroTargetSearchFrontier_closure
      fallback frontier.canonicalFrontier

/-! ## Time-bound canonical tail-gap project-length endpoint -/

/-- Project-length endpoint from the time-bound canonical tail-gap frontier.
This is the most explicit computable-witness shape in this file: the lower gap
is supplied as a thresholded tail certificate before being converted to the
finite-search endpoint. -/
def projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        scale_data frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback) :=
  projectLengthEndpointOfConcreteLengthCodeTargetFrontier
    fallback frontier.concreteLengthCodeFrontier

theorem projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier_computed_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier
        fallback frontier).computedCollisionNOfRationality hrat =
      frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
        ((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier
          fallback frontier).upperTailOfRationality hrat).U
        ((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier
          fallback frontier).upperTailOfRationality hrat).polynomial
        ((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier
          fallback frontier).upperTailOfRationality hrat).upperN := by
  simpa [projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier] using
    projectLengthEndpointOfConcreteLengthCodeTargetFrontier_computed_n_eq
      fallback frontier.concreteLengthCodeFrontier hrat

theorem projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    (projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier
      fallback frontier).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            scale_data frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
            fallback)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          ((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier
              fallback frontier)
            ).computedCollisionNOfRationality hrat =
            frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
              (((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).U
              (((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).polynomial
              (((projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    projectLengthEndpointOfConcreteLengthCodeTargetFrontier_closure
      fallback frontier.concreteLengthCodeFrontier
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      projectLengthEndpointOfTimeBoundCanonicalConjIntroTargetTailGapFrontier_computed_n_eq
        fallback frontier,
      hclosure.2.2.2.1,
      hclosure.2.2.2.2⟩

/-! ## Local-Hilbert checked-target endpoint -/

/-- Local-Hilbert instantiation of the checked-target project-length endpoint.
This removes root `proof_length` from the Sondow upper bridge.  Axiom probes
still expose the two payload predicates until the local-Hilbert payload route is
internally discharged. -/
def projectLengthEndpointOfLocalHilbertTargetUpper
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertCheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics interp)
    (upper_provider :
      InternalPudlakTheorem5LocalHilbertCheckedTargetUpperProvider interp) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        core.scale_data core.checkerSemantics fallback) :=
  checkerProjectLengthDirectEndpointOfCheckedUpper
    fallback core.rejectionExtractor
    (checkedUpperProviderOfLocalHilbertProjectionAndTargetUpper
      projection upper_provider)

theorem projectLengthEndpointOfLocalHilbertTargetUpper_computed_n_eq
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertCheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics interp)
    (upper_provider :
      InternalPudlakTheorem5LocalHilbertCheckedTargetUpperProvider interp)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthEndpointOfLocalHilbertTargetUpper
        core fallback projection upper_provider).computedCollisionNOfRationality
        hrat =
      core.rejectionExtractor.witness
        ((projectLengthEndpointOfLocalHilbertTargetUpper
          core fallback projection upper_provider).upperTailOfRationality
            hrat).U
        ((projectLengthEndpointOfLocalHilbertTargetUpper
          core fallback projection upper_provider).upperTailOfRationality
            hrat).polynomial
        ((projectLengthEndpointOfLocalHilbertTargetUpper
          core fallback projection upper_provider).upperTailOfRationality
            hrat).upperN :=
  checkerProjectLengthDirectEndpoint_computed_n_eq_extractorWitness
    fallback core.rejectionExtractor
    (checkedUpperProviderOfLocalHilbertProjectionAndTargetUpper
      projection upper_provider)
    hrat

theorem projectLengthEndpointOfLocalHilbertTargetUpper_closure
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (projection :
      InternalPudlakTheorem5LocalHilbertCheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics interp)
    (upper_provider :
      InternalPudlakTheorem5LocalHilbertCheckedTargetUpperProvider interp) :
    (projectLengthEndpointOfLocalHilbertTargetUpper
      core fallback projection upper_provider).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            core.scale_data core.checkerSemantics fallback)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          ((projectLengthEndpointOfLocalHilbertTargetUpper
              core fallback projection upper_provider)
            ).computedCollisionNOfRationality hrat =
            core.rejectionExtractor.witness
              (((projectLengthEndpointOfLocalHilbertTargetUpper
                core fallback projection upper_provider)
                  ).upperTailOfRationality hrat).U
              (((projectLengthEndpointOfLocalHilbertTargetUpper
                core fallback projection upper_provider)
                  ).upperTailOfRationality hrat).polynomial
              (((projectLengthEndpointOfLocalHilbertTargetUpper
                core fallback projection upper_provider)
                  ).upperTailOfRationality hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨(projectLengthEndpointOfLocalHilbertTargetUpper
      core fallback projection upper_provider).audit,
    ⟨(projectLengthEndpointOfLocalHilbertTargetUpper
      core fallback projection upper_provider).gap⟩,
    projectLengthEndpointOfLocalHilbertTargetUpper_computed_n_eq
      core fallback projection upper_provider,
    (projectLengthEndpointOfLocalHilbertTargetUpper
      core fallback projection upper_provider).computed_n_contradiction,
    (projectLengthEndpointOfLocalHilbertTargetUpper
      core fallback projection upper_provider).not_rational⟩

end SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint
end SondowMainCheckedCodeBridge
