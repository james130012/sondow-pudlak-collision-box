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
open SondowProjectMonth11PAHilbertCheckerSurface
open SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface
open SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint

/-! ## Tail-gap frontier instantiation adapters -/

/-- Transport a tail-form strict gap across pointwise equality of the measured
functions, preserving the explicit threshold. -/
def transportTailStrictGapCertificate
    {U measuredA measuredB : Nat → Real}
    (heq : ∀ m : Nat, measuredA m = measuredB m)
    (gap : TailStrictGapCertificate U measuredA) :
    TailStrictGapCertificate U measuredB where
  threshold := gap.threshold
  strict_after := by
    intro m hm
    rw [← heq m]
    exact gap.strict_after m hm

/-- Transport a computable tail-gap certificate across pointwise equality of
the measured functions, without changing the computed threshold. -/
def transportComputableGapCertificate
    {measuredA measuredB : Nat → Real}
    (heq : ∀ m : Nat, measuredA m = measuredB m)
    (gap : ComputableGapCertificate measuredA) :
    ComputableGapCertificate measuredB where
  gap_for_polynomial_upper := fun U hU =>
    transportTailStrictGapCertificate heq
      (gap.gap_for_polynomial_upper U hU)

/-- Transport an explicit polynomial upper-tail certificate across pointwise
equality of measured functions, preserving the polynomial upper function and
the explicit cutoff. -/
def transportPolynomialUpperTailCertificate
    {measuredA measuredB : Nat → Real}
    (heq : ∀ m : Nat, measuredA m = measuredB m)
    (upper : PolynomialUpperTailCertificate measuredA) :
    PolynomialUpperTailCertificate measuredB where
  U := upper.U
  polynomial := upper.polynomial
  upperN := upper.upperN
  upper_after := by
    intro m hm
    rw [← heq m]
    exact upper.upper_after m hm

/-- Local explicit upper provider for the project-length endpoint layer.  It is
the no-`choose` version of an upper provider: rationality returns an explicit
polynomial upper-tail certificate. -/
structure ProjectLengthExplicitMeasuredUpperProvider
    (measured : Nat → Real) : Type where
  upperTailOfRationality :
    _root_.is_rational _root_.euler_mascheroni →
      PolynomialUpperTailCertificate measured

namespace ProjectLengthExplicitMeasuredUpperProvider

def transportEq
    {measuredA measuredB : Nat → Real}
    (heq : ∀ n : Nat, measuredA n = measuredB n)
    (h : ProjectLengthExplicitMeasuredUpperProvider measuredA) :
    ProjectLengthExplicitMeasuredUpperProvider measuredB where
  upperTailOfRationality := fun hrat =>
    transportPolynomialUpperTailCertificate heq
      (h.upperTailOfRationality hrat)

def toAbstract
    {measured : Nat → Real}
    (h : ProjectLengthExplicitMeasuredUpperProvider measured) :
    Month9Month10AbstractMeasuredUpperProvider measured where
  upper_under_rationality := by
    intro hrat
    let upper := h.upperTailOfRationality hrat
    exact ⟨upper.U, upper.polynomial, upper.upperN, upper.upper_after⟩

end ProjectLengthExplicitMeasuredUpperProvider

/-- Build the strongest time-bound canonical tail-gap frontier from the smaller
singleton tail-gap input plus the concrete left/right proof families.  This
turns the remaining frontier-instantiation task into the explicit obligations:
time-bound strictness, nonzero exponent, two polynomial family-length bounds,
and the checked-length code equality. -/
def timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
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
    (tail_input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
    (lengthCodeAt_eq_conj_source :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m))
    (left_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real left_family.length))
    (right_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real right_family.length)) :
    Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
      scale_data (Ax := Ax) (A := A) (B := B) where
  left_family := left_family
  right_family := right_family
  time_bound_strict := time_bound_strict
  exponent_ne_zero := exponent_ne_zero
  tail_gap :=
    transportComputableGapCertificate
      (by
        intro m
        exact_mod_cast lengthCodeAt_eq_conj_source m)
      tail_input.tail_gap
  left_length_polynomial := left_length_polynomial
  right_length_polynomial := right_length_polynomial

/-- The singleton-input frontier adapter preserves the original tail-gap
threshold exactly.  This keeps the computed large-`N` witness auditable at the
smaller input boundary, not only after frontier construction. -/
theorem singletonTailGapFrontier_tailGap_threshold_eq
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
    (tail_input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
    (lengthCodeAt_eq_conj_source :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m))
    (left_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real left_family.length))
    (right_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    ((timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero tail_input
        lengthCodeAt_eq_conj_source left_length_polynomial
        right_length_polynomial).tail_gap.gap_for_polynomial_upper U hU).threshold =
      (tail_input.tail_gap.gap_for_polynomial_upper U hU).threshold := by
  rfl

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

theorem projectLengthScale_injective_of_scale_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b) :
    Function.Injective scale_data.scale := by
  intro a b hscale_eq
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have hstrict : scale_data.scale a < scale_data.scale b :=
      scale_strict hlt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)
  · exact heq
  · have hstrict : scale_data.scale b < scale_data.scale a :=
      scale_strict hgt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)

theorem projectLengthPowerBoundRawCode_injective_of_scale_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b) :
    Function.Injective scale_data.powerBoundRawCode :=
  concretePAHilbert_powerBoundRawCode_injective_of_scale_injective
    scale_data (projectLengthScale_injective_of_scale_strict scale_strict)

theorem projectLengthPowerBoundRawCode_injective_of_timeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0) :
    Function.Injective scale_data.powerBoundRawCode :=
  projectLengthPowerBoundRawCode_injective_of_scale_strict
    (Month9Month10ActualProofLengthGapFrontier.scale_strict_of_timeConstructibleBound_strict
      time_bound_strict exponent_ne_zero)

theorem calibratedCheckerProjectLengthMeasured_eq_lengthCodeAt_of_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (fallback : _root_.FormulaCode → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    (n : Nat) :
    checkerProjectLengthMeasured scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        fallback n =
      (lengthCodeAt n : Real) :=
  concretePAHilbertPowerBoundCalibrated_projectLengthAt_eq_lengthCodeAt_of_injective
    scale_data lengthCodeAt fallback n hinjective

theorem rootProofLength_eq_lengthCodeAt_of_calibratedCheckerExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (fallback : _root_.FormulaCode → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)) :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (lengthCodeAt n : Real) := by
  intro n
  calc
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode n) =
        ((concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).minProofCodeSizeAt n : Real) :=
          exactness.at_powerBoundRawCode n
    _ =
        checkerProjectLengthMeasured scale_data
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data lengthCodeAt)
          fallback n := by
          rw [checkerProjectLengthMeasured_eq_checked]
          rfl
    _ = (lengthCodeAt n : Real) :=
        calibratedCheckerProjectLengthMeasured_eq_lengthCodeAt_of_injective
          lengthCodeAt fallback hinjective n

theorem rootProofLength_eq_lengthCodeAt_of_calibratedCheckerExactness_timeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (fallback : _root_.FormulaCode → Nat)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)) :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (lengthCodeAt n : Real) :=
  rootProofLength_eq_lengthCodeAt_of_calibratedCheckerExactness
    lengthCodeAt fallback
    (projectLengthPowerBoundRawCode_injective_of_timeBound
      time_bound_strict exponent_ne_zero)
    exactness

/-- Direct no-fallback form of the calibrated-checker-to-root equation bridge:
checker exactness gives root proof length equal to the calibrated length family
as soon as the raw-code family is injective. -/
theorem rootProofLength_eq_lengthCodeAt_of_calibratedCheckerExactness_of_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)) :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (lengthCodeAt n : Real) := by
  intro n
  calc
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode n) =
        ((concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).minProofCodeSizeAt n : Real) :=
          exactness.at_powerBoundRawCode n
    _ = (lengthCodeAt n : Real) := by
          exact_mod_cast
            concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
              scale_data lengthCodeAt n hinjective

/-- The primitive pointwise root equation is enough to build family-shaped
proof-length exactness for the calibrated PA/Hilbert checker.  The only
checker-side ingredient is injectivity of the theorem-5 raw-code family, which
makes the calibrated minimum at `n` compute exactly `lengthCodeAt n`. -/
theorem calibratedCheckerFamilyExactness_of_rootProofLength_eq_lengthCodeAt
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    (hroot :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt) where
  proof_length_eq_minProofCodeSizeAt := by
    intro n
    calc
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (lengthCodeAt n : Real) :=
          hroot n
      _ =
        ((concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).minProofCodeSizeAt n : Real) := by
          exact_mod_cast
            (concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
              scale_data lengthCodeAt n hinjective).symm

/-- Family-shaped calibrated checker exactness is also exactly the primitive
pointwise root equation.  This is the tight family-level residual before
eliminating the relevant-code existential wrapper. -/
theorem calibratedCheckerFamilyExactness_iff_rootProofLength_eq_lengthCodeAt
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt)
      ↔
      (∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) := by
  constructor
  · intro family n
    calc
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        ((concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).minProofCodeSizeAt n : Real) :=
          family.proof_length_eq_minProofCodeSizeAt n
      _ = (lengthCodeAt n : Real) := by
          exact_mod_cast
            concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
              scale_data lengthCodeAt n hinjective
  · intro hroot
    exact
      calibratedCheckerFamilyExactness_of_rootProofLength_eq_lengthCodeAt
        lengthCodeAt hinjective hroot

/-- The primitive pointwise root equation is enough to build the relevant-code
checker exactness certificate for the calibrated PA/Hilbert checker. -/
theorem calibratedCheckerExactness_of_rootProofLength_eq_lengthCodeAt
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    (hroot :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt) :=
  (calibratedCheckerFamilyExactness_of_rootProofLength_eq_lengthCodeAt
    lengthCodeAt hinjective hroot).toCheckerProofLengthExactness

/-- Calibrated checker exactness is not a separate stronger residual: under
raw-code injectivity it is equivalent to the primitive pointwise root equation
`proof_length (powerBoundRawCode n) = lengthCodeAt n`. -/
theorem calibratedCheckerExactness_iff_rootProofLength_eq_lengthCodeAt
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt)
      ↔
      (∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) := by
  constructor
  · intro exactness
    exact
      rootProofLength_eq_lengthCodeAt_of_calibratedCheckerExactness_of_injective
        lengthCodeAt hinjective exactness
  · intro hroot
    exact
      calibratedCheckerExactness_of_rootProofLength_eq_lengthCodeAt
        lengthCodeAt hinjective hroot

/-- Time-bound strictness and a nonzero exponent supply the raw-code
injectivity needed by the calibrated exactness/root-equation equivalence. -/
theorem calibratedCheckerExactness_iff_rootProofLength_eq_lengthCodeAt_timeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0) :
    InternalPudlakTheorem5CheckerProofLengthExactness
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data lengthCodeAt)
      ↔
      (∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :=
  calibratedCheckerExactness_iff_rootProofLength_eq_lengthCodeAt
    lengthCodeAt
    (projectLengthPowerBoundRawCode_injective_of_timeBound
      time_bound_strict exponent_ne_zero)

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

/-- Transport an explicit checked-measured upper-tail certificate to the checker
`projectLength` measured object.  This is the calculable version of
`checkerProjectLengthUpperProviderOfChecked`: it preserves the concrete
polynomial upper function and the explicit upper cutoff. -/
def checkerProjectLengthUpperTailCertificateOfChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (fallback : _root_.FormulaCode → Nat)
    (checked_upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    PolynomialUpperTailCertificate
      (checkerProjectLengthMeasured scale_data checker fallback) :=
  transportPolynomialUpperTailCertificate
    (fun n =>
      (checkerProjectLengthMeasured_eq_checked
        (scale_data := scale_data) (checker := checker) fallback n).symm)
    checked_upper

/-- Transport a checked-measured explicit upper provider to checker
`projectLength`.  Unlike `checkerProjectLengthUpperProviderOfChecked`, this
preserves the selected certificate under rationality instead of falling back to
an existential upper-provider shape. -/
def checkerProjectLengthExplicitUpperProviderOfChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (fallback : _root_.FormulaCode → Nat)
    (checked_upper_provider :
      ProjectLengthExplicitMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    ProjectLengthExplicitMeasuredUpperProvider
      (checkerProjectLengthMeasured scale_data checker fallback) :=
  ProjectLengthExplicitMeasuredUpperProvider.transportEq
    (fun n =>
      (checkerProjectLengthMeasured_eq_checked
        (scale_data := scale_data) (checker := checker) fallback n).symm)
    checked_upper_provider

/-- Direct explicit collision endpoint over a measured object.  Unlike
`Month9Month10AbstractMeasuredDirectCollisionEndpoint`, this endpoint keeps the
upper certificate selected by the explicit provider and computes `N` from that
certificate directly. -/
structure ProjectLengthExplicitMeasuredDirectCollisionEndpoint
    (measured : Nat → Real) : Type where
  gap : ComputableSearchGapCertificate measured
  upper_provider : ProjectLengthExplicitMeasuredUpperProvider measured

namespace ProjectLengthExplicitMeasuredDirectCollisionEndpoint

def upperTailOfRationality
    {measured : Nat → Real}
    (h : ProjectLengthExplicitMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate measured :=
  h.upper_provider.upperTailOfRationality hrat

def computedWitnessOfRationality
    {measured : Nat → Real}
    (h : ProjectLengthExplicitMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      (h.upperTailOfRationality hrat).U measured :=
  h.gap.collisionWitness (h.upperTailOfRationality hrat)

def computedCollisionNOfRationality
    {measured : Nat → Real}
    (h : ProjectLengthExplicitMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) : Nat :=
  (h.computedWitnessOfRationality hrat).n

theorem computedCollisionN_eq_searchGapWitness
    {measured : Nat → Real}
    (h : ProjectLengthExplicitMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    h.computedCollisionNOfRationality hrat =
      (h.gap.gap_for_polynomial_upper
        (h.upperTailOfRationality hrat).U
        (h.upperTailOfRationality hrat).polynomial).witness
          (h.upperTailOfRationality hrat).upperN :=
  rfl

theorem computedCollisionN_ge_upperN
    {measured : Nat → Real}
    (h : ProjectLengthExplicitMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.upperTailOfRationality hrat).upperN ≤
      h.computedCollisionNOfRationality hrat := by
  simpa [computedCollisionNOfRationality, computedWitnessOfRationality,
    ComputableSearchGapCertificate.collisionWitness,
    PolynomialUpperTailCertificate.computedSearchWitness,
    SearchStrictGapCertificate.toComputedSearchCollisionWitness] using
    (h.computedWitnessOfRationality hrat).n_ge_upper

theorem upper_at_computedCollisionN
    {measured : Nat → Real}
    (h : ProjectLengthExplicitMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    measured (h.computedCollisionNOfRationality hrat) ≤
      (h.upperTailOfRationality hrat).U
        (h.computedCollisionNOfRationality hrat) := by
  simpa [computedCollisionNOfRationality] using
    (h.computedWitnessOfRationality hrat).upper_at_n

theorem lower_at_computedCollisionN
    {measured : Nat → Real}
    (h : ProjectLengthExplicitMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (h.upperTailOfRationality hrat).U
        (h.computedCollisionNOfRationality hrat) <
      measured (h.computedCollisionNOfRationality hrat) := by
  simpa [computedCollisionNOfRationality] using
    (h.computedWitnessOfRationality hrat).lower_at_n

theorem computed_n_contradiction
    {measured : Nat → Real}
    (h : ProjectLengthExplicitMeasuredDirectCollisionEndpoint measured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (h.computedWitnessOfRationality hrat).contradiction

theorem not_rational
    {measured : Nat → Real}
    (h : ProjectLengthExplicitMeasuredDirectCollisionEndpoint measured) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat => h.computed_n_contradiction hrat

structure Audit
    {measured : Nat → Real}
    (h : ProjectLengthExplicitMeasuredDirectCollisionEndpoint measured) :
    Prop where
  explicitUpperProviderClosure :
    h.upper_provider.toAbstract.Audit
  computableSearchGap :
    Nonempty (ComputableSearchGapCertificate measured)
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
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    {measured : Nat → Real}
    (h : ProjectLengthExplicitMeasuredDirectCollisionEndpoint measured) :
    h.Audit where
  explicitUpperProviderClosure := h.upper_provider.toAbstract.audit
  computableSearchGap := ⟨h.gap⟩
  computedWitnessFormula := h.computedCollisionN_eq_searchGapWitness
  computedNGeUpperN := h.computedCollisionN_ge_upperN
  lowerAtComputedN := h.lower_at_computedCollisionN
  upperAtComputedN := h.upper_at_computedCollisionN
  contradictionAtComputedN := h.computed_n_contradiction
  endpointNotRational := h.not_rational

theorem closure
    {measured : Nat → Real}
    (h : ProjectLengthExplicitMeasuredDirectCollisionEndpoint measured) :
    h.Audit ∧
      h.upper_provider.toAbstract.Audit ∧
        Nonempty (ComputableSearchGapCertificate measured) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          h.computedCollisionNOfRationality hrat =
            (h.gap.gap_for_polynomial_upper
              (h.upperTailOfRationality hrat).U
              (h.upperTailOfRationality hrat).polynomial).witness
                (h.upperTailOfRationality hrat).upperN) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (h.upperTailOfRationality hrat).upperN ≤
            h.computedCollisionNOfRationality hrat) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (h.upperTailOfRationality hrat).U
              (h.computedCollisionNOfRationality hrat) <
            measured (h.computedCollisionNOfRationality hrat)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          measured (h.computedCollisionNOfRationality hrat) ≤
            (h.upperTailOfRationality hrat).U
              (h.computedCollisionNOfRationality hrat)) ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨h.audit,
    h.upper_provider.toAbstract.audit,
    ⟨h.gap⟩,
    h.computedCollisionN_eq_searchGapWitness,
    h.computedCollisionN_ge_upperN,
    h.lower_at_computedCollisionN,
    h.upper_at_computedCollisionN,
    h.computed_n_contradiction,
    h.not_rational⟩

end ProjectLengthExplicitMeasuredDirectCollisionEndpoint

/-- Direct explicit collision endpoint over checker `projectLength`, once the
Sondow upper side has already been expressed as an explicit checked upper
provider. -/
def checkerProjectLengthExplicitDirectEndpointOfCheckedUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (checked_upper_provider :
      ProjectLengthExplicitMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    ProjectLengthExplicitMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured scale_data checker fallback) where
  gap := checkerProjectLengthGapOfExtractor fallback extractor
  upper_provider :=
    checkerProjectLengthExplicitUpperProviderOfChecked
      fallback checked_upper_provider

theorem checkerProjectLengthExplicitDirectEndpoint_computed_n_eq_extractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (checked_upper_provider :
      ProjectLengthExplicitMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (checkerProjectLengthExplicitDirectEndpointOfCheckedUpper
        fallback extractor checked_upper_provider).computedCollisionNOfRationality
        hrat =
      extractor.witness
        ((checkerProjectLengthExplicitDirectEndpointOfCheckedUpper
          fallback extractor checked_upper_provider).upperTailOfRationality
            hrat).U
        ((checkerProjectLengthExplicitDirectEndpointOfCheckedUpper
          fallback extractor checked_upper_provider).upperTailOfRationality
            hrat).polynomial
        ((checkerProjectLengthExplicitDirectEndpointOfCheckedUpper
          fallback extractor checked_upper_provider).upperTailOfRationality
            hrat).upperN := by
  let endpoint :=
    checkerProjectLengthExplicitDirectEndpointOfCheckedUpper
      fallback extractor checked_upper_provider
  let upper := endpoint.upperTailOfRationality hrat
  calc
    endpoint.computedCollisionNOfRationality hrat =
        (endpoint.gap.gap_for_polynomial_upper
          upper.U upper.polynomial).witness upper.upperN := by
          simpa [endpoint, upper] using
            endpoint.computedCollisionN_eq_searchGapWitness hrat
    _ = extractor.witness upper.U upper.polynomial upper.upperN := by
          simpa [endpoint,
            checkerProjectLengthExplicitDirectEndpointOfCheckedUpper] using
            checkerProjectLengthGapOfExtractor_witness_eq
              fallback extractor upper.U upper.polynomial upper.upperN

theorem checkerProjectLengthExplicitDirectEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (fallback : _root_.FormulaCode → Nat)
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (checked_upper_provider :
      ProjectLengthExplicitMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    let endpoint :=
      checkerProjectLengthExplicitDirectEndpointOfCheckedUpper
        fallback extractor checked_upper_provider
    endpoint.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured scale_data checker fallback)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        endpoint.computedCollisionNOfRationality hrat =
          extractor.witness
            (endpoint.upperTailOfRationality hrat).U
            (endpoint.upperTailOfRationality hrat).polynomial
            (endpoint.upperTailOfRationality hrat).upperN) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).upperN ≤
          endpoint.computedCollisionNOfRationality hrat) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).U
            (endpoint.computedCollisionNOfRationality hrat) <
          checkerProjectLengthMeasured scale_data checker fallback
            (endpoint.computedCollisionNOfRationality hrat)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        checkerProjectLengthMeasured scale_data checker fallback
            (endpoint.computedCollisionNOfRationality hrat) ≤
          (endpoint.upperTailOfRationality hrat).U
            (endpoint.computedCollisionNOfRationality hrat)) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
        False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  let endpoint :=
    checkerProjectLengthExplicitDirectEndpointOfCheckedUpper
      fallback extractor checked_upper_provider
  exact
    ⟨endpoint.audit,
      ⟨endpoint.gap⟩,
      checkerProjectLengthExplicitDirectEndpoint_computed_n_eq_extractorWitness
        fallback extractor checked_upper_provider,
      endpoint.computedCollisionN_ge_upperN,
      endpoint.lower_at_computedCollisionN,
      endpoint.upper_at_computedCollisionN,
      endpoint.computed_n_contradiction,
      endpoint.not_rational⟩

/-! ## Explicit checked-target upper endpoint -/

/-- Explicit upper provider for an abstract checked target measurement.  This is
the no-`choose` counterpart of
`InternalPudlakTheorem5CheckedTargetUpperProvider`: rationality returns a
concrete polynomial upper-tail certificate. -/
structure ProjectLengthExplicitCheckedTargetUpperProvider
    (targetMeasured : Nat → Nat) : Type where
  upperTailOfRationality :
    _root_.is_rational _root_.euler_mascheroni →
      PolynomialUpperTailCertificate (fun m : Nat => (targetMeasured m : Real))

namespace ProjectLengthExplicitCheckedTargetUpperProvider

def toAbstract
    {targetMeasured : Nat → Nat}
    (h : ProjectLengthExplicitCheckedTargetUpperProvider targetMeasured) :
    InternalPudlakTheorem5CheckedTargetUpperProvider targetMeasured where
  upper_under_rationality := by
    intro hrat
    let upper := h.upperTailOfRationality hrat
    exact ⟨upper.U, upper.polynomial, upper.upperN, upper.upper_after⟩

end ProjectLengthExplicitCheckedTargetUpperProvider

/-- Transport an explicit checked-target upper bound to the theorem-5 checked
source measurement through a source-to-target `+2` projection, preserving the
selected cutoff. -/
def checkedExplicitUpperProviderOfCheckedTargetProjectionAndUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {targetMeasured : Nat → Nat}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        scale_data sem targetMeasured)
    (upper_provider :
      ProjectLengthExplicitCheckedTargetUpperProvider targetMeasured) :
    ProjectLengthExplicitMeasuredUpperProvider
      (month9_month10_checkedProofCodeMeasured scale_data sem) where
  upperTailOfRationality := by
    intro hrat
    let upper := upper_provider.upperTailOfRationality hrat
    exact {
      U := fun m => upper.U m + 2
      polynomial := _root_.is_polynomial_bound_add_const
        upper.polynomial (by norm_num)
      upperN := upper.upperN
      upper_after := by
        intro m hm
        have hsource :
            (sem.minProofCodeSize (scale_data.powerBoundRawCode m)
              ⟨m, rfl⟩ : Real) ≤ (targetMeasured m : Real) + 2 := by
          exact_mod_cast projection.source_le_target_add_two m
        have htarget := upper.upper_after m hm
        have hchecked :
            (sem.minProofCodeSize (scale_data.powerBoundRawCode m)
              ⟨m, rfl⟩ : Real) ≤ upper.U m + 2 := by
          nlinarith
        simpa [month9_month10_checkedProofCodeMeasured] using hchecked }

theorem checkedExplicitUpperProviderOfCheckedTargetProjectionAndUpper_upperN
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {targetMeasured : Nat → Nat}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        scale_data sem targetMeasured)
    (upper_provider :
      ProjectLengthExplicitCheckedTargetUpperProvider targetMeasured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((checkedExplicitUpperProviderOfCheckedTargetProjectionAndUpper
      projection upper_provider).upperTailOfRationality hrat).upperN =
      (upper_provider.upperTailOfRationality hrat).upperN :=
  rfl

/-- Project-length endpoint from an explicit checked target projection and upper
provider.  This is the calculable checked-target route: `N` is computed directly
from the transported explicit target upper certificate. -/
def projectLengthExplicitEndpointOfCheckedTargetUpper
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {targetMeasured : Nat → Nat}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        targetMeasured)
    (upper_provider :
      ProjectLengthExplicitCheckedTargetUpperProvider targetMeasured) :
    ProjectLengthExplicitMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        core.scale_data core.checkerSemantics fallback) :=
  checkerProjectLengthExplicitDirectEndpointOfCheckedUpper
    fallback core.rejectionExtractor
    (checkedExplicitUpperProviderOfCheckedTargetProjectionAndUpper
      projection upper_provider)

theorem projectLengthExplicitEndpointOfCheckedTargetUpper_computed_n_eq
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {targetMeasured : Nat → Nat}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        targetMeasured)
    (upper_provider :
      ProjectLengthExplicitCheckedTargetUpperProvider targetMeasured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitEndpointOfCheckedTargetUpper
        core fallback projection upper_provider).computedCollisionNOfRationality
        hrat =
      core.rejectionExtractor.witness
        ((projectLengthExplicitEndpointOfCheckedTargetUpper
          core fallback projection upper_provider).upperTailOfRationality
            hrat).U
        ((projectLengthExplicitEndpointOfCheckedTargetUpper
          core fallback projection upper_provider).upperTailOfRationality
            hrat).polynomial
        ((projectLengthExplicitEndpointOfCheckedTargetUpper
          core fallback projection upper_provider).upperTailOfRationality
            hrat).upperN := by
  simpa [projectLengthExplicitEndpointOfCheckedTargetUpper] using
    checkerProjectLengthExplicitDirectEndpoint_computed_n_eq_extractorWitness
      fallback core.rejectionExtractor
      (checkedExplicitUpperProviderOfCheckedTargetProjectionAndUpper
        projection upper_provider)
      hrat

theorem projectLengthExplicitEndpointOfCheckedTargetUpper_upperN
    (core : PAHilbertCanonicalSearchCore)
    (fallback : _root_.FormulaCode → Nat)
    {targetMeasured : Nat → Nat}
    (projection :
      InternalPudlakTheorem5CheckedTargetProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics
        targetMeasured)
    (upper_provider :
      ProjectLengthExplicitCheckedTargetUpperProvider targetMeasured)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((projectLengthExplicitEndpointOfCheckedTargetUpper
      core fallback projection upper_provider).upperTailOfRationality
        hrat).upperN =
      (upper_provider.upperTailOfRationality hrat).upperN :=
  rfl

/-- Explicit concrete-proof-family target upper provider generated from the
family length polynomial bound.  Its upper cutoff is definitionally `0`. -/
def projectLengthConcreteProofFamilyExplicitUpperProviderOfLengthPolynomial
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (hpoly :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real target_family.length)) :
    ProjectLengthExplicitCheckedTargetUpperProvider
      (InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection.targetMeasured
        target_family) where
  upperTailOfRationality := by
    intro _hrat
    exact {
      U := _root_.MiniHilbert.nat_bound_as_real target_family.length
      polynomial := hpoly
      upperN := 0
      upper_after := by
        intro m _hm
        have hmin :
            target_family.minCheckedCodeSize m ≤ target_family.length m := by
          rw [_root_.MiniHilbert.ConcreteProofFamily.minCheckedCodeSize_eq_minLength]
          exact target_family.minLength_le_length m
        have hminReal :
            (target_family.minCheckedCodeSize m : Real) ≤
              (target_family.length m : Real) := by
          exact_mod_cast hmin
        simpa [_root_.MiniHilbert.nat_bound_as_real,
          InternalPudlakTheorem5ConcreteProofFamilyCheckedTargetProjection.targetMeasured]
          using hminReal }

theorem projectLengthConcreteProofFamilyExplicitUpperProviderOfLengthPolynomial_upperN
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (hpoly :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real target_family.length))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((projectLengthConcreteProofFamilyExplicitUpperProviderOfLengthPolynomial
      (target_family := target_family) hpoly).upperTailOfRationality
        hrat).upperN = 0 :=
  rfl

/-- Explicit project-length endpoint when the concrete target proof-family
length is polynomially bounded.  This is the computable certificate shape:
the transported upper cutoff remains `0`. -/
def projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
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
    ProjectLengthExplicitMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        core.scale_data core.checkerSemantics fallback) :=
  projectLengthExplicitEndpointOfCheckedTargetUpper
    core fallback projection.toCheckedTargetProjection
    (projectLengthConcreteProofFamilyExplicitUpperProviderOfLengthPolynomial
      hpoly)

theorem projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial_upperN
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
    ((projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
      core fallback projection hpoly).upperTailOfRationality hrat).upperN =
      0 :=
  rfl

theorem projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial_computed_n_eq
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
    (projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
        core fallback projection hpoly).computedCollisionNOfRationality
        hrat =
      core.rejectionExtractor.witness
        ((projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
          core fallback projection hpoly).upperTailOfRationality hrat).U
        ((projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
          core fallback projection hpoly).upperTailOfRationality
            hrat).polynomial
        0 := by
  calc
    (projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
        core fallback projection hpoly).computedCollisionNOfRationality
        hrat =
      core.rejectionExtractor.witness
        ((projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
          core fallback projection hpoly).upperTailOfRationality hrat).U
        ((projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
          core fallback projection hpoly).upperTailOfRationality
            hrat).polynomial
        ((projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
          core fallback projection hpoly).upperTailOfRationality
            hrat).upperN :=
        projectLengthExplicitEndpointOfCheckedTargetUpper_computed_n_eq
          core fallback projection.toCheckedTargetProjection
          (projectLengthConcreteProofFamilyExplicitUpperProviderOfLengthPolynomial
            hpoly)
          hrat
    _ = core.rejectionExtractor.witness
        ((projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
          core fallback projection hpoly).upperTailOfRationality hrat).U
        ((projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
          core fallback projection hpoly).upperTailOfRationality
            hrat).polynomial
        0 := by
          rw [projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial_upperN]

theorem projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial_closure
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
    let endpoint :=
      projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
        core fallback projection hpoly
    endpoint.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            core.scale_data core.checkerSemantics fallback)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        endpoint.computedCollisionNOfRationality hrat =
          core.rejectionExtractor.witness
            (endpoint.upperTailOfRationality hrat).U
            (endpoint.upperTailOfRationality hrat).polynomial
            0) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).upperN = 0) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).upperN ≤
          endpoint.computedCollisionNOfRationality hrat) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).U
            (endpoint.computedCollisionNOfRationality hrat) <
          checkerProjectLengthMeasured
            core.scale_data core.checkerSemantics fallback
            (endpoint.computedCollisionNOfRationality hrat)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        checkerProjectLengthMeasured
            core.scale_data core.checkerSemantics fallback
            (endpoint.computedCollisionNOfRationality hrat) ≤
          (endpoint.upperTailOfRationality hrat).U
            (endpoint.computedCollisionNOfRationality hrat)) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
        False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  let endpoint :=
    projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
      core fallback projection hpoly
  exact
    ⟨endpoint.audit,
      ⟨endpoint.gap⟩,
      projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial_computed_n_eq
        core fallback projection hpoly,
      projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial_upperN
        core fallback projection hpoly,
      endpoint.computedCollisionN_ge_upperN,
      endpoint.lower_at_computedCollisionN,
      endpoint.upper_at_computedCollisionN,
      endpoint.computed_n_contradiction,
      endpoint.not_rational⟩

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

/-- Explicit project-length endpoint from the concrete length-code frontier.
This keeps the same lower-search data as the abstract endpoint but exposes the
computable `N = rejectionExtractor.witness U polynomial 0` formula. -/
def projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier
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
    ProjectLengthExplicitMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        scale_data frontier.lower_search.checkerSemantics fallback) :=
  projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial
    frontier.lower_search.toCanonicalSearchCore
    fallback frontier.projection frontier.target_length_polynomial

theorem projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier_upperN
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
    ((projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier
      fallback frontier).upperTailOfRationality hrat).upperN = 0 :=
  rfl

theorem projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier_computed_n_eq
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
    (projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier
        fallback frontier).computedCollisionNOfRationality hrat =
      frontier.lower_search.rejectionExtractor.witness
        ((projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier
          fallback frontier).upperTailOfRationality hrat).U
        ((projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier
          fallback frontier).upperTailOfRationality hrat).polynomial
        0 := by
  simpa [projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier,
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput.toCanonicalSearchCore] using
    projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial_computed_n_eq
      frontier.lower_search.toCanonicalSearchCore
      fallback frontier.projection frontier.target_length_polynomial hrat

theorem projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier_closure
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
    let endpoint :=
      projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier
        fallback frontier
    endpoint.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            scale_data frontier.lower_search.checkerSemantics fallback)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        endpoint.computedCollisionNOfRationality hrat =
          frontier.lower_search.rejectionExtractor.witness
            (endpoint.upperTailOfRationality hrat).U
            (endpoint.upperTailOfRationality hrat).polynomial
            0) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).upperN = 0) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).upperN ≤
          endpoint.computedCollisionNOfRationality hrat) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).U
            (endpoint.computedCollisionNOfRationality hrat) <
          checkerProjectLengthMeasured
            scale_data frontier.lower_search.checkerSemantics fallback
            (endpoint.computedCollisionNOfRationality hrat)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        checkerProjectLengthMeasured
            scale_data frontier.lower_search.checkerSemantics fallback
            (endpoint.computedCollisionNOfRationality hrat) ≤
          (endpoint.upperTailOfRationality hrat).U
            (endpoint.computedCollisionNOfRationality hrat)) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
        False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier,
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput.toCanonicalSearchCore] using
    projectLengthExplicitEndpointOfConcreteProofFamilyLengthPolynomial_closure
      frontier.lower_search.toCanonicalSearchCore
      fallback frontier.projection frontier.target_length_polynomial

/-- Public main closure for the concrete length-code frontier after transport
to checker `projectLength`.  This is the direct replacement for reading the
theorem-5 family through the root `proof_length` box: the measured object is
`ProofCodeSemantics.projectLength`, and the computed collision index is the
same lower-search rejection-extractor witness. -/
theorem projectLengthEndpointOfConcreteLengthCodeTargetFrontier_publicMainClosure
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
    let endpoint :=
      projectLengthEndpointOfConcreteLengthCodeTargetFrontier
        fallback frontier
    endpoint.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            scale_data frontier.lower_search.checkerSemantics fallback)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          endpoint.computedCollisionNOfRationality hrat =
            frontier.lower_search.rejectionExtractor.witness
              (endpoint.upperTailOfRationality hrat).U
              (endpoint.upperTailOfRationality hrat).polynomial
              (endpoint.upperTailOfRationality hrat).upperN) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (endpoint.upperTailOfRationality hrat).upperN ≤
              endpoint.computedCollisionNOfRationality hrat) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              (endpoint.upperTailOfRationality hrat).U
                  (endpoint.computedCollisionNOfRationality hrat) <
                checkerProjectLengthMeasured
                  scale_data frontier.lower_search.checkerSemantics fallback
                  (endpoint.computedCollisionNOfRationality hrat)) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                checkerProjectLengthMeasured
                    scale_data frontier.lower_search.checkerSemantics fallback
                    (endpoint.computedCollisionNOfRationality hrat) ≤
                  (endpoint.upperTailOfRationality hrat).U
                    (endpoint.computedCollisionNOfRationality hrat)) ∧
                (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                  False) ∧
                ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    projectLengthEndpointOfConcreteLengthCodeTargetFrontier
      fallback frontier
  exact
    ⟨endpoint.audit,
      ⟨endpoint.gap⟩,
      projectLengthEndpointOfConcreteLengthCodeTargetFrontier_computed_n_eq
        fallback frontier,
      endpoint.computedCollisionN_ge_upperN,
      endpoint.lower_at_computedCollisionN,
      endpoint.upper_at_computedCollisionN,
      endpoint.computed_n_contradiction,
      endpoint.not_rational⟩

/-! ## Concrete length-code explicit search witness -/

/-- Checked upper tail transported to the checker `projectLength` measured
object for any concrete length-code frontier. -/
noncomputable def projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
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
    PolynomialUpperTailCertificate
      (checkerProjectLengthMeasured
        scale_data frontier.lower_search.checkerSemantics fallback) :=
  let checkedTail :=
    checkedSearchUpperTail
      frontier.lower_search.toProofLengthFreeMonth12Candidate
      frontier.checkedUpperProvider
      hrat
  {
    U := checkedTail.U
    polynomial := checkedTail.polynomial
    upperN := checkedTail.upperN
    upper_after := by
      intro m hm
      have hchecked := checkedTail.upper_after m hm
      simpa [checkerProjectLengthMeasured_eq_checked,
        checkedSearchUpperTail,
        Month9Month10CheckedSearchCollisionEndpoint.toDirectEndpoint,
        SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.Month12ProofLengthFreeCheckerSearchCandidate.toCheckedSearchCollisionEndpoint,
        SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.PAHilbertCanonicalSearchCore.toProofLengthFreeMonth12Candidate,
        ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput.toProofLengthFreeMonth12Candidate,
        ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput.toCanonicalSearchCore]
        using hchecked }

/-- Computable search gap for the concrete length-code frontier, transported
to the checker `projectLength` measured object. -/
def projectLengthSearchGapOfConcreteLengthCodeTargetFrontier
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
    ComputableSearchGapCertificate
      (checkerProjectLengthMeasured
        scale_data frontier.lower_search.checkerSemantics fallback) where
  gap_for_polynomial_upper := by
    intro U hU
    let sourceGap := frontier.lower_search.gap.gap_for_polynomial_upper U hU
    exact {
      witness := sourceGap.witness
      witness_ge := sourceGap.witness_ge
      strict_at_witness := by
        intro N
        let w := sourceGap.witness N
        have hsourceStrict :
            U w <
              (frontier.lower_search.lengthCodeAt w : Real) := by
          exact sourceGap.strict_at_witness N
        have hcheckedTarget :
            month9_month10_checkedProofCodeMeasured
                scale_data
                frontier.lower_search.checkerSemantics.toProofCodeSemantics
                w =
              (target_family.rightConjElim.minCheckedCodeSize w : Real) := by
          simpa [month9_month10_checkedProofCodeMeasured] using
            (show
              (frontier.lower_search.checkerSemantics.toProofCodeSemantics.minProofCodeSize
                  (scale_data.powerBoundRawCode w) ⟨w, rfl⟩ : Real) =
                (target_family.rightConjElim.minCheckedCodeSize w : Real) from by
                exact_mod_cast
                  frontier.projection.theorem5_source_eq_family_source w)
        have hlengthTarget :
            (frontier.lower_search.lengthCodeAt w : Real) =
              (target_family.rightConjElim.minCheckedCodeSize w : Real) := by
          exact_mod_cast frontier.lengthCodeAt_eq_family_source w
        have hproject :
            checkerProjectLengthMeasured
                scale_data frontier.lower_search.checkerSemantics fallback w =
              (frontier.lower_search.lengthCodeAt w : Real) := by
          rw [checkerProjectLengthMeasured_eq_checked]
          exact hcheckedTarget.trans hlengthTarget.symm
        rw [hproject.symm] at hsourceStrict
        exact hsourceStrict }

theorem projectLengthSearchGapOfConcreteLengthCodeTargetFrontier_witness_eq_inputGap
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
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((projectLengthSearchGapOfConcreteLengthCodeTargetFrontier
        fallback frontier).gap_for_polynomial_upper U hU).witness N =
      ((frontier.lower_search.gap.gap_for_polynomial_upper U hU).witness
        N) :=
  rfl

theorem projectLengthSearchGapOfConcreteLengthCodeTargetFrontier_witness_eq_checkedMeasuredGap
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
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((projectLengthSearchGapOfConcreteLengthCodeTargetFrontier
        fallback frontier).gap_for_polynomial_upper U hU).witness N =
      ((frontier.lower_search.checkedMeasuredGap.gap_for_polynomial_upper
        U hU).witness N) := by
  calc
    ((projectLengthSearchGapOfConcreteLengthCodeTargetFrontier
        fallback frontier).gap_for_polynomial_upper U hU).witness N =
        ((frontier.lower_search.gap.gap_for_polynomial_upper U hU).witness
          N) :=
          projectLengthSearchGapOfConcreteLengthCodeTargetFrontier_witness_eq_inputGap
            fallback frontier U hU N
    _ = ((frontier.lower_search.checkedMeasuredGap.gap_for_polynomial_upper
        U hU).witness N) :=
          (frontier.lower_search.checkedMeasuredGap_witness_eq_inputGap
            U hU N).symm

theorem projectLengthSearchGapOfConcreteLengthCodeTargetFrontier_witness_eq_rejectionExtractor
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
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((projectLengthSearchGapOfConcreteLengthCodeTargetFrontier
        fallback frontier).gap_for_polynomial_upper U hU).witness N =
      frontier.lower_search.rejectionExtractor.witness U hU N := by
  calc
    ((projectLengthSearchGapOfConcreteLengthCodeTargetFrontier
        fallback frontier).gap_for_polynomial_upper U hU).witness N =
        ((frontier.lower_search.checkedMeasuredGap.gap_for_polynomial_upper
          U hU).witness N) :=
          projectLengthSearchGapOfConcreteLengthCodeTargetFrontier_witness_eq_checkedMeasuredGap
            fallback frontier U hU N
    _ = frontier.lower_search.rejectionExtractor.witness U hU N :=
          rfl

/-- Explicit search-style project-length collision witness for a concrete
length-code frontier.  Its index is the lower-search witness at the selected
upper threshold. -/
noncomputable def projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier
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
    ComputedSearchCollisionWitness
      (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
        fallback frontier hrat).U
      (checkerProjectLengthMeasured
        scale_data frontier.lower_search.checkerSemantics fallback) :=
  let upper :=
    projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
      fallback frontier hrat
  upper.computedSearchWitness
    ((projectLengthSearchGapOfConcreteLengthCodeTargetFrontier
      fallback frontier).gap_for_polynomial_upper
        upper.U upper.polynomial)

theorem projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier_n_eq
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
    (projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier
      fallback frontier hrat).n =
      (frontier.lower_search.gap.gap_for_polynomial_upper
        (checkedSearchUpperTail
          frontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.checkedUpperProvider
          hrat).U
        (checkedSearchUpperTail
          frontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.checkedUpperProvider
          hrat).polynomial).witness
        (checkedSearchUpperTail
          frontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.checkedUpperProvider
          hrat).upperN := by
  rfl

theorem projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier_n_eq_rejectionExtractorWitness
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
    (projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier
      fallback frontier hrat).n =
      frontier.lower_search.rejectionExtractor.witness
        (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback frontier hrat).U
        (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback frontier hrat).polynomial
        (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback frontier hrat).upperN := by
  let upper := projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
    fallback frontier hrat
  calc
    (projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier
        fallback frontier hrat).n =
        ((projectLengthSearchGapOfConcreteLengthCodeTargetFrontier
            fallback frontier).gap_for_polynomial_upper
            upper.U upper.polynomial).witness upper.upperN := by
          rfl
    _ = frontier.lower_search.rejectionExtractor.witness
          upper.U upper.polynomial upper.upperN := by
          exact
            projectLengthSearchGapOfConcreteLengthCodeTargetFrontier_witness_eq_rejectionExtractor
              fallback frontier upper.U upper.polynomial upper.upperN

/-- The explicit project-length search witness computes exactly the same
collision index as the proof-length-free theorem-5 provider.  This is the
stable equality used by the clean route; it avoids the abstract endpoint's
`Classical.choose` upper-tail path and compares the concrete search witnesses
directly. -/
theorem projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier_n_eq_providerComputedN
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
    (projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier
      fallback frontier hrat).n =
      frontier.computedCollisionNOfRationality hrat := by
  calc
    (projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier
        fallback frontier hrat).n =
        frontier.lower_search.rejectionExtractor.witness
          (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
            fallback frontier hrat).U
          (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
            fallback frontier hrat).polynomial
          (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
            fallback frontier hrat).upperN :=
          projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier_n_eq_rejectionExtractorWitness
            fallback frontier hrat
    _ =
        frontier.lower_search.rejectionExtractor.witness
          (checkedSearchUpperTail
            frontier.lower_search.toProofLengthFreeMonth12Candidate
            frontier.checkedUpperProvider hrat).U
          (checkedSearchUpperTail
            frontier.lower_search.toProofLengthFreeMonth12Candidate
            frontier.checkedUpperProvider hrat).polynomial
          (checkedSearchUpperTail
            frontier.lower_search.toProofLengthFreeMonth12Candidate
            frontier.checkedUpperProvider hrat).upperN := by
          rfl
    _ = frontier.computedCollisionNOfRationality hrat :=
          (frontier.computedCollisionN_eq_rejectionExtractorWitness hrat).symm

theorem projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier_contradiction
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
    False :=
  (projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier
    fallback frontier hrat).contradiction

theorem projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier_not_rational
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
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat =>
    projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier_contradiction
      fallback frontier hrat

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

/-! ## Time-bound canonical explicit search witness -/

/-- Checked upper tail for the time-bound canonical search frontier, transported
to checker `projectLength`.  This names the tail used by the explicit computed
search witness so later audit statements do not hide it behind unfolding. -/
noncomputable def projectLengthUpperTailOfTimeBoundCanonicalSearchFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate
      (checkerProjectLengthMeasured
        scale_data
        (frontier.canonicalFrontier
          |>.conjIntroLengthCodeFrontier
          |>.concreteLengthCodeFrontier
          |>.lower_search
          |>.checkerSemantics)
        fallback) :=
  projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
    fallback
    (frontier.canonicalFrontier
      |>.conjIntroLengthCodeFrontier
      |>.concreteLengthCodeFrontier)
    hrat

/-- Explicit search-style project-length collision witness for the time-bound
canonical target-search frontier.  This is the proof-complexity-native computed
`n` route: no tail threshold is required. -/
noncomputable def projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
        fallback
        (frontier.canonicalFrontier
          |>.conjIntroLengthCodeFrontier
          |>.concreteLengthCodeFrontier)
        hrat).U
      (checkerProjectLengthMeasured
        scale_data
        (frontier.canonicalFrontier
          |>.conjIntroLengthCodeFrontier
          |>.concreteLengthCodeFrontier
          |>.lower_search
          |>.checkerSemantics)
        fallback) :=
  projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier
    fallback
    (frontier.canonicalFrontier
      |>.conjIntroLengthCodeFrontier
      |>.concreteLengthCodeFrontier)
    hrat

theorem projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
      fallback frontier hrat).n =
      (frontier.gap.gap_for_polynomial_upper
        (checkedSearchUpperTail
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.lower_search
            |>.toProofLengthFreeMonth12Candidate)
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.checkedUpperProvider)
          hrat).U
        (checkedSearchUpperTail
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.lower_search
            |>.toProofLengthFreeMonth12Candidate)
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.checkedUpperProvider)
          hrat).polynomial).witness
        (checkedSearchUpperTail
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.lower_search
            |>.toProofLengthFreeMonth12Candidate)
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.checkedUpperProvider)
          hrat).upperN := by
  rfl

theorem projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_n_eq_checkedMeasuredGapWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
      fallback frontier hrat).n =
      (((frontier.canonicalFrontier
          |>.conjIntroLengthCodeFrontier
          |>.concreteLengthCodeFrontier
          |>.lower_search
          |>.checkedMeasuredGap).gap_for_polynomial_upper
        (checkedSearchUpperTail
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.lower_search
            |>.toProofLengthFreeMonth12Candidate)
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.checkedUpperProvider)
          hrat).U
        (checkedSearchUpperTail
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.lower_search
            |>.toProofLengthFreeMonth12Candidate)
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.checkedUpperProvider)
          hrat).polynomial).witness
        (checkedSearchUpperTail
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.lower_search
            |>.toProofLengthFreeMonth12Candidate)
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.checkedUpperProvider)
          hrat).upperN) := by
  let concreteFrontier :=
    frontier.canonicalFrontier
      |>.conjIntroLengthCodeFrontier
      |>.concreteLengthCodeFrontier
  let tail :=
    checkedSearchUpperTail
      concreteFrontier.lower_search.toProofLengthFreeMonth12Candidate
      concreteFrontier.checkedUpperProvider
      hrat
  calc
    (projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
        fallback frontier hrat).n =
        (frontier.gap.gap_for_polynomial_upper tail.U tail.polynomial).witness
          tail.upperN := by
          simpa [concreteFrontier, tail] using
            projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_n_eq
              fallback frontier hrat
    _ =
        ((concreteFrontier.lower_search.checkedMeasuredGap
          |>.gap_for_polynomial_upper tail.U tail.polynomial).witness
          tail.upperN) := by
          exact
            (concreteFrontier.lower_search.checkedMeasuredGap_witness_eq_inputGap
              tail.U tail.polynomial tail.upperN).symm

theorem projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_n_eq_rejectionExtractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
      fallback frontier hrat).n =
      frontier.canonicalFrontier.lowerSearch.rejectionExtractor.witness
        (projectLengthUpperTailOfTimeBoundCanonicalSearchFrontier
          fallback frontier hrat).U
        (projectLengthUpperTailOfTimeBoundCanonicalSearchFrontier
          fallback frontier hrat).polynomial
        (projectLengthUpperTailOfTimeBoundCanonicalSearchFrontier
          fallback frontier hrat).upperN := by
  let concreteFrontier :=
    frontier.canonicalFrontier
      |>.conjIntroLengthCodeFrontier
      |>.concreteLengthCodeFrontier
  simpa [projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier,
    projectLengthUpperTailOfTimeBoundCanonicalSearchFrontier,
    concreteFrontier,
    Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier.canonicalFrontier,
    Month9Month10CanonicalConjIntroTargetSearchFrontier.conjIntroLengthCodeFrontier,
    Month9Month10ConjIntroLengthCodeTargetInternalTheorem5Frontier.concreteLengthCodeFrontier] using
    projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier_n_eq_rejectionExtractorWitness
      fallback concreteFrontier hrat

theorem projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_contradiction
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
    fallback frontier hrat).contradiction

theorem projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_not_rational
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat =>
    projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_contradiction
      fallback frontier hrat

theorem projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
      fallback frontier hrat).n =
      (frontier.gap.gap_for_polynomial_upper
        (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier)
          hrat).U
        (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier)
          hrat).polynomial).witness
        (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier)
          hrat).upperN ∧
      (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier)
          hrat).upperN ≤
        (projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
          fallback frontier hrat).n ∧
      (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier)
          hrat).U
          (projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
            fallback frontier hrat).n <
        checkerProjectLengthMeasured
          scale_data
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.lower_search
            |>.checkerSemantics)
          fallback
          (projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
            fallback frontier hrat).n ∧
      checkerProjectLengthMeasured
          scale_data
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier
            |>.lower_search
            |>.checkerSemantics)
          fallback
          (projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
            fallback frontier hrat).n ≤
        (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback
          (frontier.canonicalFrontier
            |>.conjIntroLengthCodeFrontier
            |>.concreteLengthCodeFrontier)
          hrat).U
          (projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
            fallback frontier hrat).n ∧
      False ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  let concreteFrontier :=
    frontier.canonicalFrontier
      |>.conjIntroLengthCodeFrontier
      |>.concreteLengthCodeFrontier
  let w :=
    projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
      fallback frontier hrat
  exact
    ⟨projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_n_eq
        fallback frontier hrat,
      w.n_ge_upper,
      w.lower_at_n,
      w.upper_at_n,
      w.contradiction,
      projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_not_rational
        fallback frontier⟩

theorem projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_internalExtractorClosure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetSearchFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier
      fallback frontier hrat).n =
      frontier.canonicalFrontier.lowerSearch.rejectionExtractor.witness
        (projectLengthUpperTailOfTimeBoundCanonicalSearchFrontier
          fallback frontier hrat).U
        (projectLengthUpperTailOfTimeBoundCanonicalSearchFrontier
          fallback frontier hrat).polynomial
        (projectLengthUpperTailOfTimeBoundCanonicalSearchFrontier
          fallback frontier hrat).upperN ∧
      False ∧
      ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_n_eq_rejectionExtractorWitness
      fallback frontier hrat,
    projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_contradiction
      fallback frontier hrat,
    projectLengthExplicitSearchWitnessOfTimeBoundCanonicalSearchFrontier_not_rational
      fallback frontier⟩

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

/-- Provider-computed collision index for a time-bound tail-gap frontier is the
same lower-search rejection-extractor witness used by the proof-length-free
checker endpoint.  This is the witness form complementary to
`computedCollisionN_eq_tailGapMax`: the same `N` is both the explicit
`max upperN threshold` and the lower-machine extractor witness. -/
theorem tailGapComputedN_eq_rejectionExtractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    frontier.computedCollisionNOfRationality hrat =
      frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
        (checkedSearchUpperTail
          frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.concreteLengthCodeFrontier.checkedUpperProvider
          hrat).U
        (checkedSearchUpperTail
          frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.concreteLengthCodeFrontier.checkedUpperProvider
          hrat).polynomial
        (checkedSearchUpperTail
          frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.concreteLengthCodeFrontier.checkedUpperProvider
          hrat).upperN := by
  calc
    frontier.computedCollisionNOfRationality hrat =
        frontier.concreteLengthCodeFrontier.computedCollisionNOfRationality hrat :=
          rfl
    _ =
        frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
          (checkedSearchUpperTail
            frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
            frontier.concreteLengthCodeFrontier.checkedUpperProvider
            hrat).U
          (checkedSearchUpperTail
            frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
            frontier.concreteLengthCodeFrontier.checkedUpperProvider
            hrat).polynomial
          (checkedSearchUpperTail
            frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
            frontier.concreteLengthCodeFrontier.checkedUpperProvider
            hrat).upperN := by
          simpa [
            Month9Month10ConcreteLengthCodeTargetInternalTheorem5Frontier.checkedUpperProvider]
            using
            frontier.concreteLengthCodeFrontier.computedCollisionN_eq_rejectionExtractorWitness
              hrat

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

/-- The checked upper tail, transported to the checker `projectLength` measured
object without using the endpoint's own `Classical.choose` path. -/
noncomputable def projectLengthUpperTailOfTimeBoundCanonicalTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate
      (checkerProjectLengthMeasured
        scale_data frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback) :=
  let checkedTail :=
    checkedSearchUpperTail
      frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
      frontier.concreteLengthCodeFrontier.checkedUpperProvider
      hrat
  {
    U := checkedTail.U
    polynomial := checkedTail.polynomial
    upperN := checkedTail.upperN
    upper_after := by
      intro m hm
      have hchecked := checkedTail.upper_after m hm
      simpa [checkerProjectLengthMeasured_eq_checked,
        checkedSearchUpperTail,
        Month9Month10CheckedSearchCollisionEndpoint.toDirectEndpoint,
        SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.Month12ProofLengthFreeCheckerSearchCandidate.toCheckedSearchCollisionEndpoint,
        SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.PAHilbertCanonicalSearchCore.toProofLengthFreeMonth12Candidate,
        ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput.toProofLengthFreeMonth12Candidate,
        ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput.toCanonicalSearchCore]
        using hchecked }

/-- On the time-bound canonical tail-gap frontier, the checker `projectLength`
measurement is exactly the concrete right-conj-eliminated proof-family minimum
checked code size.  This exposes the proof-length-free target that the final
root `proof_length` exactness bridge must match. -/
theorem projectLengthMeasuredOfTimeBoundCanonicalTailGap_eq_familyMinChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (m : Nat) :
    checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback m =
      (((frontier.left_family.conjIntro frontier.right_family)
        |>.rightConjElim
        |>.minCheckedCodeSize m : Nat) : Real) := by
  rw [checkerProjectLengthMeasured_eq_checked]
  simpa [month9_month10_checkedProofCodeMeasured] using
    (show
      (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics.minProofCodeSize
          (scale_data.powerBoundRawCode m) ⟨m, rfl⟩ : Real) =
        (((frontier.left_family.conjIntro frontier.right_family)
          |>.rightConjElim
          |>.minCheckedCodeSize m : Nat) : Real) from by
        exact_mod_cast
          frontier.concreteLengthCodeFrontier.projection
            |>.theorem5_source_eq_family_source m)

/-- The final root-proof-length residual for the time-bound canonical tail-gap
route is exactly pointwise agreement with the concrete proof-family
`minCheckedCodeSize`.  The left-to-right direction is the remaining bridge
specialized to this frontier; the right-to-left direction reconstructs that
bridge without any additional theorem-5 lower-bound data. -/
theorem tailGapActualBridge_iff_actual_eq_familyMinChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data
        (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)
      ↔
      (∀ m : Nat,
        actualProofLengthMeasured scale_data m =
          (((frontier.left_family.conjIntro frontier.right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m : Nat) : Real)) := by
  constructor
  · intro bridge m
    have hproject_actual :
        checkerProjectLengthMeasured
            scale_data
            frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
            fallback m =
          actualProofLengthMeasured scale_data m :=
      (checkerProjectLengthMeasured_eq_checked
        (scale_data := scale_data)
        (checker :=
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics)
        fallback m).trans (bridge.checked_eq_actual m)
    exact
      hproject_actual.symm.trans
        (projectLengthMeasuredOfTimeBoundCanonicalTailGap_eq_familyMinChecked
          fallback frontier m)
  · intro h
    refine ⟨?_⟩
    intro m
    have hproject_family :=
      projectLengthMeasuredOfTimeBoundCanonicalTailGap_eq_familyMinChecked
        fallback frontier m
    have hproject_checked :
        checkerProjectLengthMeasured
            scale_data
            frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
            fallback m =
          month9_month10_checkedProofCodeMeasured
            scale_data
            frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics
            m :=
      checkerProjectLengthMeasured_eq_checked
        (scale_data := scale_data)
        (checker :=
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics)
        fallback m
    exact hproject_checked.symm.trans (hproject_family.trans (h m).symm)

/-- Concrete proof-length-code model replacing the bare root `proof_length`
symbol on the theorem-5 power-bound fragment.  Its length is induced by the
same PA/Hilbert checker semantics used by the clean project-length route. -/
noncomputable def tailGapProofLengthCodeSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    _root_.ProofLengthCodeSemantics.{0}
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) where
  proof_code_semantics :=
    frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics
  fallback_length := fallback

/-- The concrete replacement proof-length model agrees with the checker
`projectLength` measured object on the theorem-5 raw-code family. -/
theorem tailGapProofLengthCodeSemantics_length_eq_projectLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (m : Nat) :
    (((tailGapProofLengthCodeSemantics fallback frontier).length
        (scale_data.powerBoundRawCode m) : Nat) : Real) =
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback m := by
  rw [_root_.ProofLengthCodeSemantics.length,
    checkerProjectLengthMeasured,
    _root_.ProofCodeSemantics.projectLength]
  rfl

/-- The concrete replacement proof-length model is the same concrete
right-conj-eliminated proof-family minimum checked code size.  This is the
axiom-free exactness target that replaces the old root `proof_length` symbol in
the final theorem-5 route. -/
theorem tailGapProofLengthCodeSemantics_length_eq_familyMinChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (m : Nat) :
    (((tailGapProofLengthCodeSemantics fallback frontier).length
        (scale_data.powerBoundRawCode m) : Nat) : Real) =
      (((frontier.left_family.conjIntro frontier.right_family)
        |>.rightConjElim
        |>.minCheckedCodeSize m : Nat) : Real) := by
  exact
    (tailGapProofLengthCodeSemantics_length_eq_projectLengthMeasured
      fallback frontier m).trans
      (projectLengthMeasuredOfTimeBoundCanonicalTailGap_eq_familyMinChecked
        fallback frontier m)

/-- Local theorem-5 code-map fact: the internal power-bound raw code is the
rescaled Pudlak strengthened finite-consistency code used by the literature
statement map. -/
theorem tailGapPowerBoundRawCode_eq_rescaledPudlak
    (scale_data : InternalPudlakTheorem5ScaleData) (m : Nat) :
    scale_data.powerBoundRawCode m =
      _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
        scale_data.scale m :=
  InternalPudlakTheorem5ScaleData.powerBoundRawCode_eq_rescaledPudlak
    scale_data m

/-- Local theorem-5 statement-map chain: the literature rescaled raw code, the
internal power-bound raw code, and the rescaled Pudlak strengthened
finite-consistency code are the same formula-code family. -/
theorem tailGapRawRescaledPowerCodeChain
    (scale_data : InternalPudlakTheorem5ScaleData) (m : Nat) :
    scale_data.rescaledRawCode m = scale_data.powerBoundRawCode m ∧
      scale_data.powerBoundRawCode m =
        _root_.rescaledPudlakStrengthenedFiniteConsistencyCode
          scale_data.scale m :=
  ⟨InternalPudlakTheorem5ScaleData.rescaledRawCode_eq_powerBoundRawCode
      scale_data m,
    tailGapPowerBoundRawCode_eq_rescaledPudlak scale_data m⟩

/-- The concrete replacement proof-length model agrees with checker
`projectLength` on the literature rescaled raw-code form of theorem 5. -/
theorem tailGapProofLengthCodeSemantics_length_at_rescaledRawCode_eq_projectLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (m : Nat) :
    (((tailGapProofLengthCodeSemantics fallback frontier).length
        (scale_data.rescaledRawCode m) : Nat) : Real) =
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback m := by
  rw [(tailGapRawRescaledPowerCodeChain scale_data m).1]
  exact
    tailGapProofLengthCodeSemantics_length_eq_projectLengthMeasured
      fallback frontier m

/-- On the literature rescaled raw-code form, the concrete replacement
proof-length model is exactly the concrete right-conj-eliminated proof-family
minimum checked code size. -/
theorem tailGapProofLengthCodeSemantics_length_at_rescaledRawCode_eq_familyMinChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (m : Nat) :
    (((tailGapProofLengthCodeSemantics fallback frontier).length
        (scale_data.rescaledRawCode m) : Nat) : Real) =
      (((frontier.left_family.conjIntro frontier.right_family)
        |>.rightConjElim
        |>.minCheckedCodeSize m : Nat) : Real) := by
  rw [(tailGapRawRescaledPowerCodeChain scale_data m).1]
  exact
    tailGapProofLengthCodeSemantics_length_eq_familyMinChecked
      fallback frontier m

/-- The concrete replacement proof-length model also agrees with checker
`projectLength` when the theorem-5 family is stated in the rescaled Pudlak
literature code, not only in the internal `powerBoundRawCode` name. -/
theorem tailGapProofLengthCodeSemantics_length_at_rescaledPudlak_eq_projectLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (m : Nat) :
    (((tailGapProofLengthCodeSemantics fallback frontier).length
        (_root_.rescaledPudlakStrengthenedFiniteConsistencyCode
          scale_data.scale m) : Nat) : Real) =
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback m := by
  rw [← tailGapPowerBoundRawCode_eq_rescaledPudlak scale_data m]
  exact
    tailGapProofLengthCodeSemantics_length_eq_projectLengthMeasured
      fallback frontier m

/-- In the literature-code form, the concrete replacement proof-length model is
exactly the concrete right-conj-eliminated proof-family minimum checked code
size. -/
theorem tailGapProofLengthCodeSemantics_length_at_rescaledPudlak_eq_familyMinChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (m : Nat) :
    (((tailGapProofLengthCodeSemantics fallback frontier).length
        (_root_.rescaledPudlakStrengthenedFiniteConsistencyCode
          scale_data.scale m) : Nat) : Real) =
      (((frontier.left_family.conjIntro frontier.right_family)
        |>.rightConjElim
        |>.minCheckedCodeSize m : Nat) : Real) := by
  rw [← tailGapPowerBoundRawCode_eq_rescaledPudlak scale_data m]
  exact
    tailGapProofLengthCodeSemantics_length_eq_familyMinChecked
      fallback frontier m

/-- The theorem-5 family measured by the concrete replacement proof-length
model, not by the root `proof_length` axiom. -/
noncomputable def tailGapConcreteProofLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Nat → Real :=
  fun m =>
    ((tailGapProofLengthCodeSemantics fallback frontier).length
      (scale_data.powerBoundRawCode m) : Nat)

/-- The concrete proof-length measured function is definitionally the same
checker `projectLength` measurement on the theorem-5 raw-code family. -/
theorem tailGapConcreteProofLengthMeasured_eq_projectLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (m : Nat) :
    tailGapConcreteProofLengthMeasured fallback frontier m =
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback m := by
  simpa [tailGapConcreteProofLengthMeasured] using
    tailGapProofLengthCodeSemantics_length_eq_projectLengthMeasured
      fallback frontier m

/-- The concrete proof-length measured function is exactly the concrete
right-conj-eliminated proof-family minimum checked code size. -/
theorem tailGapConcreteProofLengthMeasured_eq_familyMinChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (m : Nat) :
    tailGapConcreteProofLengthMeasured fallback frontier m =
      (((frontier.left_family.conjIntro frontier.right_family)
        |>.rightConjElim
        |>.minCheckedCodeSize m : Nat) : Real) := by
  simpa [tailGapConcreteProofLengthMeasured] using
    tailGapProofLengthCodeSemantics_length_eq_familyMinChecked
      fallback frontier m

/-- The concrete theorem-5 measurement is independent of the fallback outside
the theorem-5 raw-code fragment.  Thus the computed collision route cannot be
tuned by changing fallback lengths. -/
theorem tailGapConcreteProofLengthMeasured_fallback_irrelevant
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback₁ fallback₂ : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (m : Nat) :
    tailGapConcreteProofLengthMeasured fallback₁ frontier m =
      tailGapConcreteProofLengthMeasured fallback₂ frontier m := by
  exact
    (tailGapConcreteProofLengthMeasured_eq_familyMinChecked
      fallback₁ frontier m).trans
      (tailGapConcreteProofLengthMeasured_eq_familyMinChecked
        fallback₂ frontier m).symm

/-- The old actual/root proof-length bridge is precisely the pointwise
statement that root `actualProofLengthMeasured` agrees with the concrete
proof-length model constructed from the PA/Hilbert checker.  This isolates the
remaining root `proof_length` residual as one exact equality. -/
theorem tailGapActualBridge_iff_actual_eq_concreteProofLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data
        (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)
      ↔
      (∀ m : Nat,
        actualProofLengthMeasured scale_data m =
          tailGapConcreteProofLengthMeasured fallback frontier m) := by
  constructor
  · intro bridge m
    have hproject_actual :
        checkerProjectLengthMeasured
            scale_data
            frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
            fallback m =
          actualProofLengthMeasured scale_data m :=
      (checkerProjectLengthMeasured_eq_checked
        (scale_data := scale_data)
        (checker :=
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics)
        fallback m).trans (bridge.checked_eq_actual m)
    have hconcrete_project :=
      tailGapConcreteProofLengthMeasured_eq_projectLengthMeasured
        fallback frontier m
    exact hproject_actual.symm.trans hconcrete_project.symm
  · intro h
    refine ⟨?_⟩
    intro m
    have hproject_checked :
        checkerProjectLengthMeasured
            scale_data
            frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
            fallback m =
          month9_month10_checkedProofCodeMeasured
            scale_data
            frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics
            m :=
      checkerProjectLengthMeasured_eq_checked
        (scale_data := scale_data)
        (checker :=
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics)
        fallback m
    have hconcrete_project :=
      tailGapConcreteProofLengthMeasured_eq_projectLengthMeasured
        fallback frontier m
    exact
      hproject_checked.symm.trans
        (hconcrete_project.symm.trans (h m).symm)

/-- Same residual as
`tailGapActualBridge_iff_actual_eq_concreteProofLengthMeasured`, unfolded to
the root `proof_length` symbol.  This is the exact statement whose unconditional
proof would make the old root-proof-length theorem-5 route close over the
concrete checker model. -/
theorem tailGapActualBridge_iff_rootProofLength_eq_concreteProofLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data
        (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)
      ↔
      (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          tailGapConcreteProofLengthMeasured fallback frontier m) := by
  simpa [actualProofLengthMeasured] using
    tailGapActualBridge_iff_actual_eq_concreteProofLengthMeasured
      fallback frontier

/-- Literature-code form of the same root exactness residual.  The remaining
old-root obligation is unchanged after replacing the internal
`powerBoundRawCode` name by the rescaled Pudlak theorem-5 code. -/
theorem tailGapActualBridge_iff_rootProofLength_at_rescaledPudlak_eq_concreteProofLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data
        (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)
      ↔
      (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (_root_.rescaledPudlakStrengthenedFiniteConsistencyCode
              scale_data.scale m) =
          tailGapConcreteProofLengthMeasured fallback frontier m) := by
  constructor
  · intro bridge m
    have hroot :=
      (tailGapActualBridge_iff_rootProofLength_eq_concreteProofLengthMeasured
        fallback frontier).1 bridge m
    rwa [tailGapPowerBoundRawCode_eq_rescaledPudlak scale_data m] at hroot
  · intro hroot
    refine
      (tailGapActualBridge_iff_rootProofLength_eq_concreteProofLengthMeasured
        fallback frontier).2 ?_
    intro m
    rw [tailGapPowerBoundRawCode_eq_rescaledPudlak scale_data m]
    exact hroot m

/-- Literature-rescaled-raw-code form of the same root exactness residual.
This matches the first code family exposed by the theorem-5 statement map. -/
theorem tailGapActualBridge_iff_rootProofLength_at_rescaledRawCode_eq_concreteProofLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data
        (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)
      ↔
      (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.rescaledRawCode m) =
          tailGapConcreteProofLengthMeasured fallback frontier m) := by
  constructor
  · intro bridge m
    have hroot :=
      (tailGapActualBridge_iff_rootProofLength_eq_concreteProofLengthMeasured
        fallback frontier).1 bridge m
    rwa [← (tailGapRawRescaledPowerCodeChain scale_data m).1] at hroot
  · intro hroot
    refine
      (tailGapActualBridge_iff_rootProofLength_eq_concreteProofLengthMeasured
        fallback frontier).2 ?_
    intro m
    rw [← (tailGapRawRescaledPowerCodeChain scale_data m).1]
    exact hroot m

/-- The root exactness residual is exactly the standard
`ProofLengthCodeSemantics.Calibration` of the concrete theorem-5 proof-length
model.  This is the minimal project-level convention still needed to turn the
concrete checker model into the old root `proof_length` model. -/
theorem tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    (tailGapProofLengthCodeSemantics fallback frontier).Calibration
      ↔
      (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          tailGapConcreteProofLengthMeasured fallback frontier m) := by
  constructor
  · intro hcal m
    simpa [tailGapConcreteProofLengthMeasured] using
      hcal.proof_length_eq_length
        (scale_data.powerBoundRawCode m) ⟨m, rfl⟩
  · intro hroot
    refine ⟨?_⟩
    intro code hcode
    rcases hcode with ⟨m, hcode_eq⟩
    subst hcode_eq
    simpa [tailGapConcreteProofLengthMeasured] using hroot m

/-- A calibrated concrete proof-length model gives the primitive root equality
against the lower-search `lengthCodeAt` family used by the singleton
PA/Hilbert checker. -/
theorem tailGapRootProofLength_eq_lowerSearchLengthCodeAt_of_calibration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hcal : (tailGapProofLengthCodeSemantics fallback frontier).Calibration)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode m) =
      (frontier.concreteLengthCodeFrontier.lower_search.lengthCodeAt m :
        Real) := by
  have hroot :
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode m) =
        tailGapConcreteProofLengthMeasured fallback frontier m :=
    (tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
      fallback frontier).1 hcal m
  have hconcrete :
      tailGapConcreteProofLengthMeasured fallback frontier m =
        (((frontier.left_family.conjIntro frontier.right_family)
          |>.rightConjElim
          |>.minCheckedCodeSize m : Nat) : Real) :=
    tailGapConcreteProofLengthMeasured_eq_familyMinChecked
      fallback frontier m
  have hlength :
      (((frontier.left_family.conjIntro frontier.right_family)
          |>.rightConjElim
          |>.minCheckedCodeSize m : Nat) : Real) =
        (frontier.concreteLengthCodeFrontier.lower_search.lengthCodeAt m :
          Real) := by
    exact_mod_cast
      (frontier.concreteLengthCodeFrontier.lengthCodeAt_eq_family_source
        m).symm
  exact hroot.trans (hconcrete.trans hlength)

/-- Transport the lower-search computable gap from the checked
`lengthCodeAt` family to the root `proof_length` family once the concrete
proof-length model has been calibrated. -/
def tailGapRootProofLengthGapOfCalibration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hcal : (tailGapProofLengthCodeSemantics fallback frontier).Calibration) :
    ComputableSearchGapCertificate
      (fun m : Nat =>
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode m)) where
  gap_for_polynomial_upper := by
    intro U hU
    let gap :=
      frontier.concreteLengthCodeFrontier.lower_search.gap
        |>.gap_for_polynomial_upper U hU
    exact
      { witness := gap.witness
        witness_ge := gap.witness_ge
        strict_at_witness := by
          intro N
          have hstrict := gap.strict_at_witness N
          have hroot :=
            tailGapRootProofLength_eq_lowerSearchLengthCodeAt_of_calibration
              fallback frontier hcal (gap.witness N)
          simpa [hroot] using hstrict }

/-- A calibrated concrete proof-length model closes exactly the input expected
by the final PA/Hilbert checker core.  The only root-level assumption consumed
here is the standard `ProofLengthCodeSemantics.Calibration` of the concrete
replacement model. -/
def tailGapFinalExactCheckerCoreInputOfCalibration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hcal : (tailGapProofLengthCodeSemantics fallback frontier).Calibration) :
    ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data where
  lengthCodeAt :=
    frontier.concreteLengthCodeFrontier.lower_search.lengthCodeAt
  timeConstructiblePower_strict := by
    intro a b hlt
    exact
      pow_lt_pow_left₀
        (frontier.time_bound_strict hlt)
        (Nat.zero_le (scale_data.time_constructible_bound a))
        frontier.exponent_ne_zero
  proof_length_gap :=
    tailGapRootProofLengthGapOfCalibration fallback frontier hcal
  proof_length_eq_lengthCodeAt :=
    tailGapRootProofLength_eq_lowerSearchLengthCodeAt_of_calibration
      fallback frontier hcal

/-- The final checker core generated from a calibrated concrete model recovers
root proof length as checker `projectLength` on every theorem-5 raw code. -/
theorem tailGapFinalExactCheckerCoreInputOfCalibration_rootProofLength_eq_projectLengthAt
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hcal : (tailGapProofLengthCodeSemantics fallback frontier).Calibration)
    (projectFallback : _root_.FormulaCode → Nat) (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode m) =
      _root_.ProofCodeSemantics.projectLength
        (InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data
            frontier.concreteLengthCodeFrontier.lower_search.lengthCodeAt))
        projectFallback (scale_data.powerBoundRawCode m) := by
  calc
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode m) =
      (frontier.concreteLengthCodeFrontier.lower_search.lengthCodeAt m :
        Real) :=
        tailGapRootProofLength_eq_lowerSearchLengthCodeAt_of_calibration
          fallback frontier hcal m
    _ =
      _root_.ProofCodeSemantics.projectLength
        (InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data
            frontier.concreteLengthCodeFrontier.lower_search.lengthCodeAt))
        projectFallback (scale_data.powerBoundRawCode m) := by
        symm
        exact
          concretePAHilbertPowerBoundCalibrated_projectLengthAt_eq_lengthCodeAt_of_injective
            scale_data
            frontier.concreteLengthCodeFrontier.lower_search.lengthCodeAt
            projectFallback m
            frontier.concreteLengthCodeFrontier.lower_search.powerBoundRawCode_injective

/-- Literature-code form of the standard calibration residual.  It says that
calibrating the concrete checker model against root `proof_length` is exactly
pointwise root equality on the rescaled Pudlak theorem-5 codes. -/
theorem tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_at_rescaledPudlak_eq_concreteProofLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    (tailGapProofLengthCodeSemantics fallback frontier).Calibration
      ↔
      (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (_root_.rescaledPudlakStrengthenedFiniteConsistencyCode
              scale_data.scale m) =
          tailGapConcreteProofLengthMeasured fallback frontier m) := by
  constructor
  · intro hcal m
    have hroot :=
      (tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
        fallback frontier).1 hcal m
    rwa [tailGapPowerBoundRawCode_eq_rescaledPudlak scale_data m] at hroot
  · intro hroot
    refine
      (tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
        fallback frontier).2 ?_
    intro m
    rw [tailGapPowerBoundRawCode_eq_rescaledPudlak scale_data m]
    exact hroot m

/-- Calibration form at the literature rescaled raw-code entry point.  This is
the root proof-length exactness obligation stated on the first theorem-5 code
family of the literature statement map. -/
theorem tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_at_rescaledRawCode_eq_concreteProofLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    (tailGapProofLengthCodeSemantics fallback frontier).Calibration
      ↔
      (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.rescaledRawCode m) =
          tailGapConcreteProofLengthMeasured fallback frontier m) := by
  constructor
  · intro hcal m
    have hroot :=
      (tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
        fallback frontier).1 hcal m
    rwa [← (tailGapRawRescaledPowerCodeChain scale_data m).1] at hroot
  · intro hroot
    refine
      (tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
        fallback frontier).2 ?_
    intro m
    rw [← (tailGapRawRescaledPowerCodeChain scale_data m).1]
    exact hroot m

/-- The old checked-to-actual bridge is equivalent to calibrating the concrete
theorem-5 proof-length model against root `proof_length`.  After the concrete
model route, this is the single remaining root-convention obligation. -/
theorem tailGapActualBridge_iff_concreteProofLengthCalibration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data
        (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)
      ↔
      (tailGapProofLengthCodeSemantics fallback frontier).Calibration :=
  (tailGapActualBridge_iff_rootProofLength_eq_concreteProofLengthMeasured
    fallback frontier).trans
    (tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
      fallback frontier).symm

/-- Project-proof-length-semantics form of the remaining root calibration.
This is definitionally the same obligation as
`ProofLengthCodeSemantics.Calibration`, but stated in the project-level
semantics interface used by the older proof-length bridge code. -/
theorem tailGapProjectProofLengthSemantics_iff_concreteProofLengthCalibration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
      ↔
      (tailGapProofLengthCodeSemantics fallback frontier).Calibration := by
  constructor
  · intro hsem
    exact ⟨hsem.proof_length_eq⟩
  · intro hcal
    exact hcal.toProjectProofLengthSemantics

/-- The old checked-to-actual bridge is also equivalent to the standard
`ProjectProofLengthSemantics` statement for the concrete theorem-5
proof-length model. -/
theorem tailGapActualBridge_iff_projectProofLengthSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data
        (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)
      ↔
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) :=
  (tailGapActualBridge_iff_concreteProofLengthCalibration
    fallback frontier).trans
    (tailGapProjectProofLengthSemantics_iff_concreteProofLengthCalibration
      fallback frontier).symm

/-- Project-level proof-length semantics gives the root exactness statement
against the concrete theorem-5 proof-length model. -/
theorem tailGapProjectProofLengthSemantics_rootProofLength_eq_concreteProofLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hsem :
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode m) =
      tailGapConcreteProofLengthMeasured fallback frontier m := by
  have hcal :
      (tailGapProofLengthCodeSemantics fallback frontier).Calibration :=
    (tailGapProjectProofLengthSemantics_iff_concreteProofLengthCalibration
      fallback frontier).1 hsem
  exact
    (tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
      fallback frontier).1 hcal m

/-- Project-level proof-length semantics is exactly pointwise equality between
root `proof_length` and the concrete checker `projectLength` measurement on the
theorem-5 raw-code family. -/
theorem tailGapProjectProofLengthSemantics_iff_rootProofLength_eq_projectLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
      ↔
      (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          checkerProjectLengthMeasured
            scale_data
            frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
            fallback m) := by
  constructor
  · intro hsem m
    exact
      (tailGapProjectProofLengthSemantics_rootProofLength_eq_concreteProofLengthMeasured
        fallback frontier hsem m).trans
        (tailGapConcreteProofLengthMeasured_eq_projectLengthMeasured
          fallback frontier m)
  · intro hroot
    refine
      (tailGapProjectProofLengthSemantics_iff_concreteProofLengthCalibration
        fallback frontier).2 ?_
    refine
      (tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
        fallback frontier).2 ?_
    intro m
    exact
      (hroot m).trans
        (tailGapConcreteProofLengthMeasured_eq_projectLengthMeasured
          fallback frontier m).symm

/-- Project-level proof-length semantics identifies root proof length with the
concrete right-conj-eliminated family minimum checked code size. -/
theorem tailGapProjectProofLengthSemantics_rootProofLength_eq_familyMinChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hsem :
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode m) =
      (((frontier.left_family.conjIntro frontier.right_family)
        |>.rightConjElim
        |>.minCheckedCodeSize m : Nat) : Real) := by
  exact
    (tailGapProjectProofLengthSemantics_rootProofLength_eq_concreteProofLengthMeasured
      fallback frontier hsem m).trans
      (tailGapConcreteProofLengthMeasured_eq_familyMinChecked
        fallback frontier m)

/-- Project-level proof-length semantics is also exactly pointwise equality
between root `proof_length` and the concrete right-conj-eliminated family
minimum checked code size. -/
theorem tailGapProjectProofLengthSemantics_iff_rootProofLength_eq_familyMinChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
      ↔
      (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (((frontier.left_family.conjIntro frontier.right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m : Nat) : Real)) := by
  constructor
  · intro hsem m
    exact
      tailGapProjectProofLengthSemantics_rootProofLength_eq_familyMinChecked
        fallback frontier hsem m
  · intro hroot
    refine
      (tailGapProjectProofLengthSemantics_iff_concreteProofLengthCalibration
        fallback frontier).2 ?_
    refine
      (tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
        fallback frontier).2 ?_
    intro m
    exact
      (hroot m).trans
        (tailGapConcreteProofLengthMeasured_eq_familyMinChecked
          fallback frontier m).symm

/-- Project-level proof-length semantics gives root exactness against the
concrete theorem-5 proof-length model in the literature-code statement form. -/
theorem tailGapProjectProofLengthSemantics_rootProofLength_at_rescaledPudlak_eq_concreteProofLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hsem :
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.rescaledPudlakStrengthenedFiniteConsistencyCode
          scale_data.scale m) =
      tailGapConcreteProofLengthMeasured fallback frontier m := by
  have hroot :=
    tailGapProjectProofLengthSemantics_rootProofLength_eq_concreteProofLengthMeasured
      fallback frontier hsem m
  rwa [tailGapPowerBoundRawCode_eq_rescaledPudlak scale_data m] at hroot

/-- Under project-level proof-length semantics, the root `proof_length` of the
rescaled Pudlak theorem-5 statement is exactly the concrete right-conj-eliminated
family minimum checked code size. -/
theorem tailGapProjectProofLengthSemantics_rootProofLength_at_rescaledPudlak_eq_familyMinChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hsem :
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.rescaledPudlakStrengthenedFiniteConsistencyCode
          scale_data.scale m) =
      (((frontier.left_family.conjIntro frontier.right_family)
        |>.rightConjElim
        |>.minCheckedCodeSize m : Nat) : Real) := by
  exact
    (tailGapProjectProofLengthSemantics_rootProofLength_at_rescaledPudlak_eq_concreteProofLengthMeasured
      fallback frontier hsem m).trans
      (tailGapConcreteProofLengthMeasured_eq_familyMinChecked
        fallback frontier m)

/-- Project-level proof-length semantics gives root exactness at the literature
rescaled raw-code entry point of theorem 5. -/
theorem tailGapProjectProofLengthSemantics_rootProofLength_at_rescaledRawCode_eq_concreteProofLengthMeasured
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hsem :
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.rescaledRawCode m) =
      tailGapConcreteProofLengthMeasured fallback frontier m := by
  have hroot :=
    tailGapProjectProofLengthSemantics_rootProofLength_eq_concreteProofLengthMeasured
      fallback frontier hsem m
  rwa [← (tailGapRawRescaledPowerCodeChain scale_data m).1] at hroot

/-- Under project-level proof-length semantics, the root `proof_length` of the
literature rescaled raw-code theorem-5 statement is exactly the concrete
right-conj-eliminated family minimum checked code size. -/
theorem tailGapProjectProofLengthSemantics_rootProofLength_at_rescaledRawCode_eq_familyMinChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hsem :
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.rescaledRawCode m) =
      (((frontier.left_family.conjIntro frontier.right_family)
        |>.rightConjElim
        |>.minCheckedCodeSize m : Nat) : Real) := by
  exact
    (tailGapProjectProofLengthSemantics_rootProofLength_at_rescaledRawCode_eq_concreteProofLengthMeasured
      fallback frontier hsem m).trans
      (tailGapConcreteProofLengthMeasured_eq_familyMinChecked
        fallback frontier m)

/-- The checker-native proof-length exactness certificate is exactly the same
root residual as calibrating the concrete theorem-5 proof-length model built in
this endpoint.  This collapses the old checker exactness input and the new
project-length calibration input to one obligation. -/
theorem tailGapCheckerProofLengthExactness_iff_concreteProofLengthCalibration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    InternalPudlakTheorem5CheckerProofLengthExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
      ↔
      (tailGapProofLengthCodeSemantics fallback frontier).Calibration := by
  constructor
  · intro exactness
    exact
      (tailGapActualBridge_iff_concreteProofLengthCalibration
        fallback frontier).1
        (Month9Month10CheckedMeasuredToActualProofLengthBridge.ofCheckerProofLengthExactness
          exactness)
  · intro hcal
    refine ⟨?_⟩
    intro code hcode
    let sem :=
      frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        |>.toProofCodeSemantics
    calc
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize code =
        ((tailGapProofLengthCodeSemantics fallback frontier).length code : Nat) :=
          hcal.proof_length_eq_length code hcode
      _ =
        (sem.minProofCodeSize code hcode : Real) := by
          change
            ((sem.semanticProofLength fallback code : Nat) : Real) =
              (sem.minProofCodeSize code hcode : Real)
          exact_mod_cast
            (sem.semanticProofLength_eq_minProofCodeSize fallback hcode)

/-- Checker-native proof-length exactness is also exactly the same as the
project-level `ProjectProofLengthSemantics` certificate for the concrete
theorem-5 model. -/
theorem tailGapCheckerProofLengthExactness_iff_projectProofLengthSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    InternalPudlakTheorem5CheckerProofLengthExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
      ↔
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) :=
  (tailGapCheckerProofLengthExactness_iff_concreteProofLengthCalibration
    fallback frontier).trans
    (tailGapProjectProofLengthSemantics_iff_concreteProofLengthCalibration
      fallback frontier).symm

/-- The family-shaped checker exactness certificate and the relevant-code
checker exactness certificate are equivalent on the theorem-5 fragment.  This
aligns the endpoint residual with the shape used by the hard-residual audit
file. -/
theorem tailGapCheckerProofLengthFamilyExactness_iff_checkerProofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
      ↔
      InternalPudlakTheorem5CheckerProofLengthExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics :=
  ⟨fun family => family.toCheckerProofLengthExactness,
    fun exactness =>
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness.ofCheckerProofLengthExactness
        exactness⟩

/-- Family-shaped checker proof-length exactness is the same residual as
calibrating the concrete theorem-5 proof-length model. -/
theorem tailGapCheckerProofLengthFamilyExactness_iff_concreteProofLengthCalibration
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
      ↔
      (tailGapProofLengthCodeSemantics fallback frontier).Calibration :=
  (tailGapCheckerProofLengthFamilyExactness_iff_checkerProofLengthExactness
    frontier).trans
    (tailGapCheckerProofLengthExactness_iff_concreteProofLengthCalibration
      fallback frontier)

/-- Family-shaped checker proof-length exactness is also the same residual as
the project-level proof-length semantics certificate for the concrete theorem-5
model. -/
theorem tailGapCheckerProofLengthFamilyExactness_iff_projectProofLengthSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
      ↔
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) :=
  (tailGapCheckerProofLengthFamilyExactness_iff_checkerProofLengthExactness
    frontier).trans
    (tailGapCheckerProofLengthExactness_iff_projectProofLengthSemantics
      fallback frontier)

/-- The old checked-to-actual bridge is not a separate residual from
checker-native proof-length exactness.  They are the same theorem-5 root
proof-length calibration obligation, stated in two different interfaces. -/
theorem tailGapActualBridge_iff_checkerProofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data
        (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)
      ↔
      InternalPudlakTheorem5CheckerProofLengthExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics :=
  (tailGapActualBridge_iff_concreteProofLengthCalibration
    fallback frontier).trans
    (tailGapCheckerProofLengthExactness_iff_concreteProofLengthCalibration
      fallback frontier).symm

/-- The old checked-to-actual bridge is also equivalent to the family-shaped
checker proof-length exactness statement used by the hard-residual file. -/
theorem tailGapActualBridge_iff_checkerProofLengthFamilyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data
        (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)
      ↔
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics :=
  (tailGapActualBridge_iff_checkerProofLengthExactness
    fallback frontier).trans
    (tailGapCheckerProofLengthFamilyExactness_iff_checkerProofLengthExactness
      frontier).symm

/-- Checker-native proof-length exactness identifies the root `proof_length` of
the literature rescaled raw-code theorem-5 statement with the concrete
right-conj-eliminated family minimum checked code size. -/
theorem tailGapCheckerProofLengthExactness_rootProofLength_at_rescaledRawCode_eq_familyMinChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.rescaledRawCode m) =
      (((frontier.left_family.conjIntro frontier.right_family)
        |>.rightConjElim
        |>.minCheckedCodeSize m : Nat) : Real) := by
  have hsem :
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) :=
    (tailGapCheckerProofLengthExactness_iff_projectProofLengthSemantics
      fallback frontier).1 exactness
  exact
    tailGapProjectProofLengthSemantics_rootProofLength_at_rescaledRawCode_eq_familyMinChecked
      fallback frontier hsem m

/-- Family-shaped checker proof-length exactness identifies the root
`proof_length` of the literature rescaled raw-code theorem-5 statement with the
concrete right-conj-eliminated family minimum checked code size. -/
theorem tailGapCheckerProofLengthFamilyExactness_rootProofLength_at_rescaledRawCode_eq_familyMinChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.rescaledRawCode m) =
      (((frontier.left_family.conjIntro frontier.right_family)
        |>.rightConjElim
        |>.minCheckedCodeSize m : Nat) : Real) :=
  tailGapCheckerProofLengthExactness_rootProofLength_at_rescaledRawCode_eq_familyMinChecked
    fallback frontier family.toCheckerProofLengthExactness m

/-- Project-level proof-length semantics directly rebuilds the old
checked-to-actual bridge. -/
theorem tailGapProjectProofLengthSemantics_to_actualBridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hsem :
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
      scale_data
      (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics) :=
  (tailGapActualBridge_iff_projectProofLengthSemantics
    fallback frontier).2 hsem

/-- Root calibration identifies the old project-level proof length with the
concrete proof-family minimum checked code size on every theorem-5 raw code. -/
theorem tailGapCalibration_rootProofLength_eq_familyMinChecked
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hcal :
      (tailGapProofLengthCodeSemantics fallback frontier).Calibration)
    (m : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode m) =
      (((frontier.left_family.conjIntro frontier.right_family)
        |>.rightConjElim
        |>.minCheckedCodeSize m : Nat) : Real) := by
  have hroot :
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode m) =
        tailGapConcreteProofLengthMeasured fallback frontier m :=
    (tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
      fallback frontier).1 hcal m
  exact
    hroot.trans
      (tailGapConcreteProofLengthMeasured_eq_familyMinChecked
        fallback frontier m)

/-- If two theorem-5 concrete models are both calibrated to the same root
`proof_length`, then they agree pointwise on the theorem-5 raw-code family.
This is the uniqueness pressure behind the final root exactness obligation. -/
theorem tailGapConcreteProofLengthMeasured_eq_of_calibrations
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback₁ fallback₂ : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier₁ frontier₂ :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hcal₁ :
      (tailGapProofLengthCodeSemantics fallback₁ frontier₁).Calibration)
    (hcal₂ :
      (tailGapProofLengthCodeSemantics fallback₂ frontier₂).Calibration)
    (m : Nat) :
    tailGapConcreteProofLengthMeasured fallback₁ frontier₁ m =
      tailGapConcreteProofLengthMeasured fallback₂ frontier₂ m := by
  have hroot₁ :
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode m) =
        tailGapConcreteProofLengthMeasured fallback₁ frontier₁ m :=
    (tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
      fallback₁ frontier₁).1 hcal₁ m
  have hroot₂ :
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode m) =
        tailGapConcreteProofLengthMeasured fallback₂ frontier₂ m :=
    (tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
      fallback₂ frontier₂).1 hcal₂ m
  exact hroot₁.symm.trans hroot₂

/-- The tail lower gap transported from the concrete checked target to the
checker `projectLength` measured object. -/
def projectLengthTailGapOfTimeBoundCanonicalTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (upper :
      PolynomialUpperTailCertificate
        (checkerProjectLengthMeasured
          scale_data frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
          fallback)) :
    TailStrictGapCertificate upper.U
      (checkerProjectLengthMeasured
        scale_data frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback) where
  threshold :=
    (frontier.tail_gap.gap_for_polynomial_upper
      upper.U upper.polynomial).threshold
  strict_after := by
    intro m hm
    have htail :=
      (frontier.tail_gap.gap_for_polynomial_upper
        upper.U upper.polynomial).strict_after m hm
    have hsource :
        month9_month10_checkedProofCodeMeasured
            scale_data
            frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics
            m =
          (frontier.concreteLengthCodeFrontier.lower_search.lengthCodeAt m :
            Real) := by
      have hcheckedTarget :
          month9_month10_checkedProofCodeMeasured
              scale_data
              frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics
              m =
            ((frontier.left_family.conjIntro frontier.right_family)
              |>.rightConjElim
              |>.minCheckedCodeSize m : Real) := by
        simpa [month9_month10_checkedProofCodeMeasured] using
          (show
            (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics.minProofCodeSize
                (scale_data.powerBoundRawCode m) ⟨m, rfl⟩ : Real) =
              ((frontier.left_family.conjIntro frontier.right_family)
                |>.rightConjElim
                |>.minCheckedCodeSize m : Real) from by
              exact_mod_cast
                frontier.concreteLengthCodeFrontier.projection
                  |>.theorem5_source_eq_family_source m)
      have hlengthTarget :
          (frontier.concreteLengthCodeFrontier.lower_search.lengthCodeAt m :
            Real) =
            ((frontier.left_family.conjIntro frontier.right_family)
              |>.rightConjElim
              |>.minCheckedCodeSize m : Real) := by
        exact_mod_cast
          frontier.concreteLengthCodeFrontier.lengthCodeAt_eq_family_source m
      exact hcheckedTarget.trans hlengthTarget.symm
    have hproject :
        checkerProjectLengthMeasured
            scale_data frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
            fallback m =
          (frontier.concreteLengthCodeFrontier.lower_search.lengthCodeAt m :
            Real) := by
      rw [checkerProjectLengthMeasured_eq_checked]
      exact hsource
    have hlengthTarget :
        (frontier.concreteLengthCodeFrontier.lower_search.lengthCodeAt m :
          Real) =
          ((frontier.left_family.conjIntro frontier.right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m : Real) := by
      exact_mod_cast
        frontier.concreteLengthCodeFrontier.lengthCodeAt_eq_family_source m
    have htargetProject :
        (((frontier.left_family.conjIntro frontier.right_family)
          |>.rightConjElim
          |>.minCheckedCodeSize m : Nat) : Real) =
          checkerProjectLengthMeasured
            scale_data frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
            fallback m :=
      hlengthTarget.symm.trans hproject.symm
    rw [htargetProject] at htail
    exact htail

/-- Explicit-upper raw theorem-5 big-`N` certificate for the clean
project-length tail-gap route.  This is the computable handoff shape: once an
explicit polynomial upper-tail certificate is supplied, the collision index is
the concrete `max upper.upperN gap.threshold`, with no rationality witness,
root `proof_length`, or payload predicate in the interface. -/
theorem projectLengthExplicitUpper_tailGapRawCodeBigNCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (upper :
      PolynomialUpperTailCertificate
        (checkerProjectLengthMeasured
          scale_data frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
          fallback)) :
    let measured :=
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback
    let gap :=
      projectLengthTailGapOfTimeBoundCanonicalTailGap
        fallback frontier upper
    let bigN := max upper.upperN gap.threshold
    PAHilbertAcceptedProofCodeForFormulaCode
      (concretePAHilbertPowerBoundChecker scale_data)
      (scale_data.powerBoundRawCode bigN)
      bigN ∧
      scale_data.powerBoundRawCode bigN =
        _root_.strengthenedPartialConsistencyCode
          (scale_data.scale bigN) ∧
        upper.U bigN < measured bigN ∧
          measured bigN ≤ upper.U bigN ∧
            False := by
  dsimp
  let measured :=
    checkerProjectLengthMeasured
      scale_data
      frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
      fallback
  let gap :=
    projectLengthTailGapOfTimeBoundCanonicalTailGap
      fallback frontier upper
  let bigN := max upper.upperN gap.threshold
  have haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode bigN)
        bigN :=
    concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
      scale_data bigN
  have hraw :
      scale_data.powerBoundRawCode bigN =
        _root_.strengthenedPartialConsistencyCode
          (scale_data.scale bigN) :=
    InternalPudlakTheorem5ScaleData.powerBoundRawCode_eq_scaled_strengthened
      scale_data bigN
  have hupperN : upper.upperN ≤ bigN := by
    exact Nat.le_max_left upper.upperN gap.threshold
  have hthreshold : gap.threshold ≤ bigN := by
    exact Nat.le_max_right upper.upperN gap.threshold
  have hlower : upper.U bigN < measured bigN := by
    exact gap.strict_after bigN hthreshold
  have hupper : measured bigN ≤ upper.U bigN := by
    exact upper.upper_after bigN hupperN
  exact
    ⟨haccepted,
      hraw,
      hlower,
      hupper,
      (not_lt_of_ge hupper) hlower⟩

/-- Checked-side explicit upper-tail version of
`projectLengthExplicitUpper_tailGapRawCodeBigNCertificate`.  This is the
intended numerical handoff: a concrete checked upper-tail certificate is
transported to checker `projectLength`, then the final theorem-5 raw-code
collision index is the explicit `max upper.upperN gap.threshold`. -/
theorem projectLengthCheckedUpper_tailGapRawCodeBigNCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (checked_upper :
      PolynomialUpperTailCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)) :
    let upper :=
      checkerProjectLengthUpperTailCertificateOfChecked
        (scale_data := scale_data)
        (checker := frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics)
        fallback checked_upper
    let measured :=
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback
    let gap :=
      projectLengthTailGapOfTimeBoundCanonicalTailGap
        fallback frontier upper
    let bigN := max upper.upperN gap.threshold
    PAHilbertAcceptedProofCodeForFormulaCode
      (concretePAHilbertPowerBoundChecker scale_data)
      (scale_data.powerBoundRawCode bigN)
      bigN ∧
      scale_data.powerBoundRawCode bigN =
        _root_.strengthenedPartialConsistencyCode
          (scale_data.scale bigN) ∧
        upper.U bigN < measured bigN ∧
          measured bigN ≤ upper.U bigN ∧
            False := by
  dsimp
  exact
    projectLengthExplicitUpper_tailGapRawCodeBigNCertificate
      fallback frontier
      (checkerProjectLengthUpperTailCertificateOfChecked
        (scale_data := scale_data)
        (checker := frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics)
        fallback checked_upper)

/-- Explicit-upper-provider raw theorem-5 big-`N` certificate.  This route
selects the upper certificate under rationality directly from a computable
provider, rather than extracting it from an existential upper-provider via
`Classical.choose`. -/
theorem projectLengthExplicitCheckedUpperProvider_tailGapRawCodeBigNCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (checked_upper_provider :
      ProjectLengthExplicitMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let checked_upper := checked_upper_provider.upperTailOfRationality hrat
    let upper :=
      checkerProjectLengthUpperTailCertificateOfChecked
        (scale_data := scale_data)
        (checker := frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics)
        fallback checked_upper
    let measured :=
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback
    let gap :=
      projectLengthTailGapOfTimeBoundCanonicalTailGap
        fallback frontier upper
    let bigN := max upper.upperN gap.threshold
    PAHilbertAcceptedProofCodeForFormulaCode
      (concretePAHilbertPowerBoundChecker scale_data)
      (scale_data.powerBoundRawCode bigN)
      bigN ∧
      scale_data.powerBoundRawCode bigN =
        _root_.strengthenedPartialConsistencyCode
          (scale_data.scale bigN) ∧
        upper.U bigN < measured bigN ∧
          measured bigN ≤ upper.U bigN ∧
            False := by
  dsimp
  exact
    projectLengthCheckedUpper_tailGapRawCodeBigNCertificate
      fallback frontier
      (checked_upper_provider.upperTailOfRationality hrat)

/-- Public no-choose closure for the explicit checked upper-provider route.
The contradiction still starts from rationality, but the upper side is now an
explicit certificate selected by the provider, not a `Classical.choose`d witness
from an existential upper statement. -/
theorem projectLengthExplicitCheckedUpperProvider_tailGapRawCode_not_rational
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (checked_upper_provider :
      ProjectLengthExplicitMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  intro hrat
  have hcert :=
    projectLengthExplicitCheckedUpperProvider_tailGapRawCodeBigNCertificate
      fallback frontier checked_upper_provider hrat
  exact hcert.2.2.2.2

/-- Fallback-free singleton-tail-gap entry for the explicit upper-provider raw
theorem-5 big-`N` certificate.  This is the high-level handoff shape: the
frontier is generated from the concrete time-bound tail input, while the upper
side is supplied as an explicit certificate provider rather than an existential
upper route. -/
theorem projectLengthExplicitCheckedUpperProvider_tailGapRawCodeBigNCertificate_of_singletonTailGap_noFallback
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
    (tail_input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
    (lengthCodeAt_eq_conj_source :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m))
    (left_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real left_family.length))
    (right_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (checked_upper_provider :
      let frontier :=
        timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
          left_family right_family time_bound_strict exponent_ne_zero
          tail_input lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      ProjectLengthExplicitMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let fallback : _root_.FormulaCode → Nat := fun _ => 0
    let frontier :=
      timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero
        tail_input lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial
    let checked_upper := checked_upper_provider.upperTailOfRationality hrat
    let upper :=
      checkerProjectLengthUpperTailCertificateOfChecked
        (scale_data := scale_data)
        (checker := frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics)
        fallback checked_upper
    let measured :=
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback
    let gap :=
      projectLengthTailGapOfTimeBoundCanonicalTailGap
        fallback frontier upper
    let bigN := max upper.upperN gap.threshold
    PAHilbertAcceptedProofCodeForFormulaCode
      (concretePAHilbertPowerBoundChecker scale_data)
      (scale_data.powerBoundRawCode bigN)
      bigN ∧
      scale_data.powerBoundRawCode bigN =
        _root_.strengthenedPartialConsistencyCode
          (scale_data.scale bigN) ∧
        upper.U bigN < measured bigN ∧
          measured bigN ≤ upper.U bigN ∧
            False := by
  dsimp
  let fallback : _root_.FormulaCode → Nat := fun _ => 0
  let frontier :=
    timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
      left_family right_family time_bound_strict exponent_ne_zero
      tail_input lengthCodeAt_eq_conj_source
      left_length_polynomial right_length_polynomial
  simpa [fallback, frontier] using
    projectLengthExplicitCheckedUpperProvider_tailGapRawCodeBigNCertificate
      fallback frontier checked_upper_provider hrat

/-- Fallback-free singleton-tail-gap public closure for the explicit upper
provider route.  The contradiction still uses rationality as the assumed
source of the upper side, but the upper side itself is now an explicit
certificate provider and the endpoint has no exposed fallback. -/
theorem projectLengthExplicitCheckedUpperProvider_tailGapRawCode_not_rational_of_singletonTailGap_noFallback
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
    (tail_input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
    (lengthCodeAt_eq_conj_source :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m))
    (left_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real left_family.length))
    (right_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (checked_upper_provider :
      let frontier :=
        timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
          left_family right_family time_bound_strict exponent_ne_zero
          tail_input lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      ProjectLengthExplicitMeasuredUpperProvider
        (month9_month10_checkedProofCodeMeasured
          scale_data
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  intro hrat
  have hcert :=
    projectLengthExplicitCheckedUpperProvider_tailGapRawCodeBigNCertificate_of_singletonTailGap_noFallback
      left_family right_family time_bound_strict exponent_ne_zero tail_input
      lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial checked_upper_provider hrat
  exact hcert.2.2.2.2

/-- Explicit project-length collision witness for the time-bound canonical
tail-gap frontier.  Its index is definitionally `max upperN gapThreshold`, so
this is the auditable computed `n` path independent of endpoint choice. -/
noncomputable def projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedCollisionWitness
      (projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat).U
      (checkerProjectLengthMeasured
        scale_data frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback) :=
  (projectLengthUpperTailOfTimeBoundCanonicalTailGap
    fallback frontier hrat).computedWitness
    (projectLengthTailGapOfTimeBoundCanonicalTailGap
      fallback frontier
      (projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat))

theorem projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap
      fallback frontier hrat).n =
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
            hrat).polynomial).threshold := by
  rfl

/-- The explicit project-length tail-gap witness computes the same index as the
proof-length-free checked provider.  This pins the clean route's large `N` to
one auditable formula, `max upperN threshold`. -/
theorem projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap_n_eq_providerComputedN
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap
      fallback frontier hrat).n =
      frontier.computedCollisionNOfRationality hrat := by
  calc
    (projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap
      fallback frontier hrat).n =
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
              hrat).polynomial).threshold :=
          projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap_n_eq
            fallback frontier hrat
    _ = frontier.computedCollisionNOfRationality hrat :=
          (frontier.computedCollisionN_eq_tailGapMax hrat).symm

/-- At the same proof-length-free provider-computed large `N`, the explicit
project-length tail-gap route gives both sides of the collision inequality.
This is the clean contradiction trace for the auditable `max upperN threshold`
number, without root `proof_length` or payload assumptions. -/
theorem projectLengthProviderComputedN_tailGapContradictionTrace
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    let computedN := frontier.computedCollisionNOfRationality hrat
    upper.U computedN <
        checkerProjectLengthMeasured
          scale_data
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
          fallback computedN ∧
      checkerProjectLengthMeasured
          scale_data
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
          fallback computedN ≤
        upper.U computedN ∧
      False := by
  dsimp
  let w :=
    projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap
      fallback frontier hrat
  have hn :
      w.n = frontier.computedCollisionNOfRationality hrat :=
    projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap_n_eq_providerComputedN
      fallback frontier hrat
  have hlower :
      (projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat).U
          (frontier.computedCollisionNOfRationality hrat) <
        checkerProjectLengthMeasured
          scale_data
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
          fallback
          (frontier.computedCollisionNOfRationality hrat) := by
    simpa [w, hn] using w.lower_at_n
  have hupper :
      checkerProjectLengthMeasured
          scale_data
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
          fallback
          (frontier.computedCollisionNOfRationality hrat) ≤
        (projectLengthUpperTailOfTimeBoundCanonicalTailGap
          fallback frontier hrat).U
          (frontier.computedCollisionNOfRationality hrat) := by
    simpa [w, hn] using w.upper_at_n
  exact ⟨hlower, hupper, (not_lt_of_ge hupper) hlower⟩

/-- Big-`N` certificate for the clean project-length tail-gap route.  The
provider-computed collision index is the explicit `max upperN threshold`,
dominates both thresholds, and is the exact point where the project-length
upper and lower bounds collide. -/
theorem projectLengthProviderComputedN_tailGapBigNCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    let measured :=
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < measured bigN ∧
            measured bigN ≤ upper.U bigN ∧
              False := by
  dsimp
  let checkedTail :=
    checkedSearchUpperTail
      frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
      frontier.concreteLengthCodeFrontier.checkedUpperProvider
      hrat
  let bigN :=
    max checkedTail.upperN
      (frontier.tail_gap.gap_for_polynomial_upper
        checkedTail.U checkedTail.polynomial).threshold
  have hcomputed :
      frontier.computedCollisionNOfRationality hrat = bigN := by
    simpa [bigN, checkedTail] using
      frontier.computedCollisionN_eq_tailGapMax hrat
  have htrace :=
    projectLengthProviderComputedN_tailGapContradictionTrace
      fallback frontier hrat
  rcases htrace with ⟨hlower, hupper, hfalse⟩
  exact
    ⟨hcomputed,
      by
        exact Nat.le_max_left checkedTail.upperN
          (frontier.tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold,
      by
        exact Nat.le_max_right checkedTail.upperN
          (frontier.tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold,
      by
        simpa [bigN, hcomputed] using hlower,
      by
        simpa [bigN, hcomputed] using hupper,
      hfalse⟩

/-- Witness-strengthened big-`N` certificate for the clean project-length
tail-gap route.  The provider-computed collision index is simultaneously the
lower-search rejection-extractor witness and the explicit `max upperN
threshold` number, and it is the exact point where the project-length upper and
lower bounds collide. -/
theorem projectLengthProviderComputedN_tailGapWitnessBigNCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    let measured :=
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback
    frontier.computedCollisionNOfRationality hrat =
        frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN ∧
      frontier.computedCollisionNOfRationality hrat = bigN ∧
        checkedTail.upperN ≤ bigN ∧
          (frontier.tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
            upper.U bigN < measured bigN ∧
              measured bigN ≤ upper.U bigN ∧
                False := by
  dsimp
  let checkedTail :=
    checkedSearchUpperTail
      frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
      frontier.concreteLengthCodeFrontier.checkedUpperProvider
      hrat
  have hwitness :
      frontier.computedCollisionNOfRationality hrat =
        frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN := by
    simpa [checkedTail] using
      tailGapComputedN_eq_rejectionExtractorWitness frontier hrat
  have hbig :=
    projectLengthProviderComputedN_tailGapBigNCertificate
      fallback frontier hrat
  rcases hbig with
    ⟨hcomputed, hupperN, hthreshold, hlower, hupper, hfalse⟩
  exact
    ⟨hwitness,
      hcomputed,
      hupperN,
      hthreshold,
      hlower,
      hupper,
      hfalse⟩

/-- Diagnostic two-family payload-data big-`N` certificate for the clean
project-length tail-gap route.  It shows how a supplied ordinary-plus-
strengthened checker-acceptance package would be carried at the same computed
`bigN` without mentioning the root `accepted_certificate` predicate.  The
compatible final theorem-5 shape is the strengthened-only certificate below:
the ordinary branch is incompatible with the concrete theorem-5 semantics once
accepted-code exactness is imposed. -/
theorem projectLengthProviderComputedN_tailGapPayloadCodeBigNCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance)
    (checker_eq :
      checker_acceptance.checker =
        concretePAHilbertPowerBoundChecker scale_data)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    let measured :=
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback
    frontier.computedCollisionNOfRationality hrat =
        frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN ∧
      frontier.computedCollisionNOfRationality hrat = bigN ∧
        checkedTail.upperN ≤ bigN ∧
          (frontier.tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
            PAHilbertAcceptedProofCodeForFormulaCode
              (concretePAHilbertPowerBoundChecker scale_data)
              (_root_.partialConsistencyCode bigN)
              (checker_acceptance.ordinary.proofCode bigN) ∧
              PAHilbertAcceptedProofCodeForFormulaCode
                (concretePAHilbertPowerBoundChecker scale_data)
                (_root_.strengthenedPartialConsistencyCode bigN)
                (checker_acceptance.strengthened.proofCode bigN) ∧
                upper.U bigN < measured bigN ∧
                  measured bigN ≤ upper.U bigN ∧
                    False := by
  dsimp
  let checkedTail :=
    checkedSearchUpperTail
      frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
      frontier.concreteLengthCodeFrontier.checkedUpperProvider
      hrat
  let bigN :=
    max checkedTail.upperN
      (frontier.tail_gap.gap_for_polynomial_upper
        checkedTail.U checkedTail.polynomial).threshold
  have hordinary :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (_root_.partialConsistencyCode bigN)
        (checker_acceptance.ordinary.proofCode bigN) := by
    simpa [checker_eq] using checker_acceptance.ordinary.acceptedCode bigN
  have hstrengthened :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (_root_.strengthenedPartialConsistencyCode bigN)
        (checker_acceptance.strengthened.proofCode bigN) := by
    simpa [checker_eq] using checker_acceptance.strengthened.acceptedCode bigN
  have hbig :=
    projectLengthProviderComputedN_tailGapWitnessBigNCertificate
      fallback frontier hrat
  rcases hbig with
    ⟨hwitness, hcomputed, hupperN, hthreshold, hlower, hupper, hfalse⟩
  exact
    ⟨hwitness,
      hcomputed,
      hupperN,
      hthreshold,
      hordinary,
      hstrengthened,
      hlower,
      hupper,
      hfalse⟩

/-- Strengthened-only payload-code big-`N` certificate for the clean
project-length tail-gap route.  This is the compatible final theorem-5 shape:
the computed `bigN` carries checker-accepted proof-code evidence for the
strengthened finite-consistency target without mentioning the root
`accepted_certificate` or the ordinary payload branch. -/
theorem projectLengthProviderComputedN_tailGapStrengthenedPayloadCodeBigNCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (strengthened_acceptance :
      Month9Month10PayloadFreeCheckerAcceptedFamily
        (concretePAHilbertPowerBoundChecker scale_data)
        _root_.strengthenedPartialConsistencyCode)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    let measured :=
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback
    frontier.computedCollisionNOfRationality hrat =
        frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN ∧
      frontier.computedCollisionNOfRationality hrat = bigN ∧
        checkedTail.upperN ≤ bigN ∧
          (frontier.tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
            PAHilbertAcceptedProofCodeForFormulaCode
              (concretePAHilbertPowerBoundChecker scale_data)
              (_root_.strengthenedPartialConsistencyCode bigN)
              (strengthened_acceptance.proofCode bigN) ∧
              upper.U bigN < measured bigN ∧
                measured bigN ≤ upper.U bigN ∧
                  False := by
  dsimp
  let checkedTail :=
    checkedSearchUpperTail
      frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
      frontier.concreteLengthCodeFrontier.checkedUpperProvider
      hrat
  let bigN :=
    max checkedTail.upperN
      (frontier.tail_gap.gap_for_polynomial_upper
        checkedTail.U checkedTail.polynomial).threshold
  have hstrengthened :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (_root_.strengthenedPartialConsistencyCode bigN)
        (strengthened_acceptance.proofCode bigN) :=
    strengthened_acceptance.acceptedCode bigN
  have hbig :=
    projectLengthProviderComputedN_tailGapWitnessBigNCertificate
      fallback frontier hrat
  rcases hbig with
    ⟨hwitness, hcomputed, hupperN, hthreshold, hlower, hupper, hfalse⟩
  exact
    ⟨hwitness,
      hcomputed,
      hupperN,
      hthreshold,
      hstrengthened,
      hlower,
      hupper,
      hfalse⟩

/-- Raw theorem-5 payload-code big-`N` certificate for the clean
project-length tail-gap route.  This removes the strengthened-acceptance input
entirely: at the computed `bigN`, the concrete PA/Hilbert power-bound checker
accepts proof code `bigN` for the actual theorem-5 raw code
`scale_data.powerBoundRawCode bigN`.  This is the calibrated final shape; the
same raw code is the strengthened finite-consistency target at
`scale_data.scale bigN`. -/
theorem projectLengthProviderComputedN_tailGapRawPayloadCodeBigNCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    let measured :=
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback
    frontier.computedCollisionNOfRationality hrat =
        frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN ∧
      frontier.computedCollisionNOfRationality hrat = bigN ∧
        checkedTail.upperN ≤ bigN ∧
          (frontier.tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
            PAHilbertAcceptedProofCodeForFormulaCode
              (concretePAHilbertPowerBoundChecker scale_data)
              (scale_data.powerBoundRawCode bigN)
              bigN ∧
              scale_data.powerBoundRawCode bigN =
                _root_.strengthenedPartialConsistencyCode
                  (scale_data.scale bigN) ∧
                upper.U bigN < measured bigN ∧
                  measured bigN ≤ upper.U bigN ∧
                    False := by
  dsimp
  let checkedTail :=
    checkedSearchUpperTail
      frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
      frontier.concreteLengthCodeFrontier.checkedUpperProvider
      hrat
  let bigN :=
    max checkedTail.upperN
      (frontier.tail_gap.gap_for_polynomial_upper
        checkedTail.U checkedTail.polynomial).threshold
  have haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode bigN)
        bigN :=
    concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
      scale_data bigN
  have hraw :
      scale_data.powerBoundRawCode bigN =
        _root_.strengthenedPartialConsistencyCode
          (scale_data.scale bigN) :=
    InternalPudlakTheorem5ScaleData.powerBoundRawCode_eq_scaled_strengthened
      scale_data bigN
  have hbig :=
    projectLengthProviderComputedN_tailGapWitnessBigNCertificate
      fallback frontier hrat
  rcases hbig with
    ⟨hwitness, hcomputed, hupperN, hthreshold, hlower, hupper, hfalse⟩
  exact
    ⟨hwitness,
      hcomputed,
      hupperN,
      hthreshold,
      haccepted,
      hraw,
      hlower,
      hupper,
      hfalse⟩

/-- Public closure for the raw theorem-5 payload-code big-`N` route.  This is
the current clean final statement shape: audits for the proof-length-free
provider and endpoint, the raw-code checker certificate at every rationality
witness, the contradiction under rationality, and the final non-rationality
conclusion. -/
theorem projectLengthProviderComputedN_tailGapRawPayloadCode_publicMainClosure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    frontier.provider.Audit ∧
      frontier.endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          let checkedTail :=
            checkedSearchUpperTail
              frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
              frontier.concreteLengthCodeFrontier.checkedUpperProvider
              hrat
          let bigN :=
            max checkedTail.upperN
              (frontier.tail_gap.gap_for_polynomial_upper
                checkedTail.U checkedTail.polynomial).threshold
          let upper :=
            projectLengthUpperTailOfTimeBoundCanonicalTailGap
              fallback frontier hrat
          let measured :=
            checkerProjectLengthMeasured
              scale_data
              frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
              fallback
          frontier.computedCollisionNOfRationality hrat =
              frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
                checkedTail.U checkedTail.polynomial checkedTail.upperN ∧
            frontier.computedCollisionNOfRationality hrat = bigN ∧
              checkedTail.upperN ≤ bigN ∧
                (frontier.tail_gap.gap_for_polynomial_upper
                  checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
                  PAHilbertAcceptedProofCodeForFormulaCode
                    (concretePAHilbertPowerBoundChecker scale_data)
                    (scale_data.powerBoundRawCode bigN)
                    bigN ∧
                    scale_data.powerBoundRawCode bigN =
                      _root_.strengthenedPartialConsistencyCode
                        (scale_data.scale bigN) ∧
                      upper.U bigN < measured bigN ∧
                        measured bigN ≤ upper.U bigN ∧
                          False) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
            ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure := frontier.closure
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      fun hrat =>
        projectLengthProviderComputedN_tailGapRawPayloadCodeBigNCertificate
          fallback frontier hrat,
      hclosure.2.2.1,
      hclosure.2.2.2⟩

/-- At the same provider-computed big `N`, the concrete replacement
proof-length model produces the tail-gap collision without using root
`proof_length`. -/
theorem tailGapConcreteProofLengthModel_bigNCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    let measured :=
      tailGapConcreteProofLengthMeasured fallback frontier
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < measured bigN ∧
            measured bigN ≤ upper.U bigN ∧
              False := by
  dsimp
  let checkedTail :=
    checkedSearchUpperTail
      frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
      frontier.concreteLengthCodeFrontier.checkedUpperProvider
      hrat
  let bigN :=
    max checkedTail.upperN
      (frontier.tail_gap.gap_for_polynomial_upper
        checkedTail.U checkedTail.polynomial).threshold
  have hproject :=
    projectLengthProviderComputedN_tailGapBigNCertificate
      fallback frontier hrat
  rcases hproject with
    ⟨hcomputed, hupperN, hthreshold, hlower, hupper, hfalse⟩
  have hmeasured :
      tailGapConcreteProofLengthMeasured fallback frontier bigN =
        checkerProjectLengthMeasured
          scale_data
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
          fallback bigN :=
    tailGapProofLengthCodeSemantics_length_eq_projectLengthMeasured
      fallback frontier bigN
  have hlowerModel :
      (projectLengthUpperTailOfTimeBoundCanonicalTailGap fallback frontier hrat).U
          bigN <
        tailGapConcreteProofLengthMeasured fallback frontier bigN := by
    rw [hmeasured]
    exact hlower
  have hupperModel :
      tailGapConcreteProofLengthMeasured fallback frontier bigN ≤
        (projectLengthUpperTailOfTimeBoundCanonicalTailGap fallback frontier hrat).U
          bigN := by
    rw [hmeasured]
    exact hupper
  exact
    ⟨hcomputed,
      hupperN,
      hthreshold,
      by
        simpa using hlowerModel,
      by
        simpa using hupperModel,
      hfalse⟩

/-- The concrete replacement proof-length model gives the contradiction at
the provider-computed big `N`, without using root `proof_length`. -/
theorem tailGapConcreteProofLengthModel_contradiction
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False := by
  have hcert :=
    tailGapConcreteProofLengthModel_bigNCertificate
      fallback frontier hrat
  dsimp at hcert
  rcases hcert with ⟨_, _, _, _, _, hfalse⟩
  exact hfalse

/-- Closed theorem-5 tail-gap conclusion over the concrete replacement
proof-length model.  This is the proof-length-axiom-free version of the final
collision route. -/
theorem tailGapConcreteProofLengthModel_not_rational
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat =>
    tailGapConcreteProofLengthModel_contradiction
      fallback frontier hrat

/-- End-to-end contradiction from the smaller singleton tail-gap input.  This
uses the frontier-instantiation adapter above and then runs the closed concrete
proof-length-model route, still without root `proof_length`. -/
theorem tailGapConcreteProofLengthModel_contradiction_of_singletonTailGapInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
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
    (tail_input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
    (lengthCodeAt_eq_conj_source :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m))
    (left_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real left_family.length))
    (right_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  tailGapConcreteProofLengthModel_contradiction
    fallback
    (timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
      left_family right_family time_bound_strict exponent_ne_zero tail_input
      lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial)
    hrat

/-- Big-`N` certificate from the smaller singleton tail-gap input.  This keeps
the computable collision witness visible after frontier instantiation: the
provider-computed index is the explicit `max upperN threshold` number, and the
same index carries the concrete proof-length-model collision. -/
theorem tailGapConcreteProofLengthModel_bigNCertificate_of_singletonTailGapInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
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
    (tail_input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
    (lengthCodeAt_eq_conj_source :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m))
    (left_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real left_family.length))
    (right_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let frontier :=
      timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero tail_input
        lengthCodeAt_eq_conj_source left_length_polynomial
        right_length_polynomial
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    let measured :=
      tailGapConcreteProofLengthMeasured fallback frontier
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < measured bigN ∧
            measured bigN ≤ upper.U bigN ∧
              False := by
  dsimp
  exact
    tailGapConcreteProofLengthModel_bigNCertificate
      fallback
      (timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero tail_input
        lengthCodeAt_eq_conj_source left_length_polynomial
        right_length_polynomial)
      hrat

/-- Singleton-input big-`N` certificate with the threshold stated directly at
the original tail-gap input.  This removes the last bookkeeping ambiguity in
the computable witness formula introduced by the frontier adapter. -/
theorem tailGapConcreteProofLengthModel_bigNCertificate_of_singletonTailGapInput_tailInputThreshold
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
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
    (tail_input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
    (lengthCodeAt_eq_conj_source :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m))
    (left_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real left_family.length))
    (right_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let frontier :=
      timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero tail_input
        lengthCodeAt_eq_conj_source left_length_polynomial
        right_length_polynomial
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (tail_input.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    let measured :=
      tailGapConcreteProofLengthMeasured fallback frontier
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (tail_input.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < measured bigN ∧
            measured bigN ≤ upper.U bigN ∧
              False := by
  simpa [singletonTailGapFrontier_tailGap_threshold_eq] using
    tailGapConcreteProofLengthModel_bigNCertificate_of_singletonTailGapInput
      fallback left_family right_family time_bound_strict exponent_ne_zero
      tail_input lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial hrat

/-- Closed proof-length-axiom-free theorem-5 tail-gap conclusion from the
smaller singleton tail-gap input.  This is the direct endpoint after the
frontier-instantiation adapter has supplied the canonical tail-gap frontier. -/
theorem tailGapConcreteProofLengthModel_not_rational_of_singletonTailGapInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
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
    (tail_input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
    (lengthCodeAt_eq_conj_source :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
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
  fun hrat =>
    tailGapConcreteProofLengthModel_contradiction_of_singletonTailGapInput
      fallback left_family right_family time_bound_strict exponent_ne_zero
      tail_input lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial hrat

/-- Build the singleton tail-gap input directly from theorem-5 time-bound
strictness.  This is the primitive surface used by the hard-residual file:
scale strictness is derived, not supplied as an independent field. -/
def projectLengthSingletonTailGapInputOfTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real))) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data where
  lengthCodeAt := lengthCodeAt
  scale_strict :=
    SondowMainCheckedCodeBridge.SondowProjectMonth9Month10ProofLengthGapFrontier.Month9Month10ActualProofLengthGapFrontier.scale_strict_of_timeConstructibleBound_strict
      time_bound_strict exponent_ne_zero
  tail_gap := tail_gap

/-- Primitive time-bound constructor for the canonical tail-gap frontier used by
the project-length endpoint.  It keeps the public input surface at theorem-5
time-bound strictness plus a concrete checked-length tail-gap, while deriving
the strict-scale singleton input internally. -/
def projectLengthTimeBoundTailGapFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
    Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
      scale_data (Ax := Ax) (A := A) (B := B) :=
  timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
    left_family right_family time_bound_strict exponent_ne_zero
    (projectLengthSingletonTailGapInputOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap)
    (by
      intro m
      simpa [projectLengthSingletonTailGapInputOfTimeBound] using
        lengthCodeAt_eq_conj_source m)
    left_length_polynomial right_length_polynomial

/-- On the primitive time-bound tail-gap surface, the old checked-to-actual
bridge is exactly the family-shaped checker proof-length exactness residual. -/
theorem tailGapActualBridge_iff_checkerProofLengthFamilyExactness_of_timeBoundTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
    let frontier :=
      projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial
    Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data
        (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)
      ↔
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics := by
  dsimp
  exact
    tailGapActualBridge_iff_checkerProofLengthFamilyExactness
      fallback
      (projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial)

/-- On the same primitive surface, the family exactness residual is also exactly
the project-level proof-length semantics calibration for the concrete checker
model. -/
theorem tailGapCheckerProofLengthFamilyExactness_iff_projectProofLengthSemantics_of_timeBoundTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
    let frontier :=
      projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
      ↔
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) := by
  dsimp
  exact
    tailGapCheckerProofLengthFamilyExactness_iff_projectProofLengthSemantics
      fallback
      (projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial)

/-- Direct primitive-surface residual theorem: the old checked-to-actual bridge
and the concrete project-level proof-length semantics certificate are the same
obligation after the time-bound tail-gap frontier has been built. -/
theorem tailGapActualBridge_iff_projectProofLengthSemantics_of_timeBoundTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
    let frontier :=
      projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial
    Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data
        (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics)
      ↔
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) := by
  dsimp
  exact
    tailGapActualBridge_iff_projectProofLengthSemantics
      fallback
      (projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial)

/-- Primitive-surface exactness target in checker-project-length form.  This is
the remaining old-root proof-length obligation stated exactly as pointwise
equality between root `proof_length` and the concrete checker `projectLength`
measurement on theorem-5 raw codes. -/
theorem tailGapProjectProofLengthSemantics_iff_rootProofLength_eq_projectLengthMeasured_of_timeBoundTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
    let frontier :=
      projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
      ↔
      (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          checkerProjectLengthMeasured
            scale_data
            frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
            fallback m) := by
  dsimp
  exact
    tailGapProjectProofLengthSemantics_iff_rootProofLength_eq_projectLengthMeasured
      fallback
      (projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial)

/-- Primitive-surface exactness target in proof-family form.  This is the same
remaining old-root obligation, but written as pointwise equality between root
`proof_length` and the right-conj-eliminated family `minCheckedCodeSize`. -/
theorem tailGapProjectProofLengthSemantics_iff_rootProofLength_eq_familyMinChecked_of_timeBoundTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
    let frontier :=
      projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial
    _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
      ↔
      (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (((frontier.left_family.conjIntro frontier.right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m : Nat) : Real)) := by
  dsimp
  exact
    tailGapProjectProofLengthSemantics_iff_rootProofLength_eq_familyMinChecked
      fallback
      (projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial)

/-- Primitive time-bound form of the concrete proof-length-model theorem-5
tail-gap endpoint.  It closes the route over checker-defined project length
without mentioning root `proof_length`, while deriving the strict-scale input
from the theorem-5 time-bound data. -/
theorem tailGapConcreteProofLengthModel_not_rational_of_timeBoundTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
  tailGapConcreteProofLengthModel_not_rational_of_singletonTailGapInput
    fallback left_family right_family time_bound_strict exponent_ne_zero
    (projectLengthSingletonTailGapInputOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap)
    (by
      intro m
      simpa [projectLengthSingletonTailGapInputOfTimeBound] using
        lengthCodeAt_eq_conj_source m)
    left_length_polynomial right_length_polynomial

/-- Primitive time-bound big-`N` certificate for the concrete proof-length-model
tail-gap endpoint.  The computed collision index remains the explicit
`max upperN threshold` from the supplied tail-gap certificate. -/
theorem tailGapConcreteProofLengthModel_bigNCertificate_of_timeBoundTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let tail_input :=
      projectLengthSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
    let frontier :=
      timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero
        tail_input
        (by
          intro m
          simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
            lengthCodeAt_eq_conj_source m)
        left_length_polynomial right_length_polynomial
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    let measured :=
      tailGapConcreteProofLengthMeasured fallback frontier
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < measured bigN ∧
            measured bigN ≤ upper.U bigN ∧
              False := by
  dsimp
  simpa [projectLengthSingletonTailGapInputOfTimeBound] using
    tailGapConcreteProofLengthModel_bigNCertificate_of_singletonTailGapInput_tailInputThreshold
      fallback left_family right_family time_bound_strict exponent_ne_zero
      (projectLengthSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap)
      (by
        intro m
        simpa [projectLengthSingletonTailGapInputOfTimeBound] using
          lengthCodeAt_eq_conj_source m)
      left_length_polynomial right_length_polynomial hrat

/-- Fallback-free primitive time-bound contradiction for the concrete
project-length theorem-5 tail-gap endpoint.  The internal fallback is fixed to
zero, so the public statement has no root `proof_length` and no fallback knob. -/
theorem tailGapConcreteProofLengthModel_contradiction_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  tailGapConcreteProofLengthModel_not_rational_of_timeBoundTailGap
    (fun _ => 0) left_family right_family lengthCodeAt time_bound_strict
    exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
    left_length_polynomial right_length_polynomial hrat

/-- Fallback-free primitive time-bound theorem-5 conclusion over the concrete
checker-defined project length route.  This is the clean route: no root
`proof_length`, no old exactness residual, and no exposed fallback parameter. -/
theorem tailGapConcreteProofLengthModel_not_rational_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
  fun hrat =>
    tailGapConcreteProofLengthModel_contradiction_of_timeBoundTailGap_noFallback
      left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
      tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial hrat

/-- Fallback-free primitive time-bound big-`N` certificate for the clean
project-length route.  The computed collision index is the same explicit
`max upperN threshold`; the hidden internal fallback is fixed to zero. -/
theorem tailGapConcreteProofLengthModel_bigNCertificate_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let fallback : _root_.FormulaCode → Nat := fun _ => 0
    let tail_input :=
      projectLengthSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
    let frontier :=
      timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero
        tail_input
        (by
          intro m
          simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
            lengthCodeAt_eq_conj_source m)
        left_length_polynomial right_length_polynomial
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    let measured :=
      tailGapConcreteProofLengthMeasured fallback frontier
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < measured bigN ∧
            measured bigN ≤ upper.U bigN ∧
              False := by
  dsimp
  simpa using
    tailGapConcreteProofLengthModel_bigNCertificate_of_timeBoundTailGap
      (fun _ => 0) left_family right_family lengthCodeAt time_bound_strict
      exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
      left_length_polynomial right_length_polynomial hrat

/-- Fallback-free primitive time-bound witness-strengthened big-`N`
certificate for the clean project-length route.  It exposes the lower-search
rejection-extractor witness at the same public surface as
`tailGapConcreteProofLengthModel_bigNCertificate_of_timeBoundTailGap_noFallback`,
so the final computed `N` is auditable without unfolding the generated
frontier. -/
theorem tailGapConcreteProofLengthModel_witnessBigNCertificate_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let fallback : _root_.FormulaCode → Nat := fun _ => 0
    let tail_input :=
      projectLengthSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
    let frontier :=
      timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero
        tail_input
        (by
          intro m
          simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
            lengthCodeAt_eq_conj_source m)
        left_length_polynomial right_length_polynomial
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    let measured :=
      tailGapConcreteProofLengthMeasured fallback frontier
    frontier.computedCollisionNOfRationality hrat =
        frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN ∧
      frontier.computedCollisionNOfRationality hrat = bigN ∧
        checkedTail.upperN ≤ bigN ∧
          (tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
            upper.U bigN < measured bigN ∧
              measured bigN ≤ upper.U bigN ∧
                False := by
  dsimp
  let fallback : _root_.FormulaCode → Nat := fun _ => 0
  let tail_input :=
    projectLengthSingletonTailGapInputOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
  have hsource :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m) := by
    intro m
    simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
      lengthCodeAt_eq_conj_source m
  let frontier :=
    timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
      left_family right_family time_bound_strict exponent_ne_zero tail_input
      hsource left_length_polynomial right_length_polynomial
  let checkedTail :=
    checkedSearchUpperTail
      frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
      frontier.concreteLengthCodeFrontier.checkedUpperProvider
      hrat
  have hwitness :
      frontier.computedCollisionNOfRationality hrat =
        frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN := by
    simpa [frontier, checkedTail] using
      tailGapComputedN_eq_rejectionExtractorWitness frontier hrat
  have hbig :
      let fallback : _root_.FormulaCode → Nat := fun _ => 0
      let tail_input :=
        projectLengthSingletonTailGapInputOfTimeBound
          lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
      let frontier :=
        timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
          left_family right_family time_bound_strict exponent_ne_zero
          tail_input
          (by
            intro m
            simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
              lengthCodeAt_eq_conj_source m)
          left_length_polynomial right_length_polynomial
      let checkedTail :=
        checkedSearchUpperTail
          frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.concreteLengthCodeFrontier.checkedUpperProvider
          hrat
      let bigN :=
        max checkedTail.upperN
          (tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold
      let upper :=
        projectLengthUpperTailOfTimeBoundCanonicalTailGap
          fallback frontier hrat
      let measured :=
        tailGapConcreteProofLengthMeasured fallback frontier
      frontier.computedCollisionNOfRationality hrat = bigN ∧
        checkedTail.upperN ≤ bigN ∧
          (tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
            upper.U bigN < measured bigN ∧
              measured bigN ≤ upper.U bigN ∧
                False :=
    tailGapConcreteProofLengthModel_bigNCertificate_of_timeBoundTailGap_noFallback
      left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
      tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial hrat
  simpa [fallback, tail_input, frontier, hsource, checkedTail,
    projectLengthSingletonTailGapInputOfTimeBound] using
    And.intro hwitness hbig

/-- Fallback-free primitive time-bound raw theorem-5 big-`N` certificate for
the clean project-length route.  This is the high-level no-fallback form of
`projectLengthProviderComputedN_tailGapRawPayloadCodeBigNCertificate`: at the
computed collision index, the concrete PA/Hilbert checker accepts the actual
theorem-5 raw code `scale_data.powerBoundRawCode bigN`, and that raw code is
definitionally calibrated to the strengthened finite-consistency code at
`scale_data.scale bigN`. -/
theorem projectLengthProviderComputedN_tailGapRawPayloadCodeBigNCertificate_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let fallback : _root_.FormulaCode → Nat := fun _ => 0
    let tail_input :=
      projectLengthSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
    let frontier :=
      timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero
        tail_input
        (by
          intro m
          simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
            lengthCodeAt_eq_conj_source m)
        left_length_polynomial right_length_polynomial
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    let measured :=
      checkerProjectLengthMeasured
        scale_data
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback
    frontier.computedCollisionNOfRationality hrat =
        frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN ∧
      frontier.computedCollisionNOfRationality hrat = bigN ∧
        checkedTail.upperN ≤ bigN ∧
          (tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
            PAHilbertAcceptedProofCodeForFormulaCode
              (concretePAHilbertPowerBoundChecker scale_data)
              (scale_data.powerBoundRawCode bigN)
              bigN ∧
              scale_data.powerBoundRawCode bigN =
                _root_.strengthenedPartialConsistencyCode
                  (scale_data.scale bigN) ∧
                upper.U bigN < measured bigN ∧
                  measured bigN ≤ upper.U bigN ∧
                    False := by
  dsimp
  let fallback : _root_.FormulaCode → Nat := fun _ => 0
  let tail_input :=
    projectLengthSingletonTailGapInputOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
  have hsource :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m) := by
    intro m
    simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
      lengthCodeAt_eq_conj_source m
  let frontier :=
    timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
      left_family right_family time_bound_strict exponent_ne_zero tail_input
      hsource left_length_polynomial right_length_polynomial
  simpa [fallback, tail_input, frontier, hsource,
    singletonTailGapFrontier_tailGap_threshold_eq,
    projectLengthSingletonTailGapInputOfTimeBound] using
    projectLengthProviderComputedN_tailGapRawPayloadCodeBigNCertificate
      fallback frontier hrat

/-- Fallback-free primitive public closure for the raw theorem-5 code route.
It packages the no-fallback time-bound hypotheses directly into audits, the
raw-code checker certificate at every rationality witness, the contradiction
under rationality, and the final non-rationality conclusion, without using root
`proof_length` or the old payload bridge. -/
theorem projectLengthProviderComputedN_tailGapRawPayloadCode_publicMainClosure_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
    let fallback : _root_.FormulaCode → Nat := fun _ => 0
    let tail_input :=
      projectLengthSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
    let frontier :=
      timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero
        tail_input
        (by
          intro m
          simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
            lengthCodeAt_eq_conj_source m)
        left_length_polynomial right_length_polynomial
    frontier.provider.Audit ∧
      frontier.endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          let checkedTail :=
            checkedSearchUpperTail
              frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
              frontier.concreteLengthCodeFrontier.checkedUpperProvider
              hrat
          let bigN :=
            max checkedTail.upperN
              (tail_gap.gap_for_polynomial_upper
                checkedTail.U checkedTail.polynomial).threshold
          let upper :=
            projectLengthUpperTailOfTimeBoundCanonicalTailGap
              fallback frontier hrat
          let measured :=
            checkerProjectLengthMeasured
              scale_data
              frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
              fallback
          frontier.computedCollisionNOfRationality hrat =
              frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
                checkedTail.U checkedTail.polynomial checkedTail.upperN ∧
            frontier.computedCollisionNOfRationality hrat = bigN ∧
              checkedTail.upperN ≤ bigN ∧
                (tail_gap.gap_for_polynomial_upper
                  checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
                  PAHilbertAcceptedProofCodeForFormulaCode
                    (concretePAHilbertPowerBoundChecker scale_data)
                    (scale_data.powerBoundRawCode bigN)
                    bigN ∧
                    scale_data.powerBoundRawCode bigN =
                      _root_.strengthenedPartialConsistencyCode
                        (scale_data.scale bigN) ∧
                      upper.U bigN < measured bigN ∧
                        measured bigN ≤ upper.U bigN ∧
                          False) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
            ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let fallback : _root_.FormulaCode → Nat := fun _ => 0
  let tail_input :=
    projectLengthSingletonTailGapInputOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
  have hsource :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m) := by
    intro m
    simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
      lengthCodeAt_eq_conj_source m
  let frontier :=
    timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
      left_family right_family time_bound_strict exponent_ne_zero tail_input
      hsource left_length_polynomial right_length_polynomial
  simpa [fallback, tail_input, frontier, hsource,
    singletonTailGapFrontier_tailGap_threshold_eq,
    projectLengthSingletonTailGapInputOfTimeBound] using
    projectLengthProviderComputedN_tailGapRawPayloadCode_publicMainClosure
      fallback frontier

/-- Fallback-free primitive main closure for the proof-length-free project
length route.  It packages the public primitive hypotheses into a single
auditable theorem: the explicit project-length witness computes the same
large `N` as the checked provider, that `N` is the lower-search
rejection-extractor witness, and the same `N` carries the strict lower/upper
collision proving non-rationality. -/
theorem tailGapProofLengthFreeMainTheorem_closure_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
    let fallback : _root_.FormulaCode → Nat := fun _ => 0
    let tail_input :=
      projectLengthSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
    let frontier :=
      timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero
        tail_input
        (by
          intro m
          simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
            lengthCodeAt_eq_conj_source m)
        left_length_polynomial right_length_polynomial
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      let checkedTail :=
        checkedSearchUpperTail
          frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
          frontier.concreteLengthCodeFrontier.checkedUpperProvider
          hrat
      let bigN :=
        max checkedTail.upperN
          (tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold
      let upper :=
        projectLengthUpperTailOfTimeBoundCanonicalTailGap
          fallback frontier hrat
      let measured :=
        tailGapConcreteProofLengthMeasured fallback frontier
      (projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap
          fallback frontier hrat).n =
          frontier.computedCollisionNOfRationality hrat ∧
        frontier.computedCollisionNOfRationality hrat =
            frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
              checkedTail.U checkedTail.polynomial checkedTail.upperN ∧
          frontier.computedCollisionNOfRationality hrat = bigN ∧
            checkedTail.upperN ≤ bigN ∧
              (tail_gap.gap_for_polynomial_upper
                checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
                upper.U bigN < measured bigN ∧
                  measured bigN ≤ upper.U bigN ∧
                    False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  constructor
  · intro hrat
    let fallback : _root_.FormulaCode → Nat := fun _ => 0
    let tail_input :=
      projectLengthSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
    have hsource :
        ∀ m : Nat,
          tail_input.lengthCodeAt m =
            ((left_family.conjIntro right_family)
              |>.rightConjElim
              |>.minCheckedCodeSize m) := by
      intro m
      simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
        lengthCodeAt_eq_conj_source m
    let frontier :=
      timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero tail_input
        hsource left_length_polynomial right_length_polynomial
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    have hexplicit :
        (projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap
            fallback frontier hrat).n =
          frontier.computedCollisionNOfRationality hrat := by
      simpa [frontier] using
        projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap_n_eq_providerComputedN
          fallback frontier hrat
    have hcert :=
      tailGapConcreteProofLengthModel_witnessBigNCertificate_of_timeBoundTailGap_noFallback
        left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
        tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
        right_length_polynomial hrat
    simpa [fallback, tail_input, frontier, hsource, checkedTail,
      projectLengthSingletonTailGapInputOfTimeBound] using
      And.intro hexplicit hcert
  · exact
      tailGapConcreteProofLengthModel_not_rational_of_timeBoundTailGap_noFallback
        left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
        tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
        right_length_polynomial

/-- A root exactness proof at theorem-5 raw codes immediately transports the
concrete model big-`N` certificate to the old `actualProofLengthMeasured`
statement.  Thus the remaining old-root residual is exactly the input `hroot`.
-/
theorem projectLengthProviderComputedN_tailGapRootExactnessCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hroot :
      ∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          tailGapConcreteProofLengthMeasured fallback frontier m)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < actualProofLengthMeasured scale_data bigN ∧
            actualProofLengthMeasured scale_data bigN ≤ upper.U bigN ∧
              actualProofLengthMeasured scale_data bigN =
                tailGapConcreteProofLengthMeasured fallback frontier bigN ∧
                False := by
  dsimp
  let checkedTail :=
    checkedSearchUpperTail
      frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
      frontier.concreteLengthCodeFrontier.checkedUpperProvider
      hrat
  let bigN :=
    max checkedTail.upperN
      (frontier.tail_gap.gap_for_polynomial_upper
        checkedTail.U checkedTail.polynomial).threshold
  have hconcrete :=
    tailGapConcreteProofLengthModel_bigNCertificate
      fallback frontier hrat
  rcases hconcrete with
    ⟨hcomputed, hupperN, hthreshold, hlower, hupper, hfalse⟩
  have hactual :
      actualProofLengthMeasured scale_data bigN =
        tailGapConcreteProofLengthMeasured fallback frontier bigN := by
    simpa [actualProofLengthMeasured] using hroot bigN
  have hlowerActual :
      (projectLengthUpperTailOfTimeBoundCanonicalTailGap fallback frontier hrat).U
          bigN <
        actualProofLengthMeasured scale_data bigN := by
    rw [hactual]
    exact hlower
  have hupperActual :
      actualProofLengthMeasured scale_data bigN ≤
        (projectLengthUpperTailOfTimeBoundCanonicalTailGap fallback frontier hrat).U
          bigN := by
    rw [hactual]
    exact hupper
  exact
    ⟨hcomputed,
      hupperN,
      hthreshold,
      by
        simpa using hlowerActual,
      by
        simpa using hupperActual,
      hactual,
      hfalse⟩

/-- Singleton-input form of the old-root exactness certificate, with the
large-`N` threshold stated at the original tail-gap input.  The only old-root
residual remains `hroot`; the witness formula no longer depends on inspecting
the transported frontier tail-gap. -/
theorem projectLengthProviderComputedN_tailGapRootExactnessCertificate_of_singletonTailGapInput_tailInputThreshold
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
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
    (tail_input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data)
    (lengthCodeAt_eq_conj_source :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m))
    (left_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real left_family.length))
    (right_length_polynomial :
      _root_.is_polynomial_bound
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hroot :
      ∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          tailGapConcreteProofLengthMeasured fallback
            (timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
              left_family right_family time_bound_strict exponent_ne_zero
              tail_input lengthCodeAt_eq_conj_source left_length_polynomial
              right_length_polynomial) m)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let frontier :=
      timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero tail_input
        lengthCodeAt_eq_conj_source left_length_polynomial
        right_length_polynomial
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (tail_input.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (tail_input.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < actualProofLengthMeasured scale_data bigN ∧
            actualProofLengthMeasured scale_data bigN ≤ upper.U bigN ∧
              actualProofLengthMeasured scale_data bigN =
                tailGapConcreteProofLengthMeasured fallback frontier bigN ∧
                False := by
  simpa [singletonTailGapFrontier_tailGap_threshold_eq] using
    projectLengthProviderComputedN_tailGapRootExactnessCertificate
      fallback
      (timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero tail_input
        lengthCodeAt_eq_conj_source left_length_polynomial
        right_length_polynomial)
      hroot hrat

/-- Standard-calibration form of
`projectLengthProviderComputedN_tailGapRootExactnessCertificate`.  The only
old-root input is now the canonical calibration object for the concrete
theorem-5 proof-length model. -/
theorem projectLengthProviderComputedN_tailGapCalibrationCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hcal :
      (tailGapProofLengthCodeSemantics fallback frontier).Calibration)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < actualProofLengthMeasured scale_data bigN ∧
            actualProofLengthMeasured scale_data bigN ≤ upper.U bigN ∧
              actualProofLengthMeasured scale_data bigN =
                tailGapConcreteProofLengthMeasured fallback frontier bigN ∧
                False := by
  have hroot :
      ∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          tailGapConcreteProofLengthMeasured fallback frontier m :=
    (tailGapProofLengthCodeSemantics_calibration_iff_rootProofLength_eq_concreteProofLengthMeasured
      fallback frontier).1 hcal
  exact
    projectLengthProviderComputedN_tailGapRootExactnessCertificate
      fallback frontier hroot hrat

/-- Project-proof-length-semantics form of the old-root big-`N` certificate.
This is the same transport as the calibration certificate, but its input uses
the project-level semantics interface shared by the older proof-length code. -/
theorem projectLengthProviderComputedN_tailGapProjectSemanticsCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hsem :
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < actualProofLengthMeasured scale_data bigN ∧
            actualProofLengthMeasured scale_data bigN ≤ upper.U bigN ∧
              actualProofLengthMeasured scale_data bigN =
                tailGapConcreteProofLengthMeasured fallback frontier bigN ∧
                False := by
  have hcal :
      (tailGapProofLengthCodeSemantics fallback frontier).Calibration :=
    (tailGapProjectProofLengthSemantics_iff_concreteProofLengthCalibration
      fallback frontier).1 hsem
  exact
    projectLengthProviderComputedN_tailGapCalibrationCertificate
      fallback frontier hcal hrat

/-- Conditional root-`proof_length` transport of the clean tail-gap big-`N`
certificate.  The only extra input is the checked-to-actual exactness bridge;
under that bridge, the provider-computed `max upperN threshold` witness is
unchanged and the collision is stated over `actualProofLengthMeasured`. -/
theorem projectLengthProviderComputedN_tailGapActualBridgeCertificate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (bridge :
      Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data
        (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (frontier.tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < actualProofLengthMeasured scale_data bigN ∧
            actualProofLengthMeasured scale_data bigN ≤ upper.U bigN ∧
              checkerProjectLengthMeasured
                  scale_data
                  frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
                  fallback bigN =
                actualProofLengthMeasured scale_data bigN ∧
                False := by
  dsimp
  let checkedTail :=
    checkedSearchUpperTail
      frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
      frontier.concreteLengthCodeFrontier.checkedUpperProvider
      hrat
  let bigN :=
    max checkedTail.upperN
      (frontier.tail_gap.gap_for_polynomial_upper
        checkedTail.U checkedTail.polynomial).threshold
  have hproject :=
    projectLengthProviderComputedN_tailGapBigNCertificate
      fallback frontier hrat
  rcases hproject with
    ⟨hcomputed, hupperN, hthreshold, hlower, hupper, hfalse⟩
  have hactual :
      checkerProjectLengthMeasured
          scale_data
          frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
          fallback bigN =
        actualProofLengthMeasured scale_data bigN :=
    (checkerProjectLengthMeasured_eq_checked
      (scale_data := scale_data)
      (checker :=
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics)
      fallback bigN).trans (bridge.checked_eq_actual bigN)
  have hlowerActual :
      (projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat).U bigN <
        actualProofLengthMeasured scale_data bigN := by
    rw [← hactual]
    exact hlower
  have hupperActual :
      actualProofLengthMeasured scale_data bigN ≤
        (projectLengthUpperTailOfTimeBoundCanonicalTailGap
          fallback frontier hrat).U bigN := by
    rw [← hactual]
    exact hupper
  exact
    ⟨hcomputed,
      hupperN,
      hthreshold,
      hlowerActual,
      hupperActual,
      hactual,
      hfalse⟩

/-- Primitive time-bound form of the old checked-to-actual bridge transport.
The concrete project-length route has already produced the `max upperN threshold`
collision witness; the only extra input here is precisely the old root bridge,
and the witness is still stated at the original tail-gap threshold. -/
theorem projectLengthProviderComputedN_tailGapActualBridgeCertificate_of_timeBoundTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (bridge :
      let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      Month9Month10CheckedMeasuredToActualProofLengthBridge
        scale_data
        (frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics.toProofCodeSemantics))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let frontier :=
      projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < actualProofLengthMeasured scale_data bigN ∧
            actualProofLengthMeasured scale_data bigN ≤ upper.U bigN ∧
              checkerProjectLengthMeasured
                  scale_data
                  frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
                  fallback bigN =
                actualProofLengthMeasured scale_data bigN ∧
                False := by
  dsimp at bridge ⊢
  simpa [projectLengthTimeBoundTailGapFrontier,
    projectLengthSingletonTailGapInputOfTimeBound,
    singletonTailGapFrontier_tailGap_threshold_eq] using
    projectLengthProviderComputedN_tailGapActualBridgeCertificate
      fallback
      (projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial)
      bridge hrat

/-- Primitive time-bound project-semantics transport of the clean tail-gap
big-`N` certificate to the old actual-proof-length route.  This states the
remaining proof-length residual in the project-semantics form rather than the
checked-to-actual bridge form. -/
theorem projectLengthProviderComputedN_tailGapProjectSemanticsCertificate_of_timeBoundTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hsem :
      let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let frontier :=
      projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < actualProofLengthMeasured scale_data bigN ∧
            actualProofLengthMeasured scale_data bigN ≤ upper.U bigN ∧
              actualProofLengthMeasured scale_data bigN =
                tailGapConcreteProofLengthMeasured fallback frontier bigN ∧
                False := by
  dsimp at hsem ⊢
  simpa [projectLengthTimeBoundTailGapFrontier,
    projectLengthSingletonTailGapInputOfTimeBound,
    singletonTailGapFrontier_tailGap_threshold_eq] using
    projectLengthProviderComputedN_tailGapProjectSemanticsCertificate
      fallback
      (projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial)
      hsem hrat

/-- Project-semantics residual form of the primitive time-bound tail-gap
contradiction.  This is the old root route after all non-root work has been
compiled down to the single project-semantics calibration input. -/
theorem tailGapProjectSemantics_contradiction_of_timeBoundTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hsem :
      let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False := by
  have hcert :=
    projectLengthProviderComputedN_tailGapProjectSemanticsCertificate_of_timeBoundTailGap
      fallback left_family right_family lengthCodeAt time_bound_strict
      exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
      left_length_polynomial right_length_polynomial hsem hrat
  dsimp at hcert
  exact hcert.2.2.2.2.2.2

/-- Final old-root-compatible theorem-5 conclusion on the primitive time-bound
tail-gap surface, with the remaining proof-length input stated only as
project-level proof-length semantics for the concrete checker model. -/
theorem tailGapProjectSemantics_not_rational_of_timeBoundTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hsem :
      let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat =>
    tailGapProjectSemantics_contradiction_of_timeBoundTailGap
      fallback left_family right_family lengthCodeAt time_bound_strict
      exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
      left_length_polynomial right_length_polynomial hsem hrat

/-- Final old-root-compatible conclusion from the exact pointwise equality
between root `proof_length` and checker `projectLength` on theorem-5 raw codes.
This is the same residual as `ProjectProofLengthSemantics`, but stated in the
form needed to discharge the historical proof-length bridge. -/
theorem tailGapRootProofLengthProjectLengthExactness_not_rational_of_timeBoundTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hroot :
      let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      ∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          checkerProjectLengthMeasured
            scale_data
            frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
            fallback m) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hsem :
      let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) :=
    (tailGapProjectProofLengthSemantics_iff_rootProofLength_eq_projectLengthMeasured_of_timeBoundTailGap
      fallback left_family right_family lengthCodeAt time_bound_strict
      exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
      left_length_polynomial right_length_polynomial).2 hroot
  exact
    tailGapProjectSemantics_not_rational_of_timeBoundTailGap
      fallback left_family right_family lengthCodeAt time_bound_strict
      exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
      left_length_polynomial right_length_polynomial hsem

/-- Final old-root-compatible conclusion from the exact pointwise equality
between root `proof_length` and the concrete family `minCheckedCodeSize`. -/
theorem tailGapRootProofLengthFamilyMinCheckedExactness_not_rational_of_timeBoundTailGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hroot :
      let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      ∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (((frontier.left_family.conjIntro frontier.right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m : Nat) : Real)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hsem :
      let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      _root_.ProjectProofLengthSemantics
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (tailGapProofLengthCodeSemantics fallback frontier).length
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) :=
    (tailGapProjectProofLengthSemantics_iff_rootProofLength_eq_familyMinChecked_of_timeBoundTailGap
      fallback left_family right_family lengthCodeAt time_bound_strict
      exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
      left_length_polynomial right_length_polynomial).2 hroot
  exact
    tailGapProjectSemantics_not_rational_of_timeBoundTailGap
      fallback left_family right_family lengthCodeAt time_bound_strict
      exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
      left_length_polynomial right_length_polynomial hsem

/-- Fallback-free contradiction from the exact pointwise equality between root
`proof_length` and the concrete family `minCheckedCodeSize`.  The fallback used
inside the intermediate project-length model is fixed to zero and is invisible
in the final residual statement. -/
theorem tailGapRootProofLengthFamilyMinCheckedExactness_contradiction_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hroot :
      let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      ∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (((frontier.left_family.conjIntro frontier.right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m : Nat) : Real))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  tailGapRootProofLengthFamilyMinCheckedExactness_not_rational_of_timeBoundTailGap
    (fun _ => 0) left_family right_family lengthCodeAt time_bound_strict
    exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
    left_length_polynomial right_length_polynomial hroot hrat

/-- Fallback-free old-root-compatible theorem-5 conclusion.  After all concrete
project-length work, the sole remaining root residual is exactly the pointwise
family equality `proof_length(powerBoundRawCode m) = minCheckedCodeSize m`. -/
theorem tailGapRootProofLengthFamilyMinCheckedExactness_not_rational_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hroot :
      let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      ∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (((frontier.left_family.conjIntro frontier.right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m : Nat) : Real)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat =>
    tailGapRootProofLengthFamilyMinCheckedExactness_contradiction_of_timeBoundTailGap_noFallback
      left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
      tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial hroot hrat

/-- The named checker-family exactness residual and the fallback-free pointwise
root-`proof_length`/`minCheckedCodeSize` residual are the same obligation on the
primitive time-bound tail-gap surface. -/
theorem tailGapCheckerProofLengthFamilyExactness_iff_rootProofLength_eq_familyMinChecked_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
    let frontier :=
      projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
      ↔
      (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (((frontier.left_family.conjIntro frontier.right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m : Nat) : Real)) :=
  (tailGapCheckerProofLengthFamilyExactness_iff_projectProofLengthSemantics_of_timeBoundTailGap
    (fun _ => 0) left_family right_family lengthCodeAt time_bound_strict
    exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
    left_length_polynomial right_length_polynomial).trans
    (tailGapProjectProofLengthSemantics_iff_rootProofLength_eq_familyMinChecked_of_timeBoundTailGap
      (fun _ => 0) left_family right_family lengthCodeAt time_bound_strict
      exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
      left_length_polynomial right_length_polynomial)

/-- The fallback-free root exactness residual can be stated directly against the
primitive `lengthCodeAt` function.  This is equivalent to the family
`minCheckedCodeSize` statement because `lengthCodeAt_eq_conj_source` identifies
the two pointwise. -/
theorem tailGapRootProofLength_eq_lengthCodeAt_iff_rootProofLength_eq_familyMinChecked_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
    (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (lengthCodeAt m : Real))
      ↔
      (let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      ∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (((frontier.left_family.conjIntro frontier.right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m : Nat) : Real)) := by
  change
    (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (lengthCodeAt m : Real))
      ↔
      (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m : Nat) : Real))
  constructor
  · intro hroot m
    exact
      (hroot m).trans
        (by
          exact_mod_cast lengthCodeAt_eq_conj_source m)
  · intro hroot m
    exact
      (hroot m).trans
        (by
          exact_mod_cast (lengthCodeAt_eq_conj_source m).symm)

/-- The named checker-family exactness residual is equivalently the primitive
pointwise equation `proof_length(powerBoundRawCode m) = lengthCodeAt m`. -/
theorem tailGapCheckerProofLengthFamilyExactness_iff_rootProofLength_eq_lengthCodeAt_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
    (let frontier :=
      projectLengthTimeBoundTailGapFrontier
        left_family right_family lengthCodeAt time_bound_strict
        exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
        left_length_polynomial right_length_polynomial
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics)
      ↔
      (∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (lengthCodeAt m : Real)) :=
  (tailGapCheckerProofLengthFamilyExactness_iff_rootProofLength_eq_familyMinChecked_of_timeBoundTailGap_noFallback
    left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
    tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
    right_length_polynomial).trans
    (tailGapRootProofLength_eq_lengthCodeAt_iff_rootProofLength_eq_familyMinChecked_of_timeBoundTailGap_noFallback
      left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
      tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial).symm

/-- Final fallback-free old-root-compatible theorem-5 conclusion from the named
checker-family exactness residual used elsewhere in the project. -/
theorem tailGapCheckerProofLengthFamilyExactness_not_rational_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (family_exactness :
      let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hroot :
      let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      ∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (((frontier.left_family.conjIntro frontier.right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m : Nat) : Real) :=
    (tailGapCheckerProofLengthFamilyExactness_iff_rootProofLength_eq_familyMinChecked_of_timeBoundTailGap_noFallback
      left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
      tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial).1 family_exactness
  exact
    tailGapRootProofLengthFamilyMinCheckedExactness_not_rational_of_timeBoundTailGap_noFallback
      left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
      tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial hroot

/-- Final fallback-free old-root-compatible theorem-5 conclusion from the
primitive pointwise equation `proof_length(powerBoundRawCode m) = lengthCodeAt m`.
This is the tightest residual statement at the time-bound tail-gap boundary. -/
theorem tailGapRootProofLengthLengthCodeAtExactness_not_rational_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (hroot :
      ∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (lengthCodeAt m : Real)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  have family_exactness :
      let frontier :=
        projectLengthTimeBoundTailGapFrontier
          left_family right_family lengthCodeAt time_bound_strict
          exponent_ne_zero tail_gap lengthCodeAt_eq_conj_source
          left_length_polynomial right_length_polynomial
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics :=
    (tailGapCheckerProofLengthFamilyExactness_iff_rootProofLength_eq_lengthCodeAt_of_timeBoundTailGap_noFallback
      left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
      tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial).2 hroot
  exact
    tailGapCheckerProofLengthFamilyExactness_not_rational_of_timeBoundTailGap_noFallback
      left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
      tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial family_exactness

/-- Fallback-free old-root-compatible theorem-5 conclusion from the calibrated
checker proof-length exactness certificate.  This removes the separate
pointwise `proof_length = lengthCodeAt` argument at the tail-gap boundary: the
root equation is generated from checker exactness, raw-code injectivity, and
the calibrated checker `projectLength` computation. -/
theorem tailGapCalibratedCheckerExactness_not_rational_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hroot :
      ∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (lengthCodeAt m : Real) :=
    rootProofLength_eq_lengthCodeAt_of_calibratedCheckerExactness_timeBound
      lengthCodeAt time_bound_strict exponent_ne_zero (fun _ => 0)
      exactness
  exact
    tailGapRootProofLengthLengthCodeAtExactness_not_rational_of_timeBoundTailGap_noFallback
      left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
      tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial hroot

/-- Contradiction form of
`tailGapCalibratedCheckerExactness_not_rational_of_timeBoundTailGap_noFallback`,
useful when an endpoint has already opened a rationality branch. -/
theorem tailGapCalibratedCheckerExactness_contradiction_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  tailGapCalibratedCheckerExactness_not_rational_of_timeBoundTailGap_noFallback
    left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
    tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
    right_length_polynomial exactness hrat

/-- Fallback-free old-root-compatible big-`N` certificate from calibrated
checker proof-length exactness.  This is the certificate version of
`tailGapCalibratedCheckerExactness_not_rational_of_timeBoundTailGap_noFallback`:
the displayed collision index is still the explicit
`max upperN threshold`, while the old-root exactness equality is generated from
the calibrated checker certificate. -/
theorem projectLengthProviderComputedN_tailGapCalibratedCheckerExactnessCertificate_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let fallback : _root_.FormulaCode → Nat := fun _ => 0
    let tail_input :=
      projectLengthSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
    let frontier :=
      timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero
        tail_input
        (by
          intro m
          simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
            lengthCodeAt_eq_conj_source m)
        left_length_polynomial right_length_polynomial
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    frontier.computedCollisionNOfRationality hrat = bigN ∧
      checkedTail.upperN ≤ bigN ∧
        (tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
          upper.U bigN < actualProofLengthMeasured scale_data bigN ∧
            actualProofLengthMeasured scale_data bigN ≤ upper.U bigN ∧
              actualProofLengthMeasured scale_data bigN =
                tailGapConcreteProofLengthMeasured fallback frontier bigN ∧
                False := by
  dsimp
  let fallback : _root_.FormulaCode → Nat := fun _ => 0
  let tail_input :=
    projectLengthSingletonTailGapInputOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
  have hsource :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m) := by
    intro m
    simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
      lengthCodeAt_eq_conj_source m
  let frontier :=
    timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
      left_family right_family time_bound_strict exponent_ne_zero tail_input
      hsource left_length_polynomial right_length_polynomial
  have hrootLength :
      ∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          (lengthCodeAt m : Real) :=
    rootProofLength_eq_lengthCodeAt_of_calibratedCheckerExactness_timeBound
      lengthCodeAt time_bound_strict exponent_ne_zero fallback exactness
  have hrootConcrete :
      ∀ m : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode m) =
          tailGapConcreteProofLengthMeasured fallback frontier m := by
    intro m
    calc
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode m) =
          (lengthCodeAt m : Real) :=
            hrootLength m
      _ =
          (((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m : Nat) : Real) := by
            exact_mod_cast lengthCodeAt_eq_conj_source m
      _ = tailGapConcreteProofLengthMeasured fallback frontier m :=
          (tailGapConcreteProofLengthMeasured_eq_familyMinChecked
            fallback frontier m).symm
  simpa [fallback, tail_input, frontier, hsource,
    projectLengthSingletonTailGapInputOfTimeBound] using
    projectLengthProviderComputedN_tailGapRootExactnessCertificate_of_singletonTailGapInput_tailInputThreshold
      fallback left_family right_family time_bound_strict exponent_ne_zero
      tail_input hsource left_length_polynomial right_length_polynomial
      hrootConcrete hrat

/-- Witness-strengthened old-root-compatible big-`N` certificate from
calibrated checker proof-length exactness.  It extends
`projectLengthProviderComputedN_tailGapCalibratedCheckerExactnessCertificate_of_timeBoundTailGap_noFallback`
with the proof-length-free witness equation
`computed N = rejectionExtractor.witness`, while the actual-root collision
part is still generated through the calibrated checker exactness certificate. -/
theorem projectLengthProviderComputedN_tailGapCalibratedCheckerExactnessWitnessCertificate_of_timeBoundTailGap_noFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (left_family : _root_.MiniHilbert.ConcreteProofFamily Ax A)
    (right_family : _root_.MiniHilbert.ConcreteProofFamily Ax B)
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun m : Nat => (lengthCodeAt m : Real)))
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
        (_root_.MiniHilbert.nat_bound_as_real right_family.length))
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let fallback : _root_.FormulaCode → Nat := fun _ => 0
    let tail_input :=
      projectLengthSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
    let frontier :=
      timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
        left_family right_family time_bound_strict exponent_ne_zero
        tail_input
        (by
          intro m
          simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
            lengthCodeAt_eq_conj_source m)
        left_length_polynomial right_length_polynomial
    let checkedTail :=
      checkedSearchUpperTail
        frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
        frontier.concreteLengthCodeFrontier.checkedUpperProvider
        hrat
    let bigN :=
      max checkedTail.upperN
        (tail_gap.gap_for_polynomial_upper
          checkedTail.U checkedTail.polynomial).threshold
    let upper :=
      projectLengthUpperTailOfTimeBoundCanonicalTailGap
        fallback frontier hrat
    frontier.computedCollisionNOfRationality hrat =
        frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN ∧
      frontier.computedCollisionNOfRationality hrat = bigN ∧
        checkedTail.upperN ≤ bigN ∧
          (tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold ≤ bigN ∧
            upper.U bigN < actualProofLengthMeasured scale_data bigN ∧
              actualProofLengthMeasured scale_data bigN ≤ upper.U bigN ∧
                actualProofLengthMeasured scale_data bigN =
                  tailGapConcreteProofLengthMeasured fallback frontier bigN ∧
                  False := by
  dsimp
  let fallback : _root_.FormulaCode → Nat := fun _ => 0
  let tail_input :=
    projectLengthSingletonTailGapInputOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
  have hsource :
      ∀ m : Nat,
        tail_input.lengthCodeAt m =
          ((left_family.conjIntro right_family)
            |>.rightConjElim
            |>.minCheckedCodeSize m) := by
    intro m
    simpa [tail_input, projectLengthSingletonTailGapInputOfTimeBound] using
      lengthCodeAt_eq_conj_source m
  let frontier :=
    timeBoundCanonicalConjIntroTargetTailGapFrontierOfSingletonTailGapInput
      left_family right_family time_bound_strict exponent_ne_zero tail_input
      hsource left_length_polynomial right_length_polynomial
  let checkedTail :=
    checkedSearchUpperTail
      frontier.concreteLengthCodeFrontier.lower_search.toProofLengthFreeMonth12Candidate
      frontier.concreteLengthCodeFrontier.checkedUpperProvider
      hrat
  have hwitness :
      frontier.computedCollisionNOfRationality hrat =
        frontier.concreteLengthCodeFrontier.lower_search.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN := by
    simpa [frontier, checkedTail] using
      tailGapComputedN_eq_rejectionExtractorWitness frontier hrat
  have hcert :=
    projectLengthProviderComputedN_tailGapCalibratedCheckerExactnessCertificate_of_timeBoundTailGap_noFallback
      left_family right_family lengthCodeAt time_bound_strict exponent_ne_zero
      tail_gap lengthCodeAt_eq_conj_source left_length_polynomial
      right_length_polynomial exactness hrat
  simpa [fallback, tail_input, frontier, hsource, checkedTail,
    projectLengthSingletonTailGapInputOfTimeBound] using
    And.intro hwitness hcert

theorem projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap_contradiction
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap
    fallback frontier hrat).contradiction

theorem projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap_not_rational
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat =>
    projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap_contradiction
      fallback frontier hrat

theorem projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap
        fallback frontier hrat).n =
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
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap_n_eq
      fallback frontier,
    projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap_contradiction
      fallback frontier,
    projectLengthExplicitCollisionWitnessOfTimeBoundCanonicalTailGap_not_rational
      fallback frontier⟩

/-! ## Local-Hilbert length-code project-length endpoint -/

/-- Project-length endpoint from the local-Hilbert length-code frontier.  This
uses the Month 8 concrete proof-object checker interface to identify the local
source minimum with the concrete target proof-family source, and then reuses
the payload-free concrete project-length endpoint. -/
def projectLengthEndpointOfLocalHilbertLengthCodeFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp) :
    Month9Month10AbstractMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        scale_data frontier.lowerSearch.checkerSemantics fallback) :=
  projectLengthEndpointOfConcreteLengthCodeTargetFrontier
    fallback frontier.concreteLengthCodeFrontier

theorem projectLengthEndpointOfLocalHilbertLengthCodeFrontier_computed_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthEndpointOfLocalHilbertLengthCodeFrontier
        fallback frontier).computedCollisionNOfRationality hrat =
      frontier.lowerSearch.rejectionExtractor.witness
        ((projectLengthEndpointOfLocalHilbertLengthCodeFrontier
          fallback frontier).upperTailOfRationality hrat).U
        ((projectLengthEndpointOfLocalHilbertLengthCodeFrontier
          fallback frontier).upperTailOfRationality hrat).polynomial
        ((projectLengthEndpointOfLocalHilbertLengthCodeFrontier
          fallback frontier).upperTailOfRationality hrat).upperN := by
  simpa [projectLengthEndpointOfLocalHilbertLengthCodeFrontier,
    Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier.concreteLengthCodeFrontier] using
    projectLengthEndpointOfConcreteLengthCodeTargetFrontier_computed_n_eq
      fallback frontier.concreteLengthCodeFrontier hrat

theorem projectLengthEndpointOfLocalHilbertLengthCodeFrontier_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp) :
    (projectLengthEndpointOfLocalHilbertLengthCodeFrontier
      fallback frontier).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            scale_data frontier.lowerSearch.checkerSemantics fallback)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          ((projectLengthEndpointOfLocalHilbertLengthCodeFrontier
              fallback frontier)
            ).computedCollisionNOfRationality hrat =
            frontier.lowerSearch.rejectionExtractor.witness
              (((projectLengthEndpointOfLocalHilbertLengthCodeFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).U
              (((projectLengthEndpointOfLocalHilbertLengthCodeFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).polynomial
              (((projectLengthEndpointOfLocalHilbertLengthCodeFrontier
                fallback frontier)
                  ).upperTailOfRationality hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [projectLengthEndpointOfLocalHilbertLengthCodeFrontier,
    Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier.concreteLengthCodeFrontier] using
    projectLengthEndpointOfConcreteLengthCodeTargetFrontier_closure
      fallback frontier.concreteLengthCodeFrontier

/-- Public main closure for the Local-Hilbert length-code project-length
endpoint.  It transports the already-clean concrete length-code endpoint to the
Local-Hilbert boundary, where the Month 8 proof-object checker interface
supplies the source-code exactness. -/
theorem projectLengthEndpointOfLocalHilbertLengthCodeFrontier_publicMainClosure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp) :
    let endpoint :=
      projectLengthEndpointOfLocalHilbertLengthCodeFrontier
        fallback frontier
    endpoint.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            scale_data frontier.lowerSearch.checkerSemantics fallback)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          endpoint.computedCollisionNOfRationality hrat =
            frontier.lowerSearch.rejectionExtractor.witness
              (endpoint.upperTailOfRationality hrat).U
              (endpoint.upperTailOfRationality hrat).polynomial
              (endpoint.upperTailOfRationality hrat).upperN) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (endpoint.upperTailOfRationality hrat).upperN ≤
              endpoint.computedCollisionNOfRationality hrat) ∧
            (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
              (endpoint.upperTailOfRationality hrat).U
                  (endpoint.computedCollisionNOfRationality hrat) <
                checkerProjectLengthMeasured
                  scale_data frontier.lowerSearch.checkerSemantics fallback
                  (endpoint.computedCollisionNOfRationality hrat)) ∧
              (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
                checkerProjectLengthMeasured
                    scale_data frontier.lowerSearch.checkerSemantics fallback
                    (endpoint.computedCollisionNOfRationality hrat) ≤
                  (endpoint.upperTailOfRationality hrat).U
                    (endpoint.computedCollisionNOfRationality hrat)) ∧
                (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                  False) ∧
                ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [projectLengthEndpointOfLocalHilbertLengthCodeFrontier,
    Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier.concreteLengthCodeFrontier]
    using
      projectLengthEndpointOfConcreteLengthCodeTargetFrontier_publicMainClosure
        fallback frontier.concreteLengthCodeFrontier

/-! ## Local-Hilbert explicit project-length endpoint -/

/-- Explicit project-length endpoint from the Local-Hilbert length-code frontier.
This is the direct computed-`N` version of
`projectLengthEndpointOfLocalHilbertLengthCodeFrontier`: the upper threshold is
definitionally the concrete length-polynomial threshold `0`, and the collision
index is the lower-search rejection-extractor witness at that threshold. -/
def projectLengthExplicitEndpointOfLocalHilbertLengthCodeFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp) :
    ProjectLengthExplicitMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        scale_data frontier.lowerSearch.checkerSemantics fallback) :=
  projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier
    fallback frontier.concreteLengthCodeFrontier

theorem projectLengthExplicitEndpointOfLocalHilbertLengthCodeFrontier_upperN
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((projectLengthExplicitEndpointOfLocalHilbertLengthCodeFrontier
      fallback frontier).upperTailOfRationality hrat).upperN = 0 := by
  simpa [projectLengthExplicitEndpointOfLocalHilbertLengthCodeFrontier,
    Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier.concreteLengthCodeFrontier] using
    projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier_upperN
      fallback frontier.concreteLengthCodeFrontier hrat

theorem projectLengthExplicitEndpointOfLocalHilbertLengthCodeFrontier_computed_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitEndpointOfLocalHilbertLengthCodeFrontier
        fallback frontier).computedCollisionNOfRationality hrat =
      frontier.lowerSearch.rejectionExtractor.witness
        ((projectLengthExplicitEndpointOfLocalHilbertLengthCodeFrontier
          fallback frontier).upperTailOfRationality hrat).U
        ((projectLengthExplicitEndpointOfLocalHilbertLengthCodeFrontier
          fallback frontier).upperTailOfRationality hrat).polynomial
        0 := by
  simpa [projectLengthExplicitEndpointOfLocalHilbertLengthCodeFrontier,
    Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier.concreteLengthCodeFrontier] using
    projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier_computed_n_eq
      fallback frontier.concreteLengthCodeFrontier hrat

theorem projectLengthExplicitEndpointOfLocalHilbertLengthCodeFrontier_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp) :
    let endpoint :=
      projectLengthExplicitEndpointOfLocalHilbertLengthCodeFrontier
        fallback frontier
    endpoint.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            scale_data frontier.lowerSearch.checkerSemantics fallback)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        endpoint.computedCollisionNOfRationality hrat =
          frontier.lowerSearch.rejectionExtractor.witness
            (endpoint.upperTailOfRationality hrat).U
            (endpoint.upperTailOfRationality hrat).polynomial
            0) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).upperN = 0) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).upperN ≤
          endpoint.computedCollisionNOfRationality hrat) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).U
            (endpoint.computedCollisionNOfRationality hrat) <
          checkerProjectLengthMeasured
            scale_data frontier.lowerSearch.checkerSemantics fallback
            (endpoint.computedCollisionNOfRationality hrat)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        checkerProjectLengthMeasured
            scale_data frontier.lowerSearch.checkerSemantics fallback
            (endpoint.computedCollisionNOfRationality hrat) ≤
          (endpoint.upperTailOfRationality hrat).U
            (endpoint.computedCollisionNOfRationality hrat)) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
        False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [projectLengthExplicitEndpointOfLocalHilbertLengthCodeFrontier,
    Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier.concreteLengthCodeFrontier] using
    projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier_closure
      fallback frontier.concreteLengthCodeFrontier

/-! ## Payload-free Local-Hilbert explicit project-length endpoint -/

/-- Explicit project-length endpoint for the payload-free Local-Hilbert target
frontier.  Unlike `projectLengthExplicitEndpointOfLocalHilbertLengthCodeFrontier`,
this statement does not quantify over `HilbertProjectionCodeAlignment`; the
local formula-code interpretation and concrete target proof family are enough
to reuse the concrete length-code endpoint. -/
def projectLengthExplicitEndpointOfPayloadFreeLocalHilbertLengthCodeTargetFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {local_interpretation :
      _root_.MiniHilbert.LocalFormulaCodeHilbertInterpretation A B}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10PayloadFreeLocalHilbertLengthCodeTargetFrontier
        scale_data local_interpretation target_family) :
    ProjectLengthExplicitMeasuredDirectCollisionEndpoint
      (checkerProjectLengthMeasured
        scale_data frontier.lowerSearch.checkerSemantics fallback) :=
  projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier
    fallback frontier.concreteLengthCodeFrontier

theorem projectLengthExplicitEndpointOfPayloadFreeLocalHilbertLengthCodeTargetFrontier_upperN
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {local_interpretation :
      _root_.MiniHilbert.LocalFormulaCodeHilbertInterpretation A B}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10PayloadFreeLocalHilbertLengthCodeTargetFrontier
        scale_data local_interpretation target_family)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ((projectLengthExplicitEndpointOfPayloadFreeLocalHilbertLengthCodeTargetFrontier
      fallback frontier).upperTailOfRationality hrat).upperN = 0 := by
  simpa [
    projectLengthExplicitEndpointOfPayloadFreeLocalHilbertLengthCodeTargetFrontier,
    Month9Month10PayloadFreeLocalHilbertLengthCodeTargetFrontier.concreteLengthCodeFrontier] using
    projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier_upperN
      fallback frontier.concreteLengthCodeFrontier hrat

theorem projectLengthExplicitEndpointOfPayloadFreeLocalHilbertLengthCodeTargetFrontier_computed_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {local_interpretation :
      _root_.MiniHilbert.LocalFormulaCodeHilbertInterpretation A B}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10PayloadFreeLocalHilbertLengthCodeTargetFrontier
        scale_data local_interpretation target_family)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitEndpointOfPayloadFreeLocalHilbertLengthCodeTargetFrontier
        fallback frontier).computedCollisionNOfRationality hrat =
      frontier.lowerSearch.rejectionExtractor.witness
        ((projectLengthExplicitEndpointOfPayloadFreeLocalHilbertLengthCodeTargetFrontier
          fallback frontier).upperTailOfRationality hrat).U
        ((projectLengthExplicitEndpointOfPayloadFreeLocalHilbertLengthCodeTargetFrontier
          fallback frontier).upperTailOfRationality hrat).polynomial
        0 := by
  simpa [
    projectLengthExplicitEndpointOfPayloadFreeLocalHilbertLengthCodeTargetFrontier,
    Month9Month10PayloadFreeLocalHilbertLengthCodeTargetFrontier.concreteLengthCodeFrontier] using
    projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier_computed_n_eq
      fallback frontier.concreteLengthCodeFrontier hrat

theorem projectLengthExplicitEndpointOfPayloadFreeLocalHilbertLengthCodeTargetFrontier_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {local_interpretation :
      _root_.MiniHilbert.LocalFormulaCodeHilbertInterpretation A B}
    {target_family :
      _root_.MiniHilbert.ConcreteProofFamily Ax
        (fun m => A m ⊓ B m)}
    (frontier :
      Month9Month10PayloadFreeLocalHilbertLengthCodeTargetFrontier
        scale_data local_interpretation target_family) :
    let endpoint :=
      projectLengthExplicitEndpointOfPayloadFreeLocalHilbertLengthCodeTargetFrontier
        fallback frontier
    endpoint.Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (checkerProjectLengthMeasured
            scale_data frontier.lowerSearch.checkerSemantics fallback)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        endpoint.computedCollisionNOfRationality hrat =
          frontier.lowerSearch.rejectionExtractor.witness
            (endpoint.upperTailOfRationality hrat).U
            (endpoint.upperTailOfRationality hrat).polynomial
            0) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).upperN = 0) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).upperN ≤
          endpoint.computedCollisionNOfRationality hrat) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (endpoint.upperTailOfRationality hrat).U
            (endpoint.computedCollisionNOfRationality hrat) <
          checkerProjectLengthMeasured
            scale_data frontier.lowerSearch.checkerSemantics fallback
            (endpoint.computedCollisionNOfRationality hrat)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        checkerProjectLengthMeasured
            scale_data frontier.lowerSearch.checkerSemantics fallback
            (endpoint.computedCollisionNOfRationality hrat) ≤
          (endpoint.upperTailOfRationality hrat).U
            (endpoint.computedCollisionNOfRationality hrat)) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
        False) ∧
      ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [
    projectLengthExplicitEndpointOfPayloadFreeLocalHilbertLengthCodeTargetFrontier,
    Month9Month10PayloadFreeLocalHilbertLengthCodeTargetFrontier.concreteLengthCodeFrontier] using
    projectLengthExplicitEndpointOfConcreteLengthCodeTargetFrontier_closure
      fallback frontier.concreteLengthCodeFrontier

/-! ## Local-Hilbert explicit project-length witness -/

/-- Explicit project-length collision witness for the Local-Hilbert length-code
frontier.  This reuses the concrete length-code endpoint but keeps the public
statement at the Local-Hilbert layer, where the Month 8 proof-object checker
interface supplies the source-code exactness. -/
noncomputable def projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ComputedSearchCollisionWitness
      (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
        fallback frontier.concreteLengthCodeFrontier hrat).U
      (checkerProjectLengthMeasured
        scale_data frontier.concreteLengthCodeFrontier.lower_search.checkerSemantics
        fallback) :=
  projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier
    fallback frontier.concreteLengthCodeFrontier hrat

theorem projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier_n_eq_rejectionExtractorWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier
      fallback frontier hrat).n =
      frontier.lowerSearch.rejectionExtractor.witness
        (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback frontier.concreteLengthCodeFrontier hrat).U
        (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback frontier.concreteLengthCodeFrontier hrat).polynomial
        (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback frontier.concreteLengthCodeFrontier hrat).upperN := by
  simpa [projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier,
    Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier.concreteLengthCodeFrontier] using
    projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier_n_eq_rejectionExtractorWitness
      fallback frontier.concreteLengthCodeFrontier hrat

/-- The Local-Hilbert explicit project-length witness computes the same `N` as
the proof-length-free theorem-5 provider at this frontier.  This is the
Local-Hilbert analogue of the concrete length-code exactness theorem. -/
theorem projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier_n_eq_providerComputedN
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier
      fallback frontier hrat).n =
      frontier.computedCollisionNOfRationality hrat := by
  calc
    (projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier
        fallback frontier hrat).n =
        (projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier
          fallback frontier.concreteLengthCodeFrontier hrat).n := rfl
    _ = frontier.concreteLengthCodeFrontier.computedCollisionNOfRationality hrat :=
        projectLengthExplicitSearchWitnessOfConcreteLengthCodeTargetFrontier_n_eq_providerComputedN
          fallback frontier.concreteLengthCodeFrontier hrat
    _ = frontier.computedCollisionNOfRationality hrat := rfl

theorem projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier_contradiction
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False :=
  (projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier
    fallback frontier hrat).contradiction

theorem projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier_not_rational
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  fun hrat =>
    projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier_contradiction
      fallback frontier hrat

theorem projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier
      fallback frontier hrat).n =
      frontier.lowerSearch.rejectionExtractor.witness
        (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback frontier.concreteLengthCodeFrontier hrat).U
        (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback frontier.concreteLengthCodeFrontier hrat).polynomial
        (projectLengthUpperTailOfConcreteLengthCodeTargetFrontier
          fallback frontier.concreteLengthCodeFrontier hrat).upperN ∧
      False ∧
      ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier_n_eq_rejectionExtractorWitness
      fallback frontier hrat,
    projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier_contradiction
      fallback frontier hrat,
    projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier_not_rational
      fallback frontier⟩

/-- Provider-computed form of the Local-Hilbert explicit project-length witness
closure. -/
theorem projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier_providerComputedClosure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (fallback : _root_.FormulaCode → Nat)
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (frontier :
      Month9Month10LocalHilbertLengthCodeInternalTheorem5Frontier
        scale_data interp)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier
      fallback frontier hrat).n =
      frontier.computedCollisionNOfRationality hrat ∧
      False ∧
      ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier_n_eq_providerComputedN
      fallback frontier hrat,
    projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier_contradiction
      fallback frontier hrat,
    projectLengthExplicitSearchWitnessOfLocalHilbertLengthCodeFrontier_not_rational
      fallback frontier⟩

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
