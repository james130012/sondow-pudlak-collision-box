import integration.SondowProjectBigNGrowthObligationAudit
import integration.SondowProjectBigNAxiomatizedSubmissionRoute
import BoundedArithmeticLab.CnBoxPudlakGap
import BoundedArithmeticLab.CnBoxPudlakProjectConcreteCertificateObligation
import BoundedArithmeticLab.CnBoxPudlakProjectSourceAssemblyFieldIndex
import BoundedArithmeticLab.SemanticProofLength
import BoundedArithmeticLab.OperationalVerifier
import BoundedArithmeticLab.VerifierCompiler
import BoundedArithmeticLab.CertificateVerifier
import EulerLimit.ProofLengthCalibrationInternalizationSurface
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectPudlakLowerBoundInputAudit

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10ProofLengthGapFrontier
open SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint
open SondowProjectMonth9Month10Month11ExactProofGapHandoff
open SondowProjectMonth11PAHilbertCheckerSurface
open SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface
open SondowProjectBigNCleanSubmissionRoute
open SondowProjectBigNParameterClosureAudit
open SondowProjectBigNGrowthObligationAudit
open SondowProjectBigNAxiomatizedSubmissionRoute
open Filter Asymptotics

universe u v w q

/-!
This audit file fixes the lower-bound boundary:

* `tail_gap` is a field of the clean checker input package;
* the clean search input is built from that field;
* the displayed computed-`N` formula reads the same field;
* downstream clean axiom profiles therefore audit the abstract interface, not
  an unconditional derivation of the Pudlak lower bound.
-/

/-- The clean singleton tail-gap input literally stores the tail-gap certificate. -/
def tailGapInput_tail_gap_is_field
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput
        scale_data) :
    ComputableGapCertificate
      (fun n : Nat => (input.lengthCodeAt n : Real)) :=
  input.tail_gap

/-- The search-gap package used downstream is obtained from the stored tail gap. -/
theorem tailGapInput_toSearchInput_gap_eq_tail_gap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput
        scale_data) :
    input.toSearchInput.gap =
      input.tail_gap.toComputableSearchGapCertificate :=
  rfl

/--
The clean computed-`N` formula reads `input.tail_gap`; the threshold is not
constructed inside this theorem from checker/extractor/exactness.
-/
theorem cleanComputedN_formula_reads_tail_gap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput
        scale_data)
    (upper_provider :
      input.toSearchInput.toProofLengthFreeMonth12Candidate.checkedMeasuredUpperProviderType)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
      upper_provider).computedCollisionNOfRationality hrat =
      max
        (checkedSearchUpperTail
          input.toSearchInput.toProofLengthFreeMonth12Candidate
          upper_provider hrat).upperN
        (input.tail_gap.gap_for_polynomial_upper
          (checkedSearchUpperTail
            input.toSearchInput.toProofLengthFreeMonth12Candidate
            upper_provider hrat).U
          (checkedSearchUpperTail
            input.toSearchInput.toProofLengthFreeMonth12Candidate
            upper_provider hrat).polynomial).threshold :=
  ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput.computedCollisionN_eq_tailGapMax
    input upper_provider hrat

/--
The frontier route removes the raw input from the theorem surface, but the
frontier still carries a tail-gap certificate.
-/
def frontier_tail_gap_is_field
    {scale_data : InternalPudlakTheorem5ScaleData}
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {n : Nat}
    {Ax : L.BoundedFormula α n → Prop}
    {A B : Nat → L.BoundedFormula α n}
    (frontier :
      Month9Month10TimeBoundCanonicalConjIntroTargetTailGapFrontier
        scale_data (Ax := Ax) (A := A) (B := B)) :
    ComputableGapCertificate
      (fun m : Nat =>
        (((frontier.left_family.conjIntro frontier.right_family)
          |>.rightConjElim
          |>.minCheckedCodeSize m) : Real)) :=
  frontier.tail_gap

/--
The lower-level construction theorem remains conditional on extractor and
proof-length exactness; it is not an unconditional source of the gap.
-/
theorem lowerGap_from_extractor_exactness_is_conditional
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker) :
    let core := extractor.toComputableFiniteSearchNoSmallCore exactness
    Nonempty
      (ComputableSearchGapCertificate
        (actualProofLengthMeasured core.scale_data)) :=
  (checkerExtractorExactness_to_actualProofLength_searchGap
    extractor exactness).1

/--
The next lower-bound target as a proposition: the actual theorem-5 measured
proof length has a computable search-gap certificate.

This is the object that must be produced upstream; moving `tail_gap` into a
larger input package is not a proof of this target.
-/
def ActualProofLengthSearchGapTarget
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  Nonempty
    (ComputableSearchGapCertificate
      (actualProofLengthMeasured scale_data))

/--
The stronger pointwise target used by the collision proof: the produced gap
computes, for every polynomial upper `U` and starting cutoff `N`, a witness
where `U` is strictly below actual proof length.
-/
def ActualProofLengthPointwiseSearchGapTarget
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  ∃ gap :
    ComputableSearchGapCertificate
      (actualProofLengthMeasured scale_data),
    ∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
      U ((gap.gap_for_polynomial_upper U hU).witness N) <
        actualProofLengthMeasured scale_data
          ((gap.gap_for_polynomial_upper U hU).witness N)

/-- A computable no-small-code core gives the exact next search-gap target. -/
theorem noSmallCore_to_actualProofLengthPointwiseSearchGapTarget
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q}) :
    ActualProofLengthPointwiseSearchGapTarget core.scale_data := by
  refine ⟨actualProofLengthGapOfComputableFiniteSearchNoSmallCore core, ?_⟩
  intro U hU N
  exact actualProofLengthGapOfComputableFiniteSearchNoSmallCore_strict_at_witness
    core U hU N

/--
Checker/extractor/exactness is the current upstream conditional route to the
next target.  The assumptions are still explicit theorem inputs.
-/
theorem checkerExtractorExactness_to_actualProofLengthPointwiseSearchGapTarget
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{q} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness checker) :
    let core := extractor.toComputableFiniteSearchNoSmallCore exactness
    ActualProofLengthPointwiseSearchGapTarget core.scale_data :=
  noSmallCore_to_actualProofLengthPointwiseSearchGapTarget
    (extractor.toComputableFiniteSearchNoSmallCore exactness)

/--
Under the current project-level root semantics, PA/symbol-size proof length on
the theorem-5 power-bound family is just the structural fallback code size:
`scale n + 12`.  This is a boundary probe, not a submission theorem.
-/
theorem actualProofLengthMeasured_currentRoot_eq_scale_add_twelve
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat) :
    actualProofLengthMeasured scale_data n =
      (scale_data.scale n : Real) + 12 := by
  rw [actualProofLengthMeasured, _root_.proof_length_eq_rootFormulaCodeSize]
  rw [InternalPudlakTheorem5ScaleData.powerBoundRawCode_eq_scaled_strengthened]
  simp [_root_.rootFormulaCodeSize, _root_.strengthenedPartialConsistencyCode,
    _root_.FormulaFamily.rootWeight, _root_.ProofSystem.rootWeight,
    _root_.ProofLengthMeasure.rootWeight, Nat.cast_add]
  ring

/--
Consequently, the current root `actualProofLengthMeasured` is polynomially
bounded because the theorem-5 scale is polynomially bounded.
-/
theorem actualProofLengthMeasured_currentRoot_polynomial
    (scale_data : InternalPudlakTheorem5ScaleData) :
    _root_.is_polynomial_bound (actualProofLengthMeasured scale_data) := by
  have hlin :
      _root_.is_polynomial_bound
        (fun n : Nat => (1 : Real) * (scale_data.scale n : Real) + 12) :=
    scale_data.scale_polynomial_bound.linear_rescale
      (C := 1) (D := 12) (by norm_num) (by norm_num)
  exact _root_.is_polynomial_bound_of_le
    (f := actualProofLengthMeasured scale_data)
    (g := fun n : Nat => (1 : Real) * (scale_data.scale n : Real) + 12)
    (by
      intro n
      rw [actualProofLengthMeasured_currentRoot_eq_scale_add_twelve]
      norm_num)
    hlin

/--
The actual proof-length search-gap target cannot be closed on the current root
fallback measurement: a polynomially bounded measured function cannot dominate
every polynomial upper bound.
-/
theorem no_actualProofLengthSearchGapTarget_currentRoot
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ActualProofLengthSearchGapTarget scale_data → False := by
  intro htarget
  rcases htarget with ⟨gap⟩
  exact no_computable_search_gap_of_polynomial_bound
    (actualProofLengthMeasured_currentRoot_polynomial scale_data) gap

/--
The stronger pointwise target is impossible for the same reason; it contains a
search-gap certificate for the current polynomially bounded root measurement.
-/
theorem no_actualProofLengthPointwiseSearchGapTarget_currentRoot
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ActualProofLengthPointwiseSearchGapTarget scale_data → False := by
  intro htarget
  rcases htarget with ⟨gap, _strict⟩
  exact no_computable_search_gap_of_polynomial_bound
    (actualProofLengthMeasured_currentRoot_polynomial scale_data) gap

/-- The linear function `n ↦ n + 1` is a polynomial bound. -/
theorem linear_succ_real_is_polynomial_bound :
    _root_.is_polynomial_bound (fun n : Nat => (n : Real) + 1) := by
  refine ⟨1, 1, ?_⟩
  intro n
  ring_nf
  exact le_rfl

/--
The final numeric-code residual route is internally inconsistent for the
all-polynomial lower-search target.  Taking `f(n)=n+1`, `cutoff_gt` forces the
chosen witness code itself below the cutoff; `scaleNoCollisionBelow` then says
that the witness scale is different from itself.
-/
theorem no_finalResidualInput_cutoffSelfCollision
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ConcretePAHilbertPowerBoundFinalResidualInput scale_data → False := by
  intro input
  let f : Nat → Real := fun n => (n : Real) + 1
  have hf : _root_.is_polynomial_bound f := by
    simpa [f] using linear_succ_real_is_polynomial_bound
  let w := input.witness f hf 0
  let K := input.cutoff f hf 0
  have hgt : (w : Real) + 1 < (K : Real) := by
    simpa [f, w, K] using input.cutoff_gt f hf 0
  have hw_lt_K_nat : w < K := by
    exact_mod_cast (lt_trans (lt_add_one (w : Real)) hgt)
  exact input.scaleNoCollisionBelow f hf 0 w hw_lt_K_nat rfl

/-- The by-index residual route is therefore impossible as well. -/
theorem no_finalByIndexResidualInput_cutoffSelfCollision
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ConcretePAHilbertPowerBoundFinalByIndexResidualInput scale_data → False := by
  intro input
  exact no_finalResidualInput_cutoffSelfCollision scale_data
    input.toFinalResidualInput

/-- The scale-injective by-index residual route is also impossible. -/
theorem no_finalScaleInjectiveByIndexResidualInput_cutoffSelfCollision
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ConcretePAHilbertPowerBoundFinalScaleInjectiveByIndexResidualInput
      scale_data → False := by
  intro input
  exact no_finalResidualInput_cutoffSelfCollision scale_data
    input.toFinalResidualInput

/-- The strict-scale by-index residual route is also impossible. -/
theorem no_finalStrictScaleByIndexResidualInput_cutoffSelfCollision
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
      scale_data → False := by
  intro input
  exact no_finalResidualInput_cutoffSelfCollision scale_data
    input.toFinalResidualInput

/-- The bounded strict-scale by-index residual route is also impossible. -/
theorem no_finalBoundedStrictScaleByIndexResidualInput_cutoffSelfCollision
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
      scale_data → False := by
  intro input
  exact no_finalResidualInput_cutoffSelfCollision scale_data
    input.toFinalResidualInput

/--
Generic rejection-extractor obstruction.  A checker-side Pudlak extractor can
exist only if the measured minimum accepted proof-code size is not already
polynomially bounded.

This opens the old proof-length-free route at its root: replacing `tail_gap`
by a `rejectionExtractor` is not a proof unless the extractor is backed by a
genuine super-polynomial minimum-proof-code theorem.  If the measured checker
minimum is polynomially bounded, the extractor itself generates a computable
search gap for that polynomially bounded function, contradicting
`no_computable_search_gap_of_polynomial_bound`.
-/
theorem no_checkerRejectionExtractor_of_checkedMeasured_polynomial
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (hpoly :
      _root_.is_polynomial_bound
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics)) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration →
      False := by
  intro extractor
  exact
    no_computable_search_gap_of_polynomial_bound hpoly
      (month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
        extractor.toComputableFiniteSearchExclusion)

/--
The same obstruction stated in the native checker notation:
`checker.minProofCodeSizeAt n` is the measured function used by the
proof-length-free endpoint.
-/
theorem no_checkerRejectionExtractor_of_minProofCodeSizeAt_polynomial
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration : InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (hpoly :
      _root_.is_polynomial_bound
        (fun n : Nat => (checker.minProofCodeSizeAt n : Real))) :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration →
      False := by
  have hmeasured :
      _root_.is_polynomial_bound
        (month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics) := by
    change
      _root_.is_polynomial_bound
        (fun n : Nat =>
          (checker.toProofCodeSemantics.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real))
    simpa [InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
      using hpoly
  exact
    no_checkerRejectionExtractor_of_checkedMeasured_polynomial
      (scale_data := scale_data) (checker := checker)
      (enumeration := enumeration) hmeasured

/--
Correct positive lower-search entry point: a calibrated four-piece checker
input gives a checked proof-code measured search gap directly, through
finite-search exclusion and without using the historical root `proof_length`
measurement.
-/
def calibratedFourPiece_checkedMeasuredSearchGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data) :
    ComputableSearchGapCertificate
      (month9_month10_checkedProofCodeMeasured
        scale_data input.checkerSemantics.toProofCodeSemantics) :=
  month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
    input.rejectionExtractor.toComputableFiniteSearchExclusion

/--
The checked-measured gap generated from a calibrated four-piece input uses the
executable rejection-search witness.  This is the non-`tail_gap` witness path.
-/
theorem calibratedFourPiece_checkedMeasuredSearchGap_witness_eq_rejectionSearch
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((calibratedFourPiece_checkedMeasuredSearchGap input)
      |>.gap_for_polynomial_upper U hU).witness N =
      input.rejection_search.witness U hU N :=
  rfl

/--
This names the remaining real closure target: construct a calibrated
four-piece input with size-filtered finite enumeration and executable rejection
search.  Once supplied, the checked proof-code search gap is produced by Lean.
-/
def SizeFilteredNoSmallClosureTarget
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  Nonempty (ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data)

theorem sizeFilteredNoSmallClosureTarget_to_checkedMeasuredSearchGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (target : SizeFilteredNoSmallClosureTarget scale_data) :
    Nonempty
      (Σ input :
        ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data,
      ComputableSearchGapCertificate
        (month9_month10_checkedProofCodeMeasured
          scale_data input.checkerSemantics.toProofCodeSemantics)) := by
  rcases target with ⟨input⟩
  exact ⟨⟨input, calibratedFourPiece_checkedMeasuredSearchGap input⟩⟩

/--
Sharper proof-length-free entry point: size-filtered finite enumeration plus an
executable rejection search already gives the checked proof-code measured
search gap.  No proof-length exactness field is involved here.
-/
def calibratedRejectionSearch_checkedMeasuredSearchGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (rejection_search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    ComputableSearchGapCertificate
      (month9_month10_checkedProofCodeMeasured
        scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics) :=
  month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
    rejection_search.toCheckerExtractor.toComputableFiniteSearchExclusion

theorem calibratedRejectionSearch_checkedMeasuredSearchGap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (rejection_search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((calibratedRejectionSearch_checkedMeasuredSearchGap rejection_search)
      |>.gap_for_polynomial_upper U hU).witness N =
      rejection_search.witness U hU N :=
  rfl

/--
For the calibrated PA/Hilbert checker, saying that every accepted proof code
for the theorem-5 target has calibrated size above `U n` is equivalent to
saying that the checked measured minimum proof-code size is above `U n`.
-/
theorem calibratedAcceptedCodeSizeLowerBound_iff_checkedMeasured_gt
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (U : Nat → Real) (n : Nat) :
    (∀ code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode n) code →
        U n < (lengthCodeAt code : Real)) ↔
      U n <
        month9_month10_checkedProofCodeMeasured
          scale_data
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data lengthCodeAt).toProofCodeSemantics n := by
  let checkerSem :=
    concretePAHilbertPowerBoundCalibratedCheckerSemantics
      scale_data lengthCodeAt
  let sem := checkerSem.toProofCodeSemantics
  constructor
  · intro hall
    have hhas :
        sem.HasProofCodeOfSize
          (scale_data.powerBoundRawCode n)
          (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩) :=
      sem.hasProofCodeOfSize_minProofCodeSize
        (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩
    rcases hhas with ⟨code, hchecks, hsize_le⟩
    have haccepted :
        PAHilbertAcceptedProofCodeForFormulaCode
          (concretePAHilbertPowerBoundChecker scale_data)
          (scale_data.powerBoundRawCode n) code := by
      simpa [sem, checkerSem,
        InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
        concretePAHilbertPowerBoundCalibratedCheckerSemantics] using hchecks
    have hlt_size : U n < (lengthCodeAt code : Real) :=
      hall code haccepted
    have hsize_le_min :
        (lengthCodeAt code : Real) ≤
          (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) := by
      exact_mod_cast hsize_le
    have hlt_min :
        U n <
          (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) :=
      lt_of_lt_of_le hlt_size hsize_le_min
    simpa [month9_month10_checkedProofCodeMeasured, sem, checkerSem] using
      hlt_min
  · intro hmin code haccepted
    have hchecks :
        sem.checks code (scale_data.powerBoundRawCode n) := by
      simpa [sem, checkerSem,
        InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
        concretePAHilbertPowerBoundCalibratedCheckerSemantics] using haccepted
    have hhas :
        sem.HasProofCodeOfSize
          (scale_data.powerBoundRawCode n) (lengthCodeAt code) := by
      refine ⟨code, hchecks, ?_⟩
      simp [sem, checkerSem,
        InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
        concretePAHilbertPowerBoundCalibratedCheckerSemantics]
    have hmin_le :
        sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ ≤
          lengthCodeAt code :=
      sem.minProofCodeSize_le_of_hasProofCodeOfSize
        (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩ hhas
    have hmin' :
        U n <
          (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) := by
      simpa [month9_month10_checkedProofCodeMeasured, sem, checkerSem] using
        hmin
    have hmin_le_real :
        (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
          (lengthCodeAt code : Real) := by
      exact_mod_cast hmin_le
    exact lt_of_lt_of_le hmin' hmin_le_real

/--
Expanded no-small-code content of the calibrated executable rejection search:
at the selected witness, the checked measured minimum proof-code size is
strictly above the polynomial upper value.
-/
theorem calibratedRejectionSearch_checkedMeasured_gt_at_witness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (rejection_search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    U (rejection_search.witness U hU N) <
      month9_month10_checkedProofCodeMeasured
        scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics
        (rejection_search.witness U hU N) := by
  have hstrict :=
    (calibratedRejectionSearch_checkedMeasuredSearchGap rejection_search
      |>.gap_for_polynomial_upper U hU).strict_at_witness N
  rw [calibratedRejectionSearch_checkedMeasuredSearchGap_witness_eq
    rejection_search U hU N] at hstrict
  exact hstrict

/--
The same lower-bound content stated directly over concrete accepted proof
codes: at the selected witness, every PA/Hilbert code accepted for the target
formula has calibrated size strictly above the polynomial upper value.
-/
theorem calibratedRejectionSearch_acceptedCodeSize_gt_at_witness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (rejection_search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat)
    (code : Nat)
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode
          (rejection_search.witness U hU N))
        code) :
    U (rejection_search.witness U hU N) <
      (lengthCodeAt code : Real) := by
  let w := rejection_search.witness U hU N
  have hchecked :
      U w <
        month9_month10_checkedProofCodeMeasured
          scale_data
          (concretePAHilbertPowerBoundCalibratedCheckerSemantics
            scale_data lengthCodeAt).toProofCodeSemantics w := by
    simpa [w] using
      calibratedRejectionSearch_checkedMeasured_gt_at_witness
        rejection_search U hU N
  have hall :=
    (calibratedAcceptedCodeSizeLowerBound_iff_checkedMeasured_gt
      scale_data lengthCodeAt U w).mpr hchecked
  exact hall code haccepted

/--
The size-filtered rejection-search package builds the canonical
proof-length-free PA/Hilbert search core.  This closes the adapter layer from
the executable checker search to the Month 12 proof-length-free endpoint; it
does not construct the rejection search itself.
-/
def calibratedRejectionSearch_toCanonicalSearchCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (rejection_search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    PAHilbertCanonicalSearchCore where
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
    rejection_search.toCheckerExtractor
  acceptedCodeExactness := by
    intro formulaCode code haccepted
    exact
      (concretePAHilbertPowerBoundCanonicalCheckerInterface scale_data)
        |>.accepted_decoded_code_to_formulaCode_derivable
          formulaCode code haccepted

/--
The canonical core generated from the size-filtered rejection search preserves
the executable witness exactly.
-/
theorem calibratedRejectionSearch_toCanonicalSearchCore_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (rejection_search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (calibratedRejectionSearch_toCanonicalSearchCore
      rejection_search).rejectionExtractor.witness U hU N =
        rejection_search.witness U hU N :=
  rfl

/--
For the concrete powerBound checker, the executable Boolean sweep
`RejectsBelow n K = true` is exactly the semantic statement that no numeric
proof code below `K` is accepted for the target theorem-5 formula.

This opens the Boolean part of the lower-bound box: the rejection sweep is not
an opaque parameter once reduced to the concrete checker.
-/
theorem concretePAHilbertPowerBoundRejectsBelow_iff_noAcceptedBelow
    {scale_data : InternalPudlakTheorem5ScaleData}
    {n K : Nat} :
    concretePAHilbertPowerBoundRejectsBelow scale_data n K = true ↔
      ∀ code : Nat, code < K →
        ¬ PAHilbertAcceptedProofCodeForFormulaCode
          (concretePAHilbertPowerBoundChecker scale_data)
          (scale_data.powerBoundRawCode n) code := by
  constructor
  · intro hrejects code hcode_lt
    exact
      concretePAHilbertPowerBound_rejectsCode_to_not_acceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundRejectsBelow_sound
          hrejects hcode_lt)
  · intro hno
    exact
      concretePAHilbertPowerBoundRejectsBelow_of_forall_lt
        (by
          intro code hcode_lt
          let formula :=
            PAHilbertFormula.ofFormulaCode
              (scale_data.powerBoundRawCode n)
          by_cases hmatch :
              (concretePAHilbertPowerBoundProofObject
                scale_data code).conclusion.code = formula.code
          · by_cases hrec :
                concretePAHilbertTheorem5AxiomRecognizer.recognizesAny
                  formula = true
            · have haccepted :
                  PAHilbertAcceptedProofCodeForFormulaCode
                    (concretePAHilbertPowerBoundChecker scale_data)
                    (scale_data.powerBoundRawCode n) code := by
                refine ⟨concretePAHilbertPowerBoundProofObject
                    scale_data code, ?_, ?_, ?_⟩
                · rfl
                · simpa [formula, PAHilbertFormula.ofFormulaCode] using
                    hmatch
                · have hconclusion_eq :
                      (concretePAHilbertPowerBoundProofObject
                        scale_data code).conclusion = formula :=
                    PAHilbertFormula.eq_of_code_eq hmatch
                  have hrec_conclusion :
                      concretePAHilbertTheorem5AxiomRecognizer.recognizesAny
                        (concretePAHilbertPowerBoundProofObject
                          scale_data code).conclusion = true := by
                    simpa [hconclusion_eq] using hrec
                  simpa [concretePAHilbertPowerBoundChecker,
                    concretePAHilbertPowerBoundProofObject,
                    hrec_conclusion]
              exact False.elim ((hno code hcode_lt) haccepted)
            · simp [concretePAHilbertPowerBoundChecker, formula,
                hmatch, hrec]
          · exact
              concretePAHilbertPowerBoundChecker_rejectsCode_of_formulaCode_ne
                hmatch)

/--
Prop-level version of the calibrated executable lower-search input.  It
replaces the Boolean `rejectsBelowCodeBound` field by the semantic statement
that there is no accepted proof code below the enumerating numeric code bound.
-/
structure ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
    (scale_data : InternalPudlakTheorem5ScaleData)
    (lengthCodeAt : Nat → Nat)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt) : Type where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  noAcceptedBelowCodeBound :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      ∀ code : Nat,
        code <
          enumeration.codeBound
            (witness f hf N) (cutoff f hf N) →
          ¬ PAHilbertAcceptedProofCodeForFormulaCode
            (concretePAHilbertPowerBoundChecker scale_data)
            (scale_data.powerBoundRawCode (witness f hf N)) code

/--
The executable Boolean `rejection_search` always exposes a no-accepted-code
search at the same witness and cutoff.
-/
def calibratedRejectionSearch_toNoAcceptedCodeSearch
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (rejection_search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
      scale_data lengthCodeAt enumeration where
  witness := rejection_search.witness
  cutoff := rejection_search.cutoff
  witness_ge := rejection_search.witness_ge
  cutoff_gt := rejection_search.cutoff_gt
  noAcceptedBelowCodeBound := by
    intro f hf N code hcode_lt
    exact
      (concretePAHilbertPowerBoundRejectsBelow_iff_noAcceptedBelow).mp
        (rejection_search.rejectsBelowCodeBound f hf N)
        code hcode_lt

/--
Conversely, for the concrete powerBound checker, the Prop-level no-accepted-code
search reconstructs the executable Boolean `rejection_search`.
-/
def calibratedNoAcceptedCodeSearch_toRejectionSearch
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
        scale_data lengthCodeAt enumeration) :
    ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
      scale_data lengthCodeAt enumeration where
  witness := search.witness
  cutoff := search.cutoff
  witness_ge := search.witness_ge
  cutoff_gt := search.cutoff_gt
  rejectsBelowCodeBound := by
    intro f hf N
    exact
      (concretePAHilbertPowerBoundRejectsBelow_iff_noAcceptedBelow).mpr
        (search.noAcceptedBelowCodeBound f hf N)

/--
The two lower-search formulations have the same witness.
-/
theorem calibratedRejectionSearch_toNoAcceptedCodeSearch_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (rejection_search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (calibratedRejectionSearch_toNoAcceptedCodeSearch
      rejection_search).witness U hU N =
        rejection_search.witness U hU N :=
  rfl

/--
The Prop-level no-accepted-code search reconstructs a checked-measured search
gap through the Boolean rejection search, without adding any `tail_gap` input.
-/
def calibratedNoAcceptedCodeSearch_checkedMeasuredSearchGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
        scale_data lengthCodeAt enumeration) :
    ComputableSearchGapCertificate
      (month9_month10_checkedProofCodeMeasured
        scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics) :=
  calibratedRejectionSearch_checkedMeasuredSearchGap
    (calibratedNoAcceptedCodeSearch_toRejectionSearch search)

/--
The checked-measured gap generated from the Prop-level no-accepted-code search
uses the same witness.
-/
theorem calibratedNoAcceptedCodeSearch_checkedMeasuredSearchGap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
        scale_data lengthCodeAt enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((calibratedNoAcceptedCodeSearch_checkedMeasuredSearchGap search)
      |>.gap_for_polynomial_upper U hU).witness N =
      search.witness U hU N :=
  rfl

/--
Any Prop-level no-accepted-code search must put its cutoff below the calibrated
length of the canonical accepted code at its witness.  Otherwise finite
enumeration completeness would place the canonical code `witness` inside the
rejected code interval.
-/
theorem calibratedNoAcceptedCodeSearch_cutoff_le_canonicalLength
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
        scale_data lengthCodeAt enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    search.cutoff U hU N ≤
      lengthCodeAt (search.witness U hU N) := by
  let w := search.witness U hU N
  let K := search.cutoff U hU N
  have hnot_small : ¬ lengthCodeAt w < K := by
    intro hsize_lt
    have haccepted :
        PAHilbertAcceptedProofCodeForFormulaCode
          (concretePAHilbertPowerBoundChecker scale_data)
          (scale_data.powerBoundRawCode w) w :=
      concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
        scale_data w
    have hcode_lt :
        w < enumeration.codeBound w K :=
      enumeration.complete_code_lt_bound w K w haccepted hsize_lt
    exact
      (search.noAcceptedBelowCodeBound U hU N w
        (by simpa [w, K] using hcode_lt))
        (by simpa [w] using haccepted)
  exact le_of_not_gt hnot_small

/--
Consequently, at the witness selected by any no-accepted-code search, the
polynomial upper is already below the canonical accepted code's calibrated
length.
-/
theorem calibratedNoAcceptedCodeSearch_polynomialUpper_lt_canonicalLength
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (search :
      ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
        scale_data lengthCodeAt enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    U (search.witness U hU N) <
      (lengthCodeAt (search.witness U hU N) : Real) := by
  have hle :
      (search.cutoff U hU N : Real) ≤
        (lengthCodeAt (search.witness U hU N) : Real) := by
    exact_mod_cast
      calibratedNoAcceptedCodeSearch_cutoff_le_canonicalLength
        search U hU N
  exact lt_of_lt_of_le (search.cutoff_gt U hU N) hle

/--
If the canonical calibrated length `n ↦ lengthCodeAt n` is polynomially
bounded, then no all-polynomial no-accepted-code search can exist.  Taking
`U(n) = lengthCodeAt(n) + 1` forces the contradiction
`lengthCodeAt(w) + 1 < lengthCodeAt(w)`.
-/
theorem no_calibratedNoAcceptedCodeSearch_of_canonicalLength_polynomial
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    {enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt}
    (hpoly :
      _root_.is_polynomial_bound
        (fun n : Nat => (lengthCodeAt n : Real)))
    (search :
      ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
        scale_data lengthCodeAt enumeration) :
    False := by
  let U : Nat → Real := fun n => (lengthCodeAt n : Real) + 1
  have hU : _root_.is_polynomial_bound U := by
    have hlin :=
      hpoly.linear_rescale (C := 1) (D := 1)
        (by norm_num) (by norm_num)
    simpa [U] using hlin
  have hlt :=
    calibratedNoAcceptedCodeSearch_polynomialUpper_lt_canonicalLength
      search U hU 0
  let w := search.witness U hU 0
  change (lengthCodeAt w : Real) + 1 < (lengthCodeAt w : Real) at hlt
  nlinarith

/--
Audit target for the tempting but impossible variant where the calibrated
canonical length is still polynomially bounded.
-/
structure SizeFilteredNoAcceptedCodeSearchPolynomialLengthWitness
    (scale_data : InternalPudlakTheorem5ScaleData) : Type where
  lengthCodeAt : Nat → Nat
  canonicalLength_polynomial :
    _root_.is_polynomial_bound
      (fun n : Nat => (lengthCodeAt n : Real))
  enumeration :
    ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
      scale_data lengthCodeAt
  search :
    ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
      scale_data lengthCodeAt enumeration

def SizeFilteredNoAcceptedCodeSearchPolynomialLengthTarget
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  Nonempty
    (SizeFilteredNoAcceptedCodeSearchPolynomialLengthWitness scale_data)

theorem no_sizeFilteredNoAcceptedCodeSearchPolynomialLengthTarget
    (scale_data : InternalPudlakTheorem5ScaleData) :
    SizeFilteredNoAcceptedCodeSearchPolynomialLengthTarget scale_data →
      False := by
  intro target
  rcases target with ⟨pkg⟩
  exact
    no_calibratedNoAcceptedCodeSearch_of_canonicalLength_polynomial
      pkg.canonicalLength_polynomial pkg.search

/-- The identity numeric-code size is polynomially bounded. -/
theorem nativeIdentityLength_polynomial :
    _root_.is_polynomial_bound (fun n : Nat => (n : Real)) := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp

/--
Native numeric-code semantics has an explicit accepted proof code `n` for
`powerBoundRawCode n`, so its checked measured minimum is at most `n`.
-/
theorem nativePowerBoundCheckedMeasured_le_index
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat) :
    month9_month10_checkedProofCodeMeasured scale_data
        (concretePAHilbertPowerBoundCheckerSemantics
          scale_data).toProofCodeSemantics n ≤
      (n : Real) := by
  have hnat :
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
        (concretePAHilbertPowerBoundCheckerSemantics scale_data) n ≤ n :=
    concretePAHilbertPowerBound_minProofCodeSizeAt_le_self scale_data n
  simpa [month9_month10_checkedProofCodeMeasured,
    InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt] using
    (show
      ((concretePAHilbertPowerBoundCheckerSemantics
        scale_data).toProofCodeSemantics.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
        (n : Real) by
        exact_mod_cast hnat)

/--
PA/Hilbert-level obstruction: the current concrete power-bound checker already
has an accepted numeric proof code `n` for `powerBoundRawCode n`.  Therefore no
claim saying that all accepted proof codes below `n+1` are absent can hold.
-/
theorem no_concretePAHilbertPowerBound_noSmallAccepted_at_succ
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat) :
    PAHilbertNoSmallAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode n) (n + 1) →
      False := by
  intro hno
  exact hno n (Nat.lt_succ_self n)
    (concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
      scale_data n)

/--
The same obstruction stated at the decoded proof-object level.  The decoded
accepted proof object for code `n` lies below the bound `n+1`, so the
formula-code no-small-proof predicate is impossible for the current concrete
power-bound checker.
-/
theorem no_concretePAHilbertPowerBound_noSmallProofCodeForFormulaCode_at_succ
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat) :
    PAHilbertNoSmallProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode n) (n + 1) →
      False := by
  intro hno
  rcases
    concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
      scale_data n with
    ⟨proof, hdecode, hconclusion, haccepts⟩
  have hproofCode : proof.code = n :=
    (concretePAHilbertPowerBoundChecker scale_data).decoder.decodedCode_eq
      n proof hdecode
  have hlt : proof.code < n + 1 := by
    simp [hproofCode]
  have hfalse := hno proof hlt hconclusion
  rw [haccepts] at hfalse
  cases hfalse

/--
Therefore the native checked measured object for the current concrete
powerBound checker is polynomially bounded.
-/
theorem nativePowerBoundCheckedMeasured_polynomial
    (scale_data : InternalPudlakTheorem5ScaleData) :
    _root_.is_polynomial_bound
      (fun n : Nat =>
        month9_month10_checkedProofCodeMeasured scale_data
          (concretePAHilbertPowerBoundCheckerSemantics
            scale_data).toProofCodeSemantics n) :=
  _root_.is_polynomial_bound_of_le
    (f := fun n : Nat =>
      month9_month10_checkedProofCodeMeasured scale_data
        (concretePAHilbertPowerBoundCheckerSemantics
          scale_data).toProofCodeSemantics n)
    (g := fun n : Nat => (n : Real))
    (nativePowerBoundCheckedMeasured_le_index scale_data)
    nativeIdentityLength_polynomial

/--
The native numeric-code checker cannot carry the all-polynomial Pudlak
search-gap.  The obstruction is not a missing wrapper: the checker already has a
canonical accepted proof code of size at most `n`.
-/
theorem no_nativePowerBoundCheckedMeasuredSearchGap
    (scale_data : InternalPudlakTheorem5ScaleData) :
    Nonempty
        (ComputableSearchGapCertificate
          (fun n : Nat =>
            month9_month10_checkedProofCodeMeasured scale_data
              (concretePAHilbertPowerBoundCheckerSemantics
                scale_data).toProofCodeSemantics n)) →
      False := by
  intro hgap
  rcases hgap with ⟨gap⟩
  exact no_computable_search_gap_of_polynomial_bound
    (nativePowerBoundCheckedMeasured_polynomial scale_data) gap

/--
Specialized no-accepted-code obstruction for the calibrated checker when its
calibrated size is the native numeric-code size `id`.
-/
def NativeIdentityNoAcceptedCodeSearchTarget
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  Nonempty
    (Σ enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data (fun n : Nat => n),
      ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
        scale_data (fun n : Nat => n) enumeration)

theorem no_nativeIdentityNoAcceptedCodeSearchTarget
    (scale_data : InternalPudlakTheorem5ScaleData) :
    NativeIdentityNoAcceptedCodeSearchTarget scale_data → False := by
  intro htarget
  rcases htarget with ⟨enumeration, search⟩
  exact
    no_calibratedNoAcceptedCodeSearch_of_canonicalLength_polynomial
      (scale_data := scale_data)
      (lengthCodeAt := fun n : Nat => n)
        (enumeration := enumeration)
        nativeIdentityLength_polynomial
        search

/--
Corrected root target for the lower-bound side after the current concrete
PA/Hilbert power-bound checker has been ruled out.  This target uses the
canonical CnBox PA box, whose length is the semantic minimum PA proof-object
size for the finite-consistency formula family.
-/
def CorrectedCanonicalCnBoxLowerBoundClosureTarget : Prop :=
  Nonempty
    (Σ lower_source :
      BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource,
      BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        lower_source)

/--
The corrected canonical PA box measures the semantic PA proof length of the
finite-consistency formula family, not the rejected one-line native checker.
-/
theorem correctedCanonicalCnBoxPABox_length_eq_semanticFiniteConsistency
    (n : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalCnBoxPABox.length n =
      BoundedArithmeticLab.semanticBAProofLength
        BoundedArithmeticLab.PAAxiom
        BoundedArithmeticLab.finiteConsistencyFormula n := by
  rfl

/--
Once a Buss/Pudlak lower source is calibrated to the canonical CnBox target by
semantic relabeling, the canonical proof-length gap follows mechanically.
-/
theorem correctedCanonicalCnBoxLowerBoundClosureTarget_to_gap :
    CorrectedCanonicalCnBoxLowerBoundClosureTarget →
      BoundedArithmeticLab.BoundedProofPredicate.CanonicalCnBoxProofLengthGap := by
  intro htarget
  rcases htarget with ⟨⟨lower_source, calibration⟩⟩
  exact
    BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration.toProofLengthGap
      (lower_source := lower_source) calibration

/--
The same corrected target, stated as the `EventualLowerBound` consumed by the
collision kernel.
-/
theorem correctedCanonicalCnBoxLowerBoundClosureTarget_to_eventualLowerBound :
    CorrectedCanonicalCnBoxLowerBoundClosureTarget →
      BoundedArithmeticLab.EventualLowerBound
        BoundedArithmeticLab.BoundedProofPredicate.canonicalCnBoxPABox := by
  intro htarget
  exact
    (BoundedArithmeticLab.BoundedProofPredicate.proofLengthGap_iff_eventualLowerBound
        BoundedArithmeticLab.BoundedProofPredicate.canonicalCnBoxPABox).1
      (correctedCanonicalCnBoxLowerBoundClosureTarget_to_gap htarget)

/--
Exact constructor equality is not the right closure route for the canonical
CnBox target: the external Pudlak constructor and the partial-consistency
constructor are intentionally distinct.  The viable corrected route is semantic
relabeling plus length equality.
-/
theorem no_correctedCanonicalExactConstructorCalibration
    (lower_source :
      BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource) :
    ¬ BoundedArithmeticLab.BoundedProofPredicate.CanonicalExternalPudlakCalibration
      lower_source :=
  BoundedArithmeticLab.BoundedProofPredicate.not_canonicalExternalPudlakCalibration
    lower_source

/-- The bounded sidecar polynomial-bound predicate has the same numeric shape
as the root predicate, so a bounded polynomial upper can be used against the
root literature lower-bound theorem. -/
theorem boundedPolynomialBound_to_rootPolynomialBound
    {f : Nat → Real} :
    BoundedArithmeticLab.IsPolynomialBound f →
      _root_.is_polynomial_bound f := by
  intro hf
  rcases hf with ⟨c, k, hck⟩
  exact ⟨c, k, hck⟩

/-- Minimal carrier for the bounded sidecar theory conditions when the actual
mathematical lower bound is supplied by the root literature theorem.  This is
not a formalization of the metatheory fields: the proposition-valued fields are
recorded as `True`; the real growth content is carried by the lower-bound field
below. -/
def boundedPALiteratureTheoryConditions :
    BoundedArithmeticLab.BussPudlakTheoryConditions where
  system := BoundedArithmeticLab.ProofSystem.PA
  measure := BoundedArithmeticLab.ProofLengthMeasure.symbolSize
  system_eq_pa := rfl
  measure_eq_symbolSize := rfl
  consistent_statement := True
  consistent := trivial
  axiomatizable_statement := True
  axiomatizable := trivial
  axioms_polytime_recognizable_statement := True
  axioms_polytime_recognizable := trivial
  contains_bounded_arithmetic_statement := True
  contains_bounded_arithmetic := trivial
  efficient_metamathematics_statement := True
  efficient_metamathematics := trivial
  efficient_proof_coding_statement := True
  efficient_proof_coding := trivial
  binary_numerals_log_size_statement := True
  binary_numerals_log_size := trivial

def boundedTimeConstructibleScaleOfRoot
    (scale : Nat → Nat) : BoundedArithmeticLab.TimeConstructibleScale where
  scale := scale
  time_constructible_statement := True
  time_constructible := trivial
  eventually_reads_input_statement := True
  eventually_reads_input := trivial
  eventually_defined_statement := True
  eventually_defined := trivial
  dominates_input_length_statement := True
  dominates_input_length := trivial

def boundedTheorem5ConditionsOfRootScale
    (scale : Nat → Nat) :
    BoundedArithmeticLab.BussPudlakTheorem5Conditions where
  theory := boundedPALiteratureTheoryConditions
  scale_data := boundedTimeConstructibleScaleOfRoot scale
  exponent_c := 1
  exponent_c_pos := by norm_num
  epsilon := 1
  epsilon_pos := by norm_num

/--
Convert a root strong rescaled Pudlak lower-bound theorem into the bounded
sidecar lower-source interface.  This does not prove the literature theorem;
it removes one layer of abstract `lower_source` packaging by reading the root
strong lower bound directly as the bounded `EventualLowerBound`.
-/
noncomputable def boundedLowerSourceOfRootStrongRescaled
    (raw : Nat → _root_.FormulaCode) (scale : Nat → Nat)
    (hlower :
      _root_.StrongRescaledExternalStrengthenedLowerBound raw scale) :
    BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource where
  conditions := boundedTheorem5ConditionsOfRootScale scale
  pa_length := fun n : Nat =>
    _root_.proof_length _root_.ProofSystem.PA
      _root_.ProofLengthMeasure.symbolSize
      (_root_.rescaledExternalStrengthenedLowerBoundCode raw scale n)
  lower_bound := by
    refine ⟨?_⟩
    intro f hf N
    exact
      (Filter.frequently_atTop.mp
        (hlower.frequently_beats_every_polynomial f
          (boundedPolynomialBound_to_rootPolynomialBound hf))) N

/--
The bounded sidecar lower source obtained from the current root literature
Pudlak theorem-5 axioms.
-/
noncomputable def boundedLowerSourceFromRootLiterature :
    BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource :=
  boundedLowerSourceOfRootStrongRescaled
    _root_.literaturePudlakTheorem5ExternalScaleData.rawCode
    _root_.literaturePudlakTheorem5ExternalScaleData.scale
    _root_.literaturePudlakTheorem5ExternalRescaledLowerBound

theorem boundedLowerSourceFromRootLiterature_scale_eq :
    boundedLowerSourceFromRootLiterature.conditions.scale_data.scale =
      _root_.literaturePudlakTheorem5ExternalScaleData.scale := by
  rfl

theorem boundedLowerSourceFromRootLiterature_pa_length_eq
    (n : Nat) :
    boundedLowerSourceFromRootLiterature.pa_length n =
      _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.rescaledExternalStrengthenedLowerBoundCode
          _root_.literaturePudlakTheorem5ExternalScaleData.rawCode
          _root_.literaturePudlakTheorem5ExternalScaleData.scale n) := by
  rfl

/--
After the lower source has been built from the root literature theorem, the
remaining corrected CnBox closure obligation is only the semantic relabeling
calibration from that concrete source to the canonical CnBox PA length.
-/
def RootLiteratureCanonicalCnBoxCalibrationTarget : Prop :=
  Nonempty
    (BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
      boundedLowerSourceFromRootLiterature)

theorem rootLiteratureCanonicalCalibration_to_correctedClosureTarget :
    RootLiteratureCanonicalCnBoxCalibrationTarget →
      CorrectedCanonicalCnBoxLowerBoundClosureTarget := by
  intro htarget
  rcases htarget with ⟨calibration⟩
  exact ⟨⟨boundedLowerSourceFromRootLiterature, calibration⟩⟩

theorem rootLiteratureCanonicalCalibration_to_gap :
    RootLiteratureCanonicalCnBoxCalibrationTarget →
      BoundedArithmeticLab.BoundedProofPredicate.CanonicalCnBoxProofLengthGap := by
  intro calibration
  exact correctedCanonicalCnBoxLowerBoundClosureTarget_to_gap
    (rootLiteratureCanonicalCalibration_to_correctedClosureTarget calibration)

/--
A measured proof-length family that is itself polynomially bounded cannot also
be a strong Pudlak lower-bound family.  The lower-bound assertion may be tested
against the measured function itself.
-/
theorem no_strongProofLengthLowerBound_of_currentMeasuredPolynomial
    {T : _root_.ProofSystem} {measure : _root_.ProofLengthMeasure}
    {φ : Nat → _root_.FormulaCode}
    (hpoly :
      _root_.is_polynomial_bound
        (fun n : Nat => _root_.proof_length T measure (φ n))) :
    _root_.StrongProofLengthLowerBound T measure φ → False := by
  intro hlower
  have hfreq :=
    hlower.frequently_beats_every_polynomial
      (fun n : Nat => _root_.proof_length T measure (φ n)) hpoly
  rw [Filter.frequently_atTop] at hfreq
  rcases hfreq 0 with ⟨n, _hn_ge, hgt⟩
  exact (lt_irrefl (_root_.proof_length T measure (φ n))) hgt

/--
Current-root no-go for the theorem-5 power-bound lower-bound assertion itself.

Under the present project root, `proof_length(PA, symbolSize,
scale_data.powerBoundRawCode n)` is definitionally the structural formula-code
size `scale n + 12`, hence polynomially bounded.  It therefore cannot also be a
strong theorem-5 lower-bound family.
-/
theorem no_internalPudlakTheorem5PowerBoundLowerBound_currentRoot
    (scale_data : InternalPudlakTheorem5ScaleData) :
    scale_data.PowerBoundLowerBound → False := by
  intro hlower
  exact
    no_strongProofLengthLowerBound_of_currentMeasuredPolynomial
      (T := _root_.ProofSystem.PA)
      (measure := _root_.ProofLengthMeasure.symbolSize)
      (φ := scale_data.powerBoundRawCode)
      (by
        change _root_.is_polynomial_bound
          (actualProofLengthMeasured scale_data)
        exact actualProofLengthMeasured_currentRoot_polynomial scale_data)
      hlower

/--
The abstract lower-bound core is already impossible on the current root
`proof_length`; its lower-bound field is exactly the impossible power-bound
lower-bound assertion above.
-/
theorem no_internalPudlakTheorem5LowerBoundCore_currentRoot :
    InternalPudlakTheorem5LowerBoundCore → False := by
  intro core
  exact no_internalPudlakTheorem5PowerBoundLowerBound_currentRoot
    core.scale_data core.power_bound_lower_bound

theorem no_nonempty_internalPudlakTheorem5LowerBoundCore_currentRoot :
    Nonempty InternalPudlakTheorem5LowerBoundCore → False := by
  intro hcore
  rcases hcore with ⟨core⟩
  exact no_internalPudlakTheorem5LowerBoundCore_currentRoot core

/--
Any checked lower-bound core would map to the impossible lower-bound core under
the current root definition.
-/
theorem no_internalPudlakTheorem5CheckedLowerBoundCore_currentRoot :
    InternalPudlakTheorem5CheckedLowerBoundCore → False := by
  intro core
  exact no_internalPudlakTheorem5LowerBoundCore_currentRoot
    core.toLowerBoundCore

theorem no_internalPudlakTheorem5ProofCodeSemanticsCore_currentRoot :
    InternalPudlakTheorem5ProofCodeSemanticsCore.{q} → False := by
  intro core
  exact no_internalPudlakTheorem5LowerBoundCore_currentRoot
    core.toLowerBoundCore

theorem no_internalPudlakTheorem5ProofLengthCodeSemanticsCore_currentRoot :
    InternalPudlakTheorem5ProofLengthCodeSemanticsCore.{q} → False := by
  intro core
  exact no_internalPudlakTheorem5LowerBoundCore_currentRoot
    core.toLowerBoundCore

theorem no_internalPudlakTheorem5NoSmallCodeSemanticsCore_currentRoot :
    InternalPudlakTheorem5NoSmallCodeSemanticsCore.{q} → False := by
  intro core
  exact no_internalPudlakTheorem5LowerBoundCore_currentRoot
    core.toLowerBoundCore

theorem no_internalPudlakTheorem5FiniteSearchNoSmallCore_currentRoot :
    InternalPudlakTheorem5FiniteSearchNoSmallCore.{q} → False := by
  intro core
  exact no_internalPudlakTheorem5LowerBoundCore_currentRoot
    core.toLowerBoundCore

theorem no_internalPudlakTheorem5ComputableFiniteSearchNoSmallCore_currentRoot :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{q} → False := by
  intro core
  exact no_internalPudlakTheorem5LowerBoundCore_currentRoot
    core.toLowerBoundCore

/--
The most concrete Month 11-12 PA/Hilbert checker exactness core is also
impossible under the current root `proof_length`.  It projects to a theorem-5
computable finite-search/no-small-code core, and that core has already been
shown impossible for the formula-code-size root.
-/
theorem no_paHilbertCheckerExactnessCore_currentRoot :
    PAHilbertCheckerExactnessCore.{q} → False := by
  intro core
  exact no_internalPudlakTheorem5ComputableFiniteSearchNoSmallCore_currentRoot
    (PAHilbertCheckerExactnessCore_to_InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore
      core)

/--
Decoder-root no-go, independent of the project `proof_length`: the current
Month 11 checker interface asks the decoder to reconstruct every unrestricted
`PAHilbertProofObject` from its numeric code.  Since the proof-object type
admits distinct objects with the same code, that interface is uninhabitable.
-/
theorem no_paHilbertCheckerInterface_unrestrictedProofObjects
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics) :
    PAHilbertCheckerInterface checker semantics → False := by
  intro interface
  exact
    no_full_decoder_exactness_for_unrestricted_proof_objects checker
      interface.decoderExactness

/--
The current `PAHilbertCheckerExactnessCore` is therefore impossible even before
the root `proof_length` issue is considered: it contains the uninhabitable full
checker interface.
-/
theorem no_paHilbertCheckerExactnessCore_unrestrictedProofObjects :
    PAHilbertCheckerExactnessCore.{q} → False := by
  intro core
  exact
    no_paHilbertCheckerInterface_unrestrictedProofObjects
      core.checker core.semantics core.checkerInterface

/--
Named root-replacement target: a genuine PA/Hilbert checker exactness core.
This is the object that must be constructed only after replacing the current
formula-code-size root proof-length semantics.
-/
def RealPAHilbertRootReplacementTarget : Prop :=
  Nonempty PAHilbertCheckerExactnessCore.{q}

theorem no_realPAHilbertRootReplacementTarget_currentRoot :
    RealPAHilbertRootReplacementTarget.{q} → False := by
  intro htarget
  rcases htarget with ⟨core⟩
  exact no_paHilbertCheckerExactnessCore_currentRoot core

theorem no_realPAHilbertRootReplacementTarget_unrestrictedProofObjects :
    RealPAHilbertRootReplacementTarget.{q} → False := by
  intro htarget
  rcases htarget with ⟨core⟩
  exact no_paHilbertCheckerExactnessCore_unrestrictedProofObjects core

/--
Replacement decoder target: exactness is required only for canonical decoded
proof objects.  This is the root repair needed before a real PA/Hilbert checker
core can be constructed.
-/
structure PAHilbertCanonicalDecoderExactness
    (checker : PAHilbertChecker) : Type where
  IsCanonical : PAHilbertProofObject → Prop
  decodedCanonical :
    ∀ code : Nat,
      ∀ proof : PAHilbertProofObject,
        checker.decoder.decode code = some proof → IsCanonical proof
  decodeCanonical_complete :
    ∀ proof : PAHilbertProofObject,
      IsCanonical proof → checker.decoder.decode proof.code = some proof
  decodedCode_eq :
    ∀ code : Nat,
      ∀ proof : PAHilbertProofObject,
        checker.decoder.decode code = some proof → proof.code = code

/--
The concrete seed decoder already satisfies the corrected canonical decoder
interface.  This does not close theorem 5; it proves that the decoder-level
contradiction can be removed by changing the target interface rather than by
assuming an impossible full exactness statement.
-/
def concretePAHilbertSeedCanonicalDecoderExactness :
    PAHilbertCanonicalDecoderExactness concretePAHilbertSeedChecker where
  IsCanonical := ConcretePAHilbertCanonicalProofObject
  decodedCanonical := by
    intro code proof hdecode
    dsimp [concretePAHilbertSeedChecker] at hdecode
    cases hdecode
    rfl
  decodeCanonical_complete := by
    intro proof hcanonical
    dsimp [concretePAHilbertSeedChecker]
    exact concretePAHilbertProofObjectDecoder_complete_for_canonical
      proof hcanonical
  decodedCode_eq := by
    intro code proof hdecode
    dsimp [concretePAHilbertSeedChecker] at hdecode
    exact concretePAHilbertProofObjectDecoder_decodedCode_eq
      code proof hdecode

theorem concretePAHilbertSeedCanonicalDecoderExactness_nonempty :
    Nonempty
      (PAHilbertCanonicalDecoderExactness concretePAHilbertSeedChecker) :=
  ⟨concretePAHilbertSeedCanonicalDecoderExactness⟩

theorem rootLiteratureRescaledPudlak_currentRootLength_eq_scale_add_twelve
    (n : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.rescaledExternalStrengthenedLowerBoundCode
          _root_.literaturePudlakTheorem5ExternalScaleData.rawCode
          _root_.literaturePudlakTheorem5ExternalScaleData.scale n) =
      (_root_.literaturePudlakTheorem5ExternalScaleData.scale n : Real) + 12 := by
  rw [_root_.proof_length_eq_rootFormulaCodeSize]
  simp [_root_.rootFormulaCodeSize,
    _root_.rescaledExternalStrengthenedLowerBoundCode,
    _root_.LiteraturePudlakTheorem5ScaleData.rawCode,
    _root_.bussPudlakPAFiniteConsistencyRawCode,
    _root_.bussPudlakPAFiniteConsistencyDescriptor,
    _root_.LiteratureFiniteConsistencyDescriptor.toFormulaCode,
    _root_.pudlakStrengthenedFiniteConsistencyCode,
    _root_.strengthenedPartialConsistencyCode,
    _root_.FormulaFamily.rootWeight, _root_.ProofSystem.rootWeight,
    _root_.ProofLengthMeasure.rootWeight, Nat.cast_add]
  ring

theorem rootLiteratureRescaledPudlak_currentRootLength_polynomial :
    _root_.is_polynomial_bound
      (fun n : Nat =>
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.rescaledExternalStrengthenedLowerBoundCode
            _root_.literaturePudlakTheorem5ExternalScaleData.rawCode
            _root_.literaturePudlakTheorem5ExternalScaleData.scale n)) := by
  have hlin :
      _root_.is_polynomial_bound
        (fun n : Nat =>
          (1 : Real) *
              (_root_.literaturePudlakTheorem5ExternalScaleData.scale n : Real)
            + 12) :=
    _root_.literaturePudlakTheorem5ExternalScaleData.scale_polynomial_bound.linear_rescale
      (C := 1) (D := 12) (by norm_num) (by norm_num)
  exact _root_.is_polynomial_bound_of_le
    (f := fun n : Nat =>
      _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (_root_.rescaledExternalStrengthenedLowerBoundCode
          _root_.literaturePudlakTheorem5ExternalScaleData.rawCode
          _root_.literaturePudlakTheorem5ExternalScaleData.scale n))
    (g := fun n : Nat =>
      (1 : Real) *
          (_root_.literaturePudlakTheorem5ExternalScaleData.scale n : Real)
        + 12)
    (by
      intro n
      rw [rootLiteratureRescaledPudlak_currentRootLength_eq_scale_add_twelve]
      norm_num)
    hlin

/--
Root audit no-go: with the current root `proof_length` definition, the external
literature theorem-5 lower-bound axiom is incompatible with the same scale data.
The measured length is just `scale n + 12`, hence polynomially bounded.
-/
theorem no_literaturePudlakTheorem5ExternalRescaledLowerBound_currentRoot :
    ¬ _root_.StrongRescaledExternalStrengthenedLowerBound
      _root_.literaturePudlakTheorem5ExternalScaleData.rawCode
      _root_.literaturePudlakTheorem5ExternalScaleData.scale :=
  no_strongProofLengthLowerBound_of_currentMeasuredPolynomial
    rootLiteratureRescaledPudlak_currentRootLength_polynomial

theorem literaturePudlakTheorem5External_currentRoot_contradiction :
    False :=
  no_literaturePudlakTheorem5ExternalRescaledLowerBound_currentRoot
    _root_.literaturePudlakTheorem5ExternalRescaledLowerBound

/--
Current-root audit for the older external PA/Hilbert calibration bridge.

Under the present root `proof_length = rootFormulaCodeSize` convention, the
axiom `externalPAHilbertProofLength_eq_localChecked` cannot express a genuine
PA proof-length calibration: it forces the local checked-code proof length to
equal the structural formula-code size on every relevant code.
-/
theorem externalPAHilbertProofLength_eq_localChecked_forces_rootFormulaCodeSize
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {idx : Nat}
    {Ax : L.BoundedFormula α idx → Prop}
    {A B : Nat → L.BoundedFormula α idx}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp : _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (code : _root_.FormulaCode)
    (hcode : _root_.MiniHilbert.FormulaCodeHilbertRelevantCode code) :
    (interp.localCheckedCodeProofLength code : Real) =
      (_root_.rootFormulaCodeSize _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize code : Real) := by
  calc
    (interp.localCheckedCodeProofLength code : Real) =
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize code :=
          (_root_.MiniHilbert.externalPAHilbertProofLength_eq_localChecked
            interp code hcode).symm
    _ =
        (_root_.rootFormulaCodeSize _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize code : Real) :=
          _root_.proof_length_eq_rootFormulaCodeSize
            _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize code

theorem externalPAHilbertProofLength_eq_localChecked_forces_partialConsistency_linear
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {idx : Nat}
    {Ax : L.BoundedFormula α idx → Prop}
    {A B : Nat → L.BoundedFormula α idx}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp : _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (m : Nat) :
    (interp.target_proof_family.rightConjElim.minCheckedCodeSize m : Real) =
      (m : Real) + 11 := by
  have hforced :=
    externalPAHilbertProofLength_eq_localChecked_forces_rootFormulaCodeSize
      interp (_root_.partialConsistencyCode m) (Or.inl ⟨m, rfl⟩)
  rw [interp.localCheckedCodeProofLength_partialConsistency] at hforced
  calc
    (interp.target_proof_family.rightConjElim.minCheckedCodeSize m : Real) =
        (m : Real) + 7 + 2 + 1 + 1 := by
          simpa [_root_.rootFormulaCodeSize, _root_.partialConsistencyCode,
            _root_.FormulaFamily.rootWeight, _root_.ProofSystem.rootWeight,
            _root_.ProofLengthMeasure.rootWeight, Nat.cast_add] using hforced
    _ = (m : Real) + 11 := by ring

theorem externalPAHilbertProofLength_eq_localChecked_forces_reflectionGraft_linear
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {idx : Nat}
    {Ax : L.BoundedFormula α idx → Prop}
    {A B : Nat → L.BoundedFormula α idx}
    {halign : _root_.HilbertProjectionCodeAlignment}
    (interp : _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign)
    (m : Nat) :
    (interp.target_proof_family.minCheckedCodeSize m : Real) =
      (m : Real) + 13 := by
  have hforced :=
    externalPAHilbertProofLength_eq_localChecked_forces_rootFormulaCodeSize
      interp (_root_.sondowReflectionGraftCode m) (Or.inr ⟨m, rfl⟩)
  rw [interp.localCheckedCodeProofLength_reflectionGraft] at hforced
  calc
    (interp.target_proof_family.minCheckedCodeSize m : Real) =
        (m : Real) + 9 + 2 + 1 + 1 := by
          simpa [_root_.rootFormulaCodeSize, _root_.sondowReflectionGraftCode,
            _root_.FormulaFamily.rootWeight, _root_.ProofSystem.rootWeight,
            _root_.ProofLengthMeasure.rootWeight, Nat.cast_add] using hforced
    _ = (m : Real) + 13 := by ring

/--
Audit interpretation for the current bounded-arithmetic toy syntax.  Atomic
project tags are interpreted as false, while the structural PA axioms remain
true and the Hilbert rules are sound.  This is not intended as the project
semantics; it is a probe showing whether `finiteConsistencyFormula` has a real
derivation in the present toy PA calculus.
-/
def currentToyBAFormulaAuditTruth :
    BoundedArithmeticLab.BAFormula → Prop
  | BoundedArithmeticLab.BAFormula.atom _ _ => False
  | BoundedArithmeticLab.BAFormula.falsum => False
  | BoundedArithmeticLab.BAFormula.equal _ _ => True
  | BoundedArithmeticLab.BAFormula.le _ _ => True
  | BoundedArithmeticLab.BAFormula.not _ => True
  | BoundedArithmeticLab.BAFormula.and A B =>
      currentToyBAFormulaAuditTruth A ∧ currentToyBAFormulaAuditTruth B
  | BoundedArithmeticLab.BAFormula.or A B =>
      currentToyBAFormulaAuditTruth A ∨ currentToyBAFormulaAuditTruth B
  | BoundedArithmeticLab.BAFormula.imp A B =>
      currentToyBAFormulaAuditTruth A → currentToyBAFormulaAuditTruth B
  | BoundedArithmeticLab.BAFormula.forallBounded _ _ _ => True
  | BoundedArithmeticLab.BAFormula.existsBounded _ _ _ => True

theorem currentToyPAAxiom_auditTruth
    {φ : BoundedArithmeticLab.BAFormula}
    (hφ : BoundedArithmeticLab.PAAxiom φ) :
    currentToyBAFormulaAuditTruth φ := by
  cases hφ <;>
    simp [currentToyBAFormulaAuditTruth,
      BoundedArithmeticLab.sigmaBInductionFormula,
      BoundedArithmeticLab.polytimeDefinabilityFormula]

theorem currentToyPADerivation_auditTruth
    {φ : BoundedArithmeticLab.BAFormula}
    (proof :
      BoundedArithmeticLab.BADerivation
        BoundedArithmeticLab.PAAxiom φ) :
    currentToyBAFormulaAuditTruth φ := by
  induction proof with
  | ax hφ =>
      exact currentToyPAAxiom_auditTruth hφ
  | andIntro _ _ hleft hright =>
      exact ⟨hleft, hright⟩
  | andElimRight _ hpair =>
      exact hpair.2
  | impIntro _ hbody =>
      intro _
      exact hbody
  | mp _ _ himp harg =>
      exact himp harg

/--
In the current bounded-arithmetic toy calculus, the finite-consistency target is
only an uninterpreted atom.  Since no PA axiom concludes that atom, no Hilbert
derivation of it exists.
-/
theorem no_currentToyPADerivation_finiteConsistencyFormula
    (n : Nat) :
    BoundedArithmeticLab.BADerivation
      BoundedArithmeticLab.PAAxiom
      (BoundedArithmeticLab.finiteConsistencyFormula n) → False := by
  intro proof
  exact currentToyPADerivation_auditTruth proof

theorem no_currentToyPAProofObject_finiteConsistencyFormula
    (n : Nat) :
    ¬ ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.PAAxiom,
        proof.conclusion =
          BoundedArithmeticLab.finiteConsistencyFormula n := by
  intro hproof
  rcases hproof with ⟨proof, hconclusion⟩
  rcases proof with ⟨conclusion, derivation⟩
  dsimp at hconclusion
  subst conclusion
  exact no_currentToyPADerivation_finiteConsistencyFormula n derivation

/--
Since every current toy Buss-S²₁ proof object maps into the current toy PA
proof-object calculus, the no-proof result also rules out Buss-S²₁ proof
objects of the finite-consistency atom.
-/
theorem no_currentToyBussS21ProofObject_finiteConsistencyFormula
    (n : Nat) :
    ¬ ∃ proof :
        BoundedArithmeticLab.BAProofObject
          BoundedArithmeticLab.BussS21Axiom,
        proof.conclusion =
          BoundedArithmeticLab.finiteConsistencyFormula n := by
  intro hproof
  rcases hproof with ⟨proof, hconclusion⟩
  exact no_currentToyPAProofObject_finiteConsistencyFormula n
    ⟨proof.mapAxioms BoundedArithmeticLab.bussS21Axiom_subset_pa,
      by
        simpa [BoundedArithmeticLab.BAProofObject.mapAxioms]
          using hconclusion⟩

/--
Any project assembly proof certificate is, after the canonical same-object
identification, a Buss-S²₁ proof object of the finite-consistency formula
itself.  This makes the assembly field an exposed proof-construction
obligation, not a harmless bookkeeping field.
-/
theorem projectAssemblyBudgetFieldIndex_assembledProof_conclusion_eq_finiteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (index :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectAssemblyBudgetFieldIndex
        MainRationality SondowAccepted bounds bound)
    {n : Nat}
    (source :
      BoundedArithmeticLab.CompiledSondowProjectSourceCertificateAt
        bounds n) :
    (BoundedArithmeticLab.BoundedProofPredicate.ProjectAssemblyBudgetFieldIndex.assembledProof
      index source).conclusion =
        BoundedArithmeticLab.finiteConsistencyFormula n := by
  rw [← BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTarget_target_eq_finiteConsistency n]
  exact
    BoundedArithmeticLab.BoundedProofPredicate.ProjectAssemblyBudgetFieldIndex.proof_conclusion
      index source

/--
The current toy canonical proof-certificate route cannot yet supply the needed
finite-consistency proof object.  A real route must replace this toy calculus
by a genuine Buss-S²₁ proof-object construction or explicitly construct the
certificate.
-/
theorem no_currentToyCanonicalProofCertificateAt_finiteConsistency
    {bound : Nat → Real} {n : Nat}
    (cert :
      BoundedArithmeticLab.BoundedProofPredicate.CanonicalProofCertificateAt
        bound n) :
    False :=
  no_currentToyBussS21ProofObject_finiteConsistencyFormula n
    ⟨cert.proof,
      cert.proof_conclusion_eq_finiteConsistency⟩

/--
The current toy certificate verifier cannot accept a canonical finite-
consistency proof certificate, because acceptance is equivalent to the
existence of the certificate object ruled out above.
-/
theorem no_currentToyCanonicalProofCertificateAccepted_finiteConsistency
    {bound : Nat → Real} {n : Nat} :
    BoundedArithmeticLab.BoundedProofPredicate.CanonicalProofCertificateAccepted
      bound n →
    False := by
  intro haccepted
  rcases
      (BoundedArithmeticLab.BoundedProofPredicate.canonicalProofCertificateAccepted_iff_certificateAt).1
        haccepted with
    ⟨cert⟩
  exact no_currentToyCanonicalProofCertificateAt_finiteConsistency cert

/--
Accepted-trace form of the same obstruction.  Even the concrete certificate
verifier carrier cannot close the canonical finite-consistency route over the
current toy Buss-S²₁ calculus: an accepted trace contains a certificate proof
object, and `ofAcceptedTrace` exposes it as a canonical proof certificate.
-/
theorem no_currentToyCanonicalProofCertificateAcceptedTrace_finiteConsistency
    {bound : Nat → Real} {n : Nat}
    (tr :
      BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace
        (BoundedArithmeticLab.BoundedProofPredicate.canonicalProofCertificateVerifierMachine
          bound) n) :
    False :=
  no_currentToyCanonicalProofCertificateAt_finiteConsistency
    (BoundedArithmeticLab.BoundedProofPredicate.CanonicalProofCertificateAt.ofAcceptedTrace
      tr)

/--
Thus any accepted-to-canonical-certificate transport already contains the
missing proof object at every accepted index.  In the current toy calculus, such
a transport is impossible as soon as its source predicate is inhabited.
-/
theorem no_acceptedToCanonicalProofCertificateTransport_currentToy_of_accepted
    {Accepted : Nat → Prop} {bound : Nat → Real}
    (transport :
      BoundedArithmeticLab.BoundedProofPredicate.AcceptedToCanonicalProofCertificateTransport
        Accepted bound)
    {n : Nat} (haccepted : Accepted n) :
    False := by
  rcases transport.certificate_of_accepted n haccepted with ⟨cert⟩
  exact no_currentToyCanonicalProofCertificateAt_finiteConsistency cert

/--
Consequently, a project assembly budget index plus a compiled source already
contains the missing hard object.  In the current toy bounded-arithmetic
calculus this is impossible; closing the lower-bound route requires a real
assembly proof, not another wrapper around the field.
-/
theorem no_projectAssemblyBudgetFieldIndex_currentToy_of_source
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (index :
      BoundedArithmeticLab.BoundedProofPredicate.ProjectAssemblyBudgetFieldIndex
        MainRationality SondowAccepted bounds bound)
    {n : Nat}
    (source :
      BoundedArithmeticLab.CompiledSondowProjectSourceCertificateAt
        bounds n) :
    False :=
  no_currentToyBussS21ProofObject_finiteConsistencyFormula n
    ⟨BoundedArithmeticLab.BoundedProofPredicate.ProjectAssemblyBudgetFieldIndex.assembledProof
        index source,
      projectAssemblyBudgetFieldIndex_assembledProof_conclusion_eq_finiteConsistency
        index source⟩

theorem no_currentToyPADerivation_contradictionFormula :
    BoundedArithmeticLab.BADerivation
      BoundedArithmeticLab.PAAxiom
      BoundedArithmeticLab.BoundedProofPredicate.contradictionFormula →
        False := by
  intro proof
  exact currentToyPADerivation_auditTruth proof

/--
The Prop-level finite-consistency statement is therefore trivial for the current
toy PA calculus: the toy system has no derivation of `falsum` at any size bound.
This is distinct from proving the atomic formula `finiteConsistencyFormula n`.
-/
theorem currentToyPAFiniteConsistencyStatement_all
    (n : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.PAFiniteConsistencyStatement n := by
  intro hprov
  rcases hprov with ⟨proof, hwithin⟩
  rcases hwithin with ⟨hconclusion, _hsize⟩
  rcases proof with ⟨conclusion, derivation⟩
  dsimp at hconclusion
  subst conclusion
  exact no_currentToyPADerivation_contradictionFormula derivation

/--
The safer option-valued semantic proof-size view records the real obstruction:
the current toy PA calculus has no proof object for `finiteConsistencyFormula n`.
The old real-valued `semanticBAProofLength` then collapses this no-proof case
to `0` only because it uses the empty-infimum convention.
-/
theorem currentToySemanticBAMinProofSizeOption_finiteConsistency_eq_none
    (n : Nat) :
    BoundedArithmeticLab.semanticBAMinProofSizeOption
        BoundedArithmeticLab.PAAxiom
        BoundedArithmeticLab.finiteConsistencyFormula n =
      none :=
  BoundedArithmeticLab.semanticBAMinProofSizeOption_none_of_no_proof
    (no_currentToyPAProofObject_finiteConsistencyFormula n)

/--
Corrected bounded-arithmetic lower-bound target stated at the semantic
proof-object root.  The witness must be an actual minimum proof-object size
`some k`; the no-proof case `none` is not allowed to masquerade as a large
proof length.
-/
def BAOptionMinProofSizeBeatsPolynomial
    (Ax : BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → BoundedArithmeticLab.BAFormula) : Prop :=
  ∀ U : Nat → Real, _root_.is_polynomial_bound U → ∀ N : Nat,
    ∃ n : Nat, N ≤ n ∧
      ∃ k : Nat,
        BoundedArithmeticLab.semanticBAMinProofSizeOption Ax target n =
          some k ∧
        U n < (k : Real)

/--
An eventual polynomial-size proof-object family for a bounded-arithmetic target
family.  This is the direct negation-form of the desired Pudlak growth
statement: from some threshold onward, every target formula has a proof object
whose size is bounded by one fixed polynomial upper bound.
-/
def BAEventuallyPolynomialProofObjectFamily
    (Ax : BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → BoundedArithmeticLab.BAFormula) : Prop :=
  ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
    ∃ N : Nat,
      ∀ n : Nat, N ≤ n →
        ∃ proof : BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n ∧
            (proof.size : Real) ≤ U n

/--
Positive no-small-proof-object form of the same lower-bound target.  For every
polynomial upper bound and every starting point, one can find a target index
where every concrete proof object of that target is larger than the proposed
polynomial bound.
-/
def BAProofObjectStrongSizeLowerBound
    (Ax : BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → BoundedArithmeticLab.BAFormula) : Prop :=
  ∀ U : Nat → Real, _root_.is_polynomial_bound U → ∀ N : Nat,
    ∃ n : Nat, N ≤ n ∧
      ∀ proof : BoundedArithmeticLab.BAProofObject Ax,
        proof.conclusion = target n →
          U n < (proof.size : Real)

/-- Every target formula has an actual bounded-arithmetic proof object. -/
def BAProofObjectCompleteness
    (Ax : BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → BoundedArithmeticLab.BAFormula) : Prop :=
  ∀ n : Nat,
    ∃ proof : BoundedArithmeticLab.BAProofObject Ax,
      proof.conclusion = target n

/--
Non-vacuous proof-object lower-bound target.  This is the clean Pudlak-side
obligation: every target has a proof object, and every polynomial size bound is
eventually beaten by all proof objects at some arbitrarily late target index.
-/
structure BACompleteProofObjectStrongSizeLowerBound
    (Ax : BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → BoundedArithmeticLab.BAFormula) : Prop where
  complete : BAProofObjectCompleteness Ax target
  strong_lower : BAProofObjectStrongSizeLowerBound Ax target

theorem BAProofObjectStrongSizeLowerBound_to_no_eventual_polynomial_proof_family
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    (hlower : BAProofObjectStrongSizeLowerBound Ax target) :
    ¬ BAEventuallyPolynomialProofObjectFamily Ax target := by
  intro hfamily
  rcases hfamily with ⟨U, hU, N, hproofs⟩
  rcases hlower U hU N with ⟨n, hn_ge, hno_small⟩
  rcases hproofs n hn_ge with ⟨proof, hconclusion, hsize_le_U⟩
  exact (not_lt_of_ge hsize_le_U) (hno_small proof hconclusion)

theorem no_eventual_polynomial_proof_family_to_BAProofObjectStrongSizeLowerBound
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    (hno : ¬ BAEventuallyPolynomialProofObjectFamily Ax target) :
    BAProofObjectStrongSizeLowerBound Ax target := by
  intro U hU N
  by_contra hnowitness
  have htail :
      ∀ n : Nat, N ≤ n →
        ∃ proof : BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n ∧
            (proof.size : Real) ≤ U n := by
    intro n hn_ge
    have hnot_all :
        ¬ ∀ proof : BoundedArithmeticLab.BAProofObject Ax,
            proof.conclusion = target n →
              U n < (proof.size : Real) := by
      intro hno_small
      exact hnowitness ⟨n, hn_ge, hno_small⟩
    rcases not_forall.mp hnot_all with ⟨proof, hnot_imp⟩
    have hconclusion : proof.conclusion = target n := by
      by_contra hnot_conclusion
      exact hnot_imp (fun hconclusion => False.elim (hnot_conclusion hconclusion))
    have hnot_lt : ¬ U n < (proof.size : Real) := by
      intro hlt
      exact hnot_imp (fun _hconclusion => hlt)
    exact ⟨proof, hconclusion, le_of_not_gt hnot_lt⟩
  exact hno ⟨U, hU, N, htail⟩

theorem BAProofObjectStrongSizeLowerBound_iff_no_eventual_polynomial_proof_family
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula} :
    BAProofObjectStrongSizeLowerBound Ax target ↔
      ¬ BAEventuallyPolynomialProofObjectFamily Ax target :=
  ⟨BAProofObjectStrongSizeLowerBound_to_no_eventual_polynomial_proof_family,
    no_eventual_polynomial_proof_family_to_BAProofObjectStrongSizeLowerBound⟩

theorem BAOptionMinProofSizeBeatsPolynomial_to_frequently_exists_proof
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    (htarget : BAOptionMinProofSizeBeatsPolynomial Ax target)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ∃ n : Nat, N ≤ n ∧
      ∃ proof : BoundedArithmeticLab.BAProofObject Ax,
        proof.conclusion = target n := by
  rcases htarget U hU N with ⟨n, hn_ge, k, hmin, _hgt⟩
  exact ⟨n, hn_ge,
    BoundedArithmeticLab.semanticBAMinProofSizeOption_some_to_exists_proof
      hmin⟩

theorem BAOptionMinProofSizeBeatsPolynomial_to_no_eventual_polynomial_proof_family
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    (htarget : BAOptionMinProofSizeBeatsPolynomial Ax target) :
    ¬ BAEventuallyPolynomialProofObjectFamily Ax target := by
  intro hfamily
  rcases hfamily with ⟨U, hU, N, hproofs⟩
  rcases htarget U hU N with ⟨n, hn_ge, k, hmin, hgt⟩
  rcases hproofs n hn_ge with ⟨proof, hconclusion, hsize_le_U⟩
  have hk_le_size_nat : k ≤ proof.size :=
    BoundedArithmeticLab.semanticBAMinProofSizeOption_min_le_of_proof
      hmin proof hconclusion
  have hk_le_size : (k : Real) ≤ proof.size := by
    exact_mod_cast hk_le_size_nat
  linarith

theorem BAOptionMinProofSizeBeatsPolynomial_to_BAProofObjectStrongSizeLowerBound
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    (htarget : BAOptionMinProofSizeBeatsPolynomial Ax target) :
    BAProofObjectStrongSizeLowerBound Ax target := by
  intro U hU N
  rcases htarget U hU N with ⟨n, hn_ge, k, hmin, hgt⟩
  refine ⟨n, hn_ge, ?_⟩
  intro proof hconclusion
  have hk_le_size_nat : k ≤ proof.size :=
    BoundedArithmeticLab.semanticBAMinProofSizeOption_min_le_of_proof
      hmin proof hconclusion
  have hk_le_size : (k : Real) ≤ proof.size := by
    exact_mod_cast hk_le_size_nat
  exact lt_of_lt_of_le hgt hk_le_size

theorem no_eventual_polynomial_proof_family_to_BAOptionMinProofSizeBeatsPolynomial
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    (hcomplete :
      ∀ n : Nat,
        ∃ proof : BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hno : ¬ BAEventuallyPolynomialProofObjectFamily Ax target) :
    BAOptionMinProofSizeBeatsPolynomial Ax target := by
  intro U hU N
  by_contra hnowitness
  have htail :
      ∀ n : Nat, N ≤ n →
        ∃ proof : BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n ∧
            (proof.size : Real) ≤ U n := by
    intro n hn_ge
    rcases
        BoundedArithmeticLab.semanticBAMinProofSizeOption_some_of_exists_proof
          (hcomplete n) with
      ⟨k, hmin⟩
    have hnot_lt : ¬ U n < (k : Real) := by
      intro hlt
      exact hnowitness ⟨n, hn_ge, k, hmin, hlt⟩
    have hk_le_U : (k : Real) ≤ U n := le_of_not_gt hnot_lt
    rcases
        BoundedArithmeticLab.semanticBAMinProofSizeOption_some_to_hasProofOfSize
          hmin with
      ⟨proof, hconclusion, hsize_le_k_nat⟩
    have hsize_le_k : (proof.size : Real) ≤ k := by
      exact_mod_cast hsize_le_k_nat
    exact ⟨proof, hconclusion, le_trans hsize_le_k hk_le_U⟩
  exact hno ⟨U, hU, N, htail⟩

theorem BAOptionMinProofSizeBeatsPolynomial_iff_no_eventual_polynomial_proof_family
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    (hcomplete :
      ∀ n : Nat,
        ∃ proof : BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n) :
    BAOptionMinProofSizeBeatsPolynomial Ax target ↔
      ¬ BAEventuallyPolynomialProofObjectFamily Ax target :=
  ⟨BAOptionMinProofSizeBeatsPolynomial_to_no_eventual_polynomial_proof_family,
    no_eventual_polynomial_proof_family_to_BAOptionMinProofSizeBeatsPolynomial
      hcomplete⟩

theorem BAProofObjectStrongSizeLowerBound_to_BAOptionMinProofSizeBeatsPolynomial
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    (hcomplete :
      ∀ n : Nat,
        ∃ proof : BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hlower : BAProofObjectStrongSizeLowerBound Ax target) :
    BAOptionMinProofSizeBeatsPolynomial Ax target := by
  intro U hU N
  rcases hlower U hU N with ⟨n, hn_ge, hno_small⟩
  rcases
      BoundedArithmeticLab.semanticBAMinProofSizeOption_some_of_exists_proof
        (hcomplete n) with
    ⟨k, hmin⟩
  rcases
      BoundedArithmeticLab.semanticBAMinProofSizeOption_some_to_hasProofOfSize
        hmin with
    ⟨proof, hconclusion, hsize_le_k_nat⟩
  have hsize_le_k : (proof.size : Real) ≤ k := by
    exact_mod_cast hsize_le_k_nat
  exact ⟨n, hn_ge, k, hmin,
    lt_of_lt_of_le (hno_small proof hconclusion) hsize_le_k⟩

theorem BAProofObjectStrongSizeLowerBound_iff_BAOptionMinProofSizeBeatsPolynomial
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    (hcomplete :
      ∀ n : Nat,
        ∃ proof : BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n) :
    BAProofObjectStrongSizeLowerBound Ax target ↔
      BAOptionMinProofSizeBeatsPolynomial Ax target :=
  ⟨BAProofObjectStrongSizeLowerBound_to_BAOptionMinProofSizeBeatsPolynomial
      hcomplete,
    BAOptionMinProofSizeBeatsPolynomial_to_BAProofObjectStrongSizeLowerBound⟩

theorem BACompleteProofObjectStrongSizeLowerBound_to_BAOptionMinProofSizeBeatsPolynomial
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    (hlower : BACompleteProofObjectStrongSizeLowerBound Ax target) :
    BAOptionMinProofSizeBeatsPolynomial Ax target :=
  BAProofObjectStrongSizeLowerBound_to_BAOptionMinProofSizeBeatsPolynomial
    hlower.complete hlower.strong_lower

theorem BACompleteProofObjectStrongSizeLowerBound_to_no_eventual_polynomial_proof_family
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    (hlower : BACompleteProofObjectStrongSizeLowerBound Ax target) :
    ¬ BAEventuallyPolynomialProofObjectFamily Ax target :=
  BAProofObjectStrongSizeLowerBound_to_no_eventual_polynomial_proof_family
    hlower.strong_lower

theorem BACompleteProofObjectStrongSizeLowerBound_iff_complete_and_option
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula} :
    BACompleteProofObjectStrongSizeLowerBound Ax target ↔
      BAProofObjectCompleteness Ax target ∧
        BAOptionMinProofSizeBeatsPolynomial Ax target := by
  constructor
  · intro hlower
    exact ⟨hlower.complete,
      BACompleteProofObjectStrongSizeLowerBound_to_BAOptionMinProofSizeBeatsPolynomial
        hlower⟩
  · intro h
    exact
      { complete := h.1
        strong_lower :=
          BAOptionMinProofSizeBeatsPolynomial_to_BAProofObjectStrongSizeLowerBound
            h.2 }

theorem BACompleteProofObjectStrongSizeLowerBound_iff_complete_and_no_eventual
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula} :
    BACompleteProofObjectStrongSizeLowerBound Ax target ↔
      BAProofObjectCompleteness Ax target ∧
        ¬ BAEventuallyPolynomialProofObjectFamily Ax target := by
  constructor
  · intro hlower
    exact ⟨hlower.complete,
      BACompleteProofObjectStrongSizeLowerBound_to_no_eventual_polynomial_proof_family
        hlower⟩
  · intro h
    exact
      { complete := h.1
        strong_lower :=
          no_eventual_polynomial_proof_family_to_BAProofObjectStrongSizeLowerBound
            h.2 }

theorem no_BAOptionMinProofSizeBeatsPolynomial_of_polynomial_upper_bound
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    {V : Nat → Real}
    (hV : _root_.is_polynomial_bound V)
    (hupper :
      ∀ n k : Nat,
        BoundedArithmeticLab.semanticBAMinProofSizeOption Ax target n =
            some k →
          (k : Real) ≤ V n) :
    BAOptionMinProofSizeBeatsPolynomial Ax target → False := by
  intro htarget
  rcases htarget V hV 0 with ⟨n, _hn_ge, k, hmin, hgt⟩
  have hk_le : (k : Real) ≤ V n := hupper n k hmin
  linarith

theorem constant_zero_polynomial_bound :
    _root_.is_polynomial_bound (fun _n : Nat => (0 : Real)) := by
  refine ⟨0, 0, ?_⟩
  intro n
  norm_num

theorem constant_one_polynomial_bound :
    _root_.is_polynomial_bound (fun _n : Nat => (1 : Real)) := by
  refine ⟨1, 0, ?_⟩
  intro n
  norm_num

theorem no_currentToyBAOptionMinProofSizeBeatsPolynomial_finiteConsistency :
    BAOptionMinProofSizeBeatsPolynomial
        BoundedArithmeticLab.PAAxiom
        BoundedArithmeticLab.finiteConsistencyFormula →
      False := by
  intro htarget
  rcases htarget (fun _n : Nat => (0 : Real))
      constant_zero_polynomial_bound 0 with
    ⟨n, _hn_ge, k, hmin, _hgt⟩
  have hnone :=
    currentToySemanticBAMinProofSizeOption_finiteConsistency_eq_none n
  rw [hnone] at hmin
  cases hmin

/--
Adding each target formula directly as an axiom is not a valid lower-bound
closure.  It creates a one-step proof object at every index, contradicting the
requirement that the semantic minimum proof size beat even the constant
polynomial `1`.
-/
theorem no_BAOptionMinProofSizeBeatsPolynomial_of_target_axioms
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    (haxiom : ∀ n : Nat, Ax (target n)) :
    BAOptionMinProofSizeBeatsPolynomial Ax target → False := by
  intro htarget
  rcases htarget (fun _n : Nat => (1 : Real))
      constant_one_polynomial_bound 0 with
    ⟨n, _hn_ge, k, hmin, hgt⟩
  let proof : BoundedArithmeticLab.BAProofObject Ax :=
    { conclusion := target n
      derivation := BoundedArithmeticLab.BADerivation.ax (haxiom n) }
  have hk_le : k ≤ proof.size :=
    BoundedArithmeticLab.semanticBAMinProofSizeOption_min_le_of_proof
      hmin proof rfl
  have hproof_size : proof.size = 1 := rfl
  have hk_real_le : (k : Real) ≤ 1 := by
    exact_mod_cast (by simpa [hproof_size] using hk_le)
  linarith

/--
Consequently, completing the target family by adding every target formula as an
axiom cannot prove the non-vacuous lower-bound target.  It supplies
one-step proofs, hence an eventual constant-size proof family.
-/
theorem no_BACompleteProofObjectStrongSizeLowerBound_of_target_axioms
    {Ax : BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → BoundedArithmeticLab.BAFormula}
    (haxiom : ∀ n : Nat, Ax (target n)) :
    BACompleteProofObjectStrongSizeLowerBound Ax target → False := by
  intro hlower
  exact
    no_BAOptionMinProofSizeBeatsPolynomial_of_target_axioms haxiom
      (BACompleteProofObjectStrongSizeLowerBound_to_BAOptionMinProofSizeBeatsPolynomial
        hlower)

/--
Because the current toy PA calculus has no proof object for
`finiteConsistencyFormula n`, the semantic infimum is the empty-set fallback
value `0`.  This exposes why the corrected CnBox route still cannot be closed
inside the present toy semantics.
-/
theorem currentToySemanticBAProofLength_finiteConsistency_eq_zero
    (n : Nat) :
    BoundedArithmeticLab.semanticBAProofLength
        BoundedArithmeticLab.PAAxiom
        BoundedArithmeticLab.finiteConsistencyFormula n =
      0 := by
  rw [BoundedArithmeticLab.semanticBAProofLength]
  have hset :
      ({r : Real |
          ∃ proof :
            BoundedArithmeticLab.BAProofObject
              BoundedArithmeticLab.PAAxiom,
            proof.conclusion =
              BoundedArithmeticLab.finiteConsistencyFormula n ∧
              (proof.size : Real) = r} : Set Real) = ∅ := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨proof, hconclusion, _hsize⟩
      exact False.elim
        (no_currentToyPAProofObject_finiteConsistencyFormula n
          ⟨proof, hconclusion⟩)
    · intro hr
      cases hr
  rw [hset, Real.sInf_empty]

theorem currentToyCanonicalCnBoxPABox_length_eq_zero
    (n : Nat) :
    BoundedArithmeticLab.BoundedProofPredicate.canonicalCnBoxPABox.length n =
      0 := by
  rw [correctedCanonicalCnBoxPABox_length_eq_semanticFiniteConsistency,
    currentToySemanticBAProofLength_finiteConsistency_eq_zero]

/--
The current toy CnBox PA semantics cannot have a Pudlak all-polynomial
proof-length gap: its semantic length is identically zero on the target family.
-/
theorem no_currentToyCanonicalCnBoxProofLengthGap :
    ¬ BoundedArithmeticLab.BoundedProofPredicate.CanonicalCnBoxProofLengthGap := by
  intro hgap
  rcases hgap (fun _ : Nat => (0 : Real))
      (BoundedArithmeticLab.IsPolynomialBound.const 0) 0 with
    ⟨witness⟩
  have hzero :=
    currentToyCanonicalCnBoxPABox_length_eq_zero witness.n
  have hgap_pos := witness.gap_pos
  rw [hzero] at hgap_pos
  linarith

/--
Equivalently, the current toy CnBox PA semantics cannot even carry an
`EventualLowerBound`: the canonical box length is identically zero, so it cannot
eventually beat the constant polynomial `0`.
-/
theorem no_currentToyCanonicalCnBoxEventualLowerBound :
    BoundedArithmeticLab.EventualLowerBound
      BoundedArithmeticLab.BoundedProofPredicate.canonicalCnBoxPABox →
      False := by
  intro hlower
  exact no_currentToyCanonicalCnBoxProofLengthGap
    ((BoundedArithmeticLab.BoundedProofPredicate.proofLengthGap_iff_eventualLowerBound
        BoundedArithmeticLab.BoundedProofPredicate.canonicalCnBoxPABox).2
          hlower)

/--
Thus no canonical relabeling calibration can close the lower side over the
present toy `BAProofObject PAAxiom` semantics.  This rules out the entire current
canonical CnBox route, not just the special root-literature instance.
-/
theorem no_canonicalRelabeledPudlakCalibration_currentToySemantics
    {lower_source :
      BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource} :
    BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        lower_source →
      False := by
  intro calibration
  exact no_currentToyCanonicalCnBoxEventualLowerBound
    (by
      simpa [BoundedArithmeticLab.BoundedProofPredicate.canonicalCnBoxPABox]
        using
          (BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration.toConcretePALowerBound
            calibration))

/--
The general corrected canonical CnBox closure target is also impossible with the
current toy semantic proof-length model.  The missing object is therefore not a
different external source, but a real replacement for the toy PA proof-code
semantics.
-/
theorem no_correctedCanonicalCnBoxLowerBoundClosureTarget_currentToySemantics :
    CorrectedCanonicalCnBoxLowerBoundClosureTarget → False := by
  intro htarget
  rcases htarget with ⟨lower_source, calibration⟩
  exact no_canonicalRelabeledPudlakCalibration_currentToySemantics calibration

/--
Therefore the root-literature-to-canonical-CnBox calibration target is impossible
as long as the canonical CnBox endpoint is interpreted by the present toy
`BAProofObject PAAxiom` calculus.  The missing work is not another wrapper; the
finite-consistency formula must be replaced by, or linked to, a real PA proof-code
semantics before a Pudlak lower-bound theorem can attach.
-/
theorem no_rootLiteratureCanonicalCnBoxCalibrationTarget_currentToySemantics :
    RootLiteratureCanonicalCnBoxCalibrationTarget → False := by
  intro htarget
  rcases htarget with ⟨calibration⟩
  exact no_canonicalRelabeledPudlakCalibration_currentToySemantics calibration

/--
Singleton numeric bound for calibrated enumeration.  If the canonical accepted
code for formula index `n` has calibrated size below the cutoff `K`, the
enumeration range must include that single code `n`; otherwise the required
range is empty.
-/
def calibratedSingletonCodeBound
    (lengthCodeAt : Nat → Nat) (n K : Nat) : Nat :=
  if lengthCodeAt n < K then n + 1 else 0

/--
For the concrete powerBound checker, injectivity of `powerBoundRawCode` opens
the accepted-code structure completely: every accepted code for the target
formula `powerBoundRawCode n` is the canonical code `n`.  Therefore the
singleton code bound is a complete calibrated finite enumeration.
-/
def calibratedSingletonFiniteEnumeration_of_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
      scale_data lengthCodeAt where
  codeBound := calibratedSingletonCodeBound lengthCodeAt
  complete_code_lt_bound := by
    intro n K code haccepted hsize
    have hcode_eq : code = n :=
      concretePAHilbertPowerBound_acceptedProofCode_to_code_eq_of_injective
        hinjective haccepted
    subst code
    simp [calibratedSingletonCodeBound, hsize]

/--
The executable lower-search box can be opened one level further.  A genuine
search-gap certificate for the calibrated canonical length, together with
raw-code injectivity, directly constructs the semantic no-accepted-code search.

At the computed witness the cutoff is exactly `lengthCodeAt witness`, so the
singleton enumeration range is empty; no rejected-code black box is being used.
-/
def canonicalLengthGap_toNoAcceptedCodeSearch_of_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    (gap :
      ComputableSearchGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real))) :
    ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
      scale_data lengthCodeAt
      (calibratedSingletonFiniteEnumeration_of_injective
        lengthCodeAt hinjective) where
  witness := fun f hf N =>
    (gap.gap_for_polynomial_upper f hf).witness N
  cutoff := fun f hf N =>
    lengthCodeAt ((gap.gap_for_polynomial_upper f hf).witness N)
  witness_ge := by
    intro f hf N
    exact (gap.gap_for_polynomial_upper f hf).witness_ge N
  cutoff_gt := by
    intro f hf N
    exact (gap.gap_for_polynomial_upper f hf).strict_at_witness N
  noAcceptedBelowCodeBound := by
    intro f hf N code hcode_lt _haccepted
    have hcode_lt_zero : code < 0 := by
      simp [calibratedSingletonFiniteEnumeration_of_injective,
        calibratedSingletonCodeBound] at hcode_lt
    exact (Nat.not_lt_zero code) hcode_lt_zero

/--
This is the leanest remaining executable lower-gap closure target: construct a
calibrated size, a finite enumeration complete for `size(code) < K`, and a
Boolean rejection search for those enumerated codes.
-/
def SizeFilteredRejectionSearchClosureTarget
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  Nonempty
    (Σ lengthCodeAt : Nat → Nat,
      Σ enumeration :
        ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
          scale_data lengthCodeAt,
        ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
          scale_data lengthCodeAt enumeration)

/--
The same closure target with the Boolean rejection predicate opened into the
semantic statement that no accepted proof code exists below the calibrated
finite-search code bound.
-/
def SizeFilteredNoAcceptedCodeSearchClosureTarget
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  Nonempty
    (Σ lengthCodeAt : Nat → Nat,
      Σ enumeration :
        ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
          scale_data lengthCodeAt,
        ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
          scale_data lengthCodeAt enumeration)

/--
Opened closure theorem: once the remaining lower-bound content is reduced to
`powerBoundRawCode` injectivity plus a computable gap for the calibrated
canonical length, the size-filtered no-accepted-code target follows in Lean.
-/
theorem canonicalLengthGap_to_noAcceptedCodeSearchTarget_of_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    (gap :
      ComputableSearchGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real))) :
    SizeFilteredNoAcceptedCodeSearchClosureTarget scale_data := by
  exact
    ⟨⟨lengthCodeAt,
      calibratedSingletonFiniteEnumeration_of_injective
        lengthCodeAt hinjective,
      canonicalLengthGap_toNoAcceptedCodeSearch_of_injective
        hinjective gap⟩⟩

/--
Transport the calibrated canonical-length gap to the root actual proof-length
carrier when the root proof length is pointwise equal to that calibrated size.
This isolates the proof-length residual exactly.
-/
def canonicalLengthGap_and_rootExactness_to_actualProofLengthGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (gap :
      ComputableSearchGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (rootExact :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :
    ComputableSearchGapCertificate
      (actualProofLengthMeasured scale_data) where
  gap_for_polynomial_upper := by
    intro U hU
    let g := gap.gap_for_polynomial_upper U hU
    exact
      { witness := g.witness
        witness_ge := g.witness_ge
        strict_at_witness := by
          intro N
          have hstrict := g.strict_at_witness N
          simpa [actualProofLengthMeasured, rootExact (g.witness N)] using
            hstrict }

/--
Consequently, on the current root semantics no pair

* a super-polynomial search gap for `lengthCodeAt`, and
* a pointwise equality `proof_length(powerBoundRawCode n)=lengthCodeAt n`

can exist.  If it did, it would contradict the already-proved polynomial
formula-size fallback for `actualProofLengthMeasured`.
-/
theorem no_canonicalLengthGap_and_rootExactness_currentRoot
    {scale_data : InternalPudlakTheorem5ScaleData}
    {lengthCodeAt : Nat → Nat}
    (gap :
      ComputableSearchGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (rootExact :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :
    False :=
  no_actualProofLengthSearchGapTarget_currentRoot scale_data
    ⟨canonicalLengthGap_and_rootExactness_to_actualProofLengthGap
      gap rootExact⟩

theorem rootProofLength_eq_lengthCodeAt_of_calibratedCheckerExactness_direct
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

/--
Model carrier for the remaining growth obligation.  This is not claimed to be
the real PA/Hilbert proof length.  It is a proof probe showing that the
size-filtered lower-search route closes mechanically once the canonical
proof-code length is genuinely super-polynomial.
-/
def superPolynomialCanonicalLength (n : Nat) : Nat :=
  (n + 1) ^ n

/--
The model carrier `n ↦ (n+1)^n` has the required search-gap property: it
eventually beats every polynomial upper bound at a computable witness.

This theorem closes only the growth-analysis layer.  The submission-relevant
remaining task is still to identify such a carrier with a real proof-code
semantics, not to choose it artificially.
-/
def superPolynomialCanonicalLength_searchGap :
    ComputableSearchGapCertificate
      (fun n : Nat => (superPolynomialCanonicalLength n : Real)) := by
  classical
  refine ⟨?_⟩
  intro U hU
  let c : Real := Classical.choose hU.nonneg_coefficient
  let k : Nat := Classical.choose (Classical.choose_spec hU.nonneg_coefficient)
  have hbound :
      ∀ n : Nat, U n ≤ c * ((n : Real) + 1) ^ k :=
    (Classical.choose_spec
      (Classical.choose_spec hU.nonneg_coefficient)).2
  let C : Nat := Classical.choose (exists_nat_ge c)
  have hC : c ≤ (C : Real) :=
    Classical.choose_spec (exists_nat_ge c)
  refine
    { witness := fun N : Nat => max N (C + k + 1)
      witness_ge := ?_
      strict_at_witness := ?_ }
  · intro N
    exact le_max_left N (C + k + 1)
  · intro N
    let w : Nat := max N (C + k + 1)
    let B : Real := (w : Real) + 1
    have hU_le : U w ≤ c * B ^ k := by
      simpa [B] using hbound w
    have hB_ge_one : (1 : Real) ≤ B := by
      dsimp [B]
      nlinarith [show (0 : Real) ≤ (w : Real) by exact Nat.cast_nonneg w]
    have hB_pos : 0 < B := by
      dsimp [B]
      positivity
    have hpow_nonneg : 0 ≤ B ^ k := by
      positivity
    have hpow_pos : 0 < B ^ k := by
      positivity
    have hC_mul_le : c * B ^ k ≤ (C : Real) * B ^ k :=
      mul_le_mul_of_nonneg_right hC hpow_nonneg
    have hbase_bound : C + k + 1 ≤ w :=
      le_max_right N (C + k + 1)
    have hk_succ_le_w : k + 1 ≤ w := by
      omega
    have hC_lt_B : (C : Real) < B := by
      have hC_lt_w_succ : C < w + 1 := by
        omega
      have hC_lt_w_succ_real : (C : Real) < ((w + 1 : Nat) : Real) := by
        exact_mod_cast hC_lt_w_succ
      simpa [B, Nat.cast_add] using hC_lt_w_succ_real
    have hC_mul_lt : (C : Real) * B ^ k < B * B ^ k :=
      mul_lt_mul_of_pos_right hC_lt_B hpow_pos
    have hB_mul_eq : B * B ^ k = B ^ (k + 1) := by
      rw [show k + 1 = Nat.succ k by omega, pow_succ]
      ring
    have hpow_le : B ^ (k + 1) ≤ B ^ w :=
      pow_le_pow_right₀ hB_ge_one hk_succ_le_w
    have hstrict : U w < B ^ w := by
      calc
        U w ≤ c * B ^ k := hU_le
        _ ≤ (C : Real) * B ^ k := hC_mul_le
        _ < B * B ^ k := hC_mul_lt
        _ = B ^ (k + 1) := hB_mul_eq
        _ ≤ B ^ w := hpow_le
    simpa [superPolynomialCanonicalLength, w, B, Nat.cast_add,
      Nat.cast_pow] using hstrict

/--
Model closure of the size-filtered no-accepted-code target from the explicit
super-polynomial carrier.  The only mathematical input left here is injectivity
of the concrete target formula-code family.
-/
theorem superPolynomialCanonicalLength_to_noAcceptedCodeSearchTarget
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    SizeFilteredNoAcceptedCodeSearchClosureTarget scale_data :=
  canonicalLengthGap_to_noAcceptedCodeSearchTarget_of_injective
    (scale_data := scale_data)
    (lengthCodeAt := superPolynomialCanonicalLength)
    hinjective
    superPolynomialCanonicalLength_searchGap

/--
End-to-end proof-length-free model closure: in the synthetic
super-polynomial carrier, raw-code injectivity is enough to produce the
checked-measured search gap consumed by the collision kernel.

Again, this proves the adapter chain, not the identification of the synthetic
carrier with genuine PA proof length.
-/
theorem superPolynomialCanonicalLength_to_checkedMeasuredSearchGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    Nonempty
      (Σ lengthCodeAt : Nat → Nat,
        Σ enumeration :
          ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
            scale_data lengthCodeAt,
          Σ _ :
            ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
              scale_data lengthCodeAt enumeration,
            ComputableSearchGapCertificate
              (month9_month10_checkedProofCodeMeasured
                scale_data
                (concretePAHilbertPowerBoundCalibratedCheckerSemantics
                  scale_data lengthCodeAt).toProofCodeSemantics)) :=
  ⟨⟨superPolynomialCanonicalLength,
    calibratedSingletonFiniteEnumeration_of_injective
      superPolynomialCanonicalLength hinjective,
    canonicalLengthGap_toNoAcceptedCodeSearch_of_injective
      hinjective superPolynomialCanonicalLength_searchGap,
    calibratedNoAcceptedCodeSearch_checkedMeasuredSearchGap
      (canonicalLengthGap_toNoAcceptedCodeSearch_of_injective
        hinjective superPolynomialCanonicalLength_searchGap)⟩⟩

/--
The synthetic super-polynomial carrier cannot be identified with the current
root `proof_length` on the theorem-5 power-bound family.  The current root
semantics has already collapsed to the polynomial formula-size fallback.
-/
theorem no_superPolynomialCanonicalLength_rootExactness_currentRoot
    {scale_data : InternalPudlakTheorem5ScaleData}
    (rootExact :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (superPolynomialCanonicalLength n : Real)) :
    False :=
  no_canonicalLengthGap_and_rootExactness_currentRoot
    superPolynomialCanonicalLength_searchGap rootExact

/--
Consequently, under the current root `proof_length` fallback, the calibrated
checker cannot be made exact for the synthetic super-polynomial carrier.  This
is the direct audit of the old route: calibrated exactness is the hard residual,
not an automatic consequence of the checker wrapper.
-/
theorem no_superPolynomialCalibratedCheckerExactness_currentRoot
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data superPolynomialCanonicalLength) →
      False := by
  intro exactness
  exact no_superPolynomialCanonicalLength_rootExactness_currentRoot
    (rootProofLength_eq_lengthCodeAt_of_calibratedCheckerExactness_direct
      superPolynomialCanonicalLength hinjective exactness)

theorem sizeFilteredRejectionSearchClosureTarget_to_noAcceptedCodeSearchTarget
    {scale_data : InternalPudlakTheorem5ScaleData}
    (target : SizeFilteredRejectionSearchClosureTarget scale_data) :
    SizeFilteredNoAcceptedCodeSearchClosureTarget scale_data := by
  rcases target with ⟨lengthCodeAt, enumeration, rejection_search⟩
  exact
    ⟨⟨lengthCodeAt, enumeration,
      calibratedRejectionSearch_toNoAcceptedCodeSearch rejection_search⟩⟩

theorem sizeFilteredNoAcceptedCodeSearchTarget_to_rejectionSearchClosureTarget
    {scale_data : InternalPudlakTheorem5ScaleData}
    (target : SizeFilteredNoAcceptedCodeSearchClosureTarget scale_data) :
    SizeFilteredRejectionSearchClosureTarget scale_data := by
  rcases target with ⟨lengthCodeAt, enumeration, search⟩
  exact
    ⟨⟨lengthCodeAt, enumeration,
      calibratedNoAcceptedCodeSearch_toRejectionSearch search⟩⟩

theorem sizeFilteredNoAcceptedCodeSearchTarget_to_checkedMeasuredSearchGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (target : SizeFilteredNoAcceptedCodeSearchClosureTarget scale_data) :
    Nonempty
      (Σ lengthCodeAt : Nat → Nat,
        Σ enumeration :
          ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
            scale_data lengthCodeAt,
          Σ _ :
            ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput
              scale_data lengthCodeAt enumeration,
            ComputableSearchGapCertificate
              (month9_month10_checkedProofCodeMeasured
                scale_data
                (concretePAHilbertPowerBoundCalibratedCheckerSemantics
                  scale_data lengthCodeAt).toProofCodeSemantics)) := by
  rcases target with ⟨lengthCodeAt, enumeration, search⟩
  exact
    ⟨⟨lengthCodeAt, enumeration, search,
      calibratedNoAcceptedCodeSearch_checkedMeasuredSearchGap search⟩⟩

theorem sizeFilteredRejectionSearchClosureTarget_to_checkedMeasuredSearchGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (target : SizeFilteredRejectionSearchClosureTarget scale_data) :
    Nonempty
      (Σ lengthCodeAt : Nat → Nat,
        Σ enumeration :
          ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
            scale_data lengthCodeAt,
          Σ _ :
            ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
              scale_data lengthCodeAt enumeration,
            ComputableSearchGapCertificate
              (month9_month10_checkedProofCodeMeasured
                scale_data
                (concretePAHilbertPowerBoundCalibratedCheckerSemantics
                  scale_data lengthCodeAt).toProofCodeSemantics)) := by
  rcases target with ⟨lengthCodeAt, enumeration, rejection_search⟩
  exact
    ⟨⟨lengthCodeAt, enumeration, rejection_search,
      calibratedRejectionSearch_checkedMeasuredSearchGap rejection_search⟩⟩

/--
Combined audit ledger for the old lower-bound routes.

It records the three independent obstructions exposed above:

* the current root `actualProofLengthMeasured` is polynomially bounded;
* the native concrete power-bound checker has short accepted codes;
* the current toy CnBox PA semantics gives the finite-consistency family length
  zero.

This is not a new assumption.  It is the Lean-checked reason that the remaining
work cannot be solved by renaming `tail_gap` or by reusing the present toy
checker/root semantics.
-/
theorem currentLowerBoundRouteObstructionLedger
    (scale_data : InternalPudlakTheorem5ScaleData) :
    (ActualProofLengthSearchGapTarget scale_data → False) ∧
      (Nonempty
          (ComputableSearchGapCertificate
            (fun n : Nat =>
              month9_month10_checkedProofCodeMeasured scale_data
                (concretePAHilbertPowerBoundCheckerSemantics
                  scale_data).toProofCodeSemantics n)) →
        False) ∧
      (BoundedArithmeticLab.EventualLowerBound
          BoundedArithmeticLab.BoundedProofPredicate.canonicalCnBoxPABox →
        False) :=
  ⟨no_actualProofLengthSearchGapTarget_currentRoot scale_data,
    no_nativePowerBoundCheckedMeasuredSearchGap scale_data,
    no_currentToyCanonicalCnBoxEventualLowerBound⟩

/--
The proof-length-free lower-gap source is the exact positive layer that can be
closed without root `proof_length`: it consists of proof-code semantics, a finite
small-code search, and a computable finite-search exclusion certificate.
-/
def ProofLengthFreeLowerGapClosureTarget
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  Nonempty
    (Σ sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
      Σ search : InternalPudlakTheorem5SmallCodeSearch scale_data sem,
        InternalPudlakTheorem5ComputableFiniteSearchExclusion
          scale_data sem search)

/--
From the fully exposed proof-length-free lower-gap target, Lean constructs the
checked measured search gap.  No root `proof_length`, no `tail_gap`, and no
proof-length exactness field is used in this step.
-/
theorem proofLengthFreeLowerGapClosureTarget_to_checkedMeasuredSearchGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (target : ProofLengthFreeLowerGapClosureTarget scale_data) :
    Nonempty
      (Σ sem :
        _root_.ProofCodeSemantics.{0}
          (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
        ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured scale_data sem)) := by
  rcases target with ⟨sem, search, cert⟩
  exact
    ⟨⟨sem,
      month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
        (scale_data := scale_data) (sem := sem) (search := search) cert⟩⟩

/--
Root exactness needed to turn a proof-length-free checked source into the actual
project `proof_length` lower gap.  This is the hard residual: it identifies the
project-level PA/symbol-size proof length with the checked proof-code minimum on
the theorem-5 power-bound family.
-/
def ProofLengthFreeSourceRootExactness
    (source : PAHilbertProofLengthFreeLowerGapSource) : Prop :=
  ∀ n : Nat,
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (source.scale_data.powerBoundRawCode n) =
      source.measured n

/--
If a proof-length-free source is also root-exact, its checked gap transports to
the actual project proof-length gap.  This isolates the exact place where root
`proof_length` must be replaced by genuine PA/Hilbert proof-code semantics.
-/
def proofLengthFreeSource_and_rootExactness_to_actualProofLengthGap
    (source : PAHilbertProofLengthFreeLowerGapSource)
    (rootExact : ProofLengthFreeSourceRootExactness source) :
    ComputableSearchGapCertificate
      (actualProofLengthMeasured source.scale_data) where
  gap_for_polynomial_upper := by
    intro U hU
    let g := source.checkedGap.gap_for_polynomial_upper U hU
    exact
      { witness := g.witness
        witness_ge := g.witness_ge
        strict_at_witness := by
          intro N
          have hstrict := g.strict_at_witness N
          simpa [actualProofLengthMeasured,
            ProofLengthFreeSourceRootExactness,
            rootExact (g.witness N)] using hstrict }

/--
Under the current root formula-code-size semantics, no proof-length-free source
can also be root-exact.  The source may generate a genuine checked measured gap,
but identifying that measured function with the present root `proof_length` would
contradict the polynomial fallback already proved above.
-/
theorem no_proofLengthFreeSourceRootExactness_currentRoot
    (source : PAHilbertProofLengthFreeLowerGapSource) :
    ProofLengthFreeSourceRootExactness source → False := by
  intro rootExact
  exact no_actualProofLengthSearchGapTarget_currentRoot source.scale_data
    ⟨proofLengthFreeSource_and_rootExactness_to_actualProofLengthGap
      source rootExact⟩

/--
The completely exposed root-closed theorem-5 lower-bound target.

This is the smallest remaining package after opening the former `tail_gap`,
`rejection_search`, and checker exactness boxes: a proof-length-free checked
source, plus the root exactness that identifies that checked measurement with
the project-level PA/symbol-size `proof_length` on the theorem-5 family.
-/
structure RootClosedTheorem5LowerBoundWitness : Type 1 where
  source : PAHilbertProofLengthFreeLowerGapSource
  rootExact : ProofLengthFreeSourceRootExactness source

def RootClosedTheorem5LowerBoundTarget : Prop :=
  Nonempty RootClosedTheorem5LowerBoundWitness

/--
A root-closed theorem-5 target gives the actual proof-length search gap used by
the collision proof.  No additional `tail_gap` field is introduced here.
-/
theorem rootClosedTheorem5LowerBoundTarget_to_actualProofLengthSearchGapTarget :
    RootClosedTheorem5LowerBoundTarget →
      ∃ scale_data : InternalPudlakTheorem5ScaleData,
        ActualProofLengthSearchGapTarget scale_data := by
  intro target
  rcases target with ⟨witness⟩
  exact
    ⟨witness.source.scale_data,
      ⟨proofLengthFreeSource_and_rootExactness_to_actualProofLengthGap
        witness.source witness.rootExact⟩⟩

/--
The same root-closed target gives the pointwise lower witness formulation: for
every polynomial upper bound and every starting cutoff, the computed lower
search witness is already above the polynomial upper.
-/
theorem rootClosedTheorem5LowerBoundTarget_to_actualProofLengthPointwiseSearchGapTarget :
    RootClosedTheorem5LowerBoundTarget →
      ∃ scale_data : InternalPudlakTheorem5ScaleData,
        ActualProofLengthPointwiseSearchGapTarget scale_data := by
  intro target
  rcases target with ⟨witness⟩
  let gap :=
    proofLengthFreeSource_and_rootExactness_to_actualProofLengthGap
      witness.source witness.rootExact
  refine ⟨witness.source.scale_data, ⟨gap, ?_⟩⟩
  intro U hU N
  exact (gap.gap_for_polynomial_upper U hU).strict_at_witness N

/--
Current-root no-go for the fully exposed target.  With the present
formula-code-size root semantics, even the minimal root-closed theorem-5 target
cannot exist.
-/
theorem no_rootClosedTheorem5LowerBoundTarget_currentRoot :
    RootClosedTheorem5LowerBoundTarget → False := by
  intro target
  rcases target with ⟨witness⟩
  exact no_proofLengthFreeSourceRootExactness_currentRoot
    witness.source witness.rootExact

/--
The old "final exact checker-core input" is not an independent proof of the
Pudlak lower bound.  Once opened, it is exactly a root-closed theorem-5 witness:
the proof-length-free lower source is generated from its rejection extractor,
and the root exactness is its proof-length calibration field.
-/
def finalExactCheckerCoreInput_toRootClosedTheorem5LowerBoundWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data) :
    RootClosedTheorem5LowerBoundWitness where
  source :=
    { scale_data := input.toCanonicalCalibratedExactnessCore.scale_data
      proof_code_semantics :=
        input.toCanonicalCalibratedExactnessCore.checkerSemantics.toProofCodeSemantics
      small_code_search :=
        input.toCanonicalCalibratedExactnessCore.finiteEnumeration.toSmallCodeSearch
      computable_search_exclusion :=
        input.toCanonicalCalibratedExactnessCore.rejectionExtractor
          |>.toComputableFiniteSearchExclusion }
  rootExact := by
    intro n
    simpa [PAHilbertProofLengthFreeLowerGapSource.measured,
      month9_month10_checkedProofCodeMeasured,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
      using input.toCanonicalCalibratedExactnessCore.proofLengthExactness
        |>.at_powerBoundRawCode n

/--
Therefore a nonempty old final exact checker-core input immediately gives the
minimal root-closed theorem-5 target.
-/
theorem finalExactCheckerCoreInput_toRootClosedTheorem5LowerBoundTarget
    {scale_data : InternalPudlakTheorem5ScaleData} :
    Nonempty
        (ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
          scale_data) →
      RootClosedTheorem5LowerBoundTarget := by
  intro hinput
  rcases hinput with ⟨input⟩
  exact ⟨finalExactCheckerCoreInput_toRootClosedTheorem5LowerBoundWitness
    input⟩

/--
Current-root no-go for the old final exact checker-core input.  This rules out
the tempting interpretation that the old endpoint had already closed the lower
bound: under the present formula-code-size root, that input itself cannot exist.
-/
theorem no_finalExactCheckerCoreInput_currentRoot
    (scale_data : InternalPudlakTheorem5ScaleData) :
    Nonempty
        (ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
          scale_data) →
      False := by
  intro hinput
  exact no_rootClosedTheorem5LowerBoundTarget_currentRoot
    (finalExactCheckerCoreInput_toRootClosedTheorem5LowerBoundTarget
      hinput)

/--
Gap-free theorem-5 closure target.  Unlike the old final exact checker-core
input, this target does not contain a `proof_length_gap` field.  Its hard lower
content is the computable finite-search exclusion certificate, plus calibration
of the induced proof-code minimum to root `proof_length`.
-/
def GapFreeTheorem5ClosureTarget : Prop :=
  Nonempty InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}

/--
A computable finite-search no-small-code core is exactly the proof object needed
for the root-closed theorem-5 witness, without passing through a prebuilt
`proof_length_gap` field.
-/
def computableFiniteSearchNoSmallCore_toRootClosedTheorem5LowerBoundWitness
    (core : InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0}) :
    RootClosedTheorem5LowerBoundWitness where
  source :=
    { scale_data := core.scale_data
      proof_code_semantics := core.proof_length_model.proof_code_semantics
      small_code_search := core.small_code_search
      computable_search_exclusion := core.computable_search_exclusion }
  rootExact := by
    intro n
    have hexact :
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (core.scale_data.powerBoundRawCode n) =
          (core.proof_length_model.proof_code_semantics.minProofCodeSize
            (core.scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) :=
      core.calibration.proof_length_eq_minProofCodeSize
        (code := core.scale_data.powerBoundRawCode n) ⟨n, rfl⟩
    simpa [PAHilbertProofLengthFreeLowerGapSource.measured,
      month9_month10_checkedProofCodeMeasured] using hexact

theorem gapFreeTheorem5ClosureTarget_to_rootClosedTheorem5LowerBoundTarget :
    GapFreeTheorem5ClosureTarget →
      RootClosedTheorem5LowerBoundTarget := by
  intro htarget
  rcases htarget with ⟨core⟩
  exact
    ⟨computableFiniteSearchNoSmallCore_toRootClosedTheorem5LowerBoundWitness
      core⟩

/--
Current-root no-go for the gap-free theorem-5 target.  This is the cleanest
negative probe: even the target without a prebuilt `proof_length_gap` cannot be
closed until root `proof_length` is replaced or calibrated to a genuine
PA/Hilbert proof-code semantics.
-/
theorem no_gapFreeTheorem5ClosureTarget_currentRoot :
    GapFreeTheorem5ClosureTarget → False := by
  intro htarget
  exact no_rootClosedTheorem5LowerBoundTarget_currentRoot
    (gapFreeTheorem5ClosureTarget_to_rootClosedTheorem5LowerBoundTarget
      htarget)

/--
Direct opened content of `computable_search_exclusion`.

This removes the candidate-list wrapper: for every polynomial upper `f` and
every starting threshold `N`, it gives a witness index `n`, a cutoff `K > f n`,
and proves that no accepted proof code of size `< K` exists for the theorem-5
formula at `n`.
-/
structure ComputableNoAcceptedBelowCutoff
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Type 1 where
  witness : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  cutoff : ∀ f : Nat → Real, _root_.is_polynomial_bound f → Nat → Nat
  witness_ge :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      N ≤ witness f hf N
  cutoff_gt :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      f (witness f hf N) < (cutoff f hf N : Real)
  noAcceptedBelowAtWitness :
    ∀ f : Nat → Real, ∀ hf : _root_.is_polynomial_bound f, ∀ N : Nat,
      ∀ c : sem.Code,
        sem.size c < cutoff f hf N →
          ¬ sem.checks c
            (scale_data.powerBoundRawCode (witness f hf N))

/--
Root-free lower-bound form: the checked minimum accepted proof-code size itself
beats every polynomial.  This is the semantic lower-bound theorem needed before
any calibration to project `proof_length`.
-/
def CheckedMinProofCodeStrongLowerBound
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Prop :=
  ∀ f : Nat → Real, _root_.is_polynomial_bound f →
    ∃ᶠ n in Filter.atTop,
      (sem.minProofCodeSize
        (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > f n

namespace ComputableNoAcceptedBelowCutoff

/--
The direct no-accepted-below statement immediately yields the no-small-code
inequality at the computed witness.
-/
theorem noSmallAtWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (opened : ComputableNoAcceptedBelowCutoff scale_data sem)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    ∀ c : sem.Code,
      sem.checks c (scale_data.powerBoundRawCode (opened.witness f hf N)) →
        f (opened.witness f hf N) < (sem.size c : Real) := by
  intro c hchecks
  by_contra hnot_lt
  have hsize_le_f : (sem.size c : Real) ≤ f (opened.witness f hf N) :=
    le_of_not_gt hnot_lt
  have hsize_lt_K_real :
      (sem.size c : Real) < (opened.cutoff f hf N : Real) :=
    lt_of_le_of_lt hsize_le_f (opened.cutoff_gt f hf N)
  have hsize_lt_K : sem.size c < opened.cutoff f hf N := by
    exact_mod_cast hsize_lt_K_real
  exact opened.noAcceptedBelowAtWitness f hf N c hsize_lt_K hchecks

/--
The direct no-accepted-below statement gives the lower bound for the minimum
accepted proof-code size at the computed witness.
-/
theorem minProofCodeSize_gt_at_witness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (opened : ComputableNoAcceptedBelowCutoff scale_data sem)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    (sem.minProofCodeSize
      (scale_data.powerBoundRawCode (opened.witness f hf N))
      ⟨opened.witness f hf N, rfl⟩ : Real) >
      f (opened.witness f hf N) := by
  rcases sem.hasProofCodeOfSize_minProofCodeSize
      (code := scale_data.powerBoundRawCode (opened.witness f hf N))
      ⟨opened.witness f hf N, rfl⟩ with
    ⟨c, hchecks, hsize_le⟩
  have hlt_size :
      f (opened.witness f hf N) < (sem.size c : Real) :=
    opened.noSmallAtWitness f hf N c hchecks
  have hsize_le_min :
      (sem.size c : Real) ≤
        (sem.minProofCodeSize
          (scale_data.powerBoundRawCode (opened.witness f hf N))
          ⟨opened.witness f hf N, rfl⟩ : Real) := by
    exact_mod_cast hsize_le
  exact lt_of_lt_of_le hlt_size hsize_le_min

/--
The direct no-accepted-below layer produces the checked-measured search gap
without any `tail_gap`, `proof_length_gap`, or candidate-rejection field.
-/
def toCheckedMeasuredSearchGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (opened : ComputableNoAcceptedBelowCutoff scale_data sem) :
    ComputableSearchGapCertificate
      (month9_month10_checkedProofCodeMeasured scale_data sem) where
  gap_for_polynomial_upper := by
    intro U hU
    exact
      { witness := opened.witness U hU
        witness_ge := opened.witness_ge U hU
        strict_at_witness := by
          intro N
          simpa [month9_month10_checkedProofCodeMeasured] using
            opened.minProofCodeSize_gt_at_witness U hU N }

/-- The opened no-accepted-below target is exactly a root-free checked minimum
proof-code lower bound. -/
theorem toCheckedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (opened : ComputableNoAcceptedBelowCutoff scale_data sem) :
    CheckedMinProofCodeStrongLowerBound scale_data sem := by
  intro f hf
  exact
    Filter.frequently_atTop.2
      (fun N =>
        ⟨opened.witness f hf N,
          opened.witness_ge f hf N,
          opened.minProofCodeSize_gt_at_witness f hf N⟩)

end ComputableNoAcceptedBelowCutoff

/-- Chosen witness extracted from a root-free checked minimum lower bound. -/
noncomputable def checkedMinProofCodeStrongLowerBoundWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (hlower : CheckedMinProofCodeStrongLowerBound scale_data sem)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    Nat :=
  Classical.choose ((Filter.frequently_atTop.mp (hlower f hf)) N)

theorem checkedMinProofCodeStrongLowerBoundWitness_spec
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (hlower : CheckedMinProofCodeStrongLowerBound scale_data sem)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    N ≤ checkedMinProofCodeStrongLowerBoundWitness hlower f hf N ∧
      (sem.minProofCodeSize
        (scale_data.powerBoundRawCode
          (checkedMinProofCodeStrongLowerBoundWitness hlower f hf N))
        ⟨checkedMinProofCodeStrongLowerBoundWitness hlower f hf N, rfl⟩ :
          Real) >
        f (checkedMinProofCodeStrongLowerBoundWitness hlower f hf N) :=
  Classical.choose_spec ((Filter.frequently_atTop.mp (hlower f hf)) N)

theorem checkedMinProofCodeStrongLowerBoundWitness_ge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (hlower : CheckedMinProofCodeStrongLowerBound scale_data sem)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    N ≤ checkedMinProofCodeStrongLowerBoundWitness hlower f hf N :=
  (checkedMinProofCodeStrongLowerBoundWitness_spec hlower f hf N).1

theorem checkedMinProofCodeStrongLowerBoundWitness_gt
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (hlower : CheckedMinProofCodeStrongLowerBound scale_data sem)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    (sem.minProofCodeSize
      (scale_data.powerBoundRawCode
        (checkedMinProofCodeStrongLowerBoundWitness hlower f hf N))
      ⟨checkedMinProofCodeStrongLowerBoundWitness hlower f hf N, rfl⟩ :
        Real) >
      f (checkedMinProofCodeStrongLowerBoundWitness hlower f hf N) :=
  (checkedMinProofCodeStrongLowerBoundWitness_spec hlower f hf N).2

/--
A root-free checked minimum proof-code lower bound reconstructs the opened
no-accepted-below certificate by taking the cutoff to be the minimum accepted
proof-code size at the chosen witness.
-/
noncomputable def checkedMinProofCodeStrongLowerBound_toNoAcceptedBelowCutoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (hlower : CheckedMinProofCodeStrongLowerBound scale_data sem) :
    ComputableNoAcceptedBelowCutoff scale_data sem where
  witness := checkedMinProofCodeStrongLowerBoundWitness hlower
  cutoff := fun f hf N =>
    sem.minProofCodeSize
      (scale_data.powerBoundRawCode
        (checkedMinProofCodeStrongLowerBoundWitness hlower f hf N))
      ⟨checkedMinProofCodeStrongLowerBoundWitness hlower f hf N, rfl⟩
  witness_ge := checkedMinProofCodeStrongLowerBoundWitness_ge hlower
  cutoff_gt := by
    intro f hf N
    exact checkedMinProofCodeStrongLowerBoundWitness_gt hlower f hf N
  noAcceptedBelowAtWitness := by
    intro f hf N c hsize hchecks
    have hmin_le_size :
        sem.minProofCodeSize
            (scale_data.powerBoundRawCode
              (checkedMinProofCodeStrongLowerBoundWitness hlower f hf N))
            ⟨checkedMinProofCodeStrongLowerBoundWitness hlower f hf N, rfl⟩ ≤
          sem.size c :=
      sem.minProofCodeSize_le_of_hasProofCodeOfSize
        ⟨checkedMinProofCodeStrongLowerBoundWitness hlower f hf N, rfl⟩
        ⟨c, hchecks, le_rfl⟩
    exact (not_lt_of_ge hmin_le_size) hsize

/--
The checked-minimum lower bound is equivalent to the standard no-small-proof-code
form used by the theorem-5 internal surfaces.
-/
theorem checkedMinProofCodeStrongLowerBound_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (hlower : CheckedMinProofCodeStrongLowerBound scale_data sem) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data sem := by
  intro f hf
  exact
    (hlower f hf).mono
      (fun n hmin_gt c hchecks => by
        have hmin_le_size :
            sem.minProofCodeSize
                (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ ≤
              sem.size c :=
          sem.minProofCodeSize_le_of_hasProofCodeOfSize
            ⟨n, rfl⟩ ⟨c, hchecks, le_rfl⟩
        have hmin_le_size_real :
            (sem.minProofCodeSize
                (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
              (sem.size c : Real) := by
          exact_mod_cast hmin_le_size
        exact lt_of_lt_of_le hmin_gt hmin_le_size_real)

/-- The standard no-small-proof-code form gives the checked-minimum lower bound. -/
theorem noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (hno : InternalPudlakTheorem5NoSmallProofCodes scale_data sem) :
    CheckedMinProofCodeStrongLowerBound scale_data sem :=
  InternalPudlakTheorem5NoSmallProofCodes.toProofCodeLowerBound hno

/-- Exact statement of the remaining root-free theorem-5 lower-bound gap. -/
theorem checkedMinProofCodeStrongLowerBound_iff_noSmallProofCodes
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    CheckedMinProofCodeStrongLowerBound scale_data sem ↔
      InternalPudlakTheorem5NoSmallProofCodes scale_data sem :=
  ⟨checkedMinProofCodeStrongLowerBound_to_noSmallProofCodes,
    noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound⟩

/--
Current shortest root-free growth obligation: prove that the checked minimum
accepted proof-code size for the theorem-5 family eventually beats every
polynomial bound.  This is only a name for the exact target above; it introduces
no new assumption and deliberately avoids `tail_gap` and root `proof_length`.
-/
abbrev ShortestCheckedMinProofCodeGrowthObligation
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Prop :=
  CheckedMinProofCodeStrongLowerBound scale_data sem

/--
The named shortest growth obligation is exactly the theorem-5 no-small-proof-code
statement at the checked proof-code layer.
-/
theorem shortestCheckedMinProofCodeGrowthObligation_iff_noSmallProofCodes
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data sem ↔
      InternalPudlakTheorem5NoSmallProofCodes scale_data sem :=
  checkedMinProofCodeStrongLowerBound_iff_noSmallProofCodes scale_data sem

/--
The exact obstruction to theorem-5 no-small proof codes: from some threshold
on, a single polynomial bound controls one accepted proof code for every target
formula.  This is the accepted-code analogue of
`BAEventuallyPolynomialProofObjectFamily`.
-/
def InternalPudlakTheorem5EventuallyPolynomialAcceptedCodeFamily
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Prop :=
  ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
    ∃ N : Nat,
      ∀ n : Nat, N ≤ n →
        ∃ c : sem.Code,
          sem.checks c (scale_data.powerBoundRawCode n) ∧
            (sem.size c : Real) ≤ U n

theorem noSmallProofCodes_to_no_eventualPolynomialAcceptedCodeFamily
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (hno : InternalPudlakTheorem5NoSmallProofCodes scale_data sem) :
    ¬ InternalPudlakTheorem5EventuallyPolynomialAcceptedCodeFamily
        scale_data sem := by
  intro hfamily
  rcases hfamily with ⟨U, hU, N, hcodes⟩
  rcases (Filter.frequently_atTop.mp (hno U hU)) N with
    ⟨n, hn_ge, hno_small⟩
  rcases hcodes n hn_ge with ⟨c, hchecks, hsize_le⟩
  exact (not_lt_of_ge hsize_le) (hno_small c hchecks)

theorem no_eventualPolynomialAcceptedCodeFamily_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (hno_family :
      ¬ InternalPudlakTheorem5EventuallyPolynomialAcceptedCodeFamily
          scale_data sem) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data sem := by
  intro U hU
  refine Filter.frequently_atTop.2 ?_
  intro N
  by_contra hno_witness
  have htail :
      ∀ n : Nat, N ≤ n →
        ∃ c : sem.Code,
          sem.checks c (scale_data.powerBoundRawCode n) ∧
            (sem.size c : Real) ≤ U n := by
    intro n hn_ge
    have hnot_all :
        ¬ ∀ c : sem.Code,
            sem.checks c (scale_data.powerBoundRawCode n) →
              U n < (sem.size c : Real) := by
      intro hall
      exact hno_witness ⟨n, hn_ge, hall⟩
    rcases not_forall.mp hnot_all with ⟨c, hc_not⟩
    have hchecks : sem.checks c (scale_data.powerBoundRawCode n) := by
      by_contra hnot_checks
      exact hc_not (fun hchecks => False.elim (hnot_checks hchecks))
    have hnot_lt : ¬ U n < (sem.size c : Real) := by
      intro hlt
      exact hc_not (fun _hchecks => hlt)
    exact ⟨c, hchecks, le_of_not_gt hnot_lt⟩
  exact hno_family ⟨U, hU, N, htail⟩

/--
The theorem-5 no-small-code statement is exactly the absence of an eventual
polynomial-size accepted-code family.
-/
theorem noSmallProofCodes_iff_no_eventualPolynomialAcceptedCodeFamily
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data sem ↔
      ¬ InternalPudlakTheorem5EventuallyPolynomialAcceptedCodeFamily
          scale_data sem :=
  ⟨noSmallProofCodes_to_no_eventualPolynomialAcceptedCodeFamily,
    no_eventualPolynomialAcceptedCodeFamily_to_noSmallProofCodes⟩

/--
Root proof-length lower bound plus accepted-code soundness rules out every
eventual polynomial accepted-code family.

This is the most direct paper-proof spine for the lower side: Pudlak supplies
that the actual PA proof length of `powerBoundRawCode n` frequently beats every
polynomial, while checker soundness says every accepted checked code has size at
least that actual PA proof length.
-/
theorem powerBoundLowerBound_and_allCheckedCode_size_ge_actual_to_no_eventualPolynomialAcceptedCodeFamily
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (checked_code_size_ge_actual :
      ∀ n : Nat, ∀ c : sem.Code,
        sem.checks c (scale_data.powerBoundRawCode n) →
          actualProofLengthMeasured scale_data n ≤ (sem.size c : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    ¬ InternalPudlakTheorem5EventuallyPolynomialAcceptedCodeFamily
        scale_data sem := by
  intro hfamily
  rcases hfamily with ⟨U, hU, N, hcodes⟩
  rcases
      (Filter.frequently_atTop.mp
        (hlower.frequently_beats_every_polynomial U hU)) N with
    ⟨n, hn_ge, hactual_gt_U⟩
  rcases hcodes n hn_ge with ⟨c, hchecks, hsize_le_U⟩
  have hactual_gt_U_project :
      actualProofLengthMeasured scale_data n > U n := by
    simpa [actualProofLengthMeasured,
      InternalPudlakTheorem5ScaleData.powerBoundRawCode] using
      hactual_gt_U
  have hactual_le_size :
      actualProofLengthMeasured scale_data n ≤ (sem.size c : Real) :=
    checked_code_size_ge_actual n c hchecks
  linarith

/--
The same root proof-length lower-bound spine closes theorem-5 no-small proof
codes directly, without introducing `tail_gap`, candidate rejection, or a
finite-search wrapper.
-/
theorem powerBoundLowerBound_and_allCheckedCode_size_ge_actual_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (checked_code_size_ge_actual :
      ∀ n : Nat, ∀ c : sem.Code,
        sem.checks c (scale_data.powerBoundRawCode n) →
          actualProofLengthMeasured scale_data n ≤ (sem.size c : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data sem :=
  no_eventualPolynomialAcceptedCodeFamily_to_noSmallProofCodes
    (powerBoundLowerBound_and_allCheckedCode_size_ge_actual_to_no_eventualPolynomialAcceptedCodeFamily
      checked_code_size_ge_actual hlower)

/--
Checker proof-length exactness is one way to discharge the accepted-code
soundness premise above.  The theorem is stated separately so that the residual
is visible: either prove this exactness for the real checker, or replace it by a
more direct accepted-code soundness proof.
-/
theorem powerBoundLowerBound_and_checkerProofLengthExactness_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (exactness : InternalPudlakTheorem5CheckerProofLengthExactness checker)
    (hlower : scale_data.PowerBoundLowerBound) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      checker.toProofCodeSemantics :=
  powerBoundLowerBound_and_allCheckedCode_size_ge_actual_to_noSmallProofCodes
    (allCheckedCode_size_ge_actual_of_checkerProofLengthExactness exactness)
    hlower

/--
Specialized PA/Hilbert natural-code version of the short paper proof.

The residual is now stated at the exact accepted-code predicate:
every accepted numeric PA/Hilbert proof code for `powerBoundRawCode n` has code
value at least the root actual PA proof length.  Together with Pudlak's root
proof-length lower bound, this closes theorem-5 no-small proof codes for the
accepted-natural-code checker semantics.
-/
theorem powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (accepted_code_size_ge_actual :
      ∀ n : Nat, ∀ code : Nat,
        PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code →
          actualProofLengthMeasured scale_data n ≤ (code : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  powerBoundLowerBound_and_allCheckedCode_size_ge_actual_to_noSmallProofCodes
    (scale_data := scale_data)
    (sem := (PAHilbertAcceptedNatCodeCheckerSemantics
      scale_data checker completion).toProofCodeSemantics)
    (by
      intro n code hchecks
      exact accepted_code_size_ge_actual n code
        (by
          simpa [
            InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
            PAHilbertAcceptedNatCodeCheckerSemantics] using hchecks))
    hlower

/--
The older PA/Hilbert proof-length exactness package implies the weaker
accepted-code soundness inequality needed by the short paper proof.

This is a debt-reduction lemma: downstream theorem 5 does not need full
equality with the minimum accepted code size, only the one-sided fact that every
accepted numeric code is at least the actual PA proof length.
-/
theorem paHilbertAcceptedNatCode_soundness_of_proofLengthExactnessData
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (exactness :
      PAHilbertAcceptedNatCodeProofLengthExactnessData
        scale_data checker completion) :
    ∀ n : Nat, ∀ code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) code →
        actualProofLengthMeasured scale_data n ≤ (code : Real) := by
  intro n code haccepted
  let sem :=
    (PAHilbertAcceptedNatCodeCheckerSemantics
      scale_data checker completion).toProofCodeSemantics
  have hactual_eq_min :
      actualProofLengthMeasured scale_data n =
        (sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) := by
    simpa [actualProofLengthMeasured, sem] using
      exactness.proof_length_eq_minProofCodeSize
        (scale_data.powerBoundRawCode n) ⟨n, rfl⟩
  have hmin_le_code_nat :
      sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ ≤
        code :=
    sem.minProofCodeSize_le_of_hasProofCodeOfSize
      (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩
      ⟨code,
        (by
          simpa [sem,
            InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
            PAHilbertAcceptedNatCodeCheckerSemantics] using haccepted),
        le_rfl⟩
  have hmin_le_code :
      (sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
        (code : Real) := by
    exact_mod_cast hmin_le_code_nat
  exact hactual_eq_min.le.trans hmin_le_code

/--
One layer below accepted numeric-code soundness: it is enough to prove that
each accepted decoded PA/Hilbert proof object is a genuine PA proof whose root
symbol-size proof length is bounded by the object's own numeric code.

The decoder supplies `proof.code = code`, so this object-level length soundness
immediately gives the natural-code inequality used by the short proof.
-/
theorem paHilbertAcceptedNatCode_soundness_of_acceptedProofObjectLengthSound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (accepted_object_length_sound :
      ∀ formulaCode : _root_.FormulaCode,
        ∀ proof : PAHilbertProofObject,
          proof.conclusion.code = formulaCode →
            checker.accepts proof proof.conclusion = true →
              _root_.proof_length _root_.ProofSystem.PA
                _root_.ProofLengthMeasure.symbolSize formulaCode ≤
                  (proof.code : Real)) :
    ∀ n : Nat, ∀ code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) code →
        actualProofLengthMeasured scale_data n ≤ (code : Real) := by
  intro n code haccepted
  rcases haccepted with ⟨proof, hdecode, hconclusion, haccepts⟩
  have hactual_le_proofCode :
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) ≤
        (proof.code : Real) :=
    accepted_object_length_sound
      (scale_data.powerBoundRawCode n) proof hconclusion haccepts
  have hproof_code_eq : proof.code = code :=
    checker.decoder.decodedCode_eq code proof hdecode
  simpa [actualProofLengthMeasured, hproof_code_eq] using
    hactual_le_proofCode

/--
Theorem-5 no-small proof codes from Pudlak's root lower bound plus the
object-level accepted-proof length soundness above.
-/
theorem powerBoundLowerBound_and_paHilbertAcceptedProofObjectLengthSound_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (accepted_object_length_sound :
      ∀ formulaCode : _root_.FormulaCode,
        ∀ proof : PAHilbertProofObject,
          proof.conclusion.code = formulaCode →
            checker.accepts proof proof.conclusion = true →
              _root_.proof_length _root_.ProofSystem.PA
                _root_.ProofLengthMeasure.symbolSize formulaCode ≤
                  (proof.code : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_to_noSmallProofCodes
    (checker := checker)
    (completion := completion)
    (paHilbertAcceptedNatCode_soundness_of_acceptedProofObjectLengthSound
      accepted_object_length_sound)
    hlower

/--
Current-root no-go for object-level accepted-proof length soundness on the
concrete power-bound checker.

At `n = 0` the checker accepts numeric code `0` for `powerBoundRawCode 0`,
while the present project root length is `scale 0 + 12`.  Therefore the desired
object-level statement cannot be proved against the current root
`proof_length`; the root length must be replaced or calibrated to a real
PA/Hilbert proof-code semantics.
-/
theorem no_concretePAHilbertPowerBound_acceptedProofObjectLengthSound_currentRoot
    (scale_data : InternalPudlakTheorem5ScaleData) :
    (∀ formulaCode : _root_.FormulaCode,
      ∀ proof : PAHilbertProofObject,
        proof.conclusion.code = formulaCode →
          (concretePAHilbertPowerBoundChecker scale_data).accepts
              proof proof.conclusion = true →
            _root_.proof_length _root_.ProofSystem.PA
              _root_.ProofLengthMeasure.symbolSize formulaCode ≤
                (proof.code : Real)) →
      False := by
  intro accepted_object_length_sound
  rcases
      concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
        scale_data 0 with
    ⟨proof, hdecode, hconclusion, haccepts⟩
  have hproof_code_zero : proof.code = 0 :=
    (concretePAHilbertPowerBoundChecker scale_data).decoder.decodedCode_eq
      0 proof hdecode
  have hle_root :
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode 0) ≤ 0 := by
    simpa [hproof_code_zero] using
      accepted_object_length_sound
        (scale_data.powerBoundRawCode 0) proof hconclusion haccepts
  have hroot_eq :
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode 0) =
        (scale_data.scale 0 : Real) + 12 := by
    simpa [actualProofLengthMeasured] using
      actualProofLengthMeasured_currentRoot_eq_scale_add_twelve scale_data 0
  have hscale_nonneg : (0 : Real) ≤ (scale_data.scale 0 : Real) := by
    exact_mod_cast Nat.zero_le (scale_data.scale 0)
  rw [hroot_eq] at hle_root
  nlinarith

/--
Direct current-root no-go for the exact short-proof obligation
`accepted_code_size_ge_actual` on the concrete power-bound checker.

The obstruction is already visible at the native numeric accepted-code level:
the checker accepts code `0` for `powerBoundRawCode 0`, while the current root
actual length of that formula is `scale 0 + 12`.
-/
theorem no_concretePAHilbertPowerBound_acceptedNatCodeSoundness_currentRoot
    (scale_data : InternalPudlakTheorem5ScaleData) :
    (∀ n : Nat, ∀ code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode n) code →
        actualProofLengthMeasured scale_data n ≤ (code : Real)) →
      False := by
  intro accepted_code_size_ge_actual
  have haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode 0) 0 :=
    concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
      scale_data 0
  have hle_actual_raw :
      actualProofLengthMeasured scale_data 0 ≤ ((0 : Nat) : Real) :=
    accepted_code_size_ge_actual 0 0 haccepted
  have hle_actual : actualProofLengthMeasured scale_data 0 ≤ (0 : Real) := by
    simpa using hle_actual_raw
  have hactual_eq :
      actualProofLengthMeasured scale_data 0 =
        (scale_data.scale 0 : Real) + 12 :=
    actualProofLengthMeasured_currentRoot_eq_scale_add_twelve scale_data 0
  have hscale_nonneg : (0 : Real) ≤ (scale_data.scale 0 : Real) := by
    exact_mod_cast Nat.zero_le (scale_data.scale 0)
  rw [hactual_eq] at hle_actual
  nlinarith

/--
Local semantic replacement for the root PA/Hilbert proof length on the
theorem-5 raw family.

Codes are decoded PA/Hilbert proof objects; a proof object checks a formula code
when the checker accepts it and its conclusion has that formula code.  The size
measure is the proof object's own numeric code.  This is the semantic model
against which object-level length soundness is automatic.
-/
def paHilbertAcceptedProofObjectCodeSemantics
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (completion : PAHilbertAcceptedNatCodeCompletion scale_data checker) :
    _root_.ProofCodeSemantics.{0}
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) where
  Code := PAHilbertProofObject
  checks := fun proof formulaCode =>
    checker.decoder.decode proof.code = some proof ∧
      proof.conclusion.code = formulaCode ∧
      checker.accepts proof proof.conclusion = true
  size := fun proof => proof.code
  complete := by
    intro formulaCode hformula
    rcases hformula with ⟨n, rfl⟩
    rcases completion.complete_at_powerBoundRawCode n with
      ⟨code, proof, _hdecode, hconclusion, haccepts⟩
    have hproof_code : proof.code = code :=
      checker.decoder.decodedCode_eq code proof _hdecode
    have hdecode_self :
        checker.decoder.decode proof.code = some proof := by
      simpa [hproof_code] using _hdecode
    exact ⟨proof, hdecode_self, hconclusion, haccepts⟩

/--
In the semantic proof-object model, every accepted proof object has code at
least the minimum semantic proof length for its conclusion.
-/
theorem paHilbertAcceptedProofObjectSemanticLength_le_code
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    {formulaCode : _root_.FormulaCode}
    (hformula :
      InternalPudlakTheorem5PowerBoundRelevantCode scale_data formulaCode)
    {proof : PAHilbertProofObject}
    (hdecode : checker.decoder.decode proof.code = some proof)
    (hconclusion : proof.conclusion.code = formulaCode)
    (haccepts : checker.accepts proof proof.conclusion = true) :
    ((paHilbertAcceptedProofObjectCodeSemantics
        scale_data checker completion).minProofCodeSize
          formulaCode hformula : Real) ≤
      (proof.code : Real) := by
  let sem :=
    paHilbertAcceptedProofObjectCodeSemantics
      scale_data checker completion
  have hhas : sem.HasProofCodeOfSize formulaCode proof.code :=
    ⟨proof, ⟨hdecode, hconclusion, haccepts⟩, le_rfl⟩
  have hle_nat :
      sem.minProofCodeSize formulaCode hformula ≤ proof.code :=
    sem.minProofCodeSize_le_of_hasProofCodeOfSize hformula hhas
  exact_mod_cast hle_nat

/--
Numeric accepted-code soundness for the semantic proof-object length.  The
decoder only identifies the input numeric code with the decoded proof object's
`proof.code`; the length inequality itself is the minimum-size property above.
-/
theorem paHilbertAcceptedProofObjectSemanticLength_le_acceptedNatCode
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    {n code : Nat}
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) code) :
    ((paHilbertAcceptedProofObjectCodeSemantics
        scale_data checker completion).minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
      (code : Real) := by
  rcases haccepted with ⟨proof, hdecode, hconclusion, haccepts⟩
  have hproof_code : proof.code = code :=
    checker.decoder.decodedCode_eq code proof hdecode
  have hdecode_self :
      checker.decoder.decode proof.code = some proof := by
    simpa [hproof_code] using hdecode
  have hle_proof :
      ((paHilbertAcceptedProofObjectCodeSemantics
          scale_data checker completion).minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
        (proof.code : Real) :=
    paHilbertAcceptedProofObjectSemanticLength_le_code
      (scale_data := scale_data)
      (checker := checker)
      (completion := completion)
      ⟨n, rfl⟩ hdecode_self hconclusion haccepts
  simpa [hproof_code] using hle_proof

/--
The concrete power-bound checker still accepts the canonical code `n` for
`F_n`.  Therefore even the root-free proof-object semantic minimum is at most
`n` for this toy checker.
-/
theorem concretePAHilbertPowerBoundProofObjectSemanticLength_le_index
    (scale_data : InternalPudlakTheorem5ScaleData) (n : Nat) :
    ((paHilbertAcceptedProofObjectCodeSemantics
        scale_data
        (concretePAHilbertPowerBoundChecker scale_data)
        (concretePAHilbertPowerBoundCompletion scale_data)).minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
      (n : Real) := by
  exact
    paHilbertAcceptedProofObjectSemanticLength_le_acceptedNatCode
      (scale_data := scale_data)
      (checker := concretePAHilbertPowerBoundChecker scale_data)
      (completion := concretePAHilbertPowerBoundCompletion scale_data)
      (n := n) (code := n)
      (concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
        scale_data n)

/--
Consequently the concrete power-bound checker cannot be the final carrier of
the PA/Hilbert proof-object semantic lower bound: its minimum is bounded by the
linear polynomial `n`.
-/
theorem no_concretePAHilbertPowerBoundProofObjectSemanticLowerBound
    (scale_data : InternalPudlakTheorem5ScaleData) :
    (∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data
            (concretePAHilbertPowerBoundChecker scale_data)
            (concretePAHilbertPowerBoundCompletion scale_data)).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n) →
      False := by
  intro hlower
  rcases
      (Filter.frequently_atTop.mp
        (hlower (fun n : Nat => (n : Real))
          nativeIdentityLength_polynomial)) 0 with
    ⟨n, _hn_ge, hgt⟩
  have hle :
      ((paHilbertAcceptedProofObjectCodeSemantics
          scale_data
          (concretePAHilbertPowerBoundChecker scale_data)
          (concretePAHilbertPowerBoundCompletion scale_data)).minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
        (n : Real) :=
    concretePAHilbertPowerBoundProofObjectSemanticLength_le_index
      scale_data n
  exact (not_lt_of_ge hle) hgt

/--
Root-free lower-bound bridge using the semantic PA/Hilbert proof-object length.
If that semantic minimum beats every polynomial frequently, theorem-5 no-small
accepted natural proof codes follow without the project root `proof_length`.
-/
theorem paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (semantic_lower_bound :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∃ᶠ n in Filter.atTop,
          ((paHilbertAcceptedProofObjectCodeSemantics
              scale_data checker completion).minProofCodeSize
                (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics := by
  have hchecked :
      CheckedMinProofCodeStrongLowerBound scale_data
        (paHilbertAcceptedProofObjectCodeSemantics
          scale_data checker completion) := by
    intro U hU
    exact semantic_lower_bound U hU
  have hno_obj :
      InternalPudlakTheorem5NoSmallProofCodes scale_data
        (paHilbertAcceptedProofObjectCodeSemantics
          scale_data checker completion) :=
    checkedMinProofCodeStrongLowerBound_to_noSmallProofCodes hchecked
  intro U hU
  exact
    (hno_obj U hU).mono
      (fun n hno_obj_at code hchecks => by
        have haccepted :
            PAHilbertAcceptedProofCodeForFormulaCode
              checker (scale_data.powerBoundRawCode n) code := by
          simpa [
            InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
            PAHilbertAcceptedNatCodeCheckerSemantics] using hchecks
        rcases haccepted with ⟨proof, hdecode, hconclusion, haccepts⟩
        have hproof_code : proof.code = code :=
          checker.decoder.decodedCode_eq code proof hdecode
        have hdecode_self :
            checker.decoder.decode proof.code = some proof := by
          simpa [hproof_code] using hdecode
        have hobjchecks :
            (paHilbertAcceptedProofObjectCodeSemantics
              scale_data checker completion).checks proof
                (scale_data.powerBoundRawCode n) :=
          ⟨hdecode_self, hconclusion, haccepts⟩
        have hlt_proof :
            U n <
              ((paHilbertAcceptedProofObjectCodeSemantics
                scale_data checker completion).size proof : Real) :=
          hno_obj_at proof hobjchecks
        simpa [paHilbertAcceptedProofObjectCodeSemantics,
          InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
          PAHilbertAcceptedNatCodeCheckerSemantics, hproof_code] using
          hlt_proof)

/--
Temporary compatibility route from the older PA/Hilbert proof-length exactness
data to theorem-5 no-small proof codes.  The short proof factors through the
weaker soundness inequality above, so future work can replace the exactness
input by a direct soundness proof.
-/
theorem powerBoundLowerBound_and_paHilbertAcceptedNatCodeProofLengthExactness_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (exactness :
      PAHilbertAcceptedNatCodeProofLengthExactnessData
        scale_data checker completion)
    (hlower : scale_data.PowerBoundLowerBound) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_to_noSmallProofCodes
    (checker := checker)
    (completion := completion)
    (paHilbertAcceptedNatCode_soundness_of_proofLengthExactnessData
      exactness)
    hlower

/--
The proof-length-free source already gives the root-free checked minimum lower
bound.  This is the clean lower-bound closure step: it does not mention
`tail_gap`, root `proof_length`, proof-length exactness, or payload predicates.
-/
theorem proofLengthFreeLowerGapSource_to_checkedMinProofCodeStrongLowerBound
    (source : PAHilbertProofLengthFreeLowerGapSource) :
    CheckedMinProofCodeStrongLowerBound
      source.scale_data source.proof_code_semantics := by
  intro f hf
  exact
    Filter.frequently_atTop.2
      (fun N =>
        ⟨source.computable_search_exclusion.witness f hf N,
          source.computable_search_exclusion.witness_ge f hf N,
          source.computable_search_exclusion.minProofCodeSize_gt_at_witness
            f hf N⟩)

/--
The fully exposed proof-length-free closure target also produces the checked
minimum lower bound, with the proof-code semantics kept visible.
-/
theorem proofLengthFreeLowerGapClosureTarget_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (target : ProofLengthFreeLowerGapClosureTarget scale_data) :
    ∃ sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
      CheckedMinProofCodeStrongLowerBound scale_data sem := by
  rcases target with ⟨sem, search, cert⟩
  let source : PAHilbertProofLengthFreeLowerGapSource :=
    { scale_data := scale_data
      proof_code_semantics := sem
      small_code_search := search
      computable_search_exclusion := cert }
  exact
    ⟨sem,
      proofLengthFreeLowerGapSource_to_checkedMinProofCodeStrongLowerBound
        source⟩

/--
The Month 9-10 checker computable-search profile is already enough for the
root-free checked minimum lower bound.  This is the most compact clean entry
point for a future PA/Hilbert executable checker construction.
-/
theorem checkerComputableSearchProfile_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (profile :
      InternalPudlakTheorem5CheckerComputableSearchProfile.{0}
        scale_data) :
    CheckedMinProofCodeStrongLowerBound
      scale_data profile.checker.toProofCodeSemantics :=
  proofLengthFreeLowerGapSource_to_checkedMinProofCodeStrongLowerBound
    (lowerGapSourceOfCheckerComputableSearchProfile profile)

/--
Direct checked-minimum lower-bound closure for the synthetic
super-polynomial carrier.  This proves that the proof-length-free checker
adapter is complete once the calibrated proof-code size itself is genuinely
super-polynomial.

This is still a model probe: it does not identify the synthetic carrier with
root `proof_length` or with genuine PA proof length.
-/
theorem superPolynomialCanonicalLength_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    CheckedMinProofCodeStrongLowerBound
      scale_data
      (concretePAHilbertPowerBoundCalibratedCheckerSemantics
        scale_data superPolynomialCanonicalLength).toProofCodeSemantics := by
  intro U hU
  exact
    Filter.frequently_atTop.2
      (fun N => by
        let gap := superPolynomialCanonicalLength_searchGap
        let w := (gap.gap_for_polynomial_upper U hU).witness N
        have hw_ge : N ≤ w :=
          (gap.gap_for_polynomial_upper U hU).witness_ge N
        have hstrict :
            U w < (superPolynomialCanonicalLength w : Real) :=
          (gap.gap_for_polynomial_upper U hU).strict_at_witness N
        have hmin_eq_nat :
            InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
              (concretePAHilbertPowerBoundCalibratedCheckerSemantics
                scale_data superPolynomialCanonicalLength)
              w =
                superPolynomialCanonicalLength w :=
          concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
            scale_data superPolynomialCanonicalLength w hinjective
        have hmin_eq :
            (((concretePAHilbertPowerBoundCalibratedCheckerSemantics
                scale_data superPolynomialCanonicalLength).toProofCodeSemantics
              |>.minProofCodeSize
                (scale_data.powerBoundRawCode w) ⟨w, rfl⟩) : Real) =
              (superPolynomialCanonicalLength w : Real) := by
          exact_mod_cast hmin_eq_nat
        refine ⟨w, hw_ge, ?_⟩
        simpa [hmin_eq] using hstrict)

/--
Direct strong-lower-bound obstruction for the native concrete powerBound
checker.  Its canonical accepted code has size at most `n`, so the checked
minimum cannot frequently beat the polynomial `n`.
-/
theorem no_nativePowerBoundCheckedMinProofCodeStrongLowerBound
    (scale_data : InternalPudlakTheorem5ScaleData) :
    CheckedMinProofCodeStrongLowerBound scale_data
        (concretePAHilbertPowerBoundCheckerSemantics
          scale_data).toProofCodeSemantics →
      False := by
  intro hlower
  rcases
      (Filter.frequently_atTop.mp
        (hlower (fun n : Nat => (n : Real))
          nativeIdentityLength_polynomial)) 0 with
    ⟨n, _hn_ge, hgt⟩
  have hle :
      ((concretePAHilbertPowerBoundCheckerSemantics
          scale_data).toProofCodeSemantics.minProofCodeSize
        (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
        (n : Real) := by
    simpa [month9_month10_checkedProofCodeMeasured] using
      nativePowerBoundCheckedMeasured_le_index scale_data n
  exact (not_lt_of_ge hle) hgt

/--
The same obstruction stated with the current shortest-growth name.  The native
power-bound checker is therefore ruled out as a carrier for the final lower
bound: a real PA/Hilbert proof-code semantics must replace it.
-/
theorem no_nativePowerBoundShortestCheckedMinProofCodeGrowthObligation
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
        (concretePAHilbertPowerBoundCheckerSemantics
          scale_data).toProofCodeSemantics →
      False :=
  no_nativePowerBoundCheckedMinProofCodeStrongLowerBound scale_data

/--
The Month 11-12 PA/Hilbert exactness core already implies the root-free checked
minimum lower bound.  This removes `tail_gap` and root `proof_length` from this
step; the remaining content is exactly the checker/extractor/finite-search core
carried by `PAHilbertCheckerExactnessCore`.
-/
theorem paHilbertCheckerExactnessCore_to_checkedMinProofCodeStrongLowerBound
    (core : PAHilbertCheckerExactnessCore.{0}) :
    CheckedMinProofCodeStrongLowerBound
      core.scale_data core.proof_code_semantics := by
  intro f hf
  exact
    Filter.frequently_atTop.2
      (fun N =>
        ⟨core.computableSearchWitness f hf N,
          core.computableSearchWitness_ge f hf N,
          core.computableSearchMinProofCodeSize_gt f hf N⟩)

/-- The bounded-arithmetic sidecar uses the same polynomial-bound shape. -/
theorem rootPolynomialBound_to_boundedArithmeticPolynomialBound
    {f : Nat → Real}
    (hf : _root_.is_polynomial_bound f) :
    _root_.BoundedArithmeticLab.IsPolynomialBound f := by
  rcases hf with ⟨c, k, hc⟩
  exact ⟨c, k, hc⟩

/-- The two polynomial-bound interfaces have the same data shape. -/
theorem boundedArithmeticPolynomialBound_to_rootPolynomialBound_opened
    {f : Nat → Real}
    (hf : _root_.BoundedArithmeticLab.IsPolynomialBound f) :
    _root_.is_polynomial_bound f := by
  rcases hf with ⟨c, k, hc⟩
  exact ⟨c, k, hc⟩

/--
The real-valued BA semantic proof length agrees with the option-valued minimum
when the option minimum exists.  This is the bridge from existing project
calibrations stated with `semanticBAProofLength` to the newer proof-object
minimum route stated with `semanticBAMinProofSizeOption`.
-/
theorem semanticBAProofLength_eq_of_minProofSizeOption_some
    {Ax : _root_.BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → _root_.BoundedArithmeticLab.BAFormula}
    {n k : Nat}
    (hmin :
      _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption
          Ax target n =
        some k) :
    _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n =
      (k : Real) := by
  rcases
      _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption_some_to_hasProofOfSize
        hmin with
    ⟨p, hp, hsize_le_k⟩
  have hle :
      _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n ≤
        (k : Real) := by
    have hsem_le_size :
        _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n ≤
          (p.size : Real) :=
      _root_.BoundedArithmeticLab.semanticBAProofLength_le_size
        Ax target p hp
    have hsize_le_k_real : (p.size : Real) ≤ k := by
      exact_mod_cast hsize_le_k
    exact le_trans hsem_le_size hsize_le_k_real
  have hge :
      (k : Real) ≤
        _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n := by
    dsimp [_root_.BoundedArithmeticLab.semanticBAProofLength]
    refine le_csInf ?_ ?_
    · exact ⟨(p.size : Real), ⟨p, hp, rfl⟩⟩
    · intro r hr
      rcases hr with ⟨q, hq, rfl⟩
      exact_mod_cast
        _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption_min_le_of_proof
          hmin q hq
  exact le_antisymm hle hge

/--
Converts an existing real-valued semantic-length calibration into the
option-minimum calibration needed by the opened Buss-Pudlak proof-object route.
-/
theorem semanticBAProofLength_calibration_to_option_length_calibration
    {source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource}
    {Ax : _root_.BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → _root_.BoundedArithmeticLab.BAFormula}
    (hsemantic_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n) :
    ∀ n k : Nat,
      _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption
          Ax target n =
        some k →
      source.pa_length n = (k : Real) := by
  intro n k hmin
  rw [hsemantic_length n,
    semanticBAProofLength_eq_of_minProofSizeOption_some hmin]

/--
Explicit literature-axiom package for the realistic Buss-Pudlak input.

This avoids the impossible exact-code route.  The external theorem-5 source is
allowed to be semantically relabeled to the canonical finite-consistency
family, and its PA/symbol-size length is calibrated to
`semanticBAProofLength PAAxiom finiteConsistencyFormula`.

Formula family: canonical finite-consistency boxes, represented by
`finiteConsistencyFormula`.
Proof system: PA, represented on the BA side by `PAAxiom`.
Length measure: semantic minimum BA proof-object size,
`semanticBAProofLength PAAxiom finiteConsistencyFormula`.
-/
structure BussPudlakTheorem5CanonicalRelabeledPASemanticLiteratureInput :
    Type 1 where
  source :
    _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource
  calibration :
    _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
      source

/--
The named literature input.  This is the auditable point where the external
Buss/Pudlak/Friedman theorem-5 lower bound is assumed rather than proved inside
Lean.
-/
axiom
  bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput :
    BussPudlakTheorem5CanonicalRelabeledPASemanticLiteratureInput

/--
An abstract bounded-arithmetic lower-bound box directly rules out any eventual
polynomial-size family of concrete BA proof objects, once the box length is
calibrated to the option-valued semantic minimum proof size.

This is the opened content of the old `tail_gap` direction: it is not merely a
search threshold, but a proof-complexity statement saying that no single
polynomial can eventually bound actual proof objects for the target family.
-/
theorem boundedEventualLowerBound_to_no_eventual_polynomial_proof_family
    (box : _root_.BoundedArithmeticLab.AbstractProofLengthBox)
    (hlower : _root_.BoundedArithmeticLab.EventualLowerBound box)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hoption_length :
      ∀ n k : Nat,
        _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption
            Ax target n =
          some k →
        box.length n = (k : Real)) :
    ¬ BAEventuallyPolynomialProofObjectFamily Ax target := by
  intro hfamily
  rcases hfamily with ⟨U, hU, N, hproofs⟩
  rcases hlower.lower_bound U
      (rootPolynomialBound_to_boundedArithmeticPolynomialBound hU) N with
    ⟨n, hn_ge, hbox_gt⟩
  rcases hproofs n hn_ge with ⟨proof, hconclusion, hsize_le_U⟩
  rcases
      _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption_some_of_exists_proof
        ⟨proof, hconclusion⟩ with
    ⟨k, hmin⟩
  have hbox_eq : box.length n = (k : Real) :=
    hoption_length n k hmin
  have hk_le_size_nat : k ≤ proof.size :=
    _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption_min_le_of_proof
      hmin proof hconclusion
  have hk_le_size : (k : Real) ≤ proof.size := by
    exact_mod_cast hk_le_size_nat
  linarith

/--
Conversely, if every target has a proof object and no eventual polynomial-size
proof-object family exists, the option-calibrated box has an eventual lower
bound.  Together with
`boundedEventualLowerBound_to_no_eventual_polynomial_proof_family`, this makes
the old lower-bound box exactly the no-polynomial-proof-family statement.
-/
theorem no_eventual_polynomial_proof_family_to_boundedEventualLowerBound
    (box : _root_.BoundedArithmeticLab.AbstractProofLengthBox)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hoption_length :
      ∀ n k : Nat,
        _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption
            Ax target n =
          some k →
        box.length n = (k : Real))
    (hno : ¬ BAEventuallyPolynomialProofObjectFamily Ax target) :
    _root_.BoundedArithmeticLab.EventualLowerBound box where
  lower_bound := by
    intro f hf N
    rcases
        (no_eventual_polynomial_proof_family_to_BAOptionMinProofSizeBeatsPolynomial
            hcomplete hno)
          f
          (boundedArithmeticPolynomialBound_to_rootPolynomialBound_opened hf)
          N with
      ⟨n, hn_ge, k, hmin, hgt⟩
    refine ⟨n, hn_ge, ?_⟩
    have hbox_eq : box.length n = (k : Real) :=
      hoption_length n k hmin
    linarith

/--
Equivalence form of the opened lower-bound box.  Under concrete proof-object
completeness and option-minimum length calibration, an `EventualLowerBound`
field is neither more nor less than the assertion that there is no eventual
polynomial-size BA proof-object family.
-/
theorem boundedEventualLowerBound_iff_no_eventual_polynomial_proof_family
    (box : _root_.BoundedArithmeticLab.AbstractProofLengthBox)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hoption_length :
      ∀ n k : Nat,
        _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption
            Ax target n =
          some k →
        box.length n = (k : Real)) :
    _root_.BoundedArithmeticLab.EventualLowerBound box ↔
      ¬ BAEventuallyPolynomialProofObjectFamily Ax target :=
  ⟨fun hlower =>
      boundedEventualLowerBound_to_no_eventual_polynomial_proof_family
        box hlower Ax target hoption_length,
    fun hno =>
      no_eventual_polynomial_proof_family_to_boundedEventualLowerBound
        box Ax target hcomplete hoption_length hno⟩

/--
Fully positive form of the opened lower-bound box.  After option-minimum
calibration, `EventualLowerBound` is equivalent to the statement that every
polynomial bound is beaten by all proof objects at some arbitrarily late
target index.
-/
theorem boundedEventualLowerBound_iff_BAProofObjectStrongSizeLowerBound
    (box : _root_.BoundedArithmeticLab.AbstractProofLengthBox)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hoption_length :
      ∀ n k : Nat,
        _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption
            Ax target n =
          some k →
        box.length n = (k : Real)) :
    _root_.BoundedArithmeticLab.EventualLowerBound box ↔
      BAProofObjectStrongSizeLowerBound Ax target := by
  constructor
  · intro hlower
    exact
      no_eventual_polynomial_proof_family_to_BAProofObjectStrongSizeLowerBound
        (boundedEventualLowerBound_to_no_eventual_polynomial_proof_family
          box hlower Ax target hoption_length)
  · intro hstrong
    exact
      no_eventual_polynomial_proof_family_to_boundedEventualLowerBound
        box Ax target hcomplete hoption_length
        (BAProofObjectStrongSizeLowerBound_to_no_eventual_polynomial_proof_family
          hstrong)

/--
An abstract bounded-arithmetic lower-bound box closes the checked-minimum
theorem-5 target exactly when its length is calibrated to the checked
`minProofCodeSize` sequence.
-/
theorem boundedEventualLowerBound_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (box : _root_.BoundedArithmeticLab.AbstractProofLengthBox)
    (hlower : _root_.BoundedArithmeticLab.EventualLowerBound box)
    (hlength :
      ∀ n : Nat,
        box.length n =
          (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real)) :
    CheckedMinProofCodeStrongLowerBound scale_data sem := by
  intro f hf
  refine Filter.frequently_atTop.2 ?_
  intro N
  rcases hlower.lower_bound f
      (rootPolynomialBound_to_boundedArithmeticPolynomialBound hf) N with
    ⟨n, hn_ge, hgt⟩
  exact ⟨n, hn_ge, by simpa [hlength n] using hgt⟩

/--
Specialization to the bounded-arithmetic Buss-Pudlak source.  The remaining
calibration is precisely that its `pa_length` field is the checked minimum
proof-code size of the theorem-5 family.
-/
theorem bussPudlakLowerSource_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (hlength :
      ∀ n : Nat,
        source.pa_length n =
          (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real)) :
    CheckedMinProofCodeStrongLowerBound scale_data sem :=
  boundedEventualLowerBound_to_checkedMinProofCodeStrongLowerBound
    source.box source.lower_bound
    (by
      intro n
      simpa [_root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource.box,
        _root_.BoundedArithmeticLab.bussPudlakTheorem5PABox,
        _root_.BoundedArithmeticLab.paSymbolBox,
        _root_.BoundedArithmeticLab.proofLengthBox] using
        hlength n)

/--
Direct no-small-code endpoint for the non-toy lower-bound route.

This is the clean checked-minimum form: a Buss-Pudlak lower source closes the
theorem-5 lower side once its PA/symbol-size length sequence is calibrated
exactly to the `minProofCodeSize` of the concrete proof-code semantics used by
the checker.  No `semanticBAProofLength` and no canonical CnBox toy proof
object semantics are involved.
-/
theorem bussPudlakLowerSource_checkedMinProofCodeCalibration_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (hlength :
      ∀ n : Nat,
        source.pa_length n =
          (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real)) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data sem :=
  checkedMinProofCodeStrongLowerBound_to_noSmallProofCodes
    (bussPudlakLowerSource_to_checkedMinProofCodeStrongLowerBound
      source hlength)

/--
PA/Hilbert accepted-natural-code specialization of the checked-minimum route.

The remaining calibration is now the exact statement that the Buss-Pudlak
PA/symbol-size length of the theorem-5 formula family equals the minimum
accepted numeric PA/Hilbert proof code for the same `powerBoundRawCode n`.
-/
theorem bussPudlakLowerSource_checkedMinProofCodeCalibration_to_paHilbertAcceptedNatCode_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (hlength :
      ∀ n : Nat,
        source.pa_length n =
          (((PAHilbertAcceptedNatCodeCheckerSemantics
              scale_data checker completion).toProofCodeSemantics).minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real)) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  bussPudlakLowerSource_checkedMinProofCodeCalibration_to_noSmallProofCodes
    (scale_data := scale_data)
    (sem :=
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics)
    source hlength

/--
Root-proof-length calibration form of the checked-minimum route.

This is the exact seam between a literature/formalized Buss-Pudlak lower
source and the concrete PA/Hilbert accepted-natural-code checker.  The source
must first be shown to measure the same theorem-5 formula family as
`proof_length PA symbolSize (powerBoundRawCode n)`.  The checker exactness
then replaces that root proof length by the semantic minimum accepted numeric
proof-code size.  No `tail_gap` and no toy `semanticBAProofLength` route are
used here.
-/
theorem
    bussPudlakLowerSource_rootProofLengthCalibration_and_paHilbertExactness_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (hroot_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n))
    (exactness :
      PAHilbertAcceptedNatCodeProofLengthExactnessData
        scale_data checker completion) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  bussPudlakLowerSource_checkedMinProofCodeCalibration_to_paHilbertAcceptedNatCode_noSmallProofCodes
    (scale_data := scale_data)
    (checker := checker)
    (completion := completion)
    source
    (by
      intro n
      rw [hroot_length n]
      exact
        exactness.proof_length_eq_minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩)

/--
Specialization for a bounded lower source built from a root strong rescaled
Pudlak lower bound.  The only extra datum is the code identity saying that the
rescaled root theorem-5 family is exactly the internal `powerBoundRawCode`
family used by the PA/Hilbert checker.
-/
theorem
    boundedLowerSourceOfRootStrongRescaled_codeEq_and_paHilbertExactness_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (raw : Nat → _root_.FormulaCode) (scale : Nat → Nat)
    (hlower :
      _root_.StrongRescaledExternalStrengthenedLowerBound raw scale)
    (hcode :
      ∀ n : Nat,
        _root_.rescaledExternalStrengthenedLowerBoundCode raw scale n =
          scale_data.powerBoundRawCode n)
    (exactness :
      PAHilbertAcceptedNatCodeProofLengthExactnessData
        scale_data checker completion) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  bussPudlakLowerSource_rootProofLengthCalibration_and_paHilbertExactness_to_noSmallProofCodes
    (scale_data := scale_data)
    (checker := checker)
    (completion := completion)
    (source := boundedLowerSourceOfRootStrongRescaled raw scale hlower)
    (by
      intro n
      change
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (_root_.rescaledExternalStrengthenedLowerBoundCode raw scale n) =
          _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n)
      rw [hcode n])
    exactness

/--
Specialization of the opened lower-bound content to the Buss-Pudlak source.
The only calibration needed here is the exact equality between the source's
PA/symbol-size length sequence and the option-valued BA minimum proof size.
-/
theorem bussPudlakLowerSource_to_no_eventual_polynomial_proof_family
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hoption_length :
      ∀ n k : Nat,
        _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption
            Ax target n =
          some k →
        source.pa_length n = (k : Real)) :
    ¬ BAEventuallyPolynomialProofObjectFamily Ax target :=
  boundedEventualLowerBound_to_no_eventual_polynomial_proof_family
    source.box source.lower_bound Ax target
    (by
      intro n k hmin
      simpa [_root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource.box,
        _root_.BoundedArithmeticLab.bussPudlakTheorem5PABox,
        _root_.BoundedArithmeticLab.paSymbolBox,
        _root_.BoundedArithmeticLab.proofLengthBox] using
        hoption_length n k hmin)

theorem bussPudlakLowerSource_to_BAProofObjectStrongSizeLowerBound
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hoption_length :
      ∀ n k : Nat,
        _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption
            Ax target n =
          some k →
        source.pa_length n = (k : Real)) :
    BAProofObjectStrongSizeLowerBound Ax target :=
  no_eventual_polynomial_proof_family_to_BAProofObjectStrongSizeLowerBound
    (bussPudlakLowerSource_to_no_eventual_polynomial_proof_family
      source Ax target hoption_length)

/--
Opened equivalence for a Buss-Pudlak source after option-minimum calibration.
This states precisely what its `lower_bound` field must mean at the BA
proof-object level.
-/
theorem bussPudlakEventualLowerBound_iff_no_eventual_polynomial_proof_family
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hoption_length :
      ∀ n k : Nat,
        _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption
            Ax target n =
          some k →
        source.pa_length n = (k : Real)) :
    _root_.BoundedArithmeticLab.EventualLowerBound source.box ↔
      ¬ BAEventuallyPolynomialProofObjectFamily Ax target :=
  boundedEventualLowerBound_iff_no_eventual_polynomial_proof_family
    source.box Ax target hcomplete
    (by
      intro n k hmin
      simpa [_root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource.box,
        _root_.BoundedArithmeticLab.bussPudlakTheorem5PABox,
        _root_.BoundedArithmeticLab.paSymbolBox,
        _root_.BoundedArithmeticLab.proofLengthBox] using
        hoption_length n k hmin)

/--
Positive opened equivalence for a Buss-Pudlak source.  This is the cleanest
audit statement for the lower-bound input: after option-minimum calibration,
the source lower-bound field is exactly the strong proof-object size lower
bound.
-/
theorem bussPudlakEventualLowerBound_iff_BAProofObjectStrongSizeLowerBound
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hoption_length :
      ∀ n k : Nat,
        _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption
            Ax target n =
          some k →
        source.pa_length n = (k : Real)) :
    _root_.BoundedArithmeticLab.EventualLowerBound source.box ↔
      BAProofObjectStrongSizeLowerBound Ax target :=
  boundedEventualLowerBound_iff_BAProofObjectStrongSizeLowerBound
    source.box Ax target hcomplete
    (by
      intro n k hmin
      simpa [_root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource.box,
        _root_.BoundedArithmeticLab.bussPudlakTheorem5PABox,
        _root_.BoundedArithmeticLab.paSymbolBox,
        _root_.BoundedArithmeticLab.proofLengthBox] using
        hoption_length n k hmin)

/-- The checked minimum size is independent of the proof of relevance supplied. -/
theorem proofCodeSemantics_minProofCodeSize_proof_irrel
    {relevant : _root_.FormulaCode → Prop}
    (sem : _root_.ProofCodeSemantics.{0} relevant)
    {code : _root_.FormulaCode}
    (h₁ h₂ : relevant code) :
    sem.minProofCodeSize code h₁ = sem.minProofCodeSize code h₂ := by
  have h : h₁ = h₂ := Subsingleton.elim h₁ h₂
  cases h
  rfl

/--
Proof-object semantics for a bounded-arithmetic target family, transported into
the root formula-code universe.  A code is accepted exactly when the
`BAProofObject` proves the target formula attached to that root code.

The completeness argument is explicit: this construction exists only when every
target formula has a concrete `BAProofObject`.
-/
noncomputable def baProofObjectRootCodeSemantics
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (rootCode : Nat → _root_.FormulaCode)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n) :
    _root_.ProofCodeSemantics.{0}
      (fun code : _root_.FormulaCode => ∃ n : Nat, code = rootCode n) where
  Code := _root_.BoundedArithmeticLab.BAProofObject Ax
  checks := fun proof code =>
    ∃ n : Nat, code = rootCode n ∧ proof.conclusion = target n
  size := fun proof => proof.size
  complete := by
    intro code hcode
    rcases hcode with ⟨n, rfl⟩
    rcases hcomplete n with ⟨proof, hproof⟩
    exact ⟨proof, n, rfl, hproof⟩

/--
For the proof-object semantics above, the checked minimum proof-code size is
exactly the semantic bounded-arithmetic proof length.

This is the calibration bridge that removes the vague
`pa_length = minProofCodeSize` obligation when the underlying proof objects are
real and the root code map is injective.
-/
theorem baProofObjectRootCodeSemantics_minProofCodeSize_eq_semanticBAProofLength
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (rootCode : Nat → _root_.FormulaCode)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective rootCode)
    (n : Nat) :
    ((baProofObjectRootCodeSemantics Ax target rootCode hcomplete).minProofCodeSize
        (rootCode n) ⟨n, rfl⟩ : Real) =
      _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n := by
  let sem := baProofObjectRootCodeSemantics Ax target rootCode hcomplete
  apply le_antisymm
  · dsimp [_root_.BoundedArithmeticLab.semanticBAProofLength]
    refine le_csInf ?_ ?_
    · rcases hcomplete n with ⟨proof, hproof⟩
      exact ⟨(proof.size : Real), proof, hproof, rfl⟩
    · intro r hr
      rcases hr with ⟨proof, hconclusion, rfl⟩
      have hhas :
          sem.HasProofCodeOfSize (rootCode n) proof.size := by
        exact ⟨proof, ⟨n, rfl, hconclusion⟩, le_rfl⟩
      have hmin_le :
          sem.minProofCodeSize (rootCode n) ⟨n, rfl⟩ ≤ proof.size :=
        sem.minProofCodeSize_le_of_hasProofCodeOfSize ⟨n, rfl⟩ hhas
      exact_mod_cast hmin_le
  · rcases sem.hasProofCodeOfSize_minProofCodeSize
        (code := rootCode n) ⟨n, rfl⟩ with
      ⟨proof, hchecks, hsize⟩
    rcases hchecks with ⟨m, hcode, hconclusion⟩
    have hmn : m = n := hroot_injective hcode.symm
    subst m
    have hsemantic_le :
        _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n ≤
          (proof.size : Real) :=
      _root_.BoundedArithmeticLab.semanticBAProofLength_le_size
        Ax target proof hconclusion
    have hproof_le :
        (proof.size : Real) ≤
          (sem.minProofCodeSize (rootCode n) ⟨n, rfl⟩ : Real) := by
      exact_mod_cast hsize
    exact le_trans hsemantic_le hproof_le

/--
Option-valued exactness for the BA proof-object root semantics.  If the
bounded-arithmetic semantic minimum is `some k`, then the root
`ProofCodeSemantics.minProofCodeSize` for the corresponding formula code is
definitionally the same natural number `k`.

This avoids the real-valued empty-infimum convention entirely: the theorem can
only be applied after an actual `some k` minimum proof object has been
exhibited.
-/
theorem baProofObjectRootCodeSemantics_minProofCodeSize_eq_option
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (rootCode : Nat → _root_.FormulaCode)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective rootCode)
    {n k : Nat}
    (hmin :
      _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption
          Ax target n =
        some k) :
    (baProofObjectRootCodeSemantics Ax target rootCode hcomplete).minProofCodeSize
        (rootCode n) ⟨n, rfl⟩ =
      k := by
  let sem := baProofObjectRootCodeSemantics Ax target rootCode hcomplete
  apply le_antisymm
  · rcases
      _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption_some_to_hasProofOfSize
        hmin with
      ⟨proof, hconclusion, hsize_le⟩
    have hhas : sem.HasProofCodeOfSize (rootCode n) k := by
      exact ⟨proof, ⟨n, rfl, hconclusion⟩, hsize_le⟩
    exact sem.minProofCodeSize_le_of_hasProofCodeOfSize ⟨n, rfl⟩ hhas
  · rcases sem.hasProofCodeOfSize_minProofCodeSize
        (code := rootCode n) ⟨n, rfl⟩ with
      ⟨proof, hchecks, hsize_le⟩
    rcases hchecks with ⟨m, hcode, hconclusion⟩
    have hmn : m = n := hroot_injective hcode.symm
    subst m
    have hk_le_size :
        k ≤ proof.size :=
      _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption_min_le_of_proof
        hmin proof hconclusion
    exact le_trans hk_le_size hsize_le

/--
The option-valued BA lower-bound target closes the root-free checked-minimum
Pudlak target for the corresponding BA proof-object semantics.  This is the
positive counterpart to the no-go probes: once the actual option-valued
minimum proof-object sizes are proved to beat every polynomial, the checked
`minProofCodeSize` theorem follows with no `tail_gap` and no root
`proof_length`.
-/
theorem BAOptionMinProofSizeBeatsPolynomial_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hlower : BAOptionMinProofSizeBeatsPolynomial Ax target) :
    CheckedMinProofCodeStrongLowerBound scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hcomplete) := by
  intro U hU
  refine Filter.frequently_atTop.2 ?_
  intro N
  rcases hlower U hU N with ⟨n, hn_ge, k, hmin, hgt⟩
  have hmin_eq :
      (baProofObjectRootCodeSemantics
          Ax target scale_data.powerBoundRawCode hcomplete).minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ =
        k :=
    baProofObjectRootCodeSemantics_minProofCodeSize_eq_option
      Ax target scale_data.powerBoundRawCode hcomplete hroot_injective hmin
  have hgt_checked :
      U n <
        (((baProofObjectRootCodeSemantics
            Ax target scale_data.powerBoundRawCode hcomplete).minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Nat) : Real) := by
    rw [hmin_eq]
    exact hgt
  exact ⟨n, hn_ge, hgt_checked⟩

/--
The same option-valued BA lower-bound target gives the fully opened
no-accepted-below certificate for the BA proof-object root semantics.
-/
noncomputable def
    BAOptionMinProofSizeBeatsPolynomial_toNoAcceptedBelowCutoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hlower : BAOptionMinProofSizeBeatsPolynomial Ax target) :
    ComputableNoAcceptedBelowCutoff scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hcomplete) :=
  checkedMinProofCodeStrongLowerBound_toNoAcceptedBelowCutoff
    (BAOptionMinProofSizeBeatsPolynomial_to_checkedMinProofCodeStrongLowerBound
      Ax target hcomplete hroot_injective hlower)

/--
The positive proof-object lower-bound form is enough to close the checked
minimum proof-code lower bound.  This is the current clean target for the
Pudlak-side proof: prove every proposed polynomial bound is beaten by all
actual proof objects at some arbitrarily late index.
-/
theorem BAProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hlower : BAProofObjectStrongSizeLowerBound Ax target) :
    CheckedMinProofCodeStrongLowerBound scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hcomplete) :=
  BAOptionMinProofSizeBeatsPolynomial_to_checkedMinProofCodeStrongLowerBound
    Ax target hcomplete hroot_injective
    (BAProofObjectStrongSizeLowerBound_to_BAOptionMinProofSizeBeatsPolynomial
      hcomplete hlower)

/--
The positive proof-object lower-bound form also closes the theorem-5
no-small-proof-code statement itself.  This is the paper-proof root form:
after completeness and injectivity identify the BA proof-object semantics with
the theorem-5 code family, every accepted proof object at a late witness has
size above the proposed polynomial bound.
-/
theorem BAProofObjectStrongSizeLowerBound_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hlower : BAProofObjectStrongSizeLowerBound Ax target) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hcomplete) :=
  checkedMinProofCodeStrongLowerBound_to_noSmallProofCodes
    (BAProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound
      Ax target hcomplete hroot_injective hlower)

/-- Positive proof-object lower-bound form for the no-accepted-below target. -/
noncomputable def
    BAProofObjectStrongSizeLowerBound_toNoAcceptedBelowCutoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hlower : BAProofObjectStrongSizeLowerBound Ax target) :
    ComputableNoAcceptedBelowCutoff scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hcomplete) :=
  checkedMinProofCodeStrongLowerBound_toNoAcceptedBelowCutoff
    (BAProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound
      Ax target hcomplete hroot_injective hlower)

/--
The non-vacuous proof-object lower-bound target closes the checked minimum
proof-code lower bound with its completeness field used as the proof-object
semantics completion witness.
-/
theorem BACompleteProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hlower : BACompleteProofObjectStrongSizeLowerBound Ax target) :
    CheckedMinProofCodeStrongLowerBound scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hlower.complete) :=
  BAProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound
    Ax target hlower.complete hroot_injective hlower.strong_lower

/-- Non-vacuous proof-object lower-bound target for theorem-5 no-small codes. -/
theorem BACompleteProofObjectStrongSizeLowerBound_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hlower : BACompleteProofObjectStrongSizeLowerBound Ax target) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hlower.complete) :=
  BAProofObjectStrongSizeLowerBound_to_noSmallProofCodes
    Ax target hlower.complete hroot_injective hlower.strong_lower

/-- Non-vacuous proof-object lower-bound target for no-accepted-below. -/
noncomputable def
    BACompleteProofObjectStrongSizeLowerBound_toNoAcceptedBelowCutoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hlower : BACompleteProofObjectStrongSizeLowerBound Ax target) :
    ComputableNoAcceptedBelowCutoff scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hlower.complete) :=
  checkedMinProofCodeStrongLowerBound_toNoAcceptedBelowCutoff
    (BACompleteProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound
      Ax target hroot_injective hlower)

/--
Shortest root-free positive lower-bound entry point.  Once every target has a
BA proof object and no eventual polynomial-size proof-object family exists, the
checked minimum proof-code lower bound follows.
-/
theorem no_eventual_polynomial_proof_family_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hno : ¬ BAEventuallyPolynomialProofObjectFamily Ax target) :
    CheckedMinProofCodeStrongLowerBound scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hcomplete) :=
  BAOptionMinProofSizeBeatsPolynomial_to_checkedMinProofCodeStrongLowerBound
    Ax target hcomplete hroot_injective
    (no_eventual_polynomial_proof_family_to_BAOptionMinProofSizeBeatsPolynomial
      hcomplete hno)

/--
Shortest root-free no-small-code entry point: no eventual polynomial-size BA
proof-object family is exactly enough to derive theorem-5 no-small proof codes
for the corresponding proof-object semantics.
-/
theorem no_eventual_polynomial_proof_family_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hno : ¬ BAEventuallyPolynomialProofObjectFamily Ax target) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hcomplete) :=
  checkedMinProofCodeStrongLowerBound_to_noSmallProofCodes
    (no_eventual_polynomial_proof_family_to_checkedMinProofCodeStrongLowerBound
      Ax target hcomplete hroot_injective hno)

/--
The same shortest entry point for the fully opened no-accepted-below target.
-/
noncomputable def
    no_eventual_polynomial_proof_family_toNoAcceptedBelowCutoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hno : ¬ BAEventuallyPolynomialProofObjectFamily Ax target) :
    ComputableNoAcceptedBelowCutoff scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hcomplete) :=
  BAOptionMinProofSizeBeatsPolynomial_toNoAcceptedBelowCutoff
    Ax target hcomplete hroot_injective
    (no_eventual_polynomial_proof_family_to_BAOptionMinProofSizeBeatsPolynomial
      hcomplete hno)

/--
Closed semantic route from a Buss-Pudlak lower source to the checked minimum
proof-code lower bound, with the proof-length calibration opened into concrete
`BAProofObject` semantics.

What remains as input is no longer a tail-gap object: it is the actual
Buss-Pudlak lower-bound source, a concrete proof object for each target formula,
the length identity from the source to `semanticBAProofLength`, and injectivity
of the theorem-5 root code map.
-/
theorem bussPudlakLowerSource_baProofObjectSemantics_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hsemantic_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n) :
    CheckedMinProofCodeStrongLowerBound scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hcomplete) :=
  bussPudlakLowerSource_to_checkedMinProofCodeStrongLowerBound
    source
    (by
      intro n
      let sem :=
        baProofObjectRootCodeSemantics
          Ax target scale_data.powerBoundRawCode hcomplete
      rw [hsemantic_length n]
      rw [← baProofObjectRootCodeSemantics_minProofCodeSize_eq_semanticBAProofLength
        Ax target scale_data.powerBoundRawCode hcomplete hroot_injective n]
      exact_mod_cast
        proofCodeSemantics_minProofCodeSize_proof_irrel
          sem ⟨n, rfl⟩ _)

/--
The Buss-Pudlak source route, after semantic length calibration to concrete BA
proof objects, gives theorem-5 no-small proof codes.  This is the exact root
statement used by the short paper proof; the source's `lower_bound` field is
the remaining literature/formalization content.
-/
theorem bussPudlakLowerSource_baProofObjectSemantics_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hsemantic_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hcomplete) :=
  checkedMinProofCodeStrongLowerBound_to_noSmallProofCodes
    (bussPudlakLowerSource_baProofObjectSemantics_to_checkedMinProofCodeStrongLowerBound
      source Ax target hcomplete hroot_injective hsemantic_length)

/--
Canonical proof-object shortest-growth endpoint.  This is the direct
proof-length-free lower-bound route after the old `tail_gap` and root
`proof_length` layers have been opened:

* the Buss-Pudlak source supplies the lower bound,
* the relabeled canonical calibration identifies its length sequence with
  `semanticBAProofLength PAAxiom finiteConsistencyFormula`,
* completeness supplies actual PA proof objects for each finite-consistency
  target, and
* injectivity identifies the theorem-5 root code index.

No project-level `proof_length` occurs in the statement.
-/
theorem canonicalRelabeledBussPudlak_baProofObjectSemantics_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject
            _root_.BoundedArithmeticLab.PAAxiom,
          proof.conclusion =
            _root_.BoundedArithmeticLab.finiteConsistencyFormula n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (baProofObjectRootCodeSemantics
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        scale_data.powerBoundRawCode hcomplete) :=
  bussPudlakLowerSource_baProofObjectSemantics_to_checkedMinProofCodeStrongLowerBound
    source
    _root_.BoundedArithmeticLab.PAAxiom
    _root_.BoundedArithmeticLab.finiteConsistencyFormula
    hcomplete hroot_injective calibration.length_eq

/--
Literature-input specialization of the canonical proof-object shortest-growth
endpoint.  The only non-kernel source here is the explicitly named
`bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput`; the remaining
arguments are the real PA proof-object completeness and root-code injectivity
obligations.
-/
theorem canonicalLiteratureInput_baProofObjectSemantics_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject
            _root_.BoundedArithmeticLab.PAAxiom,
          proof.conclusion =
            _root_.BoundedArithmeticLab.finiteConsistencyFormula n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (baProofObjectRootCodeSemantics
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        scale_data.powerBoundRawCode hcomplete) := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalRelabeledBussPudlak_baProofObjectSemantics_to_shortestCheckedMinProofCodeGrowthObligation
      input.source input.calibration hcomplete hroot_injective

/--
Scale-injective version of the canonical proof-object endpoint.  The root-code
injectivity premise is discharged from the concrete PA/Hilbert code definition:
`powerBoundRawCode n` is a strengthened partial-consistency code at
`scale_data.scale n`.
-/
theorem canonicalRelabeledBussPudlak_baProofObjectSemantics_of_scaleInjective_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject
            _root_.BoundedArithmeticLab.PAAxiom,
          proof.conclusion =
            _root_.BoundedArithmeticLab.finiteConsistencyFormula n)
    (hscale_injective : Function.Injective scale_data.scale) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (baProofObjectRootCodeSemantics
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        scale_data.powerBoundRawCode hcomplete) :=
  canonicalRelabeledBussPudlak_baProofObjectSemantics_to_shortestCheckedMinProofCodeGrowthObligation
    source calibration hcomplete
    (concretePAHilbert_powerBoundRawCode_injective_of_scale_injective
      scale_data hscale_injective)

/--
Literature-input plus scale-injectivity version.  After this point the remaining
non-literature mathematical construction is the real PA proof-object completeness
for finite-consistency formulas.
-/
theorem canonicalLiteratureInput_baProofObjectSemantics_of_scaleInjective_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject
            _root_.BoundedArithmeticLab.PAAxiom,
          proof.conclusion =
            _root_.BoundedArithmeticLab.finiteConsistencyFormula n)
    (hscale_injective : Function.Injective scale_data.scale) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (baProofObjectRootCodeSemantics
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        scale_data.powerBoundRawCode hcomplete) := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalRelabeledBussPudlak_baProofObjectSemantics_of_scaleInjective_to_shortestCheckedMinProofCodeGrowthObligation
      input.source input.calibration hcomplete hscale_injective

/-- A strictly increasing scale is injective. -/
theorem internalPudlakScale_injective_of_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hscale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b) :
    Function.Injective scale_data.scale := by
  intro a b hscale_eq
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have hstrict := hscale_strict hlt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)
  · exact heq
  · have hstrict := hscale_strict hgt
    rw [hscale_eq] at hstrict
    exact False.elim ((Nat.lt_irrefl _) hstrict)

/--
Strict-scale version of the canonical proof-object endpoint.  This is often the
most natural way to close the injectivity side of the theorem-5 code family.
-/
theorem canonicalRelabeledBussPudlak_baProofObjectSemantics_of_scaleStrict_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject
            _root_.BoundedArithmeticLab.PAAxiom,
          proof.conclusion =
            _root_.BoundedArithmeticLab.finiteConsistencyFormula n)
    (hscale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (baProofObjectRootCodeSemantics
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        scale_data.powerBoundRawCode hcomplete) :=
  canonicalRelabeledBussPudlak_baProofObjectSemantics_of_scaleInjective_to_shortestCheckedMinProofCodeGrowthObligation
    source calibration hcomplete
    (internalPudlakScale_injective_of_strict hscale_strict)

/-- Literature-input strict-scale version. -/
theorem canonicalLiteratureInput_baProofObjectSemantics_of_scaleStrict_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject
            _root_.BoundedArithmeticLab.PAAxiom,
          proof.conclusion =
            _root_.BoundedArithmeticLab.finiteConsistencyFormula n)
    (hscale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (baProofObjectRootCodeSemantics
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        scale_data.powerBoundRawCode hcomplete) := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalRelabeledBussPudlak_baProofObjectSemantics_of_scaleStrict_to_shortestCheckedMinProofCodeGrowthObligation
      input.source input.calibration hcomplete hscale_strict

/--
Root-literature specialization of the canonical proof-object endpoint.  This
uses the bounded lower source already constructed from the root external
Buss-Pudlak theorem-5 axiom, so the remaining inputs are exactly the real
canonical relabeling calibration, real PA proof-object completeness for
finite-consistency targets, and strictness of the theorem-5 scale.

This is an audit specialization, not the final proof-length-free endpoint: its
axiom profile still exposes the root literature `proof_length` boundary because
the external theorem-5 lower bound is currently stated in that measure.
-/
theorem rootLiteratureCanonicalCalibration_baProofObjectSemantics_of_scaleStrict_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    (calibration_target : RootLiteratureCanonicalCnBoxCalibrationTarget)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject
            _root_.BoundedArithmeticLab.PAAxiom,
          proof.conclusion =
            _root_.BoundedArithmeticLab.finiteConsistencyFormula n)
    (hscale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (baProofObjectRootCodeSemantics
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        scale_data.powerBoundRawCode hcomplete) := by
  rcases calibration_target with ⟨calibration⟩
  exact
    canonicalRelabeledBussPudlak_baProofObjectSemantics_of_scaleStrict_to_shortestCheckedMinProofCodeGrowthObligation
      boundedLowerSourceFromRootLiterature calibration hcomplete hscale_strict

/--
No-go for treating the proof-object endpoint above as already closed in the
current toy `PAAxiom` semantics.  Any such package contains, before the lower
bound is even used, a proof object for every `finiteConsistencyFormula n`; the
current toy BA calculus has none.
-/
theorem no_currentToyCanonicalLiteratureProofObjectGrowthPackage
    {scale_data : InternalPudlakTheorem5ScaleData} :
    (∃ hcomplete :
        ∀ n : Nat,
          ∃ proof :
            _root_.BoundedArithmeticLab.BAProofObject
              _root_.BoundedArithmeticLab.PAAxiom,
            proof.conclusion =
              _root_.BoundedArithmeticLab.finiteConsistencyFormula n,
      ShortestCheckedMinProofCodeGrowthObligation scale_data
        (baProofObjectRootCodeSemantics
          _root_.BoundedArithmeticLab.PAAxiom
          _root_.BoundedArithmeticLab.finiteConsistencyFormula
          scale_data.powerBoundRawCode hcomplete)) →
      False := by
  intro hpackage
  rcases hpackage with ⟨hcomplete, _hgrowth⟩
  exact no_currentToyPAProofObject_finiteConsistencyFormula 0 (hcomplete 0)

/--
The same BA proof-object route closes the fully opened no-accepted-below target.
This is the strongest proof-length-free conclusion available from the
structured proof-object semantics: it produces explicit witnesses and cutoffs
whose correctness follows from the Buss-Pudlak lower source and the semantic
length calibration.

It still does not construct PA/Hilbert numeric proof-code rejection; for that,
one must add an exact encoder/checker for these proof objects or work directly
with a PA/Hilbert accepted-code checker.
-/
noncomputable def bussPudlakLowerSource_baProofObjectSemantics_toNoAcceptedBelowCutoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hsemantic_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n) :
    ComputableNoAcceptedBelowCutoff scale_data
      (baProofObjectRootCodeSemantics
        Ax target scale_data.powerBoundRawCode hcomplete) :=
  checkedMinProofCodeStrongLowerBound_toNoAcceptedBelowCutoff
    (bussPudlakLowerSource_baProofObjectSemantics_to_checkedMinProofCodeStrongLowerBound
      source Ax target hcomplete hroot_injective hsemantic_length)

/--
Consequently, the BA proof-object route gives the checked measured search gap
without `tail_gap` and without the root `proof_length` fallback.
-/
noncomputable def bussPudlakLowerSource_baProofObjectSemantics_to_checkedMeasuredSearchGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hsemantic_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n) :
    ComputableSearchGapCertificate
      (month9_month10_checkedProofCodeMeasured scale_data
        (baProofObjectRootCodeSemantics
          Ax target scale_data.powerBoundRawCode hcomplete)) :=
  (bussPudlakLowerSource_baProofObjectSemantics_toNoAcceptedBelowCutoff
      source Ax target hcomplete hroot_injective hsemantic_length)
    |>.toCheckedMeasuredSearchGap

/--
Exact bridge from a PA/Hilbert accepted numeric-code checker to structured
bounded-arithmetic proof objects.  This is the missing encoder/checker
obligation after the BA proof-object lower route has been opened:

every accepted natural proof code for `powerBoundRawCode n` must decode or
extract a `BAProofObject` of the target formula, with object size bounded by
the numeric proof code.
-/
structure BAProofObjectAcceptedNatCodeBridge
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula) :
    Type 1 where
  accepted_to_baProofObject :
    ∀ n : Nat, ∀ code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code →
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n ∧ proof.size ≤ code

/--
Linear-overhead version of the accepted-code extractor.  This is the realistic
form for checked traces and machine runs: the extracted bounded-arithmetic
proof object may be linearly larger than the numeric PA/Hilbert proof code.
Linear overhead is still harmless for the Pudlak lower-bound argument because
linear rescaling preserves polynomial bounds.
-/
structure BAProofObjectAcceptedNatCodeLinearBridge
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula) :
    Type 1 where
  C : Real
  D : Real
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  accepted_to_baProofObject_linear :
    ∀ n : Nat, ∀ code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code →
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n ∧
            (proof.size : Real) ≤ C * (code : Real) + D

namespace BAProofObjectAcceptedNatCodeBridge

/-- A no-overhead extractor is a linear-overhead extractor with constants
`C = 1`, `D = 0`. -/
def toLinear
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {Ax : _root_.BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → _root_.BoundedArithmeticLab.BAFormula}
    (bridge :
      BAProofObjectAcceptedNatCodeBridge
        scale_data checker Ax target) :
    BAProofObjectAcceptedNatCodeLinearBridge
      scale_data checker Ax target where
  C := 1
  D := 0
  C_nonneg := by norm_num
  D_nonneg := by norm_num
  accepted_to_baProofObject_linear := by
    intro n code haccepted
    rcases bridge.accepted_to_baProofObject n code haccepted with
      ⟨proof, hconclusion, hsize⟩
    refine ⟨proof, hconclusion, ?_⟩
    have hsize_real : (proof.size : Real) ≤ (code : Real) := by
      exact_mod_cast hsize
    simpa using hsize_real

end BAProofObjectAcceptedNatCodeBridge

/--
Direct code-plus-two compiler from accepted PA/Hilbert natural proof codes to
PA-side BA proof objects.  This is weaker and more faithful than the
Buss-S²₁ extractor: an accepted PA/Hilbert proof code only has to decode to a
PA proof object of the target formula, with the same `code + 2` affine budget.
-/
structure PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula) :
    Type 1 where
  accepted_to_paProofObject_codePlusTwo :
    ∀ n : Nat, ∀ code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code →
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject
            _root_.BoundedArithmeticLab.PAAxiom,
          proof.conclusion = target n ∧
            (proof.size : Real) ≤ (code : Real) + 2

/--
The direct PA proof-object code-plus-two compiler is exactly the generic
linear accepted-code bridge specialized to `PAAxiom`, with constants `1, 2`.
-/
def
    PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {target : Nat → _root_.BoundedArithmeticLab.BAFormula}
    (compiler :
      PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler
        scale_data checker target) :
    BAProofObjectAcceptedNatCodeLinearBridge
      scale_data checker _root_.BoundedArithmeticLab.PAAxiom target where
  C := 1
  D := 2
  C_nonneg := by norm_num
  D_nonneg := by norm_num
  accepted_to_baProofObject_linear := by
    intro n code haccepted
    rcases compiler.accepted_to_paProofObject_codePlusTwo
        n code haccepted with
      ⟨proof, hconclusion, hsize⟩
    refine ⟨proof, hconclusion, ?_⟩
    calc
      (proof.size : Real) ≤ (code : Real) + 2 := hsize
      _ = (1 : Real) * (code : Real) + 2 := by ring

/--
Current-toy obstruction for the direct PA proof-object code-plus-two compiler.
This confirms that the remaining work is a real PA proof-object semantics,
not a Buss-S²₁ detour and not another size adapter.
-/
theorem no_acceptedNatCodePAProofObjectCodePlusTwoCompiler_currentToy_of_acceptedCode
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (compiler :
      PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    {n code : Nat}
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) code) :
    False := by
  rcases
      compiler.accepted_to_paProofObject_codePlusTwo n code haccepted with
    ⟨proof, hconclusion, _hsize⟩
  exact
    no_currentToyPAProofObject_finiteConsistencyFormula n
      ⟨proof, hconclusion⟩

/--
Trace-level form of the remaining extractor obligation.  The checker interface
already turns every accepted PA/Hilbert proof object into a checked trace; this
compiler is the remaining concrete step that turns such a checked trace into a
bounded-arithmetic proof object of the target formula, with no larger code
budget than the PA/Hilbert proof object.
-/
structure PAHilbertCheckedTraceToBAProofObjectCompiler
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (interface : PAHilbertCheckerInterface checker semantics)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula) :
    Type 1 where
  trace_to_baProofObject :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        interface.traceOf proof = some trace →
          trace.proof = proof →
            interface.traceChecker.checkTrace trace = true →
              proof.conclusion.code = scale_data.powerBoundRawCode n →
                ∃ baProof :
                  _root_.BoundedArithmeticLab.BAProofObject Ax,
                  baProof.conclusion = target n ∧
                    baProof.size ≤ proof.code

/--
Linear-overhead trace compiler to BA proof objects.  This is the same extractor
obligation as `PAHilbertCheckedTraceToBAProofObjectCompiler`, but with an
audited linear size overhead.
-/
structure PAHilbertCheckedTraceToBAProofObjectLinearCompiler
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (interface : PAHilbertCheckerInterface checker semantics)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula) :
    Type 1 where
  C : Real
  D : Real
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  trace_to_baProofObject_linear :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        interface.traceOf proof = some trace →
          trace.proof = proof →
            interface.traceChecker.checkTrace trace = true →
              proof.conclusion.code = scale_data.powerBoundRawCode n →
                ∃ baProof :
                  _root_.BoundedArithmeticLab.BAProofObject Ax,
                  baProof.conclusion = target n ∧
                    (baProof.size : Real) ≤ C * (proof.code : Real) + D

/--
S²₁-level trace compiler.  This is the sharper form of the extractor
obligation for the canonical Buss-Pudlak route: a checked PA/Hilbert trace is
first turned into a Buss-S²₁ bounded-arithmetic proof object.  The existing
`BussS21Axiom ⊆ PAAxiom` map then moves it to PA without increasing size.
-/
structure PAHilbertCheckedTraceToBussS21ProofObjectCompiler
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (interface : PAHilbertCheckerInterface checker semantics)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula) :
    Type 1 where
  trace_to_bussS21ProofObject :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        interface.traceOf proof = some trace →
          trace.proof = proof →
            interface.traceChecker.checkTrace trace = true →
              proof.conclusion.code = scale_data.powerBoundRawCode n →
                ∃ s21Proof :
                  _root_.BoundedArithmeticLab.BAProofObject
                  _root_.BoundedArithmeticLab.BussS21Axiom,
                  s21Proof.conclusion = target n ∧
                    s21Proof.size ≤ proof.code

/--
Linear-overhead S²₁ trace compiler.  This is the operationally robust version:
checked PA/Hilbert traces may compile to Buss-S²₁ proof objects with linear
overhead in the original numeric proof code.
-/
structure PAHilbertCheckedTraceToBussS21ProofObjectLinearCompiler
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (interface : PAHilbertCheckerInterface checker semantics)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula) :
    Type 1 where
  C : Real
  D : Real
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  trace_to_bussS21ProofObject_linear :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        interface.traceOf proof = some trace →
          trace.proof = proof →
            interface.traceChecker.checkTrace trace = true →
              proof.conclusion.code = scale_data.powerBoundRawCode n →
                ∃ s21Proof :
                  _root_.BoundedArithmeticLab.BAProofObject
                    _root_.BoundedArithmeticLab.BussS21Axiom,
                  s21Proof.conclusion = target n ∧
                    (s21Proof.size : Real) ≤ C * (proof.code : Real) + D

/--
Concrete verifier-trace interpretation of PA/Hilbert checked traces.  This is
one level more operational than `PAHilbertCheckedTraceToBussS21ProofObjectCompiler`:
the PA checked trace is first interpreted as a trace of an existing
`ConcreteVerifierTraceSystem`, whose `compileTrace` field already produces the
Buss-S²₁ proof object.

The size condition is deliberately numeric and local: the interpreted verifier
trace must have size at most the original PA/Hilbert proof code.  Together with
`compile_size_le_trace_size`, this gives the size bound needed by the
Pudlak-side extractor.
-/
structure PAHilbertCheckedTraceConcreteVerifierRealization
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (interface : PAHilbertCheckerInterface checker semantics)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (accepted : Nat → Prop)
    (traceSystem :
      _root_.BoundedArithmeticLab.ConcreteVerifierTraceSystem.{u}
        target accepted) :
    Type (u + 1) where
  toVerifierTrace :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        interface.traceOf proof = some trace →
          trace.proof = proof →
            interface.traceChecker.checkTrace trace = true →
              proof.conclusion.code = scale_data.powerBoundRawCode n →
                traceSystem.Trace
  verifierTrace_index :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        ∀ htraceOf :
          interface.traceOf proof = some trace,
        ∀ htraceProof :
          trace.proof = proof,
        ∀ htraceCheck :
          interface.traceChecker.checkTrace trace = true,
        ∀ hconclusion :
          proof.conclusion.code = scale_data.powerBoundRawCode n,
          traceSystem.index
            (toVerifierTrace n proof trace
              htraceOf htraceProof htraceCheck hconclusion) = n
  verifierTrace_accepted :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        ∀ htraceOf :
          interface.traceOf proof = some trace,
        ∀ htraceProof :
          trace.proof = proof,
        ∀ htraceCheck :
          interface.traceChecker.checkTrace trace = true,
        ∀ hconclusion :
          proof.conclusion.code = scale_data.powerBoundRawCode n,
          traceSystem.traceAccepted
            (toVerifierTrace n proof trace
              htraceOf htraceProof htraceCheck hconclusion)
  verifierTrace_size_le_proof_code :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        ∀ htraceOf :
          interface.traceOf proof = some trace,
        ∀ htraceProof :
          trace.proof = proof,
        ∀ htraceCheck :
          interface.traceChecker.checkTrace trace = true,
        ∀ hconclusion :
          proof.conclusion.code = scale_data.powerBoundRawCode n,
          traceSystem.trace_size
            (toVerifierTrace n proof trace
              htraceOf htraceProof htraceCheck hconclusion) ≤ proof.code

/--
Linear-overhead concrete verifier-trace interpretation of PA/Hilbert checked
traces.  This is the realistic form for an actual verifier simulation: the
interpreted verifier trace may be longer than the original numeric proof code,
but only by a fixed affine bound `C * proof.code + D`.
-/
structure PAHilbertCheckedTraceConcreteVerifierLinearRealization
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (interface : PAHilbertCheckerInterface checker semantics)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (accepted : Nat → Prop)
    (traceSystem :
      _root_.BoundedArithmeticLab.ConcreteVerifierTraceSystem.{u}
        target accepted) :
    Type (u + 1) where
  C : Real
  D : Real
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  toVerifierTrace :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        interface.traceOf proof = some trace →
          trace.proof = proof →
            interface.traceChecker.checkTrace trace = true →
              proof.conclusion.code = scale_data.powerBoundRawCode n →
                traceSystem.Trace
  verifierTrace_index :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        ∀ htraceOf :
          interface.traceOf proof = some trace,
        ∀ htraceProof :
          trace.proof = proof,
        ∀ htraceCheck :
          interface.traceChecker.checkTrace trace = true,
        ∀ hconclusion :
          proof.conclusion.code = scale_data.powerBoundRawCode n,
          traceSystem.index
            (toVerifierTrace n proof trace
              htraceOf htraceProof htraceCheck hconclusion) = n
  verifierTrace_accepted :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        ∀ htraceOf :
          interface.traceOf proof = some trace,
        ∀ htraceProof :
          trace.proof = proof,
        ∀ htraceCheck :
          interface.traceChecker.checkTrace trace = true,
        ∀ hconclusion :
          proof.conclusion.code = scale_data.powerBoundRawCode n,
          traceSystem.traceAccepted
            (toVerifierTrace n proof trace
              htraceOf htraceProof htraceCheck hconclusion)
  verifierTrace_size_le_linear :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        ∀ htraceOf :
          interface.traceOf proof = some trace,
        ∀ htraceProof :
          trace.proof = proof,
        ∀ htraceCheck :
          interface.traceChecker.checkTrace trace = true,
        ∀ hconclusion :
          proof.conclusion.code = scale_data.powerBoundRawCode n,
          (traceSystem.trace_size
            (toVerifierTrace n proof trace
              htraceOf htraceProof htraceCheck hconclusion) : Real) ≤
            C * (proof.code : Real) + D

/--
Linear compiler from PA/Hilbert checked traces to canonical Cn-box proof
certificates.  This is the next non-black-box implementation target for the
lower-bound route: the compiler must actually produce the canonical
Buss-S²₁ certificate consumed by `canonicalProofCertificateVerifierMachine`,
and the resulting verifier trace must have only affine overhead over the
original PA/Hilbert numeric proof code.
-/
structure PAHilbertCheckedTraceToCanonicalProofCertificateLinearCompiler
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (interface : PAHilbertCheckerInterface checker semantics)
    (bound : Nat → Real) :
    Type where
  C : Real
  D : Real
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  trace_to_certificate :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        interface.traceOf proof = some trace →
          trace.proof = proof →
            interface.traceChecker.checkTrace trace = true →
              proof.conclusion.code = scale_data.powerBoundRawCode n →
                _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalProofCertificateAt
                  bound n
  certificate_trace_size_le_linear :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        ∀ htraceOf :
          interface.traceOf proof = some trace,
        ∀ htraceProof :
          trace.proof = proof,
        ∀ htraceCheck :
          interface.traceChecker.checkTrace trace = true,
        ∀ hconclusion :
          proof.conclusion.code = scale_data.powerBoundRawCode n,
          (_root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace.size
            ((trace_to_certificate n proof trace
              htraceOf htraceProof htraceCheck hconclusion).toAcceptedTrace) :
              Real) ≤
            C * (proof.code : Real) + D

/--
Accepted-natural-code version of the canonical proof-certificate compiler.
This is closer to the actual finite-search lower-bound object than the checked
trace version: from every numeric PA/Hilbert proof code accepted for
`powerBoundRawCode n`, it constructs the canonical Cn-box proof certificate,
with proof-object size linearly controlled by the numeric code.
-/
structure PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (bound : Nat → Real) :
    Type where
  C : Real
  D : Real
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  accepted_to_certificate :
    ∀ n : Nat, ∀ code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code →
        _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalProofCertificateAt
          bound n
  certificate_proof_size_le_linear :
    ∀ n : Nat, ∀ code : Nat,
      ∀ haccepted :
        PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code,
        ((((accepted_to_certificate n code haccepted).proof.size : Nat) :
            Real)) ≤
          C * (code : Real) + D

/--
Bound-free accepted-natural-code compiler to Buss-S²₁ proof objects.  This is
the minimal lower-bound-side extractor: it does not require a certificate
acceptance bound `bound n`; it only extracts, from every accepted numeric
PA/Hilbert proof code, a Buss-S²₁ proof object of the target formula with
linear size overhead.
-/
structure PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula) :
    Type 1 where
  C : Real
  D : Real
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  accepted_to_bussS21ProofObject_linear :
    ∀ n : Nat, ∀ code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code →
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject
            _root_.BoundedArithmeticLab.BussS21Axiom,
          proof.conclusion = target n ∧
            (proof.size : Real) ≤ C * (code : Real) + D

/--
Operational verifier-machine interpretation of PA/Hilbert checked traces.  This
is a still lower implementation target than `ConcreteVerifierTraceSystem`: the
PA checked trace must be realized as an accepted run of a concrete verifier
machine, and the existing `OperationalS21Compiler` then turns that run into a
Buss-S²₁ proof object.
-/
structure PAHilbertCheckedTraceOperationalVerifierRealization
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (interface : PAHilbertCheckerInterface checker semantics)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (M : _root_.BoundedArithmeticLab.VerifierMachine.{u})
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        M target) :
    Type (u + 1) where
  toAcceptedTrace :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        interface.traceOf proof = some trace →
          trace.proof = proof →
            interface.traceChecker.checkTrace trace = true →
              proof.conclusion.code = scale_data.powerBoundRawCode n →
                _root_.BoundedArithmeticLab.VerifierMachine.AcceptedTrace M n
  acceptedTrace_size_le_proof_code :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        ∀ htraceOf :
          interface.traceOf proof = some trace,
        ∀ htraceProof :
          trace.proof = proof,
        ∀ htraceCheck :
          interface.traceChecker.checkTrace trace = true,
        ∀ hconclusion :
          proof.conclusion.code = scale_data.powerBoundRawCode n,
          (_root_.BoundedArithmeticLab.VerifierMachine.AcceptedTrace.size
            (toAcceptedTrace n proof trace
              htraceOf htraceProof htraceCheck hconclusion)) ≤ proof.code

/--
Linear-overhead operational verifier-machine interpretation.  This is the
form needed for real machine traces, where the accepted run size may have a
constant or linear overhead over the original PA/Hilbert proof code.
-/
structure PAHilbertCheckedTraceOperationalVerifierLinearRealization
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (interface : PAHilbertCheckerInterface checker semantics)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (M : _root_.BoundedArithmeticLab.VerifierMachine.{u})
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        M target) :
    Type (u + 1) where
  C : Real
  D : Real
  C_nonneg : 0 ≤ C
  D_nonneg : 0 ≤ D
  toAcceptedTrace :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        interface.traceOf proof = some trace →
          trace.proof = proof →
            interface.traceChecker.checkTrace trace = true →
              proof.conclusion.code = scale_data.powerBoundRawCode n →
                _root_.BoundedArithmeticLab.VerifierMachine.AcceptedTrace M n
  acceptedTrace_size_le_linear :
    ∀ n : Nat, ∀ proof : PAHilbertProofObject,
      ∀ trace : PAHilbertCheckedProofTrace,
        ∀ htraceOf :
          interface.traceOf proof = some trace,
        ∀ htraceProof :
          trace.proof = proof,
        ∀ htraceCheck :
          interface.traceChecker.checkTrace trace = true,
        ∀ hconclusion :
          proof.conclusion.code = scale_data.powerBoundRawCode n,
          (_root_.BoundedArithmeticLab.VerifierMachine.AcceptedTrace.size
            (toAcceptedTrace n proof trace
              htraceOf htraceProof htraceCheck hconclusion) : Real) ≤
            C * (proof.code : Real) + D

/--
Accepted state for a proof-carrying PA/Hilbert checked-trace verifier.  This is
not yet the S²₁ compiler; it is the precise operational object saying that the
checked trace data has been packaged as an accepting verifier run.
-/
structure PAHilbertCheckedTraceVerifierAcceptedData
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (interface : PAHilbertCheckerInterface checker semantics) :
    Type where
  n : Nat
  proof : PAHilbertProofObject
  trace : PAHilbertCheckedProofTrace
  htraceOf : interface.traceOf proof = some trace
  htraceProof : trace.proof = proof
  htraceCheck : interface.traceChecker.checkTrace trace = true
  hconclusion : proof.conclusion.code = scale_data.powerBoundRawCode n

/-- State space for the proof-carrying PA/Hilbert checked-trace verifier. -/
inductive PAHilbertCheckedTraceVerifierState
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (interface : PAHilbertCheckerInterface checker semantics) :
    Type where
  | start (n : Nat)
  | accepted
      (data :
        PAHilbertCheckedTraceVerifierAcceptedData
          scale_data checker semantics interface)

/--
Proof-carrying PA/Hilbert checked-trace verifier machine.  A single transition
from `start n` to an accepted state is allowed exactly when the accepted state's
stored index is the same `n`.
-/
def paHilbertCheckedTraceVerifierMachine
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (interface : PAHilbertCheckerInterface checker semantics) :
    _root_.BoundedArithmeticLab.VerifierMachine where
  State :=
    PAHilbertCheckedTraceVerifierState
      scale_data checker semantics interface
  initial := fun n =>
    PAHilbertCheckedTraceVerifierState.start n
  step := fun state next =>
    match state, next with
    | PAHilbertCheckedTraceVerifierState.start n,
        PAHilbertCheckedTraceVerifierState.accepted data =>
        data.n = n
    | _, _ => False
  accepting := fun state =>
    match state with
    | PAHilbertCheckedTraceVerifierState.accepted _ => True
    | _ => False
  stateSize := fun _ => 1

/--
Every checked trace satisfying the canonical conclusion condition gives a
one-step accepted run of the proof-carrying PA/Hilbert checked-trace verifier.
The run has size `2`, hence is linearly bounded by `0 * proof.code + 2`.
-/
def paHilbertCheckedTraceVerifierLinearRealization
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        (paHilbertCheckedTraceVerifierMachine
          scale_data checker semantics interface)
        target) :
    PAHilbertCheckedTraceOperationalVerifierLinearRealization
      scale_data checker semantics interface target
      (paHilbertCheckedTraceVerifierMachine
        scale_data checker semantics interface)
      compiler where
  C := 0
  D := 2
  C_nonneg := by norm_num
  D_nonneg := by norm_num
  toAcceptedTrace := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    let data :
        PAHilbertCheckedTraceVerifierAcceptedData
          scale_data checker semantics interface :=
      { n := n
        proof := proof
        trace := trace
        htraceOf := htraceOf
        htraceProof := htraceProof
        htraceCheck := htraceCheck
        hconclusion := hconclusion }
    exact
      { final :=
          PAHilbertCheckedTraceVerifierState.accepted data
        steps := 1
        reaches :=
          _root_.BoundedArithmeticLab.VerifierMachine.Reaches.cons
            (M :=
              paHilbertCheckedTraceVerifierMachine
                scale_data checker semantics interface)
            (s := PAHilbertCheckedTraceVerifierState.start n)
            (t := PAHilbertCheckedTraceVerifierState.accepted data)
            (u := PAHilbertCheckedTraceVerifierState.accepted data)
            (k := 0)
            (by
              dsimp [paHilbertCheckedTraceVerifierMachine])
            (_root_.BoundedArithmeticLab.VerifierMachine.Reaches.refl
              (M :=
                paHilbertCheckedTraceVerifierMachine
                  scale_data checker semantics interface)
              (PAHilbertCheckedTraceVerifierState.accepted data))
        accepts := trivial }
  acceptedTrace_size_le_linear := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    norm_num [_root_.BoundedArithmeticLab.VerifierMachine.AcceptedTrace.size]

/--
The accepted trace carried by a stored PA/Hilbert checked-trace witness.  This
is the concrete non-vacuous trace used to audit any proposed compiler for the
one-step checked-trace verifier.
-/
def checkedTraceVerifierAcceptedTraceOfData
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {interface : PAHilbertCheckerInterface checker semantics}
    (data :
      PAHilbertCheckedTraceVerifierAcceptedData
        scale_data checker semantics interface) :
    _root_.BoundedArithmeticLab.VerifierMachine.AcceptedTrace
      (paHilbertCheckedTraceVerifierMachine
        scale_data checker semantics interface) data.n where
  final :=
    PAHilbertCheckedTraceVerifierState.accepted data
  steps := 1
  reaches :=
    _root_.BoundedArithmeticLab.VerifierMachine.Reaches.cons
      (M :=
        paHilbertCheckedTraceVerifierMachine
          scale_data checker semantics interface)
      (s := PAHilbertCheckedTraceVerifierState.start data.n)
      (t := PAHilbertCheckedTraceVerifierState.accepted data)
      (u := PAHilbertCheckedTraceVerifierState.accepted data)
      (k := 0)
      (by
        dsimp [paHilbertCheckedTraceVerifierMachine])
      (_root_.BoundedArithmeticLab.VerifierMachine.Reaches.refl
        (M :=
          paHilbertCheckedTraceVerifierMachine
            scale_data checker semantics interface)
        (PAHilbertCheckedTraceVerifierState.accepted data))
  accepts := trivial

/--
The current proof-carrying checked-trace verifier has one transition and its
operational trace-size convention counts only `steps + 1`.  Thus every stored
accepted datum has verifier-trace size exactly `2`.
-/
theorem checkedTraceVerifierAcceptedTraceOfData_size
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {interface : PAHilbertCheckerInterface checker semantics}
    (data :
      PAHilbertCheckedTraceVerifierAcceptedData
        scale_data checker semantics interface) :
    _root_.BoundedArithmeticLab.VerifierMachine.AcceptedTrace.size
      (checkedTraceVerifierAcceptedTraceOfData data) = 2 := by
  rfl

/--
Every accepted run of the one-step checked-trace verifier ends in a stored
PA/Hilbert checked-trace datum.  This is just inversion on the verifier's
accepting states; no proof-complexity content is hidden here.
-/
theorem checkedTraceVerifierAcceptedTrace_hasAcceptedData
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {interface : PAHilbertCheckerInterface checker semantics}
    {n : Nat}
    (tr :
      _root_.BoundedArithmeticLab.VerifierMachine.AcceptedTrace
        (paHilbertCheckedTraceVerifierMachine
          scale_data checker semantics interface) n) :
    ∃ data :
      PAHilbertCheckedTraceVerifierAcceptedData
        scale_data checker semantics interface,
      tr.final =
        PAHilbertCheckedTraceVerifierState.accepted data := by
  cases hfinal : tr.final with
  | start m =>
      have hfalse : False := by
        simpa [paHilbertCheckedTraceVerifierMachine, hfinal] using tr.accepts
      cases hfalse
  | accepted data =>
      exact ⟨data, rfl⟩

/--
Any `OperationalS21Compiler` for the one-step checked-trace verifier turns a
stored accepted PA/Hilbert trace into a Buss-S²₁ proof object of
`finiteConsistencyFormula data.n`.

This is the exact content of the remaining compiler obligation.
-/
theorem checkedTraceVerifierCompiler_produces_bussS21ProofObject_of_data
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {interface : PAHilbertCheckerInterface checker semantics}
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        (paHilbertCheckedTraceVerifierMachine
          scale_data checker semantics interface)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    (data :
      PAHilbertCheckedTraceVerifierAcceptedData
        scale_data checker semantics interface) :
    ∃ proof :
      _root_.BoundedArithmeticLab.BAProofObject
        _root_.BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
        _root_.BoundedArithmeticLab.finiteConsistencyFormula data.n :=
  ⟨compiler.compileTrace data.n
      (checkedTraceVerifierAcceptedTraceOfData data),
    compiler.compile_conclusion data.n
      (checkedTraceVerifierAcceptedTraceOfData data)⟩

/--
Size-opened form of the previous theorem.  With the current one-step
proof-carrying verifier, any `OperationalS21Compiler` would have to output a
Buss-S²₁ proof object of `finiteConsistencyFormula data.n` of size at most `2`.

This makes the remaining compiler obligation exact: the current verifier is not
measuring the carried PA/Hilbert trace data in its operational trace size.
-/
theorem checkedTraceVerifierCompiler_produces_size_le_two_bussS21ProofObject_of_data
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {interface : PAHilbertCheckerInterface checker semantics}
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        (paHilbertCheckedTraceVerifierMachine
          scale_data checker semantics interface)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    (data :
      PAHilbertCheckedTraceVerifierAcceptedData
        scale_data checker semantics interface) :
    ∃ proof :
      _root_.BoundedArithmeticLab.BAProofObject
        _root_.BoundedArithmeticLab.BussS21Axiom,
      proof.conclusion =
          _root_.BoundedArithmeticLab.finiteConsistencyFormula data.n ∧
        proof.size ≤ 2 := by
  let tr := checkedTraceVerifierAcceptedTraceOfData data
  let proof := compiler.compileTrace data.n tr
  refine ⟨proof, compiler.compile_conclusion data.n tr, ?_⟩
  have hsize_real :
      (proof.size : Real) ≤ (2 : Real) := by
    have hcompile := compiler.compile_size_le_trace_size data.n tr
    simpa [proof, tr, checkedTraceVerifierAcceptedTraceOfData,
      _root_.BoundedArithmeticLab.VerifierMachine.AcceptedTrace.size] using
      hcompile
  exact_mod_cast hsize_real

/--
Contrast with the certificate verifier already available in the sidecar
library: its accepted-trace size includes the carried certificate size.  This
is the size convention needed for a real lower-bound route; unlike the current
one-step proof-carrying verifier, it does not collapse every accepted trace to
constant size `2`.
-/
theorem proofCertificateVerifierAcceptedTrace_size_eq_cert_size_add_two
    {target : Nat → _root_.BoundedArithmeticLab.BAFormula}
    {bound : Nat → Real} {n : Nat}
    (tr :
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace
        (_root_.BoundedArithmeticLab.proofCertificateVerifierMachine
          target bound) n) :
    _root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace.size
      tr = tr.cert.size + 2 := by
  dsimp [
    _root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace.size,
    _root_.BoundedArithmeticLab.proofCertificateVerifierMachine,
    _root_.BoundedArithmeticLab.ProofCertificateState.size]

/--
For the concrete proof-certificate verifier, the built-in certificate compiler
returns the carried certificate itself.  Hence the compiled proof-object size is
the certificate size, not a constant operational step count.
-/
theorem proofCertificateVerifierCompiler_compile_size_eq_cert_size
    {target : Nat → _root_.BoundedArithmeticLab.BAFormula}
    {bound : Nat → Real} {n : Nat}
    (hbound : _root_.BoundedArithmeticLab.IsPolynomialBound bound)
    (tr :
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace
        (_root_.BoundedArithmeticLab.proofCertificateVerifierMachine
          target bound) n) :
    ((_root_.BoundedArithmeticLab.proofCertificateVerifierMachine.compiler
        target hbound).compileTrace n tr).size = tr.cert.size := by
  rfl

/--
Combined non-collapsing size statement for the proof-certificate verifier:
the compiled proof object is bounded by `cert.size + 2` because the trace size is
exactly `cert.size + 2`, not because all traces have constant size.
-/
theorem proofCertificateVerifierCompiler_compile_size_le_cert_size_add_two
    {target : Nat → _root_.BoundedArithmeticLab.BAFormula}
    {bound : Nat → Real} {n : Nat}
    (hbound : _root_.BoundedArithmeticLab.IsPolynomialBound bound)
    (tr :
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace
        (_root_.BoundedArithmeticLab.proofCertificateVerifierMachine
          target bound) n) :
    ((_root_.BoundedArithmeticLab.proofCertificateVerifierMachine.compiler
        target hbound).compileTrace n tr).size ≤ tr.cert.size + 2 := by
  rw [proofCertificateVerifierCompiler_compile_size_eq_cert_size hbound tr]
  exact Nat.le_add_right tr.cert.size 2

/--
Certificate-verifier state for native accepted PA/Hilbert natural proof codes.
Unlike the one-step operational verifier above, the certificate machine stores
the numeric proof code as the certificate and charges it in `stateSize`.
-/
inductive PAHilbertAcceptedNatCodeCertificateState
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker) where
  | start (n code : Nat)
  | accepted (n code : Nat)
      (haccepted :
        PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code)

namespace PAHilbertAcceptedNatCodeCertificateState

def size
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker} :
    PAHilbertAcceptedNatCodeCertificateState scale_data checker → Nat
  | start _ code => code + 1
  | accepted _ code _ => code + 1

def accepting
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker} :
    PAHilbertAcceptedNatCodeCertificateState scale_data checker → Prop
  | accepted _ _ _ => True
  | start _ _ => False

inductive Step
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker} :
    PAHilbertAcceptedNatCodeCertificateState scale_data checker →
    PAHilbertAcceptedNatCodeCertificateState scale_data checker → Prop where
  | accept {n code : Nat}
      (haccepted :
        PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code) :
      Step (start n code) (accepted n code haccepted)

end PAHilbertAcceptedNatCodeCertificateState

/--
Certificate verifier whose certificates are native PA/Hilbert natural proof
codes.  Its accepted traces are non-collapsing: the trace size is the numeric
code size plus a fixed constant.
-/
def paHilbertAcceptedNatCodeCertificateVerifierMachine
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker) :
    _root_.BoundedArithmeticLab.CertificateVerifierMachine where
  Cert := Nat
  State := PAHilbertAcceptedNatCodeCertificateState scale_data checker
  initial := fun n code =>
    PAHilbertAcceptedNatCodeCertificateState.start n code
  step := PAHilbertAcceptedNatCodeCertificateState.Step
  accepting := PAHilbertAcceptedNatCodeCertificateState.accepting
  stateSize := PAHilbertAcceptedNatCodeCertificateState.size

/--
Every accepted native PA/Hilbert proof code gives a one-step accepted trace of
the certificate verifier that stores that same numeric code as its certificate.
-/
def paHilbertAcceptedNatCodeCertificateTraceOfAccepted
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {n code : Nat}
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) code) :
    _root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace
      (paHilbertAcceptedNatCodeCertificateVerifierMachine
        scale_data checker) n where
  cert := code
  final :=
    PAHilbertAcceptedNatCodeCertificateState.accepted n code haccepted
  steps := 1
  reaches :=
    _root_.BoundedArithmeticLab.CertificateVerifierMachine.Reaches.cons
      (M :=
        paHilbertAcceptedNatCodeCertificateVerifierMachine
          scale_data checker)
      (s :=
        PAHilbertAcceptedNatCodeCertificateState.start n code)
      (t :=
        PAHilbertAcceptedNatCodeCertificateState.accepted n code haccepted)
      (u :=
        PAHilbertAcceptedNatCodeCertificateState.accepted n code haccepted)
      (k := 0)
      (PAHilbertAcceptedNatCodeCertificateState.Step.accept haccepted)
      (_root_.BoundedArithmeticLab.CertificateVerifierMachine.Reaches.refl
        (M :=
          paHilbertAcceptedNatCodeCertificateVerifierMachine
            scale_data checker)
        (PAHilbertAcceptedNatCodeCertificateState.accepted n code haccepted))
  accepts := trivial

/--
The accepted-code certificate verifier charges the carried numeric proof code:
the accepted trace has size `code + 2`.
-/
theorem paHilbertAcceptedNatCodeCertificateTraceOfAccepted_size
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {n code : Nat}
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) code) :
    _root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace.size
      (paHilbertAcceptedNatCodeCertificateTraceOfAccepted
        (scale_data := scale_data) (checker := checker)
        (n := n) (code := code) haccepted) = code + 2 := by
  rfl

/--
Local S²₁ compiler for the accepted-code certificate verifier.  This is the
exact lower-bound-side compiler obligation: every accepted trace compiles to a
Buss-S²₁ proof object of the target, and the proof-object size is bounded by
that same trace size.

Unlike `CertificateOperationalS21Compiler`, this local interface does not ask
for a global polynomial `trace_bound n` bounding all certificates for the same
index `n`; such a bound is not needed for the accepted-code lower-bound
transfer.
-/
structure PAHilbertAcceptedNatCodeCertificateLocalS21Compiler
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula) :
    Type 1 where
  compileTrace :
    ∀ n : Nat,
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace
        (paHilbertAcceptedNatCodeCertificateVerifierMachine
          scale_data checker) n →
        _root_.BoundedArithmeticLab.BAProofObject
          _root_.BoundedArithmeticLab.BussS21Axiom
  compile_conclusion :
    ∀ n : Nat,
      ∀ tr :
        _root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace
          (paHilbertAcceptedNatCodeCertificateVerifierMachine
            scale_data checker) n,
        (compileTrace n tr).conclusion = target n
  compile_size_le_trace_size :
    ∀ n : Nat,
      ∀ tr :
        _root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace
          (paHilbertAcceptedNatCodeCertificateVerifierMachine
            scale_data checker) n,
        ((compileTrace n tr).size : Real) ≤
          (_root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace.size
            tr : Real)

/--
The older global certificate operational compiler is a special case of the
local accepted-code compiler; the global `trace_bound` fields are intentionally
discarded here.
-/
def
    PAHilbertAcceptedNatCodeCertificateOperationalCompiler_to_LocalS21Compiler
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {target : Nat → _root_.BoundedArithmeticLab.BAFormula}
    (compiler :
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.CertificateOperationalS21Compiler
        (paHilbertAcceptedNatCodeCertificateVerifierMachine
          scale_data checker)
        target) :
    PAHilbertAcceptedNatCodeCertificateLocalS21Compiler
      scale_data checker target where
  compileTrace := compiler.compileTrace
  compile_conclusion := compiler.compile_conclusion
  compile_size_le_trace_size := compiler.compile_size_le_trace_size

/--
Direct code-plus-two compiler from accepted PA/Hilbert natural proof codes to
Buss-S²₁ proof objects.  This is the sharp lower-bound-side target induced by
the non-collapsing accepted-code certificate verifier: the verifier trace for
an accepted code has size exactly `code + 2`, so no separate verifier trace or
global `trace_bound` field is part of the remaining obligation.
-/
structure PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula) :
    Type 1 where
  accepted_to_bussS21ProofObject_codePlusTwo :
    ∀ n : Nat, ∀ code : Nat,
      PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code →
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject
            _root_.BoundedArithmeticLab.BussS21Axiom,
          proof.conclusion = target n ∧
            (proof.size : Real) ≤ (code : Real) + 2

/--
A local S²₁ compiler for the non-collapsing accepted-code certificate verifier
induces the direct code-plus-two compiler.  The only size fact used is the
proved equality `accepted trace size = code + 2`.
-/
def
    PAHilbertAcceptedNatCodeCertificateLocalS21Compiler_to_CodePlusTwoCompiler
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {target : Nat → _root_.BoundedArithmeticLab.BAFormula}
    (compiler :
      PAHilbertAcceptedNatCodeCertificateLocalS21Compiler
        scale_data checker target) :
    PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler
      scale_data checker target where
  accepted_to_bussS21ProofObject_codePlusTwo := by
    intro n code haccepted
    let tr :=
      paHilbertAcceptedNatCodeCertificateTraceOfAccepted
        (scale_data := scale_data) (checker := checker)
        (n := n) (code := code) haccepted
    let proof := compiler.compileTrace n tr
    have hconclusion :
        proof.conclusion = target n := by
      simpa [proof] using compiler.compile_conclusion n tr
    have hcompile :
        (proof.size : Real) ≤
          (_root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace.size
            tr : Real) := by
      simpa [proof] using compiler.compile_size_le_trace_size n tr
    have htrace :
        (_root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace.size
          tr : Real) = (code : Real) + 2 := by
      have htrace_nat :
          _root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace.size
            tr = code + 2 := by
        simpa [tr] using
          paHilbertAcceptedNatCodeCertificateTraceOfAccepted_size
            (scale_data := scale_data) (checker := checker)
            (n := n) (code := code) haccepted
      exact_mod_cast htrace_nat
    refine ⟨proof, hconclusion, ?_⟩
    calc
      (proof.size : Real) ≤
          (_root_.BoundedArithmeticLab.CertificateVerifierMachine.AcceptedTrace.size
            tr : Real) := hcompile
      _ = (code : Real) + 2 := htrace

/--
The direct code-plus-two compiler is a special case of the existing affine
accepted-code Buss-S²₁ compiler, with constants `C = 1` and `D = 2`.
-/
def
    PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler_to_LinearCompiler
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {target : Nat → _root_.BoundedArithmeticLab.BAFormula}
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler
        scale_data checker target) :
    PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler
      scale_data checker target where
  C := 1
  D := 2
  C_nonneg := by norm_num
  D_nonneg := by norm_num
  accepted_to_bussS21ProofObject_linear := by
    intro n code haccepted
    rcases compiler.accepted_to_bussS21ProofObject_codePlusTwo
        n code haccepted with ⟨proof, hconclusion, hsize⟩
    refine ⟨proof, hconclusion, ?_⟩
    calc
      (proof.size : Real) ≤ (code : Real) + 2 := hsize
      _ = (1 : Real) * (code : Real) + 2 := by ring

/--
Any local S²₁ compiler for the accepted-code certificate verifier gives the
bound-free accepted-code Buss-S²₁ compiler required by the lower-bound core.
The size overhead is exactly affine: `proof.size <= code + 2`.
-/
def
    PAHilbertAcceptedNatCodeCertificateLocalS21Compiler_to_BussS21ProofObjectLinearCompiler
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (compiler :
      PAHilbertAcceptedNatCodeCertificateLocalS21Compiler
        scale_data checker
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler
      scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula :=
  PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler_to_LinearCompiler
    (PAHilbertAcceptedNatCodeCertificateLocalS21Compiler_to_CodePlusTwoCompiler
      compiler)

/--
Compatibility wrapper for the older global certificate operational compiler.
It first forgets the global `trace_bound` fields and then applies the exact
local lower-bound compiler route.
-/
def
    PAHilbertAcceptedNatCodeCertificateVerifierCompiler_to_BussS21ProofObjectLinearCompiler
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (compiler :
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.CertificateOperationalS21Compiler
        (paHilbertAcceptedNatCodeCertificateVerifierMachine
          scale_data checker)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler
      scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula :=
  PAHilbertAcceptedNatCodeCertificateLocalS21Compiler_to_BussS21ProofObjectLinearCompiler
    (PAHilbertAcceptedNatCodeCertificateOperationalCompiler_to_LocalS21Compiler
      compiler)

/--
Current-toy obstruction for the checked-trace verifier compiler.  If the
one-step verifier has even one accepted PA/Hilbert trace datum, then a compiler
to `finiteConsistencyFormula` would create a Buss-S²₁ proof object that the
current toy bounded-arithmetic calculus provably lacks.
-/
theorem no_checkedTraceVerifierCompiler_currentToy_of_acceptedData
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {interface : PAHilbertCheckerInterface checker semantics}
    (data :
      PAHilbertCheckedTraceVerifierAcceptedData
        scale_data checker semantics interface) :
    _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        (paHilbertCheckedTraceVerifierMachine
          scale_data checker semantics interface)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula →
      False := by
  intro compiler
  exact no_currentToyBussS21ProofObject_finiteConsistencyFormula data.n
    (checkedTraceVerifierCompiler_produces_bussS21ProofObject_of_data
      compiler data)

/--
If the one-step checked-trace verifier accepts even one input, then the current
toy Buss-S²₁ calculus cannot support an `OperationalS21Compiler` for the
finite-consistency target.  A real compiler must therefore replace the toy
calculus, not merely wrap this verifier.
-/
theorem no_checkedTraceVerifierCompiler_currentToy_of_acceptsInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {interface : PAHilbertCheckerInterface checker semantics}
    {n : Nat}
    (haccepts :
      _root_.BoundedArithmeticLab.VerifierMachine.acceptsInput
        (paHilbertCheckedTraceVerifierMachine
          scale_data checker semantics interface) n) :
    _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        (paHilbertCheckedTraceVerifierMachine
          scale_data checker semantics interface)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula →
      False := by
  intro compiler
  rcases haccepts with ⟨tr⟩
  rcases checkedTraceVerifierAcceptedTrace_hasAcceptedData tr with ⟨data, _hfinal⟩
  exact no_checkedTraceVerifierCompiler_currentToy_of_acceptedData data compiler

/--
Equivalently, any current-toy compiler for the checked-trace verifier would
force that verifier to reject every input.  This records the non-vacuity
condition needed by the short lower-bound proof.
-/
theorem checkedTraceVerifierCompiler_currentToy_forces_no_acceptsInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {interface : PAHilbertCheckerInterface checker semantics}
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        (paHilbertCheckedTraceVerifierMachine
          scale_data checker semantics interface)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    (n : Nat) :
    ¬ _root_.BoundedArithmeticLab.VerifierMachine.acceptsInput
        (paHilbertCheckedTraceVerifierMachine
          scale_data checker semantics interface) n := by
  intro haccepts
  exact no_checkedTraceVerifierCompiler_currentToy_of_acceptsInput haccepts compiler

/--
The trace compiler closes the accepted-code extractor bridge using only the
existing PA/Hilbert checker interface.  This opens the previous
`BAProofObjectAcceptedNatCodeBridge` black box one level further.
-/
def
    PAHilbertCheckedTraceToBAProofObjectCompiler_to_BAProofObjectAcceptedNatCodeBridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (compiler :
      PAHilbertCheckedTraceToBAProofObjectCompiler
        scale_data checker semantics interface Ax target) :
    BAProofObjectAcceptedNatCodeBridge scale_data checker Ax target where
  accepted_to_baProofObject := by
    intro n code haccepted
    rcases haccepted with ⟨proof, hdecode, hconclusion, haccepts⟩
    rcases
        PAHilbertCheckerInterface.accepts_to_checked_trace
          interface proof proof.conclusion haccepts with
      ⟨trace, htraceOf, htraceProof, htraceCheck⟩
    rcases
        compiler.trace_to_baProofObject
          n proof trace htraceOf htraceProof htraceCheck hconclusion with
      ⟨baProof, hbaConclusion, hbaSize_le_proofCode⟩
    have hproofCode : proof.code = code :=
      checker.decoder.decodedCode_eq code proof hdecode
    exact
      ⟨baProof, hbaConclusion, by
        simpa [hproofCode] using hbaSize_le_proofCode⟩

/--
Linear trace compiler closes the linear accepted-code extractor bridge.
-/
def
    PAHilbertCheckedTraceToBAProofObjectLinearCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (compiler :
      PAHilbertCheckedTraceToBAProofObjectLinearCompiler
        scale_data checker semantics interface Ax target) :
    BAProofObjectAcceptedNatCodeLinearBridge scale_data checker Ax target where
  C := compiler.C
  D := compiler.D
  C_nonneg := compiler.C_nonneg
  D_nonneg := compiler.D_nonneg
  accepted_to_baProofObject_linear := by
    intro n code haccepted
    rcases haccepted with ⟨proof, hdecode, hconclusion, haccepts⟩
    rcases
        PAHilbertCheckerInterface.accepts_to_checked_trace
          interface proof proof.conclusion haccepts with
      ⟨trace, htraceOf, htraceProof, htraceCheck⟩
    rcases
        compiler.trace_to_baProofObject_linear
          n proof trace htraceOf htraceProof htraceCheck hconclusion with
      ⟨baProof, hbaConclusion, hbaSize_le_linear⟩
    have hproofCode : proof.code = code :=
      checker.decoder.decodedCode_eq code proof hdecode
    exact
      ⟨baProof, hbaConclusion, by
        simpa [hproofCode] using hbaSize_le_linear⟩

/-- A no-overhead trace compiler is a linear trace compiler with constants
`C = 1`, `D = 0`. -/
def PAHilbertCheckedTraceToBAProofObjectCompiler_to_LinearCompiler
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {interface : PAHilbertCheckerInterface checker semantics}
    {Ax : _root_.BoundedArithmeticLab.BAFormula → Prop}
    {target : Nat → _root_.BoundedArithmeticLab.BAFormula}
    (compiler :
      PAHilbertCheckedTraceToBAProofObjectCompiler
        scale_data checker semantics interface Ax target) :
    PAHilbertCheckedTraceToBAProofObjectLinearCompiler
      scale_data checker semantics interface Ax target where
  C := 1
  D := 0
  C_nonneg := by norm_num
  D_nonneg := by norm_num
  trace_to_baProofObject_linear := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    rcases
        compiler.trace_to_baProofObject
          n proof trace htraceOf htraceProof htraceCheck hconclusion with
      ⟨baProof, hbaConclusion, hbaSize⟩
    refine ⟨baProof, hbaConclusion, ?_⟩
    have hsize_real : (baProof.size : Real) ≤ (proof.code : Real) := by
      exact_mod_cast hbaSize
    simpa using hsize_real

/--
S²₁ trace compiler implies the PA trace compiler used by the canonical
literature route.  The only mathematical ingredient is the already formalized
inclusion of Buss-S²₁ axioms into PA axioms; `size_mapS21ToPA` proves that this
map preserves proof-object size exactly.
-/
def
    PAHilbertCheckedTraceToBussS21ProofObjectCompiler_to_PACompiler
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (compiler :
      PAHilbertCheckedTraceToBussS21ProofObjectCompiler
        scale_data checker semantics interface target) :
    PAHilbertCheckedTraceToBAProofObjectCompiler
      scale_data checker semantics interface
      _root_.BoundedArithmeticLab.PAAxiom target where
  trace_to_baProofObject := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    rcases
        compiler.trace_to_bussS21ProofObject
          n proof trace htraceOf htraceProof htraceCheck hconclusion with
      ⟨s21Proof, hs21Conclusion, hs21Size⟩
    let paProof :
        _root_.BoundedArithmeticLab.BAProofObject
          _root_.BoundedArithmeticLab.PAAxiom :=
      _root_.BoundedArithmeticLab.BAProofObject.mapS21ToPA s21Proof
    have hpaConclusion : paProof.conclusion = target n := by
      change s21Proof.conclusion = target n
      exact hs21Conclusion
    have hpaSize_eq : paProof.size = s21Proof.size := by
      simpa [paProof] using
        (_root_.BoundedArithmeticLab.BAProofObject.size_mapS21ToPA s21Proof)
    exact
      ⟨paProof, hpaConclusion, by
        simpa [hpaSize_eq] using hs21Size⟩

/--
Linear S²₁ trace compiler implies the linear PA trace compiler used by the
canonical route.  The S²₁-to-PA proof-object map preserves size exactly, so the
linear constants are unchanged.
-/
def
    PAHilbertCheckedTraceToBussS21ProofObjectLinearCompiler_to_PACompiler
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (compiler :
      PAHilbertCheckedTraceToBussS21ProofObjectLinearCompiler
        scale_data checker semantics interface target) :
    PAHilbertCheckedTraceToBAProofObjectLinearCompiler
      scale_data checker semantics interface
      _root_.BoundedArithmeticLab.PAAxiom target where
  C := compiler.C
  D := compiler.D
  C_nonneg := compiler.C_nonneg
  D_nonneg := compiler.D_nonneg
  trace_to_baProofObject_linear := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    rcases
        compiler.trace_to_bussS21ProofObject_linear
          n proof trace htraceOf htraceProof htraceCheck hconclusion with
      ⟨s21Proof, hs21Conclusion, hs21Size⟩
    let paProof :
        _root_.BoundedArithmeticLab.BAProofObject
          _root_.BoundedArithmeticLab.PAAxiom :=
      _root_.BoundedArithmeticLab.BAProofObject.mapS21ToPA s21Proof
    have hpaConclusion : paProof.conclusion = target n := by
      change s21Proof.conclusion = target n
      exact hs21Conclusion
    have hpaSize_eq : (paProof.size : Real) = (s21Proof.size : Real) := by
      exact_mod_cast
        (_root_.BoundedArithmeticLab.BAProofObject.size_mapS21ToPA s21Proof)
    exact
      ⟨paProof, hpaConclusion, by
        simpa [hpaSize_eq] using hs21Size⟩

/-- A no-overhead S²₁ compiler is a linear S²₁ compiler with constants
`C = 1`, `D = 0`. -/
def PAHilbertCheckedTraceToBussS21ProofObjectCompiler_to_LinearCompiler
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {interface : PAHilbertCheckerInterface checker semantics}
    {target : Nat → _root_.BoundedArithmeticLab.BAFormula}
    (compiler :
      PAHilbertCheckedTraceToBussS21ProofObjectCompiler
        scale_data checker semantics interface target) :
    PAHilbertCheckedTraceToBussS21ProofObjectLinearCompiler
      scale_data checker semantics interface target where
  C := 1
  D := 0
  C_nonneg := by norm_num
  D_nonneg := by norm_num
  trace_to_bussS21ProofObject_linear := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    rcases
        compiler.trace_to_bussS21ProofObject
          n proof trace htraceOf htraceProof htraceCheck hconclusion with
      ⟨s21Proof, hs21Conclusion, hs21Size⟩
    refine ⟨s21Proof, hs21Conclusion, ?_⟩
    have hsize_real : (s21Proof.size : Real) ≤ (proof.code : Real) := by
      exact_mod_cast hs21Size
    simpa using hsize_real

/--
Operational verifier-trace realization closes the S²₁ trace compiler.  The
actual construction of S²₁ proofs is delegated to the already existing
`ConcreteVerifierTraceSystem.compileTrace`; this theorem only checks that the
PA/Hilbert checked trace is interpreted at the same index and with no larger
numeric size budget.
-/
def
    PAHilbertCheckedTraceConcreteVerifierRealization_to_BussS21Compiler
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    {accepted : Nat → Prop}
    (traceSystem :
      _root_.BoundedArithmeticLab.ConcreteVerifierTraceSystem.{u}
        target accepted)
    (realization :
      PAHilbertCheckedTraceConcreteVerifierRealization
        scale_data checker semantics interface target accepted traceSystem) :
    PAHilbertCheckedTraceToBussS21ProofObjectCompiler
      scale_data checker semantics interface target where
  trace_to_bussS21ProofObject := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    let verifierTrace :=
      realization.toVerifierTrace
        n proof trace htraceOf htraceProof htraceCheck hconclusion
    have hVerifierAccepted :
        traceSystem.traceAccepted verifierTrace :=
      realization.verifierTrace_accepted
        n proof trace htraceOf htraceProof htraceCheck hconclusion
    let s21Proof :=
      traceSystem.compileTrace verifierTrace hVerifierAccepted
    have hindex :
        traceSystem.index verifierTrace = n :=
      realization.verifierTrace_index
        n proof trace htraceOf htraceProof htraceCheck hconclusion
    have hconcl :
        s21Proof.conclusion = target n := by
      have hcompile_conclusion :=
        traceSystem.compile_conclusion verifierTrace hVerifierAccepted
      simpa [s21Proof, hindex] using hcompile_conclusion
    have hcompile_size_real :
        ((s21Proof.size : Nat) : Real) ≤
          traceSystem.trace_size verifierTrace := by
      simpa [s21Proof] using
        traceSystem.compile_size_le_trace_size
          verifierTrace hVerifierAccepted
    have hcompile_size_nat :
        s21Proof.size ≤ traceSystem.trace_size verifierTrace := by
      exact_mod_cast hcompile_size_real
    have htrace_size_nat :
        traceSystem.trace_size verifierTrace ≤ proof.code :=
      realization.verifierTrace_size_le_proof_code
        n proof trace htraceOf htraceProof htraceCheck hconclusion
    exact
      ⟨s21Proof, hconcl,
        Nat.le_trans hcompile_size_nat htrace_size_nat⟩

/--
Linear concrete verifier-trace realization closes the linear S²₁ trace
compiler.  The affine overhead is preserved as-is, so later polynomial
rescaling happens in the existing linear accepted-code bridge rather than by
assuming a no-overhead trace simulation.
-/
def
    PAHilbertCheckedTraceConcreteVerifierLinearRealization_to_BussS21LinearCompiler
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    {accepted : Nat → Prop}
    (traceSystem :
      _root_.BoundedArithmeticLab.ConcreteVerifierTraceSystem.{u}
        target accepted)
    (realization :
      PAHilbertCheckedTraceConcreteVerifierLinearRealization
        scale_data checker semantics interface target accepted traceSystem) :
    PAHilbertCheckedTraceToBussS21ProofObjectLinearCompiler
      scale_data checker semantics interface target where
  C := realization.C
  D := realization.D
  C_nonneg := realization.C_nonneg
  D_nonneg := realization.D_nonneg
  trace_to_bussS21ProofObject_linear := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    let verifierTrace :=
      realization.toVerifierTrace
        n proof trace htraceOf htraceProof htraceCheck hconclusion
    have hVerifierAccepted :
        traceSystem.traceAccepted verifierTrace :=
      realization.verifierTrace_accepted
        n proof trace htraceOf htraceProof htraceCheck hconclusion
    let s21Proof :=
      traceSystem.compileTrace verifierTrace hVerifierAccepted
    have hindex :
        traceSystem.index verifierTrace = n :=
      realization.verifierTrace_index
        n proof trace htraceOf htraceProof htraceCheck hconclusion
    have hconcl :
        s21Proof.conclusion = target n := by
      have hcompile_conclusion :=
        traceSystem.compile_conclusion verifierTrace hVerifierAccepted
      simpa [s21Proof, hindex] using hcompile_conclusion
    have hcompile_size :
        (s21Proof.size : Real) ≤
          (traceSystem.trace_size verifierTrace : Real) := by
      simpa [s21Proof] using
        traceSystem.compile_size_le_trace_size
          verifierTrace hVerifierAccepted
    have htrace_size :
        (traceSystem.trace_size verifierTrace : Real) ≤
          realization.C * (proof.code : Real) + realization.D :=
      realization.verifierTrace_size_le_linear
        n proof trace htraceOf htraceProof htraceCheck hconclusion
    exact
      ⟨s21Proof, hconcl, le_trans hcompile_size htrace_size⟩

/--
A canonical proof-certificate compiler induces the concrete verifier-trace
linear realization for the canonical proof-certificate verifier.  This removes
the last arbitrary `ConcreteVerifierTraceSystem` layer from the implementation
target: it is now enough to build canonical proof certificates from checked
PA/Hilbert traces with linear overhead.
-/
noncomputable def
    PAHilbertCheckedTraceToCanonicalProofCertificateLinearCompiler_to_ConcreteVerifierLinearRealization
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    {bound : Nat → Real}
    (hbound : _root_.BoundedArithmeticLab.IsPolynomialBound bound)
    (compiler :
      PAHilbertCheckedTraceToCanonicalProofCertificateLinearCompiler
        scale_data checker semantics interface bound) :
    PAHilbertCheckedTraceConcreteVerifierLinearRealization
      scale_data checker semantics interface
      _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec.target
      (_root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalProofCertificateAccepted
        bound)
      (_root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalProofCertificateTraceSystem
        hbound) where
  C := compiler.C
  D := compiler.D
  C_nonneg := compiler.C_nonneg
  D_nonneg := compiler.D_nonneg
  toVerifierTrace := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    exact
      ⟨n,
        (compiler.trace_to_certificate
          n proof trace htraceOf htraceProof htraceCheck hconclusion).toAcceptedTrace⟩
  verifierTrace_index := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    rfl
  verifierTrace_accepted := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    trivial
  verifierTrace_size_le_linear := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    simpa [
      _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalProofCertificateTraceSystem,
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalProofCertificateAccepted,
      _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalProofCertificateVerifierMachine,
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.CertificateOperationalS21Compiler.toConcreteTraceSystem]
      using
        compiler.certificate_trace_size_le_linear
          n proof trace htraceOf htraceProof htraceCheck hconclusion

/--
Current-toy obstruction for the canonical proof-certificate compiler.  If a
PA/Hilbert checked trace satisfying the canonical conclusion condition exists,
then such a compiler would produce a canonical finite-consistency proof
certificate, which the current toy Buss-S²₁ proof-object semantics provably
lacks.  This is the audit guard preventing the new endpoint from being
mistaken for a toy-semantics closure.
-/
theorem no_canonicalProofCertificateCompiler_currentToy_of_checkedTrace
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {interface : PAHilbertCheckerInterface checker semantics}
    {bound : Nat → Real}
    (compiler :
      PAHilbertCheckedTraceToCanonicalProofCertificateLinearCompiler
        scale_data checker semantics interface bound)
    {n : Nat} {proof : PAHilbertProofObject}
    {trace : PAHilbertCheckedProofTrace}
    (htraceOf : interface.traceOf proof = some trace)
    (htraceProof : trace.proof = proof)
    (htraceCheck : interface.traceChecker.checkTrace trace = true)
    (hconclusion : proof.conclusion.code = scale_data.powerBoundRawCode n) :
    False :=
  no_currentToyCanonicalProofCertificateAt_finiteConsistency
    (compiler.trace_to_certificate
      n proof trace htraceOf htraceProof htraceCheck hconclusion)

/--
A bound-free accepted-code Buss-S²₁ compiler gives the linear accepted-code BA
proof-object bridge.  The Buss-S²₁ proof object is mapped into the PA
proof-object carrier with no size change.
-/
def
    PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {target : Nat → _root_.BoundedArithmeticLab.BAFormula}
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler
        scale_data checker target) :
    BAProofObjectAcceptedNatCodeLinearBridge
      scale_data checker _root_.BoundedArithmeticLab.PAAxiom target where
  C := compiler.C
  D := compiler.D
  C_nonneg := compiler.C_nonneg
  D_nonneg := compiler.D_nonneg
  accepted_to_baProofObject_linear := by
    intro n code haccepted
    rcases
        compiler.accepted_to_bussS21ProofObject_linear n code haccepted with
      ⟨s21Proof, hs21Conclusion, hs21Size⟩
    let paProof :
        _root_.BoundedArithmeticLab.BAProofObject
          _root_.BoundedArithmeticLab.PAAxiom :=
      _root_.BoundedArithmeticLab.BAProofObject.mapS21ToPA s21Proof
    have hpaConclusion : paProof.conclusion = target n := by
      change s21Proof.conclusion = target n
      exact hs21Conclusion
    have hpaSize_eq : (paProof.size : Real) = (s21Proof.size : Real) := by
      exact_mod_cast
        (_root_.BoundedArithmeticLab.BAProofObject.size_mapS21ToPA
          s21Proof)
    exact ⟨paProof, hpaConclusion, by
      simpa [hpaSize_eq] using hs21Size⟩

/--
Finite-consistency toy obstruction for the bound-free accepted-code compiler.
Even without a certificate bound, the current toy Buss-S²₁ proof-object
semantics cannot produce the required finite-consistency proof object.
-/
theorem no_acceptedNatCodeBussS21Compiler_currentToy_of_acceptedCode
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    {n code : Nat}
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) code) :
    False := by
  rcases
      compiler.accepted_to_bussS21ProofObject_linear n code haccepted with
    ⟨proof, hconclusion, _hsize⟩
  exact
    no_currentToyBussS21ProofObject_finiteConsistencyFormula n
      ⟨proof, hconclusion⟩

/--
Sharper finite-consistency toy obstruction for the direct code-plus-two
accepted-code compiler.  The obstruction is not the size bound: even a
perfect `proof.size <= code + 2` compiler would have to produce a current-toy
Buss-S²₁ proof object of `finiteConsistencyFormula n`, which the present toy
calculus provably lacks.
-/
theorem no_acceptedNatCodeCodePlusTwoCompiler_currentToy_of_acceptedCode
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    {n code : Nat}
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) code) :
    False := by
  rcases
      compiler.accepted_to_bussS21ProofObject_codePlusTwo
        n code haccepted with
    ⟨proof, hconclusion, _hsize⟩
  exact
    no_currentToyBussS21ProofObject_finiteConsistencyFormula n
      ⟨proof, hconclusion⟩

/--
Equivalently, within the current toy proof-object semantics, any direct
code-plus-two compiler would force the accepted-code predicate to be empty on
the entire `powerBoundRawCode` family.  This is an audit theorem, not a desired
mathematical route.
-/
theorem acceptedNatCodeCodePlusTwoCompiler_currentToy_forces_no_acceptedCode
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    (n code : Nat) :
    ¬ PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) code := by
  intro haccepted
  exact
    no_acceptedNatCodeCodePlusTwoCompiler_currentToy_of_acceptedCode
      compiler haccepted

/--
The same obstruction applies to the local accepted-code certificate verifier
compiler, because Lean already proves that such a local compiler induces the
direct code-plus-two compiler.
-/
theorem no_acceptedNatCodeCertificateLocalCompiler_currentToy_of_acceptedCode
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (compiler :
      PAHilbertAcceptedNatCodeCertificateLocalS21Compiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    {n code : Nat}
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) code) :
    False :=
  no_acceptedNatCodeCodePlusTwoCompiler_currentToy_of_acceptedCode
    (PAHilbertAcceptedNatCodeCertificateLocalS21Compiler_to_CodePlusTwoCompiler
      compiler)
    haccepted

/--
Current-toy obstruction for the accepted-code certificate-verifier compiler.
The verifier itself no longer collapses the numeric code size, but a compiler
from its accepted traces to the current toy Buss-S²₁ proof objects would still
produce an impossible proof of `finiteConsistencyFormula n`.
-/
theorem no_acceptedNatCodeCertificateVerifierCompiler_currentToy_of_acceptedCode
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (compiler :
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.CertificateOperationalS21Compiler
        (paHilbertAcceptedNatCodeCertificateVerifierMachine
          scale_data checker)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    {n code : Nat}
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) code) :
    False :=
  no_acceptedNatCodeBussS21Compiler_currentToy_of_acceptedCode
    (PAHilbertAcceptedNatCodeCertificateVerifierCompiler_to_BussS21ProofObjectLinearCompiler
      compiler)
    haccepted

/--
A canonical proof-certificate compiler forgets its verifier-side bound and
yields the bound-free Buss-S²₁ proof-object compiler used by the lower-bound
core.  The certificate bound is therefore not part of the lower-bound
extraction obligation; only the underlying Buss-S²₁ proof object and its
linear size control are retained.
-/
def
    PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler_to_BussS21ProofObjectLinearCompiler
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {bound : Nat → Real}
    (compiler :
      PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler
        scale_data checker bound) :
    PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler
      scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula where
  C := compiler.C
  D := compiler.D
  C_nonneg := compiler.C_nonneg
  D_nonneg := compiler.D_nonneg
  accepted_to_bussS21ProofObject_linear := by
    intro n code haccepted
    let cert := compiler.accepted_to_certificate n code haccepted
    exact
      ⟨cert.proof,
        cert.proof_conclusion_eq_finiteConsistency,
        by
          simpa [cert] using
            compiler.certificate_proof_size_le_linear n code haccepted⟩

/--
An accepted-natural-code canonical certificate compiler is exactly the linear
accepted-code BA proof-object bridge needed by the Pudlak lower-bound transfer.
The compiler produces Buss-S²₁ certificates; `mapS21ToPA` moves them into the
PA proof-object carrier without changing size.
-/
def
    PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {bound : Nat → Real}
    (compiler :
      PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler
        scale_data checker bound) :
    BAProofObjectAcceptedNatCodeLinearBridge
      scale_data checker
      _root_.BoundedArithmeticLab.PAAxiom
      _root_.BoundedArithmeticLab.finiteConsistencyFormula :=
  PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge
    (PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler_to_BussS21ProofObjectLinearCompiler
      compiler)

/--
Current-toy obstruction for the accepted-code canonical certificate compiler.
If any accepted PA/Hilbert numeric code exists at an index, such a compiler
would produce the canonical finite-consistency certificate ruled out by the
toy Buss-S²₁ proof-object semantics.
-/
theorem no_acceptedNatCodeCanonicalProofCertificateCompiler_currentToy_of_acceptedCode
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {bound : Nat → Real}
    (compiler :
      PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler
        scale_data checker bound)
    {n code : Nat}
    (haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) code) :
    False :=
  no_currentToyCanonicalProofCertificateAt_finiteConsistency
    (compiler.accepted_to_certificate n code haccepted)

/--
An operational verifier-machine realization is a concrete verifier-trace
realization for the trace system generated by `OperationalS21Compiler`.
-/
def
    PAHilbertCheckedTraceOperationalVerifierRealization_to_ConcreteVerifierRealization
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (M : _root_.BoundedArithmeticLab.VerifierMachine.{u})
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        M target)
    (realization :
      PAHilbertCheckedTraceOperationalVerifierRealization
        scale_data checker semantics interface target M compiler) :
    PAHilbertCheckedTraceConcreteVerifierRealization
      scale_data checker semantics interface target
      (_root_.BoundedArithmeticLab.VerifierMachine.acceptsInput M)
      compiler.toConcreteTraceSystem where
  toVerifierTrace := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    exact
      ⟨n,
        realization.toAcceptedTrace
          n proof trace htraceOf htraceProof htraceCheck hconclusion⟩
  verifierTrace_index := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    rfl
  verifierTrace_accepted := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    trivial
  verifierTrace_size_le_proof_code := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    exact
      realization.acceptedTrace_size_le_proof_code
        n proof trace htraceOf htraceProof htraceCheck hconclusion

/--
Linear operational verifier-machine realization closes the linear S²₁ trace
compiler.  The constants are exactly the constants supplied by the realization.
-/
def
    PAHilbertCheckedTraceOperationalVerifierLinearRealization_to_BussS21LinearCompiler
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (interface : PAHilbertCheckerInterface checker semantics)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (M : _root_.BoundedArithmeticLab.VerifierMachine.{u})
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        M target)
    (realization :
      PAHilbertCheckedTraceOperationalVerifierLinearRealization
        scale_data checker semantics interface target M compiler) :
    PAHilbertCheckedTraceToBussS21ProofObjectLinearCompiler
      scale_data checker semantics interface target where
  C := realization.C
  D := realization.D
  C_nonneg := realization.C_nonneg
  D_nonneg := realization.D_nonneg
  trace_to_bussS21ProofObject_linear := by
    intro n proof trace htraceOf htraceProof htraceCheck hconclusion
    let acceptedTrace :=
      realization.toAcceptedTrace
        n proof trace htraceOf htraceProof htraceCheck hconclusion
    let s21Proof :=
      compiler.compileTrace n acceptedTrace
    have hconcl :
        s21Proof.conclusion = target n := by
      simpa [s21Proof] using
        compiler.compile_conclusion n acceptedTrace
    have hcompile_size :
        (s21Proof.size : Real) ≤
          (_root_.BoundedArithmeticLab.VerifierMachine.AcceptedTrace.size
            acceptedTrace : Real) := by
      simpa [s21Proof] using
        compiler.compile_size_le_trace_size n acceptedTrace
    have htrace_size :
        (_root_.BoundedArithmeticLab.VerifierMachine.AcceptedTrace.size
          acceptedTrace : Real) ≤
          realization.C * (proof.code : Real) + realization.D :=
      realization.acceptedTrace_size_le_linear
        n proof trace htraceOf htraceProof htraceCheck hconclusion
    exact
      ⟨s21Proof, hconcl, le_trans hcompile_size htrace_size⟩

/--
Opened PA/Hilbert semantic lower-bound bridge.  A BA proof-object lower bound
plus an exact extractor from every accepted PA/Hilbert numeric code to a no
larger BA proof object forces the PA/Hilbert accepted proof-object semantic
minimum to beat every polynomial.

This is the root-free form of the next lower-bound task.  The remaining
content is the real extractor/checker construction, not `tail_gap` or the root
`proof_length`.
-/
theorem
    BAProofObjectStrongSizeLowerBound_and_acceptedNatCodeBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hlower : BAProofObjectStrongSizeLowerBound Ax target)
    (bridge : BAProofObjectAcceptedNatCodeBridge
      scale_data checker Ax target) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n := by
  intro U hU
  refine Filter.frequently_atTop.2 ?_
  intro N
  rcases hlower U hU N with ⟨n, hn_ge, hno_small_ba⟩
  refine ⟨n, hn_ge, ?_⟩
  let sem :=
    paHilbertAcceptedProofObjectCodeSemantics
      scale_data checker completion
  by_contra hnot_gt
  have hmin_le_U :
      ((sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Nat) : Real) ≤
        U n :=
    le_of_not_gt hnot_gt
  rcases
      sem.hasProofCodeOfSize_minProofCodeSize
        (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩ with
    ⟨proof, hchecks, hsize_le_min⟩
  rcases hchecks with ⟨hdecode, hconclusion, haccepts⟩
  have haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) proof.code :=
    ⟨proof, hdecode, hconclusion, haccepts⟩
  rcases bridge.accepted_to_baProofObject n proof.code haccepted with
    ⟨baProof, hba_conclusion, hba_size_le_code⟩
  have hcode_le_min_nat :
      proof.code ≤
        sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ := by
    simpa [sem, paHilbertAcceptedProofObjectCodeSemantics] using
      hsize_le_min
  have hba_size_le_code_real : (baProof.size : Real) ≤ proof.code := by
    exact_mod_cast hba_size_le_code
  have hcode_le_min_real :
      (proof.code : Real) ≤
        (sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) := by
    exact_mod_cast hcode_le_min_nat
  have hba_size_le_U : (baProof.size : Real) ≤ U n :=
    le_trans hba_size_le_code_real
      (le_trans hcode_le_min_real hmin_le_U)
  exact (not_lt_of_ge hba_size_le_U)
    (hno_small_ba baProof hba_conclusion)

/--
Linear-overhead accepted-code extractor version.  If every accepted PA/Hilbert
numeric code extracts a BA proof object of size at most `C * code + D`, then a
BA proof-object lower bound still forces the PA/Hilbert semantic minimum to
beat every polynomial: given a hypothetical polynomial `U` for PA codes, the
BA side is bounded by the polynomial `C * U + D`.
-/
theorem
    BAProofObjectStrongSizeLowerBound_and_acceptedNatCodeLinearBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hlower : BAProofObjectStrongSizeLowerBound Ax target)
    (bridge : BAProofObjectAcceptedNatCodeLinearBridge
      scale_data checker Ax target) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n := by
  intro U hU
  let V : Nat → Real := fun n => bridge.C * U n + bridge.D
  have hV : _root_.is_polynomial_bound V :=
    hU.linear_rescale bridge.C_nonneg bridge.D_nonneg
  refine Filter.frequently_atTop.2 ?_
  intro N
  rcases hlower V hV N with ⟨n, hn_ge, hno_small_ba⟩
  refine ⟨n, hn_ge, ?_⟩
  let sem :=
    paHilbertAcceptedProofObjectCodeSemantics
      scale_data checker completion
  by_contra hnot_gt
  have hmin_le_U :
      ((sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Nat) : Real) ≤
        U n :=
    le_of_not_gt hnot_gt
  rcases
      sem.hasProofCodeOfSize_minProofCodeSize
        (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩ with
    ⟨proof, hchecks, hsize_le_min⟩
  rcases hchecks with ⟨hdecode, hconclusion, haccepts⟩
  have haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        checker (scale_data.powerBoundRawCode n) proof.code :=
    ⟨proof, hdecode, hconclusion, haccepts⟩
  rcases bridge.accepted_to_baProofObject_linear n proof.code haccepted with
    ⟨baProof, hba_conclusion, hba_size_le_linear⟩
  have hcode_le_min_nat :
      proof.code ≤
        sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ := by
    simpa [sem, paHilbertAcceptedProofObjectCodeSemantics] using
      hsize_le_min
  have hcode_le_min_real :
      (proof.code : Real) ≤
        (sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) := by
    exact_mod_cast hcode_le_min_nat
  have hcode_le_U : (proof.code : Real) ≤ U n :=
    le_trans hcode_le_min_real hmin_le_U
  have hlinear_le_V :
      bridge.C * (proof.code : Real) + bridge.D ≤ V n := by
    have hmul :
        bridge.C * (proof.code : Real) ≤ bridge.C * U n :=
      mul_le_mul_of_nonneg_left hcode_le_U bridge.C_nonneg
    dsimp [V]
    linarith
  have hba_size_le_V : (baProof.size : Real) ≤ V n :=
    le_trans hba_size_le_linear hlinear_le_V
  exact (not_lt_of_ge hba_size_le_V)
    (hno_small_ba baProof hba_conclusion)

/--
Specialized source version: once a Buss-Pudlak lower source is calibrated to
the BA semantic minimum and the accepted-code extractor is available, the
PA/Hilbert proof-object semantic lower bound follows.
-/
theorem
    bussPudlakLowerSource_and_acceptedNatCodeBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hoption_length :
      ∀ n k : Nat,
        _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption
            Ax target n =
          some k →
        source.pa_length n = (k : Real))
    (bridge : BAProofObjectAcceptedNatCodeBridge
      scale_data checker Ax target) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n :=
  BAProofObjectStrongSizeLowerBound_and_acceptedNatCodeBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
    Ax target
    (bussPudlakLowerSource_to_BAProofObjectStrongSizeLowerBound
      source Ax target hoption_length)
    bridge

/--
Same source route, but accepting the existing project-style real semantic
length calibration.  The option-minimum calibration is derived, not assumed.
-/
theorem
    bussPudlakLowerSource_semanticLength_and_acceptedNatCodeBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hsemantic_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n)
    (bridge : BAProofObjectAcceptedNatCodeBridge
      scale_data checker Ax target) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n :=
  bussPudlakLowerSource_and_acceptedNatCodeBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
    source Ax target
    (semanticBAProofLength_calibration_to_option_length_calibration
      hsemantic_length)
    bridge

/--
Semantic-length source route with a linear-overhead accepted-code extractor.
-/
theorem
    bussPudlakLowerSource_semanticLength_and_acceptedNatCodeLinearBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hsemantic_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n)
    (bridge : BAProofObjectAcceptedNatCodeLinearBridge
      scale_data checker Ax target) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n :=
  BAProofObjectStrongSizeLowerBound_and_acceptedNatCodeLinearBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
    Ax target
    (bussPudlakLowerSource_to_BAProofObjectStrongSizeLowerBound
      source Ax target
      (semanticBAProofLength_calibration_to_option_length_calibration
        hsemantic_length))
    bridge

/--
End-to-end no-small-code closure for the same opened route.  This is the clean
replacement for a `tail_gap` input, conditional only on the Buss-Pudlak source
calibration and the accepted-code extractor.
-/
theorem
    bussPudlakLowerSource_and_acceptedNatCodeBridge_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hoption_length :
      ∀ n k : Nat,
        _root_.BoundedArithmeticLab.semanticBAMinProofSizeOption
            Ax target n =
          some k →
        source.pa_length n = (k : Real))
    (bridge : BAProofObjectAcceptedNatCodeBridge
      scale_data checker Ax target) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
    (checker := checker)
    (completion := completion)
    (bussPudlakLowerSource_and_acceptedNatCodeBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
      source Ax target hoption_length bridge)

/--
End-to-end no-small-code closure from the real semantic-length calibration.
-/
theorem
    bussPudlakLowerSource_semanticLength_and_acceptedNatCodeBridge_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hsemantic_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n)
    (bridge : BAProofObjectAcceptedNatCodeBridge
      scale_data checker Ax target) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
    (checker := checker)
    (completion := completion)
    (bussPudlakLowerSource_semanticLength_and_acceptedNatCodeBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
      source Ax target hsemantic_length bridge)

/--
End-to-end no-small-code closure from the real semantic-length calibration and
a linear-overhead accepted-code extractor.
-/
theorem
    bussPudlakLowerSource_semanticLength_and_acceptedNatCodeLinearBridge_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hsemantic_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n)
    (bridge : BAProofObjectAcceptedNatCodeLinearBridge
      scale_data checker Ax target) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
    (checker := checker)
    (completion := completion)
    (bussPudlakLowerSource_semanticLength_and_acceptedNatCodeLinearBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
      source Ax target hsemantic_length bridge)

/--
Canonical PA proof-object code-plus-two route to the PA/Hilbert proof-object
semantic lower bound.  This is the weakest accepted-code extractor needed for
the Pudlak lower-bound transfer: accepted PA/Hilbert numeric codes decode to
PA-side BA proof objects, not necessarily to Buss-S²₁ proof objects.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n :=
  bussPudlakLowerSource_semanticLength_and_acceptedNatCodeLinearBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
    source
    _root_.BoundedArithmeticLab.PAAxiom
    _root_.BoundedArithmeticLab.finiteConsistencyFormula
    calibration.length_eq
    (PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge
      compiler)

/--
Literature-input version of the canonical PA proof-object code-plus-two route
to the PA/Hilbert proof-object semantic lower bound.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
      input.source input.calibration compiler

/--
Canonical PA proof-object code-plus-two route to the no-small-code endpoint.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
    (checker := checker)
    (completion := completion)
    (canonicalSourceCalibration_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
      source calibration compiler)

/--
Literature-input version of the PA proof-object code-plus-two no-small-code
endpoint.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
    (checker := checker)
    (completion := completion)
    (canonicalLiteratureInput_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
      compiler)

/--
Canonical bound-free Buss-S²₁ compiler route to the PA/Hilbert proof-object
semantic lower bound.  This is the direct Lean form of the short paper
contradiction: a polynomially small accepted PA/Hilbert numeric code would
compile to a polynomially small BA proof object, contradicting the calibrated
Buss-Pudlak proof-object lower bound.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n :=
  bussPudlakLowerSource_semanticLength_and_acceptedNatCodeLinearBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
    source
    _root_.BoundedArithmeticLab.PAAxiom
    _root_.BoundedArithmeticLab.finiteConsistencyFormula
    calibration.length_eq
    (PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge
      compiler)

/--
Literature-input version of the canonical bound-free Buss-S²₁ compiler route
to the PA/Hilbert proof-object semantic lower bound.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
      input.source input.calibration compiler

/--
Direct code-plus-two accepted-code compiler route to the PA/Hilbert
proof-object semantic lower bound.  It is the sharp specialization of the
bound-free linear Buss-S²₁ compiler endpoint with constants `1, 2`.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n :=
  canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    source calibration
    (PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler_to_LinearCompiler
      compiler)

/--
Literature-input version of the direct code-plus-two accepted-code compiler
route to the PA/Hilbert proof-object semantic lower bound.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n :=
  canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    (PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler_to_LinearCompiler
      compiler)

/--
Canonical certificate compiler route to the PA/Hilbert proof-object semantic
lower bound.  The certificate bound is forgotten first, so this endpoint has
the same lower-bound core as the bound-free Buss-S²₁ compiler route.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    {bound : Nat → Real}
    (compiler :
      PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler
        scale_data checker bound) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n :=
  canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    source calibration
    (PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler_to_BussS21ProofObjectLinearCompiler
      compiler)

/--
Literature-input version of the canonical certificate compiler route to the
PA/Hilbert proof-object semantic lower bound.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    {bound : Nat → Real}
    (compiler :
      PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler
        scale_data checker bound) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n :=
  canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    (PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler_to_BussS21ProofObjectLinearCompiler
      compiler)

/--
Local accepted-code certificate-verifier compiler route to the PA/Hilbert
proof-object semantic lower bound.  This is the exact non-collapsing verifier
version of the lower-bound core: the verifier trace charges the carried
numeric proof code before the S²₁ compiler is applied, and no global
`trace_bound n` over all certificates is required.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertAcceptedNatCodeCertificateLocalS21Compiler
        scale_data checker
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n :=
  canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    source calibration
    (PAHilbertAcceptedNatCodeCertificateLocalS21Compiler_to_BussS21ProofObjectLinearCompiler
      compiler)

/--
Literature-input version of the local accepted-code certificate-verifier
compiler route to the PA/Hilbert proof-object semantic lower bound.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeCertificateLocalCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      PAHilbertAcceptedNatCodeCertificateLocalS21Compiler
        scale_data checker
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n :=
  canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    (PAHilbertAcceptedNatCodeCertificateLocalS21Compiler_to_BussS21ProofObjectLinearCompiler
      compiler)

/--
Compatibility route from the older global certificate operational compiler to
the local accepted-code certificate-verifier semantic lower-bound endpoint.
The global `trace_bound` fields are not used by the lower-bound transfer.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeCertificateVerifierCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.CertificateOperationalS21Compiler
        (paHilbertAcceptedNatCodeCertificateVerifierMachine
          scale_data checker)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n :=
  canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    source calibration
    (PAHilbertAcceptedNatCodeCertificateOperationalCompiler_to_LocalS21Compiler
      compiler)

/--
Literature-input compatibility route from the older global certificate
operational compiler to the local accepted-code certificate-verifier semantic
lower-bound endpoint.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeCertificateVerifierCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.CertificateOperationalS21Compiler
        (paHilbertAcceptedNatCodeCertificateVerifierMachine
          scale_data checker)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ∀ U : Nat → Real, _root_.is_polynomial_bound U →
      ∃ᶠ n in Filter.atTop,
        ((paHilbertAcceptedProofObjectCodeSemantics
            scale_data checker completion).minProofCodeSize
              (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n :=
  canonicalLiteratureInput_and_acceptedNatCodeCertificateLocalCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
    (PAHilbertAcceptedNatCodeCertificateOperationalCompiler_to_LocalS21Compiler
      compiler)

/--
Bound-free accepted-code Buss-S²₁ compiler version of the canonical
finite-consistency endpoint.  This is the lower-bound-side extractor stripped
of the certificate-acceptance bound: it only needs the accepted numeric code to
produce a Buss-S²₁ proof object of `finiteConsistencyFormula n` with linear
overhead.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
    (checker := checker)
    (completion := completion)
    (canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
      source calibration compiler)

/--
Literature-input version of the bound-free accepted-code Buss-S²₁ compiler
endpoint.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics := by
  exact
    paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
      (checker := checker)
      (completion := completion)
    (canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
        compiler)

/--
Direct code-plus-two accepted-code compiler version of the canonical
finite-consistency no-small endpoint.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeCodePlusTwoCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
    (checker := checker)
    (completion := completion)
    (canonicalSourceCalibration_and_acceptedNatCodeCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
      source calibration compiler)

/--
Literature-input version of the direct code-plus-two accepted-code compiler
no-small endpoint.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeCodePlusTwoCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
    (checker := checker)
    (completion := completion)
    (canonicalLiteratureInput_and_acceptedNatCodeCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
      compiler)

/--
Local accepted-code certificate-verifier compiler version of the canonical
finite-consistency no-small endpoint.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertAcceptedNatCodeCertificateLocalS21Compiler
        scale_data checker
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
    (checker := checker)
    (completion := completion)
    (canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
      source calibration compiler)

/--
Literature-input version of the local accepted-code certificate-verifier
compiler no-small endpoint.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeCertificateLocalCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      PAHilbertAcceptedNatCodeCertificateLocalS21Compiler
        scale_data checker
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
    (checker := checker)
    (completion := completion)
    (canonicalLiteratureInput_and_acceptedNatCodeCertificateLocalCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
      compiler)

/--
Compatibility wrapper from the older global certificate operational compiler
to the local accepted-code certificate-verifier no-small endpoint.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeCertificateVerifierCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.CertificateOperationalS21Compiler
        (paHilbertAcceptedNatCodeCertificateVerifierMachine
          scale_data checker)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_noSmallProofCodes
    source calibration
    (PAHilbertAcceptedNatCodeCertificateOperationalCompiler_to_LocalS21Compiler
      compiler)

/--
Literature-input compatibility wrapper from the older global certificate
operational compiler to the local accepted-code certificate-verifier no-small
endpoint.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeCertificateVerifierCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.CertificateOperationalS21Compiler
        (paHilbertAcceptedNatCodeCertificateVerifierMachine
          scale_data checker)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalLiteratureInput_and_acceptedNatCodeCertificateLocalCompiler_to_noSmallProofCodes
    (PAHilbertAcceptedNatCodeCertificateOperationalCompiler_to_LocalS21Compiler
      compiler)

/--
Accepted-natural-code canonical certificate compiler version of the canonical
finite-consistency endpoint.  This avoids the impossible unrestricted
`traceOf` interface entirely: the implementation obligation is directly on
accepted numeric PA/Hilbert proof codes, the objects actually searched by the
finite enumeration.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    {bound : Nat → Real}
    (compiler :
      PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler
        scale_data checker bound) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_noSmallProofCodes
    source calibration
    (PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler_to_BussS21ProofObjectLinearCompiler
      compiler)

/--
Literature-input version of the accepted-code canonical certificate endpoint.
Only the named Buss-Pudlak source/calibration input and the concrete
accepted-code certificate compiler remain visible.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    {bound : Nat → Real}
    (compiler :
      PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler
        scale_data checker bound) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_noSmallProofCodes
      (PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler_to_BussS21ProofObjectLinearCompiler
        compiler)

/--
Trace-compiler version of the opened PA/Hilbert semantic lower-bound route.
The accepted-code extractor is no longer an input; it is produced from the
checker interface and the checked-trace-to-BA compiler.
-/
theorem
    bussPudlakLowerSource_semanticLength_and_traceCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hsemantic_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n)
    (compiler :
      PAHilbertCheckedTraceToBAProofObjectCompiler
        scale_data checker semantics interface Ax target) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  bussPudlakLowerSource_semanticLength_and_acceptedNatCodeBridge_to_noSmallProofCodes
    source Ax target hsemantic_length
    (PAHilbertCheckedTraceToBAProofObjectCompiler_to_BAProofObjectAcceptedNatCodeBridge
      interface Ax target compiler)

/--
Trace-compiler version with linear overhead.  This is the robust endpoint for
real checker traces and machine simulations.
-/
theorem
    bussPudlakLowerSource_semanticLength_and_traceLinearCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hsemantic_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n)
    (compiler :
      PAHilbertCheckedTraceToBAProofObjectLinearCompiler
        scale_data checker semantics interface Ax target) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  bussPudlakLowerSource_semanticLength_and_acceptedNatCodeLinearBridge_to_noSmallProofCodes
    source Ax target hsemantic_length
    (PAHilbertCheckedTraceToBAProofObjectLinearCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge
      interface Ax target compiler)

/--
Canonical finite-consistency endpoint without invoking the named literature
axiom.  If a source and its canonical relabeled semantic calibration are
provided by an internal proof, this theorem closes the lower-bound route
directly.
-/
theorem
    canonicalSourceCalibration_and_traceCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertCheckedTraceToBAProofObjectCompiler
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  bussPudlakLowerSource_semanticLength_and_traceCompiler_to_noSmallProofCodes
    interface
    source
    _root_.BoundedArithmeticLab.PAAxiom
    _root_.BoundedArithmeticLab.finiteConsistencyFormula
    calibration.length_eq
    compiler

/--
Canonical finite-consistency endpoint with a linear-overhead trace compiler.
This is the preferred robust form for real machine/checker implementations.
-/
theorem
    canonicalSourceCalibration_and_traceLinearCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertCheckedTraceToBAProofObjectLinearCompiler
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  bussPudlakLowerSource_semanticLength_and_traceLinearCompiler_to_noSmallProofCodes
    interface
    source
    _root_.BoundedArithmeticLab.PAAxiom
    _root_.BoundedArithmeticLab.finiteConsistencyFormula
    calibration.length_eq
    compiler

/--
Application of the explicit literature input to the current canonical
finite-consistency target.  The only remaining non-literature input is the
checked-trace compiler from accepted PA/Hilbert traces to BA proof objects.
-/
theorem
    canonicalLiteratureInput_and_traceCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (compiler :
      PAHilbertCheckedTraceToBAProofObjectCompiler
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_traceCompiler_to_noSmallProofCodes
      interface
      input.source
      input.calibration
      compiler

/--
Source-and-calibration version with the extractor lowered to S²₁.  This is the
preferred target once the Buss-Pudlak source and calibration are proved
internally: no named literature axiom is used by this theorem.
-/
theorem
    canonicalSourceCalibration_and_s21TraceCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertCheckedTraceToBussS21ProofObjectCompiler
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalSourceCalibration_and_traceCompiler_to_noSmallProofCodes
    interface source calibration
    (PAHilbertCheckedTraceToBussS21ProofObjectCompiler_to_PACompiler
      interface
      _root_.BoundedArithmeticLab.finiteConsistencyFormula
      compiler)

/--
Source-and-calibration version with the extractor lowered to a linear-overhead
S²₁ trace compiler.
-/
theorem
    canonicalSourceCalibration_and_s21TraceLinearCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertCheckedTraceToBussS21ProofObjectLinearCompiler
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalSourceCalibration_and_traceLinearCompiler_to_noSmallProofCodes
    interface source calibration
    (PAHilbertCheckedTraceToBussS21ProofObjectLinearCompiler_to_PACompiler
      interface
      _root_.BoundedArithmeticLab.finiteConsistencyFormula
      compiler)

/--
Canonical endpoint with the extractor lowered to S²₁.  This is stronger as an
audit boundary than asking for a PA proof-object compiler directly: the
remaining concrete compiler only has to build a Buss-S²₁ proof object from the
checked PA/Hilbert trace, and the already formalized `S²₁ ⊆ PA` map handles the
PA transport without increasing size.
-/
theorem
    canonicalLiteratureInput_and_s21TraceCompiler_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (compiler :
      PAHilbertCheckedTraceToBussS21ProofObjectCompiler
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalLiteratureInput_and_traceCompiler_to_noSmallProofCodes
    interface
    (PAHilbertCheckedTraceToBussS21ProofObjectCompiler_to_PACompiler
      interface
      _root_.BoundedArithmeticLab.finiteConsistencyFormula
      compiler)

/--
Source-and-calibration version with the extractor lowered to concrete verifier
traces.  This exposes the two independent remaining mathematical obligations:
the Buss-Pudlak source/calibration, and the PA checked-trace realization.
-/
theorem
    canonicalSourceCalibration_and_concreteVerifierTraceRealization_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    {accepted : Nat → Prop}
    (traceSystem :
      _root_.BoundedArithmeticLab.ConcreteVerifierTraceSystem.{u}
        _root_.BoundedArithmeticLab.finiteConsistencyFormula accepted)
    (realization :
      PAHilbertCheckedTraceConcreteVerifierRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        accepted traceSystem) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalSourceCalibration_and_s21TraceCompiler_to_noSmallProofCodes
    interface source calibration
    (PAHilbertCheckedTraceConcreteVerifierRealization_to_BussS21Compiler
      interface
      _root_.BoundedArithmeticLab.finiteConsistencyFormula
      traceSystem
      realization)

/--
Source-and-calibration version with the extractor lowered to concrete verifier
traces and only a linear overhead requirement.  This is the implementation
shape expected from a real checker/verifier simulation.
-/
theorem
    canonicalSourceCalibration_and_concreteVerifierTraceLinearRealization_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    {accepted : Nat → Prop}
    (traceSystem :
      _root_.BoundedArithmeticLab.ConcreteVerifierTraceSystem.{u}
        _root_.BoundedArithmeticLab.finiteConsistencyFormula accepted)
    (realization :
      PAHilbertCheckedTraceConcreteVerifierLinearRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        accepted traceSystem) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalSourceCalibration_and_s21TraceLinearCompiler_to_noSmallProofCodes
    interface source calibration
    (PAHilbertCheckedTraceConcreteVerifierLinearRealization_to_BussS21LinearCompiler
      interface
      _root_.BoundedArithmeticLab.finiteConsistencyFormula
      traceSystem
      realization)

/--
Source-and-calibration endpoint with the extractor lowered to an operational
verifier machine plus its S²₁ compiler.
-/
theorem
    canonicalSourceCalibration_and_operationalVerifierRealization_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (M : _root_.BoundedArithmeticLab.VerifierMachine.{u})
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        M _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    (realization :
      PAHilbertCheckedTraceOperationalVerifierRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        M compiler) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalSourceCalibration_and_concreteVerifierTraceRealization_to_noSmallProofCodes
    interface source calibration
    compiler.toConcreteTraceSystem
    (PAHilbertCheckedTraceOperationalVerifierRealization_to_ConcreteVerifierRealization
      interface
      _root_.BoundedArithmeticLab.finiteConsistencyFormula
      M compiler realization)

/--
Source-and-calibration endpoint with a linear-overhead operational verifier
realization.  This form allows accepted verifier runs to have linear overhead
over the original PA/Hilbert numeric proof code.
-/
theorem
    canonicalSourceCalibration_and_operationalVerifierLinearRealization_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (M : _root_.BoundedArithmeticLab.VerifierMachine.{u})
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        M _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    (realization :
      PAHilbertCheckedTraceOperationalVerifierLinearRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        M compiler) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalSourceCalibration_and_s21TraceLinearCompiler_to_noSmallProofCodes
    interface source calibration
    (PAHilbertCheckedTraceOperationalVerifierLinearRealization_to_BussS21LinearCompiler
      interface
      _root_.BoundedArithmeticLab.finiteConsistencyFormula
      M compiler realization)

/--
Canonical endpoint with the extractor lowered to an operational verifier-trace
realization.  The remaining non-literature input is now the concrete
interpretation of PA/Hilbert checked traces as traces of a verifier system
whose compiler already emits Buss-S²₁ proof objects.
-/
theorem
    canonicalLiteratureInput_and_concreteVerifierTraceRealization_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    {accepted : Nat → Prop}
    (traceSystem :
      _root_.BoundedArithmeticLab.ConcreteVerifierTraceSystem.{u}
        _root_.BoundedArithmeticLab.finiteConsistencyFormula accepted)
    (realization :
      PAHilbertCheckedTraceConcreteVerifierRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        accepted traceSystem) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalLiteratureInput_and_s21TraceCompiler_to_noSmallProofCodes
    interface
    (PAHilbertCheckedTraceConcreteVerifierRealization_to_BussS21Compiler
      interface
      _root_.BoundedArithmeticLab.finiteConsistencyFormula
      traceSystem
      realization)

/--
Literature-input endpoint with the extractor lowered to concrete verifier
traces and a linear overhead bound.
-/
theorem
    canonicalLiteratureInput_and_concreteVerifierTraceLinearRealization_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    {accepted : Nat → Prop}
    (traceSystem :
      _root_.BoundedArithmeticLab.ConcreteVerifierTraceSystem.{u}
        _root_.BoundedArithmeticLab.finiteConsistencyFormula accepted)
    (realization :
      PAHilbertCheckedTraceConcreteVerifierLinearRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        accepted traceSystem) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_concreteVerifierTraceLinearRealization_to_noSmallProofCodes
      interface
      input.source
      input.calibration
      traceSystem
      realization

/--
Current literature-input endpoint with the extractor lowered to an operational
verifier machine.
-/
theorem
    canonicalLiteratureInput_and_operationalVerifierRealization_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (M : _root_.BoundedArithmeticLab.VerifierMachine.{u})
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        M _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    (realization :
      PAHilbertCheckedTraceOperationalVerifierRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        M compiler) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_operationalVerifierRealization_to_noSmallProofCodes
      interface
      input.source
      input.calibration
      M compiler realization

/--
Current literature-input endpoint with a linear-overhead operational verifier
realization.
-/
theorem
    canonicalLiteratureInput_and_operationalVerifierLinearRealization_to_noSmallProofCodes
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (M : _root_.BoundedArithmeticLab.VerifierMachine.{u})
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        M _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    (realization :
      PAHilbertCheckedTraceOperationalVerifierLinearRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        M compiler) :
    InternalPudlakTheorem5NoSmallProofCodes scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_operationalVerifierLinearRealization_to_noSmallProofCodes
      interface
      input.source
      input.calibration
      M compiler realization

/--
Growth-obligation endpoint for the source/calibration trace-compiler route.
This is the same theorem as the no-small-code endpoint, stated in the exact
`ShortestCheckedMinProofCodeGrowthObligation` form used by the short proof
guide.  It avoids `tail_gap` and root `proof_length`; the remaining inputs are
the Buss-Pudlak source/calibration and the accepted-trace-to-BA compiler.
-/
theorem
    canonicalSourceCalibration_and_traceCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertCheckedTraceToBAProofObjectCompiler
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
    (canonicalSourceCalibration_and_traceCompiler_to_noSmallProofCodes
      interface source calibration compiler)

/--
Linear trace-compiler version of the shortest checked-minimum growth endpoint.
The polynomial rescaling is handled inside the accepted-code linear bridge, so
the conclusion is still the native minimum accepted PA/Hilbert numeric code
growth statement.
-/
theorem
    canonicalSourceCalibration_and_traceLinearCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertCheckedTraceToBAProofObjectLinearCompiler
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
    (canonicalSourceCalibration_and_traceLinearCompiler_to_noSmallProofCodes
      interface source calibration compiler)

/--
Concrete verifier-trace version of the shortest checked-minimum growth
endpoint with only linear overhead.  This is the verifier-system analogue of
the linear trace-compiler endpoint.
-/
theorem
    canonicalSourceCalibration_and_concreteVerifierTraceLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    {accepted : Nat → Prop}
    (traceSystem :
      _root_.BoundedArithmeticLab.ConcreteVerifierTraceSystem.{u}
        _root_.BoundedArithmeticLab.finiteConsistencyFormula accepted)
    (realization :
      PAHilbertCheckedTraceConcreteVerifierLinearRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        accepted traceSystem) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
    (canonicalSourceCalibration_and_concreteVerifierTraceLinearRealization_to_noSmallProofCodes
      interface source calibration traceSystem realization)

/--
Operational verifier-machine version of the shortest checked-minimum growth
endpoint.  This is the preferred implementation-facing statement: once the
canonical Buss-Pudlak source/calibration and the concrete operational verifier
linear realization are supplied, Lean returns the exact checked-min growth
obligation needed by the lower-bound side.
-/
theorem
    canonicalSourceCalibration_and_operationalVerifierLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (M : _root_.BoundedArithmeticLab.VerifierMachine.{u})
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        M _root_.BoundedArithmeticLab.finiteConsistencyFormula)
    (realization :
      PAHilbertCheckedTraceOperationalVerifierLinearRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        M compiler) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
    (canonicalSourceCalibration_and_operationalVerifierLinearRealization_to_noSmallProofCodes
      interface source calibration M compiler realization)

/--
Specialized checked-trace verifier endpoint.  The operational realization is
now fixed to the explicit one-step proof-carrying PA/Hilbert checked-trace
verifier.  The remaining implementation obligation is only the
`OperationalS21Compiler` for that verifier machine and the canonical
finite-consistency target.

This removes one more black-box layer from the shortest checked-minimum growth
route: the theorem no longer asks for an arbitrary operational linear
realization.
-/
theorem
    canonicalSourceCalibration_and_checkedTraceVerifierCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        (paHilbertCheckedTraceVerifierMachine
          scale_data checker semantics interface)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalSourceCalibration_and_operationalVerifierLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation
    (scale_data := scale_data)
    (checker := checker)
    (semantics := semantics)
    (completion := completion)
    interface source calibration
    (paHilbertCheckedTraceVerifierMachine
      scale_data checker semantics interface)
    compiler
    (paHilbertCheckedTraceVerifierLinearRealization
      interface
      _root_.BoundedArithmeticLab.finiteConsistencyFormula
      compiler)

/--
Literature-input version of the specialized checked-trace verifier endpoint.
This is useful as an audit boundary: after accepting the named external
Buss-Pudlak source/calibration input, the only remaining non-kernel datum is
the `OperationalS21Compiler` for the explicit one-step checked-trace verifier.
-/
theorem
    canonicalLiteratureInput_and_checkedTraceVerifierCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (compiler :
      _root_.BoundedArithmeticLab.VerifierMachine.OperationalS21Compiler
        (paHilbertCheckedTraceVerifierMachine
          scale_data checker semantics interface)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_checkedTraceVerifierCompiler_to_shortestCheckedMinProofCodeGrowthObligation
      interface input.source input.calibration compiler

/--
Certificate-verifier specialization of the shortest checked-minimum growth
endpoint.  This keeps the non-collapsing proof-certificate carrier fixed:
accepted verifier traces are traces of
`canonicalProofCertificateVerifierMachine bound`, whose size contains the
carried certificate size.

The remaining implementation obligation is the PA/Hilbert checked-trace
realization into that concrete proof-certificate trace system, with trace size
bounded by the original numeric PA/Hilbert proof code.
-/
theorem
    canonicalSourceCalibration_and_proofCertificateVerifierRealization_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    {bound : Nat → Real}
    (hbound : _root_.BoundedArithmeticLab.IsPolynomialBound bound)
    (realization :
      PAHilbertCheckedTraceConcreteVerifierRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        (_root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalProofCertificateAccepted
          bound)
        (by
          simpa [
            _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec,
            _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalFiniteConsistencyGenerator]
            using
              (_root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalProofCertificateTraceSystem
                (bound := bound) hbound))) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
    (canonicalSourceCalibration_and_concreteVerifierTraceRealization_to_noSmallProofCodes
      interface source calibration
      (by
        simpa [
          _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec,
          _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalFiniteConsistencyGenerator]
          using
            (_root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalProofCertificateTraceSystem
              (bound := bound) hbound))
      realization)

/--
Linear certificate-verifier specialization of the shortest checked-minimum
growth endpoint.  This is the realistic implementation target for the
canonical proof-certificate verifier: the accepted verifier trace may have
fixed linear overhead over the PA/Hilbert numeric proof code.
-/
theorem
    canonicalSourceCalibration_and_proofCertificateVerifierLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    {bound : Nat → Real}
    (hbound : _root_.BoundedArithmeticLab.IsPolynomialBound bound)
    (realization :
      PAHilbertCheckedTraceConcreteVerifierLinearRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        (_root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalProofCertificateAccepted
          bound)
        (by
          simpa [
            _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec,
            _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalFiniteConsistencyGenerator]
            using
              (_root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalProofCertificateTraceSystem
                (bound := bound) hbound))) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalSourceCalibration_and_concreteVerifierTraceLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation
    interface source calibration
    (by
      simpa [
        _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec,
        _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalFiniteConsistencyGenerator]
        using
          (_root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalProofCertificateTraceSystem
            (bound := bound) hbound))
    realization

/--
Canonical proof-certificate compiler endpoint for the source/calibration route.
This is the sharpened implementation target: the arbitrary concrete verifier
realization has been replaced by a compiler that directly constructs the
canonical Cn-box proof certificate consumed by the non-collapsing certificate
verifier.
-/
theorem
    canonicalSourceCalibration_and_canonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    {bound : Nat → Real}
    (hbound : _root_.BoundedArithmeticLab.IsPolynomialBound bound)
    (compiler :
      PAHilbertCheckedTraceToCanonicalProofCertificateLinearCompiler
        scale_data checker semantics interface bound) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalSourceCalibration_and_concreteVerifierTraceLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation
    interface source calibration
    (by
      simpa [
        _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec,
        _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalFiniteConsistencyGenerator]
        using
          (_root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalProofCertificateTraceSystem
            (bound := bound) hbound))
    (by
      simpa [
        _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec,
        _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalFiniteConsistencyGenerator]
        using
          (PAHilbertCheckedTraceToCanonicalProofCertificateLinearCompiler_to_ConcreteVerifierLinearRealization
            interface hbound compiler))

/--
Accepted-natural-code canonical certificate compiler endpoint for the
source/calibration route.  This is the current preferred implementation-facing
statement because it works directly with the numeric proof codes searched by
the finite lower-bound side and does not require the uninhabitable full
`traceOf` checker interface.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    {bound : Nat → Real}
    (compiler :
      PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler
        scale_data checker bound) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
    (canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_noSmallProofCodes
      source calibration
      (PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler_to_BussS21ProofObjectLinearCompiler
        compiler))

/--
Direct PA proof-object code-plus-two endpoint for the exact shortest checked
minimum growth statement.  This is the minimal accepted-code extractor route:
no Buss-S²₁ proof object is required at this stage.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
    (canonicalSourceCalibration_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_noSmallProofCodes
      source calibration compiler)

/--
Literature-input version of the direct PA proof-object code-plus-two
shortest-growth endpoint.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation
      input.source input.calibration compiler

/--
Bound-free accepted-code Buss-S²₁ compiler endpoint for the exact shortest
checked-minimum growth statement.  This is the cleanest lower-bound-side target:
no certificate bound, no verifier trace, and no full `traceOf` interface are
part of the statement.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
    (canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_noSmallProofCodes
      source calibration compiler)

/--
Direct code-plus-two accepted-code compiler endpoint for the exact shortest
checked-minimum growth statement.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
    (canonicalSourceCalibration_and_acceptedNatCodeCodePlusTwoCompiler_to_noSmallProofCodes
      source calibration compiler)

/--
Literature-input version of the direct code-plus-two accepted-code compiler
shortest-growth endpoint.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_acceptedNatCodeCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation
      input.source input.calibration compiler

/--
Local accepted-code certificate-verifier compiler endpoint for shortest checked
minimum growth.  This is the full non-collapsing verifier route from native
accepted proof codes to the lower-bound conclusion, without a global
`trace_bound n` premise.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      PAHilbertAcceptedNatCodeCertificateLocalS21Compiler
        scale_data checker
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
    (canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_noSmallProofCodes
      source calibration compiler)

/--
Compatibility wrapper from the older global certificate operational compiler
to the local accepted-code certificate-verifier shortest-growth endpoint.
-/
theorem
    canonicalSourceCalibration_and_acceptedNatCodeCertificateVerifierCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (calibration :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalRelabeledPudlakCalibration
        source)
    (compiler :
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.CertificateOperationalS21Compiler
        (paHilbertAcceptedNatCodeCertificateVerifierMachine
          scale_data checker)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    source calibration
    (PAHilbertAcceptedNatCodeCertificateOperationalCompiler_to_LocalS21Compiler
      compiler)

/--
Literature-input version of the proof-certificate verifier endpoint.  This is
the current cleanest implementation-facing lower-bound target: after the named
Buss-Pudlak literature input, the remaining construction is a real PA/Hilbert
checked-trace realization into the non-collapsing canonical proof-certificate
verifier.
-/
theorem
    canonicalLiteratureInput_and_proofCertificateVerifierRealization_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    {bound : Nat → Real}
    (hbound : _root_.BoundedArithmeticLab.IsPolynomialBound bound)
    (realization :
      PAHilbertCheckedTraceConcreteVerifierRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        (_root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalProofCertificateAccepted
          bound)
        (by
          simpa [
            _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec,
            _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalFiniteConsistencyGenerator]
            using
              (_root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalProofCertificateTraceSystem
                (bound := bound) hbound))) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_proofCertificateVerifierRealization_to_shortestCheckedMinProofCodeGrowthObligation
      interface input.source input.calibration hbound realization

/--
Literature-input version of the linear proof-certificate verifier endpoint.
After the named Buss-Pudlak source/calibration input, the only remaining
construction is a real linear PA/Hilbert checked-trace realization into the
canonical proof-certificate verifier.
-/
theorem
    canonicalLiteratureInput_and_proofCertificateVerifierLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    {bound : Nat → Real}
    (hbound : _root_.BoundedArithmeticLab.IsPolynomialBound bound)
    (realization :
      PAHilbertCheckedTraceConcreteVerifierLinearRealization
        scale_data checker semantics interface
        _root_.BoundedArithmeticLab.finiteConsistencyFormula
        (_root_.BoundedArithmeticLab.BoundedProofPredicate.CanonicalProofCertificateAccepted
          bound)
        (by
          simpa [
            _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalPudlakTargetFamilySpec,
            _root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalFiniteConsistencyGenerator]
            using
              (_root_.BoundedArithmeticLab.BoundedProofPredicate.canonicalProofCertificateTraceSystem
                (bound := bound) hbound))) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_proofCertificateVerifierLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation
      interface input.source input.calibration hbound realization

/--
Literature-input version of the canonical proof-certificate compiler endpoint.
This leaves exactly two non-kernel obligations visible: the named
Buss-Pudlak source/calibration input and the concrete compiler from checked
PA/Hilbert traces to canonical proof certificates.
-/
theorem
    canonicalLiteratureInput_and_canonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (interface : PAHilbertCheckerInterface checker semantics)
    {bound : Nat → Real}
    (hbound : _root_.BoundedArithmeticLab.IsPolynomialBound bound)
    (compiler :
      PAHilbertCheckedTraceToCanonicalProofCertificateLinearCompiler
        scale_data checker semantics interface bound) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_canonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation
      interface input.source input.calibration hbound compiler

/--
Literature-input version of the accepted-code canonical certificate compiler
endpoint.  After the named Buss-Pudlak input, the remaining construction is
exactly the accepted-code-to-canonical-certificate compiler.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    {bound : Nat → Real}
    (compiler :
      PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler
        scale_data checker bound) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation
      input.source input.calibration compiler

/--
Literature-input version of the bound-free accepted-code Buss-S²₁ compiler
shortest-growth endpoint.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler
        scale_data checker _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_shortestCheckedMinProofCodeGrowthObligation
      input.source input.calibration compiler

/--
Literature-input version of the local accepted-code certificate-verifier
compiler shortest-growth endpoint.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeCertificateLocalCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      PAHilbertAcceptedNatCodeCertificateLocalS21Compiler
        scale_data checker
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics := by
  let input :=
    bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
  exact
    canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_shortestCheckedMinProofCodeGrowthObligation
      input.source input.calibration compiler

/--
Literature-input compatibility wrapper from the older global certificate
operational compiler to the local accepted-code certificate-verifier
shortest-growth endpoint.
-/
theorem
    canonicalLiteratureInput_and_acceptedNatCodeCertificateVerifierCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (compiler :
      _root_.BoundedArithmeticLab.CertificateVerifierMachine.CertificateOperationalS21Compiler
        (paHilbertAcceptedNatCodeCertificateVerifierMachine
          scale_data checker)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  canonicalLiteratureInput_and_acceptedNatCodeCertificateLocalCompiler_to_shortestCheckedMinProofCodeGrowthObligation
    (PAHilbertAcceptedNatCodeCertificateOperationalCompiler_to_LocalS21Compiler
      compiler)

/--
Reverse exactness bridge from structured BA proof objects to accepted
PA/Hilbert numeric proof codes.  This is the semantic encoder obligation
needed to pull a numeric-code no-small theorem back to the proof-object layer:
every BA proof object of `target n` must encode as an accepted natural proof
code for `powerBoundRawCode n`, with numeric code no larger than the proof
object size.
-/
structure BAProofObjectToAcceptedNatCodeBridge
    (scale_data : InternalPudlakTheorem5ScaleData)
    (checker : PAHilbertChecker)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula) :
    Type 1 where
  baProofObject_to_accepted_code :
    ∀ n : Nat, ∀ proof : _root_.BoundedArithmeticLab.BAProofObject Ax,
      proof.conclusion = target n →
        ∃ code : Nat,
          code ≤ proof.size ∧
            PAHilbertAcceptedProofCodeForFormulaCode
              checker (scale_data.powerBoundRawCode n) code

/--
Once the BA proof-object route supplies `NoAcceptedBelowCutoff`, the exact
accepted-code bridge above turns it into the PA/Hilbert numeric-code rejection
data.  This is the precise natural-code version of the lower-bound target:
small accepted nat codes are ruled out by extracting smaller BA proof objects.
-/
def baProofObjectNoAcceptedBelow_toPAHilbertAcceptedNatCodeRejectionData
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (opened :
      ComputableNoAcceptedBelowCutoff scale_data
        (baProofObjectRootCodeSemantics
          Ax target scale_data.powerBoundRawCode hcomplete))
    (bridge :
      BAProofObjectAcceptedNatCodeBridge scale_data checker Ax target) :
    PAHilbertAcceptedNatCodeRejectionExtractorData scale_data checker where
  witness := opened.witness
  cutoff := opened.cutoff
  witness_ge := opened.witness_ge
  cutoff_gt := opened.cutoff_gt
  rejects_lt_cutoff := by
    intro f hf N code hcode_lt haccepted
    rcases bridge.accepted_to_baProofObject
        (opened.witness f hf N) code haccepted with
      ⟨proof, hconclusion, hsize_le_code⟩
    have hsize_lt_cutoff :
        proof.size < opened.cutoff f hf N :=
      Nat.lt_of_le_of_lt hsize_le_code hcode_lt
    have hchecks :
        (baProofObjectRootCodeSemantics
            Ax target scale_data.powerBoundRawCode hcomplete).checks proof
          (scale_data.powerBoundRawCode (opened.witness f hf N)) := by
      exact ⟨opened.witness f hf N, rfl, hconclusion⟩
    exact
      opened.noAcceptedBelowAtWitness f hf N proof
        hsize_lt_cutoff hchecks

/--
End-to-end conditional closure from a Buss-Pudlak lower source to accepted
PA/Hilbert numeric-code rejection through structured BA proof objects.

The remaining inputs are explicit and minimal: the Buss-Pudlak lower-bound
source, completeness of the BA proof-object semantics for the target family,
injectivity of the root code family, the semantic length calibration, and the
accepted-code-to-BA-proof-object extraction bridge.
-/
noncomputable def
    bussPudlakLowerSource_baProofObjectBridge_toPAHilbertAcceptedNatCodeRejectionData
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete :
      ∀ n : Nat,
        ∃ proof :
          _root_.BoundedArithmeticLab.BAProofObject Ax,
          proof.conclusion = target n)
    (hroot_injective : Function.Injective scale_data.powerBoundRawCode)
    (hsemantic_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.BoundedArithmeticLab.semanticBAProofLength Ax target n)
    (bridge :
      BAProofObjectAcceptedNatCodeBridge scale_data checker Ax target) :
    PAHilbertAcceptedNatCodeRejectionExtractorData scale_data checker :=
  baProofObjectNoAcceptedBelow_toPAHilbertAcceptedNatCodeRejectionData
    Ax target hcomplete
    (bussPudlakLowerSource_baProofObjectSemantics_toNoAcceptedBelowCutoff
      source Ax target hcomplete hroot_injective hsemantic_length)
    bridge

/--
Pull accepted numeric-code rejection back to the BA proof-object layer.  The
only semantic bridge used here is the reverse encoder exactness above: a small
BA proof object would encode to a small accepted natural proof code, contradicting
the rejection data.
-/
theorem paHilbertAcceptedNatCodeRejectionData_to_BAProofObjectStrongSizeLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (data : PAHilbertAcceptedNatCodeRejectionExtractorData scale_data checker)
    (bridge :
      BAProofObjectToAcceptedNatCodeBridge scale_data checker Ax target) :
    BAProofObjectStrongSizeLowerBound Ax target := by
  intro U hU N
  refine ⟨data.witness U hU N, data.witness_ge U hU N, ?_⟩
  intro proof hconclusion
  by_contra hnot_gt
  have hproof_le_U : (proof.size : Real) ≤ U (data.witness U hU N) :=
    le_of_not_gt hnot_gt
  rcases bridge.baProofObject_to_accepted_code
      (data.witness U hU N) proof hconclusion with
    ⟨code, hcode_le_size, haccepted⟩
  have hcode_le_size_real : (code : Real) ≤ proof.size := by
    exact_mod_cast hcode_le_size
  have hcode_lt_cutoff_real :
      (code : Real) < (data.cutoff U hU N : Real) :=
    lt_of_le_of_lt (le_trans hcode_le_size_real hproof_le_U)
      (data.cutoff_gt U hU N)
  have hcode_lt_cutoff : code < data.cutoff U hU N := by
    exact_mod_cast hcode_lt_cutoff_real
  exact
    (data.rejects_lt_cutoff U hU N code hcode_lt_cutoff) haccepted

/--
Non-vacuous version: accepted numeric-code rejection plus completeness of the
BA proof-object target family gives the full complete proof-object lower-bound
package.
-/
theorem paHilbertAcceptedNatCodeRejectionData_to_BACompleteProofObjectStrongSizeLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete : BAProofObjectCompleteness Ax target)
    (data : PAHilbertAcceptedNatCodeRejectionExtractorData scale_data checker)
    (bridge :
      BAProofObjectToAcceptedNatCodeBridge scale_data checker Ax target) :
    BACompleteProofObjectStrongSizeLowerBound Ax target where
  complete := hcomplete
  strong_lower :=
    paHilbertAcceptedNatCodeRejectionData_to_BAProofObjectStrongSizeLowerBound
      Ax target data bridge

/--
The current canonical finite-consistency target cannot instantiate the
proof-object semantics above: in the present toy PA calculus there is no
`BAProofObject PAAxiom` proving `finiteConsistencyFormula n`.
-/
theorem no_currentToyFiniteConsistencyProofObjectCompleteness :
    (∀ n : Nat,
      ∃ proof :
        _root_.BoundedArithmeticLab.BAProofObject
          _root_.BoundedArithmeticLab.PAAxiom,
        proof.conclusion =
          _root_.BoundedArithmeticLab.finiteConsistencyFormula n) →
      False := by
  intro hcomplete
  exact no_currentToyPAProofObject_finiteConsistencyFormula 0
    (hcomplete 0)

/--
The non-vacuous proof-object lower-bound target also cannot be instantiated in
the current toy finite-consistency semantics, because its completeness field
would require proof objects that the toy PA calculus does not have.
-/
theorem no_currentToyBACompleteProofObjectStrongSizeLowerBound_finiteConsistency :
    BACompleteProofObjectStrongSizeLowerBound
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula →
      False := by
  intro hlower
  exact no_currentToyFiniteConsistencyProofObjectCompleteness
    hlower.complete

/--
The old concrete power-bound checker cannot even be connected to the opened
BA proof-object bridge for the current finite-consistency target.  It accepts
the numeric code `n` for `powerBoundRawCode n`; the bridge would therefore
extract a `BAProofObject PAAxiom` proving `finiteConsistencyFormula n`, but the
current toy PA calculus has no such proof object.

This pins down the old route's defect: the checker is not merely missing an
adapter, it is incompatible with the opened BA proof-object semantics.
-/
theorem no_currentToyBAProofObjectAcceptedNatCodeBridge_concretePowerBound
    (scale_data : InternalPudlakTheorem5ScaleData) :
    BAProofObjectAcceptedNatCodeBridge
        scale_data
        (concretePAHilbertPowerBoundChecker scale_data)
        _root_.BoundedArithmeticLab.PAAxiom
        _root_.BoundedArithmeticLab.finiteConsistencyFormula →
      False := by
  intro bridge
  let n : Nat := 0
  have haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode n) n :=
    concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
      scale_data n
  rcases bridge.accepted_to_baProofObject n n haccepted with
    ⟨proof, hconclusion, _hsize_le⟩
  exact no_currentToyPAProofObject_finiteConsistencyFormula n
    ⟨proof, hconclusion⟩

/--
The same obstruction, specialized to the minimal direct code-plus-two target.
The old concrete power-bound checker already accepts the native code `0` at
`n = 0`; a real accepted-code-to-PA-proof-object compiler would then have to
produce a current-toy `BAProofObject PAAxiom` of `finiteConsistencyFormula 0`,
which Lean has proved impossible.
-/
theorem no_currentToyPAProofObjectCodePlusTwoCompiler_concretePowerBound
    (scale_data : InternalPudlakTheorem5ScaleData) :
    PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler
        scale_data
        (concretePAHilbertPowerBoundChecker scale_data)
        _root_.BoundedArithmeticLab.finiteConsistencyFormula →
      False := by
  intro compiler
  let n : Nat := 0
  have haccepted :
      PAHilbertAcceptedProofCodeForFormulaCode
        (concretePAHilbertPowerBoundChecker scale_data)
        (scale_data.powerBoundRawCode n) n :=
    concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
      scale_data n
  exact
    no_acceptedNatCodePAProofObjectCodePlusTwoCompiler_currentToy_of_acceptedCode
      compiler haccepted

/-! ## Correct quantitative theorem-5 asymptotic reduction -/

/-- The explicit exponential envelope used when Buss's quantitative theorem is
specialized with a sufficiently fast time-constructible function. -/
def powTwoLowerEnvelope (n : Nat) : Real :=
  (2 : Real) ^ n

/-- `2^n` eventually strictly dominates every project polynomial bound. -/
theorem powTwoLowerEnvelope_eventually_gt_polynomial
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    ∀ᶠ n in atTop, U n < powTwoLowerEnvelope n := by
  rcases hU with ⟨c, k, hc⟩
  have hlittle :
      (fun n : Nat => (n : Real) ^ k) =o[atTop]
        (fun n : Nat => (2 : Real) ^ n) :=
    isLittleO_pow_const_const_pow_of_one_lt k (by norm_num)
  have hshift :
      (fun n : Nat => ((n + 1 : Nat) : Real) ^ k) =o[atTop]
        (fun n : Nat => (2 : Real) ^ (n + 1)) :=
    hlittle.comp_tendsto (tendsto_add_atTop_nat 1)
  have hscaled :
      (fun n : Nat => c * ((n + 1 : Nat) : Real) ^ k) =o[atTop]
        (fun n : Nat => (2 : Real) ^ n) := by
    have hconst :
        (fun n : Nat => c * ((n + 1 : Nat) : Real) ^ k) =o[atTop]
          (fun n : Nat => (2 : Real) ^ (n + 1)) :=
      hshift.const_mul_left c
    have hbigO :
        (fun n : Nat => (2 : Real) ^ (n + 1)) =O[atTop]
          (fun n : Nat => (2 : Real) ^ n) := by
      apply IsBigO.of_bound 2
      filter_upwards with n
      rw [pow_succ]
      simp only [Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
      rw [mul_comm (2 : Real)]
    exact hconst.trans_isBigO hbigO
  have hlt :
      ∀ᶠ n in atTop,
        c * ((n + 1 : Nat) : Real) ^ k < (2 : Real) ^ n := by
    have hnorm := hscaled.eventuallyLT_norm_of_eventually_pos
      (Filter.Eventually.of_forall fun n => by simp)
    filter_upwards [hnorm] with n hn
    have habs_lt :
        |c * ((n + 1 : Nat) : Real) ^ k| < (2 : Real) ^ n := by
      simpa [Real.norm_eq_abs, abs_pow,
        abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)] using hn
    exact (le_abs_self _).trans_lt habs_lt
  filter_upwards [hlt] with n hn
  exact (hc n).trans_lt (by
    simpa [powTwoLowerEnvelope, Nat.cast_add, Nat.cast_one] using hn)

/-- The exponential envelope is not a project polynomial bound. -/
theorem powTwoLowerEnvelope_not_polynomial_bound :
    ¬ _root_.is_polynomial_bound powTwoLowerEnvelope := by
  intro hpoly
  have hself :=
    powTwoLowerEnvelope_eventually_gt_polynomial
      powTwoLowerEnvelope hpoly
  rw [Filter.eventually_atTop] at hself
  rcases hself with ⟨N, hN⟩
  exact (lt_irrefl _ (hN N le_rfl))

/-- The current theorem-5 scale is polynomial by definition, so it is
eventually strictly below the exponential envelope. -/
theorem internalScale_eventually_lt_powTwo
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ∀ᶠ n in atTop,
      (scale_data.scale n : Real) < powTwoLowerEnvelope n :=
  powTwoLowerEnvelope_eventually_gt_polynomial
    (fun n : Nat => (scale_data.scale n : Real))
    scale_data.scale_polynomial_bound

/-- Hence the current scale package cannot also provide an eventual
exponential lower scale.  This is the precise mismatch between its
`scale_polynomial_bound` field and the fast rescaling needed to extract a
super-polynomial outer-index lower bound from Buss's quantitative theorem. -/
theorem no_internalScale_eventually_ge_powTwo
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ¬ ∀ᶠ n in atTop,
      powTwoLowerEnvelope n ≤ (scale_data.scale n : Real) := by
  intro hge
  have hlt := internalScale_eventually_lt_powTwo scale_data
  rw [Filter.eventually_atTop] at hlt hge
  rcases hlt with ⟨Nlt, hNlt⟩
  rcases hge with ⟨Nge, hNge⟩
  let N := max Nlt Nge
  exact (not_lt_of_ge (hNge N (le_max_right _ _)))
    (hNlt N (le_max_left _ _))

/-- Exact quantitative premise still owed by a faithful formalization of
Buss's theorem 5: eventually every accepted proof code has measured size
strictly above `2^n`.  It is stated directly and is not hidden in a package. -/
def EventuallyEveryAcceptedCodeAbovePowTwo
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) : Prop :=
  ∀ᶠ n in atTop,
    ∀ code : sem.Code,
      sem.checks code (scale_data.powerBoundRawCode n) →
        powTwoLowerEnvelope n < (sem.size code : Real)

/-- A direct exponential lower bound on every accepted code forces the
minimum accepted-code size above every polynomial. -/
theorem eventuallyEveryAcceptedCodeAbovePowTwo_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (hlower : EventuallyEveryAcceptedCodeAbovePowTwo scale_data sem) :
    CheckedMinProofCodeStrongLowerBound scale_data sem := by
  intro U hU
  have hpoly := powTwoLowerEnvelope_eventually_gt_polynomial U hU
  have hminimum :
      ∀ᶠ n in atTop,
        U n <
          (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) := by
    filter_upwards [hpoly, hlower] with n hU_pow hcodes
    rcases sem.hasProofCodeOfSize_minProofCodeSize
        (code := scale_data.powerBoundRawCode n) ⟨n, rfl⟩ with
      ⟨code, hchecks, hsize_le⟩
    have hsize_le_real :
        (sem.size code : Real) ≤
          (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) := by
      exact_mod_cast hsize_le
    exact hU_pow.trans (lt_of_lt_of_le (hcodes code hchecks) hsize_le_real)
  rw [Filter.frequently_atTop]
  intro N
  rcases Filter.eventually_atTop.1 hminimum with ⟨Nmin, hNmin⟩
  exact ⟨max N Nmin, le_max_left _ _, hNmin _ (le_max_right _ _)⟩

/-- The same reduction at the exact endpoint named by the short proof guide. -/
theorem eventuallyEveryAcceptedCodeAbovePowTwo_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (hlower : EventuallyEveryAcceptedCodeAbovePowTwo scale_data sem) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data sem :=
  eventuallyEveryAcceptedCodeAbovePowTwo_to_checkedMinProofCodeStrongLowerBound
    hlower

/-! ## Same-object projection obstruction -/

/-- A genuine super-polynomial checked minimum cannot be projected pointwise
into a polynomially bounded target with only the advertised `+2` overhead.

This is the exact audit condition for the Sondow/Pudlak same-object bridge:
the projection is not harmless bookkeeping.  If its target is already
polynomial without the rationality hypothesis, then it contradicts the lower
bound itself. -/
theorem
    checkedMinStrongLowerBound_forbids_polynomialCheckedTargetProjection
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {targetMeasured : Nat → Nat}
    (hlower : CheckedMinProofCodeStrongLowerBound scale_data sem)
    (hpoly :
      _root_.is_polynomial_bound
        (fun n : Nat => (targetMeasured n : Real))) :
    InternalPudlakTheorem5CheckedTargetProjection
        scale_data sem targetMeasured →
      False := by
  intro projection
  let U : Nat → Real := fun n => (targetMeasured n : Real) + 2
  have hU : _root_.is_polynomial_bound U := by
    exact _root_.is_polynomial_bound_add_const hpoly (by norm_num)
  have hfreq := hlower U hU
  rw [Filter.frequently_atTop] at hfreq
  rcases hfreq 0 with ⟨n, _hn, hnLower⟩
  have hnUpper :
      (sem.minProofCodeSize
          (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
        U n := by
    have hprojection := projection.source_le_target_add_two n
    have hprojectionReal :
        (sem.minProofCodeSize
            (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) ≤
          (targetMeasured n : Real) + 2 := by
      exact_mod_cast hprojection
    simpa [U] using hprojectionReal
  exact (not_lt_of_ge hnUpper) hnLower

/--
Direct audit obstruction for the old canonical calibration idea: if a
Buss-Pudlak lower source is calibrated to the current toy semantic PA length of
`finiteConsistencyFormula`, its own lower-bound field contradicts the fact that
that semantic length is identically zero.
-/
theorem no_currentToyBussPudlakLowerSource_semanticFiniteConsistency
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource)
    (hsemantic_length :
      ∀ n : Nat,
        source.pa_length n =
          _root_.BoundedArithmeticLab.semanticBAProofLength
            _root_.BoundedArithmeticLab.PAAxiom
            _root_.BoundedArithmeticLab.finiteConsistencyFormula n) :
    False := by
  rcases source.lower_bound.lower_bound
      (fun _ : Nat => (0 : Real))
      (_root_.BoundedArithmeticLab.IsPolynomialBound.const 0) 0 with
    ⟨n, _hn_ge, hgt⟩
  have hpa_zero : source.pa_length n = 0 := by
    rw [hsemantic_length n,
      currentToySemanticBAProofLength_finiteConsistency_eq_zero n]
  simp [_root_.BoundedArithmeticLab.bussPudlakTheorem5PABox,
    _root_.BoundedArithmeticLab.paSymbolBox,
    _root_.BoundedArithmeticLab.proofLengthBox, hpa_zero] at hgt

/--
The public project certificate bundle cannot be instantiated over the current
toy finite-consistency semantics.  Its `length_eq` field calibrates the Pudlak
lower source to `semanticBAProofLength PAAxiom finiteConsistencyFormula`, while
the current toy calculus makes that semantic length identically zero.  This
would contradict the lower-bound field of the same `lower_source`.
-/
theorem no_projectPublicCollisionCertificateBundle_currentToySemantics
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : _root_.BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (bundle :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) :
    False :=
  no_currentToyBussPudlakLowerSource_semanticFiniteConsistency
    bundle.lower_source bundle.length_eq

/--
The concrete certificate-obligation wrapper is equally impossible in the
current toy semantics, because it carries the same `lower_source` and
`length_eq` fields.
-/
theorem no_projectConcreteCertificateObligation_currentToySemantics
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : _root_.BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real}
    (obligation :
      _root_.BoundedArithmeticLab.BoundedProofPredicate.ProjectConcreteCertificateObligation
        MainRationality SondowAccepted bounds bound) :
    False :=
  no_currentToyBussPudlakLowerSource_semanticFiniteConsistency
    obligation.lower_source obligation.length_eq

/--
Nonempty public bundles are therefore ruled out for the current toy semantics.
This is the audit-level statement needed to avoid mistaking the public API for
a closed lower-bound proof.
-/
theorem no_nonempty_projectPublicCollisionCertificateBundle_currentToySemantics
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : _root_.BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty
        (_root_.BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
          MainRationality SondowAccepted bounds bound) →
      False := by
  intro hbundle
  rcases hbundle with ⟨bundle⟩
  exact no_projectPublicCollisionCertificateBundle_currentToySemantics bundle

/--
The equivalent concrete obligation is also nonempty-impossible under the
current toy semantics.
-/
theorem no_nonempty_projectConcreteCertificateObligation_currentToySemantics
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : _root_.BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    Nonempty
        (_root_.BoundedArithmeticLab.BoundedProofPredicate.ProjectConcreteCertificateObligation
          MainRationality SondowAccepted bounds bound) →
      False := by
  intro hobligation
  rcases hobligation with ⟨obligation⟩
  exact no_projectConcreteCertificateObligation_currentToySemantics obligation

/--
The named public completion obligation is equivalent to a nonempty public
certificate bundle, so it is also ruled out in the current toy semantics.
-/
theorem no_projectPublicCollisionCompletionObligation_currentToySemantics
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : _root_.BoundedArithmeticLab.SondowComponentBounds}
    {bound : Nat → Real} :
    _root_.BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCompletionObligation
        MainRationality SondowAccepted bounds bound →
      False := by
  intro hcompletion
  have hbundle :
      Nonempty
        (_root_.BoundedArithmeticLab.BoundedProofPredicate.ProjectPublicCollisionCertificateBundle
          MainRationality SondowAccepted bounds bound) :=
    (_root_.BoundedArithmeticLab.BoundedProofPredicate.projectPublicCollisionCompletionObligation_iff_bundle_nonempty).mp
      hcompletion
  exact
    no_nonempty_projectPublicCollisionCertificateBundle_currentToySemantics
      hbundle

/--
Month-6 checked-code replacement does not create a genuine Pudlak lower-bound
root under the current project `proof_length`.  Because the current root length
is formula-code size, the partial-consistency checked minimum is forced to be
linear.
-/
theorem month6CheckedReplacement_forces_partialConsistency_minChecked_linear_currentRoot
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {idx : Nat}
    {Ax : L.BoundedFormula α idx → Prop}
    {A B : Nat → L.BoundedFormula α idx}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (cert :
      _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6CheckedCodeReplacementCertificate
        interp)
    (m : Nat) :
    (interp.target_proof_family.rightConjElim.minCheckedCodeSize m : Real) =
      (m : Real) + 11 := by
  have hroot :
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.partialConsistencyCode m) =
        (m : Real) + 11 := by
    rw [_root_.proof_length_eq_rootFormulaCodeSize]
    simp [_root_.rootFormulaCodeSize, _root_.partialConsistencyCode,
      _root_.FormulaFamily.rootWeight, _root_.ProofSystem.rootWeight,
      _root_.ProofLengthMeasure.rootWeight, Nat.cast_add]
    ring
  have hchecked_local :
      (interp.target_proof_family.rightConjElim.minCheckedCodeSize m : Real) =
        (interp.localProofLength (_root_.partialConsistencyCode m) : Real) := by
    exact_mod_cast
      (by
        rw [interp.localProofLength_partialConsistency m]
        exact cert.source_minima.minChecked_eq_minLength m)
  exact hchecked_local.trans
    ((cert.calibration.local_calibration.source_eq_local m).symm.trans hroot)

/--
The same Month-6 replacement certificate forces the reflection-graft checked
minimum to be linear under the current root `proof_length`.
-/
theorem month6CheckedReplacement_forces_reflectionGraft_minChecked_linear_currentRoot
    {L : _root_.FirstOrder.Language.{u, v}} {α : Type w} {idx : Nat}
    {Ax : L.BoundedFormula α idx → Prop}
    {A B : Nat → L.BoundedFormula α idx}
    {halign : _root_.HilbertProjectionCodeAlignment}
    {interp :
      _root_.MiniHilbert.FormulaCodeHilbertInterpretation Ax A B halign}
    (cert :
      _root_.MiniHilbert.Month6ProofLengthCalibrationInternalizationSurface.Month6CheckedCodeReplacementCertificate
        interp)
    (m : Nat) :
    (interp.target_proof_family.minCheckedCodeSize m : Real) =
      (m : Real) + 13 := by
  have hroot :
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowReflectionGraftCode m) =
        (m : Real) + 13 := by
    rw [_root_.proof_length_eq_rootFormulaCodeSize]
    simp [_root_.rootFormulaCodeSize, _root_.sondowReflectionGraftCode,
      _root_.FormulaFamily.rootWeight, _root_.ProofSystem.rootWeight,
      _root_.ProofLengthMeasure.rootWeight, Nat.cast_add]
    ring
  have hchecked_local :
      (interp.target_proof_family.minCheckedCodeSize m : Real) =
        (interp.localProofLength (_root_.sondowReflectionGraftCode m) : Real) := by
    exact_mod_cast
      (by
        rw [interp.localProofLength_reflectionGraft m]
        exact cert.target_minima.minChecked_eq_minLength m)
  exact hchecked_local.trans
    ((cert.calibration.local_calibration.target_eq_local m).symm.trans hroot)

/--
Chosen lower-bound witness extracted from a strong proof-length lower bound.
This is noncomputable choice over the `frequently atTop` witness; it does not
introduce a tail-gap field.
-/
noncomputable def strongProofLengthLowerBoundWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hlower :
      _root_.StrongProofLengthLowerBound
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        scale_data.powerBoundRawCode)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    Nat :=
  Classical.choose
    ((Filter.frequently_atTop.mp
      (hlower.frequently_beats_every_polynomial f hf)) N)

theorem strongProofLengthLowerBoundWitness_spec
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hlower :
      _root_.StrongProofLengthLowerBound
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        scale_data.powerBoundRawCode)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    N ≤ strongProofLengthLowerBoundWitness hlower f hf N ∧
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode
            (strongProofLengthLowerBoundWitness hlower f hf N)) >
        f (strongProofLengthLowerBoundWitness hlower f hf N) :=
  Classical.choose_spec
    ((Filter.frequently_atTop.mp
      (hlower.frequently_beats_every_polynomial f hf)) N)

theorem strongProofLengthLowerBoundWitness_ge
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hlower :
      _root_.StrongProofLengthLowerBound
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        scale_data.powerBoundRawCode)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    N ≤ strongProofLengthLowerBoundWitness hlower f hf N :=
  (strongProofLengthLowerBoundWitness_spec hlower f hf N).1

theorem strongProofLengthLowerBoundWitness_gt
    {scale_data : InternalPudlakTheorem5ScaleData}
    (hlower :
      _root_.StrongProofLengthLowerBound
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        scale_data.powerBoundRawCode)
    (f : Nat → Real) (hf : _root_.is_polynomial_bound f) (N : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode
          (strongProofLengthLowerBoundWitness hlower f hf N)) >
      f (strongProofLengthLowerBoundWitness hlower f hf N) :=
  (strongProofLengthLowerBoundWitness_spec hlower f hf N).2

/--
A calibrated strong proof-length lower bound directly closes the opened
no-accepted-below target.  The proof is the minimality argument: choose a
lower-bound witness `n`, set `K` to the minimum accepted proof-code size for the
formula at `n`, and use calibration to get `K > f n`; by definition of the
minimum, no accepted proof code can have size `< K`.
-/
noncomputable def strongProofLengthLowerBound_toNoAcceptedBelowCutoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    (model :
      _root_.ProofLengthCodeSemantics.{0}
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data))
    (calibration : model.Calibration)
    (hlower :
      _root_.StrongProofLengthLowerBound
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        scale_data.powerBoundRawCode) :
    ComputableNoAcceptedBelowCutoff scale_data
      model.proof_code_semantics where
  witness := strongProofLengthLowerBoundWitness hlower
  cutoff := fun f hf N =>
    model.proof_code_semantics.minProofCodeSize
      (scale_data.powerBoundRawCode
        (strongProofLengthLowerBoundWitness hlower f hf N))
      ⟨strongProofLengthLowerBoundWitness hlower f hf N, rfl⟩
  witness_ge := strongProofLengthLowerBoundWitness_ge hlower
  cutoff_gt := by
    intro f hf N
    have hgt := strongProofLengthLowerBoundWitness_gt hlower f hf N
    have hcal :
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode
              (strongProofLengthLowerBoundWitness hlower f hf N)) =
          (model.proof_code_semantics.minProofCodeSize
            (scale_data.powerBoundRawCode
              (strongProofLengthLowerBoundWitness hlower f hf N))
            ⟨strongProofLengthLowerBoundWitness hlower f hf N, rfl⟩ :
              Real) :=
      calibration.proof_length_eq_minProofCodeSize
        (code := scale_data.powerBoundRawCode
          (strongProofLengthLowerBoundWitness hlower f hf N))
        ⟨strongProofLengthLowerBoundWitness hlower f hf N, rfl⟩
    rw [hcal] at hgt
    exact hgt
  noAcceptedBelowAtWitness := by
    intro f hf N c hsize hchecks
    have hmin_le_size :
        model.proof_code_semantics.minProofCodeSize
            (scale_data.powerBoundRawCode
              (strongProofLengthLowerBoundWitness hlower f hf N))
            ⟨strongProofLengthLowerBoundWitness hlower f hf N, rfl⟩ ≤
          model.proof_code_semantics.size c :=
      model.proof_code_semantics.minProofCodeSize_le_of_hasProofCodeOfSize
        ⟨strongProofLengthLowerBoundWitness hlower f hf N, rfl⟩
        ⟨c, hchecks, le_rfl⟩
    exact (not_lt_of_ge hmin_le_size) hsize

/--
Any old `computable_search_exclusion` certificate opens to the direct
no-accepted-below statement by using only the completeness of the small-code
search.
-/
def computableFiniteSearchExclusion_toNoAcceptedBelowCutoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    {search : InternalPudlakTheorem5SmallCodeSearch scale_data sem}
    (cert :
      InternalPudlakTheorem5ComputableFiniteSearchExclusion
        scale_data sem search) :
    ComputableNoAcceptedBelowCutoff scale_data sem where
  witness := cert.witness
  cutoff := cert.cutoff
  witness_ge := cert.witness_ge
  cutoff_gt := cert.cutoff_gt
  noAcceptedBelowAtWitness := by
    intro f hf N c hsize hchecks
    have hmem :
        c ∈ search.candidates (cert.witness f hf N) (cert.cutoff f hf N) :=
      search.complete (cert.witness f hf N) (cert.cutoff f hf N)
        c hchecks hsize
    exact cert.rejects_candidates f hf N c hmem hchecks

/--
Proof-length-free target with the lower-bound content fully opened to
`NoAcceptedBelowCutoff`: it has no search candidates and no gap object.
-/
def ProofLengthFreeNoAcceptedBelowClosureTarget
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  Nonempty
    (Σ sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
      ComputableNoAcceptedBelowCutoff scale_data sem)

/--
Positive closure package for the opened lower-bound target: a proof-code model,
its calibration to project `proof_length`, and a strong proof-length lower bound
are enough to produce the direct no-accepted-below certificate.
-/
structure ProofLengthCalibratedStrongLowerBoundNoAcceptedCore :
    Type 1 where
  scale_data : InternalPudlakTheorem5ScaleData
  proof_length_model :
    _root_.ProofLengthCodeSemantics.{0}
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
  calibration : proof_length_model.Calibration
  strong_lower_bound :
    _root_.StrongProofLengthLowerBound
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      scale_data.powerBoundRawCode

noncomputable def
    ProofLengthCalibratedStrongLowerBoundNoAcceptedCore.toNoAcceptedBelow
    (core : ProofLengthCalibratedStrongLowerBoundNoAcceptedCore) :
    ComputableNoAcceptedBelowCutoff core.scale_data
      core.proof_length_model.proof_code_semantics :=
  strongProofLengthLowerBound_toNoAcceptedBelowCutoff
    core.proof_length_model core.calibration core.strong_lower_bound

theorem
    proofLengthCalibratedStrongLowerBoundNoAcceptedCore_to_target
    (core : ProofLengthCalibratedStrongLowerBoundNoAcceptedCore) :
    ProofLengthFreeNoAcceptedBelowClosureTarget core.scale_data := by
  exact
    ⟨⟨core.proof_length_model.proof_code_semantics,
      core.toNoAcceptedBelow⟩⟩

/--
Current-root no-go for the positive closure package.  It would contain a strong
proof-length lower bound for a family whose current root length is already
polynomially bounded.
-/
theorem no_proofLengthCalibratedStrongLowerBoundNoAcceptedCore_currentRoot
    (core : ProofLengthCalibratedStrongLowerBoundNoAcceptedCore) :
    False :=
  no_internalPudlakTheorem5PowerBoundLowerBound_currentRoot
    core.scale_data core.strong_lower_bound

/--
Bounded-arithmetic audit: the Buss-Pudlak source currently exposes the PA lower
bound as a field.  It is an exact interface target for a future formalization,
not an internal derivation of theorem 5.
-/
def bussPudlakTheorem5PALowerBoundSource_lower_bound_is_field
    (source :
      _root_.BoundedArithmeticLab.BussPudlakTheorem5PALowerBoundSource) :
    _root_.BoundedArithmeticLab.EventualLowerBound source.box :=
  source.lower_bound

/--
The fully opened proof-length-free target gives the checked-measured search gap
directly.
-/
theorem proofLengthFreeNoAcceptedBelowClosureTarget_to_checkedMeasuredSearchGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (target : ProofLengthFreeNoAcceptedBelowClosureTarget scale_data) :
    Nonempty
      (Σ sem :
        _root_.ProofCodeSemantics.{0}
          (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
        ComputableSearchGapCertificate
          (month9_month10_checkedProofCodeMeasured scale_data sem)) := by
  rcases target with ⟨sem, opened⟩
  exact ⟨⟨sem, opened.toCheckedMeasuredSearchGap⟩⟩

/--
The fully opened proof-length-free target also gives the checked-minimum strong
lower bound directly.  This is the cleanest root-free theorem-5 lower-bound
closure statement: no `tail_gap`, no root `proof_length`, no calibration, and no
candidate-rejection wrapper.
-/
theorem proofLengthFreeNoAcceptedBelowClosureTarget_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (target : ProofLengthFreeNoAcceptedBelowClosureTarget scale_data) :
    ∃ sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
      CheckedMinProofCodeStrongLowerBound scale_data sem := by
  rcases target with ⟨sem, opened⟩
  exact ⟨sem, opened.toCheckedMinProofCodeStrongLowerBound⟩

/--
Accepted numeric-code rejection is the PA/Hilbert checker form of the opened
`NoAcceptedBelowCutoff` target.  This is proof-length-free and bypasses the old
uninhabitable full checker interface: the hard content is exactly that every
numeric proof code below the cutoff is not an accepted PA/Hilbert proof code.
-/
def paHilbertAcceptedNatCodeRejectionData_toNoAcceptedBelowCutoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (data :
      PAHilbertAcceptedNatCodeRejectionExtractorData scale_data checker) :
    ComputableNoAcceptedBelowCutoff scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics where
  witness := data.witness
  cutoff := data.cutoff
  witness_ge := data.witness_ge
  cutoff_gt := data.cutoff_gt
  noAcceptedBelowAtWitness := by
    intro f hf N code hsize hchecks
    exact
      data.rejects_lt_cutoff f hf N code
        (by
          simpa [
            InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
            PAHilbertAcceptedNatCodeCheckerSemantics] using hsize)
        (by
          simpa [
            InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
            PAHilbertAcceptedNatCodeCheckerSemantics] using hchecks)

/--
The theorem-5 no-small-proof-code statement closes the accepted numeric-code
rejection layer for the canonical PA/Hilbert natural-code semantics.

This is not a new lower-bound assumption.  It shows that the old
`rejection_data` field is just the opened finite-cutoff form of the genuine
root lower-bound theorem when the proof-code semantics has `Code = Nat` and
`size = id`.
-/
noncomputable def noSmallProofCodes_toPAHilbertAcceptedNatCodeRejectionData
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (hno :
      InternalPudlakTheorem5NoSmallProofCodes scale_data
        (PAHilbertAcceptedNatCodeCheckerSemantics
          scale_data checker completion).toProofCodeSemantics) :
    PAHilbertAcceptedNatCodeRejectionExtractorData scale_data checker :=
  let opened :=
    checkedMinProofCodeStrongLowerBound_toNoAcceptedBelowCutoff
      (scale_data := scale_data)
      (sem := (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics)
      (noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound hno)
  { witness := opened.witness
    cutoff := opened.cutoff
    witness_ge := opened.witness_ge
    cutoff_gt := opened.cutoff_gt
    rejects_lt_cutoff := by
      intro f hf N code hlt haccepted
      exact
        opened.noAcceptedBelowAtWitness f hf N code
          (by
            simpa [
              InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
              PAHilbertAcceptedNatCodeCheckerSemantics] using hlt)
          (by
            simpa [
              InternalPudlakTheorem5CheckerSemantics.toProofCodeSemantics,
              PAHilbertAcceptedNatCodeCheckerSemantics] using haccepted) }

/--
When the finite-search extractor is run against the canonical accepted-numeric
code enumeration, its candidate rejection is exactly rejection of every natural
proof code below the cutoff.  This is the lossless bridge from the older
finite-search wording to the fully opened accepted-code lower-bound wording.
-/
def paHilbertAcceptedNatCodeRejectionData_ofCheckerExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {completion : PAHilbertAcceptedNatCodeCompletion scale_data checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (PAHilbertAcceptedNatCodeCheckerSemantics
          scale_data checker completion)
        (PAHilbertAcceptedNatCodeFiniteEnumeration
          scale_data checker completion)) :
    PAHilbertAcceptedNatCodeRejectionExtractorData scale_data checker where
  witness := extractor.witness
  cutoff := extractor.cutoff
  witness_ge := extractor.witness_ge
  cutoff_gt := extractor.cutoff_gt
  rejects_lt_cutoff := by
    intro f hf N code hlt
    have hmem :
        code ∈
          (PAHilbertAcceptedNatCodeFiniteEnumeration
            scale_data checker completion).candidates
              (extractor.witness f hf N) (extractor.cutoff f hf N) := by
      simpa [PAHilbertAcceptedNatCodeFiniteEnumeration] using
        (List.mem_range.mpr hlt)
    exact extractor.rejects_candidates f hf N code hmem

/--
Corrected PA/Hilbert lower-bound core after the decoder repair.  It records a
canonical checker interface, a completion witness for the theorem-5 formula
family, and the direct accepted-numeric-code rejection theorem.  It contains no
root `proof_length`, no calibration, and no full decoder exactness field.
-/
structure PAHilbertCanonicalAcceptedNatCodeNoSmallCore
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 1 where
  checker : PAHilbertChecker
  semantics : PAHilbertDerivabilitySemantics
  canonical_interface :
    PAHilbertCanonicalCheckerInterface checker semantics
  completion : PAHilbertAcceptedNatCodeCompletion scale_data checker
  rejection_data :
    PAHilbertAcceptedNatCodeRejectionExtractorData scale_data checker

namespace PAHilbertCanonicalAcceptedNatCodeNoSmallCore

def proofCodeSemantics
    {scale_data : InternalPudlakTheorem5ScaleData}
    (core : PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data) :
    _root_.ProofCodeSemantics.{0}
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data) :=
  (PAHilbertAcceptedNatCodeCheckerSemantics
    scale_data core.checker core.completion).toProofCodeSemantics

def toNoAcceptedBelowCutoff
    {scale_data : InternalPudlakTheorem5ScaleData}
    (core : PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data) :
    ComputableNoAcceptedBelowCutoff scale_data core.proofCodeSemantics :=
  paHilbertAcceptedNatCodeRejectionData_toNoAcceptedBelowCutoff
    (completion := core.completion) core.rejection_data

theorem toProofLengthFreeNoAcceptedBelowClosureTarget
    {scale_data : InternalPudlakTheorem5ScaleData}
    (core : PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data) :
    ProofLengthFreeNoAcceptedBelowClosureTarget scale_data :=
  ⟨⟨core.proofCodeSemantics, core.toNoAcceptedBelowCutoff⟩⟩

theorem to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (core : PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data) :
    ∃ sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
      CheckedMinProofCodeStrongLowerBound scale_data sem :=
  proofLengthFreeNoAcceptedBelowClosureTarget_to_checkedMinProofCodeStrongLowerBound
    core.toProofLengthFreeNoAcceptedBelowClosureTarget

/--
Exact shortest-growth closure for the corrected canonical PA/Hilbert
accepted-natural-code core.  This is the non-existential form needed by the
short proof guide: after the real accepted-code no-small core is constructed,
the lower-bound target holds for that same concrete proof-code semantics.
-/
theorem to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    (core : PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      core.proofCodeSemantics :=
  core.toNoAcceptedBelowCutoff.toCheckedMinProofCodeStrongLowerBound

theorem to_BACompleteProofObjectStrongSizeLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (core : PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data)
    (Ax : _root_.BoundedArithmeticLab.BAFormula → Prop)
    (target : Nat → _root_.BoundedArithmeticLab.BAFormula)
    (hcomplete : BAProofObjectCompleteness Ax target)
    (bridge :
      BAProofObjectToAcceptedNatCodeBridge
        scale_data core.checker Ax target) :
    BACompleteProofObjectStrongSizeLowerBound Ax target :=
  paHilbertAcceptedNatCodeRejectionData_to_BACompleteProofObjectStrongSizeLowerBound
    Ax target hcomplete core.rejection_data bridge

end PAHilbertCanonicalAcceptedNatCodeNoSmallCore

/--
Extractor-shaped version of the corrected PA/Hilbert lower-bound core.  This
is slightly closer to the old finite-search files than
`PAHilbertCanonicalAcceptedNatCodeNoSmallCore`, but it is still fully opened:
the enumeration is fixed to all natural codes below `cutoff`, so no hidden
candidate-filter can erase accepted small proof codes.
-/
structure PAHilbertAcceptedNatCodeExtractorNoSmallCore
    (scale_data : InternalPudlakTheorem5ScaleData) : Type 1 where
  checker : PAHilbertChecker
  semantics : PAHilbertDerivabilitySemantics
  canonical_interface :
    PAHilbertCanonicalCheckerInterface checker semantics
  completion : PAHilbertAcceptedNatCodeCompletion scale_data checker
  extractor :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion)
      (PAHilbertAcceptedNatCodeFiniteEnumeration
        scale_data checker completion)

namespace PAHilbertAcceptedNatCodeExtractorNoSmallCore

def rejectionData
    {scale_data : InternalPudlakTheorem5ScaleData}
    (core : PAHilbertAcceptedNatCodeExtractorNoSmallCore scale_data) :
    PAHilbertAcceptedNatCodeRejectionExtractorData scale_data core.checker :=
  paHilbertAcceptedNatCodeRejectionData_ofCheckerExtractor core.extractor

def toCanonicalAcceptedNatCodeNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (core : PAHilbertAcceptedNatCodeExtractorNoSmallCore scale_data) :
    PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data where
  checker := core.checker
  semantics := core.semantics
  canonical_interface := core.canonical_interface
  completion := core.completion
  rejection_data := core.rejectionData

theorem to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (core : PAHilbertAcceptedNatCodeExtractorNoSmallCore scale_data) :
    ∃ sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
      CheckedMinProofCodeStrongLowerBound scale_data sem :=
  core.toCanonicalAcceptedNatCodeNoSmallCore
    |>.to_checkedMinProofCodeStrongLowerBound

end PAHilbertAcceptedNatCodeExtractorNoSmallCore

def PAHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  Nonempty (PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data)

/--
If the real PA/Hilbert accepted-natural-code semantics satisfies theorem 5 in
the no-small-proof-code form, then the corrected canonical accepted-code core is
constructed directly.  The only lower-bound input left is the theorem-5
statement itself, not `tail_gap`, `rejection_search`, or a separate
accepted-code rejection package.
-/
noncomputable def
    noSmallProofCodes_toPAHilbertCanonicalAcceptedNatCodeNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (canonical_interface :
      PAHilbertCanonicalCheckerInterface checker semantics)
    (completion : PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (hno :
      InternalPudlakTheorem5NoSmallProofCodes scale_data
        (PAHilbertAcceptedNatCodeCheckerSemantics
          scale_data checker completion).toProofCodeSemantics) :
    PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data where
  checker := checker
  semantics := semantics
  canonical_interface := canonical_interface
  completion := completion
  rejection_data :=
    noSmallProofCodes_toPAHilbertAcceptedNatCodeRejectionData hno

/--
Closure-target version of the same statement: a checker, its canonical
interface, completion, and theorem-5 no-small-code lower bound are sufficient
for the next-stage PA/Hilbert target.
-/
theorem noSmallProofCodes_toPAHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (canonical_interface :
      PAHilbertCanonicalCheckerInterface checker semantics)
    (completion : PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (hno :
      InternalPudlakTheorem5NoSmallProofCodes scale_data
        (PAHilbertAcceptedNatCodeCheckerSemantics
          scale_data checker completion).toProofCodeSemantics) :
    PAHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget scale_data :=
  ⟨noSmallProofCodes_toPAHilbertCanonicalAcceptedNatCodeNoSmallCore
    checker semantics canonical_interface completion hno⟩

/--
Root-free semantic PA/Hilbert proof-object route to the corrected canonical
accepted-natural-code core.  Once the semantic minimum accepted proof-object
code size is proved to beat every polynomial, all accepted numeric proof codes
are no-small automatically; no project root `proof_length` calibration is used.
-/
noncomputable def
    paHilbertAcceptedProofObjectSemanticLowerBound_toCanonicalAcceptedNatCodeNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (canonical_interface :
      PAHilbertCanonicalCheckerInterface checker semantics)
    (completion : PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (semantic_lower_bound :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∃ᶠ n in Filter.atTop,
          ((paHilbertAcceptedProofObjectCodeSemantics
              scale_data checker completion).minProofCodeSize
                (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n) :
    PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data :=
  noSmallProofCodes_toPAHilbertCanonicalAcceptedNatCodeNoSmallCore
    checker semantics canonical_interface completion
    (paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
      (checker := checker)
      (completion := completion)
      semantic_lower_bound)

/--
Closure-target version of the semantic PA/Hilbert proof-object route.
-/
theorem
    paHilbertAcceptedProofObjectSemanticLowerBound_toCanonicalAcceptedNatCodeNoSmallClosureTarget
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (canonical_interface :
      PAHilbertCanonicalCheckerInterface checker semantics)
    (completion : PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (semantic_lower_bound :
      ∀ U : Nat → Real, _root_.is_polynomial_bound U →
        ∃ᶠ n in Filter.atTop,
          ((paHilbertAcceptedProofObjectCodeSemantics
              scale_data checker completion).minProofCodeSize
                (scale_data.powerBoundRawCode n) ⟨n, rfl⟩ : Real) > U n) :
    PAHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget scale_data :=
  ⟨paHilbertAcceptedProofObjectSemanticLowerBound_toCanonicalAcceptedNatCodeNoSmallCore
    checker semantics canonical_interface completion semantic_lower_bound⟩

/--
Paper-proof closure specialized to the corrected canonical PA/Hilbert
accepted-natural-code core.

This exposes the two remaining mathematical inputs separately:
Pudlak's root proof-length lower bound and the direct numeric accepted-code
soundness inequality.  The old `tail_gap`, payload fields, and finite-search
wrappers are not part of this closure.
-/
noncomputable def
    powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_toCanonicalAcceptedNatCodeNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (canonical_interface :
      PAHilbertCanonicalCheckerInterface checker semantics)
    (completion : PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (accepted_code_size_ge_actual :
      ∀ n : Nat, ∀ code : Nat,
        PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code →
          actualProofLengthMeasured scale_data n ≤ (code : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data :=
  noSmallProofCodes_toPAHilbertCanonicalAcceptedNatCodeNoSmallCore
    checker semantics canonical_interface completion
    (powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_to_noSmallProofCodes
      (checker := checker)
      (completion := completion)
      accepted_code_size_ge_actual hlower)

/--
Closure-target version of the same direct PA/Hilbert route.
-/
theorem
    powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_toCanonicalAcceptedNatCodeNoSmallClosureTarget
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (canonical_interface :
      PAHilbertCanonicalCheckerInterface checker semantics)
    (completion : PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (accepted_code_size_ge_actual :
      ∀ n : Nat, ∀ code : Nat,
        PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code →
          actualProofLengthMeasured scale_data n ≤ (code : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    PAHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget scale_data :=
  ⟨powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_toCanonicalAcceptedNatCodeNoSmallCore
    checker semantics canonical_interface completion
    accepted_code_size_ge_actual hlower⟩

/--
Direct short-proof endpoint for the accepted-natural-code checker.  This is the
paper proof with no intermediate tail-gap/search package: Pudlak's root lower
bound plus one-sided accepted-code soundness gives the exact shortest checked
minimum growth obligation for the same PA/Hilbert accepted-code semantics.
-/
theorem
    powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (canonical_interface :
      PAHilbertCanonicalCheckerInterface checker semantics)
    (completion : PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (accepted_code_size_ge_actual :
      ∀ n : Nat, ∀ code : Nat,
        PAHilbertAcceptedProofCodeForFormulaCode
          checker (scale_data.powerBoundRawCode n) code →
          actualProofLengthMeasured scale_data n ≤ (code : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  (powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_toCanonicalAcceptedNatCodeNoSmallCore
      checker semantics canonical_interface completion
      accepted_code_size_ge_actual hlower)
    |>.to_shortestCheckedMinProofCodeGrowthObligation

/--
Canonical-core closure from the object-level accepted-proof length soundness.
This is the next more concrete target after the short proof: prove the
object-level PA proof-length bound, then the natural-code soundness and the
no-small-code core follow mechanically.
-/
noncomputable def
    powerBoundLowerBound_and_paHilbertAcceptedProofObjectLengthSound_toCanonicalAcceptedNatCodeNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (canonical_interface :
      PAHilbertCanonicalCheckerInterface checker semantics)
    (completion : PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (accepted_object_length_sound :
      ∀ formulaCode : _root_.FormulaCode,
        ∀ proof : PAHilbertProofObject,
          proof.conclusion.code = formulaCode →
            checker.accepts proof proof.conclusion = true →
              _root_.proof_length _root_.ProofSystem.PA
                _root_.ProofLengthMeasure.symbolSize formulaCode ≤
                  (proof.code : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data :=
  powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_toCanonicalAcceptedNatCodeNoSmallCore
    checker semantics canonical_interface completion
    (paHilbertAcceptedNatCode_soundness_of_acceptedProofObjectLengthSound
      accepted_object_length_sound)
    hlower

/--
Object-level version of the direct short-proof endpoint.  It replaces the
numeric accepted-code soundness premise by the more concrete statement that
every accepted decoded PA/Hilbert proof object has numeric code at least the
root PA symbol-size proof length of its conclusion.
-/
theorem
    powerBoundLowerBound_and_paHilbertAcceptedProofObjectLengthSound_to_shortestCheckedMinProofCodeGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : PAHilbertChecker}
    {semantics : PAHilbertDerivabilitySemantics}
    (canonical_interface :
      PAHilbertCanonicalCheckerInterface checker semantics)
    (completion : PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (accepted_object_length_sound :
      ∀ formulaCode : _root_.FormulaCode,
        ∀ proof : PAHilbertProofObject,
          proof.conclusion.code = formulaCode →
            checker.accepts proof proof.conclusion = true →
              _root_.proof_length _root_.ProofSystem.PA
                _root_.ProofLengthMeasure.symbolSize formulaCode ≤
                  (proof.code : Real))
    (hlower : scale_data.PowerBoundLowerBound) :
    ShortestCheckedMinProofCodeGrowthObligation scale_data
      (PAHilbertAcceptedNatCodeCheckerSemantics
        scale_data checker completion).toProofCodeSemantics :=
  powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_to_shortestCheckedMinProofCodeGrowthObligation
    canonical_interface completion
    (paHilbertAcceptedNatCode_soundness_of_acceptedProofObjectLengthSound
      accepted_object_length_sound)
    hlower

/--
Compatibility route from the older PA/Hilbert proof-length exactness data to
the corrected canonical accepted-natural-code core.  It factors through the
one-sided accepted-code soundness lemma, which is the smaller obligation named
by the short paper proof.
-/
noncomputable def
    powerBoundLowerBound_and_paHilbertAcceptedNatCodeProofLengthExactness_toCanonicalAcceptedNatCodeNoSmallCore
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker : PAHilbertChecker)
    (semantics : PAHilbertDerivabilitySemantics)
    (canonical_interface :
      PAHilbertCanonicalCheckerInterface checker semantics)
    (completion : PAHilbertAcceptedNatCodeCompletion scale_data checker)
    (exactness :
      PAHilbertAcceptedNatCodeProofLengthExactnessData
        scale_data checker completion)
    (hlower : scale_data.PowerBoundLowerBound) :
    PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data :=
  powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_toCanonicalAcceptedNatCodeNoSmallCore
    checker semantics canonical_interface completion
    (paHilbertAcceptedNatCode_soundness_of_proofLengthExactnessData
      exactness)
    hlower

/--
Next-stage target from the short paper proof.  It is not a new assumption:
it names the concrete PA/Hilbert accepted-numeric-code core that must be
constructed in order to prove the shortest checked-minimum growth obligation.
-/
abbrev NextStageRealPAHilbertNoSmallCodeTarget
    (scale_data : InternalPudlakTheorem5ScaleData) : Prop :=
  PAHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget scale_data

theorem paHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget_to_checkedMinProofCodeStrongLowerBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (target :
      PAHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget scale_data) :
    ∃ sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
      CheckedMinProofCodeStrongLowerBound scale_data sem := by
  rcases target with ⟨core⟩
  exact core.to_checkedMinProofCodeStrongLowerBound

/--
The next-stage real PA/Hilbert target is sufficient for the short-paper
growth obligation.  The remaining work is therefore not another wrapper, but
constructing `PAHilbertCanonicalAcceptedNatCodeNoSmallCore` itself.
-/
theorem nextStageRealPAHilbertNoSmallCodeTarget_to_shortestGrowthObligation
    {scale_data : InternalPudlakTheorem5ScaleData}
    (target : NextStageRealPAHilbertNoSmallCodeTarget scale_data) :
    ∃ sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data),
      ShortestCheckedMinProofCodeGrowthObligation scale_data sem :=
  paHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget_to_checkedMinProofCodeStrongLowerBound
    target

/--
The old concrete power-bound checker cannot supply the corrected accepted
numeric-code rejection data: it accepts numeric code `n` for
`powerBoundRawCode n`, while the rejection data would choose a cutoff strictly
larger than `n` for the polynomial upper bound `n`.
-/
theorem no_concretePAHilbertPowerBoundAcceptedNatCodeRejectionData
    (scale_data : InternalPudlakTheorem5ScaleData) :
    PAHilbertAcceptedNatCodeRejectionExtractorData
        scale_data (concretePAHilbertPowerBoundChecker scale_data) →
      False := by
  intro data
  let w := data.witness (fun n : Nat => (n : Real))
    nativeIdentityLength_polynomial 0
  have hcut_real :
      (w : Real) <
        (data.cutoff (fun n : Nat => (n : Real))
          nativeIdentityLength_polynomial 0 : Real) :=
    data.cutoff_gt (fun n : Nat => (n : Real))
      nativeIdentityLength_polynomial 0
  have hcut_nat :
      w <
        data.cutoff (fun n : Nat => (n : Real))
          nativeIdentityLength_polynomial 0 := by
    exact_mod_cast hcut_real
  exact
    data.rejects_lt_cutoff (fun n : Nat => (n : Real))
      nativeIdentityLength_polynomial 0 w hcut_nat
      (concretePAHilbertPowerBoundChecker_acceptedProofCode_at_powerBoundRawCode
        scale_data w)

theorem no_concretePAHilbertPowerBoundCanonicalAcceptedNatCodeNoSmallCore
    (scale_data : InternalPudlakTheorem5ScaleData)
    (core : PAHilbertCanonicalAcceptedNatCodeNoSmallCore scale_data)
    (hchecker :
      core.checker = concretePAHilbertPowerBoundChecker scale_data) :
    False := by
  have data_concrete :
      PAHilbertAcceptedNatCodeRejectionExtractorData
        scale_data (concretePAHilbertPowerBoundChecker scale_data) := by
    rw [← hchecker]
    exact core.rejection_data
  exact
    no_concretePAHilbertPowerBoundAcceptedNatCodeRejectionData
      scale_data data_concrete

theorem no_concretePAHilbertPowerBoundAcceptedNatCodeCheckerExtractor
    (scale_data : InternalPudlakTheorem5ScaleData)
    {completion :
      PAHilbertAcceptedNatCodeCompletion
        scale_data (concretePAHilbertPowerBoundChecker scale_data)} :
    InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (PAHilbertAcceptedNatCodeCheckerSemantics
          scale_data (concretePAHilbertPowerBoundChecker scale_data)
          completion)
        (PAHilbertAcceptedNatCodeFiniteEnumeration
          scale_data (concretePAHilbertPowerBoundChecker scale_data)
          completion) →
      False := by
  intro extractor
  exact
    no_concretePAHilbertPowerBoundAcceptedNatCodeRejectionData
      scale_data
      (paHilbertAcceptedNatCodeRejectionData_ofCheckerExtractor extractor)

theorem no_concretePAHilbertPowerBoundRejectionExtractorInput
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ConcretePAHilbertPowerBoundRejectionExtractorInput scale_data →
      False := by
  intro input
  exact
    no_concretePAHilbertPowerBoundAcceptedNatCodeRejectionData
      scale_data input.toAcceptedNatCodeData

theorem no_concretePAHilbertPowerBoundFourPiece
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ConcretePAHilbertPowerBoundFourPiece scale_data → False := by
  intro fourPiece
  exact
    no_concretePAHilbertPowerBoundRejectionExtractorInput
      scale_data fourPiece.rejection_extractor_input

/--
Size-filtered strengthening of the old small-code search.  This is the missing
soundness condition needed to reconstruct candidate rejection from the direct
no-accepted-below statement.
-/
structure SizeFilteredSmallCodeSearch
    (scale_data : InternalPudlakTheorem5ScaleData)
    (sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)) :
    Type 1 where
  search : InternalPudlakTheorem5SmallCodeSearch scale_data sem
  candidates_size_lt :
    ∀ n K : Nat, ∀ c : sem.Code,
      c ∈ search.candidates n K → sem.size c < K

/--
If the candidate enumeration is size-filtered, the direct no-accepted-below
statement reconstructs the old `computable_search_exclusion` object.
-/
def noAcceptedBelowCutoff_toComputableFiniteSearchExclusion
    {scale_data : InternalPudlakTheorem5ScaleData}
    {sem :
      _root_.ProofCodeSemantics.{0}
        (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)}
    (sizeFiltered : SizeFilteredSmallCodeSearch scale_data sem)
    (opened : ComputableNoAcceptedBelowCutoff scale_data sem) :
    InternalPudlakTheorem5ComputableFiniteSearchExclusion
      scale_data sem sizeFiltered.search where
  witness := opened.witness
  cutoff := opened.cutoff
  witness_ge := opened.witness_ge
  cutoff_gt := opened.cutoff_gt
  rejects_candidates := by
    intro f hf N c hmem
    exact opened.noAcceptedBelowAtWitness f hf N c
      (sizeFiltered.candidates_size_lt
        (opened.witness f hf N) (opened.cutoff f hf N) c hmem)

/--
The theorem-5 closure target with `computable_search_exclusion` fully opened:
the lower-bound content is a direct no-accepted-below theorem, and the finite
search layer is required to be size-filtered.
-/
structure OpenedGapFreeTheorem5ClosureCore : Type 1 where
  scale_data : InternalPudlakTheorem5ScaleData
  proof_length_model :
    _root_.ProofLengthCodeSemantics.{0}
      _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
      (InternalPudlakTheorem5PowerBoundRelevantCode scale_data)
  sizeFilteredSearch :
    SizeFilteredSmallCodeSearch scale_data
      proof_length_model.proof_code_semantics
  noAcceptedBelow :
    ComputableNoAcceptedBelowCutoff scale_data
      proof_length_model.proof_code_semantics
  calibration : proof_length_model.Calibration

def OpenedGapFreeTheorem5ClosureCore.toComputableFiniteSearchNoSmallCore
    (core : OpenedGapFreeTheorem5ClosureCore) :
    InternalPudlakTheorem5ComputableFiniteSearchNoSmallCore.{0} where
  scale_data := core.scale_data
  proof_length_model := core.proof_length_model
  small_code_search := core.sizeFilteredSearch.search
  computable_search_exclusion :=
    noAcceptedBelowCutoff_toComputableFiniteSearchExclusion
      core.sizeFilteredSearch core.noAcceptedBelow
  calibration := core.calibration

def OpenedGapFreeTheorem5ClosureTarget : Prop :=
  Nonempty OpenedGapFreeTheorem5ClosureCore

theorem openedGapFreeTheorem5ClosureTarget_to_gapFreeTheorem5ClosureTarget :
    OpenedGapFreeTheorem5ClosureTarget →
      GapFreeTheorem5ClosureTarget := by
  intro htarget
  rcases htarget with ⟨core⟩
  exact ⟨core.toComputableFiniteSearchNoSmallCore⟩

theorem no_openedGapFreeTheorem5ClosureTarget_currentRoot :
    OpenedGapFreeTheorem5ClosureTarget → False := by
  intro htarget
  exact no_gapFreeTheorem5ClosureTarget_currentRoot
    (openedGapFreeTheorem5ClosureTarget_to_gapFreeTheorem5ClosureTarget
      htarget)

#check currentLowerBoundRouteObstructionLedger
#print axioms currentLowerBoundRouteObstructionLedger

#check ProofLengthFreeLowerGapClosureTarget

#check proofLengthFreeLowerGapClosureTarget_to_checkedMeasuredSearchGap
#print axioms proofLengthFreeLowerGapClosureTarget_to_checkedMeasuredSearchGap

#check proofLengthFreeLowerGapSource_to_checkedMinProofCodeStrongLowerBound
#print axioms proofLengthFreeLowerGapSource_to_checkedMinProofCodeStrongLowerBound

#check proofLengthFreeLowerGapClosureTarget_to_checkedMinProofCodeStrongLowerBound
#print axioms proofLengthFreeLowerGapClosureTarget_to_checkedMinProofCodeStrongLowerBound

#check checkerComputableSearchProfile_to_checkedMinProofCodeStrongLowerBound
#print axioms checkerComputableSearchProfile_to_checkedMinProofCodeStrongLowerBound

#check ProofLengthFreeSourceRootExactness

#check proofLengthFreeSource_and_rootExactness_to_actualProofLengthGap
#print axioms proofLengthFreeSource_and_rootExactness_to_actualProofLengthGap

#check no_proofLengthFreeSourceRootExactness_currentRoot
#print axioms no_proofLengthFreeSourceRootExactness_currentRoot

#check RootClosedTheorem5LowerBoundWitness

#check RootClosedTheorem5LowerBoundTarget

#check rootClosedTheorem5LowerBoundTarget_to_actualProofLengthSearchGapTarget
#print axioms rootClosedTheorem5LowerBoundTarget_to_actualProofLengthSearchGapTarget

#check rootClosedTheorem5LowerBoundTarget_to_actualProofLengthPointwiseSearchGapTarget
#print axioms rootClosedTheorem5LowerBoundTarget_to_actualProofLengthPointwiseSearchGapTarget

#check no_rootClosedTheorem5LowerBoundTarget_currentRoot
#print axioms no_rootClosedTheorem5LowerBoundTarget_currentRoot

#check finalExactCheckerCoreInput_toRootClosedTheorem5LowerBoundWitness
#print axioms finalExactCheckerCoreInput_toRootClosedTheorem5LowerBoundWitness

#check finalExactCheckerCoreInput_toRootClosedTheorem5LowerBoundTarget
#print axioms finalExactCheckerCoreInput_toRootClosedTheorem5LowerBoundTarget

#check no_finalExactCheckerCoreInput_currentRoot
#print axioms no_finalExactCheckerCoreInput_currentRoot

#check GapFreeTheorem5ClosureTarget

#check computableFiniteSearchNoSmallCore_toRootClosedTheorem5LowerBoundWitness
#print axioms computableFiniteSearchNoSmallCore_toRootClosedTheorem5LowerBoundWitness

#check gapFreeTheorem5ClosureTarget_to_rootClosedTheorem5LowerBoundTarget
#print axioms gapFreeTheorem5ClosureTarget_to_rootClosedTheorem5LowerBoundTarget

#check no_gapFreeTheorem5ClosureTarget_currentRoot
#print axioms no_gapFreeTheorem5ClosureTarget_currentRoot

#check OpenedGapFreeTheorem5ClosureTarget

#check openedGapFreeTheorem5ClosureTarget_to_gapFreeTheorem5ClosureTarget
#print axioms openedGapFreeTheorem5ClosureTarget_to_gapFreeTheorem5ClosureTarget

#check no_openedGapFreeTheorem5ClosureTarget_currentRoot
#print axioms no_openedGapFreeTheorem5ClosureTarget_currentRoot

#check ComputableNoAcceptedBelowCutoff

#check ComputableNoAcceptedBelowCutoff.noSmallAtWitness
#print axioms ComputableNoAcceptedBelowCutoff.noSmallAtWitness

#check ComputableNoAcceptedBelowCutoff.minProofCodeSize_gt_at_witness
#print axioms ComputableNoAcceptedBelowCutoff.minProofCodeSize_gt_at_witness

#check ComputableNoAcceptedBelowCutoff.toCheckedMeasuredSearchGap
#print axioms ComputableNoAcceptedBelowCutoff.toCheckedMeasuredSearchGap

#check CheckedMinProofCodeStrongLowerBound

#check ComputableNoAcceptedBelowCutoff.toCheckedMinProofCodeStrongLowerBound
#print axioms ComputableNoAcceptedBelowCutoff.toCheckedMinProofCodeStrongLowerBound

#check checkedMinProofCodeStrongLowerBoundWitness
#print axioms checkedMinProofCodeStrongLowerBoundWitness

#check checkedMinProofCodeStrongLowerBoundWitness_spec
#print axioms checkedMinProofCodeStrongLowerBoundWitness_spec

#check checkedMinProofCodeStrongLowerBound_toNoAcceptedBelowCutoff
#print axioms checkedMinProofCodeStrongLowerBound_toNoAcceptedBelowCutoff

#check checkedMinProofCodeStrongLowerBound_to_noSmallProofCodes
#print axioms checkedMinProofCodeStrongLowerBound_to_noSmallProofCodes

#check noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound
#print axioms noSmallProofCodes_to_checkedMinProofCodeStrongLowerBound

#check checkedMinProofCodeStrongLowerBound_iff_noSmallProofCodes
#print axioms checkedMinProofCodeStrongLowerBound_iff_noSmallProofCodes

#check ShortestCheckedMinProofCodeGrowthObligation

#check shortestCheckedMinProofCodeGrowthObligation_iff_noSmallProofCodes
#print axioms shortestCheckedMinProofCodeGrowthObligation_iff_noSmallProofCodes

#check InternalPudlakTheorem5EventuallyPolynomialAcceptedCodeFamily

#check noSmallProofCodes_to_no_eventualPolynomialAcceptedCodeFamily
#print axioms noSmallProofCodes_to_no_eventualPolynomialAcceptedCodeFamily

#check no_eventualPolynomialAcceptedCodeFamily_to_noSmallProofCodes
#print axioms no_eventualPolynomialAcceptedCodeFamily_to_noSmallProofCodes

#check noSmallProofCodes_iff_no_eventualPolynomialAcceptedCodeFamily
#print axioms noSmallProofCodes_iff_no_eventualPolynomialAcceptedCodeFamily

#check powerBoundLowerBound_and_allCheckedCode_size_ge_actual_to_no_eventualPolynomialAcceptedCodeFamily
#print axioms powerBoundLowerBound_and_allCheckedCode_size_ge_actual_to_no_eventualPolynomialAcceptedCodeFamily

#check powerBoundLowerBound_and_allCheckedCode_size_ge_actual_to_noSmallProofCodes
#print axioms powerBoundLowerBound_and_allCheckedCode_size_ge_actual_to_noSmallProofCodes

#check powerBoundLowerBound_and_checkerProofLengthExactness_to_noSmallProofCodes
#print axioms powerBoundLowerBound_and_checkerProofLengthExactness_to_noSmallProofCodes

#check powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_to_noSmallProofCodes
#print axioms powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_to_noSmallProofCodes

#check paHilbertAcceptedNatCode_soundness_of_proofLengthExactnessData
#print axioms paHilbertAcceptedNatCode_soundness_of_proofLengthExactnessData

#check paHilbertAcceptedNatCode_soundness_of_acceptedProofObjectLengthSound
#print axioms paHilbertAcceptedNatCode_soundness_of_acceptedProofObjectLengthSound

#check powerBoundLowerBound_and_paHilbertAcceptedProofObjectLengthSound_to_noSmallProofCodes
#print axioms powerBoundLowerBound_and_paHilbertAcceptedProofObjectLengthSound_to_noSmallProofCodes

#check no_concretePAHilbertPowerBound_acceptedProofObjectLengthSound_currentRoot
#print axioms no_concretePAHilbertPowerBound_acceptedProofObjectLengthSound_currentRoot

#check no_concretePAHilbertPowerBound_acceptedNatCodeSoundness_currentRoot
#print axioms no_concretePAHilbertPowerBound_acceptedNatCodeSoundness_currentRoot

#check paHilbertAcceptedProofObjectCodeSemantics

#check paHilbertAcceptedProofObjectSemanticLength_le_code
#print axioms paHilbertAcceptedProofObjectSemanticLength_le_code

#check paHilbertAcceptedProofObjectSemanticLength_le_acceptedNatCode
#print axioms paHilbertAcceptedProofObjectSemanticLength_le_acceptedNatCode

#check concretePAHilbertPowerBoundProofObjectSemanticLength_le_index
#print axioms concretePAHilbertPowerBoundProofObjectSemanticLength_le_index

#check no_concretePAHilbertPowerBoundProofObjectSemanticLowerBound
#print axioms no_concretePAHilbertPowerBoundProofObjectSemanticLowerBound

#check paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes
#print axioms paHilbertAcceptedProofObjectSemanticLowerBound_to_noSmallProofCodes

#check powerBoundLowerBound_and_paHilbertAcceptedNatCodeProofLengthExactness_to_noSmallProofCodes
#print axioms powerBoundLowerBound_and_paHilbertAcceptedNatCodeProofLengthExactness_to_noSmallProofCodes

#check paHilbertCheckerExactnessCore_to_checkedMinProofCodeStrongLowerBound
#print axioms paHilbertCheckerExactnessCore_to_checkedMinProofCodeStrongLowerBound

#check rootPolynomialBound_to_boundedArithmeticPolynomialBound
#print axioms rootPolynomialBound_to_boundedArithmeticPolynomialBound

#check boundedArithmeticPolynomialBound_to_rootPolynomialBound_opened
#print axioms boundedArithmeticPolynomialBound_to_rootPolynomialBound_opened

#check semanticBAProofLength_eq_of_minProofSizeOption_some
#print axioms semanticBAProofLength_eq_of_minProofSizeOption_some

#check semanticBAProofLength_calibration_to_option_length_calibration
#print axioms semanticBAProofLength_calibration_to_option_length_calibration

#check boundedEventualLowerBound_to_checkedMinProofCodeStrongLowerBound
#print axioms boundedEventualLowerBound_to_checkedMinProofCodeStrongLowerBound

#check bussPudlakLowerSource_to_checkedMinProofCodeStrongLowerBound
#print axioms bussPudlakLowerSource_to_checkedMinProofCodeStrongLowerBound

#check bussPudlakLowerSource_checkedMinProofCodeCalibration_to_noSmallProofCodes
#print axioms bussPudlakLowerSource_checkedMinProofCodeCalibration_to_noSmallProofCodes

#check bussPudlakLowerSource_checkedMinProofCodeCalibration_to_paHilbertAcceptedNatCode_noSmallProofCodes
#print axioms bussPudlakLowerSource_checkedMinProofCodeCalibration_to_paHilbertAcceptedNatCode_noSmallProofCodes

#check bussPudlakLowerSource_rootProofLengthCalibration_and_paHilbertExactness_to_noSmallProofCodes
#print axioms bussPudlakLowerSource_rootProofLengthCalibration_and_paHilbertExactness_to_noSmallProofCodes

#check boundedLowerSourceOfRootStrongRescaled_codeEq_and_paHilbertExactness_to_noSmallProofCodes
#print axioms boundedLowerSourceOfRootStrongRescaled_codeEq_and_paHilbertExactness_to_noSmallProofCodes

#check boundedEventualLowerBound_to_no_eventual_polynomial_proof_family
#print axioms boundedEventualLowerBound_to_no_eventual_polynomial_proof_family

#check no_eventual_polynomial_proof_family_to_boundedEventualLowerBound
#print axioms no_eventual_polynomial_proof_family_to_boundedEventualLowerBound

#check boundedEventualLowerBound_iff_no_eventual_polynomial_proof_family
#print axioms boundedEventualLowerBound_iff_no_eventual_polynomial_proof_family

#check boundedEventualLowerBound_iff_BAProofObjectStrongSizeLowerBound
#print axioms boundedEventualLowerBound_iff_BAProofObjectStrongSizeLowerBound

#check bussPudlakLowerSource_to_no_eventual_polynomial_proof_family
#print axioms bussPudlakLowerSource_to_no_eventual_polynomial_proof_family

#check bussPudlakLowerSource_to_BAProofObjectStrongSizeLowerBound
#print axioms bussPudlakLowerSource_to_BAProofObjectStrongSizeLowerBound

#check bussPudlakEventualLowerBound_iff_no_eventual_polynomial_proof_family
#print axioms bussPudlakEventualLowerBound_iff_no_eventual_polynomial_proof_family

#check bussPudlakEventualLowerBound_iff_BAProofObjectStrongSizeLowerBound
#print axioms bussPudlakEventualLowerBound_iff_BAProofObjectStrongSizeLowerBound

#check proofCodeSemantics_minProofCodeSize_proof_irrel
#print axioms proofCodeSemantics_minProofCodeSize_proof_irrel

#check baProofObjectRootCodeSemantics

#check baProofObjectRootCodeSemantics_minProofCodeSize_eq_semanticBAProofLength
#print axioms baProofObjectRootCodeSemantics_minProofCodeSize_eq_semanticBAProofLength

#check baProofObjectRootCodeSemantics_minProofCodeSize_eq_option
#print axioms baProofObjectRootCodeSemantics_minProofCodeSize_eq_option

#check BAOptionMinProofSizeBeatsPolynomial_to_checkedMinProofCodeStrongLowerBound
#print axioms BAOptionMinProofSizeBeatsPolynomial_to_checkedMinProofCodeStrongLowerBound

#check BAOptionMinProofSizeBeatsPolynomial_toNoAcceptedBelowCutoff
#print axioms BAOptionMinProofSizeBeatsPolynomial_toNoAcceptedBelowCutoff

#check BAProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound
#print axioms BAProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound

#check BAProofObjectStrongSizeLowerBound_to_noSmallProofCodes
#print axioms BAProofObjectStrongSizeLowerBound_to_noSmallProofCodes

#check canonicalRelabeledBussPudlak_baProofObjectSemantics_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalRelabeledBussPudlak_baProofObjectSemantics_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalLiteratureInput_baProofObjectSemantics_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalLiteratureInput_baProofObjectSemantics_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalRelabeledBussPudlak_baProofObjectSemantics_of_scaleInjective_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalRelabeledBussPudlak_baProofObjectSemantics_of_scaleInjective_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalLiteratureInput_baProofObjectSemantics_of_scaleInjective_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalLiteratureInput_baProofObjectSemantics_of_scaleInjective_to_shortestCheckedMinProofCodeGrowthObligation

#check internalPudlakScale_injective_of_strict
#print axioms internalPudlakScale_injective_of_strict

#check canonicalRelabeledBussPudlak_baProofObjectSemantics_of_scaleStrict_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalRelabeledBussPudlak_baProofObjectSemantics_of_scaleStrict_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalLiteratureInput_baProofObjectSemantics_of_scaleStrict_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalLiteratureInput_baProofObjectSemantics_of_scaleStrict_to_shortestCheckedMinProofCodeGrowthObligation

#check no_currentToyCanonicalLiteratureProofObjectGrowthPackage
#print axioms no_currentToyCanonicalLiteratureProofObjectGrowthPackage

#check BAProofObjectStrongSizeLowerBound_toNoAcceptedBelowCutoff
#print axioms BAProofObjectStrongSizeLowerBound_toNoAcceptedBelowCutoff

#check BACompleteProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound
#print axioms BACompleteProofObjectStrongSizeLowerBound_to_checkedMinProofCodeStrongLowerBound

#check BACompleteProofObjectStrongSizeLowerBound_to_noSmallProofCodes
#print axioms BACompleteProofObjectStrongSizeLowerBound_to_noSmallProofCodes

#check BACompleteProofObjectStrongSizeLowerBound_toNoAcceptedBelowCutoff
#print axioms BACompleteProofObjectStrongSizeLowerBound_toNoAcceptedBelowCutoff

#check no_eventual_polynomial_proof_family_to_checkedMinProofCodeStrongLowerBound
#print axioms no_eventual_polynomial_proof_family_to_checkedMinProofCodeStrongLowerBound

#check no_eventual_polynomial_proof_family_to_noSmallProofCodes
#print axioms no_eventual_polynomial_proof_family_to_noSmallProofCodes

#check no_eventual_polynomial_proof_family_toNoAcceptedBelowCutoff
#print axioms no_eventual_polynomial_proof_family_toNoAcceptedBelowCutoff

#check bussPudlakLowerSource_baProofObjectSemantics_to_checkedMinProofCodeStrongLowerBound
#print axioms bussPudlakLowerSource_baProofObjectSemantics_to_checkedMinProofCodeStrongLowerBound

#check bussPudlakLowerSource_baProofObjectSemantics_to_noSmallProofCodes
#print axioms bussPudlakLowerSource_baProofObjectSemantics_to_noSmallProofCodes

#check bussPudlakLowerSource_baProofObjectSemantics_toNoAcceptedBelowCutoff
#print axioms bussPudlakLowerSource_baProofObjectSemantics_toNoAcceptedBelowCutoff

#check bussPudlakLowerSource_baProofObjectSemantics_to_checkedMeasuredSearchGap
#print axioms bussPudlakLowerSource_baProofObjectSemantics_to_checkedMeasuredSearchGap

#check BAProofObjectAcceptedNatCodeBridge

#check PAHilbertCheckedTraceToBAProofObjectCompiler

#check PAHilbertCheckedTraceToBAProofObjectCompiler_to_BAProofObjectAcceptedNatCodeBridge
#print axioms PAHilbertCheckedTraceToBAProofObjectCompiler_to_BAProofObjectAcceptedNatCodeBridge

#check BAProofObjectAcceptedNatCodeLinearBridge

#check BAProofObjectAcceptedNatCodeBridge.toLinear
#print axioms BAProofObjectAcceptedNatCodeBridge.toLinear

#check PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler

#check PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge
#print axioms PAHilbertAcceptedNatCodeToPAProofObjectCodePlusTwoCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge

#check no_acceptedNatCodePAProofObjectCodePlusTwoCompiler_currentToy_of_acceptedCode
#print axioms no_acceptedNatCodePAProofObjectCodePlusTwoCompiler_currentToy_of_acceptedCode

#check PAHilbertCheckedTraceToBAProofObjectLinearCompiler

#check PAHilbertCheckedTraceToBAProofObjectLinearCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge
#print axioms PAHilbertCheckedTraceToBAProofObjectLinearCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge

#check PAHilbertCheckedTraceToBAProofObjectCompiler_to_LinearCompiler
#print axioms PAHilbertCheckedTraceToBAProofObjectCompiler_to_LinearCompiler

#check PAHilbertCheckedTraceToBussS21ProofObjectCompiler

#check PAHilbertCheckedTraceToBussS21ProofObjectCompiler_to_PACompiler
#print axioms PAHilbertCheckedTraceToBussS21ProofObjectCompiler_to_PACompiler

#check PAHilbertCheckedTraceToBussS21ProofObjectLinearCompiler

#check PAHilbertCheckedTraceToBussS21ProofObjectLinearCompiler_to_PACompiler
#print axioms PAHilbertCheckedTraceToBussS21ProofObjectLinearCompiler_to_PACompiler

#check PAHilbertCheckedTraceToBussS21ProofObjectCompiler_to_LinearCompiler
#print axioms PAHilbertCheckedTraceToBussS21ProofObjectCompiler_to_LinearCompiler

#check PAHilbertCheckedTraceConcreteVerifierRealization

#check PAHilbertCheckedTraceConcreteVerifierRealization_to_BussS21Compiler
#print axioms PAHilbertCheckedTraceConcreteVerifierRealization_to_BussS21Compiler

#check PAHilbertCheckedTraceConcreteVerifierLinearRealization

#check PAHilbertCheckedTraceConcreteVerifierLinearRealization_to_BussS21LinearCompiler
#print axioms PAHilbertCheckedTraceConcreteVerifierLinearRealization_to_BussS21LinearCompiler

#check PAHilbertCheckedTraceToCanonicalProofCertificateLinearCompiler

#check PAHilbertCheckedTraceToCanonicalProofCertificateLinearCompiler_to_ConcreteVerifierLinearRealization
#print axioms PAHilbertCheckedTraceToCanonicalProofCertificateLinearCompiler_to_ConcreteVerifierLinearRealization

#check no_canonicalProofCertificateCompiler_currentToy_of_checkedTrace
#print axioms no_canonicalProofCertificateCompiler_currentToy_of_checkedTrace

#check PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler

#check PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler

#check PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge
#print axioms PAHilbertAcceptedNatCodeToBussS21ProofObjectLinearCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge

#check no_acceptedNatCodeBussS21Compiler_currentToy_of_acceptedCode
#print axioms no_acceptedNatCodeBussS21Compiler_currentToy_of_acceptedCode

#check no_acceptedNatCodeCodePlusTwoCompiler_currentToy_of_acceptedCode
#print axioms no_acceptedNatCodeCodePlusTwoCompiler_currentToy_of_acceptedCode

#check acceptedNatCodeCodePlusTwoCompiler_currentToy_forces_no_acceptedCode
#print axioms acceptedNatCodeCodePlusTwoCompiler_currentToy_forces_no_acceptedCode

#check no_acceptedNatCodeCertificateLocalCompiler_currentToy_of_acceptedCode
#print axioms no_acceptedNatCodeCertificateLocalCompiler_currentToy_of_acceptedCode

#check no_acceptedNatCodeCertificateVerifierCompiler_currentToy_of_acceptedCode
#print axioms no_acceptedNatCodeCertificateVerifierCompiler_currentToy_of_acceptedCode

#check PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler_to_BussS21ProofObjectLinearCompiler
#print axioms PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler_to_BussS21ProofObjectLinearCompiler

#check PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge
#print axioms PAHilbertAcceptedNatCodeToCanonicalProofCertificateLinearCompiler_to_BAProofObjectAcceptedNatCodeLinearBridge

#check no_acceptedNatCodeCanonicalProofCertificateCompiler_currentToy_of_acceptedCode
#print axioms no_acceptedNatCodeCanonicalProofCertificateCompiler_currentToy_of_acceptedCode

#check PAHilbertCheckedTraceOperationalVerifierRealization

#check PAHilbertCheckedTraceOperationalVerifierRealization_to_ConcreteVerifierRealization
#print axioms PAHilbertCheckedTraceOperationalVerifierRealization_to_ConcreteVerifierRealization

#check PAHilbertCheckedTraceOperationalVerifierLinearRealization

#check PAHilbertCheckedTraceOperationalVerifierLinearRealization_to_BussS21LinearCompiler
#print axioms PAHilbertCheckedTraceOperationalVerifierLinearRealization_to_BussS21LinearCompiler

#check PAHilbertCheckedTraceVerifierAcceptedData

#check PAHilbertCheckedTraceVerifierState

#check paHilbertCheckedTraceVerifierMachine
#print axioms paHilbertCheckedTraceVerifierMachine

#check paHilbertCheckedTraceVerifierLinearRealization
#print axioms paHilbertCheckedTraceVerifierLinearRealization

#check checkedTraceVerifierAcceptedTraceOfData
#print axioms checkedTraceVerifierAcceptedTraceOfData

#check checkedTraceVerifierAcceptedTraceOfData_size
#print axioms checkedTraceVerifierAcceptedTraceOfData_size

#check checkedTraceVerifierAcceptedTrace_hasAcceptedData
#print axioms checkedTraceVerifierAcceptedTrace_hasAcceptedData

#check checkedTraceVerifierCompiler_produces_bussS21ProofObject_of_data
#print axioms checkedTraceVerifierCompiler_produces_bussS21ProofObject_of_data

#check checkedTraceVerifierCompiler_produces_size_le_two_bussS21ProofObject_of_data
#print axioms checkedTraceVerifierCompiler_produces_size_le_two_bussS21ProofObject_of_data

#check proofCertificateVerifierAcceptedTrace_size_eq_cert_size_add_two
#print axioms proofCertificateVerifierAcceptedTrace_size_eq_cert_size_add_two

#check proofCertificateVerifierCompiler_compile_size_eq_cert_size
#print axioms proofCertificateVerifierCompiler_compile_size_eq_cert_size

#check proofCertificateVerifierCompiler_compile_size_le_cert_size_add_two
#print axioms proofCertificateVerifierCompiler_compile_size_le_cert_size_add_two

#check PAHilbertAcceptedNatCodeCertificateState

#check paHilbertAcceptedNatCodeCertificateVerifierMachine
#print axioms paHilbertAcceptedNatCodeCertificateVerifierMachine

#check paHilbertAcceptedNatCodeCertificateTraceOfAccepted
#print axioms paHilbertAcceptedNatCodeCertificateTraceOfAccepted

#check paHilbertAcceptedNatCodeCertificateTraceOfAccepted_size
#print axioms paHilbertAcceptedNatCodeCertificateTraceOfAccepted_size

#check PAHilbertAcceptedNatCodeCertificateLocalS21Compiler

#check PAHilbertAcceptedNatCodeCertificateOperationalCompiler_to_LocalS21Compiler
#print axioms PAHilbertAcceptedNatCodeCertificateOperationalCompiler_to_LocalS21Compiler

#check PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler

#check PAHilbertAcceptedNatCodeCertificateLocalS21Compiler_to_CodePlusTwoCompiler
#print axioms PAHilbertAcceptedNatCodeCertificateLocalS21Compiler_to_CodePlusTwoCompiler

#check PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler_to_LinearCompiler
#print axioms PAHilbertAcceptedNatCodeToBussS21ProofObjectCodePlusTwoCompiler_to_LinearCompiler

#check PAHilbertAcceptedNatCodeCertificateLocalS21Compiler_to_BussS21ProofObjectLinearCompiler
#print axioms PAHilbertAcceptedNatCodeCertificateLocalS21Compiler_to_BussS21ProofObjectLinearCompiler

#check PAHilbertAcceptedNatCodeCertificateVerifierCompiler_to_BussS21ProofObjectLinearCompiler
#print axioms PAHilbertAcceptedNatCodeCertificateVerifierCompiler_to_BussS21ProofObjectLinearCompiler

#check no_checkedTraceVerifierCompiler_currentToy_of_acceptedData
#print axioms no_checkedTraceVerifierCompiler_currentToy_of_acceptedData

#check no_checkedTraceVerifierCompiler_currentToy_of_acceptsInput
#print axioms no_checkedTraceVerifierCompiler_currentToy_of_acceptsInput

#check checkedTraceVerifierCompiler_currentToy_forces_no_acceptsInput
#print axioms checkedTraceVerifierCompiler_currentToy_forces_no_acceptsInput

#check BAProofObjectStrongSizeLowerBound_and_acceptedNatCodeBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms BAProofObjectStrongSizeLowerBound_and_acceptedNatCodeBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check BAProofObjectStrongSizeLowerBound_and_acceptedNatCodeLinearBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms BAProofObjectStrongSizeLowerBound_and_acceptedNatCodeLinearBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check bussPudlakLowerSource_and_acceptedNatCodeBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms bussPudlakLowerSource_and_acceptedNatCodeBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check bussPudlakLowerSource_and_acceptedNatCodeBridge_to_noSmallProofCodes
#print axioms bussPudlakLowerSource_and_acceptedNatCodeBridge_to_noSmallProofCodes

#check bussPudlakLowerSource_semanticLength_and_acceptedNatCodeBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms bussPudlakLowerSource_semanticLength_and_acceptedNatCodeBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check bussPudlakLowerSource_semanticLength_and_acceptedNatCodeLinearBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms bussPudlakLowerSource_semanticLength_and_acceptedNatCodeLinearBridge_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check canonicalSourceCalibration_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms canonicalSourceCalibration_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check canonicalLiteratureInput_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms canonicalLiteratureInput_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check canonicalSourceCalibration_and_acceptedNatCodeCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms canonicalSourceCalibration_and_acceptedNatCodeCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check canonicalLiteratureInput_and_acceptedNatCodeCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms canonicalLiteratureInput_and_acceptedNatCodeCodePlusTwoCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check canonicalSourceCalibration_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms canonicalSourceCalibration_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check canonicalLiteratureInput_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms canonicalLiteratureInput_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check canonicalLiteratureInput_and_acceptedNatCodeCertificateLocalCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms canonicalLiteratureInput_and_acceptedNatCodeCertificateLocalCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check canonicalSourceCalibration_and_acceptedNatCodeCertificateVerifierCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms canonicalSourceCalibration_and_acceptedNatCodeCertificateVerifierCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check canonicalLiteratureInput_and_acceptedNatCodeCertificateVerifierCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound
#print axioms canonicalLiteratureInput_and_acceptedNatCodeCertificateVerifierCompiler_to_paHilbertAcceptedProofObjectSemanticLowerBound

#check bussPudlakLowerSource_semanticLength_and_acceptedNatCodeBridge_to_noSmallProofCodes
#print axioms bussPudlakLowerSource_semanticLength_and_acceptedNatCodeBridge_to_noSmallProofCodes

#check bussPudlakLowerSource_semanticLength_and_acceptedNatCodeLinearBridge_to_noSmallProofCodes
#print axioms bussPudlakLowerSource_semanticLength_and_acceptedNatCodeLinearBridge_to_noSmallProofCodes

#check canonicalSourceCalibration_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_noSmallProofCodes

#check canonicalLiteratureInput_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_noSmallProofCodes
#print axioms canonicalLiteratureInput_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_noSmallProofCodes

#check canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_noSmallProofCodes

#check canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_noSmallProofCodes
#print axioms canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_noSmallProofCodes

#check canonicalSourceCalibration_and_acceptedNatCodeCodePlusTwoCompiler_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_acceptedNatCodeCodePlusTwoCompiler_to_noSmallProofCodes

#check canonicalLiteratureInput_and_acceptedNatCodeCodePlusTwoCompiler_to_noSmallProofCodes
#print axioms canonicalLiteratureInput_and_acceptedNatCodeCodePlusTwoCompiler_to_noSmallProofCodes

#check canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_noSmallProofCodes

#check canonicalLiteratureInput_and_acceptedNatCodeCertificateLocalCompiler_to_noSmallProofCodes
#print axioms canonicalLiteratureInput_and_acceptedNatCodeCertificateLocalCompiler_to_noSmallProofCodes

#check canonicalSourceCalibration_and_acceptedNatCodeCertificateVerifierCompiler_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_acceptedNatCodeCertificateVerifierCompiler_to_noSmallProofCodes

#check canonicalLiteratureInput_and_acceptedNatCodeCertificateVerifierCompiler_to_noSmallProofCodes
#print axioms canonicalLiteratureInput_and_acceptedNatCodeCertificateVerifierCompiler_to_noSmallProofCodes

#check canonicalSourceCalibration_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_noSmallProofCodes

#check canonicalLiteratureInput_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_noSmallProofCodes
#print axioms canonicalLiteratureInput_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_noSmallProofCodes

#check bussPudlakLowerSource_semanticLength_and_traceCompiler_to_noSmallProofCodes
#print axioms bussPudlakLowerSource_semanticLength_and_traceCompiler_to_noSmallProofCodes

#check bussPudlakLowerSource_semanticLength_and_traceLinearCompiler_to_noSmallProofCodes
#print axioms bussPudlakLowerSource_semanticLength_and_traceLinearCompiler_to_noSmallProofCodes

#check canonicalSourceCalibration_and_traceCompiler_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_traceCompiler_to_noSmallProofCodes

#check canonicalSourceCalibration_and_traceLinearCompiler_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_traceLinearCompiler_to_noSmallProofCodes

#check BussPudlakTheorem5CanonicalRelabeledPASemanticLiteratureInput

#check bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput
#print axioms bussPudlakTheorem5CanonicalRelabeledPASemantic_literatureInput

#check canonicalLiteratureInput_and_traceCompiler_to_noSmallProofCodes
#print axioms canonicalLiteratureInput_and_traceCompiler_to_noSmallProofCodes

#check canonicalSourceCalibration_and_s21TraceCompiler_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_s21TraceCompiler_to_noSmallProofCodes

#check canonicalSourceCalibration_and_s21TraceLinearCompiler_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_s21TraceLinearCompiler_to_noSmallProofCodes

#check canonicalLiteratureInput_and_s21TraceCompiler_to_noSmallProofCodes
#print axioms canonicalLiteratureInput_and_s21TraceCompiler_to_noSmallProofCodes

#check canonicalSourceCalibration_and_concreteVerifierTraceRealization_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_concreteVerifierTraceRealization_to_noSmallProofCodes

#check canonicalSourceCalibration_and_concreteVerifierTraceLinearRealization_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_concreteVerifierTraceLinearRealization_to_noSmallProofCodes

#check canonicalLiteratureInput_and_concreteVerifierTraceRealization_to_noSmallProofCodes
#print axioms canonicalLiteratureInput_and_concreteVerifierTraceRealization_to_noSmallProofCodes

#check canonicalLiteratureInput_and_concreteVerifierTraceLinearRealization_to_noSmallProofCodes
#print axioms canonicalLiteratureInput_and_concreteVerifierTraceLinearRealization_to_noSmallProofCodes

#check canonicalSourceCalibration_and_operationalVerifierRealization_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_operationalVerifierRealization_to_noSmallProofCodes

#check canonicalSourceCalibration_and_operationalVerifierLinearRealization_to_noSmallProofCodes
#print axioms canonicalSourceCalibration_and_operationalVerifierLinearRealization_to_noSmallProofCodes

#check canonicalLiteratureInput_and_operationalVerifierRealization_to_noSmallProofCodes
#print axioms canonicalLiteratureInput_and_operationalVerifierRealization_to_noSmallProofCodes

#check canonicalLiteratureInput_and_operationalVerifierLinearRealization_to_noSmallProofCodes
#print axioms canonicalLiteratureInput_and_operationalVerifierLinearRealization_to_noSmallProofCodes

#check canonicalSourceCalibration_and_traceCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_traceCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalSourceCalibration_and_traceLinearCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_traceLinearCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalSourceCalibration_and_concreteVerifierTraceLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_concreteVerifierTraceLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalSourceCalibration_and_operationalVerifierLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_operationalVerifierLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalSourceCalibration_and_checkedTraceVerifierCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_checkedTraceVerifierCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalLiteratureInput_and_checkedTraceVerifierCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalLiteratureInput_and_checkedTraceVerifierCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalSourceCalibration_and_proofCertificateVerifierRealization_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_proofCertificateVerifierRealization_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalSourceCalibration_and_proofCertificateVerifierLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_proofCertificateVerifierLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalSourceCalibration_and_canonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_canonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalSourceCalibration_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalSourceCalibration_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_acceptedNatCodeBussS21Compiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalSourceCalibration_and_acceptedNatCodeCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_acceptedNatCodeCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_acceptedNatCodeCertificateLocalCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalSourceCalibration_and_acceptedNatCodeCertificateVerifierCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalSourceCalibration_and_acceptedNatCodeCertificateVerifierCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalLiteratureInput_and_proofCertificateVerifierRealization_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalLiteratureInput_and_proofCertificateVerifierRealization_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalLiteratureInput_and_proofCertificateVerifierLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalLiteratureInput_and_proofCertificateVerifierLinearRealization_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalLiteratureInput_and_canonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalLiteratureInput_and_canonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalLiteratureInput_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalLiteratureInput_and_acceptedNatCodeCanonicalProofCertificateCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalLiteratureInput_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalLiteratureInput_and_acceptedNatCodePAProofObjectCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalLiteratureInput_and_acceptedNatCodeBussS21Compiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalLiteratureInput_and_acceptedNatCodeCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalLiteratureInput_and_acceptedNatCodeCodePlusTwoCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalLiteratureInput_and_acceptedNatCodeCertificateLocalCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalLiteratureInput_and_acceptedNatCodeCertificateLocalCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check canonicalLiteratureInput_and_acceptedNatCodeCertificateVerifierCompiler_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms canonicalLiteratureInput_and_acceptedNatCodeCertificateVerifierCompiler_to_shortestCheckedMinProofCodeGrowthObligation

#check BAProofObjectToAcceptedNatCodeBridge

#check baProofObjectNoAcceptedBelow_toPAHilbertAcceptedNatCodeRejectionData
#print axioms baProofObjectNoAcceptedBelow_toPAHilbertAcceptedNatCodeRejectionData

#check bussPudlakLowerSource_baProofObjectBridge_toPAHilbertAcceptedNatCodeRejectionData
#print axioms bussPudlakLowerSource_baProofObjectBridge_toPAHilbertAcceptedNatCodeRejectionData

#check paHilbertAcceptedNatCodeRejectionData_to_BAProofObjectStrongSizeLowerBound
#print axioms paHilbertAcceptedNatCodeRejectionData_to_BAProofObjectStrongSizeLowerBound

#check paHilbertAcceptedNatCodeRejectionData_to_BACompleteProofObjectStrongSizeLowerBound
#print axioms paHilbertAcceptedNatCodeRejectionData_to_BACompleteProofObjectStrongSizeLowerBound

#check no_currentToyFiniteConsistencyProofObjectCompleteness
#print axioms no_currentToyFiniteConsistencyProofObjectCompleteness

#check no_currentToyBACompleteProofObjectStrongSizeLowerBound_finiteConsistency
#print axioms no_currentToyBACompleteProofObjectStrongSizeLowerBound_finiteConsistency

#check no_currentToyBAProofObjectAcceptedNatCodeBridge_concretePowerBound
#print axioms no_currentToyBAProofObjectAcceptedNatCodeBridge_concretePowerBound

#check no_currentToyPAProofObjectCodePlusTwoCompiler_concretePowerBound
#print axioms no_currentToyPAProofObjectCodePlusTwoCompiler_concretePowerBound

#check powTwoLowerEnvelope_eventually_gt_polynomial
#print axioms powTwoLowerEnvelope_eventually_gt_polynomial

#check powTwoLowerEnvelope_not_polynomial_bound
#print axioms powTwoLowerEnvelope_not_polynomial_bound

#check internalScale_eventually_lt_powTwo
#print axioms internalScale_eventually_lt_powTwo

#check no_internalScale_eventually_ge_powTwo
#print axioms no_internalScale_eventually_ge_powTwo

#check eventuallyEveryAcceptedCodeAbovePowTwo_to_checkedMinProofCodeStrongLowerBound
#print axioms eventuallyEveryAcceptedCodeAbovePowTwo_to_checkedMinProofCodeStrongLowerBound

#check eventuallyEveryAcceptedCodeAbovePowTwo_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms eventuallyEveryAcceptedCodeAbovePowTwo_to_shortestCheckedMinProofCodeGrowthObligation

#check checkedMinStrongLowerBound_forbids_polynomialCheckedTargetProjection
#print axioms checkedMinStrongLowerBound_forbids_polynomialCheckedTargetProjection

#check no_currentToyBussPudlakLowerSource_semanticFiniteConsistency
#print axioms no_currentToyBussPudlakLowerSource_semanticFiniteConsistency

#check no_projectPublicCollisionCertificateBundle_currentToySemantics
#print axioms no_projectPublicCollisionCertificateBundle_currentToySemantics

#check no_projectConcreteCertificateObligation_currentToySemantics
#print axioms no_projectConcreteCertificateObligation_currentToySemantics

#check no_nonempty_projectPublicCollisionCertificateBundle_currentToySemantics
#print axioms no_nonempty_projectPublicCollisionCertificateBundle_currentToySemantics

#check no_nonempty_projectConcreteCertificateObligation_currentToySemantics
#print axioms no_nonempty_projectConcreteCertificateObligation_currentToySemantics

#check no_projectPublicCollisionCompletionObligation_currentToySemantics
#print axioms no_projectPublicCollisionCompletionObligation_currentToySemantics

#check month6CheckedReplacement_forces_partialConsistency_minChecked_linear_currentRoot
#print axioms month6CheckedReplacement_forces_partialConsistency_minChecked_linear_currentRoot

#check month6CheckedReplacement_forces_reflectionGraft_minChecked_linear_currentRoot
#print axioms month6CheckedReplacement_forces_reflectionGraft_minChecked_linear_currentRoot

#check _root_.MiniHilbert.FormulaCodeHilbertInterpretation.localHilbertProofCodeSemantics_source_min_eq
#print axioms _root_.MiniHilbert.FormulaCodeHilbertInterpretation.localHilbertProofCodeSemantics_source_min_eq

#check _root_.MiniHilbert.FormulaCodeHilbertInterpretation.localHilbertProofCodeSemantics_target_min_eq
#print axioms _root_.MiniHilbert.FormulaCodeHilbertInterpretation.localHilbertProofCodeSemantics_target_min_eq

#check strongProofLengthLowerBoundWitness
#print axioms strongProofLengthLowerBoundWitness

#check strongProofLengthLowerBoundWitness_spec
#print axioms strongProofLengthLowerBoundWitness_spec

#check strongProofLengthLowerBound_toNoAcceptedBelowCutoff
#print axioms strongProofLengthLowerBound_toNoAcceptedBelowCutoff

#check computableFiniteSearchExclusion_toNoAcceptedBelowCutoff
#print axioms computableFiniteSearchExclusion_toNoAcceptedBelowCutoff

#check ProofLengthFreeNoAcceptedBelowClosureTarget

#check ProofLengthCalibratedStrongLowerBoundNoAcceptedCore

#check ProofLengthCalibratedStrongLowerBoundNoAcceptedCore.toNoAcceptedBelow
#print axioms ProofLengthCalibratedStrongLowerBoundNoAcceptedCore.toNoAcceptedBelow

#check proofLengthCalibratedStrongLowerBoundNoAcceptedCore_to_target
#print axioms proofLengthCalibratedStrongLowerBoundNoAcceptedCore_to_target

#check no_proofLengthCalibratedStrongLowerBoundNoAcceptedCore_currentRoot
#print axioms no_proofLengthCalibratedStrongLowerBoundNoAcceptedCore_currentRoot

#check bussPudlakTheorem5PALowerBoundSource_lower_bound_is_field
#print axioms bussPudlakTheorem5PALowerBoundSource_lower_bound_is_field

#check proofLengthFreeNoAcceptedBelowClosureTarget_to_checkedMeasuredSearchGap
#print axioms proofLengthFreeNoAcceptedBelowClosureTarget_to_checkedMeasuredSearchGap

#check proofLengthFreeNoAcceptedBelowClosureTarget_to_checkedMinProofCodeStrongLowerBound
#print axioms proofLengthFreeNoAcceptedBelowClosureTarget_to_checkedMinProofCodeStrongLowerBound

#check paHilbertAcceptedNatCodeRejectionData_toNoAcceptedBelowCutoff
#print axioms paHilbertAcceptedNatCodeRejectionData_toNoAcceptedBelowCutoff

#check paHilbertAcceptedNatCodeRejectionData_ofCheckerExtractor
#print axioms paHilbertAcceptedNatCodeRejectionData_ofCheckerExtractor

#check PAHilbertCanonicalAcceptedNatCodeNoSmallCore

#check noSmallProofCodes_toPAHilbertAcceptedNatCodeRejectionData
#print axioms noSmallProofCodes_toPAHilbertAcceptedNatCodeRejectionData

#check PAHilbertCanonicalAcceptedNatCodeNoSmallCore.toNoAcceptedBelowCutoff
#print axioms PAHilbertCanonicalAcceptedNatCodeNoSmallCore.toNoAcceptedBelowCutoff

#check PAHilbertCanonicalAcceptedNatCodeNoSmallCore.toProofLengthFreeNoAcceptedBelowClosureTarget
#print axioms PAHilbertCanonicalAcceptedNatCodeNoSmallCore.toProofLengthFreeNoAcceptedBelowClosureTarget

#check PAHilbertCanonicalAcceptedNatCodeNoSmallCore.to_checkedMinProofCodeStrongLowerBound
#print axioms PAHilbertCanonicalAcceptedNatCodeNoSmallCore.to_checkedMinProofCodeStrongLowerBound

#check PAHilbertCanonicalAcceptedNatCodeNoSmallCore.to_shortestCheckedMinProofCodeGrowthObligation
#print axioms PAHilbertCanonicalAcceptedNatCodeNoSmallCore.to_shortestCheckedMinProofCodeGrowthObligation

#check PAHilbertCanonicalAcceptedNatCodeNoSmallCore.to_BACompleteProofObjectStrongSizeLowerBound
#print axioms PAHilbertCanonicalAcceptedNatCodeNoSmallCore.to_BACompleteProofObjectStrongSizeLowerBound

#check noSmallProofCodes_toPAHilbertCanonicalAcceptedNatCodeNoSmallCore
#print axioms noSmallProofCodes_toPAHilbertCanonicalAcceptedNatCodeNoSmallCore

#check noSmallProofCodes_toPAHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget
#print axioms noSmallProofCodes_toPAHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget

#check paHilbertAcceptedProofObjectSemanticLowerBound_toCanonicalAcceptedNatCodeNoSmallCore
#print axioms paHilbertAcceptedProofObjectSemanticLowerBound_toCanonicalAcceptedNatCodeNoSmallCore

#check paHilbertAcceptedProofObjectSemanticLowerBound_toCanonicalAcceptedNatCodeNoSmallClosureTarget
#print axioms paHilbertAcceptedProofObjectSemanticLowerBound_toCanonicalAcceptedNatCodeNoSmallClosureTarget

#check powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_toCanonicalAcceptedNatCodeNoSmallCore
#print axioms powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_toCanonicalAcceptedNatCodeNoSmallCore

#check powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_toCanonicalAcceptedNatCodeNoSmallClosureTarget
#print axioms powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_toCanonicalAcceptedNatCodeNoSmallClosureTarget

#check powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms powerBoundLowerBound_and_paHilbertAcceptedNatCode_soundness_to_shortestCheckedMinProofCodeGrowthObligation

#check powerBoundLowerBound_and_paHilbertAcceptedProofObjectLengthSound_toCanonicalAcceptedNatCodeNoSmallCore
#print axioms powerBoundLowerBound_and_paHilbertAcceptedProofObjectLengthSound_toCanonicalAcceptedNatCodeNoSmallCore

#check powerBoundLowerBound_and_paHilbertAcceptedProofObjectLengthSound_to_shortestCheckedMinProofCodeGrowthObligation
#print axioms powerBoundLowerBound_and_paHilbertAcceptedProofObjectLengthSound_to_shortestCheckedMinProofCodeGrowthObligation

#check powerBoundLowerBound_and_paHilbertAcceptedNatCodeProofLengthExactness_toCanonicalAcceptedNatCodeNoSmallCore
#print axioms powerBoundLowerBound_and_paHilbertAcceptedNatCodeProofLengthExactness_toCanonicalAcceptedNatCodeNoSmallCore

#check PAHilbertAcceptedNatCodeExtractorNoSmallCore

#check PAHilbertAcceptedNatCodeExtractorNoSmallCore.to_checkedMinProofCodeStrongLowerBound
#print axioms PAHilbertAcceptedNatCodeExtractorNoSmallCore.to_checkedMinProofCodeStrongLowerBound

#check PAHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget

#check paHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget_to_checkedMinProofCodeStrongLowerBound
#print axioms paHilbertCanonicalAcceptedNatCodeNoSmallClosureTarget_to_checkedMinProofCodeStrongLowerBound

#check NextStageRealPAHilbertNoSmallCodeTarget

#check nextStageRealPAHilbertNoSmallCodeTarget_to_shortestGrowthObligation
#print axioms nextStageRealPAHilbertNoSmallCodeTarget_to_shortestGrowthObligation

#check no_concretePAHilbertPowerBoundAcceptedNatCodeRejectionData
#print axioms no_concretePAHilbertPowerBoundAcceptedNatCodeRejectionData

#check no_concretePAHilbertPowerBoundCanonicalAcceptedNatCodeNoSmallCore
#print axioms no_concretePAHilbertPowerBoundCanonicalAcceptedNatCodeNoSmallCore

#check no_concretePAHilbertPowerBoundAcceptedNatCodeCheckerExtractor
#print axioms no_concretePAHilbertPowerBoundAcceptedNatCodeCheckerExtractor

#check no_concretePAHilbertPowerBoundRejectionExtractorInput
#print axioms no_concretePAHilbertPowerBoundRejectionExtractorInput

#check no_concretePAHilbertPowerBoundFourPiece
#print axioms no_concretePAHilbertPowerBoundFourPiece

#check SizeFilteredSmallCodeSearch

#check noAcceptedBelowCutoff_toComputableFiniteSearchExclusion
#print axioms noAcceptedBelowCutoff_toComputableFiniteSearchExclusion

#check OpenedGapFreeTheorem5ClosureCore

#check OpenedGapFreeTheorem5ClosureCore.toComputableFiniteSearchNoSmallCore
#print axioms OpenedGapFreeTheorem5ClosureCore.toComputableFiniteSearchNoSmallCore

#check OpenedGapFreeTheorem5ClosureTarget

#check openedGapFreeTheorem5ClosureTarget_to_gapFreeTheorem5ClosureTarget
#print axioms openedGapFreeTheorem5ClosureTarget_to_gapFreeTheorem5ClosureTarget

#check no_openedGapFreeTheorem5ClosureTarget_currentRoot
#print axioms no_openedGapFreeTheorem5ClosureTarget_currentRoot

#check cleanUpperProvider_submissionRoute
#print axioms cleanUpperProvider_submissionRoute

#check cleanTailGapFrontier_submissionRoute
#print axioms cleanTailGapFrontier_submissionRoute

#check eventuallyStrictLength_noTailGap_submissionRoute
#print axioms eventuallyStrictLength_noTailGap_submissionRoute

#check singletonMonomialLowerBound_submissionRoute
#print axioms singletonMonomialLowerBound_submissionRoute

#check tailGapInput_tail_gap_is_field
#print axioms tailGapInput_tail_gap_is_field

#check tailGapInput_toSearchInput_gap_eq_tail_gap
#print axioms tailGapInput_toSearchInput_gap_eq_tail_gap

#check frontier_tail_gap_is_field
#print axioms frontier_tail_gap_is_field

#check cleanComputedN_formula_reads_tail_gap
#print axioms cleanComputedN_formula_reads_tail_gap

#check singletonMonomialLowerBound_conjSource_obligation_impossible
#print axioms singletonMonomialLowerBound_conjSource_obligation_impossible

#check lowerGap_from_extractor_exactness_is_conditional
#print axioms lowerGap_from_extractor_exactness_is_conditional

#check ActualProofLengthSearchGapTarget
#check ActualProofLengthPointwiseSearchGapTarget

#check noSmallCore_to_actualProofLengthPointwiseSearchGapTarget
#print axioms noSmallCore_to_actualProofLengthPointwiseSearchGapTarget

#check checkerExtractorExactness_to_actualProofLengthPointwiseSearchGapTarget
#print axioms checkerExtractorExactness_to_actualProofLengthPointwiseSearchGapTarget

#check _root_.proof_length

#check _root_.rootSemanticProofLength_eq_rootFormulaCodeSize
#print axioms _root_.rootSemanticProofLength_eq_rootFormulaCodeSize

#check _root_.proof_length_eq_rootFormulaCodeSize
#print axioms _root_.proof_length_eq_rootFormulaCodeSize

#check _root_.rootStructuralProofLength_eq_minProofCodeSize
#print axioms _root_.rootStructuralProofLength_eq_minProofCodeSize

#check actualProofLengthMeasured_currentRoot_eq_scale_add_twelve
#print axioms actualProofLengthMeasured_currentRoot_eq_scale_add_twelve

#check actualProofLengthMeasured_currentRoot_polynomial
#print axioms actualProofLengthMeasured_currentRoot_polynomial

#check no_actualProofLengthSearchGapTarget_currentRoot
#print axioms no_actualProofLengthSearchGapTarget_currentRoot

#check no_actualProofLengthPointwiseSearchGapTarget_currentRoot
#print axioms no_actualProofLengthPointwiseSearchGapTarget_currentRoot

#check no_finalResidualInput_cutoffSelfCollision
#print axioms no_finalResidualInput_cutoffSelfCollision

#check no_finalByIndexResidualInput_cutoffSelfCollision
#print axioms no_finalByIndexResidualInput_cutoffSelfCollision

#check no_finalScaleInjectiveByIndexResidualInput_cutoffSelfCollision
#print axioms no_finalScaleInjectiveByIndexResidualInput_cutoffSelfCollision

#check no_finalStrictScaleByIndexResidualInput_cutoffSelfCollision
#print axioms no_finalStrictScaleByIndexResidualInput_cutoffSelfCollision

#check no_finalBoundedStrictScaleByIndexResidualInput_cutoffSelfCollision
#print axioms no_finalBoundedStrictScaleByIndexResidualInput_cutoffSelfCollision

#check no_checkerRejectionExtractor_of_checkedMeasured_polynomial
#print axioms no_checkerRejectionExtractor_of_checkedMeasured_polynomial

#check no_checkerRejectionExtractor_of_minProofCodeSizeAt_polynomial
#print axioms no_checkerRejectionExtractor_of_minProofCodeSizeAt_polynomial

#check calibratedFourPiece_checkedMeasuredSearchGap
#print axioms calibratedFourPiece_checkedMeasuredSearchGap

#check calibratedFourPiece_checkedMeasuredSearchGap_witness_eq_rejectionSearch
#print axioms calibratedFourPiece_checkedMeasuredSearchGap_witness_eq_rejectionSearch

#check SizeFilteredNoSmallClosureTarget

#check sizeFilteredNoSmallClosureTarget_to_checkedMeasuredSearchGap
#print axioms sizeFilteredNoSmallClosureTarget_to_checkedMeasuredSearchGap

#check calibratedRejectionSearch_checkedMeasuredSearchGap
#print axioms calibratedRejectionSearch_checkedMeasuredSearchGap

#check calibratedRejectionSearch_checkedMeasuredSearchGap_witness_eq
#print axioms calibratedRejectionSearch_checkedMeasuredSearchGap_witness_eq

#check calibratedAcceptedCodeSizeLowerBound_iff_checkedMeasured_gt
#print axioms calibratedAcceptedCodeSizeLowerBound_iff_checkedMeasured_gt

#check calibratedRejectionSearch_checkedMeasured_gt_at_witness
#print axioms calibratedRejectionSearch_checkedMeasured_gt_at_witness

#check calibratedRejectionSearch_acceptedCodeSize_gt_at_witness
#print axioms calibratedRejectionSearch_acceptedCodeSize_gt_at_witness

#check calibratedRejectionSearch_toCanonicalSearchCore
#print axioms calibratedRejectionSearch_toCanonicalSearchCore

#check calibratedRejectionSearch_toCanonicalSearchCore_witness_eq
#print axioms calibratedRejectionSearch_toCanonicalSearchCore_witness_eq

#check concretePAHilbertPowerBoundRejectsBelow_iff_noAcceptedBelow
#print axioms concretePAHilbertPowerBoundRejectsBelow_iff_noAcceptedBelow

#check ConcretePAHilbertPowerBoundCalibratedNoAcceptedCodeSearchInput

#check calibratedRejectionSearch_toNoAcceptedCodeSearch
#print axioms calibratedRejectionSearch_toNoAcceptedCodeSearch

#check calibratedNoAcceptedCodeSearch_toRejectionSearch
#print axioms calibratedNoAcceptedCodeSearch_toRejectionSearch

#check calibratedRejectionSearch_toNoAcceptedCodeSearch_witness_eq
#print axioms calibratedRejectionSearch_toNoAcceptedCodeSearch_witness_eq

#check calibratedNoAcceptedCodeSearch_checkedMeasuredSearchGap
#print axioms calibratedNoAcceptedCodeSearch_checkedMeasuredSearchGap

#check calibratedNoAcceptedCodeSearch_checkedMeasuredSearchGap_witness_eq
#print axioms calibratedNoAcceptedCodeSearch_checkedMeasuredSearchGap_witness_eq

#check calibratedNoAcceptedCodeSearch_cutoff_le_canonicalLength
#print axioms calibratedNoAcceptedCodeSearch_cutoff_le_canonicalLength

#check calibratedNoAcceptedCodeSearch_polynomialUpper_lt_canonicalLength
#print axioms calibratedNoAcceptedCodeSearch_polynomialUpper_lt_canonicalLength

#check no_calibratedNoAcceptedCodeSearch_of_canonicalLength_polynomial
#print axioms no_calibratedNoAcceptedCodeSearch_of_canonicalLength_polynomial

#check SizeFilteredNoAcceptedCodeSearchPolynomialLengthTarget

#check no_sizeFilteredNoAcceptedCodeSearchPolynomialLengthTarget
#print axioms no_sizeFilteredNoAcceptedCodeSearchPolynomialLengthTarget

#check nativeIdentityLength_polynomial
#print axioms nativeIdentityLength_polynomial

#check nativePowerBoundCheckedMeasured_le_index
#print axioms nativePowerBoundCheckedMeasured_le_index

#check no_concretePAHilbertPowerBound_noSmallAccepted_at_succ
#print axioms no_concretePAHilbertPowerBound_noSmallAccepted_at_succ

#check no_concretePAHilbertPowerBound_noSmallProofCodeForFormulaCode_at_succ
#print axioms no_concretePAHilbertPowerBound_noSmallProofCodeForFormulaCode_at_succ

#check nativePowerBoundCheckedMeasured_polynomial
#print axioms nativePowerBoundCheckedMeasured_polynomial

#check no_nativePowerBoundCheckedMeasuredSearchGap
#print axioms no_nativePowerBoundCheckedMeasuredSearchGap

#check no_nativePowerBoundCheckedMinProofCodeStrongLowerBound
#print axioms no_nativePowerBoundCheckedMinProofCodeStrongLowerBound

#check no_nativePowerBoundShortestCheckedMinProofCodeGrowthObligation
#print axioms no_nativePowerBoundShortestCheckedMinProofCodeGrowthObligation

#check NativeIdentityNoAcceptedCodeSearchTarget

#check no_nativeIdentityNoAcceptedCodeSearchTarget
#print axioms no_nativeIdentityNoAcceptedCodeSearchTarget

#check CorrectedCanonicalCnBoxLowerBoundClosureTarget

#check correctedCanonicalCnBoxPABox_length_eq_semanticFiniteConsistency
#print axioms correctedCanonicalCnBoxPABox_length_eq_semanticFiniteConsistency

#check correctedCanonicalCnBoxLowerBoundClosureTarget_to_gap
#print axioms correctedCanonicalCnBoxLowerBoundClosureTarget_to_gap

#check correctedCanonicalCnBoxLowerBoundClosureTarget_to_eventualLowerBound
#print axioms correctedCanonicalCnBoxLowerBoundClosureTarget_to_eventualLowerBound

#check no_correctedCanonicalExactConstructorCalibration
#print axioms no_correctedCanonicalExactConstructorCalibration

#check boundedPolynomialBound_to_rootPolynomialBound
#print axioms boundedPolynomialBound_to_rootPolynomialBound

#check boundedLowerSourceOfRootStrongRescaled
#print axioms boundedLowerSourceOfRootStrongRescaled

#check boundedLowerSourceFromRootLiterature
#print axioms boundedLowerSourceFromRootLiterature

#check boundedLowerSourceFromRootLiterature_scale_eq
#print axioms boundedLowerSourceFromRootLiterature_scale_eq

#check boundedLowerSourceFromRootLiterature_pa_length_eq
#print axioms boundedLowerSourceFromRootLiterature_pa_length_eq

#check RootLiteratureCanonicalCnBoxCalibrationTarget

#check rootLiteratureCanonicalCalibration_to_correctedClosureTarget
#print axioms rootLiteratureCanonicalCalibration_to_correctedClosureTarget

#check rootLiteratureCanonicalCalibration_to_gap
#print axioms rootLiteratureCanonicalCalibration_to_gap

#check no_strongProofLengthLowerBound_of_currentMeasuredPolynomial
#print axioms no_strongProofLengthLowerBound_of_currentMeasuredPolynomial

#check no_internalPudlakTheorem5PowerBoundLowerBound_currentRoot
#print axioms no_internalPudlakTheorem5PowerBoundLowerBound_currentRoot

#check no_internalPudlakTheorem5LowerBoundCore_currentRoot
#print axioms no_internalPudlakTheorem5LowerBoundCore_currentRoot

#check no_nonempty_internalPudlakTheorem5LowerBoundCore_currentRoot
#print axioms no_nonempty_internalPudlakTheorem5LowerBoundCore_currentRoot

#check no_internalPudlakTheorem5CheckedLowerBoundCore_currentRoot
#print axioms no_internalPudlakTheorem5CheckedLowerBoundCore_currentRoot

#check no_internalPudlakTheorem5ProofCodeSemanticsCore_currentRoot
#print axioms no_internalPudlakTheorem5ProofCodeSemanticsCore_currentRoot

#check no_internalPudlakTheorem5ProofLengthCodeSemanticsCore_currentRoot
#print axioms no_internalPudlakTheorem5ProofLengthCodeSemanticsCore_currentRoot

#check no_internalPudlakTheorem5NoSmallCodeSemanticsCore_currentRoot
#print axioms no_internalPudlakTheorem5NoSmallCodeSemanticsCore_currentRoot

#check no_internalPudlakTheorem5FiniteSearchNoSmallCore_currentRoot
#print axioms no_internalPudlakTheorem5FiniteSearchNoSmallCore_currentRoot

#check no_internalPudlakTheorem5ComputableFiniteSearchNoSmallCore_currentRoot
#print axioms no_internalPudlakTheorem5ComputableFiniteSearchNoSmallCore_currentRoot

#check no_paHilbertCheckerExactnessCore_currentRoot
#print axioms no_paHilbertCheckerExactnessCore_currentRoot

#check no_paHilbertCheckerInterface_unrestrictedProofObjects
#print axioms no_paHilbertCheckerInterface_unrestrictedProofObjects

#check no_paHilbertCheckerExactnessCore_unrestrictedProofObjects
#print axioms no_paHilbertCheckerExactnessCore_unrestrictedProofObjects

#check RealPAHilbertRootReplacementTarget

#check no_realPAHilbertRootReplacementTarget_currentRoot
#print axioms no_realPAHilbertRootReplacementTarget_currentRoot

#check no_realPAHilbertRootReplacementTarget_unrestrictedProofObjects
#print axioms no_realPAHilbertRootReplacementTarget_unrestrictedProofObjects

#check PAHilbertCanonicalDecoderExactness

#check concretePAHilbertSeedCanonicalDecoderExactness
#print axioms concretePAHilbertSeedCanonicalDecoderExactness

#check concretePAHilbertSeedCanonicalDecoderExactness_nonempty
#print axioms concretePAHilbertSeedCanonicalDecoderExactness_nonempty

#check rootLiteratureRescaledPudlak_currentRootLength_eq_scale_add_twelve
#print axioms rootLiteratureRescaledPudlak_currentRootLength_eq_scale_add_twelve

#check rootLiteratureRescaledPudlak_currentRootLength_polynomial
#print axioms rootLiteratureRescaledPudlak_currentRootLength_polynomial

#check no_literaturePudlakTheorem5ExternalRescaledLowerBound_currentRoot
#print axioms no_literaturePudlakTheorem5ExternalRescaledLowerBound_currentRoot

#check literaturePudlakTheorem5External_currentRoot_contradiction
#print axioms literaturePudlakTheorem5External_currentRoot_contradiction

#check externalPAHilbertProofLength_eq_localChecked_forces_rootFormulaCodeSize
#print axioms externalPAHilbertProofLength_eq_localChecked_forces_rootFormulaCodeSize

#check externalPAHilbertProofLength_eq_localChecked_forces_partialConsistency_linear
#print axioms externalPAHilbertProofLength_eq_localChecked_forces_partialConsistency_linear

#check externalPAHilbertProofLength_eq_localChecked_forces_reflectionGraft_linear
#print axioms externalPAHilbertProofLength_eq_localChecked_forces_reflectionGraft_linear

#check currentToyBAFormulaAuditTruth

#check currentToyPAAxiom_auditTruth
#print axioms currentToyPAAxiom_auditTruth

#check currentToyPADerivation_auditTruth
#print axioms currentToyPADerivation_auditTruth

#check no_currentToyPADerivation_finiteConsistencyFormula
#print axioms no_currentToyPADerivation_finiteConsistencyFormula

#check no_currentToyPAProofObject_finiteConsistencyFormula
#print axioms no_currentToyPAProofObject_finiteConsistencyFormula

#check no_currentToyBussS21ProofObject_finiteConsistencyFormula
#print axioms no_currentToyBussS21ProofObject_finiteConsistencyFormula

#check projectAssemblyBudgetFieldIndex_assembledProof_conclusion_eq_finiteConsistency
#print axioms projectAssemblyBudgetFieldIndex_assembledProof_conclusion_eq_finiteConsistency

#check no_currentToyCanonicalProofCertificateAt_finiteConsistency
#print axioms no_currentToyCanonicalProofCertificateAt_finiteConsistency

#check no_currentToyCanonicalProofCertificateAccepted_finiteConsistency
#print axioms no_currentToyCanonicalProofCertificateAccepted_finiteConsistency

#check no_currentToyCanonicalProofCertificateAcceptedTrace_finiteConsistency
#print axioms no_currentToyCanonicalProofCertificateAcceptedTrace_finiteConsistency

#check no_acceptedToCanonicalProofCertificateTransport_currentToy_of_accepted
#print axioms no_acceptedToCanonicalProofCertificateTransport_currentToy_of_accepted

#check no_projectAssemblyBudgetFieldIndex_currentToy_of_source
#print axioms no_projectAssemblyBudgetFieldIndex_currentToy_of_source

#check no_currentToyPADerivation_contradictionFormula
#print axioms no_currentToyPADerivation_contradictionFormula

#check currentToyPAFiniteConsistencyStatement_all
#print axioms currentToyPAFiniteConsistencyStatement_all

#check currentToySemanticBAMinProofSizeOption_finiteConsistency_eq_none
#print axioms currentToySemanticBAMinProofSizeOption_finiteConsistency_eq_none

#check BAOptionMinProofSizeBeatsPolynomial

#check BAOptionMinProofSizeBeatsPolynomial_to_frequently_exists_proof
#print axioms BAOptionMinProofSizeBeatsPolynomial_to_frequently_exists_proof

#check BAEventuallyPolynomialProofObjectFamily

#check BAProofObjectStrongSizeLowerBound

#check BAProofObjectCompleteness

#check BACompleteProofObjectStrongSizeLowerBound

#check BAProofObjectStrongSizeLowerBound_to_no_eventual_polynomial_proof_family
#print axioms BAProofObjectStrongSizeLowerBound_to_no_eventual_polynomial_proof_family

#check no_eventual_polynomial_proof_family_to_BAProofObjectStrongSizeLowerBound
#print axioms no_eventual_polynomial_proof_family_to_BAProofObjectStrongSizeLowerBound

#check BAProofObjectStrongSizeLowerBound_iff_no_eventual_polynomial_proof_family
#print axioms BAProofObjectStrongSizeLowerBound_iff_no_eventual_polynomial_proof_family

#check BAOptionMinProofSizeBeatsPolynomial_to_no_eventual_polynomial_proof_family
#print axioms BAOptionMinProofSizeBeatsPolynomial_to_no_eventual_polynomial_proof_family

#check BAOptionMinProofSizeBeatsPolynomial_to_BAProofObjectStrongSizeLowerBound
#print axioms BAOptionMinProofSizeBeatsPolynomial_to_BAProofObjectStrongSizeLowerBound

#check no_eventual_polynomial_proof_family_to_BAOptionMinProofSizeBeatsPolynomial
#print axioms no_eventual_polynomial_proof_family_to_BAOptionMinProofSizeBeatsPolynomial

#check BAOptionMinProofSizeBeatsPolynomial_iff_no_eventual_polynomial_proof_family
#print axioms BAOptionMinProofSizeBeatsPolynomial_iff_no_eventual_polynomial_proof_family

#check BAProofObjectStrongSizeLowerBound_to_BAOptionMinProofSizeBeatsPolynomial
#print axioms BAProofObjectStrongSizeLowerBound_to_BAOptionMinProofSizeBeatsPolynomial

#check BAProofObjectStrongSizeLowerBound_iff_BAOptionMinProofSizeBeatsPolynomial
#print axioms BAProofObjectStrongSizeLowerBound_iff_BAOptionMinProofSizeBeatsPolynomial

#check BACompleteProofObjectStrongSizeLowerBound_to_BAOptionMinProofSizeBeatsPolynomial
#print axioms BACompleteProofObjectStrongSizeLowerBound_to_BAOptionMinProofSizeBeatsPolynomial

#check BACompleteProofObjectStrongSizeLowerBound_to_no_eventual_polynomial_proof_family
#print axioms BACompleteProofObjectStrongSizeLowerBound_to_no_eventual_polynomial_proof_family

#check BACompleteProofObjectStrongSizeLowerBound_iff_complete_and_option
#print axioms BACompleteProofObjectStrongSizeLowerBound_iff_complete_and_option

#check BACompleteProofObjectStrongSizeLowerBound_iff_complete_and_no_eventual
#print axioms BACompleteProofObjectStrongSizeLowerBound_iff_complete_and_no_eventual

#check no_BAOptionMinProofSizeBeatsPolynomial_of_polynomial_upper_bound
#print axioms no_BAOptionMinProofSizeBeatsPolynomial_of_polynomial_upper_bound

#check no_currentToyBAOptionMinProofSizeBeatsPolynomial_finiteConsistency
#print axioms no_currentToyBAOptionMinProofSizeBeatsPolynomial_finiteConsistency

#check no_BAOptionMinProofSizeBeatsPolynomial_of_target_axioms
#print axioms no_BAOptionMinProofSizeBeatsPolynomial_of_target_axioms

#check no_BACompleteProofObjectStrongSizeLowerBound_of_target_axioms
#print axioms no_BACompleteProofObjectStrongSizeLowerBound_of_target_axioms

#check currentToySemanticBAProofLength_finiteConsistency_eq_zero
#print axioms currentToySemanticBAProofLength_finiteConsistency_eq_zero

#check currentToyCanonicalCnBoxPABox_length_eq_zero
#print axioms currentToyCanonicalCnBoxPABox_length_eq_zero

#check no_currentToyCanonicalCnBoxProofLengthGap
#print axioms no_currentToyCanonicalCnBoxProofLengthGap

#check no_currentToyCanonicalCnBoxEventualLowerBound
#print axioms no_currentToyCanonicalCnBoxEventualLowerBound

#check no_canonicalRelabeledPudlakCalibration_currentToySemantics
#print axioms no_canonicalRelabeledPudlakCalibration_currentToySemantics

#check no_correctedCanonicalCnBoxLowerBoundClosureTarget_currentToySemantics
#print axioms no_correctedCanonicalCnBoxLowerBoundClosureTarget_currentToySemantics

#check no_rootLiteratureCanonicalCnBoxCalibrationTarget_currentToySemantics
#print axioms no_rootLiteratureCanonicalCnBoxCalibrationTarget_currentToySemantics

#check calibratedSingletonCodeBound

#check calibratedSingletonFiniteEnumeration_of_injective
#print axioms calibratedSingletonFiniteEnumeration_of_injective

#check canonicalLengthGap_toNoAcceptedCodeSearch_of_injective
#print axioms canonicalLengthGap_toNoAcceptedCodeSearch_of_injective

#check canonicalLengthGap_to_noAcceptedCodeSearchTarget_of_injective
#print axioms canonicalLengthGap_to_noAcceptedCodeSearchTarget_of_injective

#check canonicalLengthGap_and_rootExactness_to_actualProofLengthGap
#print axioms canonicalLengthGap_and_rootExactness_to_actualProofLengthGap

#check no_canonicalLengthGap_and_rootExactness_currentRoot
#print axioms no_canonicalLengthGap_and_rootExactness_currentRoot

#check rootProofLength_eq_lengthCodeAt_of_calibratedCheckerExactness_direct
#print axioms rootProofLength_eq_lengthCodeAt_of_calibratedCheckerExactness_direct

#check superPolynomialCanonicalLength

#check superPolynomialCanonicalLength_searchGap
#print axioms superPolynomialCanonicalLength_searchGap

#check superPolynomialCanonicalLength_to_noAcceptedCodeSearchTarget
#print axioms superPolynomialCanonicalLength_to_noAcceptedCodeSearchTarget

#check superPolynomialCanonicalLength_to_checkedMeasuredSearchGap
#print axioms superPolynomialCanonicalLength_to_checkedMeasuredSearchGap

#check superPolynomialCanonicalLength_to_checkedMinProofCodeStrongLowerBound
#print axioms superPolynomialCanonicalLength_to_checkedMinProofCodeStrongLowerBound

#check no_superPolynomialCanonicalLength_rootExactness_currentRoot
#print axioms no_superPolynomialCanonicalLength_rootExactness_currentRoot

#check no_superPolynomialCalibratedCheckerExactness_currentRoot
#print axioms no_superPolynomialCalibratedCheckerExactness_currentRoot

#check SizeFilteredNoAcceptedCodeSearchClosureTarget

#check sizeFilteredRejectionSearchClosureTarget_to_noAcceptedCodeSearchTarget
#print axioms sizeFilteredRejectionSearchClosureTarget_to_noAcceptedCodeSearchTarget

#check sizeFilteredNoAcceptedCodeSearchTarget_to_rejectionSearchClosureTarget
#print axioms sizeFilteredNoAcceptedCodeSearchTarget_to_rejectionSearchClosureTarget

#check sizeFilteredNoAcceptedCodeSearchTarget_to_checkedMeasuredSearchGap
#print axioms sizeFilteredNoAcceptedCodeSearchTarget_to_checkedMeasuredSearchGap

#check SizeFilteredRejectionSearchClosureTarget

#check sizeFilteredRejectionSearchClosureTarget_to_checkedMeasuredSearchGap
#print axioms sizeFilteredRejectionSearchClosureTarget_to_checkedMeasuredSearchGap

#check axiomatizedSubmissionRoute
#print axioms axiomatizedSubmissionRoute

end SondowProjectPudlakLowerBoundInputAudit
end SondowMainCheckedCodeBridge
