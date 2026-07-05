import integration.SondowProjectMonth9Month10Month11ExactProofGapHandoff
import integration.SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth11Month12HardResidualElimination

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10ProofLengthGapFrontier
open SondowProjectMonth9Month10Month11ExactProofGapHandoff
open SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface

/-- Deliverable 1: strict growth of the scale follows from strict growth of the
primitive time-constructible bound plus a nonzero exponent. -/
theorem your_scale_strict_theorem
    {scale_data : InternalPudlakTheorem5ScaleData}
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0) :
    ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b :=
  Month9Month10ActualProofLengthGapFrontier.scale_strict_of_timeConstructibleBound_strict
    time_bound_strict exponent_ne_zero

/-- Proof-length-free checked gap obtained directly from the checker finite
search exclusion certificate.  This is the 9-10 bridge field shape:
`checker/enumeration/extractor`, not a new wrapper candidate. -/
def checked_minProofCodeSize_gap_constructor
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration) :
    ComputableSearchGapCertificate
      (month9_month10_checkedProofCodeMeasured
        scale_data checker.toProofCodeSemantics) :=
  month9_month10_checkedMeasuredGapOfComputableFiniteSearchExclusion
    extractor.toComputableFiniteSearchExclusion

theorem checked_minProofCodeSize_gap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((checked_minProofCodeSize_gap_constructor extractor
        |>.gap_for_polynomial_upper U hU).witness N) =
      extractor.witness U hU N :=
  rfl

/-- Minimal bridge needed to turn the checked min-code-size route into the
project actual-proof-length route. -/
structure ActualProofLengthGapTransportBlocker
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data) : Prop where
  checked_eq_actual :
    ∀ n : Nat,
      month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics n =
        actualProofLengthMeasured scale_data n

def actual_transport_of_checker_proof_length_family_exactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker) :
    ActualProofLengthGapTransportBlocker checker where
  checked_eq_actual := by
    intro n
    simpa [actualProofLengthMeasured,
      month9_month10_checkedProofCodeMeasured,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
      using (family.proof_length_eq_minProofCodeSizeAt n).symm

/-- Named probe target for the actual-transport route.  Under the current
foundation this is the strongest available route: it closes the transport only
after checker family proof-length exactness has been supplied. -/
theorem your_actual_transport_theorem
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker) :
    ActualProofLengthGapTransportBlocker checker :=
  actual_transport_of_checker_proof_length_family_exactness family

/-- Minimal blocker witness: even a reflexive theorem whose statement mentions
`actualProofLengthMeasured` carries the project-level `proof_length` dependency,
because `actualProofLengthMeasured` is definitionally the root proof-length
measurement on `powerBoundRawCode`. -/
theorem actualProofLengthMeasured_statement_blocker
    (scale_data : InternalPudlakTheorem5ScaleData) :
    ∀ n : Nat,
      actualProofLengthMeasured scale_data n =
        actualProofLengthMeasured scale_data n := by
  intro n
  rfl

/-- Deliverable 2 reduced to its exact hard bridge: finite-search exclusion
gives the checked gap without project proof length; an actual proof-length gap
additionally needs checked min-code-size to equal the project actual
measurement. -/
def your_actual_proof_length_gap_constructor
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (transport : ActualProofLengthGapTransportBlocker checker) :
    ComputableSearchGapCertificate
      (actualProofLengthMeasured scale_data) :=
  transportComputableSearchGap
    transport.checked_eq_actual
    (checked_minProofCodeSize_gap_constructor extractor)

theorem your_actual_proof_length_gap_constructor_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (transport : ActualProofLengthGapTransportBlocker checker)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((your_actual_proof_length_gap_constructor extractor transport
        |>.gap_for_polynomial_upper U hU).witness N) =
      extractor.witness U hU N :=
  rfl

/-- The second hard bridge needed for `proof_length(powerBoundRawCode n) =
scale n`: after checked min-code-size has been identified with actual proof
length, the checked measurement still has to be identified with the chosen
project scale. -/
structure CheckedMinProofCodeSizeEqScaleBlocker
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data) : Prop where
  checked_eq_scale :
    ∀ n : Nat,
      month9_month10_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics n =
        scaleMeasured scale_data n

def checked_scale_gap_of_scale_transport
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (scale_transport : CheckedMinProofCodeSizeEqScaleBlocker checker) :
    ComputableSearchGapCertificate (scaleMeasured scale_data) :=
  transportComputableSearchGap scale_transport.checked_eq_scale
    (checked_minProofCodeSize_gap_constructor extractor)

theorem checked_scale_gap_witness_eq_extractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (scale_transport : CheckedMinProofCodeSizeEqScaleBlocker checker)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((checked_scale_gap_of_scale_transport extractor scale_transport
        |>.gap_for_polynomial_upper U hU).witness N) =
      extractor.witness U hU N :=
  rfl

/-- Negative audit for the tempting exact-scale bridge.  A checked
min-code-size gap cannot be transported to the polynomially bounded project
scale.  Thus the remaining route cannot require `checked = scale`; it must use
an actual proof-length measurement or a domination statement that does not make
the lower-gap object polynomially bounded. -/
theorem checked_eq_scale_blocker_impossible
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (scale_transport : CheckedMinProofCodeSizeEqScaleBlocker checker) :
    False :=
  no_scale_search_gap_for_internal_scale scale_data
    (checked_scale_gap_of_scale_transport extractor scale_transport)

/-- Deliverable 3, expressed through the two precise missing bridges.  This is
not unconditional: it isolates exactly the two equalities that must be proved
to remove the final project proof-length dependency. -/
theorem your_proof_length_eq_scale_theorem
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data)
    (actual_transport :
      ActualProofLengthGapTransportBlocker checker)
    (scale_transport :
      CheckedMinProofCodeSizeEqScaleBlocker checker) :
    ∀ n : Nat,
      actualProofLengthMeasured scale_data n = scaleMeasured scale_data n := by
  intro n
  exact
    (actual_transport.checked_eq_actual n).symm.trans
      (scale_transport.checked_eq_scale n)

structure HardResidualEliminationBlockers
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data) : Prop where
  time_bound_strict :
    ∀ {a b : Nat}, a < b →
      scale_data.time_constructible_bound a <
        scale_data.time_constructible_bound b
  exponent_ne_zero : scale_data.exponent ≠ 0
  actual_transport : ActualProofLengthGapTransportBlocker checker
  scale_transport : CheckedMinProofCodeSizeEqScaleBlocker checker

/-- Conditional final closure for the hard residual line.  It proves the three
target artifacts from the exact remaining blockers; the checked-search kernel
itself is already independent of the project actual-proof-length measurement. -/
theorem your_final_unconditional_candidate
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (blockers : HardResidualEliminationBlockers checker) :
    (∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
      (∀ n : Nat,
        actualProofLengthMeasured scale_data n =
          scaleMeasured scale_data n) :=
  ⟨your_scale_strict_theorem
      blockers.time_bound_strict blockers.exponent_ne_zero,
    ⟨your_actual_proof_length_gap_constructor
      extractor blockers.actual_transport⟩,
    your_proof_length_eq_scale_theorem
      checker blockers.actual_transport blockers.scale_transport⟩

/-- The current "exact scale" hard-residual package is inconsistent with the
checked lower-gap certificate.  This redirects the remaining proof-length work:
do not try to prove `checked minProofCodeSize = scale`; prove the actual
proof-length calibration needed for the measured lower-bound object instead. -/
theorem hard_residual_blockers_impossible
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (blockers : HardResidualEliminationBlockers checker) :
    False :=
  checked_eq_scale_blocker_impossible extractor blockers.scale_transport

/-- The final-three certificate shape with an exact `proof_length = scale`
field is itself inconsistent when it also carries a computable proof-length
gap.  Transporting that gap across the equality would produce a computable
search gap for the polynomially bounded scale, which is impossible.

This is an audit guardrail: the remaining route must use the corrected
actual-measured lower-bound object, not an exact-scale lower-gap package. -/
theorem finalThreeCertificateEndpoint_exactScale_impossible
    {scale_data : InternalPudlakTheorem5ScaleData}
    (endpoint :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint
        scale_data) :
    False := by
  have heq :
      ∀ n : Nat,
        (fun n : Nat =>
          _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n)) n =
          scaleMeasured scale_data n := by
    intro n
    simpa [scaleMeasured] using endpoint.proof_length_eq_scale n
  exact
    no_scale_search_gap_for_internal_scale scale_data
      (transportComputableSearchGap heq endpoint.proof_length_gap)

/-! ## Corrected actual-measured route after rejecting exact scale -/

/-- Corrected residual package for the remaining proof-length work.  It keeps
only the bridge from the checker-computed minimum proof-code size to the project
actual proof-length measurement.  No equality to the polynomially bounded scale
is requested. -/
structure CorrectedActualMeasuredResidual
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data) : Prop where
  actual_transport : ActualProofLengthGapTransportBlocker checker

def corrected_actual_proof_length_gap
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (residual : CorrectedActualMeasuredResidual checker) :
    ComputableSearchGapCertificate
      (actualProofLengthMeasured scale_data) :=
  your_actual_proof_length_gap_constructor extractor
    residual.actual_transport

theorem corrected_actual_proof_length_gap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (residual : CorrectedActualMeasuredResidual checker)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((corrected_actual_proof_length_gap extractor residual
        |>.gap_for_polynomial_upper U hU).witness N) =
      extractor.witness U hU N :=
  rfl

def corrected_actual_measured_endpoint
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (residual : CorrectedActualMeasuredResidual checker)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data where
  gap := corrected_actual_proof_length_gap extractor residual
  upper_provider := actual_upper

noncomputable def corrected_actual_upper_tail
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (residual : CorrectedActualMeasuredResidual checker)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate (actualProofLengthMeasured scale_data) :=
  (corrected_actual_measured_endpoint extractor residual actual_upper)
    |>.toAbstractMeasuredEndpoint
    |>.upperTailOfRationality hrat

theorem corrected_actual_computed_n_eq_extractor_witness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (residual : CorrectedActualMeasuredResidual checker)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (corrected_actual_measured_endpoint
        extractor residual actual_upper).computedCollisionNOfRationality hrat =
      extractor.witness
        (corrected_actual_upper_tail
          extractor residual actual_upper hrat).U
        (corrected_actual_upper_tail
          extractor residual actual_upper hrat).polynomial
        (corrected_actual_upper_tail
          extractor residual actual_upper hrat).upperN := by
  calc
    (corrected_actual_measured_endpoint
        extractor residual actual_upper).computedCollisionNOfRationality hrat =
        (((corrected_actual_measured_endpoint
            extractor residual actual_upper).gap.gap_for_polynomial_upper
            (corrected_actual_upper_tail
              extractor residual actual_upper hrat).U
            (corrected_actual_upper_tail
              extractor residual actual_upper hrat).polynomial).witness
          (corrected_actual_upper_tail
            extractor residual actual_upper hrat).upperN) := by
          simpa [corrected_actual_upper_tail] using
            (corrected_actual_measured_endpoint
              extractor residual actual_upper)
              |>.computedCollisionN_eq_searchGapWitness hrat
    _ = extractor.witness
        (corrected_actual_upper_tail
          extractor residual actual_upper hrat).U
        (corrected_actual_upper_tail
          extractor residual actual_upper hrat).polynomial
        (corrected_actual_upper_tail
          extractor residual actual_upper hrat).upperN :=
          corrected_actual_proof_length_gap_witness_eq
            extractor residual
            (corrected_actual_upper_tail
              extractor residual actual_upper hrat).U
            (corrected_actual_upper_tail
              extractor residual actual_upper hrat).polynomial
            (corrected_actual_upper_tail
              extractor residual actual_upper hrat).upperN

structure CorrectedActualMeasuredEndpointAudit
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (residual : CorrectedActualMeasuredResidual checker)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) : Prop where
  endpointAudit :
    (corrected_actual_measured_endpoint
      extractor residual actual_upper).Audit
  gapCertificate :
    Nonempty
      (ComputableSearchGapCertificate
        (actualProofLengthMeasured scale_data))
  computedWitnessFormula :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (corrected_actual_measured_endpoint
          extractor residual actual_upper).computedCollisionNOfRationality hrat =
        extractor.witness
          (corrected_actual_upper_tail
            extractor residual actual_upper hrat).U
          (corrected_actual_upper_tail
            extractor residual actual_upper hrat).polynomial
          (corrected_actual_upper_tail
            extractor residual actual_upper hrat).upperN
  contradictionAtComputedN :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem corrected_actual_measured_endpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration checker}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        checker enumeration)
    (residual : CorrectedActualMeasuredResidual checker)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    CorrectedActualMeasuredEndpointAudit
      extractor residual actual_upper ∧
      (corrected_actual_measured_endpoint
        extractor residual actual_upper).Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured scale_data)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (corrected_actual_measured_endpoint
                extractor residual actual_upper).computedCollisionNOfRationality hrat =
              extractor.witness
                (corrected_actual_upper_tail
                  extractor residual actual_upper hrat).U
                (corrected_actual_upper_tail
                  extractor residual actual_upper hrat).polynomial
                (corrected_actual_upper_tail
                  extractor residual actual_upper hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni := by
  exact
    ⟨{
      endpointAudit :=
        (corrected_actual_measured_endpoint
          extractor residual actual_upper).audit
      gapCertificate :=
        ⟨corrected_actual_proof_length_gap extractor residual⟩
      computedWitnessFormula :=
        corrected_actual_computed_n_eq_extractor_witness
          extractor residual actual_upper
      contradictionAtComputedN :=
        (corrected_actual_measured_endpoint
          extractor residual actual_upper).computed_n_contradiction
      endpointNotRational :=
        (corrected_actual_measured_endpoint
          extractor residual actual_upper).not_rational },
      (corrected_actual_measured_endpoint
        extractor residual actual_upper).audit,
      ⟨corrected_actual_proof_length_gap extractor residual⟩,
      corrected_actual_computed_n_eq_extractor_witness
        extractor residual actual_upper,
      (corrected_actual_measured_endpoint
        extractor residual actual_upper).computed_n_contradiction,
      (corrected_actual_measured_endpoint
        extractor residual actual_upper).not_rational⟩

/-! ## Proof-length-free candidate plus isolated transport residual -/

/-- A proof-length-free Month 12 checker-search candidate can enter the
corrected actual route once, and only once, the isolated transport residual is
provided.  This avoids bundling the transport equality into the checker/search
candidate itself. -/
def correctedResidualOfProofLengthFreeCandidate
    {scale_data : InternalPudlakTheorem5ScaleData}
    {candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data}
    (residual : Month12ProofLengthTransportResidual candidate) :
    CorrectedActualMeasuredResidual candidate.checkerSemantics where
  actual_transport :=
    actual_transport_of_checker_proof_length_family_exactness
      residual.toCheckerProofLengthFamilyExactness

/-- Corrected actual endpoint from the proof-length-free checker/search
candidate plus the isolated transport residual. -/
def correctedActualEndpointOfProofLengthFreeCandidate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (residual : Month12ProofLengthTransportResidual candidate)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data :=
  corrected_actual_measured_endpoint
    candidate.rejectionExtractor
    (correctedResidualOfProofLengthFreeCandidate residual)
    actual_upper

theorem correctedActualEndpointOfProofLengthFreeCandidate_computed_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (residual : Month12ProofLengthTransportResidual candidate)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (correctedActualEndpointOfProofLengthFreeCandidate
        candidate residual actual_upper).computedCollisionNOfRationality hrat =
      candidate.rejectionExtractor.witness
        (corrected_actual_upper_tail
          candidate.rejectionExtractor
          (correctedResidualOfProofLengthFreeCandidate residual)
          actual_upper hrat).U
        (corrected_actual_upper_tail
          candidate.rejectionExtractor
          (correctedResidualOfProofLengthFreeCandidate residual)
          actual_upper hrat).polynomial
        (corrected_actual_upper_tail
          candidate.rejectionExtractor
          (correctedResidualOfProofLengthFreeCandidate residual)
          actual_upper hrat).upperN :=
  corrected_actual_computed_n_eq_extractor_witness
    candidate.rejectionExtractor
    (correctedResidualOfProofLengthFreeCandidate residual)
    actual_upper hrat

theorem correctedActualEndpointOfProofLengthFreeCandidate_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (residual : Month12ProofLengthTransportResidual candidate)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    (correctedActualEndpointOfProofLengthFreeCandidate
      candidate residual actual_upper).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (correctedActualEndpointOfProofLengthFreeCandidate
              candidate residual actual_upper).computedCollisionNOfRationality hrat =
            candidate.rejectionExtractor.witness
              (corrected_actual_upper_tail
                candidate.rejectionExtractor
                (correctedResidualOfProofLengthFreeCandidate residual)
                actual_upper hrat).U
              (corrected_actual_upper_tail
                candidate.rejectionExtractor
                (correctedResidualOfProofLengthFreeCandidate residual)
                actual_upper hrat).polynomial
              (corrected_actual_upper_tail
                candidate.rejectionExtractor
                (correctedResidualOfProofLengthFreeCandidate residual)
                actual_upper hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    corrected_actual_measured_endpoint_closure
      candidate.rejectionExtractor
      (correctedResidualOfProofLengthFreeCandidate residual)
      actual_upper
  exact
    ⟨hclosure.2.1,
      hclosure.2.2.1,
      correctedActualEndpointOfProofLengthFreeCandidate_computed_n_eq
        candidate residual actual_upper,
      hclosure.2.2.2.2.1,
      hclosure.2.2.2.2.2⟩

/-! ## Proof-length-free candidate plus project upper route -/

/-- The isolated transport residual also gives the checked/actual bridge
needed to move a checked upper provider to the actual proof-length measurement.
This keeps the lower-gap and upper-tail transports synchronized by the same
single residual. -/
def checkedMeasuredToActualBridgeOfProofLengthFreeCandidate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (residual : Month12ProofLengthTransportResidual candidate) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
      scale_data candidate.checkerSemantics.toProofCodeSemantics where
  checked_eq_actual := by
    intro n
    simpa [month9_month10_checkedProofCodeMeasured,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
      using (residual.actualProofLengthMeasured_eq_minProofCodeSizeAt n).symm

/-- Actual upper provider obtained from the Sondow project upper route, the
same additive projection used by the theorem-5 source measurement, and the
isolated proof-length transport residual. -/
def actualUpperProviderOfProofLengthFreeCandidateProjectUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (residual : Month12ProofLengthTransportResidual candidate)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data candidate.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10AbstractMeasuredUpperProvider
      (actualProofLengthMeasured scale_data) :=
  actualUpperProviderOfProjectUpperAndAdditiveProjection
    projection
    (checkedMeasuredToActualBridgeOfProofLengthFreeCandidate
      candidate residual)
    project_upper

/-- Corrected actual endpoint from proof-length-free checker/search data, the
single actual-transport residual, additive project-box projection, and Sondow
project upper route. -/
def correctedActualEndpointOfProofLengthFreeCandidateProjectUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (residual : Month12ProofLengthTransportResidual candidate)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data candidate.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data :=
  correctedActualEndpointOfProofLengthFreeCandidate candidate residual
    (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
      candidate residual projection project_upper)

theorem correctedActualEndpointOfProofLengthFreeCandidateProjectUpper_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (residual : Month12ProofLengthTransportResidual candidate)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data candidate.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (correctedActualEndpointOfProofLengthFreeCandidateProjectUpper
      candidate residual projection project_upper).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (correctedActualEndpointOfProofLengthFreeCandidateProjectUpper
              candidate residual projection project_upper).computedCollisionNOfRationality hrat =
            candidate.rejectionExtractor.witness
              (corrected_actual_upper_tail
                candidate.rejectionExtractor
                (correctedResidualOfProofLengthFreeCandidate residual)
                (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
                  candidate residual projection project_upper)
                hrat).U
              (corrected_actual_upper_tail
                candidate.rejectionExtractor
                (correctedResidualOfProofLengthFreeCandidate residual)
                (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
                  candidate residual projection project_upper)
                hrat).polynomial
              (corrected_actual_upper_tail
                candidate.rejectionExtractor
                (correctedResidualOfProofLengthFreeCandidate residual)
                (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
                  candidate residual projection project_upper)
                hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [correctedActualEndpointOfProofLengthFreeCandidateProjectUpper] using
    correctedActualEndpointOfProofLengthFreeCandidate_closure
      candidate residual
      (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
        candidate residual projection project_upper)

/-- C-line instantiation of the corrected actual endpoint.  This is the
current cleanest combined route: checker/search is proof-length-free, the only
proof-length field is the isolated actual-transport residual, and the Sondow
upper source is the concrete C-line closure. -/
def correctedActualEndpointOfProofLengthFreeCandidateCLineMinimalClosure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (residual : Month12ProofLengthTransportResidual candidate)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data candidate.checkerSemantics.toProofCodeSemantics)
    (cline : Nonempty (SondowCLineMinimalClosureCertificate bounds)) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data :=
  correctedActualEndpointOfProofLengthFreeCandidateProjectUpper
    candidate residual projection
    (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
      cline)

theorem correctedActualEndpointOfProofLengthFreeCandidateCLineMinimalClosure_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (residual : Month12ProofLengthTransportResidual candidate)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data candidate.checkerSemantics.toProofCodeSemantics)
    (cline : Nonempty (SondowCLineMinimalClosureCertificate bounds)) :
    (correctedActualEndpointOfProofLengthFreeCandidateCLineMinimalClosure
      candidate residual projection cline).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (correctedActualEndpointOfProofLengthFreeCandidateCLineMinimalClosure
              candidate residual projection cline).computedCollisionNOfRationality hrat =
            candidate.rejectionExtractor.witness
              (corrected_actual_upper_tail
                candidate.rejectionExtractor
                (correctedResidualOfProofLengthFreeCandidate residual)
                (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
                  candidate residual projection
                  (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                    cline))
                hrat).U
              (corrected_actual_upper_tail
                candidate.rejectionExtractor
                (correctedResidualOfProofLengthFreeCandidate residual)
                (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
                  candidate residual projection
                  (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                    cline))
                hrat).polynomial
              (corrected_actual_upper_tail
                candidate.rejectionExtractor
                (correctedResidualOfProofLengthFreeCandidate residual)
                (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
                  candidate residual projection
                  (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                    cline))
                hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [correctedActualEndpointOfProofLengthFreeCandidateCLineMinimalClosure] using
    correctedActualEndpointOfProofLengthFreeCandidateProjectUpper_closure
      candidate residual projection
      (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
        cline)

/-- Fully split C-line component entry point for the corrected actual endpoint.
This removes the abstract `SondowProjectLocalS21CollapseConclusion` parameter
from the final route and exposes the exact three current Sondow-side
certificates. -/
def correctedActualEndpointOfProofLengthFreeCandidateCLineKernelCheckerLength
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (residual : Month12ProofLengthTransportResidual candidate)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data candidate.checkerSemantics.toProofCodeSemantics)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data :=
  correctedActualEndpointOfProofLengthFreeCandidateCLineMinimalClosure
    candidate residual projection
    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
      hkernel hchecker hlength)

theorem correctedActualEndpointOfProofLengthFreeCandidateCLineKernelCheckerLength_computed_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (residual : Month12ProofLengthTransportResidual candidate)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data candidate.checkerSemantics.toProofCodeSemantics)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (correctedActualEndpointOfProofLengthFreeCandidateCLineKernelCheckerLength
      candidate residual projection hkernel hchecker hlength).computedCollisionNOfRationality hrat =
      candidate.rejectionExtractor.witness
        (corrected_actual_upper_tail
          candidate.rejectionExtractor
          (correctedResidualOfProofLengthFreeCandidate residual)
          (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
            candidate residual projection
            (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
              (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                hkernel hchecker hlength)))
          hrat).U
        (corrected_actual_upper_tail
          candidate.rejectionExtractor
          (correctedResidualOfProofLengthFreeCandidate residual)
          (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
            candidate residual projection
            (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
              (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                hkernel hchecker hlength)))
          hrat).polynomial
        (corrected_actual_upper_tail
          candidate.rejectionExtractor
          (correctedResidualOfProofLengthFreeCandidate residual)
          (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
            candidate residual projection
            (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
              (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                hkernel hchecker hlength)))
          hrat).upperN := by
  simpa [correctedActualEndpointOfProofLengthFreeCandidateCLineKernelCheckerLength,
    correctedActualEndpointOfProofLengthFreeCandidateCLineMinimalClosure] using
    correctedActualEndpointOfProofLengthFreeCandidateCLineMinimalClosure_closure
      candidate residual projection
      (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
        hkernel hchecker hlength)
      |>.2.2.1 hrat

theorem correctedActualEndpointOfProofLengthFreeCandidateCLineKernelCheckerLength_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (residual : Month12ProofLengthTransportResidual candidate)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data candidate.checkerSemantics.toProofCodeSemantics)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    (correctedActualEndpointOfProofLengthFreeCandidateCLineKernelCheckerLength
      candidate residual projection hkernel hchecker hlength).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    correctedActualEndpointOfProofLengthFreeCandidateCLineMinimalClosure_closure
      candidate residual projection
      (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
        hkernel hchecker hlength)
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      hclosure.2.2.2.1,
      hclosure.2.2.2.2⟩

/-! ## Checker-family exactness as the minimal proof-length residual -/

/-- Convert checker proof-length family exactness into the isolated Month 12
transport residual.  This is the narrow proof-length blocker for the corrected
actual route: it states equality with the checked `minProofCodeSizeAt`, not
with the polynomially bounded project scale. -/
def transportResidualOfProofLengthFreeCandidateFamilyExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data}
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        candidate.checkerSemantics) :
    Month12ProofLengthTransportResidual candidate where
  actualProofLengthMeasured_eq_minProofCodeSizeAt := by
    intro n
    simpa [actualProofLengthMeasured]
      using family.proof_length_eq_minProofCodeSizeAt n

/-- Corrected actual endpoint from a proof-length-free candidate and the
minimal checker-family exactness theorem, with the Sondow upper side supplied
by the split C-line certificates. -/
def correctedActualEndpointOfProofLengthFreeCandidateFamilyExactnessCLineKernelCheckerLength
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        candidate.checkerSemantics)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data candidate.checkerSemantics.toProofCodeSemantics)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data :=
  correctedActualEndpointOfProofLengthFreeCandidateCLineKernelCheckerLength
    candidate
    (transportResidualOfProofLengthFreeCandidateFamilyExactness family)
    projection hkernel hchecker hlength

theorem correctedActualEndpointOfProofLengthFreeCandidateFamilyExactnessCLineKernelCheckerLength_computed_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        candidate.checkerSemantics)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data candidate.checkerSemantics.toProofCodeSemantics)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (correctedActualEndpointOfProofLengthFreeCandidateFamilyExactnessCLineKernelCheckerLength
      candidate family projection hkernel hchecker hlength).computedCollisionNOfRationality hrat =
      candidate.rejectionExtractor.witness
        (corrected_actual_upper_tail
          candidate.rejectionExtractor
          (correctedResidualOfProofLengthFreeCandidate
            (transportResidualOfProofLengthFreeCandidateFamilyExactness family))
          (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
            candidate
            (transportResidualOfProofLengthFreeCandidateFamilyExactness family)
            projection
            (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
              (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                hkernel hchecker hlength)))
          hrat).U
        (corrected_actual_upper_tail
          candidate.rejectionExtractor
          (correctedResidualOfProofLengthFreeCandidate
            (transportResidualOfProofLengthFreeCandidateFamilyExactness family))
          (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
            candidate
            (transportResidualOfProofLengthFreeCandidateFamilyExactness family)
            projection
            (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
              (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                hkernel hchecker hlength)))
          hrat).polynomial
        (corrected_actual_upper_tail
          candidate.rejectionExtractor
          (correctedResidualOfProofLengthFreeCandidate
            (transportResidualOfProofLengthFreeCandidateFamilyExactness family))
          (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
            candidate
            (transportResidualOfProofLengthFreeCandidateFamilyExactness family)
            projection
            (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
              (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                hkernel hchecker hlength)))
          hrat).upperN := by
  simpa [
    correctedActualEndpointOfProofLengthFreeCandidateFamilyExactnessCLineKernelCheckerLength]
    using
      correctedActualEndpointOfProofLengthFreeCandidateCLineKernelCheckerLength_computed_n_eq
        candidate
        (transportResidualOfProofLengthFreeCandidateFamilyExactness family)
        projection hkernel hchecker hlength hrat

theorem correctedActualEndpointOfProofLengthFreeCandidateFamilyExactnessCLineKernelCheckerLength_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (candidate :
      Month12ProofLengthFreeCheckerSearchCandidate scale_data)
    (family :
      InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        candidate.checkerSemantics)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data candidate.checkerSemantics.toProofCodeSemantics)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    (correctedActualEndpointOfProofLengthFreeCandidateFamilyExactnessCLineKernelCheckerLength
      candidate family projection hkernel hchecker hlength).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (correctedActualEndpointOfProofLengthFreeCandidateFamilyExactnessCLineKernelCheckerLength
            candidate family projection hkernel hchecker hlength).computedCollisionNOfRationality hrat =
            candidate.rejectionExtractor.witness
              (corrected_actual_upper_tail
                candidate.rejectionExtractor
                (correctedResidualOfProofLengthFreeCandidate
                  (transportResidualOfProofLengthFreeCandidateFamilyExactness family))
                (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
                  candidate
                  (transportResidualOfProofLengthFreeCandidateFamilyExactness family)
                  projection
                  (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                      hkernel hchecker hlength)))
                hrat).U
              (corrected_actual_upper_tail
                candidate.rejectionExtractor
                (correctedResidualOfProofLengthFreeCandidate
                  (transportResidualOfProofLengthFreeCandidateFamilyExactness family))
                (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
                  candidate
                  (transportResidualOfProofLengthFreeCandidateFamilyExactness family)
                  projection
                  (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                      hkernel hchecker hlength)))
                hrat).polynomial
              (corrected_actual_upper_tail
                candidate.rejectionExtractor
                (correctedResidualOfProofLengthFreeCandidate
                  (transportResidualOfProofLengthFreeCandidateFamilyExactness family))
                (actualUpperProviderOfProofLengthFreeCandidateProjectUpper
                  candidate
                  (transportResidualOfProofLengthFreeCandidateFamilyExactness family)
                  projection
                  (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                    (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                      hkernel hchecker hlength)))
                hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    correctedActualEndpointOfProofLengthFreeCandidateCLineKernelCheckerLength_closure
      candidate
      (transportResidualOfProofLengthFreeCandidateFamilyExactness family)
      projection hkernel hchecker hlength
  exact
    ⟨hclosure.1,
      hclosure.2.1,
      correctedActualEndpointOfProofLengthFreeCandidateFamilyExactnessCLineKernelCheckerLength_computed_n_eq
        candidate family projection hkernel hchecker hlength,
      hclosure.2.2.1,
      hclosure.2.2.2⟩

/-! ## Month 12 full-candidate adapter for the corrected actual route -/

/-- A full Month 12 checker internalization candidate supplies exactly the
remaining corrected actual-measured residual: checked minimum proof-code size is
transported to the project actual proof-length measurement. -/
def correctedResidualOfMonth12Candidate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data) :
    CorrectedActualMeasuredResidual candidate.checkerSemantics where
  actual_transport :=
    actual_transport_of_checker_proof_length_family_exactness
      candidate.minProofCodeSizeExactness

/-- The corrected actual endpoint built directly from a full Month 12 checker
candidate and an actual-measured Sondow upper provider. -/
def correctedActualEndpointOfMonth12Candidate
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint scale_data :=
  corrected_actual_measured_endpoint
    candidate.rejectionExtractor
    (correctedResidualOfMonth12Candidate candidate)
    actual_upper

theorem correctedActualEndpointOfMonth12Candidate_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    correctedActualEndpointOfMonth12Candidate candidate actual_upper =
      corrected_actual_measured_endpoint
        candidate.rejectionExtractor
        (correctedResidualOfMonth12Candidate candidate)
        actual_upper :=
  rfl

theorem correctedActualEndpointOfMonth12Candidate_computed_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (correctedActualEndpointOfMonth12Candidate
        candidate actual_upper).computedCollisionNOfRationality hrat =
      candidate.rejectionExtractor.witness
        (corrected_actual_upper_tail
          candidate.rejectionExtractor
          (correctedResidualOfMonth12Candidate candidate)
          actual_upper hrat).U
        (corrected_actual_upper_tail
          candidate.rejectionExtractor
          (correctedResidualOfMonth12Candidate candidate)
          actual_upper hrat).polynomial
        (corrected_actual_upper_tail
          candidate.rejectionExtractor
          (correctedResidualOfMonth12Candidate candidate)
          actual_upper hrat).upperN :=
  corrected_actual_computed_n_eq_extractor_witness
    candidate.rejectionExtractor
    (correctedResidualOfMonth12Candidate candidate)
    actual_upper hrat

theorem correctedActualEndpointOfMonth12Candidate_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (candidate :
      Month12UnconditionalPAHilbertCheckerInternalizationCandidate
        scale_data)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured scale_data)) :
    CorrectedActualMeasuredEndpointAudit
      candidate.rejectionExtractor
      (correctedResidualOfMonth12Candidate candidate)
      actual_upper ∧
      (correctedActualEndpointOfMonth12Candidate
        candidate actual_upper).Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured scale_data)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (correctedActualEndpointOfMonth12Candidate
                candidate actual_upper).computedCollisionNOfRationality hrat =
              candidate.rejectionExtractor.witness
                (corrected_actual_upper_tail
                  candidate.rejectionExtractor
                  (correctedResidualOfMonth12Candidate candidate)
                  actual_upper hrat).U
                (corrected_actual_upper_tail
                  candidate.rejectionExtractor
                  (correctedResidualOfMonth12Candidate candidate)
                  actual_upper hrat).polynomial
                (corrected_actual_upper_tail
                  candidate.rejectionExtractor
                  (correctedResidualOfMonth12Candidate candidate)
                  actual_upper hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [correctedActualEndpointOfMonth12Candidate] using
    corrected_actual_measured_endpoint_closure
      candidate.rejectionExtractor
      (correctedResidualOfMonth12Candidate candidate)
      actual_upper

/-! ## Canonical-core adapter for the corrected actual route -/

/-- Local spelling of the Month 12 candidate generated from the Month 11
canonical checker core.  The fully qualified names avoid ambiguity between the
checker-core namespace and the Month 12 adapter namespace. -/
private def month12CandidateOfCanonicalCore
    (core :
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertCanonicalCalibratedExactnessCore) :
    Month12UnconditionalPAHilbertCheckerInternalizationCandidate
      core.scale_data :=
  SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface.PAHilbertCanonicalCalibratedExactnessCore.toMonth12UnconditionalCandidate
    core

/-- A calibrated PA/Hilbert canonical core now feeds the corrected actual route
without an intermediate hand-written candidate package. -/
def correctedActualEndpointOfCanonicalCore
    (core :
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertCanonicalCalibratedExactnessCore)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured core.scale_data)) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint core.scale_data :=
  correctedActualEndpointOfMonth12Candidate
    (month12CandidateOfCanonicalCore core)
    actual_upper

theorem correctedActualEndpointOfCanonicalCore_computed_n_eq
    (core :
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertCanonicalCalibratedExactnessCore)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured core.scale_data))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (correctedActualEndpointOfCanonicalCore
        core actual_upper).computedCollisionNOfRationality hrat =
      core.rejectionExtractor.witness
        (corrected_actual_upper_tail
          core.rejectionExtractor
          (correctedResidualOfMonth12Candidate
            (month12CandidateOfCanonicalCore core))
          actual_upper hrat).U
        (corrected_actual_upper_tail
          core.rejectionExtractor
          (correctedResidualOfMonth12Candidate
            (month12CandidateOfCanonicalCore core))
          actual_upper hrat).polynomial
        (corrected_actual_upper_tail
          core.rejectionExtractor
          (correctedResidualOfMonth12Candidate
            (month12CandidateOfCanonicalCore core))
          actual_upper hrat).upperN :=
  correctedActualEndpointOfMonth12Candidate_computed_n_eq
    (month12CandidateOfCanonicalCore core)
    actual_upper hrat

theorem correctedActualEndpointOfCanonicalCore_closure
    (core :
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertCanonicalCalibratedExactnessCore)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured core.scale_data)) :
    (correctedActualEndpointOfCanonicalCore core actual_upper).Audit ∧
      Nonempty
        (Month12UnconditionalPAHilbertCheckerInternalizationCandidate
          core.scale_data) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured core.scale_data)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (correctedActualEndpointOfCanonicalCore
            core actual_upper).computedCollisionNOfRationality hrat =
          core.rejectionExtractor.witness
            (corrected_actual_upper_tail
              core.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore core))
              actual_upper hrat).U
            (corrected_actual_upper_tail
              core.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore core))
              actual_upper hrat).polynomial
            (corrected_actual_upper_tail
              core.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore core))
              actual_upper hrat).upperN) ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    correctedActualEndpointOfMonth12Candidate_closure
      (month12CandidateOfCanonicalCore core)
      actual_upper
  exact
    ⟨hclosure.2.1,
      ⟨month12CandidateOfCanonicalCore core⟩,
      hclosure.2.2.1,
      correctedActualEndpointOfCanonicalCore_computed_n_eq core actual_upper,
      hclosure.2.2.2.2.1,
      hclosure.2.2.2.2.2⟩

/-! ## Canonical-core plus Sondow-project upper route -/

/-- The calibrated canonical core supplies the checked/actual bridge for its
own checker semantics.  This is the exact transport from checker minimum
proof-code size to root project `proof_length` on `powerBoundRawCode n`. -/
def checkedMeasuredToActualBridgeOfCanonicalCore
    (core :
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertCanonicalCalibratedExactnessCore) :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
      core.scale_data core.checkerSemantics.toProofCodeSemantics where
  checked_eq_actual := by
    intro n
    simpa [actualProofLengthMeasured,
      month9_month10_checkedProofCodeMeasured,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
      using (core.proofLengthExactness.at_powerBoundRawCode n).symm

/-- Fully assembled actual endpoint from the calibrated checker core, the
additive projection from theorem-5 source proofs to the Sondow project box, and
the Sondow rationality upper route.  The upper tail used by the endpoint is
`U + overhead`, not the original project-box `U`, so the same-object accounting
is explicit. -/
def correctedActualEndpointOfCanonicalCoreProjectUpper
    (core :
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertCanonicalCalibratedExactnessCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint core.scale_data :=
  correctedActualEndpointOfCanonicalCore core
    (actualUpperProviderOfProjectUpperAndAdditiveProjection
      projection
      (checkedMeasuredToActualBridgeOfCanonicalCore core)
      project_upper)

theorem correctedActualEndpointOfCanonicalCoreProjectUpper_closure
    (core :
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertCanonicalCalibratedExactnessCore)
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    (correctedActualEndpointOfCanonicalCoreProjectUpper
      core projection project_upper).Audit ∧
      Nonempty
        (Month12UnconditionalPAHilbertCheckerInternalizationCandidate
          core.scale_data) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured core.scale_data)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (correctedActualEndpointOfCanonicalCoreProjectUpper
          core projection project_upper).computedCollisionNOfRationality hrat =
          core.rejectionExtractor.witness
            (corrected_actual_upper_tail
              core.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore core))
              (actualUpperProviderOfProjectUpperAndAdditiveProjection
                projection
                (checkedMeasuredToActualBridgeOfCanonicalCore core)
                project_upper)
              hrat).U
            (corrected_actual_upper_tail
              core.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore core))
              (actualUpperProviderOfProjectUpperAndAdditiveProjection
                projection
                (checkedMeasuredToActualBridgeOfCanonicalCore core)
                project_upper)
              hrat).polynomial
            (corrected_actual_upper_tail
              core.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore core))
              (actualUpperProviderOfProjectUpperAndAdditiveProjection
                projection
                (checkedMeasuredToActualBridgeOfCanonicalCore core)
                project_upper)
              hrat).upperN) ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [correctedActualEndpointOfCanonicalCoreProjectUpper] using
    correctedActualEndpointOfCanonicalCore_closure core
      (actualUpperProviderOfProjectUpperAndAdditiveProjection
        projection
        (checkedMeasuredToActualBridgeOfCanonicalCore core)
        project_upper)

/-! ## Canonical-core plus split C-line upper route -/

/-- Fully assembled actual endpoint from the calibrated checker core and the
split C-line upper certificates.  This is the direct public route: the
checker core supplies the lower finite-search gap, the additive projection
transports the Sondow upper bound to the same measured object, and the C-line
certificates supply the Sondow project upper input. -/
def correctedActualEndpointOfCanonicalCoreCLineKernelCheckerLength
    (core :
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertCanonicalCalibratedExactnessCore)
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint core.scale_data :=
  correctedActualEndpointOfCanonicalCoreProjectUpper core projection
    (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
      (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
        hkernel hchecker hlength))

theorem correctedActualEndpointOfCanonicalCoreCLineKernelCheckerLength_closure
    (core :
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertCanonicalCalibratedExactnessCore)
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        core.scale_data core.checkerSemantics.toProofCodeSemantics)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    (correctedActualEndpointOfCanonicalCoreCLineKernelCheckerLength
      core projection hkernel hchecker hlength).Audit ∧
      Nonempty
        (Month12UnconditionalPAHilbertCheckerInternalizationCandidate
          core.scale_data) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured core.scale_data)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (correctedActualEndpointOfCanonicalCoreCLineKernelCheckerLength
          core projection hkernel hchecker hlength).computedCollisionNOfRationality hrat =
          core.rejectionExtractor.witness
            (corrected_actual_upper_tail
              core.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore core))
              (actualUpperProviderOfProjectUpperAndAdditiveProjection
                projection
                (checkedMeasuredToActualBridgeOfCanonicalCore core)
                (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                  (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                    hkernel hchecker hlength)))
              hrat).U
            (corrected_actual_upper_tail
              core.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore core))
              (actualUpperProviderOfProjectUpperAndAdditiveProjection
                projection
                (checkedMeasuredToActualBridgeOfCanonicalCore core)
                (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                  (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                    hkernel hchecker hlength)))
              hrat).polynomial
            (corrected_actual_upper_tail
              core.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore core))
              (actualUpperProviderOfProjectUpperAndAdditiveProjection
                projection
                (checkedMeasuredToActualBridgeOfCanonicalCore core)
                (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                  (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                    hkernel hchecker hlength)))
              hrat).upperN) ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni := by
  simpa [correctedActualEndpointOfCanonicalCoreCLineKernelCheckerLength] using
    correctedActualEndpointOfCanonicalCoreProjectUpper_closure core projection
      (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
        (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
          hkernel hchecker hlength))

/-! ## By-size calibrated checker input plus split C-line upper route -/

/-- Direct endpoint from the by-size calibrated PA/Hilbert input.  This reuses
the Month 11 checker machinery and avoids the impossible exact-scale route:
the caller supplies a Nat-valued `lengthCodeAt` with
`proof_length (powerBoundRawCode n) = lengthCodeAt n`, plus a search-gap
certificate for that calibrated size. -/
def correctedActualEndpointOfStrictScaleSingletonBySizeInputCLineKernelCheckerLength
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
        scale_data)
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data
        (input.toCanonicalCalibratedExactnessCore.checkerSemantics.toProofCodeSemantics))
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint
      input.toCanonicalCalibratedExactnessCore.scale_data :=
  correctedActualEndpointOfCanonicalCoreCLineKernelCheckerLength
    input.toCanonicalCalibratedExactnessCore
    projection hkernel hchecker hlength

theorem correctedActualEndpointOfStrictScaleSingletonBySizeInputCLineKernelCheckerLength_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
        scale_data)
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        scale_data
        (input.toCanonicalCalibratedExactnessCore.checkerSemantics.toProofCodeSemantics))
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    (correctedActualEndpointOfStrictScaleSingletonBySizeInputCLineKernelCheckerLength
      input projection hkernel hchecker hlength).Audit ∧
      Nonempty
        (Month12UnconditionalPAHilbertCheckerInternalizationCandidate
          input.toCanonicalCalibratedExactnessCore.scale_data) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured
            input.toCanonicalCalibratedExactnessCore.scale_data)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (correctedActualEndpointOfStrictScaleSingletonBySizeInputCLineKernelCheckerLength
          input projection hkernel hchecker hlength).computedCollisionNOfRationality hrat =
          input.toCanonicalCalibratedExactnessCore.rejectionExtractor.witness
            (corrected_actual_upper_tail
              input.toCanonicalCalibratedExactnessCore.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore
                  input.toCanonicalCalibratedExactnessCore))
              (actualUpperProviderOfProjectUpperAndAdditiveProjection
                projection
                (checkedMeasuredToActualBridgeOfCanonicalCore
                  input.toCanonicalCalibratedExactnessCore)
                (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                  (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                    hkernel hchecker hlength)))
              hrat).U
            (corrected_actual_upper_tail
              input.toCanonicalCalibratedExactnessCore.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore
                  input.toCanonicalCalibratedExactnessCore))
              (actualUpperProviderOfProjectUpperAndAdditiveProjection
                projection
                (checkedMeasuredToActualBridgeOfCanonicalCore
                  input.toCanonicalCalibratedExactnessCore)
                (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                  (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                    hkernel hchecker hlength)))
              hrat).polynomial
            (corrected_actual_upper_tail
              input.toCanonicalCalibratedExactnessCore.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore
                  input.toCanonicalCalibratedExactnessCore))
              (actualUpperProviderOfProjectUpperAndAdditiveProjection
                projection
                (checkedMeasuredToActualBridgeOfCanonicalCore
                  input.toCanonicalCalibratedExactnessCore)
                (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                  (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                    hkernel hchecker hlength)))
              hrat).upperN) ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    correctedActualEndpointOfCanonicalCoreCLineKernelCheckerLength_closure
      input.toCanonicalCalibratedExactnessCore
      projection hkernel hchecker hlength
  exact
    ⟨by
      simpa [
        correctedActualEndpointOfStrictScaleSingletonBySizeInputCLineKernelCheckerLength]
        using hclosure.1,
      hclosure.2.1,
      hclosure.2.2.1,
      by
        intro hrat
        simpa [
          correctedActualEndpointOfStrictScaleSingletonBySizeInputCLineKernelCheckerLength]
          using hclosure.2.2.2.1 hrat,
      hclosure.2.2.2.2.1,
      hclosure.2.2.2.2.2⟩

/-! ## Final exact checker-core input plus split C-line upper route -/

/-- Direct endpoint from the compressed final exact checker-core input.  This
is the public-facing version of the by-size route: the input carries an actual
proof-length search gap, strict powered time-constructible growth, and the
calibration from root proof length to `lengthCodeAt`; the generated canonical
core then feeds the corrected actual C-line route. -/
def correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data)
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        input.toCanonicalCalibratedExactnessCore.scale_data
        (input.toCanonicalCalibratedExactnessCore.checkerSemantics.toProofCodeSemantics))
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint
      input.toCanonicalCalibratedExactnessCore.scale_data :=
  correctedActualEndpointOfCanonicalCoreCLineKernelCheckerLength
    input.toCanonicalCalibratedExactnessCore
    projection hkernel hchecker hlength

theorem correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data)
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (projection :
      InternalPudlakTheorem5AdditiveProjectBoxProjection
        input.toCanonicalCalibratedExactnessCore.scale_data
        (input.toCanonicalCalibratedExactnessCore.checkerSemantics.toProofCodeSemantics))
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    (correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength
      input projection hkernel hchecker hlength).Audit ∧
      Nonempty
        (Month12UnconditionalPAHilbertCheckerInternalizationCandidate
          input.toCanonicalCalibratedExactnessCore.scale_data) ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured
            input.toCanonicalCalibratedExactnessCore.scale_data)) ∧
      (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
        (correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength
          input projection hkernel hchecker hlength).computedCollisionNOfRationality hrat =
          input.toCanonicalCalibratedExactnessCore.rejectionExtractor.witness
            (corrected_actual_upper_tail
              input.toCanonicalCalibratedExactnessCore.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore
                  input.toCanonicalCalibratedExactnessCore))
              (actualUpperProviderOfProjectUpperAndAdditiveProjection
                projection
                (checkedMeasuredToActualBridgeOfCanonicalCore
                  input.toCanonicalCalibratedExactnessCore)
                (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                  (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                    hkernel hchecker hlength)))
              hrat).U
            (corrected_actual_upper_tail
              input.toCanonicalCalibratedExactnessCore.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore
                  input.toCanonicalCalibratedExactnessCore))
              (actualUpperProviderOfProjectUpperAndAdditiveProjection
                projection
                (checkedMeasuredToActualBridgeOfCanonicalCore
                  input.toCanonicalCalibratedExactnessCore)
                (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                  (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                    hkernel hchecker hlength)))
              hrat).polynomial
            (corrected_actual_upper_tail
              input.toCanonicalCalibratedExactnessCore.rejectionExtractor
              (correctedResidualOfMonth12Candidate
                (month12CandidateOfCanonicalCore
                  input.toCanonicalCalibratedExactnessCore))
              (actualUpperProviderOfProjectUpperAndAdditiveProjection
                projection
                (checkedMeasuredToActualBridgeOfCanonicalCore
                  input.toCanonicalCalibratedExactnessCore)
                (sondowCLineMinimalClosureCertificate_nonempty_to_projectCollapseConclusion
                  (sondowCLineMinimalClosureCertificate_nonempty_of_kernel_checkerExact_splitLength
                    hkernel hchecker hlength)))
              hrat).upperN) ∧
        (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    correctedActualEndpointOfCanonicalCoreCLineKernelCheckerLength_closure
      input.toCanonicalCalibratedExactnessCore
      projection hkernel hchecker hlength
  exact
    ⟨by
      simpa [
        correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength]
        using hclosure.1,
      hclosure.2.1,
      hclosure.2.2.1,
      by
        intro hrat
        simpa [
          correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength]
          using hclosure.2.2.2.1 hrat,
      hclosure.2.2.2.2.1,
      hclosure.2.2.2.2.2⟩

/-! ## Payload-free checker-acceptance audit bridge -/

/-- The assumption-free payload-elimination subtarget exposed at the hard-residual
layer.  This only records concrete PA/Hilbert accepted proof-code evidence for
the ordinary and strengthened finite-consistency families; it does not mention
the root `accepted_certificate` predicate. -/
theorem hardResidualPayloadFreeCheckerAcceptance_assumptionFreeClosure
    (h : Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance) :
    h.Audit ∧
      Nonempty
        (Month9Month10PayloadFreeCheckerAcceptedFamily
          h.checker _root_.partialConsistencyCode) ∧
        Nonempty
          (Month9Month10PayloadFreeCheckerAcceptedFamily
          h.checker _root_.strengthenedPartialConsistencyCode) ∧
          (∀ n : Nat,
            SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertAcceptedProofCodeForFormulaCode
              h.checker (_root_.partialConsistencyCode n)
              (h.ordinary.proofCode n)) ∧
            (∀ n : Nat,
              SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertAcceptedProofCodeForFormulaCode
                h.checker (_root_.strengthenedPartialConsistencyCode n)
                (h.strengthened.proofCode n)) :=
  ⟨h.audit,
    ⟨h.ordinary⟩,
    ⟨h.strengthened⟩,
    h.ordinary.acceptedCode,
    h.strengthened.acceptedCode⟩

/-- The exact root-vocabulary bridge where the two root payload predicates re-enter.
Once this theorem is replaced by a checker/accepted-certificate exactness
proof, the Sondow payload side can be connected without raw payload truth. -/
theorem hardResidualPayloadFreeCheckerAcceptance_rootBridgeClosure
    (h : Month9Month10PayloadFreeCheckerAcceptanceFrontier) :
    h.Audit ∧
      _root_.PartialConsistencyAcceptedTruth ∧
        _root_.StrengthenedPartialConsistencyAcceptedTruth ∧
          (∀ n : Nat,
            _root_.accepted_certificate (_root_.partialConsistencyCode n)) ∧
            (∀ n : Nat,
              _root_.accepted_certificate
                (_root_.strengthenedPartialConsistencyCode n)) :=
  month9_month10_payload_free_checker_acceptance_frontier_closure h

/-- Payload truths obtained from the checker-acceptance frontier after crossing
the root accepted-certificate bridge.  This theorem is intentionally separated
from `hardResidualPayloadFreeCheckerAcceptance_assumptionFreeClosure`: the
assumption-free part stops at PA/Hilbert accepted proof codes, while this bridge is
the precise place where the root payload predicates re-enter. -/
theorem hardResidualPayloadTruthsOfPayloadFreeCheckerAcceptanceFrontier
    (h : Month9Month10PayloadFreeCheckerAcceptanceFrontier) :
    _root_.PartialConsistencyPayloadTruth ∧
      _root_.StrengthenedPartialConsistencyPayloadTruth :=
  ⟨h.ordinaryAcceptedTruth.toPayloadTruth,
    h.strengthenedAcceptedTruth.toPayloadTruth⟩

/-! ## Payload-free accepted route into the corrected payload endpoint -/

/-- Accepted-payload corrected route with the ordinary/strengthened accepted
truths supplied by the payload-free checker frontier.  This keeps the next
payload-elimination target narrow: prove the checker accepted-code evidence
and its root accepted-certificate bridge, then the old accepted-payload route
is reconstructed without raw payload inputs at this level. -/
structure HardResidualPayloadFreeAcceptedRouteInputs :
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
  payload_frontier : Month9Month10PayloadFreeCheckerAcceptanceFrontier
  projection_principle : _root_.PAProofLengthProjectionPrinciple
  strengthened_to_partial_projection :
    _root_.StrengthenedToPartialConsistencyConstantProjection
  partial_to_graft_projection :
    _root_.PAConjunctionEliminationConstantCost
  computable_gap :
    ComputableGapCertificate sondowProjectLocalPudlakCollisionBox

namespace HardResidualPayloadFreeAcceptedRouteInputs

def toAcceptedPayloadCorrectedRouteInputs
    (h : HardResidualPayloadFreeAcceptedRouteInputs) :
    Month9Month10AcceptedPayloadCorrectedRouteInputs where
  scale_data := h.scale_data
  checker := h.checker
  enumeration := h.enumeration
  extractor := h.extractor
  length_calibration := h.length_calibration
  verifier := h.verifier
  partial_accepted_truth := h.payload_frontier.ordinaryAcceptedTruth
  strengthened_accepted_truth :=
    h.payload_frontier.strengthenedAcceptedTruth
  projection_principle := h.projection_principle
  strengthened_to_partial_projection :=
    h.strengthened_to_partial_projection
  partial_to_graft_projection := h.partial_to_graft_projection
  computable_gap := h.computable_gap

abbrev ComputedWitnessFormula
    (h : HardResidualPayloadFreeAcceptedRouteInputs) : Prop :=
  h.toAcceptedPayloadCorrectedRouteInputs.ComputedWitnessFormula

structure Audit
    (h : HardResidualPayloadFreeAcceptedRouteInputs) :
    Prop where
  payloadFreeFrontier :
    h.payload_frontier.Audit
  payloadFreeAssumptionFree :
    h.payload_frontier.checker_acceptance.Audit
  acceptedPayloadAudit :
    h.toAcceptedPayloadCorrectedRouteInputs.Audit
  ordinaryAcceptedTruth :
    _root_.PartialConsistencyAcceptedTruth
  strengthenedAcceptedTruth :
    _root_.StrengthenedPartialConsistencyAcceptedTruth
  ordinaryPayloadTruth :
    _root_.PartialConsistencyPayloadTruth
  strengthenedPayloadTruth :
    _root_.StrengthenedPartialConsistencyPayloadTruth
  computedWitnessFormula :
    h.ComputedWitnessFormula
  contradictionAtComputedWitness :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem audit
    (h : HardResidualPayloadFreeAcceptedRouteInputs) :
    h.Audit where
  payloadFreeFrontier := h.payload_frontier.audit
  payloadFreeAssumptionFree := h.payload_frontier.checker_acceptance.audit
  acceptedPayloadAudit := h.toAcceptedPayloadCorrectedRouteInputs.audit
  ordinaryAcceptedTruth := h.payload_frontier.ordinaryAcceptedTruth
  strengthenedAcceptedTruth := h.payload_frontier.strengthenedAcceptedTruth
  ordinaryPayloadTruth :=
    (hardResidualPayloadTruthsOfPayloadFreeCheckerAcceptanceFrontier
      h.payload_frontier).1
  strengthenedPayloadTruth :=
    (hardResidualPayloadTruthsOfPayloadFreeCheckerAcceptanceFrontier
      h.payload_frontier).2
  computedWitnessFormula :=
    h.toAcceptedPayloadCorrectedRouteInputs.computed_witness_formula
  contradictionAtComputedWitness :=
    h.toAcceptedPayloadCorrectedRouteInputs.contradiction_at_computed_witness
  endpointNotRational :=
    h.toAcceptedPayloadCorrectedRouteInputs.endpoint_not_rational

theorem closure
    (h : HardResidualPayloadFreeAcceptedRouteInputs) :
    h.Audit ∧
      h.payload_frontier.Audit ∧
        h.toAcceptedPayloadCorrectedRouteInputs.Audit ∧
          _root_.PartialConsistencyAcceptedTruth ∧
            _root_.StrengthenedPartialConsistencyAcceptedTruth ∧
              _root_.PartialConsistencyPayloadTruth ∧
                _root_.StrengthenedPartialConsistencyPayloadTruth ∧
                  h.ComputedWitnessFormula ∧
                    (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
                      False) ∧
                      ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨h.audit,
    h.payload_frontier.audit,
    h.toAcceptedPayloadCorrectedRouteInputs.audit,
    h.payload_frontier.ordinaryAcceptedTruth,
    h.payload_frontier.strengthenedAcceptedTruth,
    (hardResidualPayloadTruthsOfPayloadFreeCheckerAcceptanceFrontier
      h.payload_frontier).1,
    (hardResidualPayloadTruthsOfPayloadFreeCheckerAcceptanceFrontier
      h.payload_frontier).2,
    h.toAcceptedPayloadCorrectedRouteInputs.computed_witness_formula,
    h.toAcceptedPayloadCorrectedRouteInputs.contradiction_at_computed_witness,
    h.toAcceptedPayloadCorrectedRouteInputs.endpoint_not_rational⟩

end HardResidualPayloadFreeAcceptedRouteInputs

end SondowProjectMonth11Month12HardResidualElimination
end SondowMainCheckedCodeBridge
