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

end SondowProjectMonth11Month12HardResidualElimination
end SondowMainCheckedCodeBridge
