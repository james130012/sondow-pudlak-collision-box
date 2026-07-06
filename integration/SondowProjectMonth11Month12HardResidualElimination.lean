import integration.SondowProjectMonth9Month10Month11ExactProofGapHandoff
import integration.SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint
import integration.SondowProjectMonth12UnconditionalPAHilbertInternalizationSurface

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectMonth11Month12HardResidualElimination

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10ProofLengthGapFrontier
open SondowProjectMonth9Month10Month11ExactProofGapHandoff
open SondowProjectMonth9Month10ProofLengthAxiomFreeCheckerEndpoint
open SondowProjectMonth11PAHilbertCheckerSurface
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

/-- The actual-transport blocker is not a second independent assumption: it is
exactly the family-shaped checker proof-length exactness statement rewritten as a
pointwise equality between checked measurement and `actualProofLengthMeasured`. -/
theorem checker_proof_length_family_exactness_of_actual_transport
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data}
    (transport : ActualProofLengthGapTransportBlocker checker) :
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness checker where
  proof_length_eq_minProofCodeSizeAt := by
    intro n
    simpa [actualProofLengthMeasured,
      month9_month10_checkedProofCodeMeasured,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
      using (transport.checked_eq_actual n).symm

/-- Equivalence form of the actual proof-length transport residual.  This is the
audit target for eliminating the remaining `proof_length` bridge: prove either
side, and the other side follows without changing witnesses. -/
theorem actual_transport_iff_checker_proof_length_family_exactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (checker :
      InternalPudlakTheorem5CheckerSemantics.{0} scale_data) :
    Nonempty (ActualProofLengthGapTransportBlocker checker) ↔
      Nonempty (InternalPudlakTheorem5CheckerProofLengthFamilyExactness
        checker) := by
  constructor
  · intro h
    rcases h with ⟨transport⟩
    exact ⟨checker_proof_length_family_exactness_of_actual_transport
      transport⟩
  · intro h
    rcases h with ⟨family⟩
    exact ⟨actual_transport_of_checker_proof_length_family_exactness
      family⟩

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
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
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
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
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

/-! ## Final exact checker-core with an abstract actual upper provider -/

/-- Corrected actual endpoint from the final exact checker-core input and an
abstract upper provider already stated for the actual proof-length measured
object.  This isolates the proof-length/lower-bound side from any Sondow C-line
payload assumptions. -/
def correctedActualEndpointOfFinalExactCheckerCoreInputActualUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured input.toCanonicalCalibratedExactnessCore.scale_data)) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint
      input.toCanonicalCalibratedExactnessCore.scale_data :=
  correctedActualEndpointOfCanonicalCore
    input.toCanonicalCalibratedExactnessCore actual_upper

/-- The upper tail used by the abstract actual-upper final exact route. -/
noncomputable def finalExactCheckerCoreActualUpperTail
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured input.toCanonicalCalibratedExactnessCore.scale_data))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate
      (actualProofLengthMeasured
        input.toCanonicalCalibratedExactnessCore.scale_data) :=
  corrected_actual_upper_tail
    input.toCanonicalCalibratedExactnessCore.rejectionExtractor
    (correctedResidualOfMonth12Candidate
      (month12CandidateOfCanonicalCore
        input.toCanonicalCalibratedExactnessCore))
    actual_upper hrat

theorem correctedActualEndpointOfFinalExactCheckerCoreInputActualUpper_computed_n_eq_proofLengthGapWitness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured input.toCanonicalCalibratedExactnessCore.scale_data))
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (correctedActualEndpointOfFinalExactCheckerCoreInputActualUpper
      input actual_upper).computedCollisionNOfRationality hrat =
      (input.proof_length_gap.gap_for_polynomial_upper
        (finalExactCheckerCoreActualUpperTail input actual_upper hrat).U
        (finalExactCheckerCoreActualUpperTail
          input actual_upper hrat).polynomial).witness
        (finalExactCheckerCoreActualUpperTail
          input actual_upper hrat).upperN := by
  calc
    (correctedActualEndpointOfFinalExactCheckerCoreInputActualUpper
        input actual_upper).computedCollisionNOfRationality hrat =
        input.toCanonicalCalibratedExactnessCore.rejectionExtractor.witness
          (finalExactCheckerCoreActualUpperTail input actual_upper hrat).U
          (finalExactCheckerCoreActualUpperTail
            input actual_upper hrat).polynomial
          (finalExactCheckerCoreActualUpperTail
            input actual_upper hrat).upperN := by
          simpa [correctedActualEndpointOfFinalExactCheckerCoreInputActualUpper,
            finalExactCheckerCoreActualUpperTail] using
            correctedActualEndpointOfCanonicalCore_computed_n_eq
              input.toCanonicalCalibratedExactnessCore actual_upper hrat
    _ =
        ((input.toStrictScaleSingletonExactProofLengthGapInput
          |>.transportedGap).gap_for_polynomial_upper
          (finalExactCheckerCoreActualUpperTail input actual_upper hrat).U
          (finalExactCheckerCoreActualUpperTail
            input actual_upper hrat).polynomial).witness
          (finalExactCheckerCoreActualUpperTail
            input actual_upper hrat).upperN := by
          rfl
    _ =
        (input.proof_length_gap.gap_for_polynomial_upper
          (finalExactCheckerCoreActualUpperTail input actual_upper hrat).U
          (finalExactCheckerCoreActualUpperTail
            input actual_upper hrat).polynomial).witness
          (finalExactCheckerCoreActualUpperTail
            input actual_upper hrat).upperN :=
          input.toStrictScaleSingletonExactProofLengthGapInput
            |>.transported_gap_witness_eq
              (finalExactCheckerCoreActualUpperTail
                input actual_upper hrat).U
              (finalExactCheckerCoreActualUpperTail
                input actual_upper hrat).polynomial
              (finalExactCheckerCoreActualUpperTail
                input actual_upper hrat).upperN

/-- Payload-free audit package for the final exact checker-core route with an
abstract actual upper provider.  Any remaining Sondow-side payload assumptions
enter only when such an `actual_upper` is instantiated from the C-line route. -/
structure FinalExactCheckerCoreActualUpperAudit
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured input.toCanonicalCalibratedExactnessCore.scale_data)) :
    Prop where
  endpointAudit :
    (correctedActualEndpointOfFinalExactCheckerCoreInputActualUpper
      input actual_upper).Audit
  finalExactCertificate :
    Nonempty
      (SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate
        scale_data)
  actualProofLengthGap :
    Nonempty
      (ComputableSearchGapCertificate
        (actualProofLengthMeasured scale_data))
  computedNFromProofLengthGap :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (correctedActualEndpointOfFinalExactCheckerCoreInputActualUpper
        input actual_upper).computedCollisionNOfRationality hrat =
        (input.proof_length_gap.gap_for_polynomial_upper
          (finalExactCheckerCoreActualUpperTail input actual_upper hrat).U
          (finalExactCheckerCoreActualUpperTail
            input actual_upper hrat).polynomial).witness
          (finalExactCheckerCoreActualUpperTail
            input actual_upper hrat).upperN
  contradictionAtComputedN :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem finalExactCheckerCoreActualUpperAudit_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data)
    (actual_upper :
      Month9Month10AbstractMeasuredUpperProvider
        (actualProofLengthMeasured input.toCanonicalCalibratedExactnessCore.scale_data)) :
    FinalExactCheckerCoreActualUpperAudit input actual_upper ∧
      (correctedActualEndpointOfFinalExactCheckerCoreInputActualUpper
        input actual_upper).Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured scale_data)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (correctedActualEndpointOfFinalExactCheckerCoreInputActualUpper
              input actual_upper).computedCollisionNOfRationality hrat =
              (input.proof_length_gap.gap_for_polynomial_upper
                (finalExactCheckerCoreActualUpperTail
                  input actual_upper hrat).U
                (finalExactCheckerCoreActualUpperTail
                  input actual_upper hrat).polynomial).witness
                (finalExactCheckerCoreActualUpperTail
                  input actual_upper hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    correctedActualEndpointOfCanonicalCore_closure
      input.toCanonicalCalibratedExactnessCore actual_upper
  have hgap :
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) := by
    simpa [actualProofLengthMeasured] using ⟨input.proof_length_gap⟩
  exact
    ⟨{
      endpointAudit := by
        simpa [correctedActualEndpointOfFinalExactCheckerCoreInputActualUpper]
          using hclosure.1
      finalExactCertificate := input.certificate_nonempty
      actualProofLengthGap := hgap
      computedNFromProofLengthGap :=
        correctedActualEndpointOfFinalExactCheckerCoreInputActualUpper_computed_n_eq_proofLengthGapWitness
          input actual_upper
      contradictionAtComputedN := hclosure.2.2.2.2.1
      endpointNotRational := hclosure.2.2.2.2.2 },
      by
        simpa [correctedActualEndpointOfFinalExactCheckerCoreInputActualUpper]
          using hclosure.1,
      hgap,
      correctedActualEndpointOfFinalExactCheckerCoreInputActualUpper_computed_n_eq_proofLengthGapWitness
        input actual_upper,
      hclosure.2.2.2.2.1,
      hclosure.2.2.2.2.2⟩

/-! ## Final exact checker-core computed-witness audit -/

/-- The actual upper tail used by the final exact checker-core route after
transporting the Sondow C-line upper proof to the same actual proof-length
measurement as the lower finite-search gap. -/
noncomputable def finalExactCheckerCoreCorrectedUpperTail
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
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate
      (actualProofLengthMeasured
        input.toCanonicalCalibratedExactnessCore.scale_data) :=
  corrected_actual_upper_tail
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
    hrat

/-- The final exact checker-core endpoint computes its collision index by
applying the supplied actual proof-length gap certificate to the transported
C-line upper tail.  This is the audit equation that ties the endpoint's
computed `n` directly to the gap-certificate witness, not merely to an abstract
existence theorem. -/
theorem correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength_computed_n_eq_proofLengthGapWitness
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
        SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength
      input projection hkernel hchecker hlength).computedCollisionNOfRationality hrat =
      (input.proof_length_gap.gap_for_polynomial_upper
        (finalExactCheckerCoreCorrectedUpperTail
          input projection hkernel hchecker hlength hrat).U
        (finalExactCheckerCoreCorrectedUpperTail
          input projection hkernel hchecker hlength hrat).polynomial).witness
        (finalExactCheckerCoreCorrectedUpperTail
          input projection hkernel hchecker hlength hrat).upperN := by
  calc
    (correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength
        input projection hkernel hchecker hlength).computedCollisionNOfRationality hrat =
        input.toCanonicalCalibratedExactnessCore.rejectionExtractor.witness
          (finalExactCheckerCoreCorrectedUpperTail
            input projection hkernel hchecker hlength hrat).U
          (finalExactCheckerCoreCorrectedUpperTail
            input projection hkernel hchecker hlength hrat).polynomial
          (finalExactCheckerCoreCorrectedUpperTail
            input projection hkernel hchecker hlength hrat).upperN := by
          simpa [finalExactCheckerCoreCorrectedUpperTail] using
            correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength_closure
              input projection hkernel hchecker hlength |>.2.2.2.1 hrat
    _ =
        ((input.toStrictScaleSingletonExactProofLengthGapInput
          |>.transportedGap).gap_for_polynomial_upper
          (finalExactCheckerCoreCorrectedUpperTail
            input projection hkernel hchecker hlength hrat).U
          (finalExactCheckerCoreCorrectedUpperTail
            input projection hkernel hchecker hlength hrat).polynomial).witness
          (finalExactCheckerCoreCorrectedUpperTail
            input projection hkernel hchecker hlength hrat).upperN := by
          rfl
    _ =
        (input.proof_length_gap.gap_for_polynomial_upper
          (finalExactCheckerCoreCorrectedUpperTail
            input projection hkernel hchecker hlength hrat).U
          (finalExactCheckerCoreCorrectedUpperTail
            input projection hkernel hchecker hlength hrat).polynomial).witness
          (finalExactCheckerCoreCorrectedUpperTail
            input projection hkernel hchecker hlength hrat).upperN :=
          input.toStrictScaleSingletonExactProofLengthGapInput
            |>.transported_gap_witness_eq
              (finalExactCheckerCoreCorrectedUpperTail
                input projection hkernel hchecker hlength hrat).U
              (finalExactCheckerCoreCorrectedUpperTail
                input projection hkernel hchecker hlength hrat).polynomial
              (finalExactCheckerCoreCorrectedUpperTail
                input projection hkernel hchecker hlength hrat).upperN

/-- Terminal audit package for the corrected final exact checker-core route.
It records that the exact-scale certificate shape is blocked, while the
corrected actual-proof-length route still produces an explicit collision
witness from the supplied actual gap certificate. -/
structure FinalExactCheckerCoreCorrectedRouteAudit
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
    Prop where
  exactScaleFinalThreeBlocked :
    ∀ _ :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalThreeCertificateEndpoint
        scale_data,
      False
  endpointAudit :
    (correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength
      input projection hkernel hchecker hlength).Audit
  finalExactCertificate :
    Nonempty
      (SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreCertificate
        scale_data)
  actualProofLengthGap :
    Nonempty
      (ComputableSearchGapCertificate
        (actualProofLengthMeasured scale_data))
  computedNFromProofLengthGap :
    ∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      (correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength
        input projection hkernel hchecker hlength).computedCollisionNOfRationality hrat =
        (input.proof_length_gap.gap_for_polynomial_upper
          (finalExactCheckerCoreCorrectedUpperTail
            input projection hkernel hchecker hlength hrat).U
          (finalExactCheckerCoreCorrectedUpperTail
            input projection hkernel hchecker hlength hrat).polynomial).witness
          (finalExactCheckerCoreCorrectedUpperTail
            input projection hkernel hchecker hlength hrat).upperN
  contradictionAtComputedN :
    ∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False
  endpointNotRational :
    ¬ _root_.is_rational _root_.euler_mascheroni

theorem finalExactCheckerCoreCorrectedRouteAudit_closure
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
    FinalExactCheckerCoreCorrectedRouteAudit
      input projection hkernel hchecker hlength ∧
      (correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength
        input projection hkernel hchecker hlength).Audit ∧
        Nonempty
          (ComputableSearchGapCertificate
            (actualProofLengthMeasured scale_data)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength
              input projection hkernel hchecker hlength).computedCollisionNOfRationality hrat =
              (input.proof_length_gap.gap_for_polynomial_upper
                (finalExactCheckerCoreCorrectedUpperTail
                  input projection hkernel hchecker hlength hrat).U
                (finalExactCheckerCoreCorrectedUpperTail
                  input projection hkernel hchecker hlength hrat).polynomial).witness
                (finalExactCheckerCoreCorrectedUpperTail
                  input projection hkernel hchecker hlength hrat).upperN) ∧
            (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
              False) ∧
              ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength_closure
      input projection hkernel hchecker hlength
  have hgap :
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured scale_data)) := by
    simpa [actualProofLengthMeasured] using ⟨input.proof_length_gap⟩
  exact
    ⟨{
      exactScaleFinalThreeBlocked := by
        intro endpoint
        exact finalThreeCertificateEndpoint_exactScale_impossible endpoint
      endpointAudit := hclosure.1
      finalExactCertificate := input.certificate_nonempty
      actualProofLengthGap := hgap
      computedNFromProofLengthGap :=
        correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength_computed_n_eq_proofLengthGapWitness
          input projection hkernel hchecker hlength
      contradictionAtComputedN := hclosure.2.2.2.2.1
      endpointNotRational := hclosure.2.2.2.2.2 },
      hclosure.1,
      hgap,
      correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength_computed_n_eq_proofLengthGapWitness
        input projection hkernel hchecker hlength,
      hclosure.2.2.2.2.1,
      hclosure.2.2.2.2.2⟩

/-! ## Final exact checker-core from calibrated-size gap -/

/-- Strict growth of the theorem-5 scale gives injectivity of the scale.  This
standalone form avoids hiding the same trichotomy proof inside later adapters. -/
theorem scale_injective_of_scale_strict
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

/-- Strict growth of the scale makes the theorem-5 raw-code family injective. -/
theorem powerBoundRawCode_injective_of_scale_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b) :
    Function.Injective scale_data.powerBoundRawCode :=
  concretePAHilbert_powerBoundRawCode_injective_of_scale_injective
    scale_data (scale_injective_of_scale_strict scale_strict)

/-- For the concrete calibrated PA/Hilbert checker, checked minimum proof-code
measurement is exactly the calibrated `lengthCodeAt` measurement once the raw
theorem-5 code family is injective.  This is proof-length-free: it is a checker
minimum-size fact, not a root `proof_length` fact. -/
theorem checkedMeasured_eq_lengthCodeAt_of_calibrated_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    (n : Nat) :
    month9_month10_checkedProofCodeMeasured scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics n =
      (lengthCodeAt n : Real) := by
  have hmin :
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        n = lengthCodeAt n :=
    concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
      scale_data lengthCodeAt n hinjective
  have hmin_real :
      ((InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        n : Nat) : Real) = (lengthCodeAt n : Real) := by
    exact_mod_cast hmin
  simpa [month9_month10_checkedProofCodeMeasured,
    InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
    using hmin_real

/-- For the concrete calibrated PA/Hilbert checker, project length on the
theorem-5 raw-code family is exactly the calibrated `lengthCodeAt` measurement.
This is still proof-length-free: it identifies the checker-induced
`projectLength`, not the root `proof_length`. -/
theorem calibratedProjectLength_eq_lengthCodeAt_of_injective
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (fallback : _root_.FormulaCode → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    (n : Nat) :
    month9_month10_checkerProjectLengthMeasured scale_data
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt).toProofCodeSemantics fallback n =
      (lengthCodeAt n : Real) := by
  simpa [month9_month10_checkerProjectLengthMeasured] using
    concretePAHilbertPowerBoundCalibrated_projectLengthAt_eq_lengthCodeAt_of_injective
      scale_data lengthCodeAt fallback n hinjective

/-- The remaining root proof-length calibration to `lengthCodeAt` is equivalent
to saying that the actual theorem-5 proof length agrees with the concrete
calibrated checker `projectLength` on the raw-code family.  This does not solve
the root bridge, but states its exact local form without an extra scale or search
assumption. -/
theorem proofLength_eq_lengthCodeAt_iff_actual_eq_calibratedProjectLength
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (fallback : _root_.FormulaCode → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode) :
    (∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (lengthCodeAt n : Real)) ↔
      (∀ n : Nat,
        actualProofLengthMeasured scale_data n =
          month9_month10_checkerProjectLengthMeasured scale_data
            (concretePAHilbertPowerBoundCalibratedCheckerSemantics
              scale_data lengthCodeAt).toProofCodeSemantics fallback n) := by
  constructor
  · intro h n
    calc
      actualProofLengthMeasured scale_data n =
          _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) := rfl
      _ = (lengthCodeAt n : Real) := h n
      _ =
          month9_month10_checkerProjectLengthMeasured scale_data
            (concretePAHilbertPowerBoundCalibratedCheckerSemantics
              scale_data lengthCodeAt).toProofCodeSemantics fallback n :=
          (calibratedProjectLength_eq_lengthCodeAt_of_injective
            lengthCodeAt fallback hinjective n).symm
  · intro h n
    calc
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
          actualProofLengthMeasured scale_data n := rfl
      _ =
          month9_month10_checkerProjectLengthMeasured scale_data
            (concretePAHilbertPowerBoundCalibratedCheckerSemantics
              scale_data lengthCodeAt).toProofCodeSemantics fallback n := h n
      _ = (lengthCodeAt n : Real) :=
          calibratedProjectLength_eq_lengthCodeAt_of_injective
            lengthCodeAt fallback hinjective n

/-- A checker proof-length exactness certificate is exactly enough to identify
the actual theorem-5 proof-length measurement with the checker `projectLength`
replacement on the raw-code family. -/
theorem actual_eq_projectLength_of_checkerProofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {checker : InternalPudlakTheorem5CheckerSemantics scale_data}
    (exactness : InternalPudlakTheorem5CheckerProofLengthExactness checker)
    (fallback : _root_.FormulaCode → Nat)
    (n : Nat) :
    actualProofLengthMeasured scale_data n =
      month9_month10_checkerProjectLengthMeasured scale_data
        checker.toProofCodeSemantics fallback n := by
  calc
    actualProofLengthMeasured scale_data n =
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) := rfl
    _ = (checker.minProofCodeSizeAt n : Real) :=
        exactness.at_powerBoundRawCode n
    _ = month9_month10_checkedProofCodeMeasured scale_data
          checker.toProofCodeSemantics n := by
        rfl
    _ = month9_month10_checkerProjectLengthMeasured scale_data
          checker.toProofCodeSemantics fallback n :=
        (month9_month10_checkerProjectLengthMeasured_eq_checkedProofCodeMeasured
          scale_data checker.toProofCodeSemantics fallback n).symm

/-- No-fallback calibrated checker bridge: checker proof-length exactness plus
raw-code injectivity supplies the by-size root calibration
`proof_length(powerBoundRawCode n) = lengthCodeAt n`. -/
theorem proofLength_eq_lengthCodeAt_of_calibratedCheckerProofLengthExactness_of_injective
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
        (lengthCodeAt n : Real) :=
  fun n => by
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

/-- Backward-compatible form of
`proofLength_eq_lengthCodeAt_of_calibratedCheckerProofLengthExactness_of_injective`.
The `fallback` argument is ignored; it is kept only for older endpoint adapters. -/
theorem proofLength_eq_lengthCodeAt_of_calibratedCheckerProofLengthExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (_fallback : _root_.FormulaCode → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)) :
    ∀ n : Nat,
      _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n) =
        (lengthCodeAt n : Real) :=
  proofLength_eq_lengthCodeAt_of_calibratedCheckerProofLengthExactness_of_injective
    lengthCodeAt hinjective exactness

/-- A concrete calibrated rejection extractor generates the `lengthCodeAt`
computable search gap.  The witness is inherited from the extractor through the
checked/minimum-size gap; no root proof-length calibration is used here. -/
def lengthCodeAtGapOfCalibratedExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration) :
    ComputableSearchGapCertificate
      (fun n : Nat => (lengthCodeAt n : Real)) :=
  transportComputableSearchGap
    (fun n =>
      checkedMeasured_eq_lengthCodeAt_of_calibrated_injective
        lengthCodeAt hinjective n)
    (checked_minProofCodeSize_gap_constructor extractor)

theorem lengthCodeAtGapOfCalibratedExtractor_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (hinjective : Function.Injective scale_data.powerBoundRawCode)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((lengthCodeAtGapOfCalibratedExtractor
        lengthCodeAt hinjective extractor)
      |>.gap_for_polynomial_upper U hU).witness N =
      extractor.witness U hU N :=
  rfl

/-- Build the strict-scale singleton search input from a concrete calibrated
rejection extractor.  This is the proof-length-free construction layer: it
uses the extractor-generated `lengthCodeAt` search gap and does not require any
root `proof_length = lengthCodeAt` calibration. -/
def strictScaleSingletonSearchInputOfCalibratedExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput scale_data where
  lengthCodeAt := lengthCodeAt
  scale_strict := scale_strict
  gap :=
    lengthCodeAtGapOfCalibratedExtractor lengthCodeAt
      (powerBoundRawCode_injective_of_scale_strict scale_strict)
      extractor

theorem strictScaleSingletonSearchInputOfCalibratedExtractor_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((strictScaleSingletonSearchInputOfCalibratedExtractor
        lengthCodeAt scale_strict extractor).gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      extractor.witness U hU N :=
  rfl

/-- Executable-search form of the strict-scale singleton search input.  The
executable PA/Hilbert rejection search supplies the same witness function used
by the lower-bound route, still before any root proof-length calibration. -/
def strictScaleSingletonSearchInputOfExecutableRejectionSearch
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput scale_data :=
  strictScaleSingletonSearchInputOfCalibratedExtractor
    lengthCodeAt scale_strict search.toCheckerExtractor

theorem strictScaleSingletonSearchInputOfExecutableRejectionSearch_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((strictScaleSingletonSearchInputOfExecutableRejectionSearch
        lengthCodeAt scale_strict enumeration search).gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      search.witness U hU N :=
  rfl

/-- Time-bound form of the strict-scale singleton search input from a concrete
calibrated rejection extractor.  The scale strictness is generated from the
primitive time-bound strictness and nonzero exponent, so this construction
matches the theorem-5 scale-data obligations directly. -/
def strictScaleSingletonSearchInputOfCalibratedExtractorTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput scale_data :=
  strictScaleSingletonSearchInputOfCalibratedExtractor
    lengthCodeAt
    (your_scale_strict_theorem time_bound_strict exponent_ne_zero)
    extractor

theorem strictScaleSingletonSearchInputOfCalibratedExtractorTimeBound_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((strictScaleSingletonSearchInputOfCalibratedExtractorTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero extractor).gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      extractor.witness U hU N :=
  rfl

theorem strictScaleSingletonSearchInputOfCalibratedExtractorTimeBound_rejectionExtractor_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (strictScaleSingletonSearchInputOfCalibratedExtractorTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero extractor).rejectionExtractor.witness U hU N =
      extractor.witness U hU N :=
  rfl

/-- Time-bound executable-search form of the strict-scale singleton search
input.  This is the proof-length-free construction closest to the theorem-5
scale-data surface: time-bound monotonicity supplies scale strictness, and the
executable search supplies the rejection witness. -/
def strictScaleSingletonSearchInputOfExecutableRejectionSearchTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonSearchInput scale_data :=
  strictScaleSingletonSearchInputOfExecutableRejectionSearch
    lengthCodeAt
    (your_scale_strict_theorem time_bound_strict exponent_ne_zero)
    enumeration search

theorem strictScaleSingletonSearchInputOfExecutableRejectionSearchTimeBound_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((strictScaleSingletonSearchInputOfExecutableRejectionSearchTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero enumeration search).gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      search.witness U hU N :=
  rfl

theorem strictScaleSingletonSearchInputOfExecutableRejectionSearchTimeBound_rejectionExtractor_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (strictScaleSingletonSearchInputOfExecutableRejectionSearchTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero enumeration search).rejectionExtractor.witness U hU N =
      search.witness U hU N :=
  rfl

/-- Proof-length-free checked-upper closure from a time-bound calibrated
extractor.  This closes the checked route directly at the theorem-5 scale-data
surface and records the computed collision index as the extractor witness. -/
theorem proofLengthFreeCheckedUpperClosureOfCalibratedExtractorTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (upper_provider :
      (strictScaleSingletonSearchInputOfCalibratedExtractorTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero extractor)
        |>.toProofLengthFreeMonth12Candidate
        |>.checkedMeasuredUpperProviderType) :
    let input :=
      strictScaleSingletonSearchInputOfCalibratedExtractorTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero extractor
    (input.toProofLengthAxiomFreeCheckedUpperProvider upper_provider).Audit ∧
      (input.toProofLengthAxiomFreeCheckedUpperProvider
        upper_provider).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (input.toProofLengthAxiomFreeCheckedUpperProvider
            upper_provider).computedCollisionNOfRationality hrat =
            extractor.witness
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate upper_provider hrat).U
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate upper_provider hrat).polynomial
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate upper_provider hrat).upperN) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (checkedSearchUpperTail
              input.toProofLengthFreeMonth12Candidate upper_provider hrat).U
                ((input.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat) <
              month9_month10_checkedProofCodeMeasured
                scale_data input.checkerSemantics.toProofCodeSemantics
                ((input.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            month9_month10_checkedProofCodeMeasured
                scale_data input.checkerSemantics.toProofCodeSemantics
                ((input.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat) ≤
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate upper_provider hrat).U
                ((input.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let input :=
    strictScaleSingletonSearchInputOfCalibratedExtractorTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero extractor
  rcases input.checkedUpperProvider_closure upper_provider with
    ⟨haudit, hendpoint, hcomputed, hlower, hupper, hfalse, hnot⟩
  refine ⟨haudit, hendpoint, ?_, hlower, hupper, hfalse, hnot⟩
  intro hrat
  let tail :=
    checkedSearchUpperTail input.toProofLengthFreeMonth12Candidate
      upper_provider hrat
  calc
    (input.toProofLengthAxiomFreeCheckedUpperProvider
        upper_provider).computedCollisionNOfRationality hrat =
        input.rejectionExtractor.witness tail.U tail.polynomial tail.upperN :=
          hcomputed hrat
    _ = extractor.witness tail.U tail.polynomial tail.upperN := by
          simpa [input, tail] using
            strictScaleSingletonSearchInputOfCalibratedExtractorTimeBound_rejectionExtractor_witness_eq
              lengthCodeAt time_bound_strict exponent_ne_zero extractor
              tail.U tail.polynomial tail.upperN

/-- Executable-search version of
`proofLengthFreeCheckedUpperClosureOfCalibratedExtractorTimeBound`.  The
computed collision index is the executable search witness itself. -/
theorem proofLengthFreeCheckedUpperClosureOfExecutableRejectionSearchTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (upper_provider :
      (strictScaleSingletonSearchInputOfExecutableRejectionSearchTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero enumeration search)
        |>.toProofLengthFreeMonth12Candidate
        |>.checkedMeasuredUpperProviderType) :
    let input :=
      strictScaleSingletonSearchInputOfExecutableRejectionSearchTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero enumeration search
    (input.toProofLengthAxiomFreeCheckedUpperProvider upper_provider).Audit ∧
      (input.toProofLengthAxiomFreeCheckedUpperProvider
        upper_provider).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (input.toProofLengthAxiomFreeCheckedUpperProvider
            upper_provider).computedCollisionNOfRationality hrat =
            search.witness
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate upper_provider hrat).U
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate upper_provider hrat).polynomial
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate upper_provider hrat).upperN) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (checkedSearchUpperTail
              input.toProofLengthFreeMonth12Candidate upper_provider hrat).U
                ((input.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat) <
              month9_month10_checkedProofCodeMeasured
                scale_data input.checkerSemantics.toProofCodeSemantics
                ((input.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            month9_month10_checkedProofCodeMeasured
                scale_data input.checkerSemantics.toProofCodeSemantics
                ((input.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat) ≤
              (checkedSearchUpperTail
                input.toProofLengthFreeMonth12Candidate upper_provider hrat).U
                ((input.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let input :=
    strictScaleSingletonSearchInputOfExecutableRejectionSearchTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero enumeration search
  rcases input.checkedUpperProvider_closure upper_provider with
    ⟨haudit, hendpoint, hcomputed, hlower, hupper, hfalse, hnot⟩
  refine ⟨haudit, hendpoint, ?_, hlower, hupper, hfalse, hnot⟩
  intro hrat
  let tail :=
    checkedSearchUpperTail input.toProofLengthFreeMonth12Candidate
      upper_provider hrat
  calc
    (input.toProofLengthAxiomFreeCheckedUpperProvider
        upper_provider).computedCollisionNOfRationality hrat =
        input.rejectionExtractor.witness tail.U tail.polynomial tail.upperN :=
          hcomputed hrat
    _ = search.witness tail.U tail.polynomial tail.upperN := by
          simpa [input, tail] using
            strictScaleSingletonSearchInputOfExecutableRejectionSearchTimeBound_rejectionExtractor_witness_eq
              lengthCodeAt time_bound_strict exponent_ne_zero enumeration search
              tail.U tail.polynomial tail.upperN

/-- Direct contradiction endpoint for the time-bound calibrated-extractor
checked route. -/
theorem proofLengthFreeContradictionOfCalibratedExtractorTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (upper_provider :
      (strictScaleSingletonSearchInputOfCalibratedExtractorTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero extractor)
        |>.toProofLengthFreeMonth12Candidate
        |>.checkedMeasuredUpperProviderType)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False := by
  rcases proofLengthFreeCheckedUpperClosureOfCalibratedExtractorTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero extractor
      upper_provider with
    ⟨_, _, _, _, _, hfalse, _⟩
  exact hfalse hrat

theorem proofLengthFreeNotRationalOfCalibratedExtractorTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (upper_provider :
      (strictScaleSingletonSearchInputOfCalibratedExtractorTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero extractor)
        |>.toProofLengthFreeMonth12Candidate
        |>.checkedMeasuredUpperProviderType) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases proofLengthFreeCheckedUpperClosureOfCalibratedExtractorTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero extractor
      upper_provider with
    ⟨_, _, _, _, _, _, hnot⟩
  exact hnot

/-- Direct contradiction endpoint for the time-bound executable checked route.
-/
theorem proofLengthFreeContradictionOfExecutableRejectionSearchTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (upper_provider :
      (strictScaleSingletonSearchInputOfExecutableRejectionSearchTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero enumeration search)
        |>.toProofLengthFreeMonth12Candidate
        |>.checkedMeasuredUpperProviderType)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False := by
  rcases proofLengthFreeCheckedUpperClosureOfExecutableRejectionSearchTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero enumeration search
      upper_provider with
    ⟨_, _, _, _, _, hfalse, _⟩
  exact hfalse hrat

theorem proofLengthFreeNotRationalOfExecutableRejectionSearchTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (upper_provider :
      (strictScaleSingletonSearchInputOfExecutableRejectionSearchTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero enumeration search)
        |>.toProofLengthFreeMonth12Candidate
        |>.checkedMeasuredUpperProviderType) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases proofLengthFreeCheckedUpperClosureOfExecutableRejectionSearchTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero enumeration search
      upper_provider with
    ⟨_, _, _, _, _, _, hnot⟩
  exact hnot

/-- Time-bound form of the strict-scale singleton tail-gap input.  This keeps
the hard lower-bound residual as exactly the explicit tail-gap certificate,
while scale strictness is generated from theorem-5 scale data. -/
def strictScaleSingletonTailGapInputOfTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real))) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonTailGapInput scale_data where
  lengthCodeAt := lengthCodeAt
  scale_strict := your_scale_strict_theorem time_bound_strict exponent_ne_zero
  tail_gap := tail_gap

theorem strictScaleSingletonTailGapInputOfTimeBound_threshold_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) :
    ((strictScaleSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap).tail_gap
      |>.gap_for_polynomial_upper U hU).threshold =
      (tail_gap.gap_for_polynomial_upper U hU).threshold :=
  rfl

/-- The rejection witness generated by a time-bound singleton tail-gap input is
definitionally the explicit `max N threshold` witness of the original tail-gap
certificate.  This removes the witness-calibration parameter for the
tail-gap-generated search route itself. -/
theorem strictScaleSingletonTailGapInputOfTimeBound_rejectionExtractor_witness_eq_max
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((strictScaleSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap)
      |>.toSearchInput).rejectionExtractor.witness U hU N =
      max N (tail_gap.gap_for_polynomial_upper U hU).threshold :=
  rfl

/-- Tail-gap checked-upper closure at the theorem-5 time-bound surface.  This
is the explicit big-`N` route: the computed collision index is the auditable
`max upperN threshold` number from the supplied tail-gap certificate. -/
theorem tailGapMaxCheckedUpperClosureOfTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (upper_provider :
      ((strictScaleSingletonTailGapInputOfTimeBound
          lengthCodeAt time_bound_strict exponent_ne_zero tail_gap).toSearchInput)
        |>.toProofLengthFreeMonth12Candidate
        |>.checkedMeasuredUpperProviderType) :
    let input :=
      strictScaleSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
    (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
      upper_provider).Audit ∧
      (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
        upper_provider).endpoint.Audit ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
            upper_provider).computedCollisionNOfRationality hrat =
            max
              (checkedSearchUpperTail
                input.toSearchInput.toProofLengthFreeMonth12Candidate
                upper_provider hrat).upperN
              (tail_gap.gap_for_polynomial_upper
                (checkedSearchUpperTail
                  input.toSearchInput.toProofLengthFreeMonth12Candidate
                  upper_provider hrat).U
                (checkedSearchUpperTail
                  input.toSearchInput.toProofLengthFreeMonth12Candidate
                  upper_provider hrat).polynomial).threshold) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            (checkedSearchUpperTail
              input.toSearchInput.toProofLengthFreeMonth12Candidate
              upper_provider hrat).U
                ((input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat) <
              month9_month10_checkedProofCodeMeasured
                scale_data input.toSearchInput.checkerSemantics.toProofCodeSemantics
                ((input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
            month9_month10_checkedProofCodeMeasured
                scale_data input.toSearchInput.checkerSemantics.toProofCodeSemantics
                ((input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat) ≤
              (checkedSearchUpperTail
                input.toSearchInput.toProofLengthFreeMonth12Candidate
                upper_provider hrat).U
                ((input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
                  upper_provider).computedCollisionNOfRationality hrat)) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let input :=
    strictScaleSingletonTailGapInputOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
  rcases input.toSearchInput.checkedUpperProvider_closure upper_provider with
    ⟨haudit, hendpoint, hcomputed, hlower, hupper, hfalse, hnot⟩
  refine ⟨haudit, hendpoint, ?_, hlower, hupper, hfalse, hnot⟩
  intro hrat
  let tail :=
    checkedSearchUpperTail
      input.toSearchInput.toProofLengthFreeMonth12Candidate upper_provider hrat
  calc
    (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
        upper_provider).computedCollisionNOfRationality hrat =
        input.toSearchInput.rejectionExtractor.witness
          tail.U tail.polynomial tail.upperN :=
          hcomputed hrat
    _ = max tail.upperN
          (tail_gap.gap_for_polynomial_upper
            tail.U tail.polynomial).threshold := by
          rfl

/-- The computed collision index of the time-bound tail-gap checked route is
exactly the rejection extractor witness generated from the same tail-gap input.
Unlike the external executable-search comparison, this needs no separate witness
calibration hypothesis. -/
theorem tailGapComputedN_eq_tailGapRejectionExtractorWitnessOfTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (upper_provider :
      ((strictScaleSingletonTailGapInputOfTimeBound
          lengthCodeAt time_bound_strict exponent_ne_zero tail_gap).toSearchInput)
        |>.toProofLengthFreeMonth12Candidate
        |>.checkedMeasuredUpperProviderType)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let input :=
      strictScaleSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
    let checkedTail :=
      checkedSearchUpperTail
        input.toSearchInput.toProofLengthFreeMonth12Candidate upper_provider hrat
    (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
      upper_provider).computedCollisionNOfRationality hrat =
      input.toSearchInput.rejectionExtractor.witness
        checkedTail.U checkedTail.polynomial checkedTail.upperN := by
  dsimp
  let input :=
    strictScaleSingletonTailGapInputOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
  let checkedTail :=
    checkedSearchUpperTail
      input.toSearchInput.toProofLengthFreeMonth12Candidate upper_provider hrat
  rcases input.toSearchInput.checkedUpperProvider_closure upper_provider with
    ⟨_, _, hcomputed, _, _, _, _⟩
  exact hcomputed hrat

/-- Full tail-gap witness calibration for the time-bound checked route.  The
provider-computed index, the tail-gap-generated rejection witness, and the
explicit `max upperN threshold` number are the same natural number. -/
theorem tailGapComputedN_tailGapWitnessCalibrationOfTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (upper_provider :
      ((strictScaleSingletonTailGapInputOfTimeBound
          lengthCodeAt time_bound_strict exponent_ne_zero tail_gap).toSearchInput)
        |>.toProofLengthFreeMonth12Candidate
        |>.checkedMeasuredUpperProviderType)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let input :=
      strictScaleSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
    let checkedTail :=
      checkedSearchUpperTail
        input.toSearchInput.toProofLengthFreeMonth12Candidate upper_provider hrat
    (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
      upper_provider).computedCollisionNOfRationality hrat =
        input.toSearchInput.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN ∧
      input.toSearchInput.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN =
        max checkedTail.upperN
          (tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold ∧
      (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
        upper_provider).computedCollisionNOfRationality hrat =
        max checkedTail.upperN
          (tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold := by
  dsimp
  let input :=
    strictScaleSingletonTailGapInputOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
  let checkedTail :=
    checkedSearchUpperTail
      input.toSearchInput.toProofLengthFreeMonth12Candidate upper_provider hrat
  have hwitness :
      input.toSearchInput.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN =
        max checkedTail.upperN
          (tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold := by
    simpa [input, checkedTail] using
      strictScaleSingletonTailGapInputOfTimeBound_rejectionExtractor_witness_eq_max
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
        checkedTail.U checkedTail.polynomial checkedTail.upperN
  have hcomputed :
      (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
        upper_provider).computedCollisionNOfRationality hrat =
        input.toSearchInput.rejectionExtractor.witness
          checkedTail.U checkedTail.polynomial checkedTail.upperN :=
    tailGapComputedN_eq_tailGapRejectionExtractorWitnessOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap upper_provider hrat
  exact ⟨hcomputed, hwitness, hcomputed.trans hwitness⟩

theorem tailGapContradictionOfTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (upper_provider :
      ((strictScaleSingletonTailGapInputOfTimeBound
          lengthCodeAt time_bound_strict exponent_ne_zero tail_gap).toSearchInput)
        |>.toProofLengthFreeMonth12Candidate
        |>.checkedMeasuredUpperProviderType)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    False := by
  rcases tailGapMaxCheckedUpperClosureOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
      upper_provider with
    ⟨_, _, _, _, _, hfalse, _⟩
  exact hfalse hrat

theorem tailGapNotRationalOfTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (upper_provider :
      ((strictScaleSingletonTailGapInputOfTimeBound
          lengthCodeAt time_bound_strict exponent_ne_zero tail_gap).toSearchInput)
        |>.toProofLengthFreeMonth12Candidate
        |>.checkedMeasuredUpperProviderType) :
    ¬ _root_.is_rational _root_.euler_mascheroni := by
  rcases tailGapMaxCheckedUpperClosureOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
      upper_provider with
    ⟨_, _, _, _, _, _, hnot⟩
  exact hnot

/-- Exact calibration bridge between the explicit tail-gap big-`N` route and
the executable rejection-search witness route.  The remaining obligation for
identifying the two computed witnesses is precisely the pointwise witness
calibration `search.witness U hU N = max N threshold`. -/
theorem tailGapComputedN_eq_executableSearchWitnessOfTimeBound
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (tail_gap :
      ComputableGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (witness_calibration :
      ∀ U : Nat → Real, ∀ hU : _root_.is_polynomial_bound U, ∀ N : Nat,
        search.witness U hU N =
          max N (tail_gap.gap_for_polynomial_upper U hU).threshold)
    (upper_provider :
      ((strictScaleSingletonTailGapInputOfTimeBound
          lengthCodeAt time_bound_strict exponent_ne_zero tail_gap).toSearchInput)
        |>.toProofLengthFreeMonth12Candidate
        |>.checkedMeasuredUpperProviderType)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    let input :=
      strictScaleSingletonTailGapInputOfTimeBound
        lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
    let checkedTail :=
      checkedSearchUpperTail
        input.toSearchInput.toProofLengthFreeMonth12Candidate upper_provider hrat
    (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
      upper_provider).computedCollisionNOfRationality hrat =
      search.witness checkedTail.U checkedTail.polynomial checkedTail.upperN := by
  dsimp
  let input :=
    strictScaleSingletonTailGapInputOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap
  let checkedTail :=
    checkedSearchUpperTail
      input.toSearchInput.toProofLengthFreeMonth12Candidate upper_provider hrat
  have hclosure :=
    tailGapMaxCheckedUpperClosureOfTimeBound
      lengthCodeAt time_bound_strict exponent_ne_zero tail_gap upper_provider
  rcases hclosure with ⟨_, _, hcomputed, _, _, _, _⟩
  calc
    (input.toSearchInput.toProofLengthAxiomFreeCheckedUpperProvider
        upper_provider).computedCollisionNOfRationality hrat =
        max checkedTail.upperN
          (tail_gap.gap_for_polynomial_upper
            checkedTail.U checkedTail.polynomial).threshold :=
          hcomputed hrat
    _ = search.witness checkedTail.U checkedTail.polynomial checkedTail.upperN :=
          (witness_calibration checkedTail.U checkedTail.polynomial
            checkedTail.upperN).symm

/-- Build the strict-scale by-size singleton input from a concrete calibrated
rejection extractor.  This removes the independent `lengthCodeAt` gap field:
the gap is generated by the proof-length-free extractor, while the only root
proof-length residual remains the pointwise calibration equation. -/
def strictScaleSingletonBySizeInputOfCalibratedExtractor
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput scale_data where
  lengthCodeAt := lengthCodeAt
  scale_strict := scale_strict
  gap :=
    lengthCodeAtGapOfCalibratedExtractor lengthCodeAt
      (powerBoundRawCode_injective_of_scale_strict scale_strict)
      extractor
  proof_length_eq_lengthCodeAt := proof_length_eq_lengthCodeAt

theorem strictScaleSingletonBySizeInputOfCalibratedExtractor_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((strictScaleSingletonBySizeInputOfCalibratedExtractor
        lengthCodeAt scale_strict extractor proof_length_eq_lengthCodeAt).gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      extractor.witness U hU N :=
  rfl

/-- Build the strict-scale by-size singleton input from a concrete calibrated
extractor and checker proof-length exactness.  This removes the independent
by-size calibration argument: it is generated from the exactness certificate and
the proof-length-free calibrated minimum computation. -/
def strictScaleSingletonBySizeInputOfCalibratedExtractorExactnessNoFallback
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput scale_data :=
  strictScaleSingletonBySizeInputOfCalibratedExtractor
    lengthCodeAt scale_strict extractor
    (proofLength_eq_lengthCodeAt_of_calibratedCheckerProofLengthExactness_of_injective
      lengthCodeAt
      (powerBoundRawCode_injective_of_scale_strict scale_strict)
      exactness)

theorem strictScaleSingletonBySizeInputOfCalibratedExtractorExactnessNoFallback_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt))
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((strictScaleSingletonBySizeInputOfCalibratedExtractorExactnessNoFallback
        lengthCodeAt scale_strict extractor exactness).gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      extractor.witness U hU N :=
  rfl

/-- Backward-compatible adapter with an ignored fallback argument.  The
no-fallback core above is the actual residual boundary. -/
def strictScaleSingletonBySizeInputOfCalibratedExtractorExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (_fallback : _root_.FormulaCode → Nat)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput scale_data :=
  strictScaleSingletonBySizeInputOfCalibratedExtractorExactnessNoFallback
    lengthCodeAt scale_strict extractor exactness

theorem strictScaleSingletonBySizeInputOfCalibratedExtractorExactness_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (fallback : _root_.FormulaCode → Nat)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt))
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((strictScaleSingletonBySizeInputOfCalibratedExtractorExactness
        lengthCodeAt scale_strict extractor fallback exactness).gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      extractor.witness U hU N :=
  rfl

/-- Build the strict-scale by-size singleton input from the executable
PA/Hilbert calibrated rejection-search package.  This exposes the lower-bound
residual at the executable checker/search layer: the search procedure supplies
the witness, cutoff, and Boolean rejection sweep. -/
def strictScaleSingletonBySizeInputOfExecutableRejectionSearch
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput scale_data :=
  strictScaleSingletonBySizeInputOfCalibratedExtractor
    lengthCodeAt scale_strict search.toCheckerExtractor
    proof_length_eq_lengthCodeAt

theorem strictScaleSingletonBySizeInputOfExecutableRejectionSearch_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((strictScaleSingletonBySizeInputOfExecutableRejectionSearch
        lengthCodeAt scale_strict enumeration search
        proof_length_eq_lengthCodeAt).gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      search.witness U hU N :=
  rfl

/-- Build the strict-scale by-size singleton input from the executable
PA/Hilbert calibrated rejection-search package and checker proof-length
exactness.  The executable search supplies the proof-length-free gap; exactness
supplies the root calibration. -/
def strictScaleSingletonBySizeInputOfExecutableRejectionSearchExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (fallback : _root_.FormulaCode → Nat)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput scale_data :=
  strictScaleSingletonBySizeInputOfCalibratedExtractorExactness
    lengthCodeAt scale_strict search.toCheckerExtractor fallback exactness

theorem strictScaleSingletonBySizeInputOfExecutableRejectionSearchExactness_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (fallback : _root_.FormulaCode → Nat)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt))
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((strictScaleSingletonBySizeInputOfExecutableRejectionSearchExactness
        lengthCodeAt scale_strict enumeration search fallback exactness).gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      search.witness U hU N :=
  rfl

/-- Transport a computable search gap for the calibrated Nat-valued size
`lengthCodeAt` into the project-level root proof-length measurement.  The
computed witness is unchanged; only the measured function is rewritten through
the exact calibration equation. -/
def proofLengthGapOfLengthCodeAtGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (length_gap :
      ComputableSearchGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :
    ComputableSearchGapCertificate
      (fun n : Nat =>
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (scale_data.powerBoundRawCode n)) :=
  transportComputableSearchGap
    (fun n => (proof_length_eq_lengthCodeAt n).symm)
    length_gap

theorem proofLengthGapOfLengthCodeAtGap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (length_gap :
      ComputableSearchGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    ((proofLengthGapOfLengthCodeAtGap
        lengthCodeAt length_gap proof_length_eq_lengthCodeAt)
      |>.gap_for_polynomial_upper U hU).witness N =
      (length_gap.gap_for_polynomial_upper U hU).witness N :=
  rfl

/-- Build the final exact checker core from a proof-length-free calibrated-size
gap plus the single root proof-length calibration equation.  This removes the
need to supply an actual proof-length gap independently of the calibrated
checker lower-bound route. -/
def finalExactCheckerCoreInputOfLengthCodeAtGap
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (timeConstructiblePower_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a ^ scale_data.exponent <
          scale_data.time_constructible_bound b ^ scale_data.exponent)
    (length_gap :
      ComputableSearchGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real)) :
    ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data where
  lengthCodeAt := lengthCodeAt
  timeConstructiblePower_strict := timeConstructiblePower_strict
  proof_length_gap :=
    proofLengthGapOfLengthCodeAtGap
      lengthCodeAt length_gap proof_length_eq_lengthCodeAt
  proof_length_eq_lengthCodeAt := proof_length_eq_lengthCodeAt

theorem finalExactCheckerCoreInputOfLengthCodeAtGap_proofLengthGap_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (timeConstructiblePower_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a ^ scale_data.exponent <
          scale_data.time_constructible_bound b ^ scale_data.exponent)
    (length_gap :
      ComputableSearchGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((finalExactCheckerCoreInputOfLengthCodeAtGap
        lengthCodeAt timeConstructiblePower_strict
        length_gap proof_length_eq_lengthCodeAt).proof_length_gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      (length_gap.gap_for_polynomial_upper U hU).witness N :=
  rfl

/-- The strict-scale singleton calibrated route already contains enough
checker exactness to identify root proof length with the chosen calibrated
size.  The only project-level proof-length content is the supplied calibrated
proof-length exactness; injectivity turns the checker minimum into
`lengthCodeAt`. -/
theorem strictScaleSingletonGapCalibrated_proof_length_eq_lengthCodeAt
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data)
    (n : Nat) :
    _root_.proof_length _root_.ProofSystem.PA
        _root_.ProofLengthMeasure.symbolSize
        (scale_data.powerBoundRawCode n) =
      (input.lengthCodeAt n : Real) := by
  have hmin :
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data input.lengthCodeAt)
        n = input.lengthCodeAt n :=
    concretePAHilbertPowerBoundCalibrated_minProofCodeSizeAt_eq_lengthCodeAt_of_injective
      scale_data input.lengthCodeAt n input.powerBoundRawCode_injective
  simpa [hmin] using input.proof_length.proof_length_eq_minProofCodeSizeAt n

/-- The strict-scale singleton input already proves the powered
time-constructible strictness required by the final exact checker core.  This is
just `scale_strict` rewritten through the theorem-5 scale equation. -/
theorem strictScaleSingletonGapCalibrated_timeConstructiblePower_strict
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    ∀ {a b : Nat}, a < b →
      scale_data.time_constructible_bound a ^ scale_data.exponent <
        scale_data.time_constructible_bound b ^ scale_data.exponent := by
  intro a b hlt
  have hscale : scale_data.scale a < scale_data.scale b :=
    input.scale_strict hlt
  simpa [scale_data.scale_eq a, scale_data.scale_eq b] using hscale

/-- Reuse the existing strict-scale singleton calibrated checker route as a
final exact checker core.  Its calibrated-size gap supplies the lower side, and
the theorem above supplies the single root proof-length calibration equation. -/
def finalExactCheckerCoreInputOfStrictScaleSingletonGapCalibrated
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data)
    (timeConstructiblePower_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a ^ scale_data.exponent <
          scale_data.time_constructible_bound b ^ scale_data.exponent) :
    ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data :=
  finalExactCheckerCoreInputOfLengthCodeAtGap
    input.lengthCodeAt
    timeConstructiblePower_strict
    input.gap
    (strictScaleSingletonGapCalibrated_proof_length_eq_lengthCodeAt input)

theorem finalExactCheckerCoreInputOfStrictScaleSingletonGapCalibrated_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data)
    (timeConstructiblePower_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a ^ scale_data.exponent <
          scale_data.time_constructible_bound b ^ scale_data.exponent)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((finalExactCheckerCoreInputOfStrictScaleSingletonGapCalibrated
        input timeConstructiblePower_strict).proof_length_gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      (input.gap.gap_for_polynomial_upper U hU).witness N :=
  rfl

/-- Closed form of the previous adapter: the existing strict-scale singleton
input supplies both the calibrated-size lower gap and the powered strictness
needed by the final exact checker core. -/
def finalExactCheckerCoreInputOfStrictScaleSingletonGapCalibratedClosed
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data :=
  finalExactCheckerCoreInputOfStrictScaleSingletonGapCalibrated
    input
    (strictScaleSingletonGapCalibrated_timeConstructiblePower_strict input)

theorem finalExactCheckerCoreInputOfStrictScaleSingletonGapCalibratedClosed_witness_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data)
    (U : Nat → Real) (hU : _root_.is_polynomial_bound U) (N : Nat) :
    (((finalExactCheckerCoreInputOfStrictScaleSingletonGapCalibratedClosed
        input).proof_length_gap)
      |>.gap_for_polynomial_upper U hU).witness N =
      (input.gap.gap_for_polynomial_upper U hU).witness N :=
  rfl

/-- Recover the stricter by-size singleton package from the calibrated singleton
package.  The reverse direction already exists upstream as
`toStrictScaleSingletonGapCalibratedInput`; together they show that the two
residual formulations are equivalent at this strict-scale singleton layer. -/
def strictScaleSingletonGapCalibratedToBySizeInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data) :
    ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput scale_data where
  lengthCodeAt := input.lengthCodeAt
  scale_strict := input.scale_strict
  gap := input.gap
  proof_length_eq_lengthCodeAt :=
    strictScaleSingletonGapCalibrated_proof_length_eq_lengthCodeAt input

/-- Equivalence audit for the strict-scale singleton residual.  The route can be
stated either by a direct by-size equality
`proof_length(powerBoundRawCode n) = lengthCodeAt n` or by calibrated checker
proof-length exactness; under strict-scale injectivity these are interderivable. -/
theorem strictScaleSingleton_bySize_nonempty_iff_gapCalibrated_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData} :
    Nonempty
        (ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
          scale_data) ↔
      Nonempty
        (ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
          scale_data) := by
  constructor
  · intro h
    rcases h with ⟨input⟩
    exact ⟨input.toStrictScaleSingletonGapCalibratedInput⟩
  · intro h
    rcases h with ⟨input⟩
    exact ⟨strictScaleSingletonGapCalibratedToBySizeInput input⟩

/-! ## Final exact checker-core from constant projection -/

/-- Generate the additive project-box projection used by the corrected final
actual route from the narrower root proof-length constant projection.  This is
the compressed projection input: source exactness is already supplied by the
final exact checker core. -/
def finalExactCheckerCoreAdditiveProjectionOfConstant
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
    (constant_projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        input.toCanonicalCalibratedExactnessCore.scale_data.powerBoundRawCode
        _root_.sondowReflectionGraftCode) :
    InternalPudlakTheorem5AdditiveProjectBoxProjection
      input.toCanonicalCalibratedExactnessCore.scale_data
      input.toCanonicalCalibratedExactnessCore.checkerSemantics.toProofCodeSemantics :=
  input.toCanonicalCalibratedExactnessCore.toComputableFiniteSearchNoSmallCore
    |>.toAdditiveProjectBoxProjectionOfConstantProjection constant_projection

/-- Corrected final actual endpoint with the projection side stated through the
root proof-length constant projection rather than a prebuilt additive projection. -/
def finalExactEndpointOfConstantProjectionCLine
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (constant_projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        input.toCanonicalCalibratedExactnessCore.scale_data.powerBoundRawCode
        _root_.sondowReflectionGraftCode)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    Month9Month10ActualProofLengthDirectCollisionEndpoint
      input.toCanonicalCalibratedExactnessCore.scale_data :=
  correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength
    input
    (finalExactCheckerCoreAdditiveProjectionOfConstant
      input constant_projection)
    hkernel hchecker hlength

theorem finalExactEndpointOfConstantProjectionCLine_computed_n_eq
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (constant_projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        input.toCanonicalCalibratedExactnessCore.scale_data.powerBoundRawCode
        _root_.sondowReflectionGraftCode)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (finalExactEndpointOfConstantProjectionCLine input constant_projection
      hkernel hchecker hlength).computedCollisionNOfRationality hrat =
      (input.proof_length_gap.gap_for_polynomial_upper
        (finalExactCheckerCoreCorrectedUpperTail
          input
          (finalExactCheckerCoreAdditiveProjectionOfConstant
            input constant_projection)
          hkernel hchecker hlength hrat).U
        (finalExactCheckerCoreCorrectedUpperTail
          input
          (finalExactCheckerCoreAdditiveProjectionOfConstant
            input constant_projection)
          hkernel hchecker hlength hrat).polynomial).witness
        (finalExactCheckerCoreCorrectedUpperTail
          input
          (finalExactCheckerCoreAdditiveProjectionOfConstant
            input constant_projection)
          hkernel hchecker hlength hrat).upperN := by
  calc
    (finalExactEndpointOfConstantProjectionCLine input constant_projection
      hkernel hchecker hlength).computedCollisionNOfRationality hrat =
        input.toCanonicalCalibratedExactnessCore.rejectionExtractor.witness
          (finalExactCheckerCoreCorrectedUpperTail
            input
            (finalExactCheckerCoreAdditiveProjectionOfConstant
              input constant_projection)
            hkernel hchecker hlength hrat).U
          (finalExactCheckerCoreCorrectedUpperTail
            input
            (finalExactCheckerCoreAdditiveProjectionOfConstant
              input constant_projection)
            hkernel hchecker hlength hrat).polynomial
          (finalExactCheckerCoreCorrectedUpperTail
            input
            (finalExactCheckerCoreAdditiveProjectionOfConstant
              input constant_projection)
            hkernel hchecker hlength hrat).upperN := by
          simpa [finalExactEndpointOfConstantProjectionCLine,
            finalExactCheckerCoreCorrectedUpperTail] using
            (correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength_closure
              input
              (finalExactCheckerCoreAdditiveProjectionOfConstant
                input constant_projection)
              hkernel hchecker hlength).2.2.2.1 hrat
    _ =
        ((input.toStrictScaleSingletonExactProofLengthGapInput
          |>.transportedGap).gap_for_polynomial_upper
          (finalExactCheckerCoreCorrectedUpperTail
            input
            (finalExactCheckerCoreAdditiveProjectionOfConstant
              input constant_projection)
            hkernel hchecker hlength hrat).U
          (finalExactCheckerCoreCorrectedUpperTail
            input
            (finalExactCheckerCoreAdditiveProjectionOfConstant
              input constant_projection)
            hkernel hchecker hlength hrat).polynomial).witness
          (finalExactCheckerCoreCorrectedUpperTail
            input
            (finalExactCheckerCoreAdditiveProjectionOfConstant
              input constant_projection)
            hkernel hchecker hlength hrat).upperN := by
          rfl
    _ =
        (input.proof_length_gap.gap_for_polynomial_upper
          (finalExactCheckerCoreCorrectedUpperTail
            input
            (finalExactCheckerCoreAdditiveProjectionOfConstant
              input constant_projection)
            hkernel hchecker hlength hrat).U
          (finalExactCheckerCoreCorrectedUpperTail
            input
            (finalExactCheckerCoreAdditiveProjectionOfConstant
              input constant_projection)
            hkernel hchecker hlength hrat).polynomial).witness
          (finalExactCheckerCoreCorrectedUpperTail
            input
            (finalExactCheckerCoreAdditiveProjectionOfConstant
              input constant_projection)
            hkernel hchecker hlength hrat).upperN :=
          input.toStrictScaleSingletonExactProofLengthGapInput
            |>.transported_gap_witness_eq
              (finalExactCheckerCoreCorrectedUpperTail
                input
                (finalExactCheckerCoreAdditiveProjectionOfConstant
                  input constant_projection)
                hkernel hchecker hlength hrat).U
              (finalExactCheckerCoreCorrectedUpperTail
                input
                (finalExactCheckerCoreAdditiveProjectionOfConstant
                  input constant_projection)
                hkernel hchecker hlength hrat).polynomial
              (finalExactCheckerCoreCorrectedUpperTail
                input
                (finalExactCheckerCoreAdditiveProjectionOfConstant
                  input constant_projection)
                hkernel hchecker hlength hrat).upperN

theorem finalExactEndpointOfConstantProjectionCLine_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
    {bounds : BoundedArithmeticLab.SondowComponentBounds}
    (constant_projection :
      _root_.ConstantProofLengthProjection
        _root_.ProofSystem.PA _root_.ProofLengthMeasure.symbolSize
        input.toCanonicalCalibratedExactnessCore.scale_data.powerBoundRawCode
        _root_.sondowReflectionGraftCode)
    (hkernel :
      Nonempty SondowProjectLocalS21KernelCostAbsorptionCertificate)
    (hchecker :
      Nonempty
        (SondowReflectionGraftSidecarProofObjectCheckerExactCertificate
          bounds))
    (hlength :
      Nonempty SondowReflectionGraftSidecarSemanticLengthRecognitionSplitCertificate) :
    (finalExactEndpointOfConstantProjectionCLine
      input constant_projection hkernel hchecker hlength).Audit ∧
      Nonempty
        (ComputableSearchGapCertificate
          (actualProofLengthMeasured
            input.toCanonicalCalibratedExactnessCore.scale_data)) ∧
        (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
          (finalExactEndpointOfConstantProjectionCLine
            input constant_projection hkernel hchecker
            hlength).computedCollisionNOfRationality hrat =
            (input.proof_length_gap.gap_for_polynomial_upper
              (finalExactCheckerCoreCorrectedUpperTail
                input
                (finalExactCheckerCoreAdditiveProjectionOfConstant
                  input constant_projection)
                hkernel hchecker hlength hrat).U
              (finalExactCheckerCoreCorrectedUpperTail
                input
                (finalExactCheckerCoreAdditiveProjectionOfConstant
                  input constant_projection)
                hkernel hchecker hlength hrat).polynomial).witness
              (finalExactCheckerCoreCorrectedUpperTail
                input
                (finalExactCheckerCoreAdditiveProjectionOfConstant
                  input constant_projection)
                hkernel hchecker hlength hrat).upperN) ∧
          (∀ _hrat : _root_.is_rational _root_.euler_mascheroni,
            False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  have hclosure :=
    correctedActualEndpointOfFinalExactCheckerCoreInputCLineKernelCheckerLength_closure
      input
      (finalExactCheckerCoreAdditiveProjectionOfConstant
        input constant_projection)
      hkernel hchecker hlength
  exact
    ⟨by
      simpa [finalExactEndpointOfConstantProjectionCLine] using hclosure.1,
      hclosure.2.2.1,
      finalExactEndpointOfConstantProjectionCLine_computed_n_eq
        input constant_projection hkernel hchecker hlength,
      hclosure.2.2.2.2.1,
      hclosure.2.2.2.2.2⟩

/-! ## Final scale-size closure into the scaled project endpoint -/

/-- Feed the materialized final scale-size exact proof-gap closure into the
Month 9-10 scaled checker-extractor endpoint.  This is the route aligned with the
existing scale-projection pieces `powerBoundRawCode n -> graft (scale n)`. -/
def finalScaleSizeExactProofGapClosureToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (closure :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure
        scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} where
  scale_data := scale_data
  checker := closure.checkerSemantics
  enumeration := closure.finiteEnumeration
  extractor := closure.rejectionExtractor
  family_exactness :=
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness.ofCheckerProofLengthExactness
      closure.proofLengthExactness
  strengthened_to_partial_projection := strengthened_to_partial
  partial_to_graft_projection := partial_to_graft
  computable_gap := computable_gap
  project_upper := project_upper

/-- Closure of the scaled endpoint generated from the final scale-size exact
proof-gap closure.  The remaining external data are the two constant projection
certificates, the project upper route, and the project-box computable gap. -/
theorem finalScaleSizeExactProofGapClosure_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (closure :
      ConcretePAHilbertPowerBoundFinalScaleSizeExactProofGapClosure
        scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalScaleSizeExactProofGapClosureToFamilyEndpointInputs
        closure strengthened_to_partial partial_to_graft computable_gap
        project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalScaleSizeExactProofGapClosureToFamilyEndpointInputs
      closure strengthened_to_partial partial_to_graft computable_gap
      project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Feed an arbitrary final exact checker core into the Month 9-10 scaled
checker-extractor endpoint.  Unlike the scale-size bridge above, this keeps the
calibrated `lengthCodeAt` from the final core instead of forcing the old
`proof_length = scale` specialization. -/
noncomputable def finalExactCheckerCoreToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input : ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} where
  scale_data := input.toCanonicalCalibratedExactnessCore.scale_data
  checker := input.toCanonicalCalibratedExactnessCore.checkerSemantics
  enumeration := input.toCanonicalCalibratedExactnessCore.finiteEnumeration
  extractor := input.toCanonicalCalibratedExactnessCore.rejectionExtractor
  family_exactness :=
    InternalPudlakTheorem5CheckerProofLengthFamilyExactness.ofCheckerProofLengthExactness
      input.toCanonicalCalibratedExactnessCore.proofLengthExactness
  strengthened_to_partial_projection := strengthened_to_partial
  partial_to_graft_projection := partial_to_graft
  computable_gap := computable_gap
  project_upper := project_upper

/-- Closure of the scaled project endpoint from an arbitrary final exact checker
core.  This records that the Month 9-10 endpoint machinery can be reused once the
final core itself is constructed, without the obsolete exact-scale side condition. -/
theorem finalExactCheckerCore_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input : ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalExactCheckerCoreToFamilyEndpointInputs input strengthened_to_partial
        partial_to_graft computable_gap project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalExactCheckerCoreToFamilyEndpointInputs input strengthened_to_partial
      partial_to_graft computable_gap project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Direct endpoint input from a calibrated-size lower gap.  This is the
non-exact-scale route: the lower-bound side may stay on `lengthCodeAt`, and the
only root proof-length obligation is the pointwise calibration equation used to
transport that gap into the final checker core. -/
noncomputable def finalLengthCodeAtGapToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (timeConstructiblePower_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a ^ scale_data.exponent <
          scale_data.time_constructible_bound b ^ scale_data.exponent)
    (length_gap :
      ComputableSearchGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalExactCheckerCoreToFamilyEndpointInputs
    (finalExactCheckerCoreInputOfLengthCodeAtGap
      lengthCodeAt timeConstructiblePower_strict
      length_gap proof_length_eq_lengthCodeAt)
    strengthened_to_partial partial_to_graft computable_gap project_upper

/-- Closure of the scaled project endpoint from a calibrated-size lower gap.
This is the current compressed route for the final checker core: lower search
gap on `lengthCodeAt`, one proof-length calibration equation, then the existing
Month 9-10 endpoint machinery. -/
theorem finalLengthCodeAtGap_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (timeConstructiblePower_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a ^ scale_data.exponent <
          scale_data.time_constructible_bound b ^ scale_data.exponent)
    (length_gap :
      ComputableSearchGapCertificate
        (fun n : Nat => (lengthCodeAt n : Real)))
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalLengthCodeAtGapToFamilyEndpointInputs lengthCodeAt
        timeConstructiblePower_strict length_gap proof_length_eq_lengthCodeAt
        strengthened_to_partial partial_to_graft computable_gap project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalLengthCodeAtGapToFamilyEndpointInputs lengthCodeAt
      timeConstructiblePower_strict length_gap proof_length_eq_lengthCodeAt
      strengthened_to_partial partial_to_graft computable_gap project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Endpoint input obtained directly from the existing strict-scale singleton
calibrated checker package.  This reuses the Month 11-12 singleton route: its
calibrated-size gap is transported through the proof-length exactness already
stored in the package. -/
noncomputable def finalStrictScaleSingletonGapCalibratedToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data)
    (timeConstructiblePower_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a ^ scale_data.exponent <
          scale_data.time_constructible_bound b ^ scale_data.exponent)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalExactCheckerCoreToFamilyEndpointInputs
    (finalExactCheckerCoreInputOfStrictScaleSingletonGapCalibrated
      input timeConstructiblePower_strict)
    strengthened_to_partial partial_to_graft computable_gap project_upper

/-- Closure of the scaled project endpoint from the existing strict-scale
singleton calibrated checker package.  The remaining proof work is now exposed
where it belongs: construct that package, the time-power strictness, and the
project-side certificates unconditionally. -/
theorem finalStrictScaleSingletonGapCalibrated_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data)
    (timeConstructiblePower_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a ^ scale_data.exponent <
          scale_data.time_constructible_bound b ^ scale_data.exponent)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalStrictScaleSingletonGapCalibratedToFamilyEndpointInputs input
        timeConstructiblePower_strict strengthened_to_partial partial_to_graft
        computable_gap project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalStrictScaleSingletonGapCalibratedToFamilyEndpointInputs input
      timeConstructiblePower_strict strengthened_to_partial partial_to_graft
      computable_gap project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Closed endpoint input from the existing strict-scale singleton calibrated
checker package.  The package supplies the lower gap, proof-length calibration,
and powered strictness, so no separate `timeConstructiblePower_strict` argument
is exposed. -/
noncomputable def finalStrictScaleSingletonGapCalibratedClosedToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalExactCheckerCoreToFamilyEndpointInputs
    (finalExactCheckerCoreInputOfStrictScaleSingletonGapCalibratedClosed input)
    strengthened_to_partial partial_to_graft computable_gap project_upper

/-- Closed scaled endpoint from the existing strict-scale singleton calibrated
checker package.  This is the tightest current endpoint bridge from the
Month 11-12 singleton route to the Month 9-10 scaled machinery. -/
theorem finalStrictScaleSingletonGapCalibratedClosed_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonGapCalibratedInput
        scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalStrictScaleSingletonGapCalibratedClosedToFamilyEndpointInputs input
        strengthened_to_partial partial_to_graft computable_gap project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalStrictScaleSingletonGapCalibratedClosedToFamilyEndpointInputs input
      strengthened_to_partial partial_to_graft computable_gap project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Closed endpoint input from the stricter by-size singleton package.  This is
one layer closer to the remaining hard proof: the lower side is a
`lengthCodeAt` search gap and the root proof-length contribution is exactly the
pointwise equation `proof_length = lengthCodeAt`. -/
noncomputable def finalStrictScaleSingletonBySizeToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
        scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalStrictScaleSingletonGapCalibratedClosedToFamilyEndpointInputs
    input.toStrictScaleSingletonGapCalibratedInput
    strengthened_to_partial partial_to_graft computable_gap project_upper

/-- Closed scaled endpoint from the by-size singleton package.  Compared with
the final exact checker-core route, this exposes the true residual directly:
construct a calibrated-size computable lower gap and prove
`proof_length(powerBoundRawCode n) = lengthCodeAt n`. -/
theorem finalStrictScaleSingletonBySize_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundStrictScaleSingletonBySizeInput
        scale_data)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalStrictScaleSingletonBySizeToFamilyEndpointInputs input
        strengthened_to_partial partial_to_graft computable_gap project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalStrictScaleSingletonBySizeToFamilyEndpointInputs input
      strengthened_to_partial partial_to_graft computable_gap project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Direct endpoint input from a concrete calibrated rejection extractor.  The
proof-length-free extractor supplies the calibrated-size lower gap; the only
root proof-length residual left at this boundary is
`proof_length(powerBoundRawCode n) = lengthCodeAt n`. -/
noncomputable def finalCalibratedExtractorToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalStrictScaleSingletonBySizeToFamilyEndpointInputs
    (strictScaleSingletonBySizeInputOfCalibratedExtractor
      lengthCodeAt scale_strict extractor proof_length_eq_lengthCodeAt)
    strengthened_to_partial partial_to_graft computable_gap project_upper

/-- Closed scaled endpoint from a concrete calibrated rejection extractor.  This
is the current sharp lower-bound handoff: construct the extractor, prove scale
strictness and the root proof-length calibration, and the existing Month 9-10
endpoint machinery closes. -/
theorem finalCalibratedExtractor_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalCalibratedExtractorToFamilyEndpointInputs
        lengthCodeAt scale_strict extractor proof_length_eq_lengthCodeAt
        strengthened_to_partial partial_to_graft computable_gap project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalCalibratedExtractorToFamilyEndpointInputs
      lengthCodeAt scale_strict extractor proof_length_eq_lengthCodeAt
      strengthened_to_partial partial_to_graft computable_gap project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Direct endpoint input from the executable PA/Hilbert calibrated rejection
search package.  This is one step more concrete than the extractor boundary:
the executable search object supplies the rejection extractor used downstream. -/
noncomputable def finalExecutableRejectionSearchToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalCalibratedExtractorToFamilyEndpointInputs
    lengthCodeAt scale_strict search.toCheckerExtractor
    proof_length_eq_lengthCodeAt strengthened_to_partial partial_to_graft
    computable_gap project_upper

/-- Closed scaled endpoint from the executable calibrated rejection search.
The remaining theorem-5 lower-bound construction is now stated at executable
checker/search level plus the root proof-length calibration equation. -/
theorem finalExecutableRejectionSearch_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (proof_length_eq_lengthCodeAt :
      ∀ n : Nat,
        _root_.proof_length _root_.ProofSystem.PA
            _root_.ProofLengthMeasure.symbolSize
            (scale_data.powerBoundRawCode n) =
          (lengthCodeAt n : Real))
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalExecutableRejectionSearchToFamilyEndpointInputs
        lengthCodeAt scale_strict enumeration search
        proof_length_eq_lengthCodeAt strengthened_to_partial partial_to_graft
        computable_gap project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalExecutableRejectionSearchToFamilyEndpointInputs
      lengthCodeAt scale_strict enumeration search
      proof_length_eq_lengthCodeAt strengthened_to_partial partial_to_graft
      computable_gap project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Direct endpoint input from a concrete calibrated rejection extractor plus
checker proof-length exactness.  Compared with
`finalCalibratedExtractorToFamilyEndpointInputs`, this boundary no longer asks
for a separate by-size root calibration equation. -/
noncomputable def finalCalibratedExtractorExactnessToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (fallback : _root_.FormulaCode → Nat)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt))
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalCalibratedExtractorToFamilyEndpointInputs
    lengthCodeAt scale_strict extractor
    (proofLength_eq_lengthCodeAt_of_calibratedCheckerProofLengthExactness
      lengthCodeAt fallback
      (powerBoundRawCode_injective_of_scale_strict scale_strict)
      exactness)
    strengthened_to_partial partial_to_graft computable_gap project_upper

/-- Closed scaled endpoint from a concrete calibrated rejection extractor plus
checker proof-length exactness.  The remaining lower-bound work is now exposed
as the extractor construction, scale strictness, checker exactness, and the
project-side Sondow/Pudlak certificates. -/
theorem finalCalibratedExtractorExactness_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    {enumeration :
      InternalPudlakTheorem5CheckerFiniteEnumeration
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)}
    (extractor :
      InternalPudlakTheorem5CheckerComputableRejectionExtractor
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt)
        enumeration)
    (fallback : _root_.FormulaCode → Nat)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt))
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalCalibratedExtractorExactnessToFamilyEndpointInputs
        lengthCodeAt scale_strict extractor fallback exactness
        strengthened_to_partial partial_to_graft computable_gap project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalCalibratedExtractorExactnessToFamilyEndpointInputs
      lengthCodeAt scale_strict extractor fallback exactness
      strengthened_to_partial partial_to_graft computable_gap project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Direct endpoint input from executable PA/Hilbert calibrated rejection search
plus checker proof-length exactness.  This is the most concrete current
boundary: executable rejection search supplies the lower witness, and checker
exactness supplies the root calibration. -/
noncomputable def finalExecutableRejectionSearchExactnessToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (fallback : _root_.FormulaCode → Nat)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt))
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalExecutableRejectionSearchToFamilyEndpointInputs
    lengthCodeAt scale_strict enumeration search
    (proofLength_eq_lengthCodeAt_of_calibratedCheckerProofLengthExactness
      lengthCodeAt fallback
      (powerBoundRawCode_injective_of_scale_strict scale_strict)
      exactness)
    strengthened_to_partial partial_to_graft computable_gap project_upper

/-- Closed scaled endpoint from executable calibrated rejection search plus
checker proof-length exactness.  This removes the independent
`proof_length_eq_lengthCodeAt` argument from the executable endpoint boundary. -/
theorem finalExecutableRejectionSearchExactness_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (lengthCodeAt : Nat → Nat)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (enumeration :
      ConcretePAHilbertPowerBoundCalibratedFiniteEnumerationInput
        scale_data lengthCodeAt)
    (search :
      ConcretePAHilbertPowerBoundCalibratedExecutableRejectionSearchInput
        scale_data lengthCodeAt enumeration)
    (fallback : _root_.FormulaCode → Nat)
    (exactness :
      InternalPudlakTheorem5CheckerProofLengthExactness
        (concretePAHilbertPowerBoundCalibratedCheckerSemantics
          scale_data lengthCodeAt))
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalExecutableRejectionSearchExactnessToFamilyEndpointInputs
        lengthCodeAt scale_strict enumeration search fallback exactness
        strengthened_to_partial partial_to_graft computable_gap project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalExecutableRejectionSearchExactnessToFamilyEndpointInputs
      lengthCodeAt scale_strict enumeration search fallback exactness
      strengthened_to_partial partial_to_graft computable_gap project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Direct endpoint input from the concrete calibrated four-piece package.
The package already contains the calibrated finite enumeration, executable
rejection search, and proof-length exactness certificate; the remaining
endpoint-side arguments are scale strictness and the project Sondow/Pudlak
certificates. -/
noncomputable def finalCalibratedFourPieceToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input : ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (fallback : _root_.FormulaCode → Nat)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalExecutableRejectionSearchExactnessToFamilyEndpointInputs
    input.lengthCodeAt scale_strict input.enumeration input.rejection_search
    fallback input.proofLengthExactness strengthened_to_partial
    partial_to_graft computable_gap project_upper

/-- Closed scaled endpoint from the concrete calibrated four-piece package.
This is the current concrete boundary for the theorem-5 lower-search side:
construct the four-piece package and scale strictness, then the existing
Sondow/project certificates close the endpoint. -/
theorem finalCalibratedFourPiece_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input : ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data)
    (scale_strict :
      ∀ {a b : Nat}, a < b → scale_data.scale a < scale_data.scale b)
    (fallback : _root_.FormulaCode → Nat)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalCalibratedFourPieceToFamilyEndpointInputs input scale_strict
        fallback strengthened_to_partial partial_to_graft computable_gap
        project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalCalibratedFourPieceToFamilyEndpointInputs input scale_strict
      fallback strengthened_to_partial partial_to_graft computable_gap
      project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Direct endpoint input from the calibrated four-piece package using the
primitive time-bound strictness field.  This derives `scale_strict` from
`scale n = time_constructible_bound n ^ exponent`, so the endpoint boundary
matches the original scale-data shape more closely. -/
noncomputable def finalCalibratedFourPieceTimeStrictToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input : ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (fallback : _root_.FormulaCode → Nat)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalCalibratedFourPieceToFamilyEndpointInputs input
    (your_scale_strict_theorem time_bound_strict exponent_ne_zero)
    fallback strengthened_to_partial partial_to_graft computable_gap
    project_upper

/-- Closed scaled endpoint from the calibrated four-piece package using the
primitive time-bound strictness field instead of an already-derived
`scale_strict` hypothesis. -/
theorem finalCalibratedFourPieceTimeStrict_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input : ConcretePAHilbertPowerBoundCalibratedFourPieceInput scale_data)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (fallback : _root_.FormulaCode → Nat)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalCalibratedFourPieceTimeStrictToFamilyEndpointInputs input
        time_bound_strict exponent_ne_zero fallback strengthened_to_partial
        partial_to_graft computable_gap project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalCalibratedFourPieceTimeStrictToFamilyEndpointInputs input
      time_bound_strict exponent_ne_zero fallback strengthened_to_partial
      partial_to_graft computable_gap project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Endpoint input from the dominating-length calibrated four-piece package.
Here the finite enumeration code bound is already reduced to the size cutoff:
small calibrated size implies the numeric code lies in `List.range cutoff`. -/
noncomputable def finalDominatingCalibratedFourPieceTimeStrictToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput
        scale_data)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (fallback : _root_.FormulaCode → Nat)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalCalibratedFourPieceTimeStrictToFamilyEndpointInputs
    input.toCalibratedFourPieceInput time_bound_strict exponent_ne_zero
    fallback strengthened_to_partial partial_to_graft computable_gap
    project_upper

/-- Closed scaled endpoint from the dominating-length calibrated four-piece
package.  This removes the arbitrary calibrated code-bound residual from the
endpoint boundary. -/
theorem finalDominatingCalibratedFourPieceTimeStrict_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundDominatingCalibratedFourPieceInput
        scale_data)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (fallback : _root_.FormulaCode → Nat)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalDominatingCalibratedFourPieceTimeStrictToFamilyEndpointInputs
        input time_bound_strict exponent_ne_zero fallback
        strengthened_to_partial partial_to_graft computable_gap project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalDominatingCalibratedFourPieceTimeStrictToFamilyEndpointInputs
      input time_bound_strict exponent_ne_zero fallback
      strengthened_to_partial partial_to_graft computable_gap project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Endpoint input from the identity-size scale-no-collision calibrated package.
This is the sharpest current concrete boundary on the lower-search side: proof
codes are measured by identity size, and the finite Boolean rejection sweep is
generated from scale no-collision below the cutoff. -/
noncomputable def finalIdentityScaleNoCollisionTimeStrictToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput
        scale_data)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (fallback : _root_.FormulaCode → Nat)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalCalibratedFourPieceTimeStrictToFamilyEndpointInputs
    input.toCalibratedFourPieceInput time_bound_strict exponent_ne_zero
    fallback strengthened_to_partial partial_to_graft computable_gap
    project_upper

/-- Closed scaled endpoint from the identity-size scale-no-collision package.
The remaining lower-side construction is now concentrated in scale
no-collision below the searched cutoff and proof-length exactness for identity
calibrated size. -/
theorem finalIdentityScaleNoCollisionTimeStrict_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundIdentityScaleNoCollisionCalibratedFourPieceInput
        scale_data)
    (time_bound_strict :
      ∀ {a b : Nat}, a < b →
        scale_data.time_constructible_bound a <
          scale_data.time_constructible_bound b)
    (exponent_ne_zero : scale_data.exponent ≠ 0)
    (fallback : _root_.FormulaCode → Nat)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalIdentityScaleNoCollisionTimeStrictToFamilyEndpointInputs
        input time_bound_strict exponent_ne_zero fallback
        strengthened_to_partial partial_to_graft computable_gap project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalIdentityScaleNoCollisionTimeStrictToFamilyEndpointInputs
      input time_bound_strict exponent_ne_zero fallback
      strengthened_to_partial partial_to_graft computable_gap project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Endpoint input from the final strict-scale by-index residual.  This pushes
the identity-size no-collision boundary one step lower: scale no-collision below
the cutoff is generated from strict scale, scale injectivity, and
`cutoff ≤ witness`. -/
noncomputable def finalStrictScaleByIndexResidualToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
        scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalCalibratedFourPieceToFamilyEndpointInputs
    input.toFinalResidualInput.toCalibratedFourPieceInput input.scale_strict
    fallback strengthened_to_partial partial_to_graft computable_gap
    project_upper

/-- Closed scaled endpoint from the final strict-scale by-index residual.  The
remaining lower-side fields are now witness/cutoff, `cutoff ≤ witness`, strict
scale, and by-index proof-length exactness. -/
theorem finalStrictScaleByIndexResidual_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
        scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalStrictScaleByIndexResidualToFamilyEndpointInputs input fallback
        strengthened_to_partial partial_to_graft computable_gap project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalStrictScaleByIndexResidualToFamilyEndpointInputs input fallback
      strengthened_to_partial partial_to_graft computable_gap project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Endpoint input from the bounded strict-scale by-index residual.  Here the
same computable bound supplies both witness and cutoff, so `cutoff ≤ witness`
is no longer an exposed field. -/
noncomputable def finalBoundedStrictScaleByIndexResidualToFamilyEndpointInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
        scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    Month9Month10CheckerExtractorFamilyEndpointInputs.{0} :=
  finalStrictScaleByIndexResidualToFamilyEndpointInputs
    input.toFinalStrictScaleByIndexResidualInput fallback
    strengthened_to_partial partial_to_graft computable_gap project_upper

/-- Closed scaled endpoint from the bounded strict-scale by-index residual.
This is the most compact current residual boundary: provide one computable
bound dominating the polynomial upper, strict scale, and by-index proof-length
exactness.  The negative audit below shows this boundary is over-strong as a
positive route to the final theorem. -/
theorem finalBoundedStrictScaleByIndexResidual_scaledEndpoint_closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
        scale_data)
    (fallback : _root_.FormulaCode → Nat)
    (strengthened_to_partial :
      _root_.StrengthenedToPartialConsistencyConstantProjection)
    (partial_to_graft : _root_.PAConjunctionEliminationConstantCost)
    (computable_gap :
      ComputableGapCertificate sondowProjectLocalPudlakCollisionBox)
    (project_upper : SondowProjectLocalS21CollapseConclusion) :
    let endpoint :=
      finalBoundedStrictScaleByIndexResidualToFamilyEndpointInputs
        input fallback strengthened_to_partial partial_to_graft computable_gap
        project_upper
    Nonempty Month9Month10CheckerExtractorFamilyEndpointInputs.{0} ∧
      endpoint.toProjectEndpointInputs.EndpointFrontier ∧
        (∀ _ : _root_.is_rational _root_.euler_mascheroni,
          False) ∧
          ¬ _root_.is_rational _root_.euler_mascheroni := by
  dsimp
  let endpoint :=
    finalBoundedStrictScaleByIndexResidualToFamilyEndpointInputs
      input fallback strengthened_to_partial partial_to_graft computable_gap
      project_upper
  exact
    ⟨⟨endpoint⟩,
      endpoint.endpoint_frontier,
      (fun hrat => endpoint.endpoint_contradiction hrat),
      endpoint.not_rational⟩

/-- Negative audit: the final identity-size residual cannot satisfy every
polynomial upper.  Taking `U n = n + 1`, `cutoff_gt` gives `witness < cutoff`;
then `scaleNoCollisionBelow` can be applied to the witness itself and produces
`scale w ≠ scale w`. -/
theorem noFinalResidualInput_of_selfPlusOneUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input : ConcretePAHilbertPowerBoundFinalResidualInput scale_data) :
    False := by
  let U : Nat → Real := fun n => (n : Real) + 1
  have hU : _root_.is_polynomial_bound U := by
    refine ⟨1, 1, ?_⟩
    intro n
    simp [U]
  let w := input.witness U hU 0
  let K := input.cutoff U hU 0
  have hcut : U w < (K : Real) :=
    input.cutoff_gt U hU 0
  have hw_lt_K_real : (w : Real) < (K : Real) := by
    dsimp [U] at hcut
    nlinarith
  have hw_lt_K : w < K := by
    exact_mod_cast hw_lt_K_real
  have hne : scale_data.scale w ≠ scale_data.scale w :=
    input.scaleNoCollisionBelow U hU 0 w hw_lt_K
  exact hne rfl

/-- Negative audit for the strict-scale by-index residual: its projection to
the final identity-size residual is already contradictory. -/
theorem noFinalStrictScaleByIndexResidualInput_of_selfPlusOneUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalStrictScaleByIndexResidualInput
        scale_data) :
    False :=
  noFinalResidualInput_of_selfPlusOneUpper input.toFinalResidualInput

/-- Negative audit for the bounded strict-scale by-index residual. -/
theorem noFinalBoundedStrictScaleByIndexResidualInput_of_selfPlusOneUpper
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      ConcretePAHilbertPowerBoundFinalBoundedStrictScaleByIndexResidualInput
        scale_data) :
    False :=
  noFinalResidualInput_of_selfPlusOneUpper input.toFinalResidualInput

/-! ## Final exact checker-core accepted-code exactness -/

/-- Local hard-residual copy of the ordinary-code exclusion for the concrete
theorem-5 semantics.  It is kept here so downstream residual probes do not
depend on refreshed imported `.olean` artifacts from the checker-surface file. -/
theorem concreteTheorem5_partialConsistencyCode_not_formulaCodeDerivable_local
    (n : Nat) :
    ¬ SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
        SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
        (_root_.partialConsistencyCode n) := by
  intro hderivable
  rcases hderivable with ⟨formula, hcode, hformula_derivable⟩
  have hformula_eq :
      formula =
        SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormula.ofFormulaCode
          (_root_.partialConsistencyCode n) :=
    SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormula.eq_of_code_eq
      (by
        simpa
          [SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormula.ofFormulaCode]
          using hcode)
  rw [hformula_eq] at hformula_derivable
  rcases hformula_derivable with htag | htarget
  · rcases htag with htag0 | htag1 | htag2 | htag3
    · simp
        [SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertIsTaggedAxiom,
          SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertFormulaTag,
          SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormula.ofFormulaCode,
          _root_.partialConsistencyCode] at htag0
    · simp
        [SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertIsTaggedAxiom,
          SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertFormulaTag,
          SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormula.ofFormulaCode,
          _root_.partialConsistencyCode] at htag1
    · simp
        [SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertIsTaggedAxiom,
          SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertFormulaTag,
          SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormula.ofFormulaCode,
          _root_.partialConsistencyCode] at htag2
    · simp
        [SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertIsTaggedAxiom,
          SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertFormulaTag,
          SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormula.ofFormulaCode,
          _root_.partialConsistencyCode] at htag3
  · unfold SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertIsStrengthenedPartialConsistency at htarget
    simp
      [SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormula.ofFormulaCode,
        _root_.partialConsistencyCode] at htarget

/-- Clean incompatibility theorem for the ordinary payload-code branch.  A
concrete theorem-5 accepted-code exactness principle plus an ordinary
finite-consistency accepted-code family would imply ordinary finite-consistency
derivability, contradicting the concrete theorem-5 semantics. -/
theorem concreteTheorem5_noOrdinaryPayloadCodeAcceptance
    {scale_data : InternalPudlakTheorem5ScaleData}
    (ordinary_acceptance :
      Month9Month10PayloadFreeCheckerAcceptedFamily
        (SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertPowerBoundChecker
          scale_data)
        _root_.partialConsistencyCode)
    (acceptedCodeExactness :
      ∀ formulaCode : _root_.FormulaCode, ∀ code : Nat,
        SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertAcceptedProofCodeForFormulaCode
          (SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertPowerBoundChecker
            scale_data)
          formulaCode code →
        SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
          SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
          formulaCode) :
    False :=
  concreteTheorem5_partialConsistencyCode_not_formulaCodeDerivable_local 0
    (acceptedCodeExactness
      (_root_.partialConsistencyCode 0)
      (ordinary_acceptance.proofCode 0)
      (ordinary_acceptance.acceptedCode 0))

/-- Payload-free accepted-code exactness input for the final exact checker
core.  It only aligns the payload-free checker-acceptance object with the
concrete PA/Hilbert checker generated by the final exact core. -/
structure FinalExactCheckerCoreAcceptedCodeExactnessInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data)
    (checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance) :
    Prop where
  checker_eq :
    checker_acceptance.checker =
      SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertPowerBoundChecker
        scale_data

namespace FinalExactCheckerCoreAcceptedCodeExactnessInput

theorem acceptedCodeExactness
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (h :
      FinalExactCheckerCoreAcceptedCodeExactnessInput
        input checker_acceptance)
    (formulaCode : _root_.FormulaCode) (code : Nat)
    (haccepted :
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertAcceptedProofCodeForFormulaCode
        checker_acceptance.checker formulaCode code) :
    SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
      SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
      formulaCode := by
  have haccepted_concrete :
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertAcceptedProofCodeForFormulaCode
        (SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertPowerBoundChecker
          scale_data)
        formulaCode code := by
    simpa [h.checker_eq] using haccepted
  exact
    input.toCertificate.accepted_code_to_formulaCode_derivable
      formulaCode code haccepted_concrete

theorem ordinaryDerivable
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (h :
      FinalExactCheckerCoreAcceptedCodeExactnessInput
        input checker_acceptance)
    (n : Nat) :
    SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
      SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
      (_root_.partialConsistencyCode n) :=
  h.acceptedCodeExactness
    (_root_.partialConsistencyCode n)
    (checker_acceptance.ordinary.proofCode n)
    (checker_acceptance.ordinary.acceptedCode n)

theorem strengthenedDerivable
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (h :
      FinalExactCheckerCoreAcceptedCodeExactnessInput
        input checker_acceptance)
    (n : Nat) :
    SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
      SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
      (_root_.strengthenedPartialConsistencyCode n) :=
  h.acceptedCodeExactness
    (_root_.strengthenedPartialConsistencyCode n)
    (checker_acceptance.strengthened.proofCode n)
    (checker_acceptance.strengthened.acceptedCode n)

structure Audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (h :
      FinalExactCheckerCoreAcceptedCodeExactnessInput
        input checker_acceptance) :
    Prop where
  checkerAcceptanceClean :
    checker_acceptance.Audit
  checkerEq :
    checker_acceptance.checker =
      SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertPowerBoundChecker
        scale_data
  acceptedCodeExactness :
    ∀ formulaCode : _root_.FormulaCode, ∀ code : Nat,
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertAcceptedProofCodeForFormulaCode
        checker_acceptance.checker formulaCode code →
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
        SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
        formulaCode
  ordinaryDerivable :
    ∀ n : Nat,
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
        SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
        (_root_.partialConsistencyCode n)
  strengthenedDerivable :
    ∀ n : Nat,
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
        SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
        (_root_.strengthenedPartialConsistencyCode n)

theorem audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (h :
      FinalExactCheckerCoreAcceptedCodeExactnessInput
        input checker_acceptance) :
    h.Audit where
  checkerAcceptanceClean :=
    checker_acceptance.audit
  checkerEq :=
    h.checker_eq
  acceptedCodeExactness :=
    h.acceptedCodeExactness
  ordinaryDerivable :=
    h.ordinaryDerivable
  strengthenedDerivable :=
    h.strengthenedDerivable

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (h :
      FinalExactCheckerCoreAcceptedCodeExactnessInput
        input checker_acceptance) :
    h.Audit ∧
      (∀ formulaCode : _root_.FormulaCode, ∀ code : Nat,
        SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertAcceptedProofCodeForFormulaCode
          checker_acceptance.checker formulaCode code →
        SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
          SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
          formulaCode) ∧
        (∀ n : Nat,
          SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
            SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
            (_root_.partialConsistencyCode n)) ∧
          (∀ n : Nat,
            SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
              SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
              (_root_.strengthenedPartialConsistencyCode n)) :=
  ⟨h.audit,
    h.acceptedCodeExactness,
    h.ordinaryDerivable,
    h.strengthenedDerivable⟩

/-- The two-family payload-free checker-acceptance input is incompatible with
the concrete theorem-5 derivability semantics.  The strengthened branch is the
actual theorem-5 target; the ordinary finite-consistency branch would force
ordinary partial-consistency code derivability, which the concrete theorem-5
semantics has already excluded. -/
theorem ordinaryBranchContradiction
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (h :
      FinalExactCheckerCoreAcceptedCodeExactnessInput
        input checker_acceptance) :
    False :=
  concreteTheorem5_partialConsistencyCode_not_formulaCodeDerivable_local 0
    (h.ordinaryDerivable 0)

/-- Nonempty form of `ordinaryBranchContradiction`.  This is the formal audit
warning for the final route: a theorem-5 checker can carry strengthened
payload-code evidence, but a full ordinary-plus-strengthened payload-free
acceptance package cannot be the final concrete theorem-5 checker interface. -/
theorem not_nonempty
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance} :
    ¬ Nonempty
        (FinalExactCheckerCoreAcceptedCodeExactnessInput
          input checker_acceptance) := by
  rintro ⟨h⟩
  exact h.ordinaryBranchContradiction

end FinalExactCheckerCoreAcceptedCodeExactnessInput

/-! ## Final exact checker-core payload root bridge via derivability -/

/-- Final exact checker-core adapter for the remaining payload root bridge.
The accepted-code exactness part is generated by the concrete PA/Hilbert
checker core; the only remaining payload-side obligations are the two
derivability-soundness clauses from the PA/Hilbert semantics to the current
root `accepted_certificate` vocabulary. -/
structure FinalExactCheckerCorePayloadRootBridgeViaDerivabilityInputs
    {scale_data : InternalPudlakTheorem5ScaleData}
    (input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data)
    (checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance) :
    Prop where
  checker_eq :
    checker_acceptance.checker =
      SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertPowerBoundChecker
        scale_data
  ordinaryDerivableSound :
    ∀ n : Nat,
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
          SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
          (_root_.partialConsistencyCode n) →
        _root_.accepted_certificate (_root_.partialConsistencyCode n)
  strengthenedDerivableSound :
    ∀ n : Nat,
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
          SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
          (_root_.strengthenedPartialConsistencyCode n) →
        _root_.accepted_certificate
          (_root_.strengthenedPartialConsistencyCode n)

namespace FinalExactCheckerCorePayloadRootBridgeViaDerivabilityInputs

def toAcceptedCodeExactnessInput
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (bridge :
      FinalExactCheckerCorePayloadRootBridgeViaDerivabilityInputs
        input checker_acceptance) :
    FinalExactCheckerCoreAcceptedCodeExactnessInput
      input checker_acceptance where
  checker_eq :=
    bridge.checker_eq

def toPayloadRootBridgeViaDerivability
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (bridge :
      FinalExactCheckerCorePayloadRootBridgeViaDerivabilityInputs
        input checker_acceptance) :
    Month9Month10PayloadRootBridgeViaDerivability
      checker_acceptance
      SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics where
  acceptedCodeExactness := by
    intro formulaCode code haccepted
    exact
      bridge.toAcceptedCodeExactnessInput.acceptedCodeExactness
        formulaCode code haccepted
  ordinaryDerivableSound :=
    bridge.ordinaryDerivableSound
  strengthenedDerivableSound :=
    bridge.strengthenedDerivableSound

theorem toCheckerAcceptedRootBridge
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (bridge :
      FinalExactCheckerCorePayloadRootBridgeViaDerivabilityInputs
        input checker_acceptance) :
    Month9Month10CheckerAcceptedRootBridge checker_acceptance :=
  bridge.toPayloadRootBridgeViaDerivability.toCheckerAcceptedRootBridge

/-- Accepted-truth closure for the final exact checker-core root bridge.  This
is the narrow version: it stops at root accepted truth and does not directly
ask for raw payload truth as an input. -/
theorem acceptedTruthClosure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (bridge :
      FinalExactCheckerCorePayloadRootBridgeViaDerivabilityInputs
        input checker_acceptance) :
    Month9Month10CheckerAcceptedRootBridge checker_acceptance ∧
      _root_.PartialConsistencyAcceptedTruth ∧
        _root_.StrengthenedPartialConsistencyAcceptedTruth :=
  ⟨bridge.toCheckerAcceptedRootBridge,
    bridge.toCheckerAcceptedRootBridge.ordinaryAcceptedTruth,
    bridge.toCheckerAcceptedRootBridge.strengthenedAcceptedTruth⟩

/-- Explicit residual split for the final exact checker-core payload bridge.
The final exact checker core generates accepted-code exactness and the two
finite-consistency derivability facts.  The only remaining root-vocabulary
assumptions exposed here are the two derivability-soundness clauses into
`accepted_certificate`; no raw payload truth is used in this closure. -/
theorem acceptedTruthResidualSplit
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (bridge :
      FinalExactCheckerCorePayloadRootBridgeViaDerivabilityInputs
        input checker_acceptance) :
    bridge.toAcceptedCodeExactnessInput.Audit ∧
      checker_acceptance.Audit ∧
        (∀ formulaCode : _root_.FormulaCode, ∀ code : Nat,
          SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertAcceptedProofCodeForFormulaCode
            checker_acceptance.checker formulaCode code →
          SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
            SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
            formulaCode) ∧
          (∀ n : Nat,
            SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
              SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
              (_root_.partialConsistencyCode n)) ∧
            (∀ n : Nat,
              SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
                SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
                (_root_.strengthenedPartialConsistencyCode n)) ∧
              (∀ n : Nat,
                SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
                    SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
                    (_root_.partialConsistencyCode n) →
                  _root_.accepted_certificate
                    (_root_.partialConsistencyCode n)) ∧
                (∀ n : Nat,
                  SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
                      SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
                      (_root_.strengthenedPartialConsistencyCode n) →
                    _root_.accepted_certificate
                      (_root_.strengthenedPartialConsistencyCode n)) ∧
                  _root_.PartialConsistencyAcceptedTruth ∧
                    _root_.StrengthenedPartialConsistencyAcceptedTruth := by
  rcases bridge.toAcceptedCodeExactnessInput.closure with
    ⟨hexactAudit, hacceptedExact, hordinaryDerivable,
      hstrengthenedDerivable⟩
  exact
    ⟨hexactAudit,
      checker_acceptance.audit,
      hacceptedExact,
      hordinaryDerivable,
      hstrengthenedDerivable,
      bridge.ordinaryDerivableSound,
      bridge.strengthenedDerivableSound,
      bridge.acceptedTruthClosure.2.1,
      bridge.acceptedTruthClosure.2.2⟩

/-- Payload-truth closure after crossing the root accepted-certificate bridge.
This theorem intentionally marks the exact place where the two root payload
predicates re-enter. -/
theorem payloadTruthClosure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (bridge :
      FinalExactCheckerCorePayloadRootBridgeViaDerivabilityInputs
        input checker_acceptance) :
    _root_.PartialConsistencyPayloadTruth ∧
      _root_.StrengthenedPartialConsistencyPayloadTruth :=
  ⟨bridge.toCheckerAcceptedRootBridge.ordinaryAcceptedTruth.toPayloadTruth,
    bridge.toCheckerAcceptedRootBridge.strengthenedAcceptedTruth.toPayloadTruth⟩

structure Audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (bridge :
      FinalExactCheckerCorePayloadRootBridgeViaDerivabilityInputs
        input checker_acceptance) :
    Prop where
  checkerAcceptanceClean :
    checker_acceptance.Audit
  checkerEq :
    checker_acceptance.checker =
      SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertPowerBoundChecker
        scale_data
  acceptedCodeExactnessGenerated :
    ∀ formulaCode : _root_.FormulaCode, ∀ code : Nat,
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertAcceptedProofCodeForFormulaCode
        checker_acceptance.checker formulaCode code →
      SondowProjectMonth11PAHilbertCheckerSurface.PAHilbertFormulaCodeDerivable
        SondowProjectMonth11PAHilbertCheckerSurface.concretePAHilbertTheorem5DerivabilitySemantics
        formulaCode
  rootBridge :
    Month9Month10CheckerAcceptedRootBridge checker_acceptance
  ordinaryAcceptedTruth :
    _root_.PartialConsistencyAcceptedTruth
  strengthenedAcceptedTruth :
    _root_.StrengthenedPartialConsistencyAcceptedTruth
  ordinaryPayloadTruth :
    _root_.PartialConsistencyPayloadTruth
  strengthenedPayloadTruth :
    _root_.StrengthenedPartialConsistencyPayloadTruth

theorem audit
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (bridge :
      FinalExactCheckerCorePayloadRootBridgeViaDerivabilityInputs
        input checker_acceptance) :
    bridge.Audit where
  checkerAcceptanceClean :=
    checker_acceptance.audit
  checkerEq :=
    bridge.checker_eq
  acceptedCodeExactnessGenerated :=
    bridge.toPayloadRootBridgeViaDerivability.acceptedCodeExactness
  rootBridge :=
    bridge.toCheckerAcceptedRootBridge
  ordinaryAcceptedTruth :=
    bridge.toCheckerAcceptedRootBridge.ordinaryAcceptedTruth
  strengthenedAcceptedTruth :=
    bridge.toCheckerAcceptedRootBridge.strengthenedAcceptedTruth
  ordinaryPayloadTruth :=
    bridge.payloadTruthClosure.1
  strengthenedPayloadTruth :=
    bridge.payloadTruthClosure.2

theorem closure
    {scale_data : InternalPudlakTheorem5ScaleData}
    {input :
      SondowProjectMonth11PAHilbertCheckerSurface.ConcretePAHilbertPowerBoundFinalExactCheckerCoreInput
        scale_data}
    {checker_acceptance :
      Month9Month10PayloadFreeFiniteConsistencyCheckerAcceptance}
    (bridge :
      FinalExactCheckerCorePayloadRootBridgeViaDerivabilityInputs
        input checker_acceptance) :
    bridge.Audit ∧
      Month9Month10CheckerAcceptedRootBridge checker_acceptance ∧
        _root_.PartialConsistencyAcceptedTruth ∧
          _root_.StrengthenedPartialConsistencyAcceptedTruth ∧
            _root_.PartialConsistencyPayloadTruth ∧
              _root_.StrengthenedPartialConsistencyPayloadTruth :=
  ⟨bridge.audit,
    bridge.toCheckerAcceptedRootBridge,
    bridge.acceptedTruthClosure.2.1,
    bridge.acceptedTruthClosure.2.2,
    bridge.payloadTruthClosure.1,
    bridge.payloadTruthClosure.2⟩

end FinalExactCheckerCorePayloadRootBridgeViaDerivabilityInputs

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
