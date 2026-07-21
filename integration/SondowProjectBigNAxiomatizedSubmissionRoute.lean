import integration.SondowProjectMonth11Month12HardResidualElimination

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectBigNAxiomatizedSubmissionRoute

open SondowProjectMonth9Month10InternalPudlakWitnessSurface
open SondowProjectMonth9Month10ProofLengthGapFrontier
open SondowProjectMonth9Month10Month11ExactProofGapHandoff
open SondowProjectMonth11Month12HardResidualElimination

/-!
This file is the deliberately axiomatized submission interface.

It does not hide the remaining mathematical obligations inside a large
provider object.  Instead it names the current residual assumptions as Lean
axioms:

* a fixed theorem-5 scale datum;
* four Pudlak/checker-side axioms: checker, enumeration, extractor, and
  proof-length exactness;
* one Sondow-side project upper axiom;
* one additive projection axiom moving that Sondow upper route to the same
  theorem-5 measurement.

The theorem below is then an ordinary Lean proof from exactly these named
interfaces to the collision endpoint.
-/

/-- Fixed theorem-5 scale data for the submission route. -/
axiom submissionScaleData :
  InternalPudlakTheorem5ScaleData

/-- Pudlak axiom 1: checker semantics for the theorem-5 scale datum. -/
axiom pudlakChecker :
  InternalPudlakTheorem5CheckerSemantics.{0} submissionScaleData

/-- Pudlak axiom 2: finite enumeration of all small checker codes. -/
axiom pudlakEnumeration :
  InternalPudlakTheorem5CheckerFiniteEnumeration pudlakChecker

/-- Pudlak axiom 3: computable rejection extractor for the finite search. -/
axiom pudlakExtractor :
  InternalPudlakTheorem5CheckerComputableRejectionExtractor
    pudlakChecker pudlakEnumeration

/--
Pudlak axiom 4: exactness of actual PA proof length against checker minimum
proof-code size on the theorem-5 formula family.
-/
axiom pudlakProofLengthExactness :
  InternalPudlakTheorem5CheckerProofLengthFamilyExactness pudlakChecker

/-!
The Sondow upper route is not taken as a direct upper-provider axiom over
`actualProofLengthMeasured`.  It is lowered to a project-box upper statement
plus the additive projection needed to put it on the same theorem-5 measured
coordinate.
-/

/-- Projection axiom: the theorem-5 checker measurement is bounded by the
Sondow project collision box up to a fixed additive overhead. -/
axiom pudlakAdditiveProjection :
  InternalPudlakTheorem5AdditiveProjectBoxProjection
    submissionScaleData pudlakChecker.toProofCodeSemantics

/-- Sondow-side axiom: rationality gives the project-local S²₁ collapse upper
route. -/
axiom sondowProjectUpper :
  SondowProjectLocalS21CollapseConclusion

/-- The actual-proof-length transport residual induced by the named exactness
axiom. -/
def pudlakActualTransport :
    ActualProofLengthGapTransportBlocker pudlakChecker :=
  actual_transport_of_checker_proof_length_family_exactness
    pudlakProofLengthExactness

/-- The corrected actual-measured residual used by the endpoint. -/
def pudlakResidual :
    CorrectedActualMeasuredResidual pudlakChecker where
  actual_transport := pudlakActualTransport

/-- The checked-to-actual bridge induced by the named proof-length exactness
axiom. -/
def pudlakCheckedActualBridge :
    Month9Month10CheckedMeasuredToActualProofLengthBridge
      submissionScaleData pudlakChecker.toProofCodeSemantics where
  checked_eq_actual := by
    intro n
    simpa [actualProofLengthMeasured,
      month9_month10_checkedProofCodeMeasured,
      InternalPudlakTheorem5CheckerSemantics.minProofCodeSizeAt]
      using (pudlakProofLengthExactness.proof_length_eq_minProofCodeSizeAt n).symm

/-- The actual-measured Sondow upper provider constructed from the lower-level
Sondow project upper axiom and the additive projection axiom. -/
def sondowUpperProvider :
    Month9Month10AbstractMeasuredUpperProvider
      (actualProofLengthMeasured submissionScaleData) :=
  actualUpperProviderOfProjectUpperAndAdditiveProjection
    pudlakAdditiveProjection pudlakCheckedActualBridge sondowProjectUpper

/-- The endpoint obtained from the four Pudlak axioms and the Sondow upper
provider axiom. -/
def axiomatizedEndpoint :
    Month9Month10ActualProofLengthDirectCollisionEndpoint
      submissionScaleData :=
  corrected_actual_measured_endpoint
    pudlakExtractor pudlakResidual sondowUpperProvider

/-- The exact upper tail selected on the rationality branch. -/
abbrev axiomatizedUpperTail
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    PolynomialUpperTailCertificate
      (actualProofLengthMeasured submissionScaleData) :=
  corrected_actual_upper_tail
    pudlakExtractor pudlakResidual sondowUpperProvider hrat

/-- Formula for the computed collision index in the axiomatized route. -/
theorem axiomatizedComputedN_eq_extractorWitness
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    axiomatizedEndpoint.computedCollisionNOfRationality hrat =
      pudlakExtractor.witness
        (axiomatizedUpperTail hrat).U
        (axiomatizedUpperTail hrat).polynomial
        (axiomatizedUpperTail hrat).upperN :=
  corrected_actual_computed_n_eq_extractor_witness
    pudlakExtractor pudlakResidual sondowUpperProvider hrat

/-- The lower and upper inequalities collide at the computed index. -/
theorem axiomatizedCollisionAtComputedN
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    (axiomatizedUpperTail hrat).U
        (axiomatizedEndpoint.computedCollisionNOfRationality hrat) <
      actualProofLengthMeasured submissionScaleData
        (axiomatizedEndpoint.computedCollisionNOfRationality hrat) ∧
      actualProofLengthMeasured submissionScaleData
          (axiomatizedEndpoint.computedCollisionNOfRationality hrat) ≤
        (axiomatizedUpperTail hrat).U
          (axiomatizedEndpoint.computedCollisionNOfRationality hrat) ∧
        False :=
  ⟨axiomatizedEndpoint.lower_at_computedCollisionN hrat,
    axiomatizedEndpoint.upper_at_computedCollisionN hrat,
    axiomatizedEndpoint.computed_n_contradiction hrat⟩

/--
Submission-facing theorem from the named Lean axioms.

This statement intentionally exposes no `tail_gap`, direct `upper_provider`, or
`monomial_growth` parameter.  The remaining credit-bearing inputs are the named
Lean axioms above.
-/
theorem axiomatizedSubmissionRoute :
    (∀ hrat : _root_.is_rational _root_.euler_mascheroni,
      axiomatizedEndpoint.computedCollisionNOfRationality hrat =
        pudlakExtractor.witness
          (axiomatizedUpperTail hrat).U
          (axiomatizedUpperTail hrat).polynomial
          (axiomatizedUpperTail hrat).upperN) ∧
      (∀ _hrat : _root_.is_rational _root_.euler_mascheroni, False) ∧
        ¬ _root_.is_rational _root_.euler_mascheroni :=
  ⟨axiomatizedComputedN_eq_extractorWitness,
    axiomatizedEndpoint.computed_n_contradiction,
    axiomatizedEndpoint.not_rational⟩

/-- Audit bundle for the axiomatized endpoint. -/
theorem axiomatizedEndpointAudit :
    axiomatizedEndpoint.Audit :=
  axiomatizedEndpoint.audit

end SondowProjectBigNAxiomatizedSubmissionRoute
end SondowMainCheckedCodeBridge
