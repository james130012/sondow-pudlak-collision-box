import EulerLimit.SondowShortProofReproof
import integration.SondowProjectMonth9Month10Month11ExactProofGapHandoff
import integration.SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

noncomputable section

namespace SondowMainCheckedCodeBridge
namespace SondowProjectSondowUpperProofProbe

open SondowProjectMonth9Month10Month11ExactProofGapHandoff
open SondowProjectMonth11Month12ProjectLengthTargetUpperEndpoint

/--
Probe 1: pure Sondow-certificate upper bound from the reproved Sondow forward
package and a concrete verifier/compiler package.

This theorem does not assume an upper-tail certificate.  It derives one from:

* rationality of `euler_mascheroni`;
* the reproved Sondow forward implication;
* a concrete verification package which compiles accepted Sondow certificates
  into polynomial-length PA proofs.

The probe is intentionally stated before the reflection-graft projection.
-/
theorem pureSondowCertificateUpper_fromReproofConcreteVerification
    (hver : _root_.SondowCertificateConcreteVerificationPackage)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        _root_.proof_length _root_.ProofSystem.PA
          _root_.ProofLengthMeasure.symbolSize
          (_root_.sondowCertificateValidCode n) ≤ U n := by
  let hcollapse :=
    _root_.sondow_certificate_eventual_collapse_inputs_of_reproof hver
  rcases hcollapse.formal_verification_short with ⟨U, hU, hshort⟩
  rcases hcollapse.accepted_eventually_under_rationality hrat with
    ⟨upperN, haccepted⟩
  exact ⟨U, hU, upperN, fun n hn => hshort n (haccepted n hn)⟩

/--
Probe 2: project-local upper bound on the shared reflection-graft PA
proof-length box.

This is the exact upper-bound shape needed by the payload-free collision
surface.  It does not take `SondowProjectLocalS21CollapseConclusion`,
`Month9Month10PayloadFreeUpperProvider`, or a `PolynomialUpperTailCertificate`
as input.  Instead it derives the upper tail from the reproved Sondow forward
package and a bounded-arithmetic verification bridge.
-/
theorem projectLocalUpper_fromReproofVerifiedCollapse
    (hverify : _root_.SondowCollapseVerificationBridgePackage)
    (hrat : _root_.is_rational _root_.euler_mascheroni) :
    ∃ U : Nat → Real, _root_.is_polynomial_bound U ∧
      ∃ upperN : Nat, ∀ n : Nat, upperN ≤ n →
        sondowProjectLocalPudlakCollisionBox n ≤ U n := by
  rcases _root_.bounded_arithmetic_short_proof_collapse_of_rationality_reproof
      hverify hrat with ⟨U, hU, upperN, htail⟩
  exact ⟨U, hU, upperN, fun n hn => (htail n hn).2⟩

/--
Probe 3: the same project-local upper bound packaged into the final
payload-free upper-provider interface.

This packaging is only after the proof above; the proof of the upper tail is
not an input field.
-/
def payloadFreeUpperProvider_fromReproofVerifiedCollapse
    (hverify : _root_.SondowCollapseVerificationBridgePackage) :
    Month9Month10PayloadFreeUpperProvider where
  upper_under_rationality :=
    projectLocalUpper_fromReproofVerifiedCollapse hverify

/--
Probe 4: clean Sondow-specific tail source.

This is the lower-level Sondow side we should use for a future payload-free
upper proof.  It avoids the root `accepted_certificate` predicate and stays in
the Sondow full-certificate checker semantics.
-/
abbrev halfDenCheckedTailOfRationalParameter
    (q : Rat) (hq : (q : Real) = _root_.euler_mascheroni) :
    MainSondowFullCertificateCheckedTail :=
  mainSondowFullCertificateCheckedTail_ofReproofRationalParameter_halfDen
    q hq

end SondowProjectSondowUpperProofProbe
end SondowMainCheckedCodeBridge
