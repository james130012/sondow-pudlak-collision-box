/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectCollision

/-!
# Accepted-predicate transport through canonical proof certificates

This module refines the project-level Sondow-to-CnBox interface.  Instead of
using a bare predicate implication into the canonical proof-certificate
acceptance predicate, it records the concrete proof certificate produced at
each index.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

noncomputable def canonicalProofCertificateExpectedCode :
    Nat → FormulaCode :=
  fun n =>
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n)

theorem canonicalProofCertificateExpectedCode_eq_partialConsistency
    (n : Nat) :
    canonicalProofCertificateExpectedCode n = partialConsistencyCode n := by
  rfl

structure CanonicalProofCertificateAt
    (bound : Nat → Real) (n : Nat) where
  sourceSize : Nat
  proof : BAProofObject BussS21Axiom
  proof_conclusion :
    proof.conclusion = canonicalPudlakTargetFamilySpec.target n
  proof_size_plus_two_le :
    (((proof.size + 2 : Nat) : Real)) ≤ bound n

theorem CanonicalProofCertificateAt.proof_conclusion_eq_finiteConsistency
    {bound : Nat → Real} {n : Nat}
    (cert : CanonicalProofCertificateAt bound n) :
    cert.proof.conclusion = finiteConsistencyFormula n := by
  rw [← canonicalPudlakTarget_target_eq_finiteConsistency n]
  exact cert.proof_conclusion

def CanonicalProofCertificateAt.toComponentProofCodeCert
    {bound : Nat → Real} {n : Nat}
    (cert : CanonicalProofCertificateAt bound n) :
    CompiledComponentProofCodeCert
      canonicalPudlakTargetFamilySpec.target bound
      canonicalProofCertificateExpectedCode where
  index := n
  sourceSize := cert.sourceSize
  proof := cert.proof
  proof_conclusion := cert.proof_conclusion
  proof_size_plus_two_le := cert.proof_size_plus_two_le

noncomputable def CanonicalProofCertificateAt.toAcceptedTrace
    {bound : Nat → Real} {n : Nat}
    (cert : CanonicalProofCertificateAt bound n) :
    CertificateVerifierMachine.AcceptedTrace
      (canonicalProofCertificateVerifierMachine bound) n := by
  simpa [canonicalProofCertificateVerifierMachine]
    using
      (cert.toComponentProofCodeCert.toProofCertificateTraceAt
        (n := n) rfl)

theorem CanonicalProofCertificateAt.toAccepted
    {bound : Nat → Real} {n : Nat}
    (cert : CanonicalProofCertificateAt bound n) :
    CanonicalProofCertificateAccepted bound n := by
  exact ⟨cert.toAcceptedTrace⟩

noncomputable def CanonicalProofCertificateAt.ofAcceptedTrace
    {bound : Nat → Real} {n : Nat}
    (tr : CertificateVerifierMachine.AcceptedTrace
      (canonicalProofCertificateVerifierMachine bound) n) :
    CanonicalProofCertificateAt bound n where
  sourceSize := tr.size
  proof := tr.cert
  proof_conclusion := by
    simpa [canonicalProofCertificateVerifierMachine]
      using
        (proofCertificateVerifierMachine.acceptedTrace_conclusion
          (target := canonicalPudlakTargetFamilySpec.target)
          (bound := bound) tr)
  proof_size_plus_two_le := by
    simpa [canonicalProofCertificateVerifierMachine,
      CertificateVerifierMachine.AcceptedTrace.size,
      proofCertificateVerifierMachine, ProofCertificateState.size,
      Nat.add_assoc]
      using
        (proofCertificateVerifierMachine.acceptedTrace_size_le_bound
          (target := canonicalPudlakTargetFamilySpec.target)
          (bound := bound) tr)

theorem canonicalProofCertificateAccepted_iff_certificateAt
    {bound : Nat → Real} {n : Nat} :
    CanonicalProofCertificateAccepted bound n ↔
      Nonempty (CanonicalProofCertificateAt bound n) := by
  constructor
  · intro haccepted
    rcases haccepted with ⟨tr⟩
    exact ⟨CanonicalProofCertificateAt.ofAcceptedTrace tr⟩
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact cert.toAccepted

structure AcceptedToCanonicalProofCertificateTransport
    (Accepted : Nat → Prop) (bound : Nat → Real) : Prop where
  certificate_of_accepted :
    ∀ n : Nat, Accepted n →
      Nonempty (CanonicalProofCertificateAt bound n)

noncomputable def AcceptedToCanonicalProofCertificateTransport.toPredicateTransport
    {Accepted : Nat → Prop} {bound : Nat → Real}
    (transport :
      AcceptedToCanonicalProofCertificateTransport Accepted bound) :
    AcceptedPredicateTransport
      Accepted (CanonicalProofCertificateAccepted bound) where
  map_accepted := by
    intro n haccepted
    exact (canonicalProofCertificateAccepted_iff_certificateAt).2
      (transport.certificate_of_accepted n haccepted)

noncomputable def AcceptedToCanonicalProofCertificateTransport.ofPredicateTransport
    {Accepted : Nat → Prop} {bound : Nat → Real}
    (transport :
      AcceptedPredicateTransport
        Accepted (CanonicalProofCertificateAccepted bound)) :
    AcceptedToCanonicalProofCertificateTransport Accepted bound where
  certificate_of_accepted := by
    intro n haccepted
    exact (canonicalProofCertificateAccepted_iff_certificateAt).1
      (transport.map_accepted n haccepted)

theorem acceptedToCanonicalProofCertificateTransport_iff_predicateTransport
    {Accepted : Nat → Prop} {bound : Nat → Real} :
    AcceptedToCanonicalProofCertificateTransport Accepted bound ↔
      AcceptedPredicateTransport
        Accepted (CanonicalProofCertificateAccepted bound) := by
  constructor
  · intro h
    exact h.toPredicateTransport
  · intro h
    exact AcceptedToCanonicalProofCertificateTransport.ofPredicateTransport h

noncomputable def mainAcceptedEventually_toCanonicalProofCertificate
    {MainRationality : Prop} {Accepted : Nat → Prop}
    {bound : Nat → Real}
    (transport :
      AcceptedToCanonicalProofCertificateTransport Accepted bound)
    (haccepted :
      MainAcceptedEventuallyUnderRationality MainRationality Accepted) :
    MainAcceptedEventuallyUnderRationality MainRationality
      (CanonicalProofCertificateAccepted bound) :=
  mainAcceptedEventually_transport
    transport.toPredicateTransport haccepted

structure ProjectLevelCnBoxProofCertificateTransportChecklist
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bound : Nat → Real) where
  bound_poly : IsPolynomialBound bound
  sondow_eventual_accepted :
    MainAcceptedEventuallyUnderRationality
      MainRationality SondowAccepted
  accepted_to_certificate :
    AcceptedToCanonicalProofCertificateTransport SondowAccepted bound
  lower_source : BussPudlakTheorem5PALowerBoundSource
  relabeling :
    SemanticFormulaRelabeling lower_source.box.formula
      (concretePAFormalization
        canonicalPudlakTargetFamilySpec.target
        canonicalPudlakTargetFamilySpec.code).box.formula
  length_eq :
    ∀ n : Nat,
      lower_source.pa_length n =
        semanticBAProofLength PAAxiom finiteConsistencyFormula n

noncomputable def
    ProjectLevelCnBoxProofCertificateTransportChecklist.toProjectChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxProofCertificateTransportChecklist
        MainRationality SondowAccepted bound) :
    ProjectLevelCnBoxCollisionChecklist
      MainRationality SondowAccepted bound where
  bound_poly := checklist.bound_poly
  sondow_eventual_accepted := checklist.sondow_eventual_accepted
  accepted_transport := checklist.accepted_to_certificate.toPredicateTransport
  lower_source := checklist.lower_source
  relabeling := checklist.relabeling
  length_eq := checklist.length_eq

noncomputable def
    ProjectLevelCnBoxProofCertificateTransportChecklist.canonicalAcceptance
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxProofCertificateTransportChecklist
        MainRationality SondowAccepted bound) :
    MainAcceptedEventuallyUnderRationality
      MainRationality (CanonicalProofCertificateAccepted bound) :=
  mainAcceptedEventually_toCanonicalProofCertificate
    checklist.accepted_to_certificate checklist.sondow_eventual_accepted

noncomputable def
    ProjectLevelCnBoxProofCertificateTransportChecklist.toProofCertificateChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxProofCertificateTransportChecklist
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    CanonicalCnBoxProofCertificateChecklist bound :=
  checklist.toProjectChecklist.toProofCertificateChecklist hmain

theorem ProjectLevelCnBoxProofCertificateTransportChecklist.false_of_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxProofCertificateTransportChecklist
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    False :=
  checklist.toProjectChecklist.false_of_main_rationality hmain

theorem ProjectLevelCnBoxProofCertificateTransportChecklist.not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxProofCertificateTransportChecklist
        MainRationality SondowAccepted bound) :
    ¬ MainRationality := by
  intro hmain
  exact checklist.false_of_main_rationality hmain

end BoundedProofPredicate
end BoundedArithmeticLab
