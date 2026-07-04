/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakCompilerCollision
import BoundedArithmeticLab.CertificateVerifier

/-!
# Proof-certificate verifier route for canonical Cn-box collision

This module specializes the existing proof-certificate verifier machine to the
canonical Cn-box target.  It reduces the short-upper input from a bare compiler
to an explicit verifier-machine acceptance predicate with a polynomial bound.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

noncomputable def canonicalProofCertificateVerifierMachine
    (bound : Nat → Real) : CertificateVerifierMachine :=
  proofCertificateVerifierMachine
    canonicalPudlakTargetFamilySpec.target bound

noncomputable def CanonicalProofCertificateAccepted
    (bound : Nat → Real) : Nat → Prop :=
  (canonicalProofCertificateVerifierMachine bound).acceptsInput

noncomputable def canonicalProofCertificateTraceSystem
    {bound : Nat → Real} (hbound : IsPolynomialBound bound) :
    ConcreteVerifierTraceSystem
      canonicalPudlakTargetFamilySpec.target
      (CanonicalProofCertificateAccepted bound) := by
  simpa [CanonicalProofCertificateAccepted,
    canonicalProofCertificateVerifierMachine]
    using (proofCertificateVerifierMachine.compiler
      canonicalPudlakTargetFamilySpec.target hbound).toConcreteTraceSystem

noncomputable def canonicalProofCertificateShortUpper
    {bound : Nat → Real} (hbound : IsPolynomialBound bound) :
    CanonicalCnBoxShortUpperCertificate
      (CanonicalProofCertificateAccepted bound) where
  compiler := (canonicalProofCertificateTraceSystem hbound).toCompiler

structure CanonicalCnBoxProofCertificateChecklist
    (bound : Nat → Real) where
  bound_poly : IsPolynomialBound bound
  acceptance :
    EventualAcceptanceUnderRationality
      (CanonicalProofCertificateAccepted bound)
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
    CanonicalCnBoxProofCertificateChecklist.toExternalChecklist
    {bound : Nat → Real}
    (checklist : CanonicalCnBoxProofCertificateChecklist bound) :
    CanonicalCnBoxExternalObligationChecklist
      (CanonicalProofCertificateAccepted bound) where
  acceptance := checklist.acceptance
  compiler := (canonicalProofCertificateShortUpper checklist.bound_poly).compiler
  lower_source := checklist.lower_source
  relabeling := checklist.relabeling
  length_eq := checklist.length_eq

theorem canonicalCnBox_proof_certificate_collision
    {bound : Nat → Real}
    (checklist : CanonicalCnBoxProofCertificateChecklist bound) :
    False :=
  canonicalCnBox_external_obligation_collision
    checklist.toExternalChecklist

end BoundedProofPredicate
end BoundedArithmeticLab
