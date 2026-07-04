/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakMonth3CheckerTraceBudgetSurface

/-!
# Month 3 bounded PA proof-predicate ledger surface

This module is the Month 3 audit ledger for the bounded PA proof-predicate
endpoint.  It records that the predicate used by the project is not a new
assumption: it is exactly the accepted-input predicate of the canonical proof
certificate verifier, with traces and certificate-size bounds supplied by the
checker-trace budget surface.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace Month3ProofPredicateLedgerSurface

abbrev boundedPAProofPredicate (bound : Nat → Real) : Nat → Prop :=
  CanonicalProofCertificateAccepted bound

theorem boundedPAProofPredicate_eq_verifier_accepts
    (bound : Nat → Real) :
    boundedPAProofPredicate bound =
      (canonicalProofCertificateVerifierMachine bound).acceptsInput := by
  rfl

structure Statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) : Prop where
  checker_trace_budget_statement :
    Month3CheckerTraceBudgetSurface.Statement field_index
  proof_predicate_eq_verifier_accepts :
    boundedPAProofPredicate bound =
      (canonicalProofCertificateVerifierMachine bound).acceptsInput
  accepted_to_checker_trace_nonempty :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      Nonempty
        (CertificateVerifierMachine.AcceptedTrace
          (canonicalProofCertificateVerifierMachine bound) n)
  accepted_to_proof_predicate :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      boundedPAProofPredicate bound n
  proof_predicate_iff_certificate_at :
    ∀ n : Nat,
      boundedPAProofPredicate bound n ↔
        Nonempty (CanonicalProofCertificateAt bound n)
  checker_trace_cert_eq_canonical_proof :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (Month3CheckerTraceBudgetSurface.traceAt
        field_index n haccepted).cert =
        (Month3ProviderClosureSurface.canonicalAt
          field_index n haccepted).proof
  checker_trace_cert_eq_assembled_proof :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (Month3CheckerTraceBudgetSurface.traceAt
        field_index n haccepted).cert =
        ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
          (Month3ProviderClosureSurface.assemblyIndex field_index)
          (Month3ProviderClosureSurface.sourceAt
            field_index n haccepted)
  checker_trace_conclusion :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (Month3CheckerTraceBudgetSurface.traceAt
        field_index n haccepted).cert.conclusion =
        canonicalPudlakTargetFamilySpec.target n
  checker_trace_size_le_bound :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((Month3CheckerTraceBudgetSurface.traceAt
        field_index n haccepted).size : Real) ≤ bound n
  canonical_certificate_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((Month3ProviderClosureSurface.canonicalAt
        field_index n haccepted).proof.size + 2 : Nat) : Real)) ≤
          bound n

def statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    Statement field_index where
  checker_trace_budget_statement :=
    Month3CheckerTraceBudgetSurface.statement field_index
  proof_predicate_eq_verifier_accepts :=
    boundedPAProofPredicate_eq_verifier_accepts bound
  accepted_to_checker_trace_nonempty :=
    Month3CheckerTraceBudgetSurface.trace_nonempty field_index
  accepted_to_proof_predicate :=
    Month3CheckerTraceBudgetSurface.accepted field_index
  proof_predicate_iff_certificate_at := by
    intro n
    exact canonicalProofCertificateAccepted_iff_certificateAt
  checker_trace_cert_eq_canonical_proof :=
    Month3CheckerTraceBudgetSurface.trace_cert_eq_canonical_proof field_index
  checker_trace_cert_eq_assembled_proof :=
    Month3CheckerTraceBudgetSurface.trace_cert_eq_assembled_proof field_index
  checker_trace_conclusion :=
    Month3CheckerTraceBudgetSurface.trace_conclusion field_index
  checker_trace_size_le_bound :=
    Month3CheckerTraceBudgetSurface.trace_size_le_bound field_index
  canonical_certificate_size_plus_two_le :=
    Month3CheckerTraceBudgetSurface.canonical_size_plus_two_le_bound
      field_index

theorem statement_iff_checker_trace_budget_statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    Statement field_index ↔
      Month3CheckerTraceBudgetSurface.Statement field_index := by
  constructor
  · intro h
    exact h.checker_trace_budget_statement
  · intro _h
    exact statement field_index

structure Package
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  field_index :
    ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound
  ledger : Statement field_index

namespace Package

def ofFieldIndex
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    Package MainRationality SondowAccepted bounds bound where
  field_index := field_index
  ledger := statement field_index

end Package

theorem package_nonempty_iff_field_index_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty
        (Package MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (ProjectConcreteCertificateFieldIndex
          MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨pkg⟩
    exact ⟨pkg.field_index⟩
  · intro h
    rcases h with ⟨field_index⟩
    exact ⟨Package.ofFieldIndex field_index⟩

theorem package_accepted_to_proof_predicate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg : Package MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    boundedPAProofPredicate bound n :=
  pkg.ledger.accepted_to_proof_predicate n haccepted

theorem package_accepted_to_checker_trace_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg : Package MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty
      (CertificateVerifierMachine.AcceptedTrace
        (canonicalProofCertificateVerifierMachine bound) n) :=
  pkg.ledger.accepted_to_checker_trace_nonempty n haccepted

theorem package_proof_predicate_iff_certificate_at
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (pkg : Package MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    boundedPAProofPredicate bound n ↔
      Nonempty (CanonicalProofCertificateAt bound n) :=
  pkg.ledger.proof_predicate_iff_certificate_at n

end Month3ProofPredicateLedgerSurface
end BoundedProofPredicate
end BoundedArithmeticLab
