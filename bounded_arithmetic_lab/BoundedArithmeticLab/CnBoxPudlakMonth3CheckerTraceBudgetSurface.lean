/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakMonth3ProviderClosureSurface

/-!
# Month 3 checker-trace and budget surface

This module exposes the concrete verifier trace produced by the canonical
certificate assembled from an accepted Sondow certificate.  It also records the
budget equations connecting the assembled proof, the canonical certificate, and
the declared proof-length bound.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace Month3CheckerTraceBudgetSurface

noncomputable def traceAt
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CertificateVerifierMachine.AcceptedTrace
      (canonicalProofCertificateVerifierMachine bound) n :=
  (Month3ProviderClosureSurface.canonicalAt
    field_index n haccepted).toAcceptedTrace

theorem trace_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty
      (CertificateVerifierMachine.AcceptedTrace
        (canonicalProofCertificateVerifierMachine bound) n) :=
  ⟨traceAt field_index n haccepted⟩

theorem accepted
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CanonicalProofCertificateAccepted bound n :=
  ⟨traceAt field_index n haccepted⟩

theorem trace_cert_eq_canonical_proof
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (traceAt field_index n haccepted).cert =
      (Month3ProviderClosureSurface.canonicalAt
        field_index n haccepted).proof := by
  rfl

theorem trace_cert_eq_assembled_proof
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (traceAt field_index n haccepted).cert =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (Month3ProviderClosureSurface.assemblyIndex field_index)
        (Month3ProviderClosureSurface.sourceAt
          field_index n haccepted) := by
  rw [trace_cert_eq_canonical_proof field_index n haccepted]
  exact
    Month3ProviderClosureSurface.canonical_proof_eq_assembledProof
      field_index n haccepted

theorem trace_conclusion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (traceAt field_index n haccepted).cert.conclusion =
      canonicalPudlakTargetFamilySpec.target n := by
  simpa [canonicalProofCertificateVerifierMachine]
    using proofCertificateVerifierMachine.acceptedTrace_conclusion
      (target := canonicalPudlakTargetFamilySpec.target)
      (bound := bound)
      (tr := traceAt field_index n haccepted)

theorem trace_size_le_bound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((traceAt field_index n haccepted).size : Real) ≤ bound n := by
  simpa [canonicalProofCertificateVerifierMachine]
    using proofCertificateVerifierMachine.acceptedTrace_size_le_bound
      (target := canonicalPudlakTargetFamilySpec.target)
      (bound := bound)
      (tr := traceAt field_index n haccepted)

theorem assembly_size_eq_budget
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (Month3ProviderClosureSurface.assemblyAt field_index
      (Month3ProviderClosureSurface.sourceAt
        field_index n haccepted)).assembledProof.size =
      (Month3ProviderClosureSurface.budget field_index).assembledSize n
        (Month3ProviderClosureSurface.sourceAt
          field_index n haccepted) :=
  (Month3ProviderClosureSurface.assemblyAt field_index
    (Month3ProviderClosureSurface.sourceAt
      field_index n haccepted)).proof_size_eq_budget

theorem budget_size_plus_two_le_bound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((Month3ProviderClosureSurface.budget field_index).assembledSize n
      (Month3ProviderClosureSurface.sourceAt
        field_index n haccepted) + 2 : Nat) : Real)) ≤ bound n :=
  (Month3ProviderClosureSurface.budget field_index).size_plus_two_le_bound
    n (Month3ProviderClosureSurface.sourceAt field_index n haccepted)

theorem assembled_size_plus_two_le_bound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((Month3ProviderClosureSurface.assemblyAt field_index
      (Month3ProviderClosureSurface.sourceAt
        field_index n haccepted)).assembledProof.size + 2 : Nat) :
        Real)) ≤ bound n := by
  rw [assembly_size_eq_budget field_index n haccepted]
  exact budget_size_plus_two_le_bound field_index n haccepted

theorem canonical_size_eq_budget
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (Month3ProviderClosureSurface.canonicalAt
      field_index n haccepted).proof.size =
      (Month3ProviderClosureSurface.budget field_index).assembledSize n
        (Month3ProviderClosureSurface.sourceAt
          field_index n haccepted) := by
  rw [Month3ProviderClosureSurface.canonical_proof_eq_assembledProof
    field_index n haccepted]
  exact assembly_size_eq_budget field_index n haccepted

theorem canonical_size_plus_two_le_bound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((Month3ProviderClosureSurface.canonicalAt
      field_index n haccepted).proof.size + 2 : Nat) : Real)) ≤
        bound n :=
  (Month3ProviderClosureSurface.canonicalAt
    field_index n haccepted).proof_size_plus_two_le

structure Statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) : Prop where
  provider_closure_statement :
    Month3ProviderClosureSurface.Statement field_index
  trace_nonempty :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      Nonempty
        (CertificateVerifierMachine.AcceptedTrace
          (canonicalProofCertificateVerifierMachine bound) n)
  accepted :
    ∀ n : Nat, ∀ _haccepted : SondowAccepted n,
      CanonicalProofCertificateAccepted bound n
  trace_cert_eq_canonical_proof :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (traceAt field_index n haccepted).cert =
        (Month3ProviderClosureSurface.canonicalAt
          field_index n haccepted).proof
  trace_cert_eq_assembled_proof :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (traceAt field_index n haccepted).cert =
        ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
          (Month3ProviderClosureSurface.assemblyIndex field_index)
          (Month3ProviderClosureSurface.sourceAt
            field_index n haccepted)
  trace_conclusion :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (traceAt field_index n haccepted).cert.conclusion =
        canonicalPudlakTargetFamilySpec.target n
  trace_size_le_bound :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((traceAt field_index n haccepted).size : Real) ≤ bound n
  canonical_size_eq_budget :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (Month3ProviderClosureSurface.canonicalAt
        field_index n haccepted).proof.size =
        (Month3ProviderClosureSurface.budget field_index).assembledSize n
          (Month3ProviderClosureSurface.sourceAt
            field_index n haccepted)
  budget_size_plus_two_le_bound :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((Month3ProviderClosureSurface.budget field_index).assembledSize n
        (Month3ProviderClosureSurface.sourceAt
          field_index n haccepted) + 2 : Nat) : Real)) ≤ bound n

def statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    Statement field_index where
  provider_closure_statement :=
    Month3ProviderClosureSurface.statement field_index
  trace_nonempty := trace_nonempty field_index
  accepted := accepted field_index
  trace_cert_eq_canonical_proof :=
    trace_cert_eq_canonical_proof field_index
  trace_cert_eq_assembled_proof :=
    trace_cert_eq_assembled_proof field_index
  trace_conclusion := trace_conclusion field_index
  trace_size_le_bound := trace_size_le_bound field_index
  canonical_size_eq_budget := canonical_size_eq_budget field_index
  budget_size_plus_two_le_bound :=
    budget_size_plus_two_le_bound field_index

theorem statement_iff_provider_closure_statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    Statement field_index ↔
      Month3ProviderClosureSurface.Statement field_index := by
  constructor
  · intro h
    exact h.provider_closure_statement
  · intro _h
    exact statement field_index


end Month3CheckerTraceBudgetSurface
end BoundedProofPredicate
end BoundedArithmeticLab
