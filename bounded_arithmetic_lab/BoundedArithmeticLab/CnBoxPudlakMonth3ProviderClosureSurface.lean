/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakMonth3SourceSizeAuditSurface

/-!
# Month 3 provider-closure surface

This module records that the accepted-source compiler, the budgeted canonical
assembly provider, and the accepted-to-canonical certificate transport are the
same concrete fields of one project certificate index.  It is the audit point
for the Month 3 claim that the bounded PA proof-predicate interface is not a
separate assumption.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace Month3ProviderClosureSurface

def acceptedCompiler
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound :=
  ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index

def assemblyIndex
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound :=
  ProjectAssemblyBudgetFieldIndex.ofFieldIndex field_index

def provider
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    SondowProjectCanonicalBudgetedAssemblyProvider bounds bound :=
  (assemblyIndex field_index).provider

def budget
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    SondowProjectCanonicalAssemblyBudget bounds bound :=
  (assemblyIndex field_index).budget

noncomputable def acceptedTransport
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    AcceptedToCanonicalProofCertificateTransport SondowAccepted bound :=
  (acceptedCompiler field_index).toCanonicalCertificateTransport

def sourceAt
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt bounds n :=
  ProjectSourceAssemblyFieldReleaseSurface.accepted_compiled_source
    (acceptedCompiler field_index) n haccepted

def assemblyAt
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    SondowProjectCanonicalBudgetedAssemblyFor
      (budget field_index) source :=
  (assemblyIndex field_index).assemblyFor source

def canonicalAt
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CanonicalProofCertificateAt bound n :=
  ProjectSourceAssemblyFieldReleaseSurface.field_index_canonical_certificate_at
    field_index n haccepted

theorem compiler_eq_concrete_field
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    (acceptedCompiler field_index).compiler =
      field_index.accepted_to_compiled_source := by
  rfl

theorem provider_eq_concrete_field
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    provider field_index = field_index.canonical_budgeted_assembly := by
  rfl

theorem acceptedTransport_eq_concrete_field
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    acceptedTransport field_index =
      field_index.accepted_to_canonical_certificate := by
  rfl

theorem sourceAt_eq_sourceSizeSurface_source
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    sourceAt field_index n haccepted =
      Month3SourceSizeAuditSurface.accepted_source
        field_index n haccepted := by
  rfl

theorem canonicalAt_eq_importSurface_certificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    canonicalAt field_index n haccepted =
      Month3CanonicalImportSurface.accepted_to_canonical_certificate
        field_index n haccepted := by
  rfl

theorem canonical_sourceSize_eq_sourceAt_size
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (canonicalAt field_index n haccepted).sourceSize =
      CompiledSondowProjectSourceCertificateAt.sourceSize
        (sourceAt field_index n haccepted) := by
  rfl

theorem canonical_proof_eq_assembledProof
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (canonicalAt field_index n haccepted).proof =
      ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (assemblyIndex field_index) (sourceAt field_index n haccepted) := by
  rfl

theorem canonical_conclusion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (canonicalAt field_index n haccepted).proof.conclusion =
      canonicalPudlakTargetFamilySpec.target n :=
  (canonicalAt field_index n haccepted).proof_conclusion

theorem canonical_size_plus_two_le
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((canonicalAt field_index n haccepted).proof.size + 2 : Nat) :
      Real)) ≤ bound n :=
  (canonicalAt field_index n haccepted).proof_size_plus_two_le

structure Statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) : Prop where
  month3_statement :
    Month3CanonicalImportSurface.CanonicalStatement field_index
  source_size_statement :
    Month3SourceSizeAuditSurface.Statement field_index
  compiler_eq_concrete :
    (acceptedCompiler field_index).compiler =
      field_index.accepted_to_compiled_source
  provider_eq_concrete :
    provider field_index = field_index.canonical_budgeted_assembly
  accepted_transport_eq_concrete :
    acceptedTransport field_index =
      field_index.accepted_to_canonical_certificate
  source_eq_source_size_surface :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      sourceAt field_index n haccepted =
        Month3SourceSizeAuditSurface.accepted_source
          field_index n haccepted
  canonical_eq_import_surface :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      canonicalAt field_index n haccepted =
        Month3CanonicalImportSurface.accepted_to_canonical_certificate
          field_index n haccepted
  canonical_source_size_eq_source :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (canonicalAt field_index n haccepted).sourceSize =
        CompiledSondowProjectSourceCertificateAt.sourceSize
          (sourceAt field_index n haccepted)
  canonical_proof_eq_assembled :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (canonicalAt field_index n haccepted).proof =
        ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
          (assemblyIndex field_index) (sourceAt field_index n haccepted)
  canonical_conclusion :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (canonicalAt field_index n haccepted).proof.conclusion =
        canonicalPudlakTargetFamilySpec.target n
  canonical_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((canonicalAt field_index n haccepted).proof.size + 2 : Nat) :
        Real)) ≤ bound n

def statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    Statement field_index where
  month3_statement := Month3CanonicalImportSurface.statement field_index
  source_size_statement := Month3SourceSizeAuditSurface.statement field_index
  compiler_eq_concrete := compiler_eq_concrete_field field_index
  provider_eq_concrete := provider_eq_concrete_field field_index
  accepted_transport_eq_concrete :=
    acceptedTransport_eq_concrete_field field_index
  source_eq_source_size_surface :=
    sourceAt_eq_sourceSizeSurface_source field_index
  canonical_eq_import_surface :=
    canonicalAt_eq_importSurface_certificate field_index
  canonical_source_size_eq_source :=
    canonical_sourceSize_eq_sourceAt_size field_index
  canonical_proof_eq_assembled :=
    canonical_proof_eq_assembledProof field_index
  canonical_conclusion := canonical_conclusion field_index
  canonical_size_plus_two_le := canonical_size_plus_two_le field_index

theorem statement_iff_month3_statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    Statement field_index ↔
      Month3CanonicalImportSurface.CanonicalStatement field_index := by
  constructor
  · intro h
    exact h.month3_statement
  · intro _h
    exact statement field_index


end Month3ProviderClosureSurface
end BoundedProofPredicate
end BoundedArithmeticLab
