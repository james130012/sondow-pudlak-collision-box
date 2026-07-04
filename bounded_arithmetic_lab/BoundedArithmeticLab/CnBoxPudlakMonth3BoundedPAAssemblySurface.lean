/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectSourceAssemblyReleaseSurface

/-!
# Month 3 bounded PA proof-predicate and assembly surface

This module packages the first Month 3 audit surface: a concrete project field
index gives both the accepted-source compiler and the budgeted canonical
assembly provider, and therefore gives a route
`SondowAccepted n -> CanonicalProofCertificateAt bound n`.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace Month3BoundedPAProofPredicateAssemblySurface

structure Statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) : Prop where
  accepted_to_source_nonempty :
    ∀ n : Nat, SondowAccepted n →
      Nonempty (CompiledSondowProjectSourceCertificateAt bounds n)
  accepted_to_canonical_nonempty :
    ∀ n : Nat, SondowAccepted n →
      Nonempty (CanonicalProofCertificateAt bound n)
  accepted_to_canonical_accepted :
    ∀ n : Nat, SondowAccepted n →
      CanonicalProofCertificateAccepted bound n
  source_product_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((ProjectSourceAssemblyFieldReleaseSurface.accepted_compiled_source
        (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
        n haccepted).product.proof.size + 2 : Nat) : Real)) ≤
          bounds.product n
  source_log_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((ProjectSourceAssemblyFieldReleaseSurface.accepted_compiled_source
        (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
        n haccepted).logRelation.proof.size + 2 : Nat) : Real)) ≤
          bounds.logRelation n
  source_decomposition_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((ProjectSourceAssemblyFieldReleaseSurface.accepted_compiled_source
        (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
        n haccepted).decomposition.proof.size + 2 : Nat) : Real)) ≤
          bounds.decomposition n
  source_threePow_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((ProjectSourceAssemblyFieldReleaseSurface.accepted_compiled_source
        (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
        n haccepted).threePow.proof.size + 2 : Nat) : Real)) ≤
          bounds.threePow n
  source_payload_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((ProjectSourceAssemblyFieldReleaseSurface.accepted_compiled_source
        (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
        n haccepted).payload.proof.size + 2 : Nat) : Real)) ≤
          bounds.payload n
  assembled_conclusion :
    ∀ n : Nat, ∀ source : CompiledSondowProjectSourceCertificateAt bounds n,
      (ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (ProjectAssemblyBudgetFieldIndex.ofFieldIndex field_index)
        source).conclusion =
          canonicalPudlakTargetFamilySpec.target n
  assembled_size_eq_budget :
    ∀ n : Nat, ∀ source : CompiledSondowProjectSourceCertificateAt bounds n,
      (ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (ProjectAssemblyBudgetFieldIndex.ofFieldIndex field_index)
        source).size =
          (ProjectSourceAssemblyFieldReleaseSurface.assembly_budget
            (ProjectAssemblyBudgetFieldIndex.ofFieldIndex field_index)
              |>.assembledSize n source)
  assembled_size_plus_two_le_bound :
    ∀ n : Nat, ∀ source : CompiledSondowProjectSourceCertificateAt bounds n,
      ((((ProjectSourceAssemblyFieldReleaseSurface.assembled_proof
        (ProjectAssemblyBudgetFieldIndex.ofFieldIndex field_index)
        source).size + 2 : Nat) : Real)) ≤ bound n
  canonical_certificate_conclusion :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (ProjectSourceAssemblyFieldReleaseSurface.field_index_canonical_certificate_at
        field_index n haccepted).proof.conclusion =
          canonicalPudlakTargetFamilySpec.target n
  canonical_certificate_size_plus_two_le :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      ((((ProjectSourceAssemblyFieldReleaseSurface.field_index_canonical_certificate_at
        field_index n haccepted).proof.size + 2 : Nat) : Real)) ≤
          bound n

def statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    Statement field_index where
  accepted_to_source_nonempty := by
    intro n haccepted
    exact
      ProjectSourceAssemblyFieldReleaseSurface.accepted_compiled_source_nonempty
        (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
        n haccepted
  accepted_to_canonical_nonempty := by
    intro n haccepted
    exact
      ProjectSourceAssemblyFieldReleaseSurface.field_index_canonical_certificate_nonempty
        field_index n haccepted
  accepted_to_canonical_accepted := by
    intro n haccepted
    exact
      ProjectSourceAssemblyFieldReleaseSurface.field_index_canonical_certificate_accepted
        field_index n haccepted
  source_product_size_plus_two_le := by
    intro n haccepted
    exact
      ProjectSourceAssemblyFieldReleaseSurface.accepted_product_size_plus_two_le
        (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
        n haccepted
  source_log_size_plus_two_le := by
    intro n haccepted
    exact
      CompiledSondowProjectSourceCertificateAt.logRelation_size_plus_two_le_at
        (ProjectSourceAssemblyFieldReleaseSurface.accepted_compiled_source
          (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
          n haccepted)
  source_decomposition_size_plus_two_le := by
    intro n haccepted
    exact
      CompiledSondowProjectSourceCertificateAt.decomposition_size_plus_two_le_at
        (ProjectSourceAssemblyFieldReleaseSurface.accepted_compiled_source
          (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
          n haccepted)
  source_threePow_size_plus_two_le := by
    intro n haccepted
    exact
      CompiledSondowProjectSourceCertificateAt.threePow_size_plus_two_le_at
        (ProjectSourceAssemblyFieldReleaseSurface.accepted_compiled_source
          (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
          n haccepted)
  source_payload_size_plus_two_le := by
    intro n haccepted
    exact
      ProjectSourceAssemblyFieldReleaseSurface.accepted_payload_size_plus_two_le
        (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
        n haccepted
  assembled_conclusion := by
    intro n source
    exact
      ProjectSourceAssemblyFieldReleaseSurface.assembly_proof_conclusion
        (ProjectAssemblyBudgetFieldIndex.ofFieldIndex field_index)
        source
  assembled_size_eq_budget := by
    intro n source
    exact
      ProjectSourceAssemblyFieldReleaseSurface.assembly_proof_size_eq_budget
        (ProjectAssemblyBudgetFieldIndex.ofFieldIndex field_index)
        source
  assembled_size_plus_two_le_bound := by
    intro n source
    exact
      ProjectSourceAssemblyFieldReleaseSurface.assembly_proof_size_plus_two_le_bound
        (ProjectAssemblyBudgetFieldIndex.ofFieldIndex field_index)
        source
  canonical_certificate_conclusion := by
    intro n haccepted
    exact
      ProjectSourceAssemblyFieldReleaseSurface.field_index_canonical_certificate_at
        field_index n haccepted |>.proof_conclusion
  canonical_certificate_size_plus_two_le := by
    intro n haccepted
    exact
      ProjectSourceAssemblyFieldReleaseSurface.field_index_canonical_certificate_at
        field_index n haccepted |>.proof_size_plus_two_le

structure Package
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  field_index :
    ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound
  surface_statement : Statement field_index

def Package.ofFieldIndex
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    Package MainRationality SondowAccepted bounds bound where
  field_index := field_index
  surface_statement := statement field_index

theorem package_nonempty_iff_field_index_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (Package MainRationality SondowAccepted bounds bound) ↔
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


end Month3BoundedPAProofPredicateAssemblySurface
end BoundedProofPredicate
end BoundedArithmeticLab
