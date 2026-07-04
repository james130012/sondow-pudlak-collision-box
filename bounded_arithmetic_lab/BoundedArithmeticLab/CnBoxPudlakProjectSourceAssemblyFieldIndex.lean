/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectConcreteFieldReleaseSurface

/-!
# Project source and assembly field index

This module splits two concrete certificate obligations into audit-facing
interfaces: accepted Sondow sources compile into component certificates, and
budgeted assembly converts compiled sources into canonical CnBox certificates.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure ProjectAcceptedCompilerFieldIndex
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  field_index : ProjectConcreteCertificateFieldIndex
    MainRationality SondowAccepted bounds bound

namespace ProjectAcceptedCompilerFieldIndex

def ofFieldIndex
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound where
  field_index := field_index

def toFieldIndex
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound) :
    ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound :=
  index.field_index

def compiler
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound) :
    AcceptedToCompiledProjectSourceCertificateCompiler
      SondowAccepted bounds :=
  index.field_index.accepted_to_compiled_source

def compiledSource
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt bounds n :=
  index.compiler.compile n haccepted

theorem compiledSource_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CompiledSondowProjectSourceCertificateAt bounds n) :=
  ⟨index.compiledSource n haccepted⟩

def compiledExists
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound) :
    AcceptedToCompiledProjectSourceCertificateExists
      SondowAccepted bounds :=
  fun n haccepted => index.compiledSource_nonempty n haccepted

theorem product_conclusion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (index.compiledSource n haccepted).product.proof.conclusion =
      sondowProjectComponentFormulas.product n :=
  CompiledSondowProjectSourceCertificateAt.product_conclusion_at
    (index.compiledSource n haccepted)

theorem product_size_plus_two_le
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((index.compiledSource n haccepted).product.proof.size + 2 :
      Nat) : Real)) ≤ bounds.product n :=
  CompiledSondowProjectSourceCertificateAt.product_size_plus_two_le_at
    (index.compiledSource n haccepted)

theorem payload_conclusion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (index.compiledSource n haccepted).payload.proof.conclusion =
      sondowProjectComponentFormulas.payload n :=
  CompiledSondowProjectSourceCertificateAt.payload_conclusion_at
    (index.compiledSource n haccepted)

theorem payload_size_plus_two_le
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((index.compiledSource n haccepted).payload.proof.size + 2 :
      Nat) : Real)) ≤ bounds.payload n :=
  CompiledSondowProjectSourceCertificateAt.payload_size_plus_two_le_at
    (index.compiledSource n haccepted)

noncomputable def toCanonicalCertificateTransport
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound) :
    AcceptedToCanonicalProofCertificateTransport SondowAccepted bound :=
  index.field_index.accepted_to_canonical_certificate

end ProjectAcceptedCompilerFieldIndex

structure ProjectAssemblyBudgetFieldIndex
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  field_index : ProjectConcreteCertificateFieldIndex
    MainRationality SondowAccepted bounds bound

namespace ProjectAssemblyBudgetFieldIndex

def ofFieldIndex
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound where
  field_index := field_index

def toFieldIndex
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound) :
    ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound :=
  index.field_index

def provider
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound) :
    SondowProjectCanonicalBudgetedAssemblyProvider bounds bound :=
  index.field_index.canonical_budgeted_assembly

def budget
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound) :
    SondowProjectCanonicalAssemblyBudget bounds bound :=
  index.provider.budget

def assemblyFor
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    SondowProjectCanonicalBudgetedAssemblyFor index.budget source :=
  index.provider.assembly n source

def assembledProof
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    BAProofObject BussS21Axiom :=
  (index.assemblyFor source).assembledProof

theorem proof_conclusion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    (index.assembledProof source).conclusion =
      canonicalPudlakTargetFamilySpec.target n :=
  (index.assemblyFor source).proof_conclusion

theorem proof_size_eq_budget
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    (index.assembledProof source).size =
      index.budget.assembledSize n source :=
  (index.assemblyFor source).proof_size_eq_budget

theorem proof_size_plus_two_le_bound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    ((((index.assembledProof source).size + 2 : Nat) : Real)) ≤ bound n :=
  (index.assemblyFor source).toAssemblyFor.proof_size_plus_two_le

def toAssemblyProvider
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound) :
    SondowProjectCanonicalAssemblyProvider bounds bound :=
  index.provider.toAssemblyProvider

def toAssembler
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound) :
    SondowProjectToCanonicalProofCertificateAssembler bounds bound :=
  index.toAssemblyProvider.toAssembler

def canonicalCertificateAt
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    CanonicalProofCertificateAt bound n :=
  ((index.assemblyFor source).toAssemblyFor).toCanonicalProofCertificateAt

end ProjectAssemblyBudgetFieldIndex

theorem projectAcceptedCompilerFieldIndex_nonempty_iff_fieldIndex_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨index⟩
    exact ⟨index.toFieldIndex⟩
  · intro h
    rcases h with ⟨field_index⟩
    exact ⟨ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index⟩

theorem projectAssemblyBudgetFieldIndex_nonempty_iff_fieldIndex_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨index⟩
    exact ⟨index.toFieldIndex⟩
  · intro h
    rcases h with ⟨field_index⟩
    exact ⟨ProjectAssemblyBudgetFieldIndex.ofFieldIndex field_index⟩

end BoundedProofPredicate
end BoundedArithmeticLab
