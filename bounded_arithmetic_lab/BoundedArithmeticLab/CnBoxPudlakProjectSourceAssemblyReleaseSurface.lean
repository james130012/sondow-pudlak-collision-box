/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectSourceAssemblyFieldIndex

/-!
# Project source and assembly release surface

This module exposes stable paper-facing aliases for the accepted-source
compiler and budgeted-assembly field indexes.  It also records the direct
route from a single concrete field index to the bounded canonical PA proof
certificate interface.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace ProjectSourceAssemblyFieldReleaseSurface

def accepted_compiled_source
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt bounds n :=
  index.compiledSource n haccepted

theorem accepted_compiled_source_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CompiledSondowProjectSourceCertificateAt bounds n) :=
  index.compiledSource_nonempty n haccepted

theorem accepted_product_conclusion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (accepted_compiled_source index n haccepted).product.proof.conclusion =
      sondowProjectComponentFormulas.product n :=
  index.product_conclusion n haccepted

theorem accepted_product_size_plus_two_le
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((accepted_compiled_source index n haccepted).product.proof.size + 2 :
      Nat) : Real)) ≤ bounds.product n :=
  index.product_size_plus_two_le n haccepted

theorem accepted_payload_conclusion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (accepted_compiled_source index n haccepted).payload.proof.conclusion =
      sondowProjectComponentFormulas.payload n :=
  index.payload_conclusion n haccepted

theorem accepted_payload_size_plus_two_le
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((accepted_compiled_source index n haccepted).payload.proof.size + 2 :
      Nat) : Real)) ≤ bounds.payload n :=
  index.payload_size_plus_two_le n haccepted

noncomputable def accepted_to_canonical_transport
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound) :
    AcceptedToCanonicalProofCertificateTransport SondowAccepted bound :=
  index.toCanonicalCertificateTransport

def assembly_budget
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound) :
    SondowProjectCanonicalAssemblyBudget bounds bound :=
  index.budget

def assembly_for
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    SondowProjectCanonicalBudgetedAssemblyFor (assembly_budget index) source :=
  index.assemblyFor source

def assembled_proof
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    BAProofObject BussS21Axiom :=
  index.assembledProof source

theorem assembly_proof_conclusion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    (assembled_proof index source).conclusion =
      canonicalPudlakTargetFamilySpec.target n :=
  index.proof_conclusion source

theorem assembly_proof_size_eq_budget
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    (assembled_proof index source).size =
      (assembly_budget index).assembledSize n source :=
  index.proof_size_eq_budget source

theorem assembly_proof_size_plus_two_le_bound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    ((((assembled_proof index source).size + 2 : Nat) : Real)) ≤ bound n :=
  index.proof_size_plus_two_le_bound source

def assembly_to_assembler
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound) :
    SondowProjectToCanonicalProofCertificateAssembler bounds bound :=
  index.toAssembler

def assembly_canonical_certificate_at
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    CanonicalProofCertificateAt bound n :=
  index.canonicalCertificateAt source

def canonical_certificate_from_accepted
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (acceptedIndex : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (assemblyIndex : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CanonicalProofCertificateAt bound n :=
  assembly_canonical_certificate_at assemblyIndex
    (accepted_compiled_source acceptedIndex n haccepted)

theorem canonical_certificate_from_accepted_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (acceptedIndex : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (assemblyIndex : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CanonicalProofCertificateAt bound n) :=
  ⟨canonical_certificate_from_accepted acceptedIndex assemblyIndex
    n haccepted⟩

theorem canonical_certificate_from_accepted_conclusion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (acceptedIndex : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (assemblyIndex : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (canonical_certificate_from_accepted
      acceptedIndex assemblyIndex n haccepted).proof.conclusion =
        canonicalPudlakTargetFamilySpec.target n :=
  (canonical_certificate_from_accepted acceptedIndex assemblyIndex
    n haccepted).proof_conclusion

theorem canonical_certificate_from_accepted_size_plus_two_le
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (acceptedIndex : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (assemblyIndex : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((canonical_certificate_from_accepted
      acceptedIndex assemblyIndex n haccepted).proof.size + 2 :
        Nat) : Real)) ≤ bound n :=
  (canonical_certificate_from_accepted acceptedIndex assemblyIndex
    n haccepted).proof_size_plus_two_le

def field_index_canonical_certificate_at
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CanonicalProofCertificateAt bound n :=
  canonical_certificate_from_accepted
    (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
    (ProjectAssemblyBudgetFieldIndex.ofFieldIndex field_index)
    n haccepted

theorem field_index_canonical_certificate_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CanonicalProofCertificateAt bound n) :=
  ⟨field_index_canonical_certificate_at field_index n haccepted⟩

theorem field_index_canonical_certificate_accepted
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CanonicalProofCertificateAccepted bound n :=
  (field_index_canonical_certificate_at field_index n haccepted).toAccepted

theorem accepted_index_iff_field_index
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :=
  projectAcceptedCompilerFieldIndex_nonempty_iff_fieldIndex_nonempty

theorem assembly_index_iff_field_index
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :=
  projectAssemblyBudgetFieldIndex_nonempty_iff_fieldIndex_nonempty

theorem accepted_index_iff_assembly_index
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectAssemblyBudgetFieldIndex
        MainRationality SondowAccepted bounds bound) :=
  (accepted_index_iff_field_index).trans
    (assembly_index_iff_field_index).symm

end ProjectSourceAssemblyFieldReleaseSurface
end BoundedProofPredicate
end BoundedArithmeticLab
