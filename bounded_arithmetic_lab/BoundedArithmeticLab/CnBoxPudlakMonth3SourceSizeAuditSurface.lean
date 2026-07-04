/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakMonth3CanonicalImportSurface

/-!
# Month 3 source-size audit surface

This module isolates the source-size accounting for accepted Sondow project
certificates.  The total source size is the sum of the five component source
sizes, and the canonical PA certificate records that same source size.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace Month3SourceSizeAuditSurface

def accepted_source
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CompiledSondowProjectSourceCertificateAt bounds n :=
  ProjectSourceAssemblyFieldReleaseSurface.accepted_compiled_source
    (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
    n haccepted

def accepted_source_size
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) : Nat :=
  CompiledSondowProjectSourceCertificateAt.sourceSize
    (accepted_source field_index n haccepted)

theorem accepted_source_size_eq_component_sum
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    accepted_source_size field_index n haccepted =
      (accepted_source field_index n haccepted).product.sourceSize +
        (accepted_source field_index n haccepted).logRelation.sourceSize +
          (accepted_source field_index n haccepted).decomposition.sourceSize +
            (accepted_source field_index n haccepted).threePow.sourceSize +
              (accepted_source field_index n haccepted).payload.sourceSize := by
  rfl

theorem canonical_certificate_source_size_eq_accepted_source_size
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (Month3CanonicalImportSurface.accepted_to_canonical_certificate
      field_index n haccepted).sourceSize =
        accepted_source_size field_index n haccepted := by
  rfl

structure Statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) : Prop where
  source_size_eq_component_sum :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      accepted_source_size field_index n haccepted =
        (accepted_source field_index n haccepted).product.sourceSize +
          (accepted_source field_index n haccepted).logRelation.sourceSize +
            (accepted_source field_index n haccepted).decomposition.sourceSize +
              (accepted_source field_index n haccepted).threePow.sourceSize +
                (accepted_source field_index n haccepted).payload.sourceSize
  canonical_source_size_eq :
    ∀ n : Nat, ∀ haccepted : SondowAccepted n,
      (Month3CanonicalImportSurface.accepted_to_canonical_certificate
        field_index n haccepted).sourceSize =
          accepted_source_size field_index n haccepted

def statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    Statement field_index where
  source_size_eq_component_sum :=
    accepted_source_size_eq_component_sum field_index
  canonical_source_size_eq :=
    canonical_certificate_source_size_eq_accepted_source_size field_index


end Month3SourceSizeAuditSurface
end BoundedProofPredicate
end BoundedArithmeticLab
