/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakMonth3BoundedPAAssemblySurface

/-!
# Month 3 canonical import surface

This module is the compact import point for the Month 3 bounded PA
proof-predicate and assembly route.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace Month3CanonicalImportSurface

abbrev CanonicalStatement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) : Prop :=
  Month3BoundedPAProofPredicateAssemblySurface.Statement field_index

def statement
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound) :
    CanonicalStatement field_index :=
  Month3BoundedPAProofPredicateAssemblySurface.statement field_index

def accepted_to_canonical_certificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CanonicalProofCertificateAt bound n :=
  ProjectSourceAssemblyFieldReleaseSurface.field_index_canonical_certificate_at
    field_index n haccepted

theorem accepted_to_canonical_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    Nonempty (CanonicalProofCertificateAt bound n) :=
  (statement field_index).accepted_to_canonical_nonempty n haccepted

theorem accepted_to_canonical_accepted
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    CanonicalProofCertificateAccepted bound n :=
  (statement field_index).accepted_to_canonical_accepted n haccepted

theorem canonical_certificate_size_plus_two_le
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index :
      ProjectConcreteCertificateFieldIndex
        MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    ((((accepted_to_canonical_certificate field_index n haccepted).proof.size
      + 2 : Nat) : Real)) ≤ bound n :=
  (statement field_index).canonical_certificate_size_plus_two_le n haccepted

theorem package_nonempty_iff_field_index_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty
        (Month3BoundedPAProofPredicateAssemblySurface.Package
          MainRationality SondowAccepted bounds bound) ↔
      Nonempty
        (ProjectConcreteCertificateFieldIndex
          MainRationality SondowAccepted bounds bound) :=
  Month3BoundedPAProofPredicateAssemblySurface.package_nonempty_iff_field_index_nonempty


end Month3CanonicalImportSurface
end BoundedProofPredicate
end BoundedArithmeticLab
