/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectSameObjectReleaseSurface
import BoundedArithmeticLab.CnBoxPudlakProjectSourceAssemblyReleaseSurface

/-!
# Accepted-route same-object bridge

This module exposes the last object-identity check for the accepted Sondow
route: a canonical certificate produced from an accepted index concludes the
same formula that is stored in the canonical CnBox, and the CnBox code decodes
to that proof conclusion.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace AcceptedSameObjectBridge

open ProjectSourceAssemblyFieldReleaseSurface

theorem canonical_certificate_from_accepted_conclusion_eq_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (acceptedIndex : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (assemblyIndex : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (canonical_certificate_from_accepted
      acceptedIndex assemblyIndex n haccepted).proof.conclusion =
        (canonicalPudlakTargetFamilySpec.box n).formula := by
  calc
    (canonical_certificate_from_accepted
      acceptedIndex assemblyIndex n haccepted).proof.conclusion =
        canonicalPudlakTargetFamilySpec.target n :=
      canonical_certificate_from_accepted_conclusion
        acceptedIndex assemblyIndex n haccepted
    _ = (canonicalPudlakTargetFamilySpec.box n).formula :=
      CnBoxPudlakSameObjectBridge.target_eq_box_formula n

theorem canonical_certificate_from_accepted_box_code_roundtrip_to_conclusion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (acceptedIndex : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (assemblyIndex : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    BAFormula.decode (canonicalPudlakTargetFamilySpec.box n).code =
      some ((canonical_certificate_from_accepted
        acceptedIndex assemblyIndex n haccepted).proof.conclusion) := by
  rw [canonical_certificate_from_accepted_conclusion
    acceptedIndex assemblyIndex n haccepted]
  exact CnBoxPudlakSameObjectBridge.box_code_roundtrip_to_target n

theorem canonical_certificate_from_accepted_code_eq_box_formulaCode
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (acceptedIndex : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (assemblyIndex : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    canonicalPudlakTargetFamilySpec.code
      ((canonical_certificate_from_accepted
        acceptedIndex assemblyIndex n haccepted).proof.conclusion) =
        (canonicalPudlakTargetFamilySpec.box n).formulaCode := by
  rw [canonical_certificate_from_accepted_conclusion
    acceptedIndex assemblyIndex n haccepted]
  exact CnBoxPudlakSameObjectBridge.code_eq_box_formulaCode n

theorem canonical_certificate_from_accepted_sameObject_certificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (_acceptedIndex : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (_assemblyIndex : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (_haccepted : SondowAccepted n) :
    CnBoxPudlakSameObjectBridge.Certificate n :=
  CnBoxPudlakSameObjectBridge.certificate n

theorem canonical_certificate_from_accepted_carries_iff_pa_finite_consistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (_acceptedIndex : ProjectAcceptedCompilerFieldIndex
      MainRationality SondowAccepted bounds bound)
    (_assemblyIndex : ProjectAssemblyBudgetFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (_haccepted : SondowAccepted n) :
    CnBoxCarriesPAFiniteConsistency
      (canonicalPudlakTargetFamilySpec.box n) ↔
        PAFiniteConsistencyStatement n :=
  CnBoxPudlakSameObjectBridge.carries_iff_pa_finite_consistency n

theorem field_index_canonical_certificate_conclusion_eq_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    (field_index_canonical_certificate_at field_index n haccepted).proof.conclusion =
      (canonicalPudlakTargetFamilySpec.box n).formula := by
  simpa [field_index_canonical_certificate_at] using
    canonical_certificate_from_accepted_conclusion_eq_box_formula
      (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
      (ProjectAssemblyBudgetFieldIndex.ofFieldIndex field_index)
      n haccepted

theorem field_index_canonical_certificate_box_code_roundtrip_to_conclusion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    BAFormula.decode (canonicalPudlakTargetFamilySpec.box n).code =
      some ((field_index_canonical_certificate_at
        field_index n haccepted).proof.conclusion) := by
  simpa [field_index_canonical_certificate_at] using
    canonical_certificate_from_accepted_box_code_roundtrip_to_conclusion
      (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
      (ProjectAssemblyBudgetFieldIndex.ofFieldIndex field_index)
      n haccepted

theorem field_index_canonical_certificate_code_eq_box_formulaCode
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (field_index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (haccepted : SondowAccepted n) :
    canonicalPudlakTargetFamilySpec.code
      ((field_index_canonical_certificate_at
        field_index n haccepted).proof.conclusion) =
        (canonicalPudlakTargetFamilySpec.box n).formulaCode := by
  simpa [field_index_canonical_certificate_at] using
    canonical_certificate_from_accepted_code_eq_box_formulaCode
      (ProjectAcceptedCompilerFieldIndex.ofFieldIndex field_index)
      (ProjectAssemblyBudgetFieldIndex.ofFieldIndex field_index)
      n haccepted

theorem field_index_canonical_certificate_carries_iff_pa_finite_consistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (_field_index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) (_haccepted : SondowAccepted n) :
    CnBoxCarriesPAFiniteConsistency
      (canonicalPudlakTargetFamilySpec.box n) ↔
        PAFiniteConsistencyStatement n :=
  CnBoxPudlakSameObjectBridge.carries_iff_pa_finite_consistency n

end AcceptedSameObjectBridge
end BoundedProofPredicate
end BoundedArithmeticLab
