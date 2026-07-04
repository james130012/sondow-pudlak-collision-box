/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectConcreteCertificateObligation

/-!
# Project concrete certificate release surface

This module gives stable names to the concrete certificate obligation layer.
It keeps the obligation equivalent to the certificate bundle, the computable
gap certificate, the completion obligation, and the verified instantiation.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace ProjectConcreteCertificateReleaseSurface

theorem obligation_iff_bundle_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) :=
  projectConcreteCertificateObligation_nonempty_iff_bundle_nonempty

theorem obligation_iff_computable_gap_certificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound) :=
  projectConcreteCertificateObligation_nonempty_iff_computableGapCertificate_nonempty

theorem obligation_iff_completion_obligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound) ↔
      ProjectPublicCollisionCompletionObligation
        MainRationality SondowAccepted bounds bound :=
  projectConcreteCertificateObligation_nonempty_iff_completionObligation

theorem obligation_iff_verified_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakVerifiedProjectInstantiationChecklist
        MainRationality SondowAccepted bounds bound) :=
  projectConcreteCertificateObligation_nonempty_iff_verifiedInstantiation_nonempty

theorem obligation_to_external_gap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  projectConcreteCertificateObligation_nonempty_to_externalGapCriterion h

theorem obligation_to_public_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) :=
  projectConcreteCertificateObligation_nonempty_to_publicInstantiation h

theorem obligation_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)) :
    ¬ MainRationality :=
  projectConcreteCertificateObligation_nonempty_not_main_rationality h

theorem obligation_length_eq_semanticFiniteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (obligation : ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    obligation.lower_source.pa_length n =
      semanticBAProofLength PAAxiom finiteConsistencyFormula n :=
  obligation.length_eq_semanticFiniteConsistency n

theorem obligation_target_eq_finiteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (obligation : ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n = finiteConsistencyFormula n :=
  obligation.target_eq_finiteConsistency n

theorem obligation_code_eq_partialConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (obligation : ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        partialConsistencyCode n :=
  obligation.code_eq_partialConsistency n

theorem obligation_witness_against_declared_bound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (obligation : ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)
    (N : Nat) :
    HasProofLengthGapWitness canonicalCnBoxPABox bound N :=
  obligation.witnessAgainstDeclaredBound N

end ProjectConcreteCertificateReleaseSurface
end BoundedProofPredicate
end BoundedArithmeticLab
