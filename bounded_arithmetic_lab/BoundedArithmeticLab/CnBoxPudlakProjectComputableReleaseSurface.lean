/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectComputableGapCertificate

/-!
# Project computable gap release surface

This module provides stable paper-facing aliases for the computable CnBox gap
certificate layer.  The equivalences preserve the exact project completion
obligation; the projection theorems expose the external gap and public
collision routes once the computable certificate is nonempty.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace ProjectComputableGapReleaseSurface

theorem certificate_iff_bundle_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) :=
  projectComputableGapCertificate_nonempty_iff_bundle_nonempty

theorem certificate_iff_completion_obligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) ↔
      ProjectPublicCollisionCompletionObligation
        MainRationality SondowAccepted bounds bound :=
  projectComputableGapCertificate_nonempty_iff_completionObligation

theorem certificate_iff_verified_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakVerifiedProjectInstantiationChecklist
        MainRationality SondowAccepted bounds bound) :=
  projectComputableGapCertificate_nonempty_iff_verifiedInstantiation_nonempty

theorem certificate_iff_project_checklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
        MainRationality SondowAccepted bounds bound) :=
  projectComputableGapCertificate_nonempty_iff_projectChecklist_nonempty

theorem certificate_to_external_gap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  projectComputableGapCertificate_nonempty_to_externalGapCriterion h

theorem certificate_proof_length_gap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) :
    CanonicalCnBoxProofLengthGap :=
  cert.proofLengthGap

theorem certificate_witness_against_declared_bound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (N : Nat) :
    HasProofLengthGapWitness canonicalCnBoxPABox bound N :=
  cert.witnessAgainstDeclaredBound N

theorem certificate_to_public_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) :=
  projectComputableGapCertificate_nonempty_to_publicInstantiation h

theorem certificate_to_public_gap_instantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) :=
  projectComputableGapCertificate_nonempty_to_publicGapInstantiation h

theorem certificate_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)) :
    ¬ MainRationality :=
  projectComputableGapCertificate_nonempty_not_main_rationality h

theorem certificate_formula_roundtrip
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    BAFormula.decode (finiteConsistencyFormula n).encode =
      some (finiteConsistencyFormula n) :=
  cert.formula_roundtrip n

theorem certificate_pa_predicate_alignment
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    BoundedPAPredicateCnBoxAlignment (mkFiniteConsistencyCnBox n) :=
  cert.pa_predicate_alignment n

theorem certificate_carries_pa_finite_consistency_iff
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    CnBoxCarriesPAFiniteConsistency (mkFiniteConsistencyCnBox n) ↔
      PAFiniteConsistencyStatement n :=
  cert.carries_pa_finite_consistency_iff n

theorem certificate_generator_statement_iff
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalFiniteConsistencyGenerator.statement n ↔
      PAFiniteConsistencyStatement n :=
  cert.generator_statement_iff n

theorem certificate_target_eq_finiteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n = finiteConsistencyFormula n :=
  cert.target_eq_finiteConsistency n

theorem certificate_code_eq_partialConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        partialConsistencyCode n :=
  cert.code_eq_partialConsistency n

theorem certificate_lowerLength_eq_canonicalLength
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    cert.toCertificateBackedGapCriterion.lower_source.pa_length n =
      canonicalPudlakTargetFamilySpec.length n :=
  cert.lowerLength_eq_canonicalLength n

theorem certificate_lowerLength_eq_semanticFiniteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    cert.toCertificateBackedGapCriterion.lower_source.pa_length n =
      semanticBAProofLength PAAxiom finiteConsistencyFormula n :=
  cert.lowerLength_eq_semanticFiniteConsistency n

end ProjectComputableGapReleaseSurface
end BoundedProofPredicate
end BoundedArithmeticLab
