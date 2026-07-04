/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxFiniteConsistencyGenerator
import BoundedArithmeticLab.CnBoxPudlakProjectReleaseSurface

/-!
# Project computable gap certificate

This module ties the project-level public collision bundle to the executable
finite-consistency CnBox encoder and bounded PA proof-predicate interface.  It
does not manufacture the final project certificate bundle; it proves that once
that bundle is supplied, the computable CnBox side, completion obligation, and
public instantiation route are the same object-level obligation.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure ProjectComputableGapCertificate
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  bundle : ProjectPublicCollisionCertificateBundle
    MainRationality SondowAccepted bounds bound
  same_object : ∀ n : Nat, FiniteConsistencySameObjectCertificate n
  generation : ∀ n : Nat, FiniteConsistencyGenerationCertificate n
  predicate_alignment :
    ∀ n : Nat, BoundedPAPredicateCnBoxAlignment (mkFiniteConsistencyCnBox n)

namespace ProjectComputableGapCertificate

def ofCertificateBundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound where
  bundle := bundle
  same_object := canonicalFiniteConsistency_sameObjectCertificate
  generation := mkFiniteConsistencyGenerationCertificate
  predicate_alignment := mkFiniteConsistencyCnBox_predicateAlignment

def toCertificateBundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) :
    ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound :=
  cert.bundle

def toAuditChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) :
    ProjectPublicCollisionAuditChecklist
      MainRationality SondowAccepted bounds bound :=
  ProjectPublicCollisionAuditChecklist.ofCertificateBundle cert.bundle

def toCompletionLedger
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) :
    ProjectPublicCollisionCompletionLedger
      MainRationality SondowAccepted bounds bound :=
  ProjectPublicCollisionCompletionLedger.ofAuditChecklist cert.toAuditChecklist

theorem toCompletionObligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) :
    ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound :=
  ⟨cert.toCompletionLedger⟩

noncomputable def toExternalGapCriterionWitness
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  cert.bundle.toExternalGapCriterionWitness

noncomputable def toPublicCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) :
    PublicCollisionInstantiation MainRationality :=
  cert.bundle.toPublicCollisionInstantiation

noncomputable def toPublicGapCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) :
    PublicGapCollisionInstantiation MainRationality :=
  cert.bundle.toPublicGapCollisionInstantiation

noncomputable def toCertificateBackedGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  cert.bundle.toCertificateBackedGapCriterion

noncomputable def proofLengthGap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) :
    CanonicalCnBoxProofLengthGap :=
  cert.toCertificateBackedGapCriterion.proofLengthGap

noncomputable def witnessAgainstDeclaredBound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (N : Nat) :
    HasProofLengthGapWitness canonicalCnBoxPABox bound N :=
  cert.toCertificateBackedGapCriterion.witnessAgainstDeclaredBound N

theorem target_eq_finiteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n = finiteConsistencyFormula n :=
  cert.toCertificateBackedGapCriterion.target_eq_finiteConsistency n

theorem code_eq_partialConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        partialConsistencyCode n :=
  cert.toCertificateBackedGapCriterion.code_eq_partialConsistency n

theorem lowerLength_eq_canonicalLength
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    cert.toCertificateBackedGapCriterion.lower_source.pa_length n =
      canonicalPudlakTargetFamilySpec.length n :=
  cert.toCertificateBackedGapCriterion.lowerLength_eq_canonicalLength n

theorem lowerLength_eq_semanticFiniteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    cert.toCertificateBackedGapCriterion.lower_source.pa_length n =
      semanticBAProofLength PAAxiom finiteConsistencyFormula n :=
  cert.toCertificateBackedGapCriterion.length_eq n

theorem formula_roundtrip
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (_cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    BAFormula.decode (finiteConsistencyFormula n).encode =
      some (finiteConsistencyFormula n) :=
  finiteConsistencyFormula_decode_encode n

theorem cn_box_certifies
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    (mkFiniteConsistencyCnBox n).Certifies := by
  have hbox := (cert.generation n).box_eq
  simpa [hbox] using (cert.generation n).box_certifies

theorem pa_predicate_alignment
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    BoundedPAPredicateCnBoxAlignment (mkFiniteConsistencyCnBox n) :=
  cert.predicate_alignment n

theorem carries_pa_finite_consistency_iff
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (_cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    CnBoxCarriesPAFiniteConsistency (mkFiniteConsistencyCnBox n) ↔
      PAFiniteConsistencyStatement n :=
  mkFiniteConsistencyCnBox_carriesPAFiniteConsistency_iff n

theorem generator_statement_iff
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalFiniteConsistencyGenerator.statement n ↔
      PAFiniteConsistencyStatement n :=
  (cert.same_object n).statement_iff

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  cert.bundle.not_main_rationality

end ProjectComputableGapCertificate

theorem projectComputableGapCertificate_nonempty_iff_bundle_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨cert.toCertificateBundle⟩
  · intro h
    rcases h with ⟨bundle⟩
    exact ⟨ProjectComputableGapCertificate.ofCertificateBundle bundle⟩

theorem projectComputableGapCertificate_nonempty_iff_completionObligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) ↔
      ProjectPublicCollisionCompletionObligation
        MainRationality SondowAccepted bounds bound := by
  exact projectComputableGapCertificate_nonempty_iff_bundle_nonempty.trans
    projectPublicCollisionCompletionObligation_iff_bundle_nonempty.symm

theorem projectComputableGapCertificate_nonempty_iff_verifiedInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakVerifiedProjectInstantiationChecklist
        MainRationality SondowAccepted bounds bound) := by
  exact projectComputableGapCertificate_nonempty_iff_completionObligation.trans
    projectPublicCollisionCompletionLedger_nonempty_iff_verifiedInstantiation_nonempty

theorem projectComputableGapCertificate_nonempty_iff_projectChecklist_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
        MainRationality SondowAccepted bounds bound) := by
  exact projectComputableGapCertificate_nonempty_iff_completionObligation.trans
    projectPublicCollisionCompletionLedger_nonempty_iff_projectChecklist_nonempty

theorem projectComputableGapCertificate_nonempty_to_completionObligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)) :
    ProjectPublicCollisionCompletionObligation
      MainRationality SondowAccepted bounds bound :=
  projectComputableGapCertificate_nonempty_iff_completionObligation.1 h

theorem projectComputableGapCertificate_nonempty_to_externalGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound := by
  rcases h with ⟨cert⟩
  exact cert.toExternalGapCriterionWitness

theorem projectComputableGapCertificate_nonempty_to_publicInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) := by
  rcases h with ⟨cert⟩
  exact ⟨cert.toPublicCollisionInstantiation⟩

theorem projectComputableGapCertificate_nonempty_to_publicGapInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) := by
  rcases h with ⟨cert⟩
  exact ⟨cert.toPublicGapCollisionInstantiation⟩

theorem projectComputableGapCertificate_nonempty_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound)) :
    ¬ MainRationality := by
  rcases h with ⟨cert⟩
  exact cert.not_main_rationality

end BoundedProofPredicate
end BoundedArithmeticLab
