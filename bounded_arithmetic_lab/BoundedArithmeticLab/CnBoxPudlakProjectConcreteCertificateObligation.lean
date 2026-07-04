/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectComputableReleaseSurface

/-!
# Project concrete certificate obligation

This module exposes the concrete project certificate obligations field by
field.  The obligation is proved equivalent to the existing project public
collision certificate bundle, so the audit-facing decomposition does not
weaken the project instantiation route.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure ProjectConcreteCertificateObligation
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  bound_poly : IsPolynomialBound bound
  sondow_eventual_accepted :
    MainAcceptedEventuallyUnderRationality
      MainRationality SondowAccepted
  accepted_to_compiled_source :
    AcceptedToCompiledProjectSourceCertificateCompiler
      SondowAccepted bounds
  canonical_budgeted_assembly :
    SondowProjectCanonicalBudgetedAssemblyProvider bounds bound
  lower_source : BussPudlakTheorem5PALowerBoundSource
  relabeling :
    SemanticFormulaRelabeling lower_source.box.formula
      (concretePAFormalization
        canonicalPudlakTargetFamilySpec.target
        canonicalPudlakTargetFamilySpec.code).box.formula
  length_eq :
    ∀ n : Nat,
      lower_source.pa_length n =
        semanticBAProofLength PAAxiom finiteConsistencyFormula n

namespace ProjectConcreteCertificateObligation

def ofCertificateBundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound where
  bound_poly := bundle.bound_poly
  sondow_eventual_accepted := bundle.sondow_eventual_accepted
  accepted_to_compiled_source := bundle.accepted_to_compiled_source
  canonical_budgeted_assembly := bundle.canonical_budgeted_assembly
  lower_source := bundle.lower_source
  relabeling := bundle.relabeling
  length_eq := bundle.length_eq

def toCertificateBundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (obligation : ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound) :
    ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound where
  bound_poly := obligation.bound_poly
  sondow_eventual_accepted := obligation.sondow_eventual_accepted
  accepted_to_compiled_source := obligation.accepted_to_compiled_source
  canonical_budgeted_assembly := obligation.canonical_budgeted_assembly
  lower_source := obligation.lower_source
  relabeling := obligation.relabeling
  length_eq := obligation.length_eq

def toComputableGapCertificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (obligation : ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound) :
    ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound :=
  ProjectComputableGapCertificate.ofCertificateBundle
    obligation.toCertificateBundle

theorem length_eq_semanticFiniteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (obligation : ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    obligation.lower_source.pa_length n =
      semanticBAProofLength PAAxiom finiteConsistencyFormula n :=
  obligation.length_eq n

theorem target_eq_finiteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (obligation : ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n = finiteConsistencyFormula n :=
  obligation.toComputableGapCertificate.target_eq_finiteConsistency n

theorem code_eq_partialConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (obligation : ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        partialConsistencyCode n :=
  obligation.toComputableGapCertificate.code_eq_partialConsistency n

noncomputable def toCertificateBackedGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (obligation : ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  obligation.toComputableGapCertificate.toCertificateBackedGapCriterion

noncomputable def witnessAgainstDeclaredBound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (obligation : ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)
    (N : Nat) :
    HasProofLengthGapWitness canonicalCnBoxPABox bound N :=
  obligation.toComputableGapCertificate.witnessAgainstDeclaredBound N

end ProjectConcreteCertificateObligation

theorem projectConcreteCertificateObligation_nonempty_iff_bundle_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨obligation⟩
    exact ⟨obligation.toCertificateBundle⟩
  · intro h
    rcases h with ⟨bundle⟩
    exact ⟨ProjectConcreteCertificateObligation.ofCertificateBundle bundle⟩

theorem
    projectConcreteCertificateObligation_nonempty_iff_computableGapCertificate_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound) := by
  exact projectConcreteCertificateObligation_nonempty_iff_bundle_nonempty.trans
    projectComputableGapCertificate_nonempty_iff_bundle_nonempty.symm

theorem projectConcreteCertificateObligation_nonempty_iff_completionObligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound) ↔
      ProjectPublicCollisionCompletionObligation
        MainRationality SondowAccepted bounds bound := by
  exact projectConcreteCertificateObligation_nonempty_iff_bundle_nonempty.trans
    projectPublicCollisionCompletionObligation_iff_bundle_nonempty.symm

theorem
    projectConcreteCertificateObligation_nonempty_iff_verifiedInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakVerifiedProjectInstantiationChecklist
        MainRationality SondowAccepted bounds bound) := by
  exact projectConcreteCertificateObligation_nonempty_iff_bundle_nonempty.trans
    projectPublicCollisionCertificateBundle_nonempty_iff_verifiedInstantiation_nonempty

theorem projectConcreteCertificateObligation_nonempty_to_externalGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound := by
  rcases h with ⟨obligation⟩
  exact obligation.toCertificateBundle.toExternalGapCriterionWitness

theorem projectConcreteCertificateObligation_nonempty_to_publicInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) := by
  rcases h with ⟨obligation⟩
  exact ⟨obligation.toCertificateBundle.toPublicCollisionInstantiation⟩

theorem projectConcreteCertificateObligation_nonempty_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound)) :
    ¬ MainRationality := by
  rcases h with ⟨obligation⟩
  exact obligation.toCertificateBundle.not_main_rationality

end BoundedProofPredicate
end BoundedArithmeticLab
