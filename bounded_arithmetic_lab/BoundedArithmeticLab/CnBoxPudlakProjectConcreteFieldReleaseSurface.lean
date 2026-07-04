/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectConcreteFieldIndex

/-!
# Project concrete certificate field release surface

This module exposes stable names for the exact concrete certificate obligation
and for the primitive field projections used by the project instantiation
route.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace ProjectConcreteCertificateFieldReleaseSurface

theorem exact_obligation_iff_bundle_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    ProjectConcreteCertificateExactObligation
      MainRationality SondowAccepted bounds bound ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) :=
  projectConcreteCertificateExactObligation_iff_bundle_nonempty

theorem exact_obligation_iff_completion_obligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    ProjectConcreteCertificateExactObligation
      MainRationality SondowAccepted bounds bound ↔
      ProjectPublicCollisionCompletionObligation
        MainRationality SondowAccepted bounds bound :=
  projectConcreteCertificateExactObligation_iff_completionObligation

theorem exact_obligation_iff_computable_gap_certificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    ProjectConcreteCertificateExactObligation
      MainRationality SondowAccepted bounds bound ↔
      Nonempty (ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound) :=
  projectConcreteCertificateExactObligation_iff_computableGapCertificate

theorem field_bound_polynomial
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    IsPolynomialBound bound :=
  index.bound_polynomial

theorem field_sondow_eventual_accepted
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    MainAcceptedEventuallyUnderRationality
      MainRationality SondowAccepted :=
  index.sondow_eventual_accepted

def field_accepted_to_compiled_source
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    AcceptedToCompiledProjectSourceCertificateCompiler
      SondowAccepted bounds :=
  index.accepted_to_compiled_source

def field_canonical_budgeted_assembly
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    SondowProjectCanonicalBudgetedAssemblyProvider bounds bound :=
  index.canonical_budgeted_assembly

def field_lower_source
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    BussPudlakTheorem5PALowerBoundSource :=
  index.lower_source

def field_relabeling
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    SemanticFormulaRelabeling index.lower_source.box.formula
      (concretePAFormalization
        canonicalPudlakTargetFamilySpec.target
        canonicalPudlakTargetFamilySpec.code).box.formula :=
  index.relabeling

theorem field_length_eq_semanticFiniteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    index.lower_source.pa_length n =
      semanticBAProofLength PAAxiom finiteConsistencyFormula n :=
  index.length_eq_semanticFiniteConsistency n

theorem field_target_eq_finiteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n = finiteConsistencyFormula n :=
  index.target_eq_finiteConsistency n

theorem field_code_eq_partialConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        partialConsistencyCode n :=
  index.code_eq_partialConsistency n

noncomputable def field_accepted_to_canonical_certificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    AcceptedToCanonicalProofCertificateTransport SondowAccepted bound :=
  index.accepted_to_canonical_certificate

noncomputable def field_external_gap_criterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  index.toExternalGapCriterion

noncomputable def field_witness_against_declared_bound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (N : Nat) :
    HasProofLengthGapWitness canonicalCnBoxPABox bound N :=
  index.witnessAgainstDeclaredBound N

end ProjectConcreteCertificateFieldReleaseSurface
end BoundedProofPredicate
end BoundedArithmeticLab
