/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectConcreteReleaseSurface

/-!
# Project concrete certificate field index

This module gives audit-facing names for the primitive fields of the concrete
project certificate obligation and for the downstream projections generated
from those fields.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure ProjectConcreteCertificateFieldIndex
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  obligation : ProjectConcreteCertificateObligation
    MainRationality SondowAccepted bounds bound

namespace ProjectConcreteCertificateFieldIndex

def ofConcreteObligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (obligation : ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound) :
    ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound where
  obligation := obligation

def toConcreteObligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    ProjectConcreteCertificateObligation
      MainRationality SondowAccepted bounds bound :=
  index.obligation

def toCertificateBundle
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound :=
  index.obligation.toCertificateBundle

def toComputableGapCertificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound :=
  index.obligation.toComputableGapCertificate

theorem bound_polynomial
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    IsPolynomialBound bound :=
  index.obligation.bound_poly

theorem sondow_eventual_accepted
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    MainAcceptedEventuallyUnderRationality
      MainRationality SondowAccepted :=
  index.obligation.sondow_eventual_accepted

def accepted_to_compiled_source
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    AcceptedToCompiledProjectSourceCertificateCompiler
      SondowAccepted bounds :=
  index.obligation.accepted_to_compiled_source

def canonical_budgeted_assembly
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    SondowProjectCanonicalBudgetedAssemblyProvider bounds bound :=
  index.obligation.canonical_budgeted_assembly

def lower_source
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    BussPudlakTheorem5PALowerBoundSource :=
  index.obligation.lower_source

def relabeling
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    SemanticFormulaRelabeling index.lower_source.box.formula
      (concretePAFormalization
        canonicalPudlakTargetFamilySpec.target
        canonicalPudlakTargetFamilySpec.code).box.formula :=
  index.obligation.relabeling

theorem length_eq_semanticFiniteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    index.lower_source.pa_length n =
      semanticBAProofLength PAAxiom finiteConsistencyFormula n :=
  index.obligation.length_eq n

noncomputable def toBudgetedAssemblyChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
      MainRationality SondowAccepted bounds bound :=
  index.toCertificateBundle.toAssemblyChecklist

noncomputable def toProofCertificateTransportChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxProofCertificateTransportChecklist
      MainRationality SondowAccepted bound :=
  index.toComputableGapCertificate.toCertificateBackedGapCriterion
    |>.toProofCertificateTransportChecklist

noncomputable def accepted_to_canonical_certificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    AcceptedToCanonicalProofCertificateTransport SondowAccepted bound :=
  index.toProofCertificateTransportChecklist.accepted_to_certificate

noncomputable def toExternalGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  index.toComputableGapCertificate.toCertificateBackedGapCriterion

noncomputable def witnessAgainstDeclaredBound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (N : Nat) :
    HasProofLengthGapWitness canonicalCnBoxPABox bound N :=
  index.obligation.witnessAgainstDeclaredBound N

theorem target_eq_finiteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n = finiteConsistencyFormula n :=
  index.obligation.target_eq_finiteConsistency n

theorem code_eq_partialConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (index : ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        partialConsistencyCode n :=
  index.obligation.code_eq_partialConsistency n

end ProjectConcreteCertificateFieldIndex

abbrev ProjectConcreteCertificateExactObligation
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) : Prop :=
  Nonempty (ProjectConcreteCertificateFieldIndex
    MainRationality SondowAccepted bounds bound)

theorem projectConcreteCertificateFieldIndex_nonempty_iff_concreteObligation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectConcreteCertificateFieldIndex
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectConcreteCertificateObligation
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨index⟩
    exact ⟨index.toConcreteObligation⟩
  · intro h
    rcases h with ⟨obligation⟩
    exact ⟨ProjectConcreteCertificateFieldIndex.ofConcreteObligation
      obligation⟩

theorem projectConcreteCertificateExactObligation_iff_bundle_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    ProjectConcreteCertificateExactObligation
      MainRationality SondowAccepted bounds bound ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) := by
  exact projectConcreteCertificateFieldIndex_nonempty_iff_concreteObligation_nonempty.trans
    projectConcreteCertificateObligation_nonempty_iff_bundle_nonempty

theorem projectConcreteCertificateExactObligation_iff_completionObligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    ProjectConcreteCertificateExactObligation
      MainRationality SondowAccepted bounds bound ↔
      ProjectPublicCollisionCompletionObligation
        MainRationality SondowAccepted bounds bound := by
  exact projectConcreteCertificateFieldIndex_nonempty_iff_concreteObligation_nonempty.trans
    projectConcreteCertificateObligation_nonempty_iff_completionObligation

theorem projectConcreteCertificateExactObligation_iff_computableGapCertificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    ProjectConcreteCertificateExactObligation
      MainRationality SondowAccepted bounds bound ↔
      Nonempty (ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound) := by
  exact projectConcreteCertificateFieldIndex_nonempty_iff_concreteObligation_nonempty.trans
    projectConcreteCertificateObligation_nonempty_iff_computableGapCertificate_nonempty

end BoundedProofPredicate
end BoundedArithmeticLab
