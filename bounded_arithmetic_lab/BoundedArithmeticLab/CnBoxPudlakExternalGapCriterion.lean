/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakSondowBridge

/-!
# Certificate-backed external gap criterion

This module makes the external gap test project-level and certificate-backed.
The criterion is not an arbitrary numeric predicate: it packages the same
canonical CnBox target, the same proof-length notion, a Sondow-to-canonical
acceptance certificate, and the relabeled Pudlak lower route.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure ProjectLevelCnBoxCertificateBackedGapCriterion
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bound : Nat → Real) where
  bound_poly : IsPolynomialBound bound
  sondow_eventual_accepted :
    MainAcceptedEventuallyUnderRationality
      MainRationality SondowAccepted
  accepted_to_certificate :
    AcceptedToCanonicalProofCertificateTransport SondowAccepted bound
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

def HasProjectLevelCnBoxCertificateBackedGapCriterion
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bound : Nat → Real) : Prop :=
  Nonempty
    (ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound)

namespace ProjectLevelCnBoxCertificateBackedGapCriterion

def toProofCertificateTransportChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    ProjectLevelCnBoxProofCertificateTransportChecklist
      MainRationality SondowAccepted bound where
  bound_poly := criterion.bound_poly
  sondow_eventual_accepted := criterion.sondow_eventual_accepted
  accepted_to_certificate := criterion.accepted_to_certificate
  lower_source := criterion.lower_source
  relabeling := criterion.relabeling
  length_eq := criterion.length_eq

def ofProofCertificateTransportChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxProofCertificateTransportChecklist
        MainRationality SondowAccepted bound) :
    ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound where
  bound_poly := checklist.bound_poly
  sondow_eventual_accepted := checklist.sondow_eventual_accepted
  accepted_to_certificate := checklist.accepted_to_certificate
  lower_source := checklist.lower_source
  relabeling := checklist.relabeling
  length_eq := checklist.length_eq

theorem hasCriterion_iff_hasProofCertificateTransportChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real} :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound ↔
      Nonempty
        (ProjectLevelCnBoxProofCertificateTransportChecklist
          MainRationality SondowAccepted bound) := by
  constructor
  · intro h
    rcases h with ⟨criterion⟩
    exact ⟨criterion.toProofCertificateTransportChecklist⟩
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨ofProofCertificateTransportChecklist checklist⟩

theorem target_eq_finiteConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (_criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n = finiteConsistencyFormula n :=
  canonicalPudlakTarget_target_eq_finiteConsistency n

theorem code_eq_partialConsistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (_criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        partialConsistencyCode n :=
  canonicalPudlakTarget_code_eq_partialConsistency n

theorem lowerLength_eq_canonicalLength
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (n : Nat) :
    criterion.lower_source.pa_length n =
      canonicalPudlakTargetFamilySpec.length n := by
  rw [criterion.length_eq n]
  rw [canonicalPudlakTarget_length_eq_semanticFiniteConsistency n]

def toRelabeledCalibration
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    CanonicalRelabeledPudlakCalibration criterion.lower_source where
  relabeling := criterion.relabeling
  length_eq := criterion.length_eq

noncomputable def lowerBound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    EventualLowerBound canonicalCnBoxPABox := by
  simpa [canonicalCnBoxPABox]
    using criterion.toRelabeledCalibration.toConcretePALowerBound

noncomputable def proofLengthGap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    CanonicalCnBoxProofLengthGap :=
  criterion.toRelabeledCalibration.toProofLengthGap

noncomputable def witnessAgainstDeclaredBound
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (N : Nat) :
    HasProofLengthGapWitness canonicalCnBoxPABox bound N :=
  criterion.proofLengthGap bound criterion.bound_poly N

noncomputable def canonicalAcceptance
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    MainAcceptedEventuallyUnderRationality
      MainRationality (CanonicalProofCertificateAccepted bound) :=
  mainAcceptedEventually_toCanonicalProofCertificate
    criterion.accepted_to_certificate criterion.sondow_eventual_accepted

noncomputable def toProofCertificateChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    CanonicalCnBoxProofCertificateChecklist bound :=
  criterion.toProofCertificateTransportChecklist.toProofCertificateChecklist
    hmain

noncomputable def toExternalObligationChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    CanonicalCnBoxExternalObligationChecklist
      (CanonicalProofCertificateAccepted bound) :=
  (criterion.toProofCertificateChecklist hmain).toExternalChecklist

noncomputable def toGapInputs
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound)
    (hmain : MainRationality) :
    CanonicalCnBoxGapCollisionInputs
      (CanonicalProofCertificateAccepted bound) :=
  (criterion.toExternalObligationChecklist hmain).toCompilerInputs.toGapInputs

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bound : Nat → Real}
    (criterion :
      ProjectLevelCnBoxCertificateBackedGapCriterion
        MainRationality SondowAccepted bound) :
    ¬ MainRationality :=
  criterion.toProofCertificateTransportChecklist.not_main_rationality

end ProjectLevelCnBoxCertificateBackedGapCriterion

namespace ProjectLevelCnBoxSondowCompiledChecklist

noncomputable def toCertificateBackedGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowCompiledChecklist
        MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound where
  bound_poly := checklist.bound_poly
  sondow_eventual_accepted := checklist.sondow_eventual_accepted
  accepted_to_certificate :=
    AcceptedToCompiledProjectSourceCertificateCompiler.toCanonicalProofCertificateTransport
      checklist.accepted_to_compiled_source checklist.canonical_assembler
  lower_source := checklist.lower_source
  relabeling := checklist.relabeling
  length_eq := checklist.length_eq

theorem not_main_rationality_viaCertificateBackedGap
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowCompiledChecklist
        MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.toCertificateBackedGapCriterion.not_main_rationality

end ProjectLevelCnBoxSondowCompiledChecklist

end BoundedProofPredicate
end BoundedArithmeticLab
