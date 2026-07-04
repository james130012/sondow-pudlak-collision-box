/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakSameObjectReleaseSurface
import BoundedArithmeticLab.CnBoxPudlakProjectComputableReleaseSurface

/-!
# Project-level same-object bridge closure

This module packages the public collision route together with the canonical
same-object CnBox/Pudlak bridge.  Its main equivalences show that adding the
same-object bridge layer does not strengthen or weaken the project certificate
obligation: the closure is nonempty exactly when the existing computable gap
certificate, public certificate bundle, public checklist, and completion
obligation are nonempty.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure ProjectSameObjectBridgeClosure
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  computable_gap : ProjectComputableGapCertificate
    MainRationality SondowAccepted bounds bound
  same_object : CnBoxPudlakSameObjectBridge.Checklist
  project_checklist : CnBoxPudlakProjectPublicCollisionChecklist
    MainRationality SondowAccepted bounds bound
  completion : ProjectPublicCollisionCompletionObligation
    MainRationality SondowAccepted bounds bound

namespace ProjectSameObjectBridgeClosure

noncomputable def ofComputableGapCertificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (cert : ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound) :
    ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound where
  computable_gap := cert
  same_object := CnBoxPudlakSameObjectBridge.checklist
  project_checklist := cert.bundle.toProjectPublicCollisionChecklist
  completion := cert.toCompletionObligation

def toComputableGapCertificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :
    ProjectComputableGapCertificate
      MainRationality SondowAccepted bounds bound :=
  closure.computable_gap

def toSameObjectChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :
    CnBoxPudlakSameObjectBridge.Checklist :=
  closure.same_object

noncomputable def toProjectPublicCollisionChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :
    CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound :=
  closure.project_checklist

theorem target_eq_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (_closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n =
      (canonicalPudlakTargetFamilySpec.box n).formula :=
  CnBoxPudlakSameObjectBridge.target_eq_box_formula n

theorem code_eq_box_formulaCode
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (_closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        (canonicalPudlakTargetFamilySpec.box n).formulaCode :=
  CnBoxPudlakSameObjectBridge.code_eq_box_formulaCode n

theorem box_code_roundtrip_to_target
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (_closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    BAFormula.decode (canonicalPudlakTargetFamilySpec.box n).code =
      some (canonicalPudlakTargetFamilySpec.target n) :=
  CnBoxPudlakSameObjectBridge.box_code_roundtrip_to_target n

theorem carries_iff_pa_finite_consistency
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (_closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    CnBoxCarriesPAFiniteConsistency
      (canonicalPudlakTargetFamilySpec.box n) ↔
        PAFiniteConsistencyStatement n :=
  CnBoxPudlakSameObjectBridge.carries_iff_pa_finite_consistency n

theorem length_eq_semantic_box_formula
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (_closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)
    (n : Nat) :
    canonicalPudlakTargetFamilySpec.length n =
      semanticBAProofLength PAAxiom
        (fun k => (canonicalPudlakTargetFamilySpec.box k).formula) n :=
  CnBoxPudlakSameObjectBridge.length_eq_semantic_box_formula n

noncomputable def toExternalGapCriterionWitness
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  closure.computable_gap.toExternalGapCriterionWitness

noncomputable def toPublicCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :
    PublicCollisionInstantiation MainRationality :=
  closure.computable_gap.toPublicCollisionInstantiation

noncomputable def toPublicGapCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :
    PublicGapCollisionInstantiation MainRationality :=
  closure.computable_gap.toPublicGapCollisionInstantiation

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (closure : ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  closure.computable_gap.not_main_rationality

end ProjectSameObjectBridgeClosure

theorem projectSameObjectBridgeClosure_nonempty_iff_computableGapCertificate
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectComputableGapCertificate
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨closure⟩
    exact ⟨closure.toComputableGapCertificate⟩
  · intro h
    rcases h with ⟨cert⟩
    exact ⟨ProjectSameObjectBridgeClosure.ofComputableGapCertificate cert⟩

theorem projectSameObjectBridgeClosure_nonempty_iff_bundle_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectPublicCollisionCertificateBundle
        MainRationality SondowAccepted bounds bound) := by
  exact projectSameObjectBridgeClosure_nonempty_iff_computableGapCertificate.trans
    projectComputableGapCertificate_nonempty_iff_bundle_nonempty

theorem projectSameObjectBridgeClosure_nonempty_iff_completionObligation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) ↔
      ProjectPublicCollisionCompletionObligation
        MainRationality SondowAccepted bounds bound := by
  exact projectSameObjectBridgeClosure_nonempty_iff_computableGapCertificate.trans
    projectComputableGapCertificate_nonempty_iff_completionObligation

theorem projectSameObjectBridgeClosure_nonempty_iff_projectChecklist_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
        MainRationality SondowAccepted bounds bound) := by
  exact projectSameObjectBridgeClosure_nonempty_iff_computableGapCertificate.trans
    projectComputableGapCertificate_nonempty_iff_projectChecklist_nonempty

theorem projectSameObjectBridgeClosure_nonempty_to_externalGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound := by
  rcases h with ⟨closure⟩
  exact closure.toExternalGapCriterionWitness

theorem projectSameObjectBridgeClosure_nonempty_to_publicInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) := by
  rcases h with ⟨closure⟩
  exact ⟨closure.toPublicCollisionInstantiation⟩

theorem projectSameObjectBridgeClosure_nonempty_to_publicGapInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) := by
  rcases h with ⟨closure⟩
  exact ⟨closure.toPublicGapCollisionInstantiation⟩

theorem projectSameObjectBridgeClosure_nonempty_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectSameObjectBridgeClosure
      MainRationality SondowAccepted bounds bound)) :
    ¬ MainRationality := by
  rcases h with ⟨closure⟩
  exact closure.not_main_rationality

end BoundedProofPredicate
end BoundedArithmeticLab
