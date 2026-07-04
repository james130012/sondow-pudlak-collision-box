/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakProjectPublicCollision

/-!
# Project public collision certificate bundle

This module exposes a paper-facing certificate bundle for the project-level
public collision layer.  The bundle separates the primitive project
certificates from the public contradiction API while preserving the same
project instantiation route.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure ProjectPublicCollisionCertificateBundle
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

namespace ProjectPublicCollisionCertificateBundle

noncomputable def toAssemblyChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
      MainRationality SondowAccepted bounds bound where
  bound_poly := bundle.bound_poly
  sondow_eventual_accepted := bundle.sondow_eventual_accepted
  accepted_to_compiled_source := bundle.accepted_to_compiled_source
  canonical_budgeted_assembly := bundle.canonical_budgeted_assembly
  lower_source := bundle.lower_source
  relabeling := bundle.relabeling
  length_eq := bundle.length_eq

def ofAssemblyChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (assembly : ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
      MainRationality SondowAccepted bounds bound) :
    ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound where
  bound_poly := assembly.bound_poly
  sondow_eventual_accepted := assembly.sondow_eventual_accepted
  accepted_to_compiled_source := assembly.accepted_to_compiled_source
  canonical_budgeted_assembly := assembly.canonical_budgeted_assembly
  lower_source := assembly.lower_source
  relabeling := assembly.relabeling
  length_eq := assembly.length_eq

noncomputable def toProjectPublicCollisionChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound :=
  CnBoxPudlakProjectPublicCollisionChecklist.ofAssemblyChecklist
    bundle.toAssemblyChecklist

def ofProjectPublicCollisionChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist : CnBoxPudlakProjectPublicCollisionChecklist
      MainRationality SondowAccepted bounds bound) :
    ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound :=
  ofAssemblyChecklist checklist.toAssemblyChecklist

noncomputable def toVerifiedProjectInstantiationChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    CnBoxPudlakVerifiedProjectInstantiationChecklist
      MainRationality SondowAccepted bounds bound :=
  bundle.toProjectPublicCollisionChecklist.toVerifiedProjectInstantiationChecklist

noncomputable def toCertificateBackedGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  bundle.toProjectPublicCollisionChecklist.toCertificateBackedGapCriterion

noncomputable def toExternalGapCriterionWitness
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  ⟨bundle.toCertificateBackedGapCriterion⟩

noncomputable def toPublicCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    PublicCollisionInstantiation MainRationality :=
  bundle.toProjectPublicCollisionChecklist.toPublicCollisionInstantiation

noncomputable def toPublicSeparatedCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    PublicSeparatedCollisionInstantiation MainRationality :=
  bundle.toProjectPublicCollisionChecklist.toPublicSeparatedCollisionInstantiation

noncomputable def toPublicGapCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    PublicGapCollisionInstantiation MainRationality :=
  bundle.toProjectPublicCollisionChecklist.toPublicGapCollisionInstantiation

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  bundle.toProjectPublicCollisionChecklist.not_main_rationality

theorem public_collision_instantiation_coherent_with_project_checklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    bundle.toPublicCollisionInstantiation =
      bundle.toProjectPublicCollisionChecklist.toPublicCollisionInstantiation :=
  rfl

theorem public_separated_instantiation_coherent_with_project_checklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    bundle.toPublicSeparatedCollisionInstantiation =
      bundle.toProjectPublicCollisionChecklist.toPublicSeparatedCollisionInstantiation :=
  rfl

theorem public_gap_instantiation_coherent_with_project_checklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    bundle.toPublicGapCollisionInstantiation =
      bundle.toProjectPublicCollisionChecklist.toPublicGapCollisionInstantiation :=
  rfl

theorem public_collision_instantiation_coherent_with_gap_route
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    bundle.toPublicCollisionInstantiation =
      bundle.toCertificateBackedGapCriterion.toPublicCollisionInstantiation :=
  by
    let checklist := bundle.toProjectPublicCollisionChecklist
    exact checklist.public_collision_instantiation_coherent_with_gap_route

theorem public_separated_instantiation_coherent_with_gap_route
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    bundle.toPublicSeparatedCollisionInstantiation =
      bundle.toCertificateBackedGapCriterion.toPublicSeparatedCollisionInstantiation :=
  by
    let assembly := bundle.toAssemblyChecklist
    exact assembly.public_separated_instantiation_coherent_with_gap_criterion

theorem public_gap_instantiation_coherent_with_gap_route
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (bundle : ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) :
    bundle.toPublicGapCollisionInstantiation =
      bundle.toCertificateBackedGapCriterion.toPublicGapCollisionInstantiation :=
  by
    let checklist := bundle.toProjectPublicCollisionChecklist
    exact checklist.public_gap_instantiation_coherent_with_gap_route

end ProjectPublicCollisionCertificateBundle

theorem
    projectPublicCollisionCertificateBundle_nonempty_iff_assemblyChecklist_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨bundle⟩
    exact ⟨bundle.toAssemblyChecklist⟩
  · intro h
    rcases h with ⟨assembly⟩
    exact ⟨ProjectPublicCollisionCertificateBundle.ofAssemblyChecklist
      assembly⟩

theorem
    projectPublicCollisionCertificateBundle_nonempty_iff_projectChecklist_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakProjectPublicCollisionChecklist
        MainRationality SondowAccepted bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨bundle⟩
    exact ⟨bundle.toProjectPublicCollisionChecklist⟩
  · intro h
    rcases h with ⟨checklist⟩
    exact ⟨ProjectPublicCollisionCertificateBundle.ofProjectPublicCollisionChecklist
      checklist⟩

theorem
    projectPublicCollisionCertificateBundle_nonempty_iff_verifiedInstantiation_nonempty
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound) ↔
      Nonempty (CnBoxPudlakVerifiedProjectInstantiationChecklist
        MainRationality SondowAccepted bounds bound) := by
  exact projectPublicCollisionCertificateBundle_nonempty_iff_projectChecklist_nonempty.trans
    projectPublicCollisionChecklist_nonempty_iff_verifiedInstantiation_nonempty

theorem projectPublicCollisionCertificateBundle_nonempty_to_publicCollisionInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicCollisionInstantiation MainRationality) := by
  rcases h with ⟨bundle⟩
  exact ⟨bundle.toPublicCollisionInstantiation⟩

theorem projectPublicCollisionCertificateBundle_nonempty_to_externalGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound)) :
    HasProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound := by
  rcases h with ⟨bundle⟩
  exact bundle.toExternalGapCriterionWitness

theorem
    projectPublicCollisionCertificateBundle_nonempty_to_publicSeparatedInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicSeparatedCollisionInstantiation MainRationality) := by
  rcases h with ⟨bundle⟩
  exact ⟨bundle.toPublicSeparatedCollisionInstantiation⟩

theorem projectPublicCollisionCertificateBundle_nonempty_to_publicGapInstantiation
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound)) :
    Nonempty (PublicGapCollisionInstantiation MainRationality) := by
  rcases h with ⟨bundle⟩
  exact ⟨bundle.toPublicGapCollisionInstantiation⟩

theorem projectPublicCollisionCertificateBundle_nonempty_not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (h : Nonempty (ProjectPublicCollisionCertificateBundle
      MainRationality SondowAccepted bounds bound)) :
    ¬ MainRationality := by
  rcases h with ⟨bundle⟩
  exact bundle.not_main_rationality

end BoundedProofPredicate
end BoundedArithmeticLab
