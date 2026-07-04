/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakAssemblyBridge

/-!
# Budgeted assembly bridge

This module refines the assembly bridge by separating the assembled proof size
budget from the assembled proof itself.  The final arithmetic obligation is
now an explicit `assembledSize + 2 <= bound` certificate.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

structure SondowProjectCanonicalAssemblyBudget
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  assembledSize :
    ∀ n : Nat, CompiledSondowProjectSourceCertificateAt bounds n → Nat
  size_plus_two_le_bound :
    ∀ n : Nat, ∀ source : CompiledSondowProjectSourceCertificateAt bounds n,
      (((assembledSize n source + 2 : Nat) : Real)) ≤ bound n

structure SondowProjectCanonicalBudgetedAssemblyFor
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (budget : SondowProjectCanonicalAssemblyBudget bounds bound)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n)
    where
  assembledProof : BAProofObject BussS21Axiom
  proof_conclusion :
    assembledProof.conclusion = canonicalPudlakTargetFamilySpec.target n
  proof_size_eq_budget : assembledProof.size = budget.assembledSize n source

def SondowProjectCanonicalBudgetedAssemblyFor.toAssemblyFor
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {budget : SondowProjectCanonicalAssemblyBudget bounds bound}
    {n : Nat} {source : CompiledSondowProjectSourceCertificateAt bounds n}
    (assembly : SondowProjectCanonicalBudgetedAssemblyFor budget source) :
    SondowProjectCanonicalAssemblyFor bound source where
  assembledProof := assembly.assembledProof
  proof_conclusion := assembly.proof_conclusion
  proof_size_plus_two_le := by
    rw [assembly.proof_size_eq_budget]
    exact budget.size_plus_two_le_bound n source

structure SondowProjectCanonicalBudgetedAssemblyProvider
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  budget : SondowProjectCanonicalAssemblyBudget bounds bound
  assembly :
    ∀ n : Nat, ∀ source : CompiledSondowProjectSourceCertificateAt bounds n,
      SondowProjectCanonicalBudgetedAssemblyFor budget source

def SondowProjectCanonicalBudgetedAssemblyProvider.toAssemblyProvider
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (provider :
      SondowProjectCanonicalBudgetedAssemblyProvider bounds bound) :
    SondowProjectCanonicalAssemblyProvider bounds bound where
  assembly := by
    intro n source
    exact (provider.assembly n source).toAssemblyFor

def SondowProjectCanonicalBudgetedAssemblyProvider.ofAssemblyProvider
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (provider : SondowProjectCanonicalAssemblyProvider bounds bound) :
    SondowProjectCanonicalBudgetedAssemblyProvider bounds bound where
  budget := {
    assembledSize := fun n source =>
      (provider.assembly n source).assembledProof.size
    size_plus_two_le_bound := by
      intro n source
      exact (provider.assembly n source).proof_size_plus_two_le }
  assembly := by
    intro n source
    exact {
      assembledProof := (provider.assembly n source).assembledProof
      proof_conclusion := (provider.assembly n source).proof_conclusion
      proof_size_eq_budget := rfl }

theorem budgetedAssemblyProvider_nonempty_iff_assemblyProvider_nonempty
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (SondowProjectCanonicalBudgetedAssemblyProvider bounds bound) ↔
      Nonempty (SondowProjectCanonicalAssemblyProvider bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨provider⟩
    exact ⟨provider.toAssemblyProvider⟩
  · intro h
    rcases h with ⟨provider⟩
    exact ⟨SondowProjectCanonicalBudgetedAssemblyProvider.ofAssemblyProvider
      provider⟩

structure ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
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

namespace ProjectLevelCnBoxSondowBudgetedAssemblyChecklist

noncomputable def toAssemblyChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxSondowAssemblyChecklist
      MainRationality SondowAccepted bounds bound where
  bound_poly := checklist.bound_poly
  sondow_eventual_accepted := checklist.sondow_eventual_accepted
  accepted_to_compiled_source := checklist.accepted_to_compiled_source
  canonical_assembly :=
    checklist.canonical_budgeted_assembly.toAssemblyProvider
  lower_source := checklist.lower_source
  relabeling := checklist.relabeling
  length_eq := checklist.length_eq

noncomputable def toCertificateBackedGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  checklist.toAssemblyChecklist.toCertificateBackedGapCriterion

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowBudgetedAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.toCertificateBackedGapCriterion.not_main_rationality

end ProjectLevelCnBoxSondowBudgetedAssemblyChecklist

end BoundedProofPredicate
end BoundedArithmeticLab
