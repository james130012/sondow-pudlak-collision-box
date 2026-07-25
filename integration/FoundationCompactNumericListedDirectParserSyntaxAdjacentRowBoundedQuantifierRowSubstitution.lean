import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitutionComponents

/-! # Public-parameter substitution for the adjacent-row graph component -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierRowSubstitution

open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitutionComponents

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

theorem compactParserSyntaxAdjacentRowSourceRowFormula_rewriting
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat) :
    sourceSubstitutionQpow
        (compactParserSyntaxAdjacentRowBoundedSourceTerms tokenTable width
          tokenCount stateBoundary stateCount index valueBound) 27 ▹
      compactParserSyntaxAdjacentRowSourceRowFormula =
    compactParserSyntaxAdjacentRowRawRowFormula tokenTable width tokenCount
      stateBoundary stateCount index := by
  unfold compactParserSyntaxAdjacentRowSourceRowFormula
  unfold compactParserSyntaxAdjacentRowRawRowFormula
  simp [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply,
      compactParserSyntaxAdjacentRowBoundedSourceTerms]
  all_goals
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]

#print axioms compactParserSyntaxAdjacentRowSourceRowFormula_rewriting

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierRowSubstitution
