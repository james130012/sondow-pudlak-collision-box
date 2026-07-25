import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexSyntaxBase

/-! # Next-row coordinate alignment for an open adjacent-step index -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexNextAlignment

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexSyntaxBase

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

theorem compactParserSyntaxAdjacentStepNextAtValuationIndex_alignment
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactParserSyntaxAdjacentStepRow) :
    (Rew.subst
      (compactParserSyntaxAdjacentStepAtValuationIndexTerms tokenTable width
        tokenCount stateBoundary stateCount indexTerm row)) ▹
        compactParserSyntaxAdjacentStepSourceNextFormula =
      compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
        tokenCount stateBoundary stateCount (‘!!indexTerm + 1’ : ValuationTerm)
          row.nextCoordinates row.nextSize := by
  unfold compactParserSyntaxAdjacentStepSourceNextFormula
  unfold compactUnifiedParserStateAtRowsAtValuationIndexFormula
  rw [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply,
      compactParserSyntaxAdjacentStepAtValuationIndexTerms, Rew.subst_bvar]

#print axioms
  compactParserSyntaxAdjacentStepNextAtValuationIndex_alignment

end FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexNextAlignment
