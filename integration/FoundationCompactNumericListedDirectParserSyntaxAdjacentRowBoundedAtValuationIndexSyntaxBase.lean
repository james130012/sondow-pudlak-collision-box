import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntax
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedCheckedData
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Base syntax for a bounded adjacent row at an open index -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitutionComponents

theorem rewriting_embeddedFormulaSubstitution
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

def compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTerms
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) : Fin 7 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    indexTerm,
    shortBinaryNumeralTerm valueBound]

@[irreducible] def compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactParserSyntaxAdjacentRowBoundedDef.val) ⇜
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTerms tokenTable
      width tokenCount stateBoundary stateCount valueBound indexTerm

@[irreducible] def
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawRowFormula
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm) : ArithmeticSemiformula Nat 27 :=
  (Rewriting.emb (ξ := Nat)
      compactParserSyntaxAdjacentStepRowDef.val) ⇜
    ![sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenTable),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm width),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm tokenCount),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm stateBoundary),
      sourceSubstitutionLift 27 (shortBinaryNumeralTerm stateCount),
      sourceSubstitutionLift 27 indexTerm,
      (#26 : ArithmeticSemiterm Nat 27), #25, #24, #23, #22, #21, #20,
      #19, #18, #17, #16, #15, #14, #13, #12, #11, #10, #9, #8, #7,
      #6, #5, #4, #3, #2, #1, #0]

@[irreducible] def
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) : ArithmeticSemiformula Nat 27 :=
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawRowFormula tokenTable
      width tokenCount stateBoundary stateCount indexTerm ⋏
    (compactParserSyntaxAdjacentRowRawCurrentStatusFormula tokenTable width
        tokenCount valueBound ⋏
      compactParserSyntaxAdjacentRowRawNextStatusFormula tokenTable width
        tokenCount valueBound)

theorem substitute_sourceSubstitutionLift
    {depth : Nat} (values : Fin (0 + depth) -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift depth term) = term := by
  induction depth with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) = Rew.id := by
        apply Rew.ext
        · intro index
          exact Fin.elim0 index
        · intro freeIndex
          rfl
      rw [hrew]
      exact Rew.id_app term
  | succ depth inductionHypothesis =>
      have hrew :
          (Rew.subst values).comp Rew.bShift =
            Rew.subst (fun index : Fin (0 + depth) => values index.succ) := by
        apply Rew.ext
        · intro index
          simp [Rew.comp_app]
        · intro freeIndex
          simp [Rew.comp_app]
      calc
        Rew.subst values (sourceSubstitutionLift (depth + 1) term) =
            ((Rew.subst values).comp Rew.bShift)
              (sourceSubstitutionLift depth term) := by
                simp [sourceSubstitutionLift, Rew.comp_app]
        _ = Rew.subst (fun index : Fin (0 + depth) => values index.succ)
              (sourceSubstitutionLift depth term) := by rw [hrew]
        _ = term := inductionHypothesis _

theorem substitute_sourceSubstitutionLift27
    (values : Fin 27 -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (sourceSubstitutionLift 27 term) = term := by
  simpa only using
    (substitute_sourceSubstitutionLift (depth := 27) values term)

#print axioms rewriting_embeddedFormulaSubstitution
#print axioms substitute_sourceSubstitutionLift27

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
