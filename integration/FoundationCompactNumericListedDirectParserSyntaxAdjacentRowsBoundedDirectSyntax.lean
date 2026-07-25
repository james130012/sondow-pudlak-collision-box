import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFinal
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Direct syntax for all bounded adjacent parser rows

The bounded universal keeps only its row index bound.  All seven public graph
parameters are closed binary numerals, so each branch is exactly the completed
open-index adjacent-row formula at valuation coordinate zero.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase

def compactParserSyntaxAdjacentRowsBoundedClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount rowCount tableWidth
      valueBound : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactParserSyntaxAdjacentRowsBoundedGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      shortBinaryNumeralTerm rowCount,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound]

def compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
    (tableWidth valueBound : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) expDef.val) ⇜
    ![shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm tableWidth]

def compactParserSyntaxAdjacentRowsBoundedUniversalBody
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (Rewriting.emb (ξ := Nat)
      compactParserSyntaxAdjacentRowBoundedDef.val) ⇜
    ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
      Rew.bShift (shortBinaryNumeralTerm width),
      Rew.bShift (shortBinaryNumeralTerm tokenCount),
      Rew.bShift (shortBinaryNumeralTerm stateBoundary),
      Rew.bShift (shortBinaryNumeralTerm stateCount),
      (#0 : ArithmeticSemiterm Nat 1),
      Rew.bShift (shortBinaryNumeralTerm valueBound)]

def compactParserSyntaxAdjacentRowsBoundedExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount rowCount tableWidth
      valueBound : Nat) : ValuationFormula :=
  compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
      tableWidth valueBound ⋏
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount valueBound).ballLT
        (shortBinaryNumeralTerm rowCount)

private theorem rewriting_ballLT
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1))
    (bound : ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ body.ballLT bound =
      (rewriting.q ▹ body).ballLT (rewriting bound) := by
  have rewriting_formulaOperator
      {operatorArity : Nat}
      (operator : Semiformula.Operator ℒₒᵣ operatorArity)
      (terms : Fin operatorArity ->
        ArithmeticSemiterm sourceVariables (sourceArity + 1)) :
      rewriting.q ▹ operator.operator terms =
        operator.operator (rewriting.q ∘ terms) := by
    unfold Semiformula.Operator.operator
    exact
      FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.rewriting_embeddedFormulaSubstitution
        rewriting.q operator.sentence terms
  have hguardTerms :
      rewriting.q ∘
          ![(#0 : ArithmeticSemiterm sourceVariables (sourceArity + 1)),
            Rew.bShift bound] =
        ![(#0 : ArithmeticSemiterm targetVariables (targetArity + 1)),
          Rew.bShift (rewriting bound)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => exact Rew.q_bvar_zero rewriting
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Rew.q_comp_bShift_app rewriting bound
        | succ coordinate => exact Fin.elim0 coordinate
  unfold Semiformula.ballLT
  rw [Rewriting.smul_ball,
    rewriting_formulaOperator,
    hguardTerms]

theorem compactParserSyntaxAdjacentRowsBoundedClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount rowCount tableWidth
      valueBound : Nat) :
    compactParserSyntaxAdjacentRowsBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount rowCount tableWidth valueBound =
      compactParserSyntaxAdjacentRowsBoundedExplicitFormula tokenTable width
        tokenCount stateBoundary stateCount rowCount tableWidth valueBound := by
  unfold compactParserSyntaxAdjacentRowsBoundedClosedFormula
  unfold compactParserSyntaxAdjacentRowsBoundedExplicitFormula
  unfold compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
  unfold compactParserSyntaxAdjacentRowsBoundedUniversalBody
  unfold compactParserSyntaxAdjacentRowsBoundedGraphDef
  simp [rewriting_ballLT,
    FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

theorem compactParserSyntaxAdjacentRowsBoundedUniversalBody_free_alignment
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat) :
    Rewriting.free
        (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
          tokenCount stateBoundary stateCount valueBound) =
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula tokenTable
        width tokenCount stateBoundary stateCount valueBound
          (&0 : ValuationTerm) := by
  unfold compactParserSyntaxAdjacentRowsBoundedUniversalBody
  rw [
    FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.rewriting_embeddedFormulaSubstitution]
  unfold compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_def,
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTerms]

theorem
    compactParserSyntaxAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat) :
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount valueBound).freeVariables = ∅ := by
  unfold compactParserSyntaxAdjacentRowsBoundedUniversalBody
  apply
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate
  all_goals
    first
    | exact bShift_freeVariables_eq_empty_of_empty _
        (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    | simp

#print axioms compactParserSyntaxAdjacentRowsBoundedClosedFormula_alignment
#print axioms compactParserSyntaxAdjacentRowsBoundedUniversalBody_free_alignment
#print axioms
  compactParserSyntaxAdjacentRowsBoundedUniversalBody_freeVariables_eq_empty

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
