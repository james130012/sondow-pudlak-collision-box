import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectStructuralCompiler
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Direct syntax for all bounded sequent-formula step rows

The original ten-coordinate graph is split into its closed exponential leaf
and a numeral-bounded universal.  The universal body keeps only the row index
as a bound variable; all remaining public graph coordinates are closed binary
numerals.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula

def compactSequentFormulaStepRowsBoundedDirectClosedFormula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount tableWidth valueBound : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactSequentFormulaStepRowsBoundedGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm suffixBoundary,
      shortBinaryNumeralTerm suffixCount,
      shortBinaryNumeralTerm valueBoundary,
      shortBinaryNumeralTerm valueCount,
      shortBinaryNumeralTerm rowCount,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound]

def compactSequentFormulaStepRowsBoundedExponentialClosedFormula
    (tableWidth valueBound : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) expDef.val) ⇜
    ![shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm tableWidth]

def compactSequentFormulaStepRowsBoundedUniversalBody
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (Rewriting.emb (ξ := Nat)
      compactSequentFormulaStepRowBoundedDef.val) ⇜
    ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
      Rew.bShift (shortBinaryNumeralTerm width),
      Rew.bShift (shortBinaryNumeralTerm tokenCount),
      Rew.bShift (shortBinaryNumeralTerm suffixBoundary),
      Rew.bShift (shortBinaryNumeralTerm suffixCount),
      Rew.bShift (shortBinaryNumeralTerm valueBoundary),
      Rew.bShift (shortBinaryNumeralTerm valueCount),
      (#0 : ArithmeticSemiterm Nat 1),
      Rew.bShift (shortBinaryNumeralTerm valueBound)]

def compactSequentFormulaStepRowBoundedAtValuationIndexFormula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound : Nat)
    (indexTerm : ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactSequentFormulaStepRowBoundedDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm suffixBoundary,
      shortBinaryNumeralTerm suffixCount,
      shortBinaryNumeralTerm valueBoundary,
      shortBinaryNumeralTerm valueCount,
      indexTerm,
      shortBinaryNumeralTerm valueBound]

def compactSequentFormulaStepRowsBoundedExplicitFormula
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount tableWidth valueBound : Nat) : ValuationFormula :=
  compactSequentFormulaStepRowsBoundedExponentialClosedFormula
      tableWidth valueBound ⋏
    (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      valueBound).ballLT
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

theorem compactSequentFormulaStepRowsBoundedDirectClosedFormula_alignment
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount tableWidth valueBound : Nat) :
    compactSequentFormulaStepRowsBoundedDirectClosedFormula tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowCount
        tableWidth valueBound =
      compactSequentFormulaStepRowsBoundedExplicitFormula tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowCount
        tableWidth valueBound := by
  unfold compactSequentFormulaStepRowsBoundedDirectClosedFormula
    compactSequentFormulaStepRowsBoundedExplicitFormula
    compactSequentFormulaStepRowsBoundedExponentialClosedFormula
    compactSequentFormulaStepRowsBoundedUniversalBody
    compactSequentFormulaStepRowsBoundedGraphDef
  simp [rewriting_ballLT, ← TransitiveRewriting.comp_app]
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

theorem
    compactSequentFormulaStepRowsBoundedUniversalBody_free_alignment
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound : Nat) :
    Rewriting.free
        (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount
          valueBound) =
      compactSequentFormulaStepRowBoundedAtValuationIndexFormula tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        valueBound (&0 : ValuationTerm) := by
  unfold compactSequentFormulaStepRowsBoundedUniversalBody
    compactSequentFormulaStepRowBoundedAtValuationIndexFormula
  rw [
    FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase.rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp

theorem
    compactSequentFormulaStepRowsBoundedUniversalBody_freeVariables_eq_empty
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound : Nat) :
    (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      valueBound).freeVariables = ∅ := by
  unfold compactSequentFormulaStepRowsBoundedUniversalBody
  apply
    embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate
  all_goals
    first
    | exact bShift_freeVariables_eq_empty_of_empty _
        (shortBinaryNumeralTerm_freeVariables_eq_empty _)
    | simp

#print axioms
  compactSequentFormulaStepRowsBoundedDirectClosedFormula_alignment
#print axioms
  compactSequentFormulaStepRowsBoundedUniversalBody_free_alignment
#print axioms
  compactSequentFormulaStepRowsBoundedUniversalBody_freeVariables_eq_empty

end FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
