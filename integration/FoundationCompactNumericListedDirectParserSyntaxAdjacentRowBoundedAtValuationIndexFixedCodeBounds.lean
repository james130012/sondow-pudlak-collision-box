import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedFixedCodeBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase

/-! # Fixed raw-terminal code bound for an open adjacent-row index -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFixedCodeBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitutionComponents
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase

def compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) : Fin 7 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    indexTerm,
    shortBinaryNumeralTerm valueBound]

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

private theorem compactParserSyntaxAdjacentRowSourceRowFormula_rewriting_open
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) :
    sourceSubstitutionQpow
        (compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm) 27 ▹
      compactParserSyntaxAdjacentRowSourceRowFormula =
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawRowFormula
      tokenTable width tokenCount stateBoundary stateCount indexTerm := by
  unfold compactParserSyntaxAdjacentRowSourceRowFormula
  unfold compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawRowFormula
  simp [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply,
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms]
  all_goals
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]

private theorem
    compactParserSyntaxAdjacentRowSourceCurrentStatusFormula_rewriting_open
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) :
    sourceSubstitutionQpow
        (compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm) 27 ▹
      compactParserSyntaxAdjacentRowSourceCurrentStatusFormula =
    compactParserSyntaxAdjacentRowRawCurrentStatusFormula tokenTable width
      tokenCount valueBound := by
  unfold compactParserSyntaxAdjacentRowSourceCurrentStatusFormula
  unfold compactParserSyntaxAdjacentRowRawCurrentStatusFormula
  simp [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply,
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms]
  all_goals
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]

private theorem
    compactParserSyntaxAdjacentRowSourceNextStatusFormula_rewriting_open
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) :
    sourceSubstitutionQpow
        (compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm) 27 ▹
      compactParserSyntaxAdjacentRowSourceNextStatusFormula =
    compactParserSyntaxAdjacentRowRawNextStatusFormula tokenTable width
      tokenCount valueBound := by
  unfold compactParserSyntaxAdjacentRowSourceNextStatusFormula
  unfold compactParserSyntaxAdjacentRowRawNextStatusFormula
  simp [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply,
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms]
  all_goals
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]

theorem
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceRawTerminal_rewriting
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) :
    sourceSubstitutionQpow
        (compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm) 27 ▹
      compactParserSyntaxAdjacentRowBoundedSourceRawTerminal =
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal tokenTable
      width tokenCount stateBoundary stateCount valueBound indexTerm := by
  change sourceSubstitutionQpow
      (compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms
        tokenTable width tokenCount stateBoundary stateCount valueBound
          indexTerm) 27 ▹
      (compactParserSyntaxAdjacentRowSourceRowFormula ⋏
        (compactParserSyntaxAdjacentRowSourceCurrentStatusFormula ⋏
          compactParserSyntaxAdjacentRowSourceNextStatusFormula)) = _
  unfold compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal
  change
    (sourceSubstitutionQpow
        (compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm) 27 ▹
        compactParserSyntaxAdjacentRowSourceRowFormula) ⋏
      ((sourceSubstitutionQpow
          (compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms
            tokenTable width tokenCount stateBoundary stateCount valueBound
              indexTerm) 27 ▹
          compactParserSyntaxAdjacentRowSourceCurrentStatusFormula) ⋏
        (sourceSubstitutionQpow
          (compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms
            tokenTable width tokenCount stateBoundary stateCount valueBound
              indexTerm) 27 ▹
          compactParserSyntaxAdjacentRowSourceNextStatusFormula)) = _
  rw [compactParserSyntaxAdjacentRowSourceRowFormula_rewriting_open]
  rw [compactParserSyntaxAdjacentRowSourceCurrentStatusFormula_rewriting_open]
  rw [compactParserSyntaxAdjacentRowSourceNextStatusFormula_rewriting_open]

def compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTermCodeEnvelope
    (termCodeBound bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound + termCodeBound

def compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminalFixedCodeEnvelope
    (termCodeBound bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 27
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTermCodeEnvelope
      termCodeBound bitBound)
    (binaryFormulaCode
      compactParserSyntaxAdjacentRowBoundedSourceRawTerminal).length

theorem
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms_code_length_le
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) (termCodeBound bitBound : Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hstateBoundary : Nat.size stateBoundary <= bitBound)
    (hstateCount : Nat.size stateCount <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound) :
    forall coordinate,
      (binaryTermCode
        (compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm coordinate)).length <=
        compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTermCodeEnvelope
          termCodeBound bitBound := by
  intro coordinate
  fin_cases coordinate
  · exact (binaryNumeralTerm_code_length_le_envelope tokenTable bitBound
      htokenTable).trans (by
        unfold
          compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTermCodeEnvelope
        omega)
  · exact (binaryNumeralTerm_code_length_le_envelope width bitBound hwidth).trans
      (by
        unfold
          compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTermCodeEnvelope
        omega)
  · exact (binaryNumeralTerm_code_length_le_envelope tokenCount bitBound
      htokenCount).trans (by
        unfold
          compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTermCodeEnvelope
        omega)
  · exact (binaryNumeralTerm_code_length_le_envelope stateBoundary bitBound
      hstateBoundary).trans (by
        unfold
          compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTermCodeEnvelope
        omega)
  · exact (binaryNumeralTerm_code_length_le_envelope stateCount bitBound
      hstateCount).trans (by
        unfold
          compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTermCodeEnvelope
        omega)
  · exact hindexCode.trans (by
      unfold
        compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTermCodeEnvelope
      omega)
  · exact (binaryNumeralTerm_code_length_le_envelope valueBound bitBound
      hvalueBound).trans (by
        unfold
          compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTermCodeEnvelope
        omega)

theorem
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_code_length_le_fixed
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) (termCodeBound bitBound : Nat)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hstateBoundary : Nat.size stateBoundary <= bitBound)
    (hstateCount : Nat.size stateCount <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound) :
    (binaryFormulaCode
      (compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal
        tokenTable width tokenCount stateBoundary stateCount valueBound
          indexTerm)).length <=
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminalFixedCodeEnvelope
        termCodeBound bitBound := by
  rw [←
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceRawTerminal_rewriting
      tokenTable width tokenCount stateBoundary stateCount valueBound indexTerm]
  exact
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      27
      (compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTermCodeEnvelope
        termCodeBound bitBound)
      (binaryFormulaCode
        compactParserSyntaxAdjacentRowBoundedSourceRawTerminal).length
      (compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms
        tokenTable width tokenCount stateBoundary stateCount valueBound
          indexTerm)
      compactParserSyntaxAdjacentRowBoundedSourceRawTerminal
      (compactParserSyntaxAdjacentRowBoundedAtValuationIndexCodeSourceTerms_code_length_le
        tokenTable width tokenCount stateBoundary stateCount valueBound
        indexTerm termCodeBound bitBound htokenTable hwidth htokenCount
        hstateBoundary hstateCount hvalueBound hindexCode)
      le_rfl

#print axioms
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_code_length_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFixedCodeBounds
