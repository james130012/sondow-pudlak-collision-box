import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFormulaAlignment

/-! # Exact witness substitution into the open-index adjacent-row terminal -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexWitnessAlignment

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitutionComponents
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

theorem
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_alignment
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactParserSyntaxAdjacentStepRow) :
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal tokenTable
          width tokenCount stateBoundary stateCount valueBound indexTerm ⇜
        (fun coordinate => shortBinaryNumeralTerm
          (compactParserSyntaxAdjacentRowBoundedWitnessValues row coordinate)) =
      compactParserSyntaxAdjacentRowTerminalAtValuationIndexFormula tokenTable
        width tokenCount stateBoundary stateCount valueBound indexTerm row := by
  change Rew.subst (fun coordinate => shortBinaryNumeralTerm
      (compactParserSyntaxAdjacentRowBoundedWitnessValues row coordinate)) ▹
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal tokenTable
      width tokenCount stateBoundary stateCount valueBound indexTerm = _
  unfold compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal
  unfold compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawRowFormula
  unfold compactParserSyntaxAdjacentRowRawCurrentStatusFormula
  unfold compactParserSyntaxAdjacentRowRawNextStatusFormula
  unfold compactParserSyntaxAdjacentRowTerminalAtValuationIndexFormula
  unfold compactParserSyntaxAdjacentStepRowAtValuationIndexFormula
  unfold compactParserSyntaxAdjacentRowCurrentStatusFormula
  unfold compactParserSyntaxAdjacentRowNextStatusFormula
  simp [rewriting_embeddedFormulaSubstitution]
  repeat' apply And.intro
  all_goals
    congr 1
    funext coordinate
    fin_cases coordinate <;>
      simp [Function.comp_apply,
        compactParserSyntaxAdjacentStepAtValuationIndexTerms,
        compactParserSyntaxAdjacentRowBoundedWitnessValues, Rew.subst_bvar,
        substitute_sourceSubstitutionLift27]

#print axioms
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_alignment

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexWitnessAlignment
