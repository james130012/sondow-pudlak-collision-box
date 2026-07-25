import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase

/-! # Open-index substitution for the adjacent-row graph component -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexRowAlignment

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSubstitutionComponents
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase

theorem compactParserSyntaxAdjacentRowSourceRowFormula_rewriting_openIndex
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm) :
    sourceSubstitutionQpow
        (compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTerms
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm) 27 ▹
      compactParserSyntaxAdjacentRowSourceRowFormula =
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawRowFormula tokenTable
      width tokenCount stateBoundary stateCount indexTerm := by
  unfold compactParserSyntaxAdjacentRowSourceRowFormula
  unfold compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawRowFormula
  simp [rewriting_embeddedFormulaSubstitution]
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp [Function.comp_apply,
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexSourceTerms]
  all_goals
    rw [sourceSubstitutionQpow_bvar]
    simp [sourceSubstitutionNormalizedBVarResult]

#print axioms
  compactParserSyntaxAdjacentRowSourceRowFormula_rewriting_openIndex

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexRowAlignment
