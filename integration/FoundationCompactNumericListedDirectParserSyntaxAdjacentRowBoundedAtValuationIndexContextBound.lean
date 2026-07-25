import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexResourceDefinitions
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFreeVariables
import integration.FoundationCompactPAValuationContextSingletonCodeBound

/-! # Uniform context bound for the open-index adjacent-row body -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexContextBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationContextSingletonCodeBound
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFreeVariables
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexResourceDefinitions

theorem
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_context_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm)
    (numericBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hzero : valuation 0 <= numericBound) :
    formulaCodeSum
        (valuationContext
          (compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal
            tokenTable width tokenCount stateBoundary stateCount valueBound
              indexTerm).freeVariables valuation) <=
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexContextCodeEnvelope
        numericBound := by
  let body :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal tokenTable
      width tokenCount stateBoundary stateCount valueBound indexTerm
  have hbodyVariables : body.freeVariables ⊆ {0} := by
    dsimp only [body]
    exact
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_freeVariables_subset_singleton
        tokenTable width tokenCount stateBoundary stateCount valueBound
          indexTerm hindexVariables
  exact valuationContext_formulaCodeSum_le_singleton body.freeVariables
    valuation numericBound hbodyVariables hzero

#print axioms
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_context_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexContextBound
