import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity27

/-! # Resource definitions for a bounded adjacent row at an open index -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexResourceDefinitions

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase

def compactParserSyntaxAdjacentRowBoundedAtValuationIndexContextCodeEnvelope
    (numericBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 1 numericBound
    (binaryTermCode (&0 : ValuationTerm)).length

def compactParserSyntaxAdjacentRowBoundedAtValuationIndexFullyFixedPayloadPolynomial
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm)
    (numericBound bitBound : Nat) : Nat :=
  let body :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal tokenTable
      width tokenCount stateBoundary stateCount valueBound indexTerm
  explicitBoundedWitnessDirectPublicPayloadEnvelope 27
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexContextCodeEnvelope
      numericBound)
    valueBound (binaryFormulaCode body).length
    (compactParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedPayloadPolynomial
      indexTerm tokenCount numericBound bitBound)

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexResourceDefinitions
