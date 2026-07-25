import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexContextBound
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexTerminalFromCheckedData
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicBoundArity27

/-! # Direct compilation of the expanded open-index bounded-row formula -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexRawCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity27
open FoundationCompactPAExplicitBoundedWitnessDirectPublicBoundArity27
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedCheckedData
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexResourceDefinitions
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexContextBound
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexTerminalFromCheckedData

noncomputable def
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawBoundOfCheckedData
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm)
    (data : CompactParserSyntaxAdjacentRowCheckedData tokenTable width tokenCount
      stateBoundary stateCount (termValue valuation indexTerm) valueBound)
    (numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hvalueBound : valueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hzero : valuation 0 <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    let body :=
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal
        tokenTable width tokenCount stateBoundary stateCount valueBound indexTerm
    ExplicitDirectFormulaBound valuation
      (explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 27 body)
      (compactParserSyntaxAdjacentRowBoundedAtValuationIndexFullyFixedPayloadPolynomial
        tokenTable width tokenCount stateBoundary stateCount valueBound indexTerm
          numericBound bitBound) := by
  let body :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal tokenTable
      width tokenCount stateBoundary stateCount valueBound indexTerm
  let values := compactParserSyntaxAdjacentRowBoundedWitnessValues data.row
  let contextCodeBound :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexContextCodeEnvelope
      numericBound
  let bodyCodeBound := (binaryFormulaCode body).length
  let terminalResource :=
    compactParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedPayloadPolynomial
      indexTerm tokenCount numericBound bitBound
  let terminalBound :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexTerminalBoundOfCheckedData
      valuation tokenTable width tokenCount stateBoundary stateCount valueBound
      indexTerm data numericBound bitBound hindexVariables hvalueBound hwidth
      hwidthBit htokenCount hstateCount htokenTableSize hstateBoundarySize
      hareaNumeric hareaBit hzero hnumericSize hbitPositive
  have hcontext :
      formulaCodeSum (valuationContext body.freeVariables valuation) <=
        contextCodeBound := by
    exact
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_context_le
        valuation tokenTable width tokenCount stateBoundary stateCount
          valueBound indexTerm numericBound hindexVariables hzero
  let bound := compileExplicitBoundedWitnessDirectPublicBoundArity27
    contextCodeBound valueBound bodyCodeBound body values data.values_le
      (by rfl) hcontext terminalResource terminalBound.proof
        terminalBound.payloadLength_le
  change ExplicitDirectFormulaBound valuation
    (explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 27 body)
    (explicitBoundedWitnessDirectPublicPayloadEnvelope 27 contextCodeBound
      valueBound bodyCodeBound terminalResource)
  exact bound

#print axioms
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawBoundOfCheckedData

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexRawCompiler
