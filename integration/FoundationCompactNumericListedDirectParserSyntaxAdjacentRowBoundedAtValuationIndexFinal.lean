import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFormulaAlignment
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexRawCompiler

/-! # Original bounded adjacent-row formula at an arbitrary valuation index -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFinal

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedCheckedData
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFormulaAlignment
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexResourceDefinitions
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexRawCompiler

noncomputable def
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexFullyFixedBound
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm)
    (numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hbounded : CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
      stateBoundary stateCount (termValue valuation indexTerm) valueBound)
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
    ExplicitDirectFormulaBound valuation
      (compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula tokenTable
        width tokenCount stateBoundary stateCount valueBound indexTerm)
      (compactParserSyntaxAdjacentRowBoundedAtValuationIndexFullyFixedPayloadPolynomial
        tokenTable width tokenCount stateBoundary stateCount valueBound indexTerm
          numericBound bitBound) := by
  let index := termValue valuation indexTerm
  let data := compactParserSyntaxAdjacentRowCheckedDataOfBounded tokenTable width
    tokenCount stateBoundary stateCount index valueBound hbounded
  let body :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal tokenTable
      width tokenCount stateBoundary stateCount valueBound indexTerm
  let rawBound :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawBoundOfCheckedData
      valuation tokenTable width tokenCount stateBoundary stateCount valueBound
      indexTerm data numericBound bitBound hindexVariables hvalueBound hwidth
      hwidthBit htokenCount hstateCount htokenTableSize hstateBoundarySize
      hareaNumeric hareaBit hzero hnumericSize hbitPositive
  have hformula :
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 27 body =
        compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula tokenTable
          width tokenCount stateBoundary stateCount valueBound indexTerm :=
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount valueBound
        indexTerm).symm
  let proof := castValuationContextProof hformula rawBound.proof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = rawBound.proof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula rawBound.proof]
  exact rawBound.payloadLength_le

#print axioms
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexFullyFixedBound

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFinal
