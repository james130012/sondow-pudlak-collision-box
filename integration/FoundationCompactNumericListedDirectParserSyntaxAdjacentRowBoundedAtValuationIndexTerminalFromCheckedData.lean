import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexWitnessAlignment
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedCheckedData

/-! # Open-index terminal proof extracted from checked adjacent-row data -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexTerminalFromCheckedData

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedCheckedData
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexWitnessAlignment

noncomputable def
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexTerminalBoundOfCheckedData
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
    ExplicitDirectFormulaBound valuation
      (compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal
          tokenTable width tokenCount stateBoundary stateCount valueBound
            indexTerm ⇜
        (fun coordinate => shortBinaryNumeralTerm
          (compactParserSyntaxAdjacentRowBoundedWitnessValues data.row
            coordinate)))
      (compactParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedPayloadPolynomial
        indexTerm tokenCount numericBound bitBound) := by
  have hvalueBoundSize : Nat.size valueBound <= bitBound :=
    (Nat.size_le_size hvalueBound).trans hnumericSize
  have hcurrentAtValueBound := data.current_value_bound
  have hnextAtValueBound := data.next_value_bound
  have hwitnessAtValueBound := data.witness_value_bound
  have hcurrentValue :=
    parserStateCoordinateValueBound_mono hcurrentAtValueBound hvalueBound
  have hnextValue :=
    parserStateCoordinateValueBound_mono hnextAtValueBound hvalueBound
  have hwitnessValue :=
    parserSyntaxStepWitnessCoordinateValueBound_mono hwitnessAtValueBound
      hvalueBound
  have hcurrentSize :=
    parserStateCoordinateSizeBound_of_valueBound hcurrentAtValueBound
      hvalueBoundSize
  have hnextSize :=
    parserStateCoordinateSizeBound_of_valueBound hnextAtValueBound
      hvalueBoundSize
  have hwitnessSize :=
    parserSyntaxStepWitnessCoordinateSizeBound_of_valueBound
      hwitnessAtValueBound hvalueBoundSize
  let terminalBound :=
    compactParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedBound
      valuation tokenTable width tokenCount stateBoundary stateCount valueBound
      indexTerm data.row numericBound bitBound hindexVariables data.graph
      data.current_status data.next_status hvalueBound hwidth hwidthBit
      htokenCount hstateCount hcurrentValue hnextValue htokenTableSize
      hstateBoundarySize hcurrentSize hnextSize hwitnessValue hwitnessSize
      hareaNumeric hareaBit hzero hnumericSize hbitPositive
  let terminal := castValuationContextProof
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount valueBound indexTerm
        data.row).symm terminalBound.proof
  refine ⟨terminal, ?_⟩
  change (castValuationContextProof
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount valueBound indexTerm
        data.row).symm terminalBound.proof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  exact terminalBound.payloadLength_le

#print axioms
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexTerminalBoundOfCheckedData

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexTerminalFromCheckedData
