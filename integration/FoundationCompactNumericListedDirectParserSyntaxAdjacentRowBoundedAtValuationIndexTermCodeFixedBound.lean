import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalAtValuationIndexTermCodeFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFixedCodeBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFinal
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicBoundArity27

/-! # Term-code fixed twenty-seven-witness adjacent-row compiler -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicBoundArity27
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedCheckedData
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexWitnessAlignment
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFormulaAlignment
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexContextBound
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexResourceDefinitions
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalAtValuationIndexTermCodeFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexFixedCodeBounds

def compactParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedPayloadPolynomial
    (valueBound termCodeBound tokenCount numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 27
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexContextCodeEnvelope
      numericBound)
    valueBound
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminalFixedCodeEnvelope
      termCodeBound bitBound)
    (compactParserSyntaxAdjacentRowTerminalAtValuationIndexTermCodeFixedPayloadPolynomial
      termCodeBound tokenCount numericBound bitBound)

noncomputable def
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedBound
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm)
    (termCodeBound numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hnextIndexCode :
      (binaryTermCode (‘!!indexTerm + 1’ : ValuationTerm)).length <=
        termCodeBound)
    (hnextNextIndexCode :
      (binaryTermCode
        (‘!!(‘!!indexTerm + 1’ : ValuationTerm) + 1’ :
          ValuationTerm)).length <= termCodeBound)
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
      (compactParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedPayloadPolynomial
        valueBound termCodeBound tokenCount numericBound bitBound) := by
  let index := termValue valuation indexTerm
  let data := compactParserSyntaxAdjacentRowCheckedDataOfBounded tokenTable width
    tokenCount stateBoundary stateCount index valueBound hbounded
  have hvalueBoundSize : Nat.size valueBound <= bitBound :=
    (Nat.size_le_size hvalueBound).trans hnumericSize
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hstateCountSize : Nat.size stateCount <= bitBound :=
    (Nat.size_le_size hstateCount).trans hnumericSize
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
  let body :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal tokenTable
      width tokenCount stateBoundary stateCount valueBound indexTerm
  let values := compactParserSyntaxAdjacentRowBoundedWitnessValues data.row
  let contextCodeBound :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexContextCodeEnvelope
      numericBound
  let bodyCodeBound :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminalFixedCodeEnvelope
      termCodeBound bitBound
  let terminalResource :=
    compactParserSyntaxAdjacentRowTerminalAtValuationIndexTermCodeFixedPayloadPolynomial
      termCodeBound tokenCount numericBound bitBound
  let terminalBound :=
    compactParserSyntaxAdjacentRowTerminalAtValuationIndexTermCodeFixedBound
      valuation tokenTable width tokenCount stateBoundary stateCount valueBound
      indexTerm data.row termCodeBound numericBound bitBound hindexVariables
      hindexCode hnextIndexCode hnextNextIndexCode data.graph
      data.current_status data.next_status hvalueBound hwidth hwidthBit
      htokenCount hstateCount hcurrentValue hnextValue htokenTableSize
      hstateBoundarySize hcurrentSize hnextSize hwitnessValue hwitnessSize
      hareaNumeric hareaBit hzero hnumericSize hbitPositive
  let terminal := castValuationContextProof
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount valueBound indexTerm
        data.row).symm terminalBound.proof
  have hterminal : terminal.payloadLength <= terminalResource := by
    change (castValuationContextProof
      (compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_alignment
        tokenTable width tokenCount stateBoundary stateCount valueBound
          indexTerm data.row).symm terminalBound.proof).payloadLength <= _
    rw [castValuationContextProof_payloadLength_eq]
    exact terminalBound.payloadLength_le
  have hbody : (binaryFormulaCode body).length <= bodyCodeBound := by
    exact
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_code_length_le_fixed
        tokenTable width tokenCount stateBoundary stateCount valueBound
        indexTerm termCodeBound bitBound htokenTableSize hwidthSize
        htokenCountSize hstateBoundarySize hstateCountSize hvalueBoundSize
        hindexCode
  have hcontext :
      formulaCodeSum (valuationContext body.freeVariables valuation) <=
        contextCodeBound := by
    exact
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_context_le
        valuation tokenTable width tokenCount stateBoundary stateCount
          valueBound indexTerm numericBound hindexVariables hzero
  let rawBound := compileExplicitBoundedWitnessDirectPublicBoundArity27
    contextCodeBound valueBound bodyCodeBound body values data.values_le hbody
      hcontext terminalResource terminal hterminal
  have hformula :
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 27
          body =
        compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula tokenTable
          width tokenCount stateBoundary stateCount valueBound indexTerm :=
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount valueBound
        indexTerm).symm
  let proof := castValuationContextProof hformula rawBound.proof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = rawBound.proof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula rawBound.proof]
  simpa only [
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedPayloadPolynomial,
    contextCodeBound, bodyCodeBound, terminalResource] using
    rawBound.payloadLength_le

#print axioms
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedBound

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedBound
