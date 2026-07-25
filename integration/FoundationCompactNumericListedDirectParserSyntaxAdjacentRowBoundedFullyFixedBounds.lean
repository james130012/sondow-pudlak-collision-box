import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedCheckedData
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedFixedCodeBounds

/-!
# Fully fixed direct bound for one bounded adjacent parser row

The twenty-seven witnesses are extracted from the original bounded proposition.
The open terminal formula has a fixed code envelope and no free-variable
context, so the final resource contains no concrete row or witness coordinate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity27
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedCheckedData
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedFixedCodeBounds

private abbrev boundedRowFixedZeroValuation : Nat -> Nat :=
  compactParserStateAtRowsZeroValuation

noncomputable def compactParserSyntaxAdjacentRowBoundedFullyFixedBound
    (tokenTable width tokenCount stateBoundary stateCount index valueBound
      numericBound bitBound : Nat)
    (hbounded : CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
      stateBoundary stateCount index valueBound)
    (hindex : index <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound boundedRowFixedZeroValuation
      (compactParserSyntaxAdjacentRowBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount index valueBound)
      (compactParserSyntaxAdjacentRowBoundedFullyFixedPayloadPolynomial index
        tokenCount valueBound numericBound bitBound) := by
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
  have hindexSize : Nat.size index <= bitBound :=
    (Nat.size_le_size hindex).trans hnumericSize
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
    compactParserSyntaxAdjacentRowBoundedRawTerminal tokenTable width tokenCount
      stateBoundary stateCount index valueBound
  let values := compactParserSyntaxAdjacentRowBoundedWitnessValues data.row
  let bodyCodeBound :=
    compactParserSyntaxAdjacentRowBoundedRawTerminalFixedCodeEnvelope bitBound
  let terminalResource :=
    compactParserSyntaxAdjacentRowTerminalFullyFixedPayloadPolynomial index
      tokenCount numericBound bitBound
  let terminalBound :=
    compactParserSyntaxAdjacentRowTerminalFullyFixedBound tokenTable width
      tokenCount stateBoundary stateCount index valueBound data.row numericBound
      bitBound data.graph data.current_status data.next_status hvalueBound
      hwidth hwidthBit htokenCount hstateCount hcurrentValue hnextValue
      htokenTableSize hstateBoundarySize hcurrentSize hnextSize hwitnessValue
      hwitnessSize hareaNumeric hareaBit hnumericSize hbitPositive
  let terminal := castValuationContextProof
    (compactParserSyntaxAdjacentRowBoundedRawTerminal_alignment tokenTable width
      tokenCount stateBoundary stateCount index valueBound data.row).symm
    terminalBound.proof
  have hterminal : terminal.payloadLength <= terminalResource := by
    change (castValuationContextProof
      (compactParserSyntaxAdjacentRowBoundedRawTerminal_alignment tokenTable
        width tokenCount stateBoundary stateCount index valueBound
        data.row).symm terminalBound.proof).payloadLength <= _
    rw [castValuationContextProof_payloadLength_eq]
    exact terminalBound.payloadLength_le
  have hbody : (binaryFormulaCode body).length <= bodyCodeBound := by
    exact
      compactParserSyntaxAdjacentRowBoundedRawTerminal_code_length_le_fixed
        tokenTable width tokenCount stateBoundary stateCount index valueBound
        bitBound htokenTableSize hwidthSize htokenCountSize hstateBoundarySize
        hstateCountSize hindexSize hvalueBoundSize
  have hcontext :
      formulaCodeSum
        (valuationContext body.freeVariables boundedRowFixedZeroValuation) <=
          0 := by
    exact Nat.le_of_eq
      (compactParserSyntaxAdjacentRowBoundedRawTerminal_context_eq_zero
        tokenTable width tokenCount stateBoundary stateCount index valueBound
        boundedRowFixedZeroValuation)
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 27 body
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    0 valueBound bodyCodeBound body values data.values_le hbody hcontext
      terminalResource terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity27
      0 valueBound bodyCodeBound body values data.values_le hbody hcontext
        terminalResource terminal hterminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactParserSyntaxAdjacentRowBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount index valueBound :=
    (compactParserSyntaxAdjacentRowBoundedClosedFormula_alignment tokenTable
      width tokenCount stateBoundary stateCount index valueBound).symm
  let proof := castValuationContextProof hformula rawProof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = rawProof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula rawProof]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [
    compactParserSyntaxAdjacentRowBoundedFullyFixedPayloadPolynomial,
    body, values, bodyCodeBound, terminalResource, sourceFormula, compilation,
    rawProof] using hcoordinates.2

#print axioms compactParserSyntaxAdjacentRowBoundedFullyFixedBound

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedFullyFixedBounds
