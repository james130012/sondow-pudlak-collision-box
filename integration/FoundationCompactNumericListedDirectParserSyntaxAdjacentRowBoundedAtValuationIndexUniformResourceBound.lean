import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexTermCodeFixedBound
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompilerArity27

/-! # Uniform-resource twenty-seven-witness adjacent-row compiler -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexUniformResourceBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicUniformResourceCompilerArity27
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

def compactParserSyntaxAdjacentRowBoundedAtValuationIndexUniformPayloadPolynomial
    (uniformValueBound termCodeBound tokenCount numericBound bitBound : Nat) :
    Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 27
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexContextCodeEnvelope
      numericBound)
    uniformValueBound
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminalFixedCodeEnvelope
      termCodeBound bitBound)
    (compactParserSyntaxAdjacentRowTerminalAtValuationIndexTermCodeFixedPayloadPolynomial
      termCodeBound tokenCount numericBound bitBound)

noncomputable def
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexUniformBound
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount formulaValueBound
      uniformValueBound : Nat)
    (indexTerm : ValuationTerm)
    (termCodeBound numericBound bitBound : Nat)
    (hformulaValue : formulaValueBound <= uniformValueBound)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hnextIndexCode :
      (binaryTermCode (‘!!indexTerm + 1’ : ValuationTerm)).length <=
        termCodeBound)
    (hnextNextIndexCode :
      (binaryTermCode
        (‘!!(‘!!indexTerm + 1’ : ValuationTerm) + 1’ : ValuationTerm)).length <=
        termCodeBound)
    (hbounded : CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
      stateBoundary stateCount (termValue valuation indexTerm)
        formulaValueBound)
    (hvalueBound : formulaValueBound <= numericBound)
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
        width tokenCount stateBoundary stateCount formulaValueBound indexTerm)
      (compactParserSyntaxAdjacentRowBoundedAtValuationIndexUniformPayloadPolynomial
        uniformValueBound termCodeBound tokenCount numericBound bitBound) := by
  let index := termValue valuation indexTerm
  let data := compactParserSyntaxAdjacentRowCheckedDataOfBounded tokenTable width
    tokenCount stateBoundary stateCount index formulaValueBound hbounded
  have hvalueBoundSize : Nat.size formulaValueBound <= bitBound :=
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
    parserStateCoordinateSizeBound_of_valueBound hnextAtValueBound hvalueBoundSize
  have hwitnessSize :=
    parserSyntaxStepWitnessCoordinateSizeBound_of_valueBound hwitnessAtValueBound
      hvalueBoundSize
  let body :=
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal tokenTable
      width tokenCount stateBoundary stateCount formulaValueBound indexTerm
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
      valuation tokenTable width tokenCount stateBoundary stateCount
      formulaValueBound indexTerm data.row termCodeBound numericBound bitBound
      hindexVariables hindexCode hnextIndexCode hnextNextIndexCode data.graph
      data.current_status data.next_status hvalueBound hwidth hwidthBit
      htokenCount hstateCount hcurrentValue hnextValue htokenTableSize
      hstateBoundarySize hcurrentSize hnextSize hwitnessValue hwitnessSize
      hareaNumeric hareaBit hzero hnumericSize hbitPositive
  let terminal := castValuationContextProof
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount formulaValueBound
        indexTerm data.row).symm terminalBound.proof
  have hterminal : terminal.payloadLength <= terminalResource := by
    change (castValuationContextProof _ terminalBound.proof).payloadLength <= _
    rw [castValuationContextProof_payloadLength_eq]
    exact terminalBound.payloadLength_le
  have hbody : (binaryFormulaCode body).length <= bodyCodeBound := by
    exact
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_code_length_le_fixed
        tokenTable width tokenCount stateBoundary stateCount formulaValueBound
        indexTerm termCodeBound bitBound htokenTableSize hwidthSize
        htokenCountSize hstateBoundarySize hstateCountSize hvalueBoundSize
        hindexCode
  have hcontext :
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum
          (valuationContext body.freeVariables valuation) <=
        contextCodeBound := by
    have hraw :=
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexRawTerminal_context_le
        valuation tokenTable width tokenCount stateBoundary stateCount
          formulaValueBound indexTerm numericBound hindexVariables hzero
    simpa only [
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum,
      FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum] using
      hraw
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm formulaValueBound) 27 body
  let compilation :=
    compileExplicitBoundedWitnessDirectPublicWithUniformResource contextCodeBound
      formulaValueBound uniformValueBound bodyCodeBound hformulaValue body values
      data.values_le hbody hcontext terminalResource terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithUniformResource_coordinates_arity27
      contextCodeBound formulaValueBound uniformValueBound bodyCodeBound
      hformulaValue body values data.values_le hbody hcontext terminalResource
      terminal hterminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula tokenTable
        width tokenCount stateBoundary stateCount formulaValueBound indexTerm :=
    (compactParserSyntaxAdjacentRowBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount formulaValueBound
        indexTerm).symm
  let proof := castValuationContextProof hformula rawProof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = rawProof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula rawProof]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [
    compactParserSyntaxAdjacentRowBoundedAtValuationIndexUniformPayloadPolynomial,
    contextCodeBound, bodyCodeBound, terminalResource, sourceFormula,
    compilation, rawProof, proof] using hcoordinates.2

#print axioms
  compactParserSyntaxAdjacentRowBoundedAtValuationIndexUniformBound

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexUniformResourceBound
