import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntax

/-! # Public direct compiler for twenty-seven bounded adjacent-row witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedPublicDirectCompiler

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
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedQuantifierSyntax
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

private abbrev boundedRowZeroValuation : Nat -> Nat :=
  compactParserStateAtRowsZeroValuation

def compactParserSyntaxAdjacentRowBoundedPublicDirectPayloadEnvelope
    (tokenTable width tokenCount stateBoundary stateCount index valueBound
      numericBound bitBound : Nat) : Nat :=
  let body :=
    compactParserSyntaxAdjacentRowBoundedRawTerminal tokenTable width tokenCount
      stateBoundary stateCount index valueBound
  explicitBoundedWitnessDirectPublicPayloadEnvelope 27
    (formulaCodeSum
      (valuationContext body.freeVariables boundedRowZeroValuation))
    valueBound
    (binaryFormulaCode body).length
    (compactParserSyntaxAdjacentRowTerminalFullyFixedPayloadPolynomial index
      tokenCount numericBound bitBound)

noncomputable def compactParserSyntaxAdjacentRowBoundedPublicDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat)
    (row : CompactParserSyntaxAdjacentStepRow)
    (numericBound bitBound : Nat)
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph tokenTable width tokenCount
      stateBoundary stateCount index row)
    (hcurrentStatus : CompactBinaryNatStatusValidBounded tokenTable width
      tokenCount row.currentCoordinates.tasksFinish
      row.currentCoordinates.finish valueBound)
    (hnextStatus : CompactBinaryNatStatusValidBounded tokenTable width
      tokenCount row.nextCoordinates.tasksFinish row.nextCoordinates.finish
      valueBound)
    (hvalues : forall coordinate,
      compactParserSyntaxAdjacentRowBoundedWitnessValues row coordinate <=
        valueBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound row.currentCoordinates
        numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound row.nextCoordinates
        numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound row.currentCoordinates
        bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound row.nextCoordinates
        bitBound)
    (hwitnessValue :
      CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound row.stepWitness
        numericBound)
    (hwitnessSize :
      CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound row.stepWitness
        bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound boundedRowZeroValuation
      (compactParserSyntaxAdjacentRowBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount index valueBound)
      (compactParserSyntaxAdjacentRowBoundedPublicDirectPayloadEnvelope
        tokenTable width tokenCount stateBoundary stateCount index valueBound
        numericBound bitBound) := by
  let body :=
    compactParserSyntaxAdjacentRowBoundedRawTerminal tokenTable width tokenCount
      stateBoundary stateCount index valueBound
  let values := compactParserSyntaxAdjacentRowBoundedWitnessValues row
  let bodyCodeBound := (binaryFormulaCode body).length
  let contextCodeBound :=
    formulaCodeSum
      (valuationContext body.freeVariables boundedRowZeroValuation)
  let terminalResource :=
    compactParserSyntaxAdjacentRowTerminalFullyFixedPayloadPolynomial index
      tokenCount numericBound bitBound
  let terminalBound :=
    compactParserSyntaxAdjacentRowTerminalFullyFixedBound tokenTable width
      tokenCount stateBoundary stateCount index valueBound row numericBound
      bitBound hgraph hcurrentStatus hnextStatus hvalueBound hwidth hwidthBit
      htokenCount hstateCount hcurrentValue hnextValue htokenTableSize
      hstateBoundarySize hcurrentSize hnextSize hwitnessValue hwitnessSize
      hareaNumeric hareaBit hnumericSize hbitPositive
  let terminal := castValuationContextProof
    (compactParserSyntaxAdjacentRowBoundedRawTerminal_alignment tokenTable width
      tokenCount stateBoundary stateCount index valueBound row).symm
    terminalBound.proof
  have hterminal : terminal.payloadLength <= terminalResource := by
    change (castValuationContextProof
      (compactParserSyntaxAdjacentRowBoundedRawTerminal_alignment tokenTable
        width tokenCount stateBoundary stateCount index valueBound row).symm
      terminalBound.proof).payloadLength <= _
    rw [castValuationContextProof_payloadLength_eq]
    exact terminalBound.payloadLength_le
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 27 body
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound valueBound bodyCodeBound body values hvalues (by rfl)
      (by rfl) terminalResource terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity27
      contextCodeBound valueBound bodyCodeBound body values hvalues (by rfl)
        (by rfl) terminalResource terminal hterminal
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
    compactParserSyntaxAdjacentRowBoundedPublicDirectPayloadEnvelope,
    body, values, bodyCodeBound, contextCodeBound, terminalResource,
    sourceFormula, compilation, rawProof] using hcoordinates.2

#print axioms compactParserSyntaxAdjacentRowBoundedPublicDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedPublicDirectCompiler
