import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedFullyUniformStatePublicDirectCompiler
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity14

/-! # Uniform-state public compiler for fourteen next-state witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedFullyUniformStatePublicDirectCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity14
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedFullyUniformStatePublicDirectCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds

noncomputable def
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize) : Nat :=
  let witness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize hnext
  let innerResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound currentCoordinates currentSize witness.coordinates witness.size
      (compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec valuation
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize hnext).2
  explicitBoundedWitnessDirectPublicPayloadEnvelope 14
    (compactFormulaTransformAdjacentPublicContextCodeBound valuation rowIndexTerm)
    valueBound
    (compactFormulaTransformAdjacentNextRawTerminalPublicCodeEnvelope tokenTable
      width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound)
    innerResource

noncomputable def
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectBoundOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0})
    (hzero : valuation 0 <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hnext : CompactFormulaTransformAdjacentNextBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize)
      (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelopeOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        numericBound bitBound currentCoordinates currentSize hnext) := by
  let witness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize hnext
  have hwitness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize hnext
  let values := adjacentNextBoundedWitnessValues witness
  let rawBody := compactFormulaTransformAdjacentNextBoundedRawTerminal
    tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
    witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize
  let bodyCodeBound :=
    compactFormulaTransformAdjacentNextRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  let contextCodeBound :=
    compactFormulaTransformAdjacentPublicContextCodeBound valuation rowIndexTerm
  have hbody : (binaryFormulaCode rawBody).length <= bodyCodeBound :=
    compactFormulaTransformAdjacentNextRawTerminal_code_length_le_public
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hcurrent
  have hcontext : formulaCodeSum
      (valuationContext rawBody.freeVariables valuation) <= contextCodeBound :=
    compactFormulaTransformAdjacentNextRawTerminal_context_le_public
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize
  let innerDirect :=
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound currentCoordinates currentSize witness.coordinates witness.size
      hcurrent hwitness.1 hindexVariables hzero hvalueBound hwidthValue
      htokenCount hstateCount hareaNumeric hareaBit htokenTableSize
      hstateBoundarySize hnumericSize hnumericBit hbitPositive hwitness.2
  let innerResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound currentCoordinates currentSize witness.coordinates witness.size
      hwitness.2
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph_payloadLength_le
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound currentCoordinates currentSize witness.coordinates witness.size
      hcurrent hwitness.1 hindexVariables hzero hvalueBound hwidthValue
      htokenCount hstateCount hareaNumeric hareaBit htokenTableSize
      hstateBoundarySize hnumericSize hnumericBit hbitPositive hwitness.2
  let rawTerminal := castValuationContextProof
    (compactFormulaTransformAdjacentNextBoundedRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness).symm innerDirect
  have hrawTerminal : rawTerminal.payloadLength <= innerResource := by
    change (castValuationContextProof
      (compactFormulaTransformAdjacentNextBoundedRawTerminal_alignment
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize witness).symm innerDirect).payloadLength <= _
    rw [castValuationContextProof_payloadLength_eq]
    exact hinner
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 14 rawBody
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound valueBound bodyCodeBound rawBody values hwitness.1 hbody
      hcontext innerResource rawTerminal hrawTerminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity14
      contextCodeBound valueBound bodyCodeBound rawBody values hwitness.1
      hbody hcontext innerResource rawTerminal hrawTerminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize :=
    (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize).symm
  let proof := castValuationContextProof hformula rawProof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = rawProof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula rawProof]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelopeOfGraph,
    witness, innerResource, rawBody, bodyCodeBound, contextCodeBound,
    sourceFormula, compilation, rawProof] using hcoordinates.2

noncomputable def
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0})
    (hzero : valuation 0 <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hnext : CompactFormulaTransformAdjacentNextBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize) :=
  (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectBoundOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound numericBound
    bitBound currentCoordinates currentSize hcurrent hindexVariables hzero
    hvalueBound hwidthValue htokenCount hstateCount hareaNumeric hareaBit
    htokenTableSize hstateBoundarySize hnumericSize hnumericBit hbitPositive
    hnext).proof

theorem
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0})
    (hzero : valuation 0 <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hnext : CompactFormulaTransformAdjacentNextBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize) :
    (compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      numericBound bitBound currentCoordinates currentSize hcurrent
      hindexVariables hzero hvalueBound hwidthValue htokenCount hstateCount
      hareaNumeric hareaBit htokenTableSize hstateBoundarySize hnumericSize
      hnumericBit hbitPositive hnext).payloadLength <=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      numericBound bitBound currentCoordinates currentSize hnext :=
  (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectBoundOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound numericBound
    bitBound currentCoordinates currentSize hcurrent hindexVariables hzero
    hvalueBound hwidthValue htokenCount hstateCount hareaNumeric hareaBit
    htokenTableSize hstateBoundarySize hnumericSize hnumericBit hbitPositive
    hnext).payloadLength_le

#print axioms
  compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedFullyUniformStatePublicDirectCompiler
