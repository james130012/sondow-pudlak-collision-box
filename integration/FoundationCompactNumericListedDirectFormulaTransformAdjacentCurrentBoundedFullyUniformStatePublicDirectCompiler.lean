import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedFullyUniformStatePublicDirectCompiler
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity14

/-! # Uniform-state public compiler for fourteen current-state witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedFullyUniformStatePublicDirectCompiler

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
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedFullyUniformStatePublicDirectCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 14
    (compactFormulaTransformAdjacentPublicContextCodeBound valuation rowIndexTerm)
    valueBound
    (compactFormulaTransformAdjacentCurrentRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound)
    (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound)

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat)
    (_hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) : Nat :=
  compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelope
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound numericBound bitBound

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectBoundOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat)
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
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound)
      (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelopeOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        numericBound bitBound hcurrent) := by
  let data := compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound hcurrent
  let witness := data.witness
  let values := adjacentCurrentBoundedWitnessValues witness
  let rawBody := compactFormulaTransformAdjacentCurrentBoundedRawTerminal
    tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
    witnessStart witnessFinish witnessCount valueBound
  let bodyCodeBound :=
    compactFormulaTransformAdjacentCurrentRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  let contextCodeBound :=
    compactFormulaTransformAdjacentPublicContextCodeBound valuation rowIndexTerm
  have hbody : (binaryFormulaCode rawBody).length <= bodyCodeBound :=
    compactFormulaTransformAdjacentCurrentRawTerminal_code_length_le_public
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  have hcontext : formulaCodeSum
      (valuationContext rawBody.freeVariables valuation) <= contextCodeBound :=
    compactFormulaTransformAdjacentCurrentRawTerminal_context_le_public
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
  let innerDirect :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound witness.coordinates witness.size data.values_le hindexVariables
      hzero hvalueBound hwidthValue htokenCount hstateCount hareaNumeric
      hareaBit htokenTableSize hstateBoundarySize hnumericSize hnumericBit
      hbitPositive data.next
  let innerResource :=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound witness.coordinates witness.size data.next
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph_payloadLength_le
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound witness.coordinates witness.size data.values_le hindexVariables
      hzero hvalueBound hwidthValue htokenCount hstateCount hareaNumeric
      hareaBit htokenTableSize hstateBoundarySize hnumericSize hnumericBit
      hbitPositive data.next
  let rawTerminal := castValuationContextProof
    (compactFormulaTransformAdjacentCurrentBoundedRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound witness).symm
      innerDirect
  have hrawTerminal : rawTerminal.payloadLength <= innerResource := by
    change (castValuationContextProof
      (compactFormulaTransformAdjacentCurrentBoundedRawTerminal_alignment
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound witness).symm
      innerDirect).payloadLength <= _
    rw [castValuationContextProof_payloadLength_eq]
    exact hinner
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 14 rawBody
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound valueBound bodyCodeBound rawBody values data.values_le
      hbody hcontext innerResource rawTerminal hrawTerminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity14
      contextCodeBound valueBound bodyCodeBound rawBody values data.values_le
      hbody hcontext innerResource rawTerminal hrawTerminal
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound :=
    (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound).symm
  let proof := castValuationContextProof hformula rawProof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = rawProof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula rawProof]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  simpa only [
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelopeOfGraph,
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelope,
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelopeOfGraph,
    data, witness, innerResource, rawBody, bodyCodeBound, contextCodeBound,
    sourceFormula, compilation, rawProof] using hcoordinates.2

noncomputable def
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat)
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
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) :=
  (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectBoundOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound numericBound
    bitBound hindexVariables hzero hvalueBound hwidthValue htokenCount
    hstateCount hareaNumeric hareaBit htokenTableSize hstateBoundarySize
    hnumericSize hnumericBit hbitPositive hcurrent).proof

theorem
    compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat)
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
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound) :
    (compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      numericBound bitBound hindexVariables hzero hvalueBound hwidthValue
      htokenCount hstateCount hareaNumeric hareaBit htokenTableSize
      hstateBoundarySize hnumericSize hnumericBit hbitPositive hcurrent
      ).payloadLength <=
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      numericBound bitBound hcurrent :=
  (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectBoundOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound numericBound
    bitBound hindexVariables hzero hvalueBound hwidthValue htokenCount
    hstateCount hareaNumeric hareaBit htokenTableSize hstateBoundarySize
    hnumericSize hnumericBit hbitPositive hcurrent).payloadLength_le

#print axioms
  compileCompactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFullyUniformStatePublicDirectOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedFullyUniformStatePublicDirectCompiler
