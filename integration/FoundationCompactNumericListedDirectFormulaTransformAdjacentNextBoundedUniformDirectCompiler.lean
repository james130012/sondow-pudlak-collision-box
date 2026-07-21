import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedUniformDirectCompiler
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformArity14

/-!
# Uniform direct compiler for the fourteen next-state witnesses

The terminal is the uniform nine-witness adjacent-step proof.  The next-state
witness block is then compiled with a public resource independent of its
concrete fourteen-coordinate vector.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedUniformDirectCompiler

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectUniformCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformArity14
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedUniformDirectCompiler

noncomputable def
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexUniformDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize) : Nat :=
  let witness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize hnext
  let innerResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size
      (compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize hnext).2
  explicitBoundedWitnessDirectUniformPayloadEnvelope valuation valueBound
    (compactFormulaTransformAdjacentNextBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize)
    innerResource

noncomputable def
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexUniformDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize).freeVariables valuation)
      (compactFormulaTransformAdjacentNextBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize) := by
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
  let innerDirect :=
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  let innerResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformDirectOfGraph_payloadLength_le
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
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
  let compilation := compileExplicitBoundedWitnessDirectUniformWithResource
    valueBound rawBody values hwitness.1 innerResource rawTerminal hrawTerminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectUniformWithResource_coordinates_arity14
      valueBound rawBody values hwitness.1 innerResource rawTerminal hrawTerminal
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
  exact castValuationContextProof hformula rawProof

theorem
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexUniformDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize) :
    (compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexUniformDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hnext).payloadLength <=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexUniformDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hnext := by
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
  let innerDirect :=
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  let innerResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformDirectOfGraph_payloadLength_le
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
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
  let compilation := compileExplicitBoundedWitnessDirectUniformWithResource
    valueBound rawBody values hwitness.1 innerResource rawTerminal hrawTerminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectUniformWithResource_coordinates_arity14
      valueBound rawBody values hwitness.1 innerResource rawTerminal hrawTerminal
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
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  exact hcoordinates.2

#print axioms
  compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexUniformDirectOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedUniformDirectCompiler
