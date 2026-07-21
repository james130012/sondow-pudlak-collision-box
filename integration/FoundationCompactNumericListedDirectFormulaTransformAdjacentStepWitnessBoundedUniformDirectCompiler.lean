import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformArity09

/-!
# Uniform direct compiler for the nine adjacent-step witnesses

The terminal proof remains the independently assembled row/status proof.  The
nine bounded witnesses are constructed by the intrinsic uniform compiler, so
their public resource does not contain the concrete witness vector.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedUniformDirectCompiler

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectUniformCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformArity09
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) : Nat :=
  let data :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded
  explicitBoundedWitnessDirectUniformPayloadEnvelope valuation valueBound
    (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize)
    data.terminalResource

noncomputable def
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) :
    CertifiedPAContextProof
      (valuationContext
        (compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize nextCoordinates nextSize).freeVariables valuation)
      (compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize) := by
  let data :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded
  let rawBody :=
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 9 rawBody
  let compilation := compileExplicitBoundedWitnessDirectUniformWithResource
    valueBound rawBody data.values data.values_le data.terminalResource
      data.terminal data.terminal_payloadLength_le
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectUniformWithResource_coordinates_arity09
      valueBound rawBody data.values data.values_le data.terminalResource
      data.terminal data.terminal_payloadLength_le
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize :=
    (compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize).symm
  exact castValuationContextProof hformula rawProof

theorem
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) :
    (compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded).payloadLength <=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded := by
  let data :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded
  let rawBody :=
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 9 rawBody
  let compilation := compileExplicitBoundedWitnessDirectUniformWithResource
    valueBound rawBody data.values data.values_le data.terminalResource
      data.terminal data.terminal_payloadLength_le
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectUniformWithResource_coordinates_arity09
      valueBound rawBody data.values data.values_le data.terminalResource
      data.terminal data.terminal_payloadLength_le
  let rawProof := castDirectCompilationProof compilation sourceFormula
    hcoordinates.1
  have hformula : sourceFormula =
      compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize :=
    (compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize).symm
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  exact hcoordinates.2

#print axioms
  compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformDirectOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedUniformDirectCompiler
