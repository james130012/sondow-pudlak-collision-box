import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalBranchBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity09

/-!
# Branch-sensitive public direct compiler for the nine step witnesses

The terminal uses the checked status branch actually present in the graph.
The outer compiler performs nine bounded-existential introductions and never
enumerates all values below `valueBound`.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedBranchPublicDirectCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity09
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalBranchBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchPublicDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded tokenTable
      width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) : Nat :=
  let components := explicitAdjacentStepDirectTerminalComponentsOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize nextCoordinates nextSize hbounded
  explicitBoundedWitnessDirectPublicPayloadEnvelope 9
    (compactFormulaTransformAdjacentPublicContextCodeBound
      valuation rowIndexTerm)
    valueBound
    (compactFormulaTransformAdjacentStepRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound)
    (compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelopeOfComponents
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize components)

noncomputable def
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchPublicDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound)
    (hnext : forall index,
      adjacentNextBoundedWitnessValues
        ⟨nextCoordinates, nextSize⟩ index <= valueBound)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded tokenTable
      width tokenCount stateBoundary stateCount
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
  let components := explicitAdjacentStepDirectTerminalComponentsOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize nextCoordinates nextSize hbounded
  let data :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchDirectTerminalOfComponents
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hcurrent hnext
      components
  let terminalResource :=
    compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelopeOfComponents
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize components
  have hterminal : data.terminal.payloadLength <= terminalResource :=
    data.terminal_payloadLength_le
  let rawBody :=
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize
  let bodyCodeBound :=
    compactFormulaTransformAdjacentStepRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  let contextCodeBound :=
    compactFormulaTransformAdjacentPublicContextCodeBound valuation rowIndexTerm
  have hbody : (binaryFormulaCode rawBody).length <= bodyCodeBound :=
    compactFormulaTransformAdjacentStepRawTerminal_code_length_le_public
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hcurrent hnext
  have hcontext : formulaCodeSum
      (valuationContext rawBody.freeVariables valuation) <= contextCodeBound :=
    compactFormulaTransformAdjacentStepRawTerminal_context_le_public
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 9 rawBody
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound valueBound bodyCodeBound rawBody data.values
      data.values_le hbody hcontext terminalResource data.terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity09
      contextCodeBound valueBound bodyCodeBound rawBody data.values
      data.values_le hbody hcontext terminalResource data.terminal hterminal
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
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchPublicDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound)
    (hnext : forall index,
      adjacentNextBoundedWitnessValues
        ⟨nextCoordinates, nextSize⟩ index <= valueBound)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded tokenTable
      width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) :
    (compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hcurrent hnext
      hbounded).payloadLength <=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded := by
  let components := explicitAdjacentStepDirectTerminalComponentsOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize nextCoordinates nextSize hbounded
  let data :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchDirectTerminalOfComponents
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hcurrent hnext
      components
  let terminalResource :=
    compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelopeOfComponents
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize components
  have hterminal : data.terminal.payloadLength <= terminalResource :=
    data.terminal_payloadLength_le
  let rawBody :=
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize
  let bodyCodeBound :=
    compactFormulaTransformAdjacentStepRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  let contextCodeBound :=
    compactFormulaTransformAdjacentPublicContextCodeBound valuation rowIndexTerm
  have hbody : (binaryFormulaCode rawBody).length <= bodyCodeBound :=
    compactFormulaTransformAdjacentStepRawTerminal_code_length_le_public
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hcurrent hnext
  have hcontext : formulaCodeSum
      (valuationContext rawBody.freeVariables valuation) <= contextCodeBound :=
    compactFormulaTransformAdjacentStepRawTerminal_context_le_public
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize
  let sourceFormula := explicitBoundedWitnessFormula
    (shortBinaryNumeralTerm valueBound) 9 rawBody
  let compilation := compileExplicitBoundedWitnessDirectPublicWithResource
    contextCodeBound valueBound bodyCodeBound rawBody data.values
      data.values_le hbody hcontext terminalResource data.terminal hterminal
  have hcoordinates :=
    compileExplicitBoundedWitnessDirectPublicWithResource_coordinates_arity09
      contextCodeBound valueBound bodyCodeBound rawBody data.values
      data.values_le hbody hcontext terminalResource data.terminal hterminal
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
  compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchPublicDirectOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedBranchPublicDirectCompiler
