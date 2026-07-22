import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicAssemblyBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicFiniteBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity09

/-!
# Public direct compiler for the nine adjacent-step witnesses

The terminal remains the independently assembled checked row/status proof.
The outer nine witnesses are compiled with a resource depending only on the
public context, the public raw-body code envelope, and the terminal resource.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedPublicDirectCompiler

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
open FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicAssemblyBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicFiniteBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
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
  explicitBoundedWitnessDirectPublicPayloadEnvelope 9
    (compactFormulaTransformAdjacentPublicContextCodeBound
      valuation rowIndexTerm)
    valueBound
    (compactFormulaTransformAdjacentStepRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound)
    (compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded)

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
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
  explicitBoundedWitnessDirectPublicPayloadEnvelope 9
    (compactFormulaTransformAdjacentPublicContextCodeBound
      valuation rowIndexTerm)
    valueBound
    (compactFormulaTransformAdjacentStepRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound)
    (compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hbounded)

theorem
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph_eq_publicFinite
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
      nextSize)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0}) :
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize hbounded =
      compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize hbounded := by
  unfold
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
    compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelope
    compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelope
  rw [
    compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelopeOfComponents_eq_publicFinite
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize
      (explicitAdjacentStepDirectTerminalComponentsOfGraph valuation tokenTable
        width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound currentCoordinates currentSize
        nextCoordinates nextSize hbounded) hindexVariables]

noncomputable def
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectOfGraph
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
  let terminalResource :=
    compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded
  have hterminalResource : data.terminalResource <= terminalResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph_terminalResource_le_publicAssembly
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hcurrent hnext
      hbounded
  have hterminal : data.terminal.payloadLength <= terminalResource :=
    data.terminal_payloadLength_le.trans hterminalResource
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
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le
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
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize) :
    (compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hcurrent hnext
      hbounded).payloadLength <=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded := by
  let data :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded
  let terminalResource :=
    compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded
  have hterminalResource : data.terminalResource <= terminalResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph_terminalResource_le_publicAssembly
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hcurrent hnext
      hbounded
  have hterminal : data.terminal.payloadLength <= terminalResource :=
    data.terminal_payloadLength_le.trans hterminalResource
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

theorem
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le_publicFinite
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
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize nextCoordinates
      nextSize)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0}) :
    (compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hcurrent hnext hbounded).payloadLength <=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hbounded := by
  rw [←
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph_eq_publicFinite
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hbounded hindexVariables]
  exact
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hcurrent hnext hbounded

#print axioms
  compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le
#print axioms
  compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le_publicFinite

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedPublicDirectCompiler
