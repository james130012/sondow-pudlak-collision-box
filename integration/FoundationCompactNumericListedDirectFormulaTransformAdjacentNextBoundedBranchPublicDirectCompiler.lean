import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedBranchPublicDirectCompiler
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity14

/-! # Branch-sensitive public compiler for the fourteen next-state witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedBranchPublicDirectCompiler

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
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity14
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedBranchPublicDirectCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds

noncomputable def
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexBranchPublicDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
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
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size
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
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexBranchPublicDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound)
    (hnext : CompactFormulaTransformAdjacentNextBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize) :
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
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hcurrent hwitness.1 hwitness.2
  let innerResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchPublicDirectOfGraph_payloadLength_le
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hcurrent hwitness.1 hwitness.2
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
  exact castValuationContextProof hformula rawProof

theorem
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexBranchPublicDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound)
    (hnext : CompactFormulaTransformAdjacentNextBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm)
      mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize) :
    (compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexBranchPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hcurrent hnext).payloadLength <=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexBranchPublicDirectPayloadEnvelopeOfGraph
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
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hcurrent hwitness.1 hwitness.2
  let innerResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchPublicDirectOfGraph_payloadLength_le
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hcurrent hwitness.1 hwitness.2
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
  change (castValuationContextProof hformula rawProof).payloadLength <= _
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le compilation sourceFormula
    hcoordinates.1
  exact hcoordinates.2

#print axioms
  compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexBranchPublicDirectOfGraph_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedBranchPublicDirectCompiler
