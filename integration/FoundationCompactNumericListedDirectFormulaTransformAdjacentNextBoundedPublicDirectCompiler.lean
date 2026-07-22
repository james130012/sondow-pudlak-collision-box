import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedPublicDirectCompiler
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity14

/-! # Public direct compiler for the fourteen next-state witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedPublicDirectCompiler

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
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedPublicDirectCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds

noncomputable def
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
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
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size
      (compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize hnext).2
  explicitBoundedWitnessDirectPublicPayloadEnvelope 14
    (compactFormulaTransformAdjacentPublicContextCodeBound
      valuation rowIndexTerm)
    valueBound
    (compactFormulaTransformAdjacentNextRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound)
    innerResource

noncomputable def
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded tokenTable width tokenCount
      stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize) : Nat :=
  let witness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize hnext
  let innerResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
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

theorem
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph_eq_publicFinite
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hnext : CompactFormulaTransformAdjacentNextBounded tokenTable width tokenCount
      stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0}) :
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize hnext =
      compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize hnext := by
  unfold
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
  simp only [
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph_eq_publicFinite
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize
      (compactFormulaTransformAdjacentNextBounded_witnessOfGraph valuation
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize hnext).coordinates
      (compactFormulaTransformAdjacentNextBounded_witnessOfGraph valuation
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize hnext).size
      (compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec valuation
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize hnext).2 hindexVariables]

noncomputable def
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound)
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
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hcurrent hwitness.1 hwitness.2
  let innerResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le
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
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound)
    (hnext : CompactFormulaTransformAdjacentNextBounded
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation rowIndexTerm) mode witnessStart witnessFinish
      witnessCount valueBound currentCoordinates currentSize) :
    (compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hcurrent hnext).payloadLength <=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
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
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hcurrent hwitness.1 hwitness.2
  let innerResource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize witness.coordinates witness.size hwitness.2
  have hinner : innerDirect.payloadLength <= innerResource :=
    compileCompactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le
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

theorem
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le_publicFinite
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound)
    (hnext : CompactFormulaTransformAdjacentNextBounded tokenTable width tokenCount
      stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0}) :
    (compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hcurrent hnext).payloadLength <=
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hnext := by
  rw [←
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectPayloadEnvelopeOfGraph_eq_publicFinite
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hnext hindexVariables]
  exact
    compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize hcurrent hnext

#print axioms
  compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le
#print axioms
  compileCompactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicDirectOfGraph_payloadLength_le_publicFinite

end FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedPublicDirectCompiler
