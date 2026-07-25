import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalBranchBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedFixedWidthEntryBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectCompiler

/-!
# Fixed-core adjacent direct terminal

This layer keeps the audited current/next status branches and connector bound,
but replaces the adjacent-row child by the fixed-core direct endpoint.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalFixedCoreBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexBranchDirectBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicAssemblyBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalBranchBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedBranchDirectCompiler
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedFixedWidthEntryBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectCompiler

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAssemblyEnvelopeOfComponents
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (components : ExplicitAdjacentStepDirectTerminalComponents valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize) : Nat :=
  compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope
    (compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount components.row
      components.row_graph)
    (compactBinaryNatStatusValidBoundedUniformDirectPayloadEnvelopeOfGraph
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound components.current_status)
    (compactBinaryNatStatusValidBoundedUniformDirectPayloadEnvelopeOfGraph
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound components.next_status)
    (compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound)

theorem
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePayloadEnvelope_le_publicAssembly
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
    (components : ExplicitAdjacentStepDirectTerminalComponents valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize) :
    compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope
        valuation
        (compactFormulaTransformAdjacentStepRowAtValuationIndexFormula
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount components.row)
        (compactBinaryNatStatusValidBoundedClosedFormula tokenTable width
          tokenCount currentCoordinates.parserTasksFinish
          currentCoordinates.parserFinish valueBound)
        (compactBinaryNatStatusValidBoundedClosedFormula tokenTable width
          tokenCount nextCoordinates.parserTasksFinish
          nextCoordinates.parserFinish valueBound)
        (compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope
          valuation tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount
          components.row components.row_graph)
        (compactBinaryNatStatusValidBoundedUniformDirectPayloadEnvelopeOfGraph
          tokenTable width tokenCount currentCoordinates.parserTasksFinish
          currentCoordinates.parserFinish valueBound components.current_status)
        (compactBinaryNatStatusValidBoundedUniformDirectPayloadEnvelopeOfGraph
          tokenTable width tokenCount nextCoordinates.parserTasksFinish
          nextCoordinates.parserFinish valueBound components.next_status) <=
      compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize components := by
  have hold :=
    compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope_le_publicAssembly
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize
      hcurrent hnext components
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAssemblyEnvelopeOfComponents
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope
    compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope
    transparentHybridConjunctionPayloadEnvelope at hold ⊢
  dsimp only at hold ⊢
  omega

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFiniteStepAssemblyEnvelopeOfComponents
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (components : ExplicitAdjacentStepDirectTerminalComponents valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize) : Nat :=
  compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope
    (compactFormulaTransformAdjacentStepRowAtValuationIndexFixedCorePublicFiniteDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount components.row)
    (compactBinaryNatStatusValidBoundedUniformDirectPayloadEnvelopeOfGraph
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound components.current_status)
    (compactBinaryNatStatusValidBoundedUniformDirectPayloadEnvelopeOfGraph
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound components.next_status)
    (compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound)

theorem
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAssemblyEnvelopeOfComponents_le_publicFiniteStep
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (components : ExplicitAdjacentStepDirectTerminalComponents valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0}) :
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize components <=
      compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFiniteStepAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize components := by
  have hrow :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope_le_publicFinite
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount components.row
      components.row_graph hindexVariables
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAssemblyEnvelopeOfComponents
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFiniteStepAssemblyEnvelopeOfComponents
    compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope
  omega

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteAssemblyEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates nextCoordinates :
      CompactFormulaTransformStateRowCoordinates)
    (row : CompactFormulaTransformAdjacentStepRow) : Nat :=
  compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope
    (compactFormulaTransformAdjacentStepRowAtValuationIndexFixedCorePublicFiniteDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount row)
    (compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectPayloadEnvelope
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound)
    (compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectPayloadEnvelope
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound)
    (compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound)

theorem
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFinitePayloadEnvelope_le_assembly
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
    (components : ExplicitAdjacentStepDirectTerminalComponents valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize) :
    compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope
        valuation
        (compactFormulaTransformAdjacentStepRowAtValuationIndexFormula
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount components.row)
        (compactBinaryNatStatusValidBoundedClosedFormula tokenTable width
          tokenCount currentCoordinates.parserTasksFinish
          currentCoordinates.parserFinish valueBound)
        (compactBinaryNatStatusValidBoundedClosedFormula tokenTable width
          tokenCount nextCoordinates.parserTasksFinish
          nextCoordinates.parserFinish valueBound)
        (compactFormulaTransformAdjacentStepRowAtValuationIndexFixedCorePublicFiniteDirectPayloadEnvelope
          valuation tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount
          components.row)
        (compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectPayloadEnvelope
          tokenTable width tokenCount currentCoordinates.parserTasksFinish
          currentCoordinates.parserFinish valueBound)
        (compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectPayloadEnvelope
          tokenTable width tokenCount nextCoordinates.parserTasksFinish
          nextCoordinates.parserFinish valueBound) <=
      compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteAssemblyEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates nextCoordinates components.row := by
  have hold :=
    compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope_le_publicAssembly
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hcurrent hnext
      components
  unfold compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope at hold ⊢
  unfold compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope at hold
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteAssemblyEnvelope
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope
  unfold transparentHybridConjunctionPayloadEnvelope at hold ⊢
  dsimp only at hold ⊢
  omega

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFixedCoreDirectTerminalOfComponents
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
    (components : ExplicitAdjacentStepDirectTerminalComponents valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize) :
    ExplicitAdjacentStepBranchDirectTerminal valuation valueBound
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize)
      (compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize components) := by
  let row := components.row
  let values := boundedWitnessValues row
  let rowFormula :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexFormula
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount row
  let currentFormula := compactBinaryNatStatusValidBoundedClosedFormula
    tokenTable width tokenCount currentCoordinates.parserTasksFinish
    currentCoordinates.parserFinish valueBound
  let nextFormula := compactBinaryNatStatusValidBoundedClosedFormula
    tokenTable width tokenCount nextCoordinates.parserTasksFinish
    nextCoordinates.parserFinish valueBound
  let rowBound :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreExplicitDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount row components.row_graph
  let currentProof :=
    compileCompactBinaryNatStatusValidBoundedUniformDirectAtValuationOfGraph
      valuation tokenTable width tokenCount
      currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
      valueBound components.current_status
  let nextProof :=
    compileCompactBinaryNatStatusValidBoundedUniformDirectAtValuationOfGraph
      valuation tokenTable width tokenCount
      nextCoordinates.parserTasksFinish nextCoordinates.parserFinish
      valueBound components.next_status
  let rowResource :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount row components.row_graph
  let currentResource :=
    compactBinaryNatStatusValidBoundedUniformDirectPayloadEnvelopeOfGraph
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound components.current_status
  let nextResource :=
    compactBinaryNatStatusValidBoundedUniformDirectPayloadEnvelopeOfGraph
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound components.next_status
  let publicResource :=
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAssemblyEnvelopeOfComponents
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize components
  have hcurrentProof : currentProof.payloadLength <= currentResource :=
    compileCompactBinaryNatStatusValidBoundedUniformDirectAtValuationOfGraph_payloadLength_le
      valuation tokenTable width tokenCount
      currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
      valueBound components.current_status
  have hnextProof : nextProof.payloadLength <= nextResource :=
    compileCompactBinaryNatStatusValidBoundedUniformDirectAtValuationOfGraph_payloadLength_le
      valuation tokenTable width tokenCount
      nextCoordinates.parserTasksFinish nextCoordinates.parserFinish valueBound
      components.next_status
  let innerProof := compileDirectConjunction currentProof nextProof
  have hinner := compileDirectConjunction_payloadLength_le currentProof nextProof
    currentResource nextResource hcurrentProof hnextProof
  let terminalProof := compileDirectConjunction rowBound.proof innerProof
  have hterminal := compileDirectConjunction_payloadLength_le rowBound.proof
    innerProof rowResource
    (transparentHybridConjunctionPayloadEnvelope valuation currentFormula
      nextFormula currentResource nextResource)
    rowBound.payloadLength_le hinner
  have hassembly :=
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePayloadEnvelope_le_publicAssembly
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hcurrent hnext components
  have hterminalExact : terminalProof.payloadLength <=
      compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope
        valuation rowFormula currentFormula nextFormula rowResource
        currentResource nextResource := by
    simpa only [terminalProof, innerProof,
      compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope]
      using hterminal
  have hterminalPublic : terminalProof.payloadLength <= publicResource := by
    exact hterminalExact.trans (by
      simpa only [row, rowFormula, currentFormula, nextFormula, rowResource,
        currentResource, nextResource, publicResource] using hassembly)
  let rawBody := compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
    tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
    witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize nextCoordinates nextSize
  have hformula : rawBody ⇜
        (fun index => shortBinaryNumeralTerm (values index)) =
      rowFormula ⋏ (currentFormula ⋏ nextFormula) := by
    have hraw :=
      compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_alignment
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound row
    rw [components.row_current_coordinates, components.row_current_size,
      components.row_next_coordinates, components.row_next_size] at hraw
    simpa only [rawBody, values, row, rowFormula, currentFormula, nextFormula]
      using hraw
  let terminal := castValuationContextProof hformula.symm terminalProof
  have hterminalResource : terminal.payloadLength <= publicResource := by
    change (castValuationContextProof hformula.symm terminalProof).payloadLength <= _
    rw [castValuationContextProof_payloadLength_eq]
    exact hterminalPublic
  exact
    { values := values
      values_le := components.values_le
      terminal := terminal
      terminal_payloadLength_le := hterminalResource }

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFixedCorePublicFullyFiniteDirectTerminalOfComponents
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
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0})
    (components : ExplicitAdjacentStepDirectTerminalComponents valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize) :
    ExplicitAdjacentStepBranchDirectTerminal valuation valueBound
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize)
      (compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteAssemblyEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates nextCoordinates components.row) := by
  let row := components.row
  let values := boundedWitnessValues row
  let rowFormula :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexFormula
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount row
  let currentFormula := compactBinaryNatStatusValidBoundedClosedFormula
    tokenTable width tokenCount currentCoordinates.parserTasksFinish
    currentCoordinates.parserFinish valueBound
  let nextFormula := compactBinaryNatStatusValidBoundedClosedFormula
    tokenTable width tokenCount nextCoordinates.parserTasksFinish
    nextCoordinates.parserFinish valueBound
  let rowBound :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreExplicitDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount row components.row_graph
  let currentProof :=
    compileCompactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectAtValuationOfGraph
      valuation tokenTable width tokenCount
      currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
      valueBound components.current_status
  let nextProof :=
    compileCompactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectAtValuationOfGraph
      valuation tokenTable width tokenCount
      nextCoordinates.parserTasksFinish nextCoordinates.parserFinish
      valueBound components.next_status
  let rowResource :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexFixedCorePublicFiniteDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount row
  let currentResource :=
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectPayloadEnvelope
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound
  let nextResource :=
    compactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectPayloadEnvelope
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound
  let publicResource :=
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteAssemblyEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      nextCoordinates row
  have hrowProof : rowBound.proof.payloadLength <= rowResource :=
    rowBound.payloadLength_le.trans
      (compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope_le_publicFinite
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount row
        components.row_graph hindexVariables)
  have hcurrentProof : currentProof.payloadLength <= currentResource :=
    compileCompactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectAtValuationOfGraph_payloadLength_le
      valuation tokenTable width tokenCount
      currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
      valueBound components.current_status
  have hnextProof : nextProof.payloadLength <= nextResource :=
    compileCompactBinaryNatStatusValidBoundedCanonicalFixedWidthEntryPublicFiniteDirectAtValuationOfGraph_payloadLength_le
      valuation tokenTable width tokenCount
      nextCoordinates.parserTasksFinish nextCoordinates.parserFinish valueBound
      components.next_status
  let innerProof := compileDirectConjunction currentProof nextProof
  have hinner := compileDirectConjunction_payloadLength_le currentProof nextProof
    currentResource nextResource hcurrentProof hnextProof
  let terminalProof := compileDirectConjunction rowBound.proof innerProof
  have hterminal := compileDirectConjunction_payloadLength_le rowBound.proof
    innerProof rowResource
    (transparentHybridConjunctionPayloadEnvelope valuation currentFormula
      nextFormula currentResource nextResource)
    hrowProof hinner
  have hassembly :=
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFinitePayloadEnvelope_le_assembly
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hcurrent hnext components
  have hterminalExact : terminalProof.payloadLength <=
      compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope
        valuation rowFormula currentFormula nextFormula rowResource
        currentResource nextResource := by
    simpa only [terminalProof, innerProof,
      compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope]
      using hterminal
  have hterminalPublic : terminalProof.payloadLength <= publicResource := by
    exact hterminalExact.trans (by
      simpa only [row, rowFormula, currentFormula, nextFormula, rowResource,
        currentResource, nextResource, publicResource] using hassembly)
  let rawBody := compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
    tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
    witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize nextCoordinates nextSize
  have hformula : rawBody ⇜
        (fun index => shortBinaryNumeralTerm (values index)) =
      rowFormula ⋏ (currentFormula ⋏ nextFormula) := by
    have hraw :=
      compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_alignment
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound row
    rw [components.row_current_coordinates, components.row_current_size,
      components.row_next_coordinates, components.row_next_size] at hraw
    simpa only [rawBody, values, row, rowFormula, currentFormula, nextFormula]
      using hraw
  let terminal := castValuationContextProof hformula.symm terminalProof
  have hterminalResource : terminal.payloadLength <= publicResource := by
    change (castValuationContextProof hformula.symm terminalProof).payloadLength <= _
    rw [castValuationContextProof_payloadLength_eq]
    exact hterminalPublic
  exact
    { values := values
      values_le := components.values_le
      terminal := terminal
      terminal_payloadLength_le := hterminalResource }

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFixedCoreDirectTerminalOfGraph
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
    ExplicitAdjacentStepBranchDirectTerminal valuation valueBound
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize)
      (compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize
        (explicitAdjacentStepDirectTerminalComponentsOfGraph valuation tokenTable
          width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize nextCoordinates nextSize hbounded)) :=
  compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFixedCoreDirectTerminalOfComponents
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize nextCoordinates nextSize hcurrent hnext
    (explicitAdjacentStepDirectTerminalComponentsOfGraph valuation tokenTable
      width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound currentCoordinates currentSize
      nextCoordinates nextSize hbounded)

#print axioms
  compactFormulaTransformAdjacentStepDirectTerminalFixedCorePayloadEnvelope_le_publicAssembly
#print axioms
  compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAssemblyEnvelopeOfComponents_le_publicFiniteStep
#print axioms
  compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFixedCoreDirectTerminalOfGraph

end FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalFixedCoreBounds
