import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalFixedCoreBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectFixedBounds

/-!
# Adjacent terminal with fixed status resources

The row proof remains visible, while both bounded status children are charged
to the same numeric/bit-width polynomial.  This removes the finite output-value
enumeration from the adjacent terminal without hiding the remaining row cost.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalUniformFixedStatusBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
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
open FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalFixedCoreBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectFixedBounds

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalUniformFixedStatusAssemblyEnvelopeOfComponents
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat)
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
    (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound)
    (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound)
    (compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound)

theorem
    compactFormulaTransformAdjacentStepDirectTerminalUniformFixedStatusPayloadEnvelope_le_assembly
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat)
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
        (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
          numericBound bitBound)
        (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
          numericBound bitBound) <=
      compactFormulaTransformAdjacentStepDirectTerminalUniformFixedStatusAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        numericBound bitBound currentCoordinates currentSize nextCoordinates
        nextSize components := by
  have hold :=
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePayloadEnvelope_le_publicAssembly
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hcurrent hnext
      components
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAssemblyEnvelopeOfComponents at hold
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalUniformFixedStatusAssemblyEnvelopeOfComponents
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope
    compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope
    transparentHybridConjunctionPayloadEnvelope at hold ⊢
  dsimp only at hold ⊢
  omega

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformFixedStatusDirectTerminalOfComponents
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat)
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
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (components : ExplicitAdjacentStepDirectTerminalComponents valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize) :
    ExplicitAdjacentStepBranchDirectTerminal valuation valueBound
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize)
      (compactFormulaTransformAdjacentStepDirectTerminalUniformFixedStatusAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        numericBound bitBound currentCoordinates currentSize nextCoordinates
        nextSize components) := by
  let row := components.row
  let values := boundedWitnessValues row
  let rowFormula :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexFormula tokenTable
      width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount row
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
  let rowResource :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedFixedCoreDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount row components.row_graph
  let statusResource :=
    compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  have hcurrentStartRaw := hcurrent (9 : Fin 14)
  have hcurrentFinishRaw := hcurrent (11 : Fin 14)
  have hnextStartRaw := hnext (9 : Fin 14)
  have hnextFinishRaw := hnext (11 : Fin 14)
  have hcurrentStart : currentCoordinates.parserTasksFinish <= numericBound := by
    change currentCoordinates.parserTasksFinish <= valueBound at hcurrentStartRaw
    exact hcurrentStartRaw.trans hvalueBound
  have hcurrentFinish : currentCoordinates.parserFinish <= numericBound := by
    change currentCoordinates.parserFinish <= valueBound at hcurrentFinishRaw
    exact hcurrentFinishRaw.trans hvalueBound
  have hnextStart : nextCoordinates.parserTasksFinish <= numericBound := by
    change nextCoordinates.parserTasksFinish <= valueBound at hnextStartRaw
    exact hnextStartRaw.trans hvalueBound
  have hnextFinish : nextCoordinates.parserFinish <= numericBound := by
    change nextCoordinates.parserFinish <= valueBound at hnextFinishRaw
    exact hnextFinishRaw.trans hvalueBound
  let currentProof :=
    compileCompactBinaryNatStatusValidBoundedUniformDirectFixedAtValuationOfGraph
      valuation tokenTable width tokenCount
      currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
      valueBound numericBound bitBound components.current_status hvalueBound
      hwidthValue htokenCount hcurrentStart hcurrentFinish hareaNumeric hareaBit
      htokenTableSize hnumericSize hbitPositive
  let nextProof :=
    compileCompactBinaryNatStatusValidBoundedUniformDirectFixedAtValuationOfGraph
      valuation tokenTable width tokenCount
      nextCoordinates.parserTasksFinish nextCoordinates.parserFinish valueBound
      numericBound bitBound components.next_status hvalueBound hwidthValue
      htokenCount hnextStart hnextFinish hareaNumeric hareaBit htokenTableSize
      hnumericSize hbitPositive
  have hcurrentProof : currentProof.payloadLength <= statusResource := by
    simpa only [currentProof, statusResource] using
      compileCompactBinaryNatStatusValidBoundedUniformDirectFixedAtValuationOfGraph_payloadLength_le
        valuation tokenTable width tokenCount
        currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
        valueBound numericBound bitBound components.current_status hvalueBound
        hwidthValue htokenCount hcurrentStart hcurrentFinish hareaNumeric
        hareaBit htokenTableSize hnumericSize hbitPositive
  have hnextProof : nextProof.payloadLength <= statusResource := by
    simpa only [nextProof, statusResource] using
      compileCompactBinaryNatStatusValidBoundedUniformDirectFixedAtValuationOfGraph_payloadLength_le
        valuation tokenTable width tokenCount
        nextCoordinates.parserTasksFinish nextCoordinates.parserFinish
        valueBound numericBound bitBound components.next_status hvalueBound
        hwidthValue htokenCount hnextStart hnextFinish hareaNumeric hareaBit
        htokenTableSize hnumericSize hbitPositive
  let innerProof := compileDirectConjunction currentProof nextProof
  have hinner := compileDirectConjunction_payloadLength_le currentProof
    nextProof statusResource statusResource hcurrentProof hnextProof
  let terminalProof := compileDirectConjunction rowBound.proof innerProof
  have hterminal := compileDirectConjunction_payloadLength_le rowBound.proof
    innerProof rowResource
    (transparentHybridConjunctionPayloadEnvelope valuation currentFormula
      nextFormula statusResource statusResource)
    rowBound.payloadLength_le hinner
  have hassembly :=
    compactFormulaTransformAdjacentStepDirectTerminalUniformFixedStatusPayloadEnvelope_le_assembly
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound currentCoordinates currentSize nextCoordinates nextSize hcurrent
      hnext components
  have hterminalPublic : terminalProof.payloadLength <=
      compactFormulaTransformAdjacentStepDirectTerminalUniformFixedStatusAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        numericBound bitBound currentCoordinates currentSize nextCoordinates
        nextSize components := by
    exact hterminal.trans (by
      simpa only [row, rowFormula, currentFormula, nextFormula, rowResource,
        statusResource,
        compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope]
        using hassembly)
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
  have hterminalResource : terminal.payloadLength <=
      compactFormulaTransformAdjacentStepDirectTerminalUniformFixedStatusAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        numericBound bitBound currentCoordinates currentSize nextCoordinates
        nextSize components := by
    change (castValuationContextProof hformula.symm terminalProof).payloadLength
      <= _
    rw [castValuationContextProof_payloadLength_eq]
    exact hterminalPublic
  exact
    { values := values
      values_le := components.values_le
      terminal := terminal
      terminal_payloadLength_le := hterminalResource }

#print axioms
  compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexUniformFixedStatusDirectTerminalOfComponents

end FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalUniformFixedStatusBounds
