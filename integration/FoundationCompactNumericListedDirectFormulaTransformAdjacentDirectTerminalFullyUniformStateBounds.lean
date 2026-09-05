import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFullyUniformStateDirectFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalUniformFixedStatusBounds

/-!
# Adjacent terminal with uniform state and status resources

The adjacent-row child uses fixed state-row polynomials and keeps only the
checked transform-step public-finite resource visible.  Both status children
use their fixed numeric/bit-width polynomial.  No proof-dependent state
resource remains in this terminal.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalFullyUniformStateBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicAssemblyBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalBranchBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFullyUniformStateDirectFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectFixedBounds

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalFullyUniformStatePublicAssemblyEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat) : Nat :=
  compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope
    (compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicPayloadPolynomial
      tokenCount rowIndexTerm mode witnessStart witnessFinish witnessCount
      numericBound bitBound)
    (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound)
    (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound)
    (compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound)

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalFullyUniformStateAssemblyEnvelopeOfComponents
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound : Nat)
    (_currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (_currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (_nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (_nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (_components : ExplicitAdjacentStepDirectTerminalComponents valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound _currentCoordinates
      _currentSize _nextCoordinates _nextSize) : Nat :=
  compactFormulaTransformAdjacentStepDirectTerminalFullyUniformStatePublicAssemblyEnvelope
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound numericBound bitBound

theorem
    compactFormulaTransformAdjacentStepDirectTerminalFullyUniformStatePayloadEnvelope_le_assembly
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
        (compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepPayloadPolynomial
          tokenTable width tokenCount rowIndexTerm mode witnessStart
          witnessFinish witnessCount numericBound bitBound components.row)
        (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
          numericBound bitBound)
        (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
          numericBound bitBound) <=
      compactFormulaTransformAdjacentStepDirectTerminalFullyUniformStateAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        numericBound bitBound currentCoordinates currentSize nextCoordinates
        nextSize components := by
  have hold :=
    compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope_le_publicAssembly
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hcurrent hnext
      components
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalFullyUniformStateAssemblyEnvelopeOfComponents
    compactFormulaTransformAdjacentStepDirectTerminalFullyUniformStatePublicAssemblyEnvelope
    compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepPayloadPolynomial
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope
    compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope
    transparentHybridConjunctionPayloadEnvelope at hold ⊢
  dsimp only at hold ⊢
  omega

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFullyUniformStateDirectTerminalOfComponents
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
    (components : ExplicitAdjacentStepDirectTerminalComponents valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize) :
    ExplicitAdjacentStepBranchDirectTerminal valuation valueBound
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize)
      (compactFormulaTransformAdjacentStepDirectTerminalFullyUniformStateAssemblyEnvelopeOfComponents
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
  have hcurrentParserTokensCountRaw := hcurrent (7 : Fin 14)
  have hcurrentParserTasksCountRaw := hcurrent (5 : Fin 14)
  have hcurrentOutputCountRaw := hcurrent (3 : Fin 14)
  have hnextParserTokensCountRaw := hnext (7 : Fin 14)
  have hnextParserTasksCountRaw := hnext (5 : Fin 14)
  have hnextOutputCountRaw := hnext (3 : Fin 14)
  change currentCoordinates.parserTokensCount <= valueBound at hcurrentParserTokensCountRaw
  change currentCoordinates.parserTasksCount <= valueBound at hcurrentParserTasksCountRaw
  change currentCoordinates.outputCount <= valueBound at hcurrentOutputCountRaw
  change nextCoordinates.parserTokensCount <= valueBound at hnextParserTokensCountRaw
  change nextCoordinates.parserTasksCount <= valueBound at hnextParserTasksCountRaw
  change nextCoordinates.outputCount <= valueBound at hnextOutputCountRaw
  have hcurrentParserTokensCount :
      row.currentCoordinates.parserTokensCount <= numericBound := by
    rw [components.row_current_coordinates]
    exact hcurrentParserTokensCountRaw.trans hvalueBound
  have hcurrentParserTasksCount :
      row.currentCoordinates.parserTasksCount <= numericBound := by
    rw [components.row_current_coordinates]
    exact hcurrentParserTasksCountRaw.trans hvalueBound
  have hcurrentOutputCount :
      row.currentCoordinates.outputCount <= numericBound := by
    rw [components.row_current_coordinates]
    exact hcurrentOutputCountRaw.trans hvalueBound
  have hnextParserTokensCount :
      row.nextCoordinates.parserTokensCount <= numericBound := by
    rw [components.row_next_coordinates]
    exact hnextParserTokensCountRaw.trans hvalueBound
  have hnextParserTasksCount :
      row.nextCoordinates.parserTasksCount <= numericBound := by
    rw [components.row_next_coordinates]
    exact hnextParserTasksCountRaw.trans hvalueBound
  have hnextOutputCount :
      row.nextCoordinates.outputCount <= numericBound := by
    rw [components.row_next_coordinates]
    exact hnextOutputCountRaw.trans hvalueBound
  have hcurrentParserTokensBoundaryRaw := hcurrent (8 : Fin 14)
  have hcurrentParserTasksBoundaryRaw := hcurrent (6 : Fin 14)
  have hcurrentOutputBoundaryRaw := hcurrent (4 : Fin 14)
  have hnextParserTokensBoundaryRaw := hnext (8 : Fin 14)
  have hnextParserTasksBoundaryRaw := hnext (6 : Fin 14)
  have hnextOutputBoundaryRaw := hnext (4 : Fin 14)
  change currentCoordinates.parserTokensBoundary <= valueBound at hcurrentParserTokensBoundaryRaw
  change currentCoordinates.parserTasksBoundary <= valueBound at hcurrentParserTasksBoundaryRaw
  change currentCoordinates.outputBoundary <= valueBound at hcurrentOutputBoundaryRaw
  change nextCoordinates.parserTokensBoundary <= valueBound at hnextParserTokensBoundaryRaw
  change nextCoordinates.parserTasksBoundary <= valueBound at hnextParserTasksBoundaryRaw
  change nextCoordinates.outputBoundary <= valueBound at hnextOutputBoundaryRaw
  have hcurrentParserTokensTableSize :
      Nat.size row.currentCoordinates.parserTokensBoundary <= bitBound := by
    rw [components.row_current_coordinates]
    exact
      (Nat.size_le_size
        (hcurrentParserTokensBoundaryRaw.trans hvalueBound)).trans hnumericSize
  have hcurrentParserTasksTableSize :
      Nat.size row.currentCoordinates.parserTasksBoundary <= bitBound := by
    rw [components.row_current_coordinates]
    exact
      (Nat.size_le_size
        (hcurrentParserTasksBoundaryRaw.trans hvalueBound)).trans hnumericSize
  have hcurrentOutputTableSize :
      Nat.size row.currentCoordinates.outputBoundary <= bitBound := by
    rw [components.row_current_coordinates]
    exact
      (Nat.size_le_size
        (hcurrentOutputBoundaryRaw.trans hvalueBound)).trans hnumericSize
  have hnextParserTokensTableSize :
      Nat.size row.nextCoordinates.parserTokensBoundary <= bitBound := by
    rw [components.row_next_coordinates]
    exact
      (Nat.size_le_size
        (hnextParserTokensBoundaryRaw.trans hvalueBound)).trans hnumericSize
  have hnextParserTasksTableSize :
      Nat.size row.nextCoordinates.parserTasksBoundary <= bitBound := by
    rw [components.row_next_coordinates]
    exact
      (Nat.size_le_size
        (hnextParserTasksBoundaryRaw.trans hvalueBound)).trans hnumericSize
  have hnextOutputTableSize :
      Nat.size row.nextCoordinates.outputBoundary <= bitBound := by
    rw [components.row_next_coordinates]
    exact
      (Nat.size_le_size
        (hnextOutputBoundaryRaw.trans hvalueBound)).trans hnumericSize
  have hcurrentParserValueRaw : CompactUnifiedParserStateCoordinateValueBound
      currentCoordinates.parser numericBound := by
    intro coordinate
    fin_cases coordinate
    · have hvalue := hcurrent (13 : Fin 14)
      change currentCoordinates.start <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · have hvalue := hcurrent (11 : Fin 14)
      change currentCoordinates.parserFinish <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · have hvalue := hcurrent (10 : Fin 14)
      change currentCoordinates.parserTokensFinish <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · have hvalue := hcurrent (9 : Fin 14)
      change currentCoordinates.parserTasksFinish <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · exact hcurrentParserTokensBoundaryRaw.trans hvalueBound
    · exact hcurrentParserTokensCountRaw.trans hvalueBound
    · exact hcurrentParserTasksBoundaryRaw.trans hvalueBound
    · exact hcurrentParserTasksCountRaw.trans hvalueBound
  have hcurrentParserValue : CompactUnifiedParserStateCoordinateValueBound
      row.currentCoordinates.parser numericBound := by
    rw [components.row_current_coordinates]
    exact hcurrentParserValueRaw
  have hcurrentFinishRaw := hcurrent (12 : Fin 14)
  change currentCoordinates.finish <= valueBound at hcurrentFinishRaw
  have hcurrentRowFinish : row.currentCoordinates.finish <= numericBound := by
    rw [components.row_current_coordinates]
    exact hcurrentFinishRaw.trans hvalueBound
  have hnextParserValueRaw : CompactUnifiedParserStateCoordinateValueBound
      nextCoordinates.parser numericBound := by
    intro coordinate
    fin_cases coordinate
    · have hvalue := hnext (13 : Fin 14)
      change nextCoordinates.start <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · have hvalue := hnext (11 : Fin 14)
      change nextCoordinates.parserFinish <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · have hvalue := hnext (10 : Fin 14)
      change nextCoordinates.parserTokensFinish <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · have hvalue := hnext (9 : Fin 14)
      change nextCoordinates.parserTasksFinish <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · exact hnextParserTokensBoundaryRaw.trans hvalueBound
    · exact hnextParserTokensCountRaw.trans hvalueBound
    · exact hnextParserTasksBoundaryRaw.trans hvalueBound
    · exact hnextParserTasksCountRaw.trans hvalueBound
  have hnextParserValue : CompactUnifiedParserStateCoordinateValueBound
      row.nextCoordinates.parser numericBound := by
    rw [components.row_next_coordinates]
    exact hnextParserValueRaw
  have hnextFinishRaw := hnext (12 : Fin 14)
  change nextCoordinates.finish <= valueBound at hnextFinishRaw
  have hnextRowFinish : row.nextCoordinates.finish <= numericBound := by
    rw [components.row_next_coordinates]
    exact hnextFinishRaw.trans hvalueBound
  have hwitnessValue : CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound
      row.stepWitness numericBound := by
    intro coordinate
    fin_cases coordinate
    · have hvalue := components.values_le (8 : Fin 9)
      change row.stepWitness.slot0 <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · have hvalue := components.values_le (7 : Fin 9)
      change row.stepWitness.slot1 <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · have hvalue := components.values_le (6 : Fin 9)
      change row.stepWitness.slot2 <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · have hvalue := components.values_le (5 : Fin 9)
      change row.stepWitness.slot3 <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · have hvalue := components.values_le (4 : Fin 9)
      change row.stepWitness.slot4 <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · have hvalue := components.values_le (3 : Fin 9)
      change row.stepWitness.slot5 <= valueBound at hvalue
      exact hvalue.trans hvalueBound
    · have hvalue := components.values_le (2 : Fin 9)
      change row.stepWitness.slot6 <= valueBound at hvalue
      exact hvalue.trans hvalueBound
  have hconsumedCountRaw := components.values_le (1 : Fin 9)
  change row.consumedCount <= valueBound at hconsumedCountRaw
  have hconsumedCount : row.consumedCount <= numericBound :=
    hconsumedCountRaw.trans hvalueBound
  have hmappedHeadRaw := components.values_le (0 : Fin 9)
  change row.mappedHead <= valueBound at hmappedHeadRaw
  have hmappedHead : row.mappedHead <= numericBound :=
    hmappedHeadRaw.trans hvalueBound
  let rowBound :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepDirectBound
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount numericBound
      bitBound row hindexVariables components.row_graph hzero hwidthValue
      htokenCount hstateCount hcurrentParserTokensCount
      hcurrentParserTasksCount hcurrentOutputCount hnextParserTokensCount
      hnextParserTasksCount hnextOutputCount
      hcurrentParserValue hcurrentRowFinish hnextParserValue hnextRowFinish
      hwitnessValue hconsumedCount hmappedHead
      htokenTableSize hstateBoundarySize hcurrentParserTokensTableSize
      hcurrentParserTasksTableSize hcurrentOutputTableSize
      hnextParserTokensTableSize hnextParserTasksTableSize
      hnextOutputTableSize hnumericSize hnumericBit
  let rowResource :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepPayloadPolynomial
      tokenTable width tokenCount rowIndexTerm mode witnessStart witnessFinish
      witnessCount numericBound bitBound row
  let statusResource :=
    compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  have hcurrentStartRaw := hcurrent (9 : Fin 14)
  have hcurrentFinishRaw := hcurrent (11 : Fin 14)
  have hnextStartRaw := hnext (9 : Fin 14)
  have hnextFinishRaw := hnext (11 : Fin 14)
  change currentCoordinates.parserTasksFinish <= valueBound at hcurrentStartRaw
  change currentCoordinates.parserFinish <= valueBound at hcurrentFinishRaw
  change nextCoordinates.parserTasksFinish <= valueBound at hnextStartRaw
  change nextCoordinates.parserFinish <= valueBound at hnextFinishRaw
  have hcurrentStart :
      currentCoordinates.parserTasksFinish <= numericBound :=
    hcurrentStartRaw.trans hvalueBound
  have hcurrentFinish :
      currentCoordinates.parserFinish <= numericBound :=
    hcurrentFinishRaw.trans hvalueBound
  have hnextStart : nextCoordinates.parserTasksFinish <= numericBound :=
    hnextStartRaw.trans hvalueBound
  have hnextFinish : nextCoordinates.parserFinish <= numericBound :=
    hnextFinishRaw.trans hvalueBound
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
    compactFormulaTransformAdjacentStepDirectTerminalFullyUniformStatePayloadEnvelope_le_assembly
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound numericBound
      bitBound currentCoordinates currentSize nextCoordinates nextSize hcurrent
      hnext components
  have hterminalPublic : terminalProof.payloadLength <=
      compactFormulaTransformAdjacentStepDirectTerminalFullyUniformStateAssemblyEnvelopeOfComponents
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
      compactFormulaTransformAdjacentStepDirectTerminalFullyUniformStateAssemblyEnvelopeOfComponents
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
  compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexFullyUniformStateDirectTerminalOfComponents

end FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalFullyUniformStateBounds
