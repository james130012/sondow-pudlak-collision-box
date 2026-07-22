import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicAssemblyBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedBranchDirectCompiler

/-!
# Branch-sensitive adjacent direct terminal

The two status children use their checked running/failed/completed branches.
No resource in this file enumerates all values in `0 .. valueBound`.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalBranchBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicAssemblyBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedBranchDirectCompiler

private theorem binaryFormulaCode_left_length_le_conjunction_branch
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_length_le_conjunction_branch
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope
    (valuation : Nat -> Nat)
    (rowFormula currentFormula nextFormula : ValuationFormula)
    (rowResource currentResource nextResource : Nat) : Nat :=
  transparentHybridConjunctionPayloadEnvelope valuation rowFormula
    (currentFormula ⋏ nextFormula) rowResource
    (transparentHybridConjunctionPayloadEnvelope valuation currentFormula
      nextFormula currentResource nextResource)

def compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope
    (rowResource currentResource nextResource syntaxResource : Nat) : Nat :=
  rowResource + currentResource + nextResource +
    6 * generalContextAssemblyEnvelope syntaxResource

theorem
    compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope_le_publicAssembly_of_connector
    (valuation : Nat -> Nat)
    (rowFormula currentFormula nextFormula : ValuationFormula)
    (rowResource currentResource nextResource syntaxResource : Nat)
    (hconnector :
      weakeningFullAssemblyCost
          (insert rowFormula
            (valuationContext
              (rowFormula ⋏ (currentFormula ⋏ nextFormula)).freeVariables
              valuation)) +
        weakeningFullAssemblyCost
          (insert currentFormula
            (valuationContext
              (currentFormula ⋏ nextFormula).freeVariables valuation)) +
        weakeningFullAssemblyCost
          (insert nextFormula
            (valuationContext
              (currentFormula ⋏ nextFormula).freeVariables valuation)) +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          (valuationContext
            (currentFormula ⋏ nextFormula).freeVariables valuation)
          currentFormula nextFormula +
        weakeningFullAssemblyCost
          (insert (currentFormula ⋏ nextFormula)
            (valuationContext
              (rowFormula ⋏ (currentFormula ⋏ nextFormula)).freeVariables
              valuation)) +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          (valuationContext
            (rowFormula ⋏ (currentFormula ⋏ nextFormula)).freeVariables
            valuation)
          rowFormula (currentFormula ⋏ nextFormula) <=
        6 * generalContextAssemblyEnvelope syntaxResource) :
    compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope
        valuation rowFormula currentFormula nextFormula rowResource
        currentResource nextResource <=
      compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope
        rowResource currentResource nextResource syntaxResource := by
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope
    compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope
    transparentHybridConjunctionPayloadEnvelope
  dsimp only
  omega

theorem
    compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope_le_publicAssembly
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
        (compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope
          valuation tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount
          components.row components.row_graph)
        (compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
          tokenTable width tokenCount currentCoordinates.parserTasksFinish
          currentCoordinates.parserFinish valueBound components.current_status)
        (compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
          tokenTable width tokenCount nextCoordinates.parserTasksFinish
          nextCoordinates.parserFinish valueBound components.next_status) <=
      compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelope
        (compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope
          valuation tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount
          components.row components.row_graph)
        (compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
          tokenTable width tokenCount currentCoordinates.parserTasksFinish
          currentCoordinates.parserFinish valueBound components.current_status)
        (compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
          tokenTable width tokenCount nextCoordinates.parserTasksFinish
          nextCoordinates.parserFinish valueBound components.next_status)
        (compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
          valuation tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound) := by
  let row := components.row
  let rawBody := compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
    tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
    witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize nextCoordinates nextSize
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
  let innerFormula := currentFormula ⋏ nextFormula
  let terminalFormula := rowFormula ⋏ innerFormula
  let contextCodeBound :=
    compactFormulaTransformAdjacentPublicContextCodeBound valuation rowIndexTerm
  let terminalCodeBound :=
    compactFormulaTransformAdjacentStepInstalledTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  let syntaxResource :=
    compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound
  let rowResource :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount row components.row_graph
  let currentResource :=
    compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound components.current_status
  let nextResource :=
    compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound components.next_status
  have hrawCode : (binaryFormulaCode rawBody).length <=
      compactFormulaTransformAdjacentStepRawTerminalPublicCodeEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound :=
    compactFormulaTransformAdjacentStepRawTerminal_code_length_le_public
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hcurrent hnext
  have halignment : rawBody ⇜
        (fun index => shortBinaryNumeralTerm (values index)) =
      terminalFormula := by
    have hraw :=
      compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_alignment
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound row
    rw [components.row_current_coordinates, components.row_current_size,
      components.row_next_coordinates, components.row_next_size] at hraw
    simpa only [rawBody, values, row, rowFormula, currentFormula, nextFormula,
      innerFormula, terminalFormula] using hraw
  have hterminalCode : (binaryFormulaCode terminalFormula).length <=
      terminalCodeBound := by
    have hinstalled := explicitWitnessInstalledFormula_code_length_le_public
      valueBound
      (compactFormulaTransformAdjacentStepRawTerminalPublicCodeEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound)
      rawBody values components.values_le hrawCode
    rw [halignment] at hinstalled
    simpa only [terminalCodeBound,
      compactFormulaTransformAdjacentStepInstalledTerminalPublicCodeEnvelope]
      using hinstalled
  have hrowCode : (binaryFormulaCode rowFormula).length <= terminalCodeBound :=
    (binaryFormulaCode_left_length_le_conjunction_branch
      rowFormula innerFormula).trans hterminalCode
  have hinnerCode : (binaryFormulaCode innerFormula).length <=
      terminalCodeBound :=
    (binaryFormulaCode_right_length_le_conjunction_branch
      rowFormula innerFormula).trans hterminalCode
  have hcurrentCode : (binaryFormulaCode currentFormula).length <=
      terminalCodeBound :=
    (binaryFormulaCode_left_length_le_conjunction_branch
      currentFormula nextFormula).trans hinnerCode
  have hnextCode : (binaryFormulaCode nextFormula).length <=
      terminalCodeBound :=
    (binaryFormulaCode_right_length_le_conjunction_branch
      currentFormula nextFormula).trans hinnerCode
  have hrawContext : formulaCodeSum
      (valuationContext rawBody.freeVariables valuation) <= contextCodeBound :=
    compactFormulaTransformAdjacentStepRawTerminal_context_le_public
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize
  have hterminalContext : formulaCodeSum
      (valuationContext terminalFormula.freeVariables valuation) <=
        contextCodeBound := by
    have hinstalledContext := formulaCodeSum_mono
      (valuationContext_mono valuation
        (explicitWitnessInstalledFormula_freeVariables_subset rawBody values))
    rw [halignment] at hinstalledContext
    exact hinstalledContext.trans hrawContext
  have hinnerVariables : innerFormula.freeVariables ⊆
      terminalFormula.freeVariables := by
    simp [terminalFormula]
  have hinnerContext : formulaCodeSum
      (valuationContext innerFormula.freeVariables valuation) <=
        contextCodeBound :=
    (formulaCodeSum_mono
      (valuationContext_mono valuation hinnerVariables)).trans
        hterminalContext
  have hsyntaxPositive : 1 <= syntaxResource := by
    unfold syntaxResource
      compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
    omega
  have hcontextSyntax : contextCodeBound <= syntaxResource := by
    unfold syntaxResource
      compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
    omega
  have hcodeSyntax : terminalCodeBound <= syntaxResource := by
    unfold syntaxResource
      compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
    omega
  have hrowCodeSyntax := hrowCode.trans hcodeSyntax
  have hinnerCodeSyntax := hinnerCode.trans hcodeSyntax
  have hcurrentCodeSyntax := hcurrentCode.trans hcodeSyntax
  have hnextCodeSyntax := hnextCode.trans hcodeSyntax
  have hterminalCodeSyntax := hterminalCode.trans hcodeSyntax
  have hterminalContextSyntax := hterminalContext.trans hcontextSyntax
  have hinnerContextSyntax := hinnerContext.trans hcontextSyntax
  have hweakRowSum : formulaCodeSum
      (insert rowFormula
        (valuationContext terminalFormula.freeVariables valuation)) <=
      generalContextCoordinate syntaxResource := by
    have hsum := formulaCodeSum_insert_le
      (valuationContext terminalFormula.freeVariables valuation) rowFormula
    unfold generalContextCoordinate
    omega
  have hweakCurrentSum : formulaCodeSum
      (insert currentFormula
        (valuationContext innerFormula.freeVariables valuation)) <=
      generalContextCoordinate syntaxResource := by
    have hsum := formulaCodeSum_insert_le
      (valuationContext innerFormula.freeVariables valuation) currentFormula
    unfold generalContextCoordinate
    omega
  have hweakNextSum : formulaCodeSum
      (insert nextFormula
        (valuationContext innerFormula.freeVariables valuation)) <=
      generalContextCoordinate syntaxResource := by
    have hsum := formulaCodeSum_insert_le
      (valuationContext innerFormula.freeVariables valuation) nextFormula
    unfold generalContextCoordinate
    omega
  have hweakInnerSum : formulaCodeSum
      (insert innerFormula
        (valuationContext terminalFormula.freeVariables valuation)) <=
      generalContextCoordinate syntaxResource := by
    have hsum := formulaCodeSum_insert_le
      (valuationContext terminalFormula.freeVariables valuation) innerFormula
    unfold generalContextCoordinate
    omega
  have hweakRow := weakeningFullAssemblyCost_le_general _ syntaxResource
    hweakRowSum
  have hweakCurrent := weakeningFullAssemblyCost_le_general _ syntaxResource
    hweakCurrentSum
  have hweakNext := weakeningFullAssemblyCost_le_general _ syntaxResource
    hweakNextSum
  have hweakInner := weakeningFullAssemblyCost_le_general _ syntaxResource
    hweakInnerSum
  have hconjunctionInner := conjunctionFullAssemblyCost_le_general
    (valuationContext innerFormula.freeVariables valuation)
    currentFormula nextFormula syntaxResource hsyntaxPositive
    hinnerContextSyntax hcurrentCodeSyntax hnextCodeSyntax hinnerCodeSyntax
  have hconjunctionOuter := conjunctionFullAssemblyCost_le_general
    (valuationContext terminalFormula.freeVariables valuation)
    rowFormula innerFormula syntaxResource hsyntaxPositive
    hterminalContextSyntax hrowCodeSyntax hinnerCodeSyntax
    hterminalCodeSyntax
  have hconnector :
      weakeningFullAssemblyCost
          (insert rowFormula
            (valuationContext terminalFormula.freeVariables valuation)) +
        weakeningFullAssemblyCost
          (insert currentFormula
            (valuationContext innerFormula.freeVariables valuation)) +
        weakeningFullAssemblyCost
          (insert nextFormula
            (valuationContext innerFormula.freeVariables valuation)) +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          (valuationContext innerFormula.freeVariables valuation)
          currentFormula nextFormula +
        weakeningFullAssemblyCost
          (insert innerFormula
            (valuationContext terminalFormula.freeVariables valuation)) +
        CertifiedPAContextProof.conjunctionFullAssemblyCost
          (valuationContext terminalFormula.freeVariables valuation)
          rowFormula innerFormula <=
        6 * generalContextAssemblyEnvelope syntaxResource := by
    omega
  simpa only [row, rowFormula, currentFormula, nextFormula, innerFormula,
    terminalFormula, rowResource, currentResource, nextResource,
    syntaxResource] using
    (compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope_le_publicAssembly_of_connector
      valuation rowFormula currentFormula nextFormula rowResource
      currentResource nextResource syntaxResource hconnector)

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelopeOfComponents
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
    (compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount components.row
      components.row_graph)
    (compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound components.current_status)
    (compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound components.next_status)
    (compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound)

structure ExplicitAdjacentStepBranchDirectTerminal
    (valuation : Nat -> Nat)
    (valueBound : Nat)
    (body : ArithmeticSemiformula Nat 9)
    (publicResource : Nat) where
  values : Fin 9 -> Nat
  values_le : forall index, values index <= valueBound
  terminal : CertifiedPAContextProof
    (valuationContext
      (body ⇜ fun index =>
        shortBinaryNumeralTerm (values index)).freeVariables valuation)
    (body ⇜ fun index => shortBinaryNumeralTerm (values index))
  terminal_payloadLength_le : terminal.payloadLength <= publicResource

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchDirectTerminalOfComponents
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
      (compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelopeOfComponents
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
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedExplicitDirectOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount row components.row_graph
  let currentProof :=
    compileCompactBinaryNatStatusValidBoundedBranchDirectAtValuationOfGraph
      valuation tokenTable width tokenCount
      currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
      valueBound components.current_status
  let nextProof :=
    compileCompactBinaryNatStatusValidBoundedBranchDirectAtValuationOfGraph
      valuation tokenTable width tokenCount
      nextCoordinates.parserTasksFinish nextCoordinates.parserFinish
      valueBound components.next_status
  let rowResource :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount row components.row_graph
  let currentResource :=
    compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound components.current_status
  let nextResource :=
    compactBinaryNatStatusValidBoundedBranchDirectPayloadEnvelopeOfGraph
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound components.next_status
  let syntaxResource :=
    compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound
  let publicResource :=
    compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelopeOfComponents
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize components
  have hcurrentProof : currentProof.payloadLength <= currentResource :=
    compileCompactBinaryNatStatusValidBoundedBranchDirectAtValuationOfGraph_payloadLength_le
      valuation tokenTable width tokenCount
      currentCoordinates.parserTasksFinish currentCoordinates.parserFinish
      valueBound components.current_status
  have hnextProof : nextProof.payloadLength <= nextResource :=
    compileCompactBinaryNatStatusValidBoundedBranchDirectAtValuationOfGraph_payloadLength_le
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
    compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope_le_publicAssembly
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hcurrent hnext components
  have hassemblyLocal :
      compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope
          valuation rowFormula currentFormula nextFormula rowResource
          currentResource nextResource <= publicResource := by
    simpa only [row, rowFormula, currentFormula, nextFormula, rowResource,
      currentResource, nextResource, syntaxResource, publicResource,
      compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelopeOfComponents] using
      hassembly
  have hterminalExact : terminalProof.payloadLength <=
      compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope
        valuation rowFormula currentFormula nextFormula rowResource
        currentResource nextResource := by
    simpa only [terminalProof, innerProof,
      compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope]
      using hterminal
  have hterminalPublic : terminalProof.payloadLength <= publicResource :=
    hterminalExact.trans hassemblyLocal
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
      terminal := by simpa only [rawBody] using terminal
      terminal_payloadLength_le := by
        simpa only [rawBody] using hterminalResource }

noncomputable def
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchDirectTerminalOfGraph
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
      (compactFormulaTransformAdjacentStepDirectTerminalBranchPublicAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize
        (explicitAdjacentStepDirectTerminalComponentsOfGraph valuation tokenTable
          width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound currentCoordinates
          currentSize nextCoordinates nextSize hbounded)) :=
  compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchDirectTerminalOfComponents
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize nextCoordinates nextSize hcurrent hnext
    (explicitAdjacentStepDirectTerminalComponentsOfGraph valuation tokenTable
      width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound currentCoordinates currentSize
      nextCoordinates nextSize hbounded)

#print axioms
  compactFormulaTransformAdjacentStepDirectTerminalBranchPayloadEnvelope_le_publicAssembly
#print axioms
  compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexBranchDirectTerminalOfGraph

end FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalBranchBounds
