import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds

/-!
# Public connector bounds for the adjacent-step direct terminal

The terminal is assembled from one checked row proof and two checked status
proofs.  This file replaces its four weakening costs and two conjunction costs
by one public syntax coordinate.  The three genuine component resources remain
visible for the subsequent scalar bounds.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicAssemblyBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicScalarBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicDirectCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds

private theorem binaryFormulaCode_left_length_le_conjunction
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_length_le_conjunction
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def compactFormulaTransformAdjacentStepInstalledTerminalPublicCodeEnvelope
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
  explicitWitnessInstalledPublicCodeEnvelope valueBound
    (compactFormulaTransformAdjacentStepRawTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound)

def compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
  1 + compactFormulaTransformAdjacentPublicContextCodeBound
      valuation rowIndexTerm +
    compactFormulaTransformAdjacentStepInstalledTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelopeOfComponents
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
  let rowResource :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount components.row
      components.row_graph
  let currentResource :=
    compactBinaryNatStatusValidBoundedPublicDirectPayloadEnvelope
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound
  let nextResource :=
    compactBinaryNatStatusValidBoundedPublicDirectPayloadEnvelope
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound
  let syntaxResource :=
    compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
  rowResource + currentResource + nextResource +
    6 * generalContextAssemblyEnvelope syntaxResource

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelope
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
  compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelopeOfComponents
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize nextCoordinates nextSize
    (explicitAdjacentStepDirectTerminalComponentsOfGraph valuation tokenTable
      width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound currentCoordinates currentSize
      nextCoordinates nextSize hbounded)

theorem
    compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResource_le_publicAssembly
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
    compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResource
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates nextCoordinates components.row components.row_graph <=
      compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates currentSize nextCoordinates nextSize components := by
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
    compactFormulaTransformAdjacentPublicContextCodeBound
      valuation rowIndexTerm
  let terminalCodeBound :=
    compactFormulaTransformAdjacentStepInstalledTerminalPublicCodeEnvelope
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
  let syntaxResource :=
    compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
  let rowResource :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount row
      components.row_graph
  let currentResource :=
    compactBinaryNatStatusValidBoundedPublicDirectPayloadEnvelope
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound
  let nextResource :=
    compactBinaryNatStatusValidBoundedPublicDirectPayloadEnvelope
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound
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
    rw [components.row_current_coordinates,
      components.row_current_size, components.row_next_coordinates,
      components.row_next_size] at hraw
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
    (binaryFormulaCode_left_length_le_conjunction rowFormula innerFormula).trans
      hterminalCode
  have hinnerCode : (binaryFormulaCode innerFormula).length <=
      terminalCodeBound :=
    (binaryFormulaCode_right_length_le_conjunction rowFormula innerFormula).trans
      hterminalCode
  have hcurrentCode : (binaryFormulaCode currentFormula).length <=
      terminalCodeBound :=
    (binaryFormulaCode_left_length_le_conjunction
      currentFormula nextFormula).trans hinnerCode
  have hnextCode : (binaryFormulaCode nextFormula).length <=
      terminalCodeBound :=
    (binaryFormulaCode_right_length_le_conjunction
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
  change
    (rowResource + weakeningFullAssemblyCost
        (insert rowFormula
          (valuationContext terminalFormula.freeVariables valuation))) +
      (((currentResource + weakeningFullAssemblyCost
            (insert currentFormula
              (valuationContext innerFormula.freeVariables valuation))) +
          (nextResource + weakeningFullAssemblyCost
            (insert nextFormula
              (valuationContext innerFormula.freeVariables valuation))) +
          CertifiedPAContextProof.conjunctionFullAssemblyCost
            (valuationContext innerFormula.freeVariables valuation)
            currentFormula nextFormula) +
        weakeningFullAssemblyCost
          (insert innerFormula
            (valuationContext terminalFormula.freeVariables valuation))) +
      CertifiedPAContextProof.conjunctionFullAssemblyCost
        (valuationContext terminalFormula.freeVariables valuation)
        rowFormula innerFormula <=
      rowResource + currentResource + nextResource +
        6 * generalContextAssemblyEnvelope syntaxResource
  omega

theorem
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph_terminalResource_le_publicAssembly
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
    (compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize
      hbounded).terminalResource <=
    compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hbounded := by
  rw [
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph_terminalResource_eq]
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResourceOfGraph
    compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelope
  exact
    compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResource_le_publicAssembly
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      currentCoordinates currentSize nextCoordinates nextSize hcurrent hnext
      (explicitAdjacentStepDirectTerminalComponentsOfGraph valuation tokenTable
        width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound currentCoordinates currentSize
        nextCoordinates nextSize hbounded)

#print axioms
  compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResource_le_publicAssembly
#print axioms
  compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph_terminalResource_le_publicAssembly

end FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicAssemblyBounds
