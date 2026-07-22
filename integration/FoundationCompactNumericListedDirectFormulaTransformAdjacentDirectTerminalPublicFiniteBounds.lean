import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicAssemblyBounds

/-!
# Graph-independent component resources for the adjacent direct terminal

For an admissible row-index term, the selected row proof follows the direct
route. Its resource is therefore the public-finite row envelope and is
independent of the row graph proof. The remaining dependence is only on the
thirty-seven bounded numerical witness coordinates.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicFiniteBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAValuationTermCompiler
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
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicDirectCompiler

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalComponentPublicFinitePayloadResource
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (row : CompactFormulaTransformAdjacentStepRow) : Nat :=
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
  let rowResource :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexPublicFiniteDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount row
  let currentResource :=
    compactBinaryNatStatusValidBoundedPublicDirectPayloadEnvelope
      tokenTable width tokenCount currentCoordinates.parserTasksFinish
      currentCoordinates.parserFinish valueBound
  let nextResource :=
    compactBinaryNatStatusValidBoundedPublicDirectPayloadEnvelope
      tokenTable width tokenCount nextCoordinates.parserTasksFinish
      nextCoordinates.parserFinish valueBound
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
      rowFormula innerFormula

theorem
    compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResource_eq_publicFinite
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hrowGraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount row)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0}) :
    compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResource
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
        nextCoordinates row hrowGraph =
      compactFormulaTransformAdjacentStepDirectTerminalComponentPublicFinitePayloadResource
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
        nextCoordinates row := by
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResource
    compactFormulaTransformAdjacentStepDirectTerminalComponentPublicFinitePayloadResource
  rw [
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope_eq_publicFinite
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount row hrowGraph hindexVariables]

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelopeOfRow
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) : Nat :=
  let rowResource :=
    compactFormulaTransformAdjacentStepRowAtValuationIndexPublicFiniteDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount row
  let currentResource :=
    compactBinaryNatStatusValidBoundedPublicDirectPayloadEnvelope
      tokenTable width tokenCount row.currentCoordinates.parserTasksFinish
      row.currentCoordinates.parserFinish valueBound
  let nextResource :=
    compactBinaryNatStatusValidBoundedPublicDirectPayloadEnvelope
      tokenTable width tokenCount row.nextCoordinates.parserTasksFinish
      row.nextCoordinates.parserFinish valueBound
  let syntaxResource :=
    compactFormulaTransformAdjacentStepDirectTerminalAssemblySyntaxResource
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound
  rowResource + currentResource + nextResource +
    6 * generalContextAssemblyEnvelope syntaxResource

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelopeOfComponents
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
    compactFormulaTransformAdjacentStepRowAtValuationIndexPublicFiniteDirectPayloadEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount components.row
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
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound
  rowResource + currentResource + nextResource +
    6 * generalContextAssemblyEnvelope syntaxResource

theorem
    compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelopeOfComponents_eq_ofRow
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
      currentSize nextCoordinates nextSize) :
    compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize components =
      compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelopeOfRow
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound components.row := by
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelopeOfComponents
    compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelopeOfRow
  rw [components.row_current_coordinates, components.row_next_coordinates]

theorem
    compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelopeOfComponents_eq_publicFinite
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
    compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize components =
      compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelopeOfComponents
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize components := by
  unfold
    compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelopeOfComponents
    compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelopeOfComponents
  rw [
    compactFormulaTransformAdjacentStepRowAtValuationIndexSelectedDirectPayloadEnvelope_eq_publicFinite
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount components.row
      components.row_graph hindexVariables]

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize) : Nat :=
  compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelopeOfComponents
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
    currentSize nextCoordinates nextSize
    (explicitAdjacentStepDirectTerminalComponentsOfGraph valuation tokenTable width
      tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound currentCoordinates currentSize
      nextCoordinates nextSize hbounded)

theorem
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph_terminalResource_le_publicFiniteAssembly
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
    (hbounded : CompactFormulaTransformAdjacentStepWitnessBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize)
    (hindexVariables : rowIndexTerm.freeVariables ⊆ {0}) :
    (compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hbounded).terminalResource <=
    compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hbounded := by
  have hresource :=
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph_terminalResource_le_publicAssembly
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize hcurrent hnext hbounded
  unfold compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelope at hresource
  unfold compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelope
  rw [
    compactFormulaTransformAdjacentStepDirectTerminalPublicAssemblyEnvelopeOfComponents_eq_publicFinite
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize
      (explicitAdjacentStepDirectTerminalComponentsOfGraph valuation tokenTable
        width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound currentCoordinates currentSize
        nextCoordinates nextSize hbounded) hindexVariables] at hresource
  exact hresource

#print axioms
  compactFormulaTransformAdjacentStepDirectTerminalComponentPayloadResource_eq_publicFinite
#print axioms
  compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelopeOfComponents_eq_ofRow
#print axioms
  compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitDirectTerminalOfGraph_terminalResource_le_publicFiniteAssembly

end FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicFiniteBounds
