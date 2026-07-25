import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalFixedCoreBounds

/-!
# Fully finite adjacent-row terminal bound

The thirty-seven bounded row coordinates are reconstructed from fixed-arity
vectors and then exhausted over finite function spaces.

This is a logical completeness envelope only.  Its function-space sum has
`(valueBound + 1)^37` branches, so it must not be used as the quantitative
`A04.18` endpoint when `valueBound = 2^tableWidth`.  The submission route must
instead bound every terminal resource uniformly in the coordinate bit width.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped BigOperators

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalFullyFiniteBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalFixedCoreBounds

def adjacentStateCoordinatesOfValues
    (values : Fin 14 -> Nat) :
    CompactFormulaTransformStateRowCoordinates :=
  { start := values 13
    finish := values 12
    parserFinish := values 11
    parserTokensFinish := values 10
    parserTasksFinish := values 9
    parserTokensBoundary := values 8
    parserTokensCount := values 7
    parserTasksBoundary := values 6
    parserTasksCount := values 5
    outputBoundary := values 4
    outputCount := values 3 }

def adjacentStateSizeOfValues
    (values : Fin 14 -> Nat) : CompactFormulaTransformStateCoreSizeWitness :=
  { parserTokensBoundarySize := values 2
    parserTasksBoundarySize := values 1
    outputBoundarySize := values 0 }

def adjacentStepWitnessOfValues
    (values : Fin 9 -> Nat) :
    CompactUnifiedParserSyntaxStepWitnessCoordinates :=
  { slot0 := values 8
    slot1 := values 7
    slot2 := values 6
    slot3 := values 5
    slot4 := values 4
    slot5 := values 3
    slot6 := values 2 }

def adjacentStepRowOfValues
    (currentValues nextValues : Fin 14 -> Nat)
    (stepValues : Fin 9 -> Nat) : CompactFormulaTransformAdjacentStepRow :=
  { currentCoordinates := adjacentStateCoordinatesOfValues currentValues
    currentSize := adjacentStateSizeOfValues currentValues
    nextCoordinates := adjacentStateCoordinatesOfValues nextValues
    nextSize := adjacentStateSizeOfValues nextValues
    stepWitness := adjacentStepWitnessOfValues stepValues
    consumedCount := stepValues 1
    mappedHead := stepValues 0 }

theorem adjacentStepRowOfValues_reconstruct
    (row : CompactFormulaTransformAdjacentStepRow) :
    adjacentStepRowOfValues
        (adjacentCurrentBoundedWitnessValues
          ⟨row.currentCoordinates, row.currentSize⟩)
        (adjacentNextBoundedWitnessValues
          ⟨row.nextCoordinates, row.nextSize⟩)
        (boundedWitnessValues row) =
      row := by
  rcases row with
    ⟨currentCoordinates, currentSize, nextCoordinates, nextSize,
      stepWitness, consumedCount, mappedHead⟩
  rcases currentCoordinates with
    ⟨currentStart, currentFinish, currentParserFinish,
      currentParserTokensFinish, currentParserTasksFinish,
      currentParserTokensBoundary, currentParserTokensCount,
      currentParserTasksBoundary, currentParserTasksCount,
      currentOutputBoundary, currentOutputCount⟩
  rcases currentSize with
    ⟨currentParserTokensBoundarySize, currentParserTasksBoundarySize,
      currentOutputBoundarySize⟩
  rcases nextCoordinates with
    ⟨nextStart, nextFinish, nextParserFinish, nextParserTokensFinish,
      nextParserTasksFinish, nextParserTokensBoundary, nextParserTokensCount,
      nextParserTasksBoundary, nextParserTasksCount, nextOutputBoundary,
      nextOutputCount⟩
  rcases nextSize with
    ⟨nextParserTokensBoundarySize, nextParserTasksBoundarySize,
      nextOutputBoundarySize⟩
  rcases stepWitness with
    ⟨slot0, slot1, slot2, slot3, slot4, slot5, slot6⟩
  rfl

def boundedFinValues
    {arity valueBound : Nat}
    (values : Fin arity -> Nat)
    (hvalues : forall index, values index <= valueBound) :
    Fin arity -> Fin (valueBound + 1) :=
  fun index => ⟨values index, Nat.lt_succ_of_le (hvalues index)⟩

def natValuesOfBoundedFin
    {arity valueBound : Nat}
    (values : Fin arity -> Fin (valueBound + 1)) : Fin arity -> Nat :=
  fun index => values index

theorem natValuesOfBoundedFin_boundedFinValues
    {arity valueBound : Nat}
    (values : Fin arity -> Nat)
    (hvalues : forall index, values index <= valueBound) :
    natValuesOfBoundedFin (boundedFinValues values hvalues) = values := by
  rfl

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteRowEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) : Nat :=
  compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteAssemblyEnvelope
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound
    row.currentCoordinates row.nextCoordinates row

noncomputable def
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAllRowsFiniteEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
  ∑ currentValues : Fin 14 -> Fin (valueBound + 1),
    ∑ nextValues : Fin 14 -> Fin (valueBound + 1),
      ∑ stepValues : Fin 9 -> Fin (valueBound + 1),
        compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteRowEnvelope
          valuation tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
          (adjacentStepRowOfValues
            (natValuesOfBoundedFin currentValues)
            (natValuesOfBoundedFin nextValues)
            (natValuesOfBoundedFin stepValues))

theorem
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteAssemblyEnvelope_le_allRowsFinite
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
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteAssemblyEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
        currentCoordinates nextCoordinates components.row <=
      compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAllRowsFiniteEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount
        rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound := by
  classical
  let row := components.row
  let currentNatValues := adjacentCurrentBoundedWitnessValues
    ⟨currentCoordinates, currentSize⟩
  let nextNatValues := adjacentNextBoundedWitnessValues
    ⟨nextCoordinates, nextSize⟩
  let stepNatValues := boundedWitnessValues row
  let currentChoice : Fin 14 -> Fin (valueBound + 1) :=
    boundedFinValues currentNatValues hcurrent
  let nextChoice : Fin 14 -> Fin (valueBound + 1) :=
    boundedFinValues nextNatValues hnext
  let stepChoice : Fin 9 -> Fin (valueBound + 1) :=
    boundedFinValues stepNatValues components.values_le
  let resourceOfChoices
      (currentValues nextValues : Fin 14 -> Fin (valueBound + 1))
      (stepValues : Fin 9 -> Fin (valueBound + 1)) : Nat :=
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteRowEnvelope
      valuation tokenTable width tokenCount stateBoundary stateCount
      rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
      (adjacentStepRowOfValues
        (natValuesOfBoundedFin currentValues)
        (natValuesOfBoundedFin nextValues)
        (natValuesOfBoundedFin stepValues))
  have hcurrentWitness :
      (⟨currentCoordinates, currentSize⟩ :
          CompactFormulaTransformAdjacentCurrentStateWitness) =
        ⟨row.currentCoordinates, row.currentSize⟩ := by
    rw [components.row_current_coordinates, components.row_current_size]
  have hnextWitness :
      (⟨nextCoordinates, nextSize⟩ :
          CompactFormulaTransformAdjacentNextStateWitness) =
        ⟨row.nextCoordinates, row.nextSize⟩ := by
    rw [components.row_next_coordinates, components.row_next_size]
  have hcurrentValues : currentNatValues =
      adjacentCurrentBoundedWitnessValues
        ⟨row.currentCoordinates, row.currentSize⟩ := by
    dsimp only [currentNatValues]
    exact congrArg adjacentCurrentBoundedWitnessValues hcurrentWitness
  have hnextValues : nextNatValues =
      adjacentNextBoundedWitnessValues
        ⟨row.nextCoordinates, row.nextSize⟩ := by
    dsimp only [nextNatValues]
    exact congrArg adjacentNextBoundedWitnessValues hnextWitness
  have hrow : adjacentStepRowOfValues currentNatValues nextNatValues
      stepNatValues = row := by
    rw [hcurrentValues, hnextValues]
    dsimp only [stepNatValues, row]
    exact adjacentStepRowOfValues_reconstruct components.row
  have hselected :
      compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteAssemblyEnvelope
          valuation tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
          currentCoordinates nextCoordinates components.row =
        resourceOfChoices currentChoice nextChoice stepChoice := by
    rw [show resourceOfChoices currentChoice nextChoice stepChoice =
        compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteRowEnvelope
          valuation tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
          (adjacentStepRowOfValues currentNatValues nextNatValues
            stepNatValues) by
      simp only [resourceOfChoices, currentChoice, nextChoice, stepChoice,
        natValuesOfBoundedFin_boundedFinValues]]
    rw [hrow]
    unfold
      compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteRowEnvelope
    rw [components.row_current_coordinates, components.row_next_coordinates]
  have hstep : resourceOfChoices currentChoice nextChoice stepChoice <=
      ∑ candidate : Fin 9 -> Fin (valueBound + 1),
        resourceOfChoices currentChoice nextChoice candidate := by
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (resourceOfChoices currentChoice nextChoice candidate))
      (Finset.mem_univ stepChoice)
  have hnext :
      (∑ candidate : Fin 9 -> Fin (valueBound + 1),
          resourceOfChoices currentChoice nextChoice candidate) <=
        ∑ nextValues : Fin 14 -> Fin (valueBound + 1),
          ∑ stepValues : Fin 9 -> Fin (valueBound + 1),
            resourceOfChoices currentChoice nextValues stepValues := by
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (∑ stepValues : Fin 9 -> Fin (valueBound + 1),
          resourceOfChoices currentChoice candidate stepValues))
      (Finset.mem_univ nextChoice)
  have hcurrent :
      (∑ nextValues : Fin 14 -> Fin (valueBound + 1),
          ∑ stepValues : Fin 9 -> Fin (valueBound + 1),
            resourceOfChoices currentChoice nextValues stepValues) <=
        ∑ currentValues : Fin 14 -> Fin (valueBound + 1),
          ∑ nextValues : Fin 14 -> Fin (valueBound + 1),
            ∑ stepValues : Fin 9 -> Fin (valueBound + 1),
              resourceOfChoices currentValues nextValues stepValues := by
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (∑ nextValues : Fin 14 -> Fin (valueBound + 1),
          ∑ stepValues : Fin 9 -> Fin (valueBound + 1),
            resourceOfChoices candidate nextValues stepValues))
      (Finset.mem_univ currentChoice)
  rw [hselected]
  simpa only [
    compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicAllRowsFiniteEnvelope,
    resourceOfChoices] using hstep.trans (hnext.trans hcurrent)

#print axioms adjacentStepRowOfValues_reconstruct
#print axioms natValuesOfBoundedFin_boundedFinValues
#print axioms
  compactFormulaTransformAdjacentStepDirectTerminalFixedCorePublicFullyFiniteAssemblyEnvelope_le_allRowsFinite

end FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalFullyFiniteBounds
