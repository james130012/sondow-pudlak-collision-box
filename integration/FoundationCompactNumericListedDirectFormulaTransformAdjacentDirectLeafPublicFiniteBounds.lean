import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedPublicDirectCompiler
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicFiniteBounds

/-!
# Public-finite resource of one adjacent-row numerical witness

This file flattens the 14 + 14 + 9 bounded-witness compiler layers into one
resource depending on a numerical adjacent row, not on proofs of its graph.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped BigOperators

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectLeafPublicFiniteBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedPublicDirectCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedPublicDirectCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedPublicDirectCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectTerminalPublicFiniteBounds

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfRow
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) : Nat :=
  let contextResource :=
    compactFormulaTransformAdjacentPublicContextCodeBound valuation rowIndexTerm
  let stepResource := explicitBoundedWitnessDirectPublicPayloadEnvelope 9
    contextResource valueBound
    (compactFormulaTransformAdjacentStepRawTerminalPublicCodeEnvelope tokenTable
      width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound)
    (compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelopeOfRow
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound row)
  let nextResource := explicitBoundedWitnessDirectPublicPayloadEnvelope 14
    contextResource valueBound
    (compactFormulaTransformAdjacentNextRawTerminalPublicCodeEnvelope tokenTable
      width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound)
    stepResource
  explicitBoundedWitnessDirectPublicPayloadEnvelope 14 contextResource valueBound
    (compactFormulaTransformAdjacentCurrentRawTerminalPublicCodeEnvelope tokenTable
      width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound)
    nextResource

theorem
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph_eq_ofRow
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound) :
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound hcurrent =
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfRow
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound
        (explicitAdjacentStepDirectTerminalComponentsOfGraph valuation tokenTable
          width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
          witnessFinish witnessCount valueBound
          (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
            tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
            witnessStart witnessFinish witnessCount valueBound hcurrent).witness.coordinates
          (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
            tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
            witnessStart witnessFinish witnessCount valueBound hcurrent).witness.size
          (compactFormulaTransformAdjacentNextBounded_witnessOfGraph valuation
            tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
            witnessStart witnessFinish witnessCount valueBound
            (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
              tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
              witnessStart witnessFinish witnessCount valueBound hcurrent).witness.coordinates
            (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
              tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
              witnessStart witnessFinish witnessCount valueBound hcurrent).witness.size
            (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
              tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
              witnessStart witnessFinish witnessCount valueBound hcurrent).next).coordinates
          (compactFormulaTransformAdjacentNextBounded_witnessOfGraph valuation
            tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
            witnessStart witnessFinish witnessCount valueBound
            (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
              tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
              witnessStart witnessFinish witnessCount valueBound hcurrent).witness.coordinates
            (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
              tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
              witnessStart witnessFinish witnessCount valueBound hcurrent).witness.size
            (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
              tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
              witnessStart witnessFinish witnessCount valueBound hcurrent).next).size
          (compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec valuation
            tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
            witnessStart witnessFinish witnessCount valueBound
            (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
              tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
              witnessStart witnessFinish witnessCount valueBound hcurrent).witness.coordinates
            (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
              tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
              witnessStart witnessFinish witnessCount valueBound hcurrent).witness.size
            (compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
              tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
              witnessStart witnessFinish witnessCount valueBound hcurrent).next).2).row := by
  unfold
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
    compactFormulaTransformAdjacentNextBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
    compactFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
    compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelope
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfRow
  simp only [
    compactFormulaTransformAdjacentStepDirectTerminalPublicFiniteAssemblyEnvelopeOfComponents_eq_ofRow]

noncomputable def compactFormulaTransformAdjacentCurrentBoundedRowOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound) :
    CompactFormulaTransformAdjacentStepRow :=
  let currentData :=
    compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound hcurrent
  let nextWitness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound
    currentData.witness.coordinates currentData.witness.size currentData.next
  let hbounded :=
    (compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound
      currentData.witness.coordinates currentData.witness.size
      currentData.next).2
  (explicitAdjacentStepDirectTerminalComponentsOfGraph valuation tokenTable width
    tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
    witnessFinish witnessCount valueBound currentData.witness.coordinates
    currentData.witness.size nextWitness.coordinates nextWitness.size
    hbounded).row

theorem
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph_eq_rowOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound) :
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound hcurrent =
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfRow
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound
        (compactFormulaTransformAdjacentCurrentBoundedRowOfGraph valuation
          tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound hcurrent) := by
  simpa only [compactFormulaTransformAdjacentCurrentBoundedRowOfGraph] using
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph_eq_ofRow
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound hcurrent

abbrev CompactFormulaTransformAdjacentStepRowFiniteCoordinates
    (valueBound : Nat) :=
  (Fin 14 -> Fin (valueBound + 1)) ×
    (Fin 14 -> Fin (valueBound + 1)) ×
      (Fin 9 -> Fin (valueBound + 1))

theorem compactFormulaTransformAdjacentStepRowFiniteCoordinates_card
    (valueBound : Nat) :
    Fintype.card
        (CompactFormulaTransformAdjacentStepRowFiniteCoordinates valueBound) =
      (valueBound + 1) ^ 37 := by
  simp only [CompactFormulaTransformAdjacentStepRowFiniteCoordinates,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [← pow_add, ← pow_add]

def compactFormulaTransformAdjacentStepRowOfFiniteCoordinates
    {valueBound : Nat}
    (coordinates : CompactFormulaTransformAdjacentStepRowFiniteCoordinates
      valueBound) : CompactFormulaTransformAdjacentStepRow :=
  let current := coordinates.1
  let next := coordinates.2.1
  let step := coordinates.2.2
  { currentCoordinates :=
      { start := current 13
        finish := current 12
        parserFinish := current 11
        parserTokensFinish := current 10
        parserTasksFinish := current 9
        parserTokensBoundary := current 8
        parserTokensCount := current 7
        parserTasksBoundary := current 6
        parserTasksCount := current 5
        outputBoundary := current 4
        outputCount := current 3 }
    currentSize :=
      { parserTokensBoundarySize := current 2
        parserTasksBoundarySize := current 1
        outputBoundarySize := current 0 }
    nextCoordinates :=
      { start := next 13
        finish := next 12
        parserFinish := next 11
        parserTokensFinish := next 10
        parserTasksFinish := next 9
        parserTokensBoundary := next 8
        parserTokensCount := next 7
        parserTasksBoundary := next 6
        parserTasksCount := next 5
        outputBoundary := next 4
        outputCount := next 3 }
    nextSize :=
      { parserTokensBoundarySize := next 2
        parserTasksBoundarySize := next 1
        outputBoundarySize := next 0 }
    stepWitness :=
      { slot0 := step 8
        slot1 := step 7
        slot2 := step 6
        slot3 := step 5
        slot4 := step 4
        slot5 := step 3
        slot6 := step 2 }
    consumedCount := step 1
    mappedHead := step 0 }

noncomputable def compactFormulaTransformAdjacentStepFiniteCoordinatesOfRow
    (valueBound : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨row.currentCoordinates, row.currentSize⟩ index <= valueBound)
    (hnext : forall index,
      adjacentNextBoundedWitnessValues
        ⟨row.nextCoordinates, row.nextSize⟩ index <= valueBound)
    (hstep : forall index, boundedWitnessValues row index <= valueBound) :
    CompactFormulaTransformAdjacentStepRowFiniteCoordinates valueBound :=
  (fun index =>
      ⟨adjacentCurrentBoundedWitnessValues
          ⟨row.currentCoordinates, row.currentSize⟩ index, by
        exact Nat.lt_succ_iff.mpr (hcurrent index)⟩,
    fun index =>
      ⟨adjacentNextBoundedWitnessValues
          ⟨row.nextCoordinates, row.nextSize⟩ index, by
        exact Nat.lt_succ_iff.mpr (hnext index)⟩,
    fun index =>
      ⟨boundedWitnessValues row index, by
        exact Nat.lt_succ_iff.mpr (hstep index)⟩)

theorem compactFormulaTransformAdjacentStepRowOfFiniteCoordinates_roundtrip
    (valueBound : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨row.currentCoordinates, row.currentSize⟩ index <= valueBound)
    (hnext : forall index,
      adjacentNextBoundedWitnessValues
        ⟨row.nextCoordinates, row.nextSize⟩ index <= valueBound)
    (hstep : forall index, boundedWitnessValues row index <= valueBound) :
    compactFormulaTransformAdjacentStepRowOfFiniteCoordinates
        (compactFormulaTransformAdjacentStepFiniteCoordinatesOfRow valueBound row
          hcurrent hnext hstep) = row := by
  rfl

noncomputable def
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFiniteCoordinatePayloadEnvelopeSum
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
  ∑ coordinates : CompactFormulaTransformAdjacentStepRowFiniteCoordinates
      valueBound,
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfRow
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound
      (compactFormulaTransformAdjacentStepRowOfFiniteCoordinates coordinates)

theorem
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfRow_le_finiteCoordinateSum
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨row.currentCoordinates, row.currentSize⟩ index <= valueBound)
    (hnext : forall index,
      adjacentNextBoundedWitnessValues
        ⟨row.nextCoordinates, row.nextSize⟩ index <= valueBound)
    (hstep : forall index, boundedWitnessValues row index <= valueBound) :
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfRow
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound row <=
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFiniteCoordinatePayloadEnvelopeSum
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound := by
  let coordinates :=
    compactFormulaTransformAdjacentStepFiniteCoordinatesOfRow valueBound row
      hcurrent hnext hstep
  calc
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfRow
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound row =
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfRow
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound
        (compactFormulaTransformAdjacentStepRowOfFiniteCoordinates coordinates) := by
          rw [compactFormulaTransformAdjacentStepRowOfFiniteCoordinates_roundtrip
            valueBound row hcurrent hnext hstep]
    _ <= compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFiniteCoordinatePayloadEnvelopeSum
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound := by
      unfold
        compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFiniteCoordinatePayloadEnvelopeSum
      exact Finset.single_le_sum
        (fun candidate _ => Nat.zero_le
          (compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfRow
            valuation tokenTable width tokenCount stateBoundary stateCount
            rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
            (compactFormulaTransformAdjacentStepRowOfFiniteCoordinates candidate)))
        (Finset.mem_univ coordinates)

theorem compactFormulaTransformAdjacentCurrentBoundedRowOfGraph_currentValues_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound)
    (index : Fin 14) :
    adjacentCurrentBoundedWitnessValues
        ⟨(compactFormulaTransformAdjacentCurrentBoundedRowOfGraph valuation
            tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
            witnessStart witnessFinish witnessCount valueBound hcurrent).currentCoordinates,
          (compactFormulaTransformAdjacentCurrentBoundedRowOfGraph valuation
            tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
            witnessStart witnessFinish witnessCount valueBound hcurrent).currentSize⟩
      index <= valueBound := by
  let currentData :=
    compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound hcurrent
  let nextWitness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound
    currentData.witness.coordinates currentData.witness.size currentData.next
  let nextSpec := compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound
    currentData.witness.coordinates currentData.witness.size currentData.next
  let components := explicitAdjacentStepDirectTerminalComponentsOfGraph valuation
    tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
    witnessStart witnessFinish witnessCount valueBound
    currentData.witness.coordinates currentData.witness.size
    nextWitness.coordinates nextWitness.size nextSpec.2
  change adjacentCurrentBoundedWitnessValues
      ⟨components.row.currentCoordinates, components.row.currentSize⟩ index <=
    valueBound
  rw [components.row_current_coordinates, components.row_current_size]
  exact currentData.values_le index

theorem compactFormulaTransformAdjacentCurrentBoundedRowOfGraph_nextValues_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound)
    (index : Fin 14) :
    adjacentNextBoundedWitnessValues
        ⟨(compactFormulaTransformAdjacentCurrentBoundedRowOfGraph valuation
            tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
            witnessStart witnessFinish witnessCount valueBound hcurrent).nextCoordinates,
          (compactFormulaTransformAdjacentCurrentBoundedRowOfGraph valuation
            tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
            witnessStart witnessFinish witnessCount valueBound hcurrent).nextSize⟩
      index <= valueBound := by
  let currentData :=
    compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound hcurrent
  let nextWitness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound
    currentData.witness.coordinates currentData.witness.size currentData.next
  let nextSpec := compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound
    currentData.witness.coordinates currentData.witness.size currentData.next
  let components := explicitAdjacentStepDirectTerminalComponentsOfGraph valuation
    tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
    witnessStart witnessFinish witnessCount valueBound
    currentData.witness.coordinates currentData.witness.size
    nextWitness.coordinates nextWitness.size nextSpec.2
  change adjacentNextBoundedWitnessValues
      ⟨components.row.nextCoordinates, components.row.nextSize⟩ index <= valueBound
  rw [components.row_next_coordinates, components.row_next_size]
  exact nextSpec.1 index

theorem compactFormulaTransformAdjacentCurrentBoundedRowOfGraph_stepValues_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound)
    (index : Fin 9) :
    boundedWitnessValues
      (compactFormulaTransformAdjacentCurrentBoundedRowOfGraph valuation
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound hcurrent) index <=
      valueBound := by
  let currentData :=
    compactFormulaTransformAdjacentCurrentBoundedWitnessDataOfGraph valuation
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound hcurrent
  let nextWitness := compactFormulaTransformAdjacentNextBounded_witnessOfGraph
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound
    currentData.witness.coordinates currentData.witness.size currentData.next
  let nextSpec := compactFormulaTransformAdjacentNextBounded_witnessOfGraph_spec
    valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
    mode witnessStart witnessFinish witnessCount valueBound
    currentData.witness.coordinates currentData.witness.size currentData.next
  let components := explicitAdjacentStepDirectTerminalComponentsOfGraph valuation
    tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
    witnessStart witnessFinish witnessCount valueBound
    currentData.witness.coordinates currentData.witness.size
    nextWitness.coordinates nextWitness.size nextSpec.2
  change boundedWitnessValues components.row index <= valueBound
  exact components.values_le index

theorem
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph_le_finiteCoordinateSum
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (hcurrent : CompactFormulaTransformAdjacentCurrentBounded tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation rowIndexTerm) mode
      witnessStart witnessFinish witnessCount valueBound) :
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound hcurrent <=
      compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexFiniteCoordinatePayloadEnvelopeSum
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound := by
  rw [
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph_eq_rowOfGraph]
  exact
    compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfRow_le_finiteCoordinateSum
      valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
      mode witnessStart witnessFinish witnessCount valueBound
      (compactFormulaTransformAdjacentCurrentBoundedRowOfGraph valuation
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound hcurrent)
      (compactFormulaTransformAdjacentCurrentBoundedRowOfGraph_currentValues_le
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound hcurrent)
      (compactFormulaTransformAdjacentCurrentBoundedRowOfGraph_nextValues_le
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound hcurrent)
      (compactFormulaTransformAdjacentCurrentBoundedRowOfGraph_stepValues_le
        valuation tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
        mode witnessStart witnessFinish witnessCount valueBound hcurrent)

#print axioms
  compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph_eq_ofRow
#print axioms
  compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfRow_le_finiteCoordinateSum
#print axioms compactFormulaTransformAdjacentStepRowFiniteCoordinates_card
#print axioms
  compactFormulaTransformAdjacentCurrentBoundedAtValuationIndexPublicFiniteDirectPayloadEnvelopeOfGraph_le_finiteCoordinateSum

end FoundationCompactNumericListedDirectFormulaTransformAdjacentDirectLeafPublicFiniteBounds
