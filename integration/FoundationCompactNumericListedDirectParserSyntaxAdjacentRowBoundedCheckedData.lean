import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedPublicDirectCompiler

/-! # Checked data extracted from one bounded adjacent parser row -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedCheckedData

open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedWitnessSyntax
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

structure CompactParserSyntaxAdjacentRowCheckedData
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat) where
  row : CompactParserSyntaxAdjacentStepRow
  values_le : forall coordinate,
    compactParserSyntaxAdjacentRowBoundedWitnessValues row coordinate <=
      valueBound
  graph : CompactParserSyntaxAdjacentStepRowGraph tokenTable width tokenCount
    stateBoundary stateCount index row
  current_status : CompactBinaryNatStatusValidBounded tokenTable width tokenCount
    row.currentCoordinates.tasksFinish row.currentCoordinates.finish valueBound
  next_status : CompactBinaryNatStatusValidBounded tokenTable width tokenCount
    row.nextCoordinates.tasksFinish row.nextCoordinates.finish valueBound

private theorem compactParserSyntaxAdjacentRowCheckedData_exists
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat)
    (hbounded : CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
      stateBoundary stateCount index valueBound) :
    ∃ row : CompactParserSyntaxAdjacentStepRow,
      (forall coordinate,
        compactParserSyntaxAdjacentRowBoundedWitnessValues row coordinate <=
          valueBound) ∧
      CompactParserSyntaxAdjacentStepRowGraph tokenTable width tokenCount
        stateBoundary stateCount index row ∧
      CompactBinaryNatStatusValidBounded tokenTable width tokenCount
        row.currentCoordinates.tasksFinish row.currentCoordinates.finish
          valueBound ∧
      CompactBinaryNatStatusValidBounded tokenTable width tokenCount
        row.nextCoordinates.tasksFinish row.nextCoordinates.finish
          valueBound := by
  rcases hbounded with
    ⟨currentStart, hcurrentStart, currentFinish, hcurrentFinish,
      currentTokensFinish, hcurrentTokensFinish,
      currentTasksFinish, hcurrentTasksFinish,
      currentTokensBoundary, hcurrentTokensBoundary,
      currentTokensCount, hcurrentTokensCount,
      currentTasksBoundary, hcurrentTasksBoundary,
      currentTasksCount, hcurrentTasksCount,
      currentTokensBoundarySize, hcurrentTokensBoundarySize,
      currentTasksBoundarySize, hcurrentTasksBoundarySize,
      nextStart, hnextStart, nextFinish, hnextFinish,
      nextTokensFinish, hnextTokensFinish,
      nextTasksFinish, hnextTasksFinish,
      nextTokensBoundary, hnextTokensBoundary,
      nextTokensCount, hnextTokensCount,
      nextTasksBoundary, hnextTasksBoundary,
      nextTasksCount, hnextTasksCount,
      nextTokensBoundarySize, hnextTokensBoundarySize,
      nextTasksBoundarySize, hnextTasksBoundarySize,
      slot0, hslot0, slot1, hslot1, slot2, hslot2, slot3, hslot3,
      slot4, hslot4, slot5, hslot5, slot6, hslot6,
      hgraph, hcurrentStatus, hnextStatus⟩
  let row := compactParserSyntaxAdjacentStepRowOfValues
    currentStart currentFinish currentTokensFinish currentTasksFinish
    currentTokensBoundary currentTokensCount currentTasksBoundary
    currentTasksCount currentTokensBoundarySize currentTasksBoundarySize
    nextStart nextFinish nextTokensFinish nextTasksFinish nextTokensBoundary
    nextTokensCount nextTasksBoundary nextTasksCount nextTokensBoundarySize
    nextTasksBoundarySize slot0 slot1 slot2 slot3 slot4 slot5 slot6
  refine ⟨row, ?_, ?_, ?_, ?_⟩
  · intro coordinate
    dsimp only [row, compactParserSyntaxAdjacentStepRowOfValues,
      compactUnifiedParserStateRowCoordinatesOf]
    fin_cases coordinate
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hslot6
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hslot5
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hslot4
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hslot3
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hslot2
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hslot1
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hslot0
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using
        hnextTasksBoundarySize
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using
        hnextTokensBoundarySize
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hnextTasksCount
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hnextTasksBoundary
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hnextTokensCount
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hnextTokensBoundary
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hnextTasksFinish
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hnextTokensFinish
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hnextFinish
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hnextStart
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using
        hcurrentTasksBoundarySize
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using
        hcurrentTokensBoundarySize
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hcurrentTasksCount
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hcurrentTasksBoundary
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hcurrentTokensCount
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using
        hcurrentTokensBoundary
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hcurrentTasksFinish
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hcurrentTokensFinish
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hcurrentFinish
    · simpa [row, compactParserSyntaxAdjacentRowBoundedWitnessValues,
        compactParserSyntaxAdjacentStepRowOfValues] using hcurrentStart
  · simpa [row, compactParserSyntaxAdjacentStepRowOfValues] using hgraph
  · simpa [row, compactParserSyntaxAdjacentStepRowOfValues,
      compactUnifiedParserStateRowCoordinatesOf] using hcurrentStatus
  · simpa [row, compactParserSyntaxAdjacentStepRowOfValues,
      compactUnifiedParserStateRowCoordinatesOf] using hnextStatus

noncomputable def compactParserSyntaxAdjacentRowCheckedDataOfBounded
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat)
    (hbounded : CompactParserSyntaxAdjacentRowBounded tokenTable width tokenCount
      stateBoundary stateCount index valueBound) :
    CompactParserSyntaxAdjacentRowCheckedData tokenTable width tokenCount
      stateBoundary stateCount index valueBound := by
  let hexists := compactParserSyntaxAdjacentRowCheckedData_exists tokenTable
    width tokenCount stateBoundary stateCount index valueBound hbounded
  let row := Classical.choose hexists
  have hrow := Classical.choose_spec hexists
  exact
    { row := row
      values_le := hrow.1
      graph := hrow.2.1
      current_status := hrow.2.2.1
      next_status := hrow.2.2.2 }

theorem CompactParserSyntaxAdjacentRowCheckedData.current_value_bound
    {tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat}
    (data : CompactParserSyntaxAdjacentRowCheckedData tokenTable width tokenCount
      stateBoundary stateCount index valueBound) :
    CompactUnifiedParserStateCoordinateValueBound data.row.currentCoordinates
      valueBound := by
  intro coordinate
  fin_cases coordinate
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (26 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (25 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (24 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (23 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (22 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (21 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (20 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (19 : Fin 27)

theorem CompactParserSyntaxAdjacentRowCheckedData.next_value_bound
    {tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat}
    (data : CompactParserSyntaxAdjacentRowCheckedData tokenTable width tokenCount
      stateBoundary stateCount index valueBound) :
    CompactUnifiedParserStateCoordinateValueBound data.row.nextCoordinates
      valueBound := by
  intro coordinate
  fin_cases coordinate
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (16 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (15 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (14 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (13 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (12 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (11 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (10 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserStateCoordinateValues] using data.values_le (9 : Fin 27)

theorem CompactParserSyntaxAdjacentRowCheckedData.witness_value_bound
    {tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat}
    (data : CompactParserSyntaxAdjacentRowCheckedData tokenTable width tokenCount
      stateBoundary stateCount index valueBound) :
    CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound
      data.row.stepWitness valueBound := by
  intro coordinate
  fin_cases coordinate
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      data.values_le (6 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      data.values_le (5 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      data.values_le (4 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      data.values_le (3 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      data.values_le (2 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      data.values_le (1 : Fin 27)
  · simpa [compactParserSyntaxAdjacentRowBoundedWitnessValues,
      compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
      data.values_le (0 : Fin 27)

theorem parserStateCoordinateValueBound_mono
    {coordinates : CompactUnifiedParserStateRowCoordinates}
    {small large : Nat}
    (hbound : CompactUnifiedParserStateCoordinateValueBound coordinates small)
    (hsmall : small <= large) :
    CompactUnifiedParserStateCoordinateValueBound coordinates large :=
  fun coordinate => (hbound coordinate).trans hsmall

theorem parserSyntaxStepWitnessCoordinateValueBound_mono
    {witness : CompactUnifiedParserSyntaxStepWitnessCoordinates}
    {small large : Nat}
    (hbound :
      CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound witness small)
    (hsmall : small <= large) :
    CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound witness large :=
  fun coordinate => (hbound coordinate).trans hsmall

theorem parserStateCoordinateSizeBound_of_valueBound
    {coordinates : CompactUnifiedParserStateRowCoordinates}
    {valueBound bitBound : Nat}
    (hvalue :
      CompactUnifiedParserStateCoordinateValueBound coordinates valueBound)
    (hsize : Nat.size valueBound <= bitBound) :
    CompactUnifiedParserStateCoordinateSizeBound coordinates bitBound :=
  fun coordinate => (Nat.size_le_size (hvalue coordinate)).trans hsize

theorem parserSyntaxStepWitnessCoordinateSizeBound_of_valueBound
    {witness : CompactUnifiedParserSyntaxStepWitnessCoordinates}
    {valueBound bitBound : Nat}
    (hvalue :
      CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound witness
        valueBound)
    (hsize : Nat.size valueBound <= bitBound) :
    CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound witness bitBound :=
  fun coordinate => (Nat.size_le_size (hvalue coordinate)).trans hsize

#print axioms compactParserSyntaxAdjacentRowCheckedDataOfBounded
#print axioms CompactParserSyntaxAdjacentRowCheckedData.current_value_bound
#print axioms CompactParserSyntaxAdjacentRowCheckedData.next_value_bound
#print axioms CompactParserSyntaxAdjacentRowCheckedData.witness_value_bound

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedCheckedData
