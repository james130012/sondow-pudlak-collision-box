import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessTable
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
import integration.FoundationCompactNumericListedDirectFormulaTransformTraceBounds

/-!
# Installation of the bounded adjacent-step formula

The exact rows supplied by a typed local transform trace are selected in
index order.  One explicit width, the sum of all row-field bit lengths, bounds
every selected value and therefore witnesses the complete Delta-zero row
universal formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedInstallation

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectFormulaTransformTraceInstallation
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformTraceBounds
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

noncomputable def compactFormulaTransformFittingAdjacentStepRowAt
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hadjacent : CompactFormulaTransformStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states)
    (index : Nat) : CompactFormulaTransformAdjacentStepRow :=
  if hindex : index < states.length - 1 then
    Classical.choose
      ((stateListAdjacentStepRows_iff_exists_adjacentStepRow.mp hadjacent)
        index hindex)
  else
    default

theorem compactFormulaTransformFittingAdjacentStepRowAt_graph
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hadjacent : CompactFormulaTransformStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states)
    {index : Nat} (hindex : index < states.length - 1) :
    CompactFormulaTransformAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary states.length index mode
        witnessStart witnessFinish witnessCount
        (compactFormulaTransformFittingAdjacentStepRowAt
          hadjacent index) := by
  rw [compactFormulaTransformFittingAdjacentStepRowAt, dif_pos hindex]
  exact (Classical.choose_spec
    ((stateListAdjacentStepRows_iff_exists_adjacentStepRow.mp hadjacent)
      index hindex)).1

theorem compactFormulaTransformFittingAdjacentStepRowAt_currentStatusLayout
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hadjacent : CompactFormulaTransformStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states)
    {index : Nat} (hindex : index < states.length - 1) :
    CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount
        (compactFormulaTransformFittingAdjacentStepRowAt
          hadjacent index).currentCoordinates.parserTasksFinish
        (compactFormulaTransformFittingAdjacentStepRowAt
          hadjacent index).currentCoordinates.parserFinish
        (states.getI index).1.2.2 := by
  rw [compactFormulaTransformFittingAdjacentStepRowAt, dif_pos hindex]
  exact (Classical.choose_spec
    ((stateListAdjacentStepRows_iff_exists_adjacentStepRow.mp hadjacent)
      index hindex)).2.1

theorem compactFormulaTransformFittingAdjacentStepRowAt_nextStatusLayout
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hadjacent : CompactFormulaTransformStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states)
    {index : Nat} (hindex : index < states.length - 1) :
    CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount
        (compactFormulaTransformFittingAdjacentStepRowAt
          hadjacent index).nextCoordinates.parserTasksFinish
        (compactFormulaTransformFittingAdjacentStepRowAt
          hadjacent index).nextCoordinates.parserFinish
        (states.getI (index + 1)).1.2.2 := by
  rw [compactFormulaTransformFittingAdjacentStepRowAt, dif_pos hindex]
  exact (Classical.choose_spec
    ((stateListAdjacentStepRows_iff_exists_adjacentStepRow.mp hadjacent)
      index hindex)).2.2

noncomputable def compactFormulaTransformFittingAdjacentStepRows
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hadjacent : CompactFormulaTransformStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states) :
    List CompactFormulaTransformAdjacentStepRow :=
  (List.range (states.length - 1)).map
    (compactFormulaTransformFittingAdjacentStepRowAt hadjacent)

@[simp] theorem compactFormulaTransformFittingAdjacentStepRows_length
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hadjacent : CompactFormulaTransformStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states) :
    (compactFormulaTransformFittingAdjacentStepRows hadjacent).length =
      states.length - 1 := by
  simp [compactFormulaTransformFittingAdjacentStepRows]

theorem compactFormulaTransformFittingAdjacentStepRows_valid
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hadjacent : CompactFormulaTransformStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states) :
    CompactFormulaTransformAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length mode
        witnessStart witnessFinish witnessCount
        (compactFormulaTransformFittingAdjacentStepRows hadjacent) := by
  intro rowIndex hrowIndex
  have hindex : rowIndex < states.length - 1 := by
    simpa using hrowIndex
  rw [List.getI_eq_getElem _ hrowIndex]
  simpa [compactFormulaTransformFittingAdjacentStepRows] using
    compactFormulaTransformFittingAdjacentStepRowAt_graph
      hadjacent hindex

noncomputable def compactFormulaTransformPublicFittingAdjacentStepRowAt
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hfit : CompactFormulaTransformStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states)
    (index : Nat) : CompactFormulaTransformAdjacentStepRow :=
  if hindex : index < states.length - 1 then
    Classical.choose (hfit index hindex)
  else
    default

theorem compactFormulaTransformPublicFittingAdjacentStepRowAt_graph
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hfit : CompactFormulaTransformStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states)
    {index : Nat} (hindex : index < states.length - 1) :
    CompactFormulaTransformAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary states.length index mode
        witnessStart witnessFinish witnessCount
        (compactFormulaTransformPublicFittingAdjacentStepRowAt hfit index) := by
  rw [compactFormulaTransformPublicFittingAdjacentStepRowAt, dif_pos hindex]
  exact (Classical.choose_spec (hfit index hindex)).1

theorem compactFormulaTransformPublicFittingAdjacentStepRowAt_currentStatusLayout
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hfit : CompactFormulaTransformStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states)
    {index : Nat} (hindex : index < states.length - 1) :
    CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount
        (compactFormulaTransformPublicFittingAdjacentStepRowAt
          hfit index).currentCoordinates.parserTasksFinish
        (compactFormulaTransformPublicFittingAdjacentStepRowAt
          hfit index).currentCoordinates.parserFinish
        (states.getI index).1.2.2 := by
  rw [compactFormulaTransformPublicFittingAdjacentStepRowAt, dif_pos hindex]
  exact (Classical.choose_spec (hfit index hindex)).2.1

theorem compactFormulaTransformPublicFittingAdjacentStepRowAt_nextStatusLayout
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hfit : CompactFormulaTransformStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states)
    {index : Nat} (hindex : index < states.length - 1) :
    CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount
        (compactFormulaTransformPublicFittingAdjacentStepRowAt
          hfit index).nextCoordinates.parserTasksFinish
        (compactFormulaTransformPublicFittingAdjacentStepRowAt
          hfit index).nextCoordinates.parserFinish
        (states.getI (index + 1)).1.2.2 := by
  rw [compactFormulaTransformPublicFittingAdjacentStepRowAt, dif_pos hindex]
  exact (Classical.choose_spec (hfit index hindex)).2.2.1

theorem compactFormulaTransformPublicFittingAdjacentStepRowAt_fit
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hfit : CompactFormulaTransformStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states)
    {index : Nat} (hindex : index < states.length - 1) :
    CompactFormulaTransformAdjacentStepRowFits
      (compactFormulaTransformAdjacentStepPublicWidth width tokenCount)
      (compactFormulaTransformPublicFittingAdjacentStepRowAt hfit index) := by
  rw [compactFormulaTransformPublicFittingAdjacentStepRowAt, dif_pos hindex]
  exact (Classical.choose_spec (hfit index hindex)).2.2.2

noncomputable def compactFormulaTransformPublicFittingAdjacentStepRows
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hfit : CompactFormulaTransformStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states) :
    List CompactFormulaTransformAdjacentStepRow :=
  (List.range (states.length - 1)).map
    (compactFormulaTransformPublicFittingAdjacentStepRowAt hfit)

@[simp] theorem compactFormulaTransformPublicFittingAdjacentStepRows_length
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hfit : CompactFormulaTransformStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states) :
    (compactFormulaTransformPublicFittingAdjacentStepRows hfit).length =
      states.length - 1 := by
  simp [compactFormulaTransformPublicFittingAdjacentStepRows]

theorem compactFormulaTransformPublicFittingAdjacentStepRows_valid
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hfit : CompactFormulaTransformStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states) :
    CompactFormulaTransformAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length mode
        witnessStart witnessFinish witnessCount
        (compactFormulaTransformPublicFittingAdjacentStepRows hfit) := by
  intro rowIndex hrowIndex
  have hindex : rowIndex < states.length - 1 := by
    simpa using hrowIndex
  rw [List.getI_eq_getElem _ hrowIndex]
  simpa [compactFormulaTransformPublicFittingAdjacentStepRows] using
    compactFormulaTransformPublicFittingAdjacentStepRowAt_graph hfit hindex

theorem compactFormulaTransformPublicFittingAdjacentStepRows_fit
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hfit : CompactFormulaTransformStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states) :
    CompactFormulaTransformAdjacentStepRowsFit
      (compactFormulaTransformAdjacentStepPublicWidth width tokenCount)
      (compactFormulaTransformPublicFittingAdjacentStepRows hfit) := by
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨index, hindex, rfl⟩
  exact compactFormulaTransformPublicFittingAdjacentStepRowAt_fit hfit
    (List.mem_range.mp hindex)

theorem compactFormulaTransformPublicFittingAdjacentStepDynamicWidth_le
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hfit : CompactFormulaTransformStateListAdjacentStepRowsWithFit
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states) :
    compactFormulaTransformAdjacentStepDynamicWidth
        (compactFormulaTransformPublicFittingAdjacentStepRows hfit) ≤
      (states.length - 1) *
        compactFormulaTransformAdjacentStepWitnessColumnCount *
        compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
  calc
    compactFormulaTransformAdjacentStepDynamicWidth
          (compactFormulaTransformPublicFittingAdjacentStepRows hfit) ≤
        (compactFormulaTransformPublicFittingAdjacentStepRows hfit).length *
          compactFormulaTransformAdjacentStepWitnessColumnCount *
          compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
      apply compactFormulaTransformAdjacentStepDynamicWidth_le
      intro row hrow value hvalue
      exact (compactFormulaTransformPublicFittingAdjacentStepRows_fit
        hfit row hrow).value_size_le hvalue
    _ = (states.length - 1) *
          compactFormulaTransformAdjacentStepWitnessColumnCount *
          compactFormulaTransformAdjacentStepPublicWidth width tokenCount := by
      rw [compactFormulaTransformPublicFittingAdjacentStepRows_length]

theorem CompactFormulaTransformAdjacentStepRowGraph.toCurrentBounded
    {tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount tableWidth : Nat}
    {row : CompactFormulaTransformAdjacentStepRow}
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount row)
    (hfit : CompactFormulaTransformAdjacentStepRowFits tableWidth row)
    (hcurrentStatus : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount row.currentCoordinates.parserTasksFinish
        row.currentCoordinates.parserFinish (2 ^ tableWidth))
    (hnextStatus : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount row.nextCoordinates.parserTasksFinish
        row.nextCoordinates.parserFinish (2 ^ tableWidth)) :
    CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount (2 ^ tableWidth) := by
  have hall (value : Nat)
      (hvalue : value ∈ compactFormulaTransformAdjacentStepRowValues row) :
      value ≤ 2 ^ tableWidth :=
    (Nat.size_le.mp (hfit.value_size_le hvalue)).le
  unfold CompactFormulaTransformAdjacentCurrentBounded
    CompactFormulaTransformAdjacentNextBounded
    CompactFormulaTransformAdjacentStepWitnessBounded
  refine ⟨
    row.currentCoordinates.start, ?_,
    row.currentCoordinates.finish, ?_,
    row.currentCoordinates.parserFinish, ?_,
    row.currentCoordinates.parserTokensFinish, ?_,
    row.currentCoordinates.parserTasksFinish, ?_,
    row.currentCoordinates.parserTokensBoundary, ?_,
    row.currentCoordinates.parserTokensCount, ?_,
    row.currentCoordinates.parserTasksBoundary, ?_,
    row.currentCoordinates.parserTasksCount, ?_,
    row.currentCoordinates.outputBoundary, ?_,
    row.currentCoordinates.outputCount, ?_,
    row.currentSize.parserTokensBoundarySize, ?_,
    row.currentSize.parserTasksBoundarySize, ?_,
    row.currentSize.outputBoundarySize, ?_,
    row.nextCoordinates.start, ?_,
    row.nextCoordinates.finish, ?_,
    row.nextCoordinates.parserFinish, ?_,
    row.nextCoordinates.parserTokensFinish, ?_,
    row.nextCoordinates.parserTasksFinish, ?_,
    row.nextCoordinates.parserTokensBoundary, ?_,
    row.nextCoordinates.parserTokensCount, ?_,
    row.nextCoordinates.parserTasksBoundary, ?_,
    row.nextCoordinates.parserTasksCount, ?_,
    row.nextCoordinates.outputBoundary, ?_,
    row.nextCoordinates.outputCount, ?_,
    row.nextSize.parserTokensBoundarySize, ?_,
    row.nextSize.parserTasksBoundarySize, ?_,
    row.nextSize.outputBoundarySize, ?_,
    row.stepWitness.slot0, ?_,
    row.stepWitness.slot1, ?_,
    row.stepWitness.slot2, ?_,
    row.stepWitness.slot3, ?_,
    row.stepWitness.slot4, ?_,
    row.stepWitness.slot5, ?_,
    row.stepWitness.slot6, ?_,
    row.consumedCount, ?_,
    row.mappedHead, ?_, ?_, hcurrentStatus, hnextStatus⟩
  all_goals
    first
    | apply hall
      simp [compactFormulaTransformAdjacentStepRowValues]
    | convert hgraph using 1 <;>
        simp [compactFormulaTransformStateRowCoordinatesOf]

theorem CompactFormulaTransformAdjacentCurrentBounded.exists_row
    {tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount tableWidth : Nat}
    (hbounded : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount (2 ^ tableWidth)) :
    ∃ row : CompactFormulaTransformAdjacentStepRow,
      CompactFormulaTransformAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount row ∧
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount row.currentCoordinates.parserTasksFinish
          row.currentCoordinates.parserFinish (2 ^ tableWidth) ∧
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount row.nextCoordinates.parserTasksFinish
          row.nextCoordinates.parserFinish (2 ^ tableWidth) := by
  unfold CompactFormulaTransformAdjacentCurrentBounded
    CompactFormulaTransformAdjacentNextBounded
    CompactFormulaTransformAdjacentStepWitnessBounded at hbounded
  rcases hbounded with
    ⟨currentStart, _, currentFinish, _, currentParserFinish, _,
      currentParserTokensFinish, _, currentParserTasksFinish, _,
      currentParserTokensBoundary, _, currentParserTokensCount, _,
      currentParserTasksBoundary, _, currentParserTasksCount, _,
      currentOutputBoundary, _, currentOutputCount, _,
      currentParserTokensBoundarySize, _,
      currentParserTasksBoundarySize, _, currentOutputBoundarySize, _,
      nextStart, _, nextFinish, _, nextParserFinish, _,
      nextParserTokensFinish, _, nextParserTasksFinish, _,
      nextParserTokensBoundary, _, nextParserTokensCount, _,
      nextParserTasksBoundary, _, nextParserTasksCount, _,
      nextOutputBoundary, _, nextOutputCount, _,
      nextParserTokensBoundarySize, _, nextParserTasksBoundarySize, _,
      nextOutputBoundarySize, _,
      slot0, _, slot1, _, slot2, _, slot3, _, slot4, _, slot5, _, slot6, _,
      consumedCount, _, mappedHead, _,
      hgraph, hcurrentStatus, hnextStatus⟩
  let row := compactFormulaTransformAdjacentStepRowOfValues
    currentStart currentFinish currentParserFinish
    currentParserTokensFinish currentParserTasksFinish
    currentParserTokensBoundary currentParserTokensCount
    currentParserTasksBoundary currentParserTasksCount
    currentOutputBoundary currentOutputCount
    currentParserTokensBoundarySize currentParserTasksBoundarySize
    currentOutputBoundarySize
    nextStart nextFinish nextParserFinish
    nextParserTokensFinish nextParserTasksFinish
    nextParserTokensBoundary nextParserTokensCount
    nextParserTasksBoundary nextParserTasksCount
    nextOutputBoundary nextOutputCount
    nextParserTokensBoundarySize nextParserTasksBoundarySize
    nextOutputBoundarySize
    slot0 slot1 slot2 slot3 slot4 slot5 slot6 consumedCount mappedHead
  refine ⟨row, ?_, ?_, ?_⟩
  · simpa [row, compactFormulaTransformAdjacentStepRowOfValues] using hgraph
  · simpa [row, compactFormulaTransformAdjacentStepRowOfValues] using
      hcurrentStatus
  · simpa [row, compactFormulaTransformAdjacentStepRowOfValues] using
      hnextStatus

theorem CompactFormulaTransformAdjacentCurrentBounded.sound
    {tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount tableWidth : Nat}
    {witness : List Nat}
    (hbounded : CompactFormulaTransformAdjacentCurrentBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount (2 ^ tableWidth))
    (hwitness : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hwitnessCount : witnessCount = witness.length) :
    ∃ row : CompactFormulaTransformAdjacentStepRow,
    ∃ current next : CompactFormulaTransformState,
      CompactFormulaTransformAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount row ∧
      CompactFormulaTransformStateFixedLayout
        tokenTable width tokenCount row.currentCoordinates current ∧
      CompactFormulaTransformStateFixedLayout
        tokenTable width tokenCount row.nextCoordinates next ∧
      next = compactFormulaTransformStep (mode, witness) current := by
  rcases CompactFormulaTransformAdjacentCurrentBounded.exists_row hbounded with
    ⟨row, hgraph, hcurrentStatus, hnextStatus⟩
  rcases hgraph with ⟨hcurrentAt, hnextAt, hstepRows⟩
  rcases CompactFormulaTransformStateCoreGraph.realizeWithStatusBounded
      hcurrentAt.2.2.2 hcurrentStatus with
    ⟨current, hcurrentLayout⟩
  rcases CompactFormulaTransformStateCoreGraph.realizeWithStatusBounded
      hnextAt.2.2.2 hnextStatus with
    ⟨next, hnextLayout⟩
  have hstep : next = compactFormulaTransformStep (mode, witness) current :=
    compactFormulaTransformStepRows_sound
      hcurrentLayout hnextLayout hwitness hwitnessCount
        ⟨row.stepWitness, row.consumedCount, row.mappedHead, hstepRows⟩
  exact ⟨row, current, next, ⟨hcurrentAt, hnextAt, hstepRows⟩,
    hcurrentLayout, hnextLayout, hstep⟩

theorem stateListAdjacentStepRows_exists_boundedFormula
    {tokenTable width tokenCount stateBoundary mode
      witnessStart witnessFinish witnessCount : Nat}
    {states : List CompactFormulaTransformState}
    (hadjacent : CompactFormulaTransformStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary mode
        witnessStart witnessFinish witnessCount states) :
    ∃ tableWidth,
      compactFormulaTransformAdjacentRowsBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, states.length,
          states.length - 1, mode, witnessStart, witnessFinish, witnessCount,
          tableWidth, 2 ^ tableWidth] := by
  let rows := compactFormulaTransformFittingAdjacentStepRows hadjacent
  let tableWidth :=
    compactFormulaTransformAdjacentStepDynamicWidth rows +
      (tokenCount + 1) * tokenCount
  have hvalid : CompactFormulaTransformAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length mode
        witnessStart witnessFinish witnessCount rows :=
    compactFormulaTransformFittingAdjacentStepRows_valid hadjacent
  have hfit : CompactFormulaTransformAdjacentStepRowsFit tableWidth rows := by
    have hdynamic := compactFormulaTransformAdjacentStepRowsFit_dynamic rows
    intro row hrow column hcolumn
    exact (hdynamic row hrow column hcolumn).trans (by
      simp [tableWidth])
  have harea : (tokenCount + 1) * tokenCount ≤ tableWidth := by
    simp [tableWidth]
  refine ⟨tableWidth,
    (compactFormulaTransformAdjacentRowsBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length
        (states.length - 1) mode witnessStart witnessFinish witnessCount
        tableWidth (2 ^ tableWidth)).mpr ⟨rfl, ?_⟩⟩
  intro rowIndex hrowIndex
  have hrowIndex' : rowIndex < rows.length := by
    simpa [rows] using hrowIndex
  have hrowGraph := hvalid rowIndex hrowIndex'
  have hrowMem : rows.getI rowIndex ∈ rows := by
    rw [List.getI_eq_getElem _ hrowIndex']
    exact List.getElem_mem hrowIndex'
  have hcurrentStatusLayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount
        (rows.getI rowIndex).currentCoordinates.parserTasksFinish
        (rows.getI rowIndex).currentCoordinates.parserFinish
        (states.getI rowIndex).1.2.2 := by
    rw [List.getI_eq_getElem _ hrowIndex']
    simpa [rows, compactFormulaTransformFittingAdjacentStepRows] using
      compactFormulaTransformFittingAdjacentStepRowAt_currentStatusLayout
        hadjacent hrowIndex
  have hnextStatusLayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount
        (rows.getI rowIndex).nextCoordinates.parserTasksFinish
        (rows.getI rowIndex).nextCoordinates.parserFinish
        (states.getI (rowIndex + 1)).1.2.2 := by
    rw [List.getI_eq_getElem _ hrowIndex']
    simpa [rows, compactFormulaTransformFittingAdjacentStepRows] using
      compactFormulaTransformFittingAdjacentStepRowAt_nextStatusLayout
        hadjacent hrowIndex
  exact CompactFormulaTransformAdjacentStepRowGraph.toCurrentBounded hrowGraph
    (hfit (rows.getI rowIndex) hrowMem)
    (CompactBinaryNatStreamStatusDirectLayout.validBounded
      hcurrentStatusLayout harea)
    (CompactBinaryNatStreamStatusDirectLayout.validBounded
      hnextStatusLayout harea)

#print axioms compactFormulaTransformFittingAdjacentStepRows_valid
#print axioms compactFormulaTransformFittingAdjacentStepRowAt_currentStatusLayout
#print axioms compactFormulaTransformFittingAdjacentStepRowAt_nextStatusLayout
#print axioms CompactFormulaTransformAdjacentStepRowGraph.toCurrentBounded
#print axioms CompactFormulaTransformAdjacentCurrentBounded.exists_row
#print axioms CompactFormulaTransformAdjacentCurrentBounded.sound
#print axioms stateListAdjacentStepRows_exists_boundedFormula

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedInstallation
