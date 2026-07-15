import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable

/-!
# Installation of the bounded adjacent syntax-parser formula

Canonical rows from a typed parser trace are selected in index order.  One
explicit width bounds all twenty-seven row fields and both nested status
payloads.  Conversely, every bounded row realizes two typed parser states and
one exact public syntax-parser step.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedInstallation

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceInstallation
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

noncomputable def compactParserSyntaxFittingAdjacentStepRowAt
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserSyntaxStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states)
    (index : Nat) : CompactParserSyntaxAdjacentStepRow :=
  if hindex : index < states.length - 1 then
    Classical.choose
      ((syntaxStateListAdjacentStepRows_iff_exists_adjacentStepRow.mp hadjacent)
        index hindex)
  else
    default

theorem compactParserSyntaxFittingAdjacentStepRowAt_graph
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserSyntaxStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states)
    {index : Nat} (hindex : index < states.length - 1) :
    CompactParserSyntaxAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary states.length index
        (compactParserSyntaxFittingAdjacentStepRowAt hadjacent index) := by
  rw [compactParserSyntaxFittingAdjacentStepRowAt, dif_pos hindex]
  exact Classical.choose_spec
    ((syntaxStateListAdjacentStepRows_iff_exists_adjacentStepRow.mp hadjacent)
      index hindex)

noncomputable def compactParserSyntaxFittingAdjacentStepRows
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserSyntaxStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states) :
    List CompactParserSyntaxAdjacentStepRow :=
  (List.range (states.length - 1)).map
    (compactParserSyntaxFittingAdjacentStepRowAt hadjacent)

@[simp] theorem compactParserSyntaxFittingAdjacentStepRows_length
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserSyntaxStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states) :
    (compactParserSyntaxFittingAdjacentStepRows hadjacent).length =
      states.length - 1 := by
  simp [compactParserSyntaxFittingAdjacentStepRows]

theorem compactParserSyntaxFittingAdjacentStepRows_valid
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserSyntaxStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states) :
    CompactParserSyntaxAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length
        (compactParserSyntaxFittingAdjacentStepRows hadjacent) := by
  intro rowIndex hrowIndex
  have hindex : rowIndex < states.length - 1 := by
    simpa using hrowIndex
  rw [List.getI_eq_getElem _ hrowIndex]
  simpa [compactParserSyntaxFittingAdjacentStepRows] using
    compactParserSyntaxFittingAdjacentStepRowAt_graph hadjacent hindex

theorem CompactParserSyntaxAdjacentStepRowGraph.toBounded
    {tokenTable width tokenCount stateBoundary stateCount rowIndex
      tableWidth : Nat}
    {row : CompactParserSyntaxAdjacentStepRow}
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex row)
    (hfit : CompactParserSyntaxAdjacentStepRowFits tableWidth row)
    (hcurrentStatus : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount row.currentCoordinates.tasksFinish
        row.currentCoordinates.finish (2 ^ tableWidth))
    (hnextStatus : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount row.nextCoordinates.tasksFinish
        row.nextCoordinates.finish (2 ^ tableWidth)) :
    CompactParserSyntaxAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        (2 ^ tableWidth) := by
  have hall (value : Nat)
      (hvalue : value ∈ compactParserSyntaxAdjacentStepRowValues row) :
      value ≤ 2 ^ tableWidth :=
    (Nat.size_le.mp (hfit.value_size_le hvalue)).le
  unfold CompactParserSyntaxAdjacentRowBounded
  refine ⟨
    row.currentCoordinates.start, ?_,
    row.currentCoordinates.finish, ?_,
    row.currentCoordinates.tokensFinish, ?_,
    row.currentCoordinates.tasksFinish, ?_,
    row.currentCoordinates.tokensBoundary, ?_,
    row.currentCoordinates.tokensCount, ?_,
    row.currentCoordinates.tasksBoundary, ?_,
    row.currentCoordinates.tasksCount, ?_,
    row.currentSize.tokensBoundarySize, ?_,
    row.currentSize.tasksBoundarySize, ?_,
    row.nextCoordinates.start, ?_,
    row.nextCoordinates.finish, ?_,
    row.nextCoordinates.tokensFinish, ?_,
    row.nextCoordinates.tasksFinish, ?_,
    row.nextCoordinates.tokensBoundary, ?_,
    row.nextCoordinates.tokensCount, ?_,
    row.nextCoordinates.tasksBoundary, ?_,
    row.nextCoordinates.tasksCount, ?_,
    row.nextSize.tokensBoundarySize, ?_,
    row.nextSize.tasksBoundarySize, ?_,
    row.stepWitness.slot0, ?_,
    row.stepWitness.slot1, ?_,
    row.stepWitness.slot2, ?_,
    row.stepWitness.slot3, ?_,
    row.stepWitness.slot4, ?_,
    row.stepWitness.slot5, ?_,
    row.stepWitness.slot6, ?_, ?_, hcurrentStatus, hnextStatus⟩
  all_goals
    first
    | apply hall
      simp [compactParserSyntaxAdjacentStepRowValues]
    | simpa [compactParserSyntaxAdjacentStepRowOfValues,
        compactUnifiedParserStateRowCoordinatesOf] using hgraph

theorem CompactParserSyntaxAdjacentRowBounded.exists_row
    {tokenTable width tokenCount stateBoundary stateCount rowIndex
      tableWidth : Nat}
    (hbounded : CompactParserSyntaxAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        (2 ^ tableWidth)) :
    ∃ row : CompactParserSyntaxAdjacentStepRow,
      CompactParserSyntaxAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex row ∧
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount row.currentCoordinates.tasksFinish
          row.currentCoordinates.finish (2 ^ tableWidth) ∧
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount row.nextCoordinates.tasksFinish
          row.nextCoordinates.finish (2 ^ tableWidth) := by
  unfold CompactParserSyntaxAdjacentRowBounded at hbounded
  rcases hbounded with
    ⟨currentStart, _, currentFinish, _, currentTokensFinish, _,
      currentTasksFinish, _, currentTokensBoundary, _, currentTokensCount, _,
      currentTasksBoundary, _, currentTasksCount, _,
      currentTokensBoundarySize, _, currentTasksBoundarySize, _,
      nextStart, _, nextFinish, _, nextTokensFinish, _, nextTasksFinish, _,
      nextTokensBoundary, _, nextTokensCount, _, nextTasksBoundary, _,
      nextTasksCount, _, nextTokensBoundarySize, _, nextTasksBoundarySize, _,
      slot0, _, slot1, _, slot2, _, slot3, _, slot4, _, slot5, _, slot6, _,
      hgraph, hcurrentStatus, hnextStatus⟩
  let row := compactParserSyntaxAdjacentStepRowOfValues
    currentStart currentFinish currentTokensFinish currentTasksFinish
    currentTokensBoundary currentTokensCount currentTasksBoundary
    currentTasksCount currentTokensBoundarySize currentTasksBoundarySize
    nextStart nextFinish nextTokensFinish nextTasksFinish nextTokensBoundary
    nextTokensCount nextTasksBoundary nextTasksCount nextTokensBoundarySize
    nextTasksBoundarySize slot0 slot1 slot2 slot3 slot4 slot5 slot6
  refine ⟨row, ?_, ?_, ?_⟩
  · simpa [row, compactParserSyntaxAdjacentStepRowOfValues] using hgraph
  · simpa [row, compactParserSyntaxAdjacentStepRowOfValues,
      compactUnifiedParserStateRowCoordinatesOf] using
      hcurrentStatus
  · simpa [row, compactParserSyntaxAdjacentStepRowOfValues,
      compactUnifiedParserStateRowCoordinatesOf] using
      hnextStatus

theorem compactUnifiedParserStateCoreFixedLayout_withStatusFixed
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactUnifiedParserStateRowCoordinates}
    {tokens : List Nat}
    {tasks : List FoundationCompactSyntaxTokenMachine.CompactSyntaxTask}
    {status : Option (Option (List Nat))}
    (hcore : CompactUnifiedParserStateCoreFixedLayout
      tokenTable width tokenCount coordinates tokens tasks)
    (hstatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount coordinates.tasksFinish
        coordinates.finish status) :
    CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount coordinates (tokens, tasks, status) :=
  { tokensCount_eq := hcore.tokensCount_eq
    tasksCount_eq := hcore.tasksCount_eq
    outerSplit := hcore.outerSplit
    tokensLayout := hcore.tokensLayout
    tokensRows := hcore.tokensRows
    innerSplit := hcore.innerSplit
    tasksLayout := hcore.tasksLayout
    tasksRows := hcore.tasksRows
    statusLayout := hstatus
    tokensBoundarySize := hcore.tokensBoundarySize
    tasksBoundarySize := hcore.tasksBoundarySize }

theorem CompactUnifiedParserStateCoreGraph.realizeWithStatusBounded
    {tokenTable width tokenCount valueBound : Nat}
    {coordinates : CompactUnifiedParserStateRowCoordinates}
    {sizeWitness : CompactUnifiedParserStateCoreSizeWitness}
    (hgraph : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (hstatus : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount coordinates.tasksFinish
        coordinates.finish valueBound) :
    ∃ state : CompactUnifiedParserState,
      CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount coordinates state := by
  rcases hgraph.realize with ⟨tokens, tasks, hcore⟩
  rcases hstatus with
    ⟨outputStart, _houtputStart, outputBoundary, _houtputBoundary,
      outputBoundarySize, _houtputBoundarySize, outputCount, _houtputCount,
      hvalid⟩
  rcases hvalid.realize with ⟨status, hstatusLayout⟩
  exact ⟨(tokens, tasks, status),
    compactUnifiedParserStateCoreFixedLayout_withStatusFixed
      hcore hstatusLayout⟩

theorem CompactParserSyntaxAdjacentRowBounded.sound
    {tokenTable width tokenCount stateBoundary stateCount rowIndex
      tableWidth : Nat}
    (hbounded : CompactParserSyntaxAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        (2 ^ tableWidth)) :
    ∃ row : CompactParserSyntaxAdjacentStepRow,
    ∃ current next : CompactUnifiedParserState,
      CompactParserSyntaxAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex row ∧
      CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount row.currentCoordinates current ∧
      CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount row.nextCoordinates next ∧
      next = compactSyntaxParserStep current := by
  rcases CompactParserSyntaxAdjacentRowBounded.exists_row hbounded with
    ⟨row, hgraph, hcurrentStatus, hnextStatus⟩
  rcases hgraph with ⟨hcurrentAt, hnextAt, hstepRows⟩
  rcases CompactUnifiedParserStateCoreGraph.realizeWithStatusBounded
      hcurrentAt.2.2.2 hcurrentStatus with
    ⟨current, hcurrentLayout⟩
  rcases CompactUnifiedParserStateCoreGraph.realizeWithStatusBounded
      hnextAt.2.2.2 hnextStatus with
    ⟨next, hnextLayout⟩
  have hstep : next = compactSyntaxParserStep current :=
    compactUnifiedParserSyntaxStepRows_sound hcurrentLayout hnextLayout
      ⟨row.stepWitness, hstepRows⟩
  exact ⟨row, current, next, ⟨hcurrentAt, hnextAt, hstepRows⟩,
    hcurrentLayout, hnextLayout, hstep⟩

theorem syntaxStateListAdjacentStepRows_exists_boundedFormula
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hstateRows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hadjacent : CompactUnifiedParserSyntaxStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states) :
    ∃ tableWidth,
      compactParserSyntaxAdjacentRowsBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, states.length,
          states.length - 1, tableWidth, 2 ^ tableWidth] := by
  let rows := compactParserSyntaxFittingAdjacentStepRows hadjacent
  let tableWidth :=
    compactParserSyntaxAdjacentStepDynamicWidth rows +
      (tokenCount + 1) * tokenCount
  have hvalid : CompactParserSyntaxAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length rows :=
    compactParserSyntaxFittingAdjacentStepRows_valid hadjacent
  have hfit : CompactParserSyntaxAdjacentStepRowsFit tableWidth rows := by
    have hdynamic := compactParserSyntaxAdjacentStepRowsFit_dynamic rows
    intro row hrow column hcolumn
    exact (hdynamic row hrow column hcolumn).trans (by simp [tableWidth])
  have harea : (tokenCount + 1) * tokenCount ≤ tableWidth := by
    simp [tableWidth]
  refine ⟨tableWidth,
    (compactParserSyntaxAdjacentRowsBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length
        (states.length - 1) tableWidth (2 ^ tableWidth)).mpr ⟨rfl, ?_⟩⟩
  intro rowIndex hrowIndex
  have hrowIndex' : rowIndex < rows.length := by
    simpa [rows] using hrowIndex
  have hrowGraph := hvalid rowIndex hrowIndex'
  have hrowMem : rows.getI rowIndex ∈ rows := by
    rw [List.getI_eq_getElem _ hrowIndex']
    exact List.getElem_mem hrowIndex'
  have hcurrentStatusLayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount
        (rows.getI rowIndex).currentCoordinates.tasksFinish
        (rows.getI rowIndex).currentCoordinates.finish
        (states.getI rowIndex).2.2 :=
    (CompactUnifiedParserStateAtRows.fixedLayout_of_rows
      rfl hstateRows hrowGraph.1).statusLayout
  have hnextStatusLayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount
        (rows.getI rowIndex).nextCoordinates.tasksFinish
        (rows.getI rowIndex).nextCoordinates.finish
        (states.getI (rowIndex + 1)).2.2 :=
    (CompactUnifiedParserStateAtRows.fixedLayout_of_rows
      rfl hstateRows hrowGraph.2.1).statusLayout
  exact CompactParserSyntaxAdjacentStepRowGraph.toBounded hrowGraph
    (hfit (rows.getI rowIndex) hrowMem)
    (CompactBinaryNatStreamStatusDirectLayout.validBounded
      hcurrentStatusLayout harea)
    (CompactBinaryNatStreamStatusDirectLayout.validBounded
      hnextStatusLayout harea)

#print axioms compactParserSyntaxFittingAdjacentStepRows_valid
#print axioms CompactParserSyntaxAdjacentStepRowGraph.toBounded
#print axioms CompactParserSyntaxAdjacentRowBounded.exists_row
#print axioms compactUnifiedParserStateCoreFixedLayout_withStatusFixed
#print axioms CompactUnifiedParserStateCoreGraph.realizeWithStatusBounded
#print axioms CompactParserSyntaxAdjacentRowBounded.sound
#print axioms syntaxStateListAdjacentStepRows_exists_boundedFormula

end FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedInstallation
