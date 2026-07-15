import integration.FoundationCompactNumericListedDirectParserClosedAdjacentStepBoundedFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedInstallation

/-!
# Installation of complete bounded closed-parser rows

A closed-parser trace supplies one exact arithmetic row for every consecutive
state pair, including the absorbing failure step.  Canonical row selection and
one shared width install the complete closed-step relation without a detached
safety table or an additional witness family.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedAdjacentStepBoundedInstallation

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformTraceInstallation
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceInstallation
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedInstallation
open FoundationCompactNumericListedDirectParserClosedStepFormula
open FoundationCompactNumericListedDirectParserClosedAdjacentStepFormula
open FoundationCompactNumericListedDirectParserClosedAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

def CompactParserClosedAdjacentStepRowsValid
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rows : List CompactParserSyntaxAdjacentStepRow) : Prop :=
  ∀ rowIndex < rows.length,
    CompactParserClosedAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        (rows.getI rowIndex)

noncomputable def compactParserClosedFittingAdjacentStepRowAt
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserClosedStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states)
    (index : Nat) : CompactParserSyntaxAdjacentStepRow :=
  if hindex : index < states.length - 1 then
    Classical.choose (hadjacent index hindex)
  else
    default

theorem compactParserClosedFittingAdjacentStepRowAt_graph
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserClosedStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states)
    {index : Nat} (hindex : index < states.length - 1) :
    CompactParserClosedAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary states.length index
        (compactParserClosedFittingAdjacentStepRowAt hadjacent index) := by
  rw [compactParserClosedFittingAdjacentStepRowAt, dif_pos hindex]
  exact Classical.choose_spec (hadjacent index hindex)

noncomputable def compactParserClosedFittingAdjacentStepRows
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserClosedStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states) :
    List CompactParserSyntaxAdjacentStepRow :=
  (List.range (states.length - 1)).map
    (compactParserClosedFittingAdjacentStepRowAt hadjacent)

@[simp] theorem compactParserClosedFittingAdjacentStepRows_length
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserClosedStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states) :
    (compactParserClosedFittingAdjacentStepRows hadjacent).length =
      states.length - 1 := by
  simp [compactParserClosedFittingAdjacentStepRows]

theorem compactParserClosedFittingAdjacentStepRows_valid
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List CompactUnifiedParserState}
    (hadjacent : CompactUnifiedParserClosedStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states) :
    CompactParserClosedAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length
        (compactParserClosedFittingAdjacentStepRows hadjacent) := by
  intro rowIndex hrowIndex
  have hindex : rowIndex < states.length - 1 := by
    simpa using hrowIndex
  rw [List.getI_eq_getElem _ hrowIndex]
  simpa [compactParserClosedFittingAdjacentStepRows] using
    compactParserClosedFittingAdjacentStepRowAt_graph hadjacent hindex

theorem CompactParserClosedAdjacentStepRowGraph.toBounded
    {tokenTable width tokenCount stateBoundary stateCount rowIndex
      tableWidth : Nat}
    {row : CompactParserSyntaxAdjacentStepRow}
    (hgraph : CompactParserClosedAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex row)
    (hfit : CompactParserSyntaxAdjacentStepRowFits tableWidth row)
    (hcurrentStatus : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount row.currentCoordinates.tasksFinish
        row.currentCoordinates.finish (2 ^ tableWidth))
    (hnextStatus : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount row.nextCoordinates.tasksFinish
        row.nextCoordinates.finish (2 ^ tableWidth)) :
    CompactParserClosedAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        (2 ^ tableWidth) := by
  have hall (value : Nat)
      (hvalue : value ∈ compactParserSyntaxAdjacentStepRowValues row) :
      value ≤ 2 ^ tableWidth :=
    (Nat.size_le.mp (hfit.value_size_le hvalue)).le
  unfold CompactParserClosedAdjacentRowBounded
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
    | simpa [compactParserClosedAdjacentStepRowOfValues,
        compactUnifiedParserStateRowCoordinatesOf] using hgraph

theorem CompactParserClosedAdjacentRowBounded.exists_row
    {tokenTable width tokenCount stateBoundary stateCount rowIndex
      tableWidth : Nat}
    (hbounded : CompactParserClosedAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        (2 ^ tableWidth)) :
    ∃ row : CompactParserSyntaxAdjacentStepRow,
      CompactParserClosedAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex row ∧
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount row.currentCoordinates.tasksFinish
          row.currentCoordinates.finish (2 ^ tableWidth) ∧
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount row.nextCoordinates.tasksFinish
          row.nextCoordinates.finish (2 ^ tableWidth) := by
  unfold CompactParserClosedAdjacentRowBounded at hbounded
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
  let row := compactParserClosedAdjacentStepRowOfValues
    currentStart currentFinish currentTokensFinish currentTasksFinish
    currentTokensBoundary currentTokensCount currentTasksBoundary
    currentTasksCount currentTokensBoundarySize currentTasksBoundarySize
    nextStart nextFinish nextTokensFinish nextTasksFinish nextTokensBoundary
    nextTokensCount nextTasksBoundary nextTasksCount nextTokensBoundarySize
    nextTasksBoundarySize slot0 slot1 slot2 slot3 slot4 slot5 slot6
  refine ⟨row, ?_, ?_, ?_⟩
  · simpa [row, compactParserClosedAdjacentStepRowOfValues] using hgraph
  · simpa [row, compactParserClosedAdjacentStepRowOfValues,
      compactUnifiedParserStateRowCoordinatesOf] using hcurrentStatus
  · simpa [row, compactParserClosedAdjacentStepRowOfValues,
      compactUnifiedParserStateRowCoordinatesOf] using hnextStatus

theorem CompactParserClosedAdjacentRowBounded.sound
    {tokenTable width tokenCount stateBoundary stateCount rowIndex
      tableWidth : Nat}
    (hbounded : CompactParserClosedAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        (2 ^ tableWidth)) :
    ∃ row : CompactParserSyntaxAdjacentStepRow,
    ∃ current next : CompactUnifiedParserState,
      CompactParserClosedAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex row ∧
      CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount row.currentCoordinates current ∧
      CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount row.nextCoordinates next ∧
      next = compactClosedSyntaxParserStep current := by
  rcases CompactParserClosedAdjacentRowBounded.exists_row hbounded with
    ⟨row, hgraph, hcurrentStatus, hnextStatus⟩
  have hcurrentAt := hgraph.1
  have hnextAt := hgraph.2.1
  rcases CompactUnifiedParserStateCoreGraph.realizeWithStatusBounded
      hcurrentAt.2.2.2 hcurrentStatus with
    ⟨current, hcurrentLayout⟩
  rcases CompactUnifiedParserStateCoreGraph.realizeWithStatusBounded
      hnextAt.2.2.2 hnextStatus with
    ⟨next, hnextLayout⟩
  have hstep : next = compactClosedSyntaxParserStep current :=
    compactUnifiedParserClosedStepRows_sound
      hcurrentLayout hnextLayout ⟨row.stepWitness, hgraph.2.2⟩
  exact ⟨row, current, next, hgraph,
    hcurrentLayout, hnextLayout, hstep⟩

theorem closedLocalTrace_exists_compactParserClosedAdjacentRowsBoundedFormula
    {tokenTable width tokenCount stateBoundary fuel : Nat}
    {start : CompactUnifiedParserState}
    {result : Option (List Nat)} {states : List CompactUnifiedParserState}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed start.2.1)
    (hvalid : CompactParserOutputLocalTraceValid
      compactClosedSyntaxParserStep fuel start result states) :
    ∃ tableWidth,
      compactParserClosedAdjacentRowsBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, states.length, fuel,
          tableWidth, 2 ^ tableWidth] := by
  have hadjacent : CompactUnifiedParserClosedStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states :=
    closedStateListAdjacentStepRows_of_localTrace
      hrows hvalid.1 hstartWell
  let rows := compactParserClosedFittingAdjacentStepRows hadjacent
  let tableWidth :=
    compactParserSyntaxAdjacentStepDynamicWidth rows +
      (tokenCount + 1) * tokenCount
  have hrowsValid : CompactParserClosedAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length rows :=
    compactParserClosedFittingAdjacentStepRows_valid hadjacent
  have hfit : CompactParserSyntaxAdjacentStepRowsFit tableWidth rows := by
    have hdynamic := compactParserSyntaxAdjacentStepRowsFit_dynamic rows
    intro row hrow column hcolumn
    exact (hdynamic row hrow column hcolumn).trans (by simp [tableWidth])
  have harea : (tokenCount + 1) * tokenCount ≤ tableWidth := by
    simp [tableWidth]
  refine ⟨tableWidth,
    (compactParserClosedAdjacentRowsBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length fuel
        tableWidth (2 ^ tableWidth)).mpr ⟨rfl, ?_⟩⟩
  intro rowIndex hrowIndex
  have hrowIndexSub : rowIndex < states.length - 1 := by
    rw [hvalid.1.1]
    omega
  have hrowIndex' : rowIndex < rows.length := by
    simpa [rows] using hrowIndexSub
  have hrowGraph := hrowsValid rowIndex hrowIndex'
  have hrowMem : rows.getI rowIndex ∈ rows := by
    rw [List.getI_eq_getElem _ hrowIndex']
    exact List.getElem_mem hrowIndex'
  have hcurrentLayout := CompactUnifiedParserStateAtRows.fixedLayout_of_rows
    rfl hrows hrowGraph.1
  have hcurrentStatusLayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount
        (rows.getI rowIndex).currentCoordinates.tasksFinish
        (rows.getI rowIndex).currentCoordinates.finish
        (states.getI rowIndex).2.2 := hcurrentLayout.statusLayout
  have hnextStatusLayout : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount
        (rows.getI rowIndex).nextCoordinates.tasksFinish
        (rows.getI rowIndex).nextCoordinates.finish
        (states.getI (rowIndex + 1)).2.2 :=
    (CompactUnifiedParserStateAtRows.fixedLayout_of_rows
      rfl hrows hrowGraph.2.1).statusLayout
  exact CompactParserClosedAdjacentStepRowGraph.toBounded
    hrowGraph (hfit (rows.getI rowIndex) hrowMem)
    (CompactBinaryNatStreamStatusDirectLayout.validBounded
      hcurrentStatusLayout harea)
    (CompactBinaryNatStreamStatusDirectLayout.validBounded
      hnextStatusLayout harea)

#print axioms CompactParserClosedAdjacentStepRowGraph.toBounded
#print axioms compactParserClosedFittingAdjacentStepRowAt_graph
#print axioms compactParserClosedFittingAdjacentStepRows_valid
#print axioms CompactParserClosedAdjacentRowBounded.exists_row
#print axioms CompactParserClosedAdjacentRowBounded.sound
#print axioms closedLocalTrace_exists_compactParserClosedAdjacentRowsBoundedFormula

end FoundationCompactNumericListedDirectParserClosedAdjacentStepBoundedInstallation
