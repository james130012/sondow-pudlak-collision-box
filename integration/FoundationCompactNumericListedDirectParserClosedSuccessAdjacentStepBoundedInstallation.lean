import integration.FoundationCompactNumericListedDirectParserClosedSuccessAdjacentStepBoundedFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedInstallation

/-!
# Installation of bounded successful closed-parser rows

The ordinary syntax trace supplies the canonical finite row table.  Successful
closed parsing supplies safety for the same current state at every row.  Their
combination therefore installs the closed-success relation without a detached
safety table or an additional witness family.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedSuccessAdjacentStepBoundedInstallation

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
open FoundationCompactNumericListedDirectParserClosedSuccessBridge
open FoundationCompactNumericListedDirectParserClosedSuccessStepFormula
open FoundationCompactNumericListedDirectParserClosedSuccessAdjacentStepFormula
open FoundationCompactNumericListedDirectParserClosedSuccessAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusValidity

theorem CompactParserClosedSuccessAdjacentStepRowGraph.toBounded
    {tokenTable width tokenCount stateBoundary stateCount rowIndex
      tableWidth : Nat}
    {row : CompactParserSyntaxAdjacentStepRow}
    (hgraph : CompactParserClosedSuccessAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex row)
    (hfit : CompactParserSyntaxAdjacentStepRowFits tableWidth row)
    (hcurrentStatus : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount row.currentCoordinates.tasksFinish
        row.currentCoordinates.finish (2 ^ tableWidth))
    (hnextStatus : CompactBinaryNatStatusValidBounded
      tokenTable width tokenCount row.nextCoordinates.tasksFinish
        row.nextCoordinates.finish (2 ^ tableWidth)) :
    CompactParserClosedSuccessAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        (2 ^ tableWidth) := by
  have hall (value : Nat)
      (hvalue : value ∈ compactParserSyntaxAdjacentStepRowValues row) :
      value ≤ 2 ^ tableWidth :=
    (Nat.size_le.mp (hfit.value_size_le hvalue)).le
  unfold CompactParserClosedSuccessAdjacentRowBounded
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
    | simpa [compactParserClosedSuccessAdjacentStepRowOfValues,
        compactUnifiedParserStateRowCoordinatesOf] using hgraph

theorem CompactParserClosedSuccessAdjacentRowBounded.exists_row
    {tokenTable width tokenCount stateBoundary stateCount rowIndex
      tableWidth : Nat}
    (hbounded : CompactParserClosedSuccessAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        (2 ^ tableWidth)) :
    ∃ row : CompactParserSyntaxAdjacentStepRow,
      CompactParserClosedSuccessAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex row ∧
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount row.currentCoordinates.tasksFinish
          row.currentCoordinates.finish (2 ^ tableWidth) ∧
      CompactBinaryNatStatusValidBounded
        tokenTable width tokenCount row.nextCoordinates.tasksFinish
          row.nextCoordinates.finish (2 ^ tableWidth) := by
  unfold CompactParserClosedSuccessAdjacentRowBounded at hbounded
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
  let row := compactParserClosedSuccessAdjacentStepRowOfValues
    currentStart currentFinish currentTokensFinish currentTasksFinish
    currentTokensBoundary currentTokensCount currentTasksBoundary
    currentTasksCount currentTokensBoundarySize currentTasksBoundarySize
    nextStart nextFinish nextTokensFinish nextTasksFinish nextTokensBoundary
    nextTokensCount nextTasksBoundary nextTasksCount nextTokensBoundarySize
    nextTasksBoundarySize slot0 slot1 slot2 slot3 slot4 slot5 slot6
  refine ⟨row, ?_, ?_, ?_⟩
  · simpa [row, compactParserClosedSuccessAdjacentStepRowOfValues] using hgraph
  · simpa [row, compactParserClosedSuccessAdjacentStepRowOfValues,
      compactUnifiedParserStateRowCoordinatesOf] using hcurrentStatus
  · simpa [row, compactParserClosedSuccessAdjacentStepRowOfValues,
      compactUnifiedParserStateRowCoordinatesOf] using hnextStatus

theorem CompactParserClosedSuccessAdjacentRowBounded.sound
    {tokenTable width tokenCount stateBoundary stateCount rowIndex
      tableWidth : Nat}
    (hbounded : CompactParserClosedSuccessAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        (2 ^ tableWidth)) :
    ∃ row : CompactParserSyntaxAdjacentStepRow,
    ∃ current next : CompactUnifiedParserState,
      CompactParserClosedSuccessAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex row ∧
      CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount row.currentCoordinates current ∧
      CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount row.nextCoordinates next ∧
      next = compactClosedSyntaxParserStep current := by
  rcases CompactParserClosedSuccessAdjacentRowBounded.exists_row hbounded with
    ⟨row, hgraph, hcurrentStatus, hnextStatus⟩
  rcases hgraph.1 with ⟨hcurrentAt, hnextAt, _hordinaryStepRows⟩
  rcases CompactUnifiedParserStateCoreGraph.realizeWithStatusBounded
      hcurrentAt.2.2.2 hcurrentStatus with
    ⟨current, hcurrentLayout⟩
  rcases CompactUnifiedParserStateCoreGraph.realizeWithStatusBounded
      hnextAt.2.2.2 hnextStatus with
    ⟨next, hnextLayout⟩
  have hstep : next = compactClosedSyntaxParserStep current :=
    compactUnifiedParserClosedSuccessStepRows_sound
      hcurrentLayout hnextLayout hgraph.2
  exact ⟨row, current, next, hgraph,
    hcurrentLayout, hnextLayout, hstep⟩

theorem closedLocalTrace_exists_compactParserClosedSuccessAdjacentRowsBoundedFormula
    {tokenTable width tokenCount stateBoundary fuel : Nat}
    {start : CompactUnifiedParserState}
    {suffix : List Nat} {states : List CompactUnifiedParserState}
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed start.2.1)
    (hvalid : CompactParserOutputLocalTraceValid
      compactClosedSyntaxParserStep fuel start (some suffix) states) :
    ∃ tableWidth,
      compactParserClosedSuccessAdjacentRowsBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, stateBoundary, states.length, fuel,
          tableWidth, 2 ^ tableWidth] := by
  have hsyntax := CompactParserOutputLocalTraceValid.closed_to_syntax hvalid
  have hadjacent : CompactUnifiedParserSyntaxStateListAdjacentStepRows
      tokenTable width tokenCount stateBoundary states :=
    syntaxStateListAdjacentStepRows_of_localTrace
      hrows hsyntax.1 hstartWell
  let rows := compactParserSyntaxFittingAdjacentStepRows hadjacent
  let tableWidth :=
    compactParserSyntaxAdjacentStepDynamicWidth rows +
      (tokenCount + 1) * tokenCount
  have hrowsValid : CompactParserSyntaxAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary states.length rows :=
    compactParserSyntaxFittingAdjacentStepRows_valid hadjacent
  have hfit : CompactParserSyntaxAdjacentStepRowsFit tableWidth rows := by
    have hdynamic := compactParserSyntaxAdjacentStepRowsFit_dynamic rows
    intro row hrow column hcolumn
    exact (hdynamic row hrow column hcolumn).trans (by simp [tableWidth])
  have harea : (tokenCount + 1) * tokenCount ≤ tableWidth := by
    simp [tableWidth]
  refine ⟨tableWidth,
    (compactParserClosedSuccessAdjacentRowsBoundedGraphDef_spec
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
  have hclosedGraph : CompactParserClosedSuccessAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary states.length rowIndex
        (rows.getI rowIndex) :=
    CompactParserSyntaxAdjacentStepRowGraph.toClosedSuccess
      hrowGraph hcurrentLayout
        (CompactParserOutputLocalTraceValid.closed_safe_at
          hvalid (Nat.le_of_lt hrowIndex))
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
  exact CompactParserClosedSuccessAdjacentStepRowGraph.toBounded
    hclosedGraph (hfit (rows.getI rowIndex) hrowMem)
    (CompactBinaryNatStreamStatusDirectLayout.validBounded
      hcurrentStatusLayout harea)
    (CompactBinaryNatStreamStatusDirectLayout.validBounded
      hnextStatusLayout harea)

#print axioms CompactParserClosedSuccessAdjacentStepRowGraph.toBounded
#print axioms CompactParserClosedSuccessAdjacentRowBounded.exists_row
#print axioms CompactParserClosedSuccessAdjacentRowBounded.sound
#print axioms closedLocalTrace_exists_compactParserClosedSuccessAdjacentRowsBoundedFormula

end FoundationCompactNumericListedDirectParserClosedSuccessAdjacentStepBoundedInstallation
