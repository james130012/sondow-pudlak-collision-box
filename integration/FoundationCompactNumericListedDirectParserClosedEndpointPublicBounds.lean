import integration.FoundationCompactNumericListedDirectParserClosedEndpointCompleteness
import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds

/-!
# Public bounds for successful closed-formula parser endpoints

The closed parser follows the ordinary syntax-parser transition on every safe
state.  This module reuses the already public ordinary endpoint coordinates and
proves that the same bounded rows also carry the closed-formula safety guard.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedEndpointPublicBounds

open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedInstallation
open FoundationCompactNumericListedDirectParserSyntaxTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds
open FoundationCompactNumericListedDirectParserClosedSuccessAdjacentStepFormula
open FoundationCompactNumericListedDirectParserClosedSuccessAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserClosedSuccessBridge
open FoundationCompactNumericListedDirectParserClosedSuccessTraceFormula
open FoundationCompactNumericListedDirectParserClosedEndpointCompleteness

private theorem
    CompactParserSyntaxAdjacentRowBounded.toClosedSuccess
    {tokenTable width tokenCount stateBoundary stateCount rowIndex
      tableWidth fuel : Nat}
    {states : List CompactUnifiedParserState}
    {start : CompactUnifiedParserState}
    {suffix : List Nat}
    (hbounded : CompactParserSyntaxAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        (2 ^ tableWidth))
    (hcount : states.length = stateCount)
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hindex : rowIndex < fuel)
    (hvalid : CompactParserOutputLocalTraceValid
      compactClosedSyntaxParserStep fuel
      start (some suffix) states) :
    CompactParserClosedSuccessAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        (2 ^ tableWidth) := by
  unfold CompactParserSyntaxAdjacentRowBounded at hbounded
  rcases hbounded with
    ⟨currentStart, hcurrentStart,
      currentFinish, hcurrentFinish,
      currentTokensFinish, hcurrentTokensFinish,
      currentTasksFinish, hcurrentTasksFinish,
      currentTokensBoundary, hcurrentTokensBoundary,
      currentTokensCount, hcurrentTokensCount,
      currentTasksBoundary, hcurrentTasksBoundary,
      currentTasksCount, hcurrentTasksCount,
      currentTokensBoundarySize, hcurrentTokensBoundarySize,
      currentTasksBoundarySize, hcurrentTasksBoundarySize,
      nextStart, hnextStart,
      nextFinish, hnextFinish,
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
      hrow, hcurrentStatus, hnextStatus⟩
  let row :=
    compactParserSyntaxAdjacentStepRowOfValues
      currentStart currentFinish currentTokensFinish currentTasksFinish
      currentTokensBoundary currentTokensCount
      currentTasksBoundary currentTasksCount
      currentTokensBoundarySize currentTasksBoundarySize
      nextStart nextFinish nextTokensFinish nextTasksFinish
      nextTokensBoundary nextTokensCount nextTasksBoundary nextTasksCount
      nextTokensBoundarySize nextTasksBoundarySize
      slot0 slot1 slot2 slot3 slot4 slot5 slot6
  have hrowGraph : CompactParserSyntaxAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex row := by
    simpa only [row] using hrow
  have hcurrentLayout :
      CompactUnifiedParserStateFixedLayout
        tokenTable width tokenCount row.currentCoordinates
          (states.getI rowIndex) :=
    CompactUnifiedParserStateAtRows.fixedLayout_of_rows
      hcount hrows hrowGraph.1
  have hclosedGraph :
      CompactParserClosedSuccessAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex row :=
    CompactParserSyntaxAdjacentStepRowGraph.toClosedSuccess
      hrowGraph hcurrentLayout
        (CompactParserOutputLocalTraceValid.closed_safe_at
          hvalid (Nat.le_of_lt hindex))
  unfold CompactParserClosedSuccessAdjacentRowBounded
  refine
    ⟨currentStart, hcurrentStart,
      currentFinish, hcurrentFinish,
      currentTokensFinish, hcurrentTokensFinish,
      currentTasksFinish, hcurrentTasksFinish,
      currentTokensBoundary, hcurrentTokensBoundary,
      currentTokensCount, hcurrentTokensCount,
      currentTasksBoundary, hcurrentTasksBoundary,
      currentTasksCount, hcurrentTasksCount,
      currentTokensBoundarySize, hcurrentTokensBoundarySize,
      currentTasksBoundarySize, hcurrentTasksBoundarySize,
      nextStart, hnextStart,
      nextFinish, hnextFinish,
      nextTokensFinish, hnextTokensFinish,
      nextTasksFinish, hnextTasksFinish,
      nextTokensBoundary, hnextTokensBoundary,
      nextTokensCount, hnextTokensCount,
      nextTasksBoundary, hnextTasksBoundary,
      nextTasksCount, hnextTasksCount,
      nextTokensBoundarySize, hnextTokensBoundarySize,
      nextTasksBoundarySize, hnextTasksBoundarySize,
      slot0, hslot0, slot1, hslot1, slot2, hslot2, slot3, hslot3,
      slot4, hslot4, slot5, hslot5, slot6, hslot6, ?_,
      hcurrentStatus, hnextStatus⟩
  simpa only [row, compactParserClosedSuccessAdjacentStepRowOfValues,
    compactParserSyntaxAdjacentStepRowOfValues] using hclosedGraph

private theorem
    CompactParserSyntaxExactBoundedGraph.toClosedSuccess
    {tokenTable width tokenCount stateBoundary stateCount
      inputBoundary expectedBoundary taskKind taskBinderArity taskRepeatCount
      tableWidth : Nat}
    {states : List CompactUnifiedParserState}
    {input expected : List Nat}
    (hgraph : CompactParserSyntaxExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      inputBoundary input.length expectedBoundary expected.length
      taskKind taskBinderArity taskRepeatCount tableWidth (2 ^ tableWidth))
    (hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hvalid : CompactParserOutputLocalTraceValid
      compactClosedSyntaxParserStep (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      (some expected) states) :
    CompactParserClosedSuccessTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length expectedBoundary expected.length
      taskKind taskBinderArity taskRepeatCount tableWidth (2 ^ tableWidth) := by
  have hsyntaxTrace : CompactParserSyntaxTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length expectedBoundary expected.length
      taskKind taskBinderArity taskRepeatCount tableWidth (2 ^ tableWidth) := by
    simpa [CompactParserSyntaxExactBoundedGraph,
      compactSyntaxRunFuelBound] using hgraph
  rcases hsyntaxTrace with
    ⟨hstateCount, hinitialFinal, hadjacent⟩
  have hcount : states.length = stateCount :=
    hvalid.1.1.trans hstateCount.symm
  refine ⟨hstateCount, hinitialFinal, hadjacent.1, ?_⟩
  intro rowIndex hrowIndex
  exact CompactParserSyntaxAdjacentRowBounded.toClosedSuccess
    (hadjacent.2 rowIndex hrowIndex) hcount hrows hrowIndex hvalid

/-- The public ordinary parser budget also bounds the exact closed-formula
endpoint, with no additional coordinate or width input. -/
theorem
    exists_compactParserClosedEndpointGraph_of_rows_with_publicBounds
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish stateBoundary binderArity : Nat}
    {input expected : List Nat}
    {states : List CompactUnifiedParserState}
    (hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hexpectedLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount expectedStart expectedFinish expected)
    (hstateRows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hstateBoundarySize :
      Nat.size stateBoundary <= (states.length + 1) * tokenCount)
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, binderArity, 0)])
    (hvalid : CompactParserOutputLocalTraceValid compactClosedSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(1, binderArity, 0)], none) (some expected) states) :
    ∃ coordinates : CompactParserSyntaxExactEndpointCoordinates,
      CompactParserClosedEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            expectedStart expectedFinish binderArity coordinates ∧
        CompactParserSyntaxExactEndpointPublicBounds coordinates
          (compactParserSyntaxExactEndpointPublicCoordinateSizeBound
            width tokenCount) := by
  have hsyntaxValid :
      CompactParserOutputLocalTraceValid compactSyntaxParserStep
        (compactSyntaxRunFuelBound input)
        (input, [(1, binderArity, 0)], none) (some expected) states :=
    CompactParserOutputLocalTraceValid.closed_to_syntax hvalid
  rcases
      exists_compactParserSyntaxExactEndpointGraph_of_rows_with_publicBounds
        hinputLayout hexpectedLayout hstateRows hstateBoundarySize
        hstartWell hsyntaxValid with
    ⟨coordinates, hsyntaxResult⟩
  have hsyntaxEndpoint := hsyntaxResult.1
  have hpublic := hsyntaxResult.2.1
  have hcoordinateStateBoundary := hsyntaxResult.2.2
  rcases hsyntaxEndpoint with
    ⟨hinputWitness, hexpectedWitness, hsyntaxGraph⟩
  rcases hinputWitness.realize with
    ⟨realizedInput, hrealizedInputCount,
      hrealizedInputLayout, _hrealizedInputRows⟩
  have hrealizedInputEq : realizedInput = input :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hrealizedInputLayout hinputLayout).1.symm
  subst realizedInput
  have hinputCountEq : coordinates.inputCount = input.length :=
    hrealizedInputCount.symm
  rcases hexpectedWitness.realize with
    ⟨realizedExpected, hrealizedExpectedCount,
      hrealizedExpectedLayout, _hrealizedExpectedRows⟩
  have hrealizedExpectedEq : realizedExpected = expected :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hrealizedExpectedLayout hexpectedLayout).1.symm
  subst realizedExpected
  have hexpectedCountEq : coordinates.expectedCount = expected.length :=
    hrealizedExpectedCount.symm
  have hsyntaxTrace := hsyntaxGraph
  unfold CompactParserSyntaxExactBoundedGraph at hsyntaxTrace
  have hvalueBoundEq :
      coordinates.valueBound = 2 ^ coordinates.tableWidth :=
    hsyntaxTrace.2.2.1
  have hsyntaxGraph' := hsyntaxGraph
  rw [hinputCountEq, hexpectedCountEq, hvalueBoundEq] at hsyntaxGraph'
  rw [hcoordinateStateBoundary] at hsyntaxGraph'
  have hclosedTrace :
      CompactParserClosedSuccessTraceBoundedGraph
        tokenTable width tokenCount stateBoundary
          coordinates.stateCount (compactSyntaxRunFuelBound input)
          coordinates.inputBoundary input.length
          coordinates.expectedBoundary expected.length
          1 binderArity 0 coordinates.tableWidth
          (2 ^ coordinates.tableWidth) :=
    CompactParserSyntaxExactBoundedGraph.toClosedSuccess
      hsyntaxGraph' hstateRows hvalid
  have hclosedEndpoint :
      CompactParserClosedEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish binderArity coordinates := by
    unfold CompactParserClosedEndpointGraph
    refine ⟨hinputWitness, hexpectedWitness, ?_⟩
    rw [hinputCountEq, hexpectedCountEq, hvalueBoundEq]
    rw [hcoordinateStateBoundary]
    simpa [compactSyntaxRunFuelBound] using hclosedTrace
  exact ⟨coordinates, hclosedEndpoint, hpublic⟩

#print axioms
  exists_compactParserClosedEndpointGraph_of_rows_with_publicBounds

end FoundationCompactNumericListedDirectParserClosedEndpointPublicBounds
