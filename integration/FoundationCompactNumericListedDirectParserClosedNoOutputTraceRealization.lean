import integration.FoundationCompactNumericListedDirectParserClosedNoOutputExactFormula
import integration.FoundationCompactNumericListedDirectParserStateLayout

/-!
# Self-contained realization of closed-parser no-output traces

Every bounded adjacent row is decoded into two typed states.  Shared boundary
entries identify neighboring states, including the closed parser's explicit
free-variable failure transition.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedNoOutputTraceRealization

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateLayout
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserClosedAdjacentStepFormula
open FoundationCompactNumericListedDirectParserClosedAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserClosedAdjacentStepBoundedInstallation
open FoundationCompactNumericListedDirectParserClosedNoOutputTraceFormula
open FoundationCompactNumericListedDirectParserClosedNoOutputExactFormula

structure CompactParserClosedBoundedStepRealization
    (tokenTable width tokenCount stateBoundary stateCount index : Nat) where
  row : CompactParserSyntaxAdjacentStepRow
  current : CompactUnifiedParserState
  next : CompactUnifiedParserState
  graph : CompactParserClosedAdjacentStepRowGraph
    tokenTable width tokenCount stateBoundary stateCount index row
  currentLayout : CompactUnifiedParserStateFixedLayout
    tokenTable width tokenCount row.currentCoordinates current
  nextLayout : CompactUnifiedParserStateFixedLayout
    tokenTable width tokenCount row.nextCoordinates next

theorem compactParserClosedBoundedStepRealization_exists
    {tokenTable width tokenCount stateBoundary stateCount index tableWidth : Nat}
    (hbounded : CompactParserClosedAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount index
        (2 ^ tableWidth)) :
    Nonempty (CompactParserClosedBoundedStepRealization
      tokenTable width tokenCount stateBoundary stateCount index) := by
  rcases CompactParserClosedAdjacentRowBounded.sound hbounded with
    ⟨row, current, next, hgraph, hcurrent, hnext, _hstep⟩
  exact ⟨⟨row, current, next, hgraph, hcurrent, hnext⟩⟩

noncomputable def compactParserClosedBoundedStepAt
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound : Nat}
    (hadjacent : CompactParserClosedAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (index : Fin fuel) :
    CompactParserClosedBoundedStepRealization
      tokenTable width tokenCount stateBoundary stateCount index :=
  Classical.choice (by
    have hbounded := hadjacent.2 index index.isLt
    rw [hadjacent.1] at hbounded
    exact compactParserClosedBoundedStepRealization_exists hbounded)

def compactParserClosedLastIndex (fuel : Nat) (hfuel : 0 < fuel) : Fin fuel :=
  ⟨fuel - 1, by omega⟩

noncomputable def compactParserClosedRealizedStateAt
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound : Nat}
    (hadjacent : CompactParserClosedAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (hfuel : 0 < fuel) (index : Fin (fuel + 1)) :
    CompactUnifiedParserState :=
  if hindex : index.1 < fuel then
    (compactParserClosedBoundedStepAt hadjacent ⟨index.1, hindex⟩).current
  else
    (compactParserClosedBoundedStepAt hadjacent
      (compactParserClosedLastIndex fuel hfuel)).next

noncomputable def compactParserClosedRealizedStates
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound : Nat}
    (hadjacent : CompactParserClosedAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (hfuel : 0 < fuel) : List CompactUnifiedParserState :=
  List.ofFn (compactParserClosedRealizedStateAt hadjacent hfuel)

@[simp] theorem compactParserClosedRealizedStates_length
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound : Nat}
    (hadjacent : CompactParserClosedAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (hfuel : 0 < fuel) :
    (compactParserClosedRealizedStates hadjacent hfuel).length = fuel + 1 := by
  simp [compactParserClosedRealizedStates]

theorem compactParserClosedRealizedStates_getI_current
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound index : Nat}
    (hadjacent : CompactParserClosedAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (hfuel : 0 < fuel) (hindex : index < fuel) :
    (compactParserClosedRealizedStates hadjacent hfuel).getI index =
      (compactParserClosedBoundedStepAt hadjacent ⟨index, hindex⟩).current := by
  have hlistIndex : index <
      (compactParserClosedRealizedStates hadjacent hfuel).length := by
    simp only [compactParserClosedRealizedStates_length]
    omega
  rw [List.getI_eq_getElem _ hlistIndex]
  change (List.ofFn
    (compactParserClosedRealizedStateAt hadjacent hfuel)).get
      ⟨index, by simp; omega⟩ = _
  rw [List.get_ofFn]
  simp [compactParserClosedRealizedStateAt, hindex]

theorem compactParserClosedRealizedStates_getI_final
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound : Nat}
    (hadjacent : CompactParserClosedAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (hfuel : 0 < fuel) :
    (compactParserClosedRealizedStates hadjacent hfuel).getI fuel =
      (compactParserClosedBoundedStepAt hadjacent
        (compactParserClosedLastIndex fuel hfuel)).next := by
  have hlistIndex : fuel <
      (compactParserClosedRealizedStates hadjacent hfuel).length := by
    simp only [compactParserClosedRealizedStates_length]
    omega
  rw [List.getI_eq_getElem _ hlistIndex]
  change (List.ofFn
    (compactParserClosedRealizedStateAt hadjacent hfuel)).get
      ⟨fuel, by simp⟩ = _
  rw [List.get_ofFn]
  simp [compactParserClosedRealizedStateAt]

theorem compactParserClosedRealizedStates_rows
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound : Nat}
    (hadjacent : CompactParserClosedAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (hfuel : 0 < fuel) :
    CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary
        (compactParserClosedRealizedStates hadjacent hfuel) := by
  intro index hindex
  have hindexFuel : index < fuel + 1 := by
    simpa only [compactParserClosedRealizedStates_length] using hindex
  by_cases hcurrent : index < fuel
  · let realized := compactParserClosedBoundedStepAt hadjacent
      ⟨index, hcurrent⟩
    have hstate :
        (compactParserClosedRealizedStates hadjacent hfuel).getI index =
          realized.current := by
      simpa only [realized] using
        compactParserClosedRealizedStates_getI_current
          hadjacent hfuel hcurrent
    have hat := realized.graph.1
    rcases hat.2.2.2.1 with
      ⟨hstartMiddle, hmiddleFinish, hfinishBound⟩
    have hstartBound : realized.row.currentCoordinates.start ≤ tokenCount :=
      (Nat.le_of_lt (hstartMiddle.trans hmiddleFinish)).trans hfinishBound
    have hdirect : CompactUnifiedParserStateDirectLayout
        tokenTable width tokenCount realized.row.currentCoordinates.start
          realized.row.currentCoordinates.finish realized.current :=
      (compactUnifiedParserStateDirectLayout_iff_fixedCoordinates
        tokenTable width tokenCount realized.row.currentCoordinates.start
          realized.row.currentCoordinates.finish realized.current).mpr
        ⟨realized.row.currentCoordinates, rfl, rfl,
          realized.currentLayout⟩
    refine ⟨realized.row.currentCoordinates.start, hstartBound,
      realized.row.currentCoordinates.finish, hfinishBound,
      hat.2.1, hat.2.2.1, ?_⟩
    simpa only [hstate] using hdirect
  · have hfinal : index = fuel := by omega
    subst index
    let last := compactParserClosedBoundedStepAt hadjacent
      (compactParserClosedLastIndex fuel hfuel)
    have hstate :
        (compactParserClosedRealizedStates hadjacent hfuel).getI fuel =
          last.next := by
      simpa only [last] using
        compactParserClosedRealizedStates_getI_final hadjacent hfuel
    have hat := last.graph.2.1
    have hlast : fuel - 1 + 1 = fuel := by omega
    rcases hat.2.2.2.1 with
      ⟨hstartMiddle, hmiddleFinish, hfinishBound⟩
    have hstartBound : last.row.nextCoordinates.start ≤ tokenCount :=
      (Nat.le_of_lt (hstartMiddle.trans hmiddleFinish)).trans hfinishBound
    have hstartEntry :
        FoundationCompactNumericListedDirectArithmeticPrimitives.CompactFixedWidthEntry
          stateBoundary tokenCount fuel last.row.nextCoordinates.start := by
      simpa [compactParserClosedLastIndex, hlast] using hat.2.1
    have hfinishEntry :
        FoundationCompactNumericListedDirectArithmeticPrimitives.CompactFixedWidthEntry
          stateBoundary tokenCount (fuel + 1)
            last.row.nextCoordinates.finish := by
      simpa [compactParserClosedLastIndex, hlast] using hat.2.2.1
    have hdirect : CompactUnifiedParserStateDirectLayout
        tokenTable width tokenCount last.row.nextCoordinates.start
          last.row.nextCoordinates.finish last.next :=
      (compactUnifiedParserStateDirectLayout_iff_fixedCoordinates
        tokenTable width tokenCount last.row.nextCoordinates.start
          last.row.nextCoordinates.finish last.next).mpr
        ⟨last.row.nextCoordinates, rfl, rfl, last.nextLayout⟩
    refine ⟨last.row.nextCoordinates.start, hstartBound,
      last.row.nextCoordinates.finish, hfinishBound,
      hstartEntry, hfinishEntry, ?_⟩
    simpa only [hstate] using hdirect

theorem CompactParserClosedNoOutputTraceBoundedGraph.realize
    {tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat}
    {input : List Nat}
    (hgraph : CompactParserClosedNoOutputTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound)
    (hfuel : 0 < fuel)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout
        tokenTable width tokenCount inputBoundary input) :
    ∃ states : List CompactUnifiedParserState,
      states.length = stateCount ∧
      CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount stateBoundary states ∧
      CompactParserOutputLocalTraceValid FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep fuel
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
        none states := by
  rcases hgraph with ⟨hstateCount, hinitialFinal, hadjacent⟩
  let states := compactParserClosedRealizedStates hadjacent hfuel
  have hlengthFuel : states.length = fuel + 1 := by
    simp [states]
  have hlength : states.length = stateCount := by omega
  have hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states :=
    compactParserClosedRealizedStates_rows hadjacent hfuel
  have hvalid := CompactParserClosedNoOutputTraceBoundedGraph.sound
    (hgraph := ⟨hstateCount, hinitialFinal, hadjacent⟩)
    hlength hrows hinput
  exact ⟨states, hlength, hrows, hvalid⟩

theorem CompactParserClosedNoOutputExactBoundedGraph.realize
    {tokenTable width tokenCount stateBoundary stateCount inputBoundary
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat}
    {input : List Nat}
    (hgraph : CompactParserClosedNoOutputExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout
        tokenTable width tokenCount inputBoundary input) :
    ∃ states : List CompactUnifiedParserState,
      states.length = stateCount ∧
      CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount stateBoundary states ∧
      CompactParserOutputLocalTraceValid FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep
        (compactSyntaxRunFuelBound input)
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
        none states := by
  have htrace : CompactParserClosedNoOutputTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound := by
    simpa [CompactParserClosedNoOutputExactBoundedGraph,
      compactSyntaxRunFuelBound] using hgraph
  have hfuel : 0 < compactSyntaxRunFuelBound input := by
    simp [compactSyntaxRunFuelBound]
  exact CompactParserClosedNoOutputTraceBoundedGraph.realize
    htrace hfuel hinput


#print axioms compactParserClosedBoundedStepRealization_exists
#print axioms compactParserClosedRealizedStates_rows
#print axioms CompactParserClosedNoOutputTraceBoundedGraph.realize
#print axioms CompactParserClosedNoOutputExactBoundedGraph.realize

end FoundationCompactNumericListedDirectParserClosedNoOutputTraceRealization
