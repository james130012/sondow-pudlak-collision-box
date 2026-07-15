import integration.FoundationCompactNumericListedDirectParserSyntaxExactFormula

/-!
# Self-contained realization of a bounded syntax-parser trace

The adjacent bounded rows determine a typed state at every trace index.  The
last state is taken from the next side of the final adjacent row.  This removes
the need to supply a typed parser-state list to the soundness theorem.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxTraceRealization

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateLayout
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedInstallation
open FoundationCompactNumericListedDirectParserSyntaxTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFormula

structure CompactParserSyntaxBoundedStepRealization
    (tokenTable width tokenCount stateBoundary stateCount index : Nat) where
  row : CompactParserSyntaxAdjacentStepRow
  current : CompactUnifiedParserState
  next : CompactUnifiedParserState
  graph : CompactParserSyntaxAdjacentStepRowGraph
    tokenTable width tokenCount stateBoundary stateCount index row
  currentLayout : CompactUnifiedParserStateFixedLayout
    tokenTable width tokenCount row.currentCoordinates current
  nextLayout : CompactUnifiedParserStateFixedLayout
    tokenTable width tokenCount row.nextCoordinates next

theorem compactParserSyntaxBoundedStepRealization_exists
    {tokenTable width tokenCount stateBoundary stateCount index tableWidth : Nat}
    (hbounded : CompactParserSyntaxAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount index
        (2 ^ tableWidth)) :
    Nonempty (CompactParserSyntaxBoundedStepRealization
      tokenTable width tokenCount stateBoundary stateCount index) := by
  rcases CompactParserSyntaxAdjacentRowBounded.sound hbounded with
    ⟨row, current, next, hgraph, hcurrent, hnext, _hstep⟩
  exact ⟨⟨row, current, next, hgraph, hcurrent, hnext⟩⟩

noncomputable def compactParserSyntaxBoundedStepAt
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound : Nat}
    (hadjacent : CompactParserSyntaxAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (index : Fin fuel) :
    CompactParserSyntaxBoundedStepRealization
      tokenTable width tokenCount stateBoundary stateCount index :=
  Classical.choice (by
    have hbounded := hadjacent.2 index index.isLt
    rw [hadjacent.1] at hbounded
    exact compactParserSyntaxBoundedStepRealization_exists hbounded)

def compactParserSyntaxLastIndex (fuel : Nat) (hfuel : 0 < fuel) : Fin fuel :=
  ⟨fuel - 1, by omega⟩

noncomputable def compactParserSyntaxRealizedStateAt
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound : Nat}
    (hadjacent : CompactParserSyntaxAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (hfuel : 0 < fuel) (index : Fin (fuel + 1)) :
    CompactUnifiedParserState :=
  if hindex : index.1 < fuel then
    (compactParserSyntaxBoundedStepAt hadjacent ⟨index.1, hindex⟩).current
  else
    (compactParserSyntaxBoundedStepAt hadjacent
      (compactParserSyntaxLastIndex fuel hfuel)).next

noncomputable def compactParserSyntaxRealizedStates
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound : Nat}
    (hadjacent : CompactParserSyntaxAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (hfuel : 0 < fuel) : List CompactUnifiedParserState :=
  List.ofFn (compactParserSyntaxRealizedStateAt hadjacent hfuel)

@[simp] theorem compactParserSyntaxRealizedStates_length
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound : Nat}
    (hadjacent : CompactParserSyntaxAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (hfuel : 0 < fuel) :
    (compactParserSyntaxRealizedStates hadjacent hfuel).length = fuel + 1 := by
  simp [compactParserSyntaxRealizedStates]

theorem compactParserSyntaxRealizedStates_getI_current
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound index : Nat}
    (hadjacent : CompactParserSyntaxAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (hfuel : 0 < fuel) (hindex : index < fuel) :
    (compactParserSyntaxRealizedStates hadjacent hfuel).getI index =
      (compactParserSyntaxBoundedStepAt hadjacent ⟨index, hindex⟩).current := by
  have hlistIndex : index <
      (compactParserSyntaxRealizedStates hadjacent hfuel).length := by
    simp only [compactParserSyntaxRealizedStates_length]
    omega
  rw [List.getI_eq_getElem _ hlistIndex]
  change (List.ofFn
    (compactParserSyntaxRealizedStateAt hadjacent hfuel)).get
      ⟨index, by simp; omega⟩ = _
  rw [List.get_ofFn]
  simp [compactParserSyntaxRealizedStateAt, hindex]

theorem compactParserSyntaxRealizedStates_getI_final
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound : Nat}
    (hadjacent : CompactParserSyntaxAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (hfuel : 0 < fuel) :
    (compactParserSyntaxRealizedStates hadjacent hfuel).getI fuel =
      (compactParserSyntaxBoundedStepAt hadjacent
        (compactParserSyntaxLastIndex fuel hfuel)).next := by
  have hlistIndex : fuel <
      (compactParserSyntaxRealizedStates hadjacent hfuel).length := by
    simp only [compactParserSyntaxRealizedStates_length]
    omega
  rw [List.getI_eq_getElem _ hlistIndex]
  change (List.ofFn
    (compactParserSyntaxRealizedStateAt hadjacent hfuel)).get
      ⟨fuel, by simp⟩ = _
  rw [List.get_ofFn]
  simp [compactParserSyntaxRealizedStateAt]

theorem compactParserSyntaxRealizedStates_rows
    {tokenTable width tokenCount stateBoundary stateCount fuel
      tableWidth valueBound : Nat}
    (hadjacent : CompactParserSyntaxAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
        tableWidth valueBound)
    (hfuel : 0 < fuel) :
    CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary
        (compactParserSyntaxRealizedStates hadjacent hfuel) := by
  intro index hindex
  have hindexFuel : index < fuel + 1 := by
    simpa only [compactParserSyntaxRealizedStates_length] using hindex
  by_cases hcurrent : index < fuel
  · let realized := compactParserSyntaxBoundedStepAt hadjacent
      ⟨index, hcurrent⟩
    have hstate :
        (compactParserSyntaxRealizedStates hadjacent hfuel).getI index =
          realized.current := by
      simpa only [realized] using
        compactParserSyntaxRealizedStates_getI_current
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
    let last := compactParserSyntaxBoundedStepAt hadjacent
      (compactParserSyntaxLastIndex fuel hfuel)
    have hstate :
        (compactParserSyntaxRealizedStates hadjacent hfuel).getI fuel =
          last.next := by
      simpa only [last] using
        compactParserSyntaxRealizedStates_getI_final hadjacent hfuel
    have hat := last.graph.2.1
    have hlast : fuel - 1 + 1 = fuel := by omega
    rcases hat.2.2.2.1 with
      ⟨hstartMiddle, hmiddleFinish, hfinishBound⟩
    have hstartBound : last.row.nextCoordinates.start ≤ tokenCount :=
      (Nat.le_of_lt (hstartMiddle.trans hmiddleFinish)).trans hfinishBound
    have hstartEntry :
        FoundationCompactNumericListedDirectArithmeticPrimitives.CompactFixedWidthEntry
          stateBoundary tokenCount fuel last.row.nextCoordinates.start := by
      simpa [compactParserSyntaxLastIndex, hlast] using hat.2.1
    have hfinishEntry :
        FoundationCompactNumericListedDirectArithmeticPrimitives.CompactFixedWidthEntry
          stateBoundary tokenCount (fuel + 1)
            last.row.nextCoordinates.finish := by
      simpa [compactParserSyntaxLastIndex, hlast] using hat.2.2.1
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

theorem CompactParserSyntaxTraceBoundedGraph.realize
    {tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary expectedBoundary taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat}
    {input expected : List Nat}
    (hgraph : CompactParserSyntaxTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary input.length expectedBoundary expected.length
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound)
    (hfuel : 0 < fuel)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout
        tokenTable width tokenCount inputBoundary input)
    (hexpected : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout
        tokenTable width tokenCount expectedBoundary expected) :
    ∃ states : List CompactUnifiedParserState,
      states.length = stateCount ∧
      CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount stateBoundary states ∧
      CompactParserOutputLocalTraceValid compactSyntaxParserStep fuel
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
        (some expected) states := by
  rcases hgraph with ⟨hstateCount, hinitialFinal, hadjacent⟩
  let states := compactParserSyntaxRealizedStates hadjacent hfuel
  have hlengthFuel : states.length = fuel + 1 := by
    simp [states]
  have hlength : states.length = stateCount := by omega
  have hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states := by
    exact compactParserSyntaxRealizedStates_rows hadjacent hfuel
  have hvalid := CompactParserSyntaxTraceBoundedGraph.sound
    (hgraph := ⟨hstateCount, hinitialFinal, hadjacent⟩)
    hlength hrows hinput hexpected
  exact ⟨states, hlength, hrows, hvalid⟩

theorem CompactParserSyntaxExactBoundedGraph.realize_formula
    {tokenTable width tokenCount stateBoundary stateCount
      inputBoundary expectedBoundary binderArity tableWidth valueBound : Nat}
    {input expected : List Nat}
    (hgraph : CompactParserSyntaxExactBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      inputBoundary input.length expectedBoundary expected.length
      1 binderArity 0 tableWidth valueBound)
    (hinput : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout
        tokenTable width tokenCount inputBoundary input)
    (hexpected : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout
        tokenTable width tokenCount expectedBoundary expected) :
    ∃ states : List CompactUnifiedParserState,
      states.length = stateCount ∧
      CompactUnifiedParserStateListRowLayouts
        tokenTable width tokenCount stateBoundary states ∧
      CompactFormulaTokenParserDirectTraceValid
        binderArity input expected states := by
  have htrace : CompactParserSyntaxTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length expectedBoundary expected.length
      1 binderArity 0 tableWidth valueBound := by
    simpa [CompactParserSyntaxExactBoundedGraph,
      compactSyntaxRunFuelBound] using hgraph
  have hfuel : 0 < compactSyntaxRunFuelBound input := by
    simp [compactSyntaxRunFuelBound]
  rcases CompactParserSyntaxTraceBoundedGraph.realize
      htrace hfuel hinput hexpected with
    ⟨states, hlength, hrows, hvalid⟩
  refine ⟨states, hlength, hrows, ?_⟩
  simpa [CompactFormulaTokenParserDirectTraceValid,
    compactFormulaParserInitialState, compactFormulaTask] using hvalid

#print axioms compactParserSyntaxBoundedStepRealization_exists
#print axioms compactParserSyntaxRealizedStates_rows
#print axioms CompactParserSyntaxTraceBoundedGraph.realize
#print axioms CompactParserSyntaxExactBoundedGraph.realize_formula

end FoundationCompactNumericListedDirectParserSyntaxTraceRealization
