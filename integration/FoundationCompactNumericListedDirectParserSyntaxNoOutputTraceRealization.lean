import integration.FoundationCompactNumericListedDirectParserSyntaxTraceRealization
import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputExactFormula

/-!
# Self-contained realization of a no-output syntax-parser trace

The already bounded adjacent rows determine every typed state.  Combining
those reconstructed rows with the no-output endpoint yields the exact public
parser result without accepting a typed state list as input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxNoOutputTraceRealization

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxTraceRealization
open FoundationCompactNumericListedDirectParserSyntaxNoOutputTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactFormula

theorem CompactParserSyntaxNoOutputTraceBoundedGraph.realize
    {tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat}
    {input : List Nat}
    (hgraph : CompactParserSyntaxNoOutputTraceBoundedGraph
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
      CompactParserOutputLocalTraceValid compactSyntaxParserStep fuel
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
        none states := by
  rcases hgraph with ⟨hstateCount, hinitialFinal, hadjacent⟩
  let states := compactParserSyntaxRealizedStates hadjacent hfuel
  have hlengthFuel : states.length = fuel + 1 := by
    simp [states]
  have hlength : states.length = stateCount := by omega
  have hrows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states :=
    compactParserSyntaxRealizedStates_rows hadjacent hfuel
  have hvalid := CompactParserSyntaxNoOutputTraceBoundedGraph.sound
    (hgraph := ⟨hstateCount, hinitialFinal, hadjacent⟩)
    hlength hrows hinput
  exact ⟨states, hlength, hrows, hvalid⟩

theorem CompactParserSyntaxNoOutputExactBoundedGraph.realize
    {tokenTable width tokenCount stateBoundary stateCount inputBoundary
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat}
    {input : List Nat}
    (hgraph : CompactParserSyntaxNoOutputExactBoundedGraph
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
      CompactParserOutputLocalTraceValid compactSyntaxParserStep
        (compactSyntaxRunFuelBound input)
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
        none states := by
  have htrace : CompactParserSyntaxNoOutputTraceBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound := by
    simpa [CompactParserSyntaxNoOutputExactBoundedGraph,
      compactSyntaxRunFuelBound] using hgraph
  have hfuel : 0 < compactSyntaxRunFuelBound input := by
    simp [compactSyntaxRunFuelBound]
  exact CompactParserSyntaxNoOutputTraceBoundedGraph.realize
    htrace hfuel hinput

#print axioms CompactParserSyntaxNoOutputTraceBoundedGraph.realize
#print axioms CompactParserSyntaxNoOutputExactBoundedGraph.realize

end FoundationCompactNumericListedDirectParserSyntaxNoOutputTraceRealization
