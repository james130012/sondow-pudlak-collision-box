import integration.FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
import integration.FoundationCompactNumericListedDirectParserClosedSuccessTraceFormula

/-!
# Self-contained endpoint for successful closed-formula parsing

The closed parser uses the same reconstructed state table as the ordinary
syntax parser, while every adjacent row additionally carries the real
free-variable safety guard.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedEndpointCompleteness

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactClosedFormulaTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceRealization
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserClosedSuccessAdjacentStepFormula
open FoundationCompactNumericListedDirectParserClosedSuccessAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserClosedSuccessTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

def CompactParserClosedEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity : Nat)
    (coordinates : CompactParserSyntaxExactEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount
        inputFinish coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount expectedStart coordinates.expectedCount
        expectedFinish coordinates.expectedBoundary
        coordinates.expectedBoundarySize ∧
    CompactParserClosedSuccessTraceBoundedGraph
      tokenTable width tokenCount coordinates.stateBoundary
        coordinates.stateCount
        (16 * (coordinates.inputCount + 1) *
          (coordinates.inputCount + 1) + 8)
        coordinates.inputBoundary coordinates.inputCount
        coordinates.expectedBoundary coordinates.expectedCount
        1 binderArity 0 coordinates.tableWidth coordinates.valueBound

theorem CompactParserClosedSuccessAdjacentRowBounded.toSyntax
    {tokenTable width tokenCount stateBoundary stateCount rowIndex
      valueBound : Nat}
    (hclosed : CompactParserClosedSuccessAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        valueBound) :
    CompactParserSyntaxAdjacentRowBounded
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        valueBound := by
  unfold CompactParserClosedSuccessAdjacentRowBounded at hclosed
  unfold CompactParserSyntaxAdjacentRowBounded
  rcases hclosed with
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
  simpa [compactParserClosedSuccessAdjacentStepRowOfValues,
    compactParserSyntaxAdjacentStepRowOfValues] using hrow.1

theorem CompactParserClosedSuccessAdjacentRowsBoundedGraph.toSyntax
    {tokenTable width tokenCount stateBoundary stateCount rowCount
      tableWidth valueBound : Nat}
    (hclosed : CompactParserClosedSuccessAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount rowCount
        tableWidth valueBound) :
    CompactParserSyntaxAdjacentRowsBoundedGraph
      tokenTable width tokenCount stateBoundary stateCount rowCount
        tableWidth valueBound := by
  refine ⟨hclosed.1, ?_⟩
  intro rowIndex hrowIndex
  exact CompactParserClosedSuccessAdjacentRowBounded.toSyntax
    (hclosed.2 rowIndex hrowIndex)

theorem CompactParserClosedEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity : Nat}
    {coordinates : CompactParserSyntaxExactEndpointCoordinates}
    (hgraph : CompactParserClosedEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish binderArity coordinates) :
    ∃ input expected : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount expectedStart expectedFinish expected ∧
      compactClosedFormulaTokenParser binderArity input = some expected := by
  rcases hgraph with ⟨hinputWitness, hexpectedWitness, hclosed⟩
  rcases hinputWitness.realize with
    ⟨input, hinputCount, hinputLayout, hinputRows⟩
  rcases hexpectedWitness.realize with
    ⟨expected, hexpectedCount, hexpectedLayout, hexpectedRows⟩
  have hfuelEq :
      16 * (coordinates.inputCount + 1) *
          (coordinates.inputCount + 1) + 8 =
        compactSyntaxRunFuelBound input := by
    simp [compactSyntaxRunFuelBound, hinputCount]
  have hsyntaxAdjacent : CompactParserSyntaxAdjacentRowsBoundedGraph
      tokenTable width tokenCount coordinates.stateBoundary
        coordinates.stateCount (compactSyntaxRunFuelBound input)
        coordinates.tableWidth coordinates.valueBound := by
    rw [← hfuelEq]
    exact CompactParserClosedSuccessAdjacentRowsBoundedGraph.toSyntax
      hclosed.2.2
  have hsyntaxTrace : CompactParserSyntaxTraceBoundedGraph
      tokenTable width tokenCount coordinates.stateBoundary
        coordinates.stateCount (compactSyntaxRunFuelBound input)
        coordinates.inputBoundary input.length
        coordinates.expectedBoundary expected.length
        1 binderArity 0 coordinates.tableWidth coordinates.valueBound := by
    refine ⟨?_, ?_, hsyntaxAdjacent⟩
    · rw [← hfuelEq]
      exact hclosed.1
    · simpa [hinputCount, hexpectedCount, hfuelEq] using hclosed.2.1
  have hfuel : 0 < compactSyntaxRunFuelBound input := by
    simp [compactSyntaxRunFuelBound]
  rcases CompactParserSyntaxTraceBoundedGraph.realize
      hsyntaxTrace hfuel hinputRows hexpectedRows with
    ⟨states, hstateCount, hstateRows, _hsyntaxLocal⟩
  have hclosed' : CompactParserClosedSuccessTraceBoundedGraph
      tokenTable width tokenCount coordinates.stateBoundary
        coordinates.stateCount (compactSyntaxRunFuelBound input)
        coordinates.inputBoundary input.length
        coordinates.expectedBoundary expected.length
        1 binderArity 0 coordinates.tableWidth coordinates.valueBound := by
    simpa [hinputCount, hexpectedCount, hfuelEq] using hclosed
  have hlocal := hclosed'.sound
    hstateCount hstateRows hinputRows hexpectedRows
  have hvalid : CompactClosedFormulaTokenParserDirectTraceValid
      binderArity input expected states := by
    simpa [CompactClosedFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using hlocal
  exact ⟨input, expected, hinputLayout, hexpectedLayout,
    (compactClosedFormulaTokenParser_eq_some_iff_exists_directTrace
      binderArity input expected).mpr ⟨states, hvalid⟩⟩

/-- Install a successful closed-parser trace already present in an arbitrary
shared token table. -/
theorem exists_compactParserClosedEndpointGraph_of_rows
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
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, binderArity, 0)])
    (hvalid : CompactParserOutputLocalTraceValid compactClosedSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(1, binderArity, 0)], none) (some expected) states) :
    ∃ coordinates : CompactParserSyntaxExactEndpointCoordinates,
      CompactParserClosedEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish binderArity coordinates := by
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputRows, hinputSize⟩
  rcases hexpectedLayout with
    ⟨expectedBoundary, hexpectedStructure, hexpectedRows, hexpectedSize⟩
  rcases closedLocalTrace_exists_compactParserClosedSuccessTraceBoundedFormula
      hstateRows hinputRows hexpectedRows hstartWell hvalid with
    ⟨tableWidth, hformula⟩
  have hclosed : CompactParserClosedSuccessTraceBoundedGraph
      tokenTable width tokenCount stateBoundary states.length
        (compactSyntaxRunFuelBound input)
        inputBoundary input.length expectedBoundary expected.length
        1 binderArity 0 tableWidth (2 ^ tableWidth) :=
    (compactParserClosedSuccessTraceBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length
      (compactSyntaxRunFuelBound input)
      inputBoundary input.length expectedBoundary expected.length
      1 binderArity 0 tableWidth (2 ^ tableWidth)).mp hformula
  have hinputWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart input.length inputFinish
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputRows,
      rfl, hinputSize⟩
  have hexpectedWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount expectedStart expected.length expectedFinish
        expectedBoundary (Nat.size expectedBoundary) :=
    ⟨hexpectedStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hexpectedRows,
      rfl, hexpectedSize⟩
  let coordinates : CompactParserSyntaxExactEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      expectedBoundary := expectedBoundary
      expectedCount := expected.length
      expectedBoundarySize := Nat.size expectedBoundary
      stateBoundary := stateBoundary
      stateCount := states.length
      tableWidth := tableWidth
      valueBound := 2 ^ tableWidth }
  refine ⟨coordinates, ?_⟩
  unfold CompactParserClosedEndpointGraph
  dsimp only [coordinates]
  exact ⟨hinputWitness, hexpectedWitness, by
    simpa [compactSyntaxRunFuelBound] using hclosed⟩

theorem exists_compactParserClosedEndpointGraph_of_success
    {binderArity : Nat} {input expected : List Nat}
    (hparser : compactClosedFormulaTokenParser binderArity input =
      some expected) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ expectedStart expectedFinish,
    ∃ coordinates : CompactParserSyntaxExactEndpointCoordinates,
      CompactParserClosedEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish binderArity coordinates := by
  rcases
      (compactClosedFormulaTokenParser_eq_some_iff_exists_directTrace
        binderArity input expected).mp hparser with
    ⟨states, hvalid⟩
  let inputTokens := compactAdditiveEncode input
  let expectedTokens := compactAdditiveEncode expected
  let stateTokens := compactAdditiveEncode states
  let tokens := inputTokens ++ expectedTokens ++ stateTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input (expectedTokens ++ stateTokens)
  dsimp only at hinputRaw
  have hinputTokens :
      [] ++ compactAdditiveEncode input ++
          (expectedTokens ++ stateTokens) = tokens := by
    simp [inputTokens, tokens]
  rw [hinputTokens] at hinputRaw
  rcases hinputRaw with
    ⟨inputBoundary, hinputStructure, hinputRows, hinputSize⟩
  have hexpectedRaw := compactAdditiveNatListDirectLayout_canonical
    inputTokens expected stateTokens
  dsimp only at hexpectedRaw
  have hexpectedTokens :
      inputTokens ++ compactAdditiveEncode expected ++ stateTokens =
        tokens := by
    simp [expectedTokens, tokens]
  rw [hexpectedTokens] at hexpectedRaw
  rcases hexpectedRaw with
    ⟨expectedBoundary, hexpectedStructure, hexpectedRows, hexpectedSize⟩
  have hstatesRaw := compactUnifiedParserStateListDirectLayout_canonical
    (inputTokens ++ expectedTokens) states []
  dsimp only at hstatesRaw
  have hstateTokens :
      (inputTokens ++ expectedTokens) ++ compactAdditiveEncode states ++ [] =
        tokens := by
    simp [stateTokens, tokens, List.append_assoc]
  rw [hstateTokens] at hstatesRaw
  rcases hstatesRaw with
    ⟨_stateStructure, hstateRows, _hstateSize⟩
  have hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, binderArity, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  have hlocal : CompactParserOutputLocalTraceValid compactClosedSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(1, binderArity, 0)], none) (some expected) states := by
    simpa [CompactClosedFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using hvalid
  rcases closedLocalTrace_exists_compactParserClosedSuccessTraceBoundedFormula
      hstateRows hinputRows hexpectedRows hstartWell hlocal with
    ⟨tableWidth, hformula⟩
  have hclosed : CompactParserClosedSuccessTraceBoundedGraph
      tokenTable width tokens.length
        (compactUnifiedParserStateBoundaryTable
          tokens.length ((inputTokens ++ expectedTokens).length + 1) states)
        states.length (compactSyntaxRunFuelBound input)
        inputBoundary input.length expectedBoundary expected.length
        1 binderArity 0 tableWidth (2 ^ tableWidth) := by
    apply (compactParserClosedSuccessTraceBoundedGraphDef_spec
      tokenTable width tokens.length
      (compactUnifiedParserStateBoundaryTable
        tokens.length ((inputTokens ++ expectedTokens).length + 1) states)
      states.length (compactSyntaxRunFuelBound input)
      inputBoundary input.length expectedBoundary expected.length
      1 binderArity 0 tableWidth (2 ^ tableWidth)).mp
    simpa only [tokenTable, width, List.length_append] using hformula
  have hinputWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length 0 input.length inputTokens.length
        inputBoundary (Nat.size inputBoundary) :=
    ⟨by simpa only [tokenTable, width, List.length_nil, Nat.zero_add,
        inputTokens] using hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        (by simpa only [tokenTable, width] using hinputRows),
      rfl, by simpa only using hinputSize⟩
  have hexpectedWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length inputTokens.length expected.length
        (inputTokens.length + expectedTokens.length)
        expectedBoundary (Nat.size expectedBoundary) :=
    ⟨by simpa only [tokenTable, width, expectedTokens] using
        hexpectedStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        (by simpa only [tokenTable, width] using hexpectedRows),
      rfl, by simpa only using hexpectedSize⟩
  let coordinates : CompactParserSyntaxExactEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      expectedBoundary := expectedBoundary
      expectedCount := expected.length
      expectedBoundarySize := Nat.size expectedBoundary
      stateBoundary := compactUnifiedParserStateBoundaryTable
        tokens.length ((inputTokens ++ expectedTokens).length + 1) states
      stateCount := states.length
      tableWidth := tableWidth
      valueBound := 2 ^ tableWidth }
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    inputTokens.length, inputTokens.length + expectedTokens.length,
    coordinates, ?_⟩
  unfold CompactParserClosedEndpointGraph
  dsimp only [coordinates]
  exact ⟨hinputWitness, hexpectedWitness, by
    simpa [compactSyntaxRunFuelBound] using hclosed⟩

#print axioms CompactParserClosedSuccessAdjacentRowBounded.toSyntax
#print axioms CompactParserClosedSuccessAdjacentRowsBoundedGraph.toSyntax
#print axioms CompactParserClosedEndpointGraph.sound
#print axioms exists_compactParserClosedEndpointGraph_of_rows
#print axioms exists_compactParserClosedEndpointGraph_of_success

end FoundationCompactNumericListedDirectParserClosedEndpointCompleteness
