import integration.FoundationCompactNumericListedDirectParserSyntaxTraceRealization
import integration.FoundationCompactNumericListedDirectNatListWitnessRows
import integration.FoundationCompactNumericListedDirectParserStateListLayout

/-!
# Self-contained exact endpoints for formula and term parsing

The input, expected suffix, and all parser states are encoded in one canonical
token table.  The resulting endpoint graph is sound without typed state-list
parameters and is constructible from every successful public parser call.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
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
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceRealization

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

structure CompactParserSyntaxExactEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  expectedBoundary : Nat
  expectedCount : Nat
  expectedBoundarySize : Nat
  stateBoundary : Nat
  stateCount : Nat
  tableWidth : Nat
  valueBound : Nat

def CompactParserSyntaxExactEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish taskKind taskBinderArity taskRepeatCount :
      Nat)
    (coordinates : CompactParserSyntaxExactEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount
        inputFinish coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount expectedStart coordinates.expectedCount
        expectedFinish coordinates.expectedBoundary
        coordinates.expectedBoundarySize ∧
    CompactParserSyntaxExactBoundedGraph
      tokenTable width tokenCount coordinates.stateBoundary
        coordinates.stateCount coordinates.inputBoundary
        coordinates.inputCount coordinates.expectedBoundary
        coordinates.expectedCount taskKind taskBinderArity taskRepeatCount
        coordinates.tableWidth coordinates.valueBound

/-- The self-contained endpoint graph reconstructs its input, expected suffix,
and complete real local execution. -/
theorem CompactParserSyntaxExactEndpointGraph.sound_local
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish taskKind taskBinderArity taskRepeatCount :
      Nat}
    {coordinates : CompactParserSyntaxExactEndpointCoordinates}
    (hgraph : CompactParserSyntaxExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish taskKind taskBinderArity taskRepeatCount
        coordinates) :
    ∃ input expected : List Nat,
    ∃ states : List CompactUnifiedParserState,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount expectedStart expectedFinish expected ∧
      CompactParserOutputLocalTraceValid compactSyntaxParserStep
        (compactSyntaxRunFuelBound input)
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
        (some expected) states := by
  rcases hgraph with ⟨hinputWitness, hexpectedWitness, hexact⟩
  rcases hinputWitness.realize with
    ⟨input, hinputCount, hinputLayout, hinputRows⟩
  rcases hexpectedWitness.realize with
    ⟨expected, hexpectedCount, hexpectedLayout, hexpectedRows⟩
  have htrace : CompactParserSyntaxTraceBoundedGraph
      tokenTable width tokenCount coordinates.stateBoundary
        coordinates.stateCount (compactSyntaxRunFuelBound input)
        coordinates.inputBoundary input.length
        coordinates.expectedBoundary expected.length
        taskKind taskBinderArity taskRepeatCount
        coordinates.tableWidth coordinates.valueBound := by
    simpa [CompactParserSyntaxExactBoundedGraph,
      compactSyntaxRunFuelBound, hinputCount, hexpectedCount] using hexact
  have hfuel : 0 < compactSyntaxRunFuelBound input := by
    simp [compactSyntaxRunFuelBound]
  rcases CompactParserSyntaxTraceBoundedGraph.realize
      htrace hfuel hinputRows hexpectedRows with
    ⟨states, _hstateCount, _hstateRows, hlocal⟩
  exact ⟨input, expected, states,
    hinputLayout, hexpectedLayout, hlocal⟩

theorem CompactParserSyntaxExactEndpointGraph.sound_formula
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity : Nat}
    {coordinates : CompactParserSyntaxExactEndpointCoordinates}
    (hgraph : CompactParserSyntaxExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish 1 binderArity 0 coordinates) :
    ∃ input expected : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount expectedStart expectedFinish expected ∧
      compactFormulaTokenParser binderArity input = some expected := by
  rcases hgraph.sound_local with
    ⟨input, expected, states, hinputLayout, hexpectedLayout, hlocal⟩
  have hvalid : CompactFormulaTokenParserDirectTraceValid
      binderArity input expected states := by
    simpa [CompactFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using hlocal
  exact ⟨input, expected, hinputLayout, hexpectedLayout,
    (compactFormulaTokenParser_eq_some_iff_exists_directTrace
      binderArity input expected).mpr ⟨states, hvalid⟩⟩

theorem CompactParserSyntaxExactEndpointGraph.sound_term
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish binderArity : Nat}
    {coordinates : CompactParserSyntaxExactEndpointCoordinates}
    (hgraph : CompactParserSyntaxExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        expectedStart expectedFinish 0 binderArity 0 coordinates) :
    ∃ input expected : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount expectedStart expectedFinish expected ∧
      compactTermTokenParser binderArity input = some expected := by
  rcases hgraph.sound_local with
    ⟨input, expected, states, hinputLayout, hexpectedLayout, hlocal⟩
  have hvalid : CompactTermTokenParserDirectTraceValid
      binderArity input expected states := by
    simpa [CompactTermTokenParserDirectTraceValid,
      compactTermParserInitialState, compactTermTask] using hlocal
  exact ⟨input, expected, hinputLayout, hexpectedLayout,
    (compactTermTokenParser_eq_some_iff_exists_directTrace
      binderArity input expected).mpr ⟨states, hvalid⟩⟩

/-- Install a real ordinary parser trace already laid out in an arbitrary
shared token table.  This is the reusable entry point for larger root-parser
and verifier-step graphs. -/
theorem exists_compactParserSyntaxExactEndpointGraph_of_rows
    {tokenTable width tokenCount inputStart inputFinish
      expectedStart expectedFinish stateBoundary : Nat}
    {input expected : List Nat}
    {states : List CompactUnifiedParserState}
    {taskKind taskBinderArity taskRepeatCount : Nat}
    (hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hexpectedLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount expectedStart expectedFinish expected)
    (hstateRows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(taskKind, taskBinderArity, taskRepeatCount)])
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      (some expected) states) :
    ∃ coordinates : CompactParserSyntaxExactEndpointCoordinates,
      CompactParserSyntaxExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish taskKind taskBinderArity
          taskRepeatCount coordinates := by
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputRows, hinputSize⟩
  rcases hexpectedLayout with
    ⟨expectedBoundary, hexpectedStructure, hexpectedRows, hexpectedSize⟩
  rcases localTrace_exists_compactParserSyntaxExactBoundedFormula
      hstateRows hinputRows hexpectedRows hstartWell hvalid with
    ⟨tableWidth, hformula⟩
  have hexact : CompactParserSyntaxExactBoundedGraph
      tokenTable width tokenCount stateBoundary states.length
        inputBoundary input.length expectedBoundary expected.length
        taskKind taskBinderArity taskRepeatCount
        tableWidth (2 ^ tableWidth) :=
    (compactParserSyntaxExactBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length
      inputBoundary input.length expectedBoundary expected.length
      taskKind taskBinderArity taskRepeatCount
      tableWidth (2 ^ tableWidth)).mp hformula
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
  unfold CompactParserSyntaxExactEndpointGraph
  dsimp only [coordinates]
  exact ⟨hinputWitness, hexpectedWitness, hexact⟩

/-- One canonical shared table for an input, expected suffix, and complete
ordinary parser trace. -/
theorem exists_compactParserSyntaxExactEndpointGraph_of_localTrace
    {input expected : List Nat}
    {states : List CompactUnifiedParserState}
    {taskKind taskBinderArity taskRepeatCount : Nat}
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(taskKind, taskBinderArity, taskRepeatCount)])
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      (some expected) states) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ expectedStart expectedFinish,
    ∃ coordinates : CompactParserSyntaxExactEndpointCoordinates,
      CompactParserSyntaxExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish taskKind taskBinderArity
          taskRepeatCount coordinates := by
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
  rcases localTrace_exists_compactParserSyntaxExactBoundedFormula
      hstateRows hinputRows hexpectedRows hstartWell hvalid with
    ⟨tableWidth, hformula⟩
  have hexact : CompactParserSyntaxExactBoundedGraph
      tokenTable width tokens.length
        (compactUnifiedParserStateBoundaryTable
          tokens.length
            ((inputTokens ++ expectedTokens).length + 1) states)
        states.length inputBoundary input.length expectedBoundary
        expected.length taskKind taskBinderArity taskRepeatCount
        tableWidth (2 ^ tableWidth) := by
    apply (compactParserSyntaxExactBoundedGraphDef_spec
      tokenTable width tokens.length
      (compactUnifiedParserStateBoundaryTable
        tokens.length ((inputTokens ++ expectedTokens).length + 1) states)
      states.length inputBoundary input.length expectedBoundary
      expected.length taskKind taskBinderArity taskRepeatCount
      tableWidth (2 ^ tableWidth)).mp
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
  exact ⟨hinputWitness, hexpectedWitness, hexact⟩

theorem exists_compactParserSyntaxExactEndpointGraph_of_formula_success
    {binderArity : Nat} {input expected : List Nat}
    (hparser : compactFormulaTokenParser binderArity input = some expected) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ expectedStart expectedFinish,
    ∃ coordinates : CompactParserSyntaxExactEndpointCoordinates,
      CompactParserSyntaxExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish 1 binderArity 0 coordinates := by
  rcases
      (compactFormulaTokenParser_eq_some_iff_exists_directTrace
        binderArity input expected).mp hparser with
    ⟨states, hvalid⟩
  have hlocal : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(1, binderArity, 0)], none) (some expected) states := by
    simpa [CompactFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using hvalid
  have hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, binderArity, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  exact exists_compactParserSyntaxExactEndpointGraph_of_localTrace
    hstartWell hlocal

theorem exists_compactParserSyntaxExactEndpointGraph_of_term_success
    {binderArity : Nat} {input expected : List Nat}
    (hparser : compactTermTokenParser binderArity input = some expected) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ expectedStart expectedFinish,
    ∃ coordinates : CompactParserSyntaxExactEndpointCoordinates,
      CompactParserSyntaxExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          expectedStart expectedFinish 0 binderArity 0 coordinates := by
  rcases
      (compactTermTokenParser_eq_some_iff_exists_directTrace
        binderArity input expected).mp hparser with
    ⟨states, hvalid⟩
  have hlocal : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(0, binderArity, 0)], none) (some expected) states := by
    simpa [CompactTermTokenParserDirectTraceValid,
      compactTermParserInitialState, compactTermTask] using hvalid
  have hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(0, binderArity, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  exact exists_compactParserSyntaxExactEndpointGraph_of_localTrace
    hstartWell hlocal

#print axioms CompactParserSyntaxExactEndpointGraph.sound_local
#print axioms CompactParserSyntaxExactEndpointGraph.sound_formula
#print axioms CompactParserSyntaxExactEndpointGraph.sound_term
#print axioms exists_compactParserSyntaxExactEndpointGraph_of_rows
#print axioms exists_compactParserSyntaxExactEndpointGraph_of_localTrace
#print axioms exists_compactParserSyntaxExactEndpointGraph_of_formula_success
#print axioms exists_compactParserSyntaxExactEndpointGraph_of_term_success

end FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
