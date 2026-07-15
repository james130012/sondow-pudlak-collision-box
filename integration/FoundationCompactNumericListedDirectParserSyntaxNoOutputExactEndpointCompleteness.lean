import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputTraceRealization
import integration.FoundationCompactNumericListedDirectNatListWitnessRows
import integration.FoundationCompactNumericListedDirectParserStateListLayout

/-!
# Self-contained exact endpoints for syntax-parser no-output results

The input and every parser state are encoded in one canonical token table.
The graph is sound without typed state-list parameters and is constructible
from every public formula- or term-parser call returning `none`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness

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
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactFormula
open FoundationCompactNumericListedDirectParserSyntaxNoOutputTraceRealization

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

structure CompactParserSyntaxNoOutputExactEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  stateBoundary : Nat
  stateCount : Nat
  tableWidth : Nat
  valueBound : Nat

def CompactParserSyntaxNoOutputExactEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount : Nat)
    (coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactParserSyntaxNoOutputExactBoundedGraph
      tokenTable width tokenCount coordinates.stateBoundary
        coordinates.stateCount coordinates.inputBoundary
        coordinates.inputCount taskKind taskBinderArity taskRepeatCount
        coordinates.tableWidth coordinates.valueBound

theorem CompactParserSyntaxNoOutputExactEndpointGraph.sound_local
    {tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount : Nat}
    {coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates}
    (hgraph : CompactParserSyntaxNoOutputExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount coordinates) :
    ∃ input : List Nat,
    ∃ states : List CompactUnifiedParserState,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactParserOutputLocalTraceValid compactSyntaxParserStep
        (compactSyntaxRunFuelBound input)
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
        none states := by
  rcases hgraph with ⟨hinputWitness, hexact⟩
  rcases hinputWitness.realize with
    ⟨input, hinputCount, hinputLayout, hinputRows⟩
  have hexact' : CompactParserSyntaxNoOutputExactBoundedGraph
      tokenTable width tokenCount coordinates.stateBoundary
        coordinates.stateCount coordinates.inputBoundary input.length
        taskKind taskBinderArity taskRepeatCount
        coordinates.tableWidth coordinates.valueBound := by
    simpa only [hinputCount] using hexact
  rcases
      FoundationCompactNumericListedDirectParserSyntaxNoOutputTraceRealization.CompactParserSyntaxNoOutputExactBoundedGraph.realize
        hexact' hinputRows with
    ⟨states, _hstateCount, _hstateRows, hlocal⟩
  exact ⟨input, states, hinputLayout, hlocal⟩

theorem CompactParserSyntaxNoOutputExactEndpointGraph.sound_formula
    {tokenTable width tokenCount inputStart inputFinish binderArity : Nat}
    {coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates}
    (hgraph : CompactParserSyntaxNoOutputExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        1 binderArity 0 coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactFormulaTokenParser binderArity input = none := by
  rcases hgraph.sound_local with ⟨input, states, hinputLayout, hlocal⟩
  have houtput :=
    (compactParserOutput_eq_iff_exists_localTrace
      compactSyntaxParserStep (compactSyntaxRunFuelBound input)
      (compactFormulaParserInitialState binderArity input) none).mpr
      ⟨states, by
        simpa [compactFormulaParserInitialState, compactFormulaTask] using
          hlocal⟩
  refine ⟨input, hinputLayout, ?_⟩
  simpa [compactFormulaTokenParser, compactFormulaTokenParserRun] using
    houtput

theorem CompactParserSyntaxNoOutputExactEndpointGraph.sound_term
    {tokenTable width tokenCount inputStart inputFinish binderArity : Nat}
    {coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates}
    (hgraph : CompactParserSyntaxNoOutputExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        0 binderArity 0 coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactTermTokenParser binderArity input = none := by
  rcases hgraph.sound_local with ⟨input, states, hinputLayout, hlocal⟩
  have houtput :=
    (compactParserOutput_eq_iff_exists_localTrace
      compactSyntaxParserStep (compactSyntaxRunFuelBound input)
      (compactTermParserInitialState binderArity input) none).mpr
      ⟨states, by
        simpa [compactTermParserInitialState, compactTermTask] using hlocal⟩
  refine ⟨input, hinputLayout, ?_⟩
  simpa [compactTermTokenParser, compactTermTokenParserRun] using houtput

theorem exists_compactParserSyntaxNoOutputExactEndpointGraph_of_rows
    {tokenTable width tokenCount inputStart inputFinish stateBoundary : Nat}
    {input : List Nat}
    {states : List CompactUnifiedParserState}
    {taskKind taskBinderArity taskRepeatCount : Nat}
    (hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hstateRows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(taskKind, taskBinderArity, taskRepeatCount)])
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states) :
    ∃ coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates,
      CompactParserSyntaxNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          taskKind taskBinderArity taskRepeatCount coordinates := by
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputRows, hinputSize⟩
  rcases localTrace_exists_compactParserSyntaxNoOutputExactBoundedFormula
      hstateRows hinputRows hstartWell hvalid with
    ⟨tableWidth, hformula⟩
  have hexact : CompactParserSyntaxNoOutputExactBoundedGraph
      tokenTable width tokenCount stateBoundary states.length
        inputBoundary input.length taskKind taskBinderArity taskRepeatCount
        tableWidth (2 ^ tableWidth) :=
    (compactParserSyntaxNoOutputExactBoundedGraphDef_spec
      tokenTable width tokenCount stateBoundary states.length
      inputBoundary input.length taskKind taskBinderArity taskRepeatCount
      tableWidth (2 ^ tableWidth)).mp hformula
  have hinputWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart input.length inputFinish
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputRows,
      rfl, hinputSize⟩
  let coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      stateBoundary := stateBoundary
      stateCount := states.length
      tableWidth := tableWidth
      valueBound := 2 ^ tableWidth }
  refine ⟨coordinates, ?_⟩
  exact ⟨hinputWitness, hexact⟩

theorem exists_compactParserSyntaxNoOutputExactEndpointGraph_of_localTrace
    {input : List Nat}
    {states : List CompactUnifiedParserState}
    {taskKind taskBinderArity taskRepeatCount : Nat}
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(taskKind, taskBinderArity, taskRepeatCount)])
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates,
      CompactParserSyntaxNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          taskKind taskBinderArity taskRepeatCount coordinates := by
  let inputTokens := compactAdditiveEncode input
  let stateTokens := compactAdditiveEncode states
  let tokens := inputTokens ++ stateTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input stateTokens
  dsimp only at hinputRaw
  have hinputTokens :
      [] ++ compactAdditiveEncode input ++ stateTokens = tokens := by
    simp [inputTokens, tokens]
  rw [hinputTokens] at hinputRaw
  rcases hinputRaw with
    ⟨inputBoundary, hinputStructure, hinputRows, hinputSize⟩
  have hstatesRaw := compactUnifiedParserStateListDirectLayout_canonical
    inputTokens states []
  dsimp only at hstatesRaw
  have hstateTokens :
      inputTokens ++ compactAdditiveEncode states ++ [] = tokens := by
    simp [stateTokens, tokens, List.append_assoc]
  rw [hstateTokens] at hstatesRaw
  rcases hstatesRaw with
    ⟨_stateStructure, hstateRows, _hstateSize⟩
  rcases localTrace_exists_compactParserSyntaxNoOutputExactBoundedFormula
      hstateRows hinputRows hstartWell hvalid with
    ⟨tableWidth, hformula⟩
  have hexact : CompactParserSyntaxNoOutputExactBoundedGraph
      tokenTable width tokens.length
        (compactUnifiedParserStateBoundaryTable
          tokens.length (inputTokens.length + 1) states)
        states.length inputBoundary input.length
        taskKind taskBinderArity taskRepeatCount
        tableWidth (2 ^ tableWidth) := by
    apply (compactParserSyntaxNoOutputExactBoundedGraphDef_spec
      tokenTable width tokens.length
      (compactUnifiedParserStateBoundaryTable
        tokens.length (inputTokens.length + 1) states)
      states.length inputBoundary input.length
      taskKind taskBinderArity taskRepeatCount
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
  let coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      stateBoundary := compactUnifiedParserStateBoundaryTable
        tokens.length (inputTokens.length + 1) states
      stateCount := states.length
      tableWidth := tableWidth
      valueBound := 2 ^ tableWidth }
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    coordinates, ?_⟩
  exact ⟨hinputWitness, hexact⟩

theorem exists_compactParserSyntaxNoOutputExactEndpointGraph_of_formula_none
    {binderArity : Nat} {input : List Nat}
    (hparser : compactFormulaTokenParser binderArity input = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates,
      CompactParserSyntaxNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          1 binderArity 0 coordinates := by
  have houtput : compactSyntaxParserStateOutput
      ((compactSyntaxParserStep^[compactSyntaxRunFuelBound input])
        (compactFormulaParserInitialState binderArity input)) = none := by
    simpa [compactFormulaTokenParser, compactFormulaTokenParserRun] using
      hparser
  rcases (compactParserOutput_eq_iff_exists_localTrace
      compactSyntaxParserStep (compactSyntaxRunFuelBound input)
      (compactFormulaParserInitialState binderArity input) none).mp houtput with
    ⟨states, hvalid⟩
  have hlocal : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(1, binderArity, 0)], none) none states := by
    simpa [compactFormulaParserInitialState, compactFormulaTask] using hvalid
  have hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, binderArity, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  exact exists_compactParserSyntaxNoOutputExactEndpointGraph_of_localTrace
    hstartWell hlocal

theorem exists_compactParserSyntaxNoOutputExactEndpointGraph_of_term_none
    {binderArity : Nat} {input : List Nat}
    (hparser : compactTermTokenParser binderArity input = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactParserSyntaxNoOutputExactEndpointCoordinates,
      CompactParserSyntaxNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          0 binderArity 0 coordinates := by
  have houtput : compactSyntaxParserStateOutput
      ((compactSyntaxParserStep^[compactSyntaxRunFuelBound input])
        (compactTermParserInitialState binderArity input)) = none := by
    simpa [compactTermTokenParser, compactTermTokenParserRun] using hparser
  rcases (compactParserOutput_eq_iff_exists_localTrace
      compactSyntaxParserStep (compactSyntaxRunFuelBound input)
      (compactTermParserInitialState binderArity input) none).mp houtput with
    ⟨states, hvalid⟩
  have hlocal : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(0, binderArity, 0)], none) none states := by
    simpa [compactTermParserInitialState, compactTermTask] using hvalid
  have hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(0, binderArity, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  exact exists_compactParserSyntaxNoOutputExactEndpointGraph_of_localTrace
    hstartWell hlocal

#print axioms CompactParserSyntaxNoOutputExactEndpointGraph.sound_local
#print axioms CompactParserSyntaxNoOutputExactEndpointGraph.sound_formula
#print axioms CompactParserSyntaxNoOutputExactEndpointGraph.sound_term
#print axioms exists_compactParserSyntaxNoOutputExactEndpointGraph_of_rows
#print axioms exists_compactParserSyntaxNoOutputExactEndpointGraph_of_localTrace
#print axioms exists_compactParserSyntaxNoOutputExactEndpointGraph_of_formula_none
#print axioms exists_compactParserSyntaxNoOutputExactEndpointGraph_of_term_none

end FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness
