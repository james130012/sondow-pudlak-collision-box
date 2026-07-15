import integration.FoundationCompactNumericListedDirectParserClosedNoOutputTraceRealization
import integration.FoundationCompactNumericListedDirectNatListWitnessRows
import integration.FoundationCompactNumericListedDirectParserStateListLayout

/-!
# Self-contained exact endpoints for closed-parser no-output results

The input and every parser state are encoded in one canonical token table.
The graph is sound without typed state-list parameters and is constructible
from every public formula- or term-parser call returning `none`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointCompleteness

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
open FoundationCompactNumericListedDirectParserClosedNoOutputExactFormula
open FoundationCompactNumericListedDirectParserClosedNoOutputTraceRealization

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

structure CompactParserClosedNoOutputExactEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  stateBoundary : Nat
  stateCount : Nat
  tableWidth : Nat
  valueBound : Nat

def CompactParserClosedNoOutputExactEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount : Nat)
    (coordinates : CompactParserClosedNoOutputExactEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactParserClosedNoOutputExactBoundedGraph
      tokenTable width tokenCount coordinates.stateBoundary
        coordinates.stateCount coordinates.inputBoundary
        coordinates.inputCount taskKind taskBinderArity taskRepeatCount
        coordinates.tableWidth coordinates.valueBound

theorem CompactParserClosedNoOutputExactEndpointGraph.sound_local
    {tokenTable width tokenCount inputStart inputFinish
      taskKind taskBinderArity taskRepeatCount : Nat}
    {coordinates : CompactParserClosedNoOutputExactEndpointCoordinates}
    (hgraph : CompactParserClosedNoOutputExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        taskKind taskBinderArity taskRepeatCount coordinates) :
    ∃ input : List Nat,
    ∃ states : List CompactUnifiedParserState,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactParserOutputLocalTraceValid FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep
        (compactSyntaxRunFuelBound input)
        (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
        none states := by
  rcases hgraph with ⟨hinputWitness, hexact⟩
  rcases hinputWitness.realize with
    ⟨input, hinputCount, hinputLayout, hinputRows⟩
  have hexact' : CompactParserClosedNoOutputExactBoundedGraph
      tokenTable width tokenCount coordinates.stateBoundary
        coordinates.stateCount coordinates.inputBoundary input.length
        taskKind taskBinderArity taskRepeatCount
        coordinates.tableWidth coordinates.valueBound := by
    simpa only [hinputCount] using hexact
  rcases
      FoundationCompactNumericListedDirectParserClosedNoOutputTraceRealization.CompactParserClosedNoOutputExactBoundedGraph.realize
        hexact' hinputRows with
    ⟨states, _hstateCount, _hstateRows, hlocal⟩
  exact ⟨input, states, hinputLayout, hlocal⟩

theorem CompactParserClosedNoOutputExactEndpointGraph.sound_formula
    {tokenTable width tokenCount inputStart inputFinish binderArity : Nat}
    {coordinates : CompactParserClosedNoOutputExactEndpointCoordinates}
    (hgraph : CompactParserClosedNoOutputExactEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        1 binderArity 0 coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactClosedFormulaTokenMachine.compactClosedFormulaTokenParser binderArity input = none := by
  rcases hgraph.sound_local with ⟨input, states, hinputLayout, hlocal⟩
  have houtput :=
    (compactParserOutput_eq_iff_exists_localTrace
      FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep (compactSyntaxRunFuelBound input)
      (compactFormulaParserInitialState binderArity input) none).mpr
      ⟨states, by
        simpa [compactFormulaParserInitialState, compactFormulaTask] using
          hlocal⟩
  refine ⟨input, hinputLayout, ?_⟩
  simpa [FoundationCompactClosedFormulaTokenMachine.compactClosedFormulaTokenParser, FoundationCompactClosedFormulaTokenMachine.compactClosedFormulaTokenParserRun] using
    houtput

theorem exists_compactParserClosedNoOutputExactEndpointGraph_of_rows
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
    (hvalid : CompactParserOutputLocalTraceValid FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states) :
    ∃ coordinates : CompactParserClosedNoOutputExactEndpointCoordinates,
      CompactParserClosedNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          taskKind taskBinderArity taskRepeatCount coordinates := by
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputRows, hinputSize⟩
  rcases localTrace_exists_compactParserClosedNoOutputExactBoundedFormula
      hstateRows hinputRows hstartWell hvalid with
    ⟨tableWidth, hformula⟩
  have hexact : CompactParserClosedNoOutputExactBoundedGraph
      tokenTable width tokenCount stateBoundary states.length
        inputBoundary input.length taskKind taskBinderArity taskRepeatCount
        tableWidth (2 ^ tableWidth) :=
    (compactParserClosedNoOutputExactBoundedGraphDef_spec
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
  let coordinates : CompactParserClosedNoOutputExactEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      stateBoundary := stateBoundary
      stateCount := states.length
      tableWidth := tableWidth
      valueBound := 2 ^ tableWidth }
  refine ⟨coordinates, ?_⟩
  exact ⟨hinputWitness, hexact⟩

theorem exists_compactParserClosedNoOutputExactEndpointGraph_of_localTrace
    {input : List Nat}
    {states : List CompactUnifiedParserState}
    {taskKind taskBinderArity taskRepeatCount : Nat}
    (hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(taskKind, taskBinderArity, taskRepeatCount)])
    (hvalid : CompactParserOutputLocalTraceValid FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(taskKind, taskBinderArity, taskRepeatCount)], none)
      none states) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactParserClosedNoOutputExactEndpointCoordinates,
      CompactParserClosedNoOutputExactEndpointGraph
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
  rcases localTrace_exists_compactParserClosedNoOutputExactBoundedFormula
      hstateRows hinputRows hstartWell hvalid with
    ⟨tableWidth, hformula⟩
  have hexact : CompactParserClosedNoOutputExactBoundedGraph
      tokenTable width tokens.length
        (compactUnifiedParserStateBoundaryTable
          tokens.length (inputTokens.length + 1) states)
        states.length inputBoundary input.length
        taskKind taskBinderArity taskRepeatCount
        tableWidth (2 ^ tableWidth) := by
    apply (compactParserClosedNoOutputExactBoundedGraphDef_spec
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
  let coordinates : CompactParserClosedNoOutputExactEndpointCoordinates :=
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

theorem exists_compactParserClosedNoOutputExactEndpointGraph_of_formula_none
    {binderArity : Nat} {input : List Nat}
    (hparser : FoundationCompactClosedFormulaTokenMachine.compactClosedFormulaTokenParser binderArity input = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactParserClosedNoOutputExactEndpointCoordinates,
      CompactParserClosedNoOutputExactEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          1 binderArity 0 coordinates := by
  have houtput : compactSyntaxParserStateOutput
      ((FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep^[compactSyntaxRunFuelBound input])
        (compactFormulaParserInitialState binderArity input)) = none := by
    simpa [FoundationCompactClosedFormulaTokenMachine.compactClosedFormulaTokenParser, FoundationCompactClosedFormulaTokenMachine.compactClosedFormulaTokenParserRun] using
      hparser
  rcases (compactParserOutput_eq_iff_exists_localTrace
      FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep (compactSyntaxRunFuelBound input)
      (compactFormulaParserInitialState binderArity input) none).mp houtput with
    ⟨states, hvalid⟩
  have hlocal : CompactParserOutputLocalTraceValid FoundationCompactClosedFormulaTokenMachine.compactClosedSyntaxParserStep
      (compactSyntaxRunFuelBound input)
      (input, [(1, binderArity, 0)], none) none states := by
    simpa [compactFormulaParserInitialState, compactFormulaTask] using hvalid
  have hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, binderArity, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  exact exists_compactParserClosedNoOutputExactEndpointGraph_of_localTrace
    hstartWell hlocal

#print axioms CompactParserClosedNoOutputExactEndpointGraph.sound_local
#print axioms CompactParserClosedNoOutputExactEndpointGraph.sound_formula
#print axioms exists_compactParserClosedNoOutputExactEndpointGraph_of_rows
#print axioms exists_compactParserClosedNoOutputExactEndpointGraph_of_localTrace
#print axioms exists_compactParserClosedNoOutputExactEndpointGraph_of_formula_none

end FoundationCompactNumericListedDirectParserClosedNoOutputExactEndpointCompleteness
