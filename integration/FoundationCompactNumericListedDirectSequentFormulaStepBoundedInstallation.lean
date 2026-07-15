import integration.FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxTraceRealization
import integration.FoundationCompactSequentValueDirectTrace

/-!
# Installation of the bounded nested sequent formula-parser step

The bounded row formula is unpacked into three real natural-number lists and
one real public formula-parser trace.  Exact append slices identify the parsed
formula prefix without receiving any semantic list as a formula parameter.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaStepBoundedInstallation

open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactSequentValueDirectTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceRealization
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula

def compactSequentFormulaStepRowValues
    (row : CompactSequentFormulaStepCoordinates) : List Nat :=
  [row.current.start, row.current.finish, row.current.boundary,
    row.current.count, row.current.boundarySize,
    row.next.start, row.next.finish, row.next.boundary,
    row.next.count, row.next.boundarySize,
    row.value.start, row.value.finish, row.value.boundary,
    row.value.count, row.value.boundarySize,
    row.parserStateBoundary, row.parserTableWidth, row.parserValueBound]

theorem CompactSequentFormulaStepGraph.toBounded
    {tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount rowIndex valueBound : Nat}
    {row : CompactSequentFormulaStepCoordinates}
    (hgraph : CompactSequentFormulaStepGraph
      tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount rowIndex row)
    (hbound : ∀ value ∈ compactSequentFormulaStepRowValues row,
      value ≤ valueBound) :
    CompactSequentFormulaStepRowBounded
      tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount rowIndex valueBound := by
  unfold CompactSequentFormulaStepRowBounded
  refine ⟨row.current.start, ?_, row.current.finish, ?_,
    row.current.boundary, ?_, row.current.count, ?_,
    row.current.boundarySize, ?_, row.next.start, ?_, row.next.finish, ?_,
    row.next.boundary, ?_, row.next.count, ?_, row.next.boundarySize, ?_,
    row.value.start, ?_, row.value.finish, ?_, row.value.boundary, ?_,
    row.value.count, ?_, row.value.boundarySize, ?_,
    row.parserStateBoundary, ?_, row.parserTableWidth, ?_,
    row.parserValueBound, ?_, ?_⟩
  all_goals
    first
    | apply hbound
      simp [compactSequentFormulaStepRowValues]
    | simpa [compactSequentFormulaStepRowOfValues] using hgraph

theorem CompactSequentFormulaStepRowBounded.exists_row
    {tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount rowIndex valueBound : Nat}
    (hbounded : CompactSequentFormulaStepRowBounded
      tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount rowIndex valueBound) :
    ∃ row : CompactSequentFormulaStepCoordinates,
      CompactSequentFormulaStepGraph
        tokenTable width tokenCount suffixBoundary suffixCount
          valueBoundary valueCount rowIndex row := by
  unfold CompactSequentFormulaStepRowBounded at hbounded
  rcases hbounded with
    ⟨currentStart, _, currentFinish, _, currentBoundary, _, currentCount, _,
      currentBoundarySize, _, nextStart, _, nextFinish, _, nextBoundary, _,
      nextCount, _, nextBoundarySize, _, valueStart, _, valueFinish, _,
      valueInnerBoundary, _, valueInnerCount, _, valueBoundarySize, _,
      parserStateBoundary, _, parserTableWidth, _, parserValueBound, _,
      hgraph⟩
  let row := compactSequentFormulaStepRowOfValues
    currentStart currentFinish currentBoundary currentCount
    currentBoundarySize nextStart nextFinish nextBoundary nextCount
    nextBoundarySize valueStart valueFinish valueInnerBoundary
    valueInnerCount valueBoundarySize parserStateBoundary parserTableWidth
    parserValueBound
  refine ⟨row, ?_⟩
  simpa [row, compactSequentFormulaStepRowOfValues] using hgraph

theorem CompactSequentFormulaStepGraph.sound
    {tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount rowIndex : Nat}
    {row : CompactSequentFormulaStepCoordinates}
    (hgraph : CompactSequentFormulaStepGraph
      tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount rowIndex row) :
    ∃ current next value : List Nat,
    ∃ parserStates : List CompactUnifiedParserState,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount row.current.start row.current.finish
          current ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount row.next.start row.next.finish next ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount row.value.start row.value.finish value ∧
      CompactFormulaTokenParserDirectTraceValid
        0 current next parserStates ∧
      current = value ++ next ∧
      compactFormulaTokenValueParser 0 current = some (value, next) := by
  rcases hgraph with
    ⟨_hcurrentStart, _hcurrentFinish, _hcurrentCount,
      _hnextStart, _hnextFinish, _hnextCount,
      _hvalueStart, _hvalueFinish, _hvalueCount,
      _hcurrentStartEntry, _hcurrentFinishEntry,
      _hnextStartEntry, _hnextFinishEntry,
      _hvalueStartEntry, _hvalueFinishEntry,
      hcurrentRows, hnextRows, hvalueRows, hparser, happend,
      _hsuffixCount⟩
  rcases hcurrentRows.realize with
    ⟨current, hcurrentLength, hcurrentLayout, hcurrentElementRows⟩
  rcases hnextRows.realize with
    ⟨next, hnextLength, hnextLayout, hnextElementRows⟩
  rcases hvalueRows.realize with
    ⟨value, hvalueLength, hvalueLayout, _hvalueElementRows⟩
  have hparser' : CompactParserSyntaxExactBoundedGraph
      tokenTable width tokenCount row.parserStateBoundary
      (16 * (current.length + 1) * (current.length + 1) + 8 + 1)
      row.current.boundary current.length row.next.boundary next.length
      1 0 0 row.parserTableWidth row.parserValueBound := by
    simpa only [hcurrentLength, hnextLength] using hparser
  rcases CompactParserSyntaxExactBoundedGraph.realize_formula
      hparser' hcurrentElementRows hnextElementRows with
    ⟨parserStates, _hparserCount, _hparserRows, htrace⟩
  have happend' : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
      row.value.start row.value.finish value.length
      row.next.start row.next.finish next.length
      row.current.start row.current.finish current.length := by
    simpa only [hvalueLength, hnextLength, hcurrentLength] using happend
  have hcurrentEq : current = value ++ next :=
    (compactAdditiveNatListAppendSlices_iff_append
      hvalueLayout hnextLayout hcurrentLayout).mp happend'
  have hparserResult : compactFormulaTokenParser 0 current = some next :=
    (compactFormulaTokenParser_eq_some_iff_exists_directTrace
      0 current next).mpr ⟨parserStates, htrace⟩
  have hvalueResult : compactFormulaTokenValueParser 0 current =
      some (value, next) := by
    apply (compactFormulaTokenValueParser_eq_some_iff
      0 current value next).mpr
    refine ⟨hparserResult, ?_⟩
    rw [hcurrentEq, consumedTokenPrefix_append]
  exact ⟨current, next, value, parserStates,
    hcurrentLayout, hnextLayout, hvalueLayout,
    htrace, hcurrentEq, hvalueResult⟩

theorem exists_compactSequentFormulaStepGraph_of_directTrace
    {tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount rowIndex
      currentStart currentFinish nextStart nextFinish
      valueStart valueFinish : Nat}
    {current next value : List Nat}
    {parserStates : List CompactUnifiedParserState}
    (hcurrent : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount currentStart currentFinish current)
    (hnext : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount nextStart nextFinish next)
    (hvalue : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount valueStart valueFinish value)
    (parserStateBoundary : Nat)
    (hparserStateRows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount parserStateBoundary parserStates)
    (htrace : CompactFormulaTokenParserDirectTraceValid
      0 current next parserStates)
    (hcurrentEq : current = value ++ next)
    (hcurrentStartEntry : CompactFixedWidthEntry
      suffixBoundary tokenCount rowIndex currentStart)
    (hcurrentFinishEntry : CompactFixedWidthEntry
      suffixBoundary tokenCount (rowIndex + 1) currentFinish)
    (hnextStartEntry : CompactFixedWidthEntry
      suffixBoundary tokenCount (rowIndex + 1) nextStart)
    (hnextFinishEntry : CompactFixedWidthEntry
      suffixBoundary tokenCount (rowIndex + 2) nextFinish)
    (hvalueStartEntry : CompactFixedWidthEntry
      valueBoundary tokenCount rowIndex valueStart)
    (hvalueFinishEntry : CompactFixedWidthEntry
      valueBoundary tokenCount (rowIndex + 1) valueFinish)
    (hsuffixCount : suffixCount = valueCount + 1) :
    ∃ row : CompactSequentFormulaStepCoordinates,
      CompactSequentFormulaStepGraph
        tokenTable width tokenCount suffixBoundary suffixCount
          valueBoundary valueCount rowIndex row := by
  rcases hcurrent with
    ⟨currentBoundary, hcurrentStructure, hcurrentElementRows, hcurrentSize⟩
  rcases hnext with
    ⟨nextBoundary, hnextStructure, hnextElementRows, hnextSize⟩
  rcases hvalue with
    ⟨valueInnerBoundary, hvalueStructure, hvalueElementRows, hvalueSize⟩
  let currentBoundarySize := Nat.size currentBoundary
  let nextBoundarySize := Nat.size nextBoundary
  let valueBoundarySize := Nat.size valueInnerBoundary
  have hcurrentWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount currentStart current.length currentFinish
        currentBoundary currentBoundarySize := by
    exact ⟨hcurrentStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hcurrentElementRows,
      rfl, hcurrentSize⟩
  have hnextWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount nextStart next.length nextFinish
        nextBoundary nextBoundarySize := by
    exact ⟨hnextStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hnextElementRows,
      rfl, hnextSize⟩
  have hvalueWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount valueStart value.length valueFinish
        valueInnerBoundary valueBoundarySize := by
    exact ⟨hvalueStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hvalueElementRows,
      rfl, hvalueSize⟩
  have hcurrentLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount currentStart currentFinish current :=
    ⟨currentBoundary, hcurrentStructure, hcurrentElementRows, hcurrentSize⟩
  have hnextLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount nextStart nextFinish next :=
    ⟨nextBoundary, hnextStructure, hnextElementRows, hnextSize⟩
  have hvalueLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount valueStart valueFinish value :=
    ⟨valueInnerBoundary, hvalueStructure, hvalueElementRows, hvalueSize⟩
  have hlocal : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound current)
      (current, [(1, 0, 0)], none) (some next) parserStates := by
    simpa [CompactFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using htrace
  have hstartWell : CompactSyntaxTaskStackFieldsWellFormed [(1, 0, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  rcases localTrace_exists_compactParserSyntaxExactBoundedFormula
      hparserStateRows hcurrentElementRows hnextElementRows hstartWell hlocal with
    ⟨parserTableWidth, hparserFormula⟩
  have hparserGraph : CompactParserSyntaxExactBoundedGraph
      tokenTable width tokenCount parserStateBoundary parserStates.length
      currentBoundary current.length nextBoundary next.length
      1 0 0 parserTableWidth (2 ^ parserTableWidth) :=
    (compactParserSyntaxExactBoundedGraphDef_spec
      tokenTable width tokenCount parserStateBoundary parserStates.length
      currentBoundary current.length nextBoundary next.length
      1 0 0 parserTableWidth (2 ^ parserTableWidth)).mp hparserFormula
  have hstateCount : parserStates.length =
      16 * (current.length + 1) * (current.length + 1) + 8 + 1 := by
    simpa [compactSyntaxRunFuelBound] using hlocal.1.1
  have hparserGraph' : CompactParserSyntaxExactBoundedGraph
      tokenTable width tokenCount parserStateBoundary
      (16 * (current.length + 1) * (current.length + 1) + 8 + 1)
      currentBoundary current.length nextBoundary next.length
      1 0 0 parserTableWidth (2 ^ parserTableWidth) := by
    rw [← hstateCount]
    exact hparserGraph
  have happend : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
      valueStart valueFinish value.length
      nextStart nextFinish next.length
      currentStart currentFinish current.length :=
    (compactAdditiveNatListAppendSlices_iff_append
      hvalueLayout hnextLayout hcurrentLayout).mpr hcurrentEq
  rcases hcurrentLayout.toSlice with
    ⟨currentBody, _hcurrentBodyBound, hcurrentHeader, hcurrentFinishEq⟩
  rcases hnextLayout.toSlice with
    ⟨nextBody, _hnextBodyBound, hnextHeader, hnextFinishEq⟩
  rcases hvalueLayout.toSlice with
    ⟨valueBody, _hvalueBodyBound, hvalueHeader, hvalueFinishEq⟩
  have hcurrentStartBound : currentStart ≤ tokenCount :=
    Nat.le_of_lt hcurrentHeader.1.1
  have hcurrentBodyCountBound :
      currentBody + current.length ≤ tokenCount := hcurrentHeader.2
  have hcurrentFinishBound : currentFinish ≤ tokenCount := by omega
  have hcurrentCountBound : current.length ≤ tokenCount := by omega
  have hnextStartBound : nextStart ≤ tokenCount :=
    Nat.le_of_lt hnextHeader.1.1
  have hnextBodyCountBound :
      nextBody + next.length ≤ tokenCount := hnextHeader.2
  have hnextFinishBound : nextFinish ≤ tokenCount := by omega
  have hnextCountBound : next.length ≤ tokenCount := by omega
  have hvalueStartBound : valueStart ≤ tokenCount :=
    Nat.le_of_lt hvalueHeader.1.1
  have hvalueBodyCountBound :
      valueBody + value.length ≤ tokenCount := hvalueHeader.2
  have hvalueFinishBound : valueFinish ≤ tokenCount := by omega
  have hvalueCountBound : value.length ≤ tokenCount := by omega
  let row : CompactSequentFormulaStepCoordinates :=
    { current :=
        { start := currentStart
          finish := currentFinish
          boundary := currentBoundary
          count := current.length
          boundarySize := currentBoundarySize }
      next :=
        { start := nextStart
          finish := nextFinish
          boundary := nextBoundary
          count := next.length
          boundarySize := nextBoundarySize }
      value :=
        { start := valueStart
          finish := valueFinish
          boundary := valueInnerBoundary
          count := value.length
          boundarySize := valueBoundarySize }
      parserStateBoundary := parserStateBoundary
      parserTableWidth := parserTableWidth
      parserValueBound := 2 ^ parserTableWidth }
  refine ⟨row, ?_⟩
  exact ⟨hcurrentStartBound, hcurrentFinishBound, hcurrentCountBound,
    hnextStartBound, hnextFinishBound, hnextCountBound,
    hvalueStartBound, hvalueFinishBound, hvalueCountBound,
    hcurrentStartEntry, hcurrentFinishEntry, hnextStartEntry,
    hnextFinishEntry, hvalueStartEntry, hvalueFinishEntry,
    hcurrentWitness, hnextWitness, hvalueWitness, hparserGraph',
    happend, hsuffixCount⟩

def compactSequentFormulaStepDynamicWidth
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  ((compactSequentFormulaStepRowValues row).map Nat.size).sum

theorem compactSequentFormulaStep_value_size_le_dynamic
    (row : CompactSequentFormulaStepCoordinates) {value : Nat}
    (hvalue : value ∈ compactSequentFormulaStepRowValues row) :
    Nat.size value ≤ compactSequentFormulaStepDynamicWidth row := by
  have hsize : Nat.size value ∈
      (compactSequentFormulaStepRowValues row).map Nat.size :=
    List.mem_map.mpr ⟨value, hvalue, rfl⟩
  simpa [compactSequentFormulaStepDynamicWidth] using
    List.single_le_sum (by simp) _ hsize

theorem CompactSequentFormulaStepGraph.exists_bounded
    {tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount rowIndex : Nat}
    {row : CompactSequentFormulaStepCoordinates}
    (hgraph : CompactSequentFormulaStepGraph
      tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount rowIndex row) :
    ∃ tableWidth,
      CompactSequentFormulaStepRowBounded
        tokenTable width tokenCount suffixBoundary suffixCount
          valueBoundary valueCount rowIndex (2 ^ tableWidth) := by
  let tableWidth := compactSequentFormulaStepDynamicWidth row
  refine ⟨tableWidth, CompactSequentFormulaStepGraph.toBounded hgraph ?_⟩
  intro value hvalue
  exact (Nat.size_le.mp
    (compactSequentFormulaStep_value_size_le_dynamic row hvalue)).le

#print axioms CompactSequentFormulaStepGraph.toBounded
#print axioms CompactSequentFormulaStepRowBounded.exists_row
#print axioms CompactSequentFormulaStepGraph.sound
#print axioms exists_compactSequentFormulaStepGraph_of_directTrace
#print axioms compactSequentFormulaStep_value_size_le_dynamic
#print axioms CompactSequentFormulaStepGraph.exists_bounded

end FoundationCompactNumericListedDirectSequentFormulaStepBoundedInstallation
