import integration.FoundationCompactNumericListedDirectParserSyntaxTraceBounds
import integration.FoundationCompactNumericListedDirectSequentFormulaTraceCompleteness

/-!
# Public quantitative bounds for sequent formula-parser traces

Each row of a successful sequent parser contains three token-list slices and
one complete formula-parser trace.  The existing completeness theorem builds
these rows exactly, but its aggregate witness width is the sum of coordinates
chosen after the fact.  This file rebuilds the same rows with the public
formula-parser width theorem and retains one explicit bound depending only on
the shared token-table width and token count.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaTracePublicBounds

open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTokenMachineInversion
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectParserSyntaxTraceBounds
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedInstallation
open FoundationCompactNumericListedDirectSequentFormulaTraceFormula

def compactSequentFormulaPublicParserFuelBound
    (tokenCount : Nat) : Nat :=
  16 * (tokenCount + 1) * (tokenCount + 1) + 8

def compactSequentFormulaStepPublicCoordinateSizeBound
    (width tokenCount : Nat) : Nat :=
  tokenCount +
    (tokenCount + 1) * tokenCount +
    (compactSequentFormulaPublicParserFuelBound tokenCount + 2) * tokenCount +
    compactParserSyntaxCanonicalTableWidthBound width tokenCount
      (compactSequentFormulaPublicParserFuelBound tokenCount) +
    2

def compactSequentFormulaTracePublicTableWidthBound
    (width tokenCount : Nat) : Nat :=
  tokenCount * 18 *
    compactSequentFormulaStepPublicCoordinateSizeBound width tokenCount

private theorem list_sum_map_le_length_mul
    {α : Type*} {values : List α} {weight : α → Nat} {bound : Nat}
    (hbound : ∀ value ∈ values, weight value <= bound) :
    (values.map weight).sum <= values.length * bound := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have hhead : weight head <= bound := hbound head (by simp)
      have htail : ∀ value ∈ tail, weight value <= bound := by
        intro value hvalue
        exact hbound value (by simp [hvalue])
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        weight head + (tail.map weight).sum <=
            bound + tail.length * bound :=
          Nat.add_le_add hhead (ih htail)
        _ = (tail.length + 1) * bound := by ring

private theorem compactSyntaxRunFuelBound_length_le_public
    {tokens : List Nat} {tokenCount : Nat}
    (hcount : tokens.length <= tokenCount) :
    compactSyntaxRunFuelBound tokens <=
      compactSequentFormulaPublicParserFuelBound tokenCount := by
  have hplus : tokens.length + 1 <= tokenCount + 1 := by omega
  have hsquare :
      (tokens.length + 1) * (tokens.length + 1) <=
        (tokenCount + 1) * (tokenCount + 1) :=
    Nat.mul_le_mul hplus hplus
  unfold compactSyntaxRunFuelBound
    compactSequentFormulaPublicParserFuelBound
  simpa only [Nat.mul_assoc] using
    Nat.add_le_add_right (Nat.mul_le_mul_left 16 hsquare) 8

private theorem compactParserSyntaxCanonicalTableWidthBound_mono_fuel
    {width tokenCount leftFuel rightFuel : Nat}
    (hfuel : leftFuel <= rightFuel) :
    compactParserSyntaxCanonicalTableWidthBound
        width tokenCount leftFuel <=
      compactParserSyntaxCanonicalTableWidthBound
        width tokenCount rightFuel := by
  have hcolumn :
      leftFuel * compactParserSyntaxAdjacentStepWitnessColumnCount <=
        rightFuel * compactParserSyntaxAdjacentStepWitnessColumnCount :=
    Nat.mul_le_mul_right
      compactParserSyntaxAdjacentStepWitnessColumnCount hfuel
  have hmain :
      leftFuel * compactParserSyntaxAdjacentStepWitnessColumnCount *
          compactParserSyntaxAdjacentStepPublicWidth width tokenCount <=
        rightFuel * compactParserSyntaxAdjacentStepWitnessColumnCount *
          compactParserSyntaxAdjacentStepPublicWidth width tokenCount :=
    Nat.mul_le_mul_right
      (compactParserSyntaxAdjacentStepPublicWidth width tokenCount) hcolumn
  unfold compactParserSyntaxCanonicalTableWidthBound
  omega

structure CompactSequentFormulaStepPublicBounds
    (row : CompactSequentFormulaStepCoordinates)
    (bound : Nat) : Prop where
  value_size_le :
    ∀ value ∈ compactSequentFormulaStepRowValues row,
      Nat.size value <= bound

theorem exists_compactSequentFormulaStepGraph_of_directTrace_with_publicBounds
    {tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount rowIndex
      currentStart currentFinish nextStart nextFinish
      valueStart valueFinish parserStateBoundary : Nat}
    {current next value : List Nat}
    {parserStates : List CompactUnifiedParserState}
    (hcurrent : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount currentStart currentFinish current)
    (hnext : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount nextStart nextFinish next)
    (hvalue : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount valueStart valueFinish value)
    (hparserStateRows : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokenCount parserStateBoundary parserStates)
    (hparserStateBoundarySize :
      Nat.size parserStateBoundary <=
        (parserStates.length + 1) * tokenCount)
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
            valueBoundary valueCount rowIndex row ∧
        CompactSequentFormulaStepPublicBounds row
          (compactSequentFormulaStepPublicCoordinateSizeBound
            width tokenCount) := by
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
  have hlocal : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound current)
      (current, [(1, 0, 0)], none) (some next) parserStates := by
    simpa [CompactFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using htrace
  have hstartWell : CompactSyntaxTaskStackFieldsWellFormed [(1, 0, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  rcases
      localTrace_exists_compactParserSyntaxExactBoundedGraph_with_publicWidth
        hparserStateRows hcurrentElementRows hnextElementRows
        hstartWell hlocal with
    ⟨parserTableWidth, hparserTableWidth, hparserGraphRaw⟩
  have hstateCount : parserStates.length =
      16 * (current.length + 1) * (current.length + 1) + 8 + 1 := by
    simpa [compactSyntaxRunFuelBound] using hlocal.1.1
  have hparserGraph : CompactParserSyntaxExactBoundedGraph
      tokenTable width tokenCount parserStateBoundary
      (16 * (current.length + 1) * (current.length + 1) + 8 + 1)
      currentBoundary current.length nextBoundary next.length
      1 0 0 parserTableWidth (2 ^ parserTableWidth) := by
    rw [← hstateCount]
    exact hparserGraphRaw
  have happend : CompactAdditiveNatListAppendSlices
      tokenTable width tokenCount
      valueStart valueFinish value.length
      nextStart nextFinish next.length
      currentStart currentFinish current.length :=
    (compactAdditiveNatListAppendSlices_iff_append
      ⟨valueInnerBoundary, hvalueStructure, hvalueElementRows, hvalueSize⟩
      ⟨nextBoundary, hnextStructure, hnextElementRows, hnextSize⟩
      ⟨currentBoundary, hcurrentStructure, hcurrentElementRows,
        hcurrentSize⟩).mpr hcurrentEq
  rcases
      (show CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount currentStart currentFinish current from
        ⟨currentBoundary, hcurrentStructure, hcurrentElementRows,
          hcurrentSize⟩).toSlice with
    ⟨currentBody, _hcurrentBodyBound, hcurrentHeader, _hcurrentFinishEq⟩
  rcases
      (show CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount nextStart nextFinish next from
        ⟨nextBoundary, hnextStructure, hnextElementRows,
          hnextSize⟩).toSlice with
    ⟨nextBody, _hnextBodyBound, hnextHeader, _hnextFinishEq⟩
  rcases
      (show CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount valueStart valueFinish value from
        ⟨valueInnerBoundary, hvalueStructure, hvalueElementRows,
          hvalueSize⟩).toSlice with
    ⟨valueBody, _hvalueBodyBound, hvalueHeader, _hvalueFinishEq⟩
  have hcurrentStartBound : currentStart <= tokenCount :=
    Nat.le_of_lt hcurrentHeader.1.1
  have hcurrentFinishBound : currentFinish <= tokenCount := by
    have := hcurrentHeader.2
    omega
  have hcurrentCountBound : current.length <= tokenCount := by
    have := hcurrentHeader.2
    omega
  have hnextStartBound : nextStart <= tokenCount :=
    Nat.le_of_lt hnextHeader.1.1
  have hnextFinishBound : nextFinish <= tokenCount := by
    have := hnextHeader.2
    omega
  have hnextCountBound : next.length <= tokenCount := by
    have := hnextHeader.2
    omega
  have hvalueStartBound : valueStart <= tokenCount :=
    Nat.le_of_lt hvalueHeader.1.1
  have hvalueFinishBound : valueFinish <= tokenCount := by
    have := hvalueHeader.2
    omega
  have hvalueCountBound : value.length <= tokenCount := by
    have := hvalueHeader.2
    omega
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
  have hgraph : CompactSequentFormulaStepGraph
      tokenTable width tokenCount suffixBoundary suffixCount
        valueBoundary valueCount rowIndex row := by
    exact ⟨hcurrentStartBound, hcurrentFinishBound, hcurrentCountBound,
      hnextStartBound, hnextFinishBound, hnextCountBound,
      hvalueStartBound, hvalueFinishBound, hvalueCountBound,
      hcurrentStartEntry, hcurrentFinishEntry, hnextStartEntry,
      hnextFinishEntry, hvalueStartEntry, hvalueFinishEntry,
      hcurrentWitness, hnextWitness, hvalueWitness, hparserGraph,
      happend, hsuffixCount⟩
  let fuelBound := compactSequentFormulaPublicParserFuelBound tokenCount
  let parserWidthBound :=
    compactParserSyntaxCanonicalTableWidthBound width tokenCount fuelBound
  let coordinateBound :=
    compactSequentFormulaStepPublicCoordinateSizeBound width tokenCount
  have hfuel :
      compactSyntaxRunFuelBound current <= fuelBound := by
    exact compactSyntaxRunFuelBound_length_le_public hcurrentCountBound
  have hparserWidth :
      parserTableWidth <= parserWidthBound := by
    exact hparserTableWidth.trans
      (compactParserSyntaxCanonicalTableWidthBound_mono_fuel hfuel)
  have hcurrentBoundary :
      Nat.size currentBoundary <=
        (tokenCount + 1) * tokenCount := by
    exact hcurrentSize.trans (Nat.mul_le_mul_right tokenCount (by omega))
  have hnextBoundary :
      Nat.size nextBoundary <=
        (tokenCount + 1) * tokenCount := by
    exact hnextSize.trans (Nat.mul_le_mul_right tokenCount (by omega))
  have hvalueBoundary :
      Nat.size valueInnerBoundary <=
        (tokenCount + 1) * tokenCount := by
    exact hvalueSize.trans (Nat.mul_le_mul_right tokenCount (by omega))
  have hparserStateBoundary :
      Nat.size parserStateBoundary <=
        (fuelBound + 2) * tokenCount := by
    calc
      Nat.size parserStateBoundary <=
          (parserStates.length + 1) * tokenCount :=
        hparserStateBoundarySize
      _ = (compactSyntaxRunFuelBound current + 2) * tokenCount := by
        rw [hlocal.1.1]
      _ <= (fuelBound + 2) * tokenCount :=
        Nat.mul_le_mul_right tokenCount (by omega)
  have hparserStateBoundaryPublic :
      Nat.size parserStateBoundary <=
        (compactSequentFormulaPublicParserFuelBound tokenCount + 2) *
          tokenCount := by
    simpa only [fuelBound] using hparserStateBoundary
  have hparserWidthPublic :
      parserTableWidth <=
        compactParserSyntaxCanonicalTableWidthBound width tokenCount
          (compactSequentFormulaPublicParserFuelBound tokenCount) := by
    simpa only [parserWidthBound, fuelBound] using hparserWidth
  have hpublic :
      CompactSequentFormulaStepPublicBounds row coordinateBound := by
    constructor
    intro coordinate hcoordinate
    simp only [compactSequentFormulaStepRowValues, List.mem_cons,
      List.not_mem_nil, or_false] at hcoordinate
    rcases hcoordinate with
      h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h
    all_goals
      subst coordinate
      dsimp only [row, currentBoundarySize, nextBoundarySize,
        valueBoundarySize, coordinateBound,
        compactSequentFormulaStepPublicCoordinateSizeBound,
        fuelBound, parserWidthBound]
    · exact (natSize_le_of_le hcurrentStartBound).trans (by omega)
    · exact (natSize_le_of_le hcurrentFinishBound).trans (by omega)
    · exact hcurrentBoundary.trans (by omega)
    · exact (natSize_le_of_le hcurrentCountBound).trans (by omega)
    · exact (natSize_le_of_le hcurrentBoundary).trans (by omega)
    · exact (natSize_le_of_le hnextStartBound).trans (by omega)
    · exact (natSize_le_of_le hnextFinishBound).trans (by omega)
    · exact hnextBoundary.trans (by omega)
    · exact (natSize_le_of_le hnextCountBound).trans (by omega)
    · exact (natSize_le_of_le hnextBoundary).trans (by omega)
    · exact (natSize_le_of_le hvalueStartBound).trans (by omega)
    · exact (natSize_le_of_le hvalueFinishBound).trans (by omega)
    · exact hvalueBoundary.trans (by omega)
    · exact (natSize_le_of_le hvalueCountBound).trans (by omega)
    · exact (natSize_le_of_le hvalueBoundary).trans (by omega)
    · exact hparserStateBoundaryPublic.trans (by omega)
    · exact (natSize_le_of_le hparserWidthPublic).trans (by omega)
    · rw [Nat.size_pow]
      exact Nat.add_le_add_right hparserWidthPublic 1 |>.trans (by omega)
  exact ⟨row, hgraph, hpublic⟩

theorem exists_compactSequentFormulaTraceBoundedGraph_of_directData_with_publicWidth
    {tokenTable width tokenCount suffixBoundary valueBoundary : Nat}
    {suffixes values : List (List Nat)}
    {parserTraces : List CompactFormulaTokenParserDirectTrace}
    (hsuffixCount : suffixes.length = values.length + 1)
    (hparserCount : parserTraces.length = values.length)
    (hsuffixRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        suffixBoundary suffixes)
    (hvalueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        valueBoundary values)
    (hvalueCount : values.length <= tokenCount)
    (hparserRows : ∀ index < values.length,
      ∃ parserStateBoundary,
        CompactUnifiedParserStateListRowLayouts
          tokenTable width tokenCount parserStateBoundary
            (parserTraces.getI index) ∧
        Nat.size parserStateBoundary <=
          ((parserTraces.getI index).length + 1) * tokenCount)
    (hsteps : ∀ index < values.length,
      CompactFormulaTokenParserDirectTraceValid
        0 (suffixes.getI index) (suffixes.getI (index + 1))
          (parserTraces.getI index) ∧
      suffixes.getI index =
        values.getI index ++ suffixes.getI (index + 1)) :
    ∃ tableWidth,
      tableWidth <=
          compactSequentFormulaTracePublicTableWidthBound width tokenCount ∧
        CompactSequentFormulaTraceBoundedGraph
          tokenTable width tokenCount suffixBoundary suffixes.length
            valueBoundary values.length tableWidth (2 ^ tableWidth) := by
  have hexists (index : Fin values.length) :
      ∃ row : CompactSequentFormulaStepCoordinates,
        CompactSequentFormulaStepGraph
            tokenTable width tokenCount suffixBoundary suffixes.length
              valueBoundary values.length index row ∧
          CompactSequentFormulaStepPublicBounds row
            (compactSequentFormulaStepPublicCoordinateSizeBound
              width tokenCount) := by
    have hindex : index.1 < values.length := index.2
    have hcurrentIndex : index.1 < suffixes.length := by
      rw [hsuffixCount]
      omega
    have hnextIndex : index.1 + 1 < suffixes.length := by
      rw [hsuffixCount]
      omega
    rcases hsuffixRows index.1 hcurrentIndex with
      ⟨currentStart, _hcurrentStartBound,
        currentFinish, _hcurrentFinishBound,
        hcurrentStartEntry, hcurrentFinishEntry, hcurrentLayout⟩
    rcases hsuffixRows (index.1 + 1) hnextIndex with
      ⟨nextStart, _hnextStartBound,
        nextFinish, _hnextFinishBound,
        hnextStartEntry, hnextFinishEntry, hnextLayout⟩
    rcases hvalueRows index.1 hindex with
      ⟨valueStart, _hvalueStartBound,
        valueFinish, _hvalueFinishBound,
        hvalueStartEntry, hvalueFinishEntry, hvalueLayout⟩
    rcases hparserRows index.1 hindex with
      ⟨parserStateBoundary, hparserStateRows,
        hparserStateBoundarySize⟩
    rcases hsteps index.1 hindex with ⟨hparserTrace, hcurrentEq⟩
    exact
      exists_compactSequentFormulaStepGraph_of_directTrace_with_publicBounds
        hcurrentLayout hnextLayout hvalueLayout hparserStateRows
        hparserStateBoundarySize hparserTrace hcurrentEq
        hcurrentStartEntry hcurrentFinishEntry
        hnextStartEntry hnextFinishEntry
        hvalueStartEntry hvalueFinishEntry hsuffixCount
  let rowAt (index : Fin values.length) :
      CompactSequentFormulaStepCoordinates :=
    Classical.choose (hexists index)
  have hrowAt (index : Fin values.length) :
      CompactSequentFormulaStepGraph
          tokenTable width tokenCount suffixBoundary suffixes.length
            valueBoundary values.length index (rowAt index) ∧
        CompactSequentFormulaStepPublicBounds (rowAt index)
          (compactSequentFormulaStepPublicCoordinateSizeBound
            width tokenCount) :=
    Classical.choose_spec (hexists index)
  let rows : List CompactSequentFormulaStepCoordinates := List.ofFn rowAt
  have hrowsLength : rows.length = values.length := by
    simp [rows]
  have hrows : ∀ index < values.length,
      ∃ row ∈ rows,
        CompactSequentFormulaStepGraph
          tokenTable width tokenCount suffixBoundary suffixes.length
            valueBoundary values.length index row := by
    intro index hindex
    let finiteIndex : Fin values.length := ⟨index, hindex⟩
    refine ⟨rowAt finiteIndex, ?_, ?_⟩
    · simp [rows, finiteIndex]
    · simpa [finiteIndex] using (hrowAt finiteIndex).1
  have hrowDynamic : ∀ row ∈ rows,
      compactSequentFormulaStepDynamicWidth row <=
        18 * compactSequentFormulaStepPublicCoordinateSizeBound
          width tokenCount := by
    intro row hrow
    have hrowEq : ∃ index : Fin values.length, rowAt index = row := by
      simpa [rows] using hrow
    rcases hrowEq with ⟨index, hrowEq⟩
    subst row
    have hbound := (hrowAt index).2.value_size_le
    simpa [compactSequentFormulaStepDynamicWidth,
      compactSequentFormulaStepRowValues] using
        (list_sum_map_le_length_mul hbound)
  let tableWidth := compactSequentFormulaTraceDynamicWidth rows
  have htableWidth :
      tableWidth <=
        compactSequentFormulaTracePublicTableWidthBound width tokenCount := by
    have hsum := list_sum_map_le_length_mul
      (values := rows)
      (weight := compactSequentFormulaStepDynamicWidth)
      hrowDynamic
    rw [hrowsLength] at hsum
    dsimp only [tableWidth, compactSequentFormulaTraceDynamicWidth]
    unfold compactSequentFormulaTracePublicTableWidthBound
    calc
      (rows.map compactSequentFormulaStepDynamicWidth).sum <=
          values.length *
            (18 * compactSequentFormulaStepPublicCoordinateSizeBound
              width tokenCount) := hsum
      _ <= tokenCount *
          (18 * compactSequentFormulaStepPublicCoordinateSizeBound
            width tokenCount) :=
        Nat.mul_le_mul_right
          (18 * compactSequentFormulaStepPublicCoordinateSizeBound
            width tokenCount) hvalueCount
      _ = tokenCount * 18 *
          compactSequentFormulaStepPublicCoordinateSizeBound
            width tokenCount := by ring
  have hsuffixWellFormed :
      CompactAdditiveNatListListRowsWellFormed
        tokenTable width tokenCount suffixBoundary suffixes.length := by
    exact
      FoundationCompactNumericListedDirectNatListListRowsFormula.CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hsuffixRows
  have hvalueWellFormed :
      CompactAdditiveNatListListRowsWellFormed
        tokenTable width tokenCount valueBoundary values.length := by
    exact
      FoundationCompactNumericListedDirectNatListListRowsFormula.CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hvalueRows
  have hbounded : CompactSequentFormulaStepRowsBoundedGraph
      tokenTable width tokenCount suffixBoundary suffixes.length
        valueBoundary values.length values.length tableWidth
          (2 ^ tableWidth) := by
    refine ⟨rfl, ?_⟩
    intro index hindex
    rcases hrows index hindex with ⟨row, hrowMem, hrowGraph⟩
    apply CompactSequentFormulaStepGraph.toBounded hrowGraph
    intro value hvalue
    have hsize :=
      compactSequentFormulaStep_value_size_le_dynamic row hvalue
    have hrowWidth :=
      compactSequentFormulaStep_dynamicWidth_le_trace hrowMem
    exact (Nat.size_le.mp (hsize.trans hrowWidth)).le
  exact ⟨tableWidth, htableWidth, hsuffixCount,
    hsuffixWellFormed, hvalueWellFormed, hbounded⟩

#print axioms
  exists_compactSequentFormulaStepGraph_of_directTrace_with_publicBounds
#print axioms
  exists_compactSequentFormulaTraceBoundedGraph_of_directData_with_publicWidth

end FoundationCompactNumericListedDirectSequentFormulaTracePublicBounds
