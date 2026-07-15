import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
import integration.FoundationCompactNumericListedDirectTokenStreamInverse

/-!
# Fixed-width witness table for adjacent formula-transform steps

Each row stores the fourteen current-state values, fourteen next-state values,
seven parser-step slots, the consumed-token count, and the mapped output head.
The ten trace-wide parameters remain global, so every row has exactly
thirty-seven columns.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessTable

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula

def compactFormulaTransformAdjacentStepWitnessColumnCount : Nat := 37

def compactFormulaTransformAdjacentStepRowValues
    (row : CompactFormulaTransformAdjacentStepRow) : List Nat :=
  [row.currentCoordinates.start,
    row.currentCoordinates.finish,
    row.currentCoordinates.parserFinish,
    row.currentCoordinates.parserTokensFinish,
    row.currentCoordinates.parserTasksFinish,
    row.currentCoordinates.parserTokensBoundary,
    row.currentCoordinates.parserTokensCount,
    row.currentCoordinates.parserTasksBoundary,
    row.currentCoordinates.parserTasksCount,
    row.currentCoordinates.outputBoundary,
    row.currentCoordinates.outputCount,
    row.currentSize.parserTokensBoundarySize,
    row.currentSize.parserTasksBoundarySize,
    row.currentSize.outputBoundarySize,
    row.nextCoordinates.start,
    row.nextCoordinates.finish,
    row.nextCoordinates.parserFinish,
    row.nextCoordinates.parserTokensFinish,
    row.nextCoordinates.parserTasksFinish,
    row.nextCoordinates.parserTokensBoundary,
    row.nextCoordinates.parserTokensCount,
    row.nextCoordinates.parserTasksBoundary,
    row.nextCoordinates.parserTasksCount,
    row.nextCoordinates.outputBoundary,
    row.nextCoordinates.outputCount,
    row.nextSize.parserTokensBoundarySize,
    row.nextSize.parserTasksBoundarySize,
    row.nextSize.outputBoundarySize,
    row.stepWitness.slot0,
    row.stepWitness.slot1,
    row.stepWitness.slot2,
    row.stepWitness.slot3,
    row.stepWitness.slot4,
    row.stepWitness.slot5,
    row.stepWitness.slot6,
    row.consumedCount,
    row.mappedHead]

@[simp] theorem compactFormulaTransformAdjacentStepRowValues_length
    (row : CompactFormulaTransformAdjacentStepRow) :
    (compactFormulaTransformAdjacentStepRowValues row).length =
      compactFormulaTransformAdjacentStepWitnessColumnCount := by
  simp [compactFormulaTransformAdjacentStepRowValues,
    compactFormulaTransformAdjacentStepWitnessColumnCount]

def compactFormulaTransformAdjacentStepWitnessTableValues
    (rows : List CompactFormulaTransformAdjacentStepRow) : List Nat :=
  (List.range
      (rows.length * compactFormulaTransformAdjacentStepWitnessColumnCount)).map
    fun flatIndex =>
      (compactFormulaTransformAdjacentStepRowValues
        (rows.getI
          (flatIndex /
            compactFormulaTransformAdjacentStepWitnessColumnCount))).getI
        (flatIndex % compactFormulaTransformAdjacentStepWitnessColumnCount)

@[simp] theorem compactFormulaTransformAdjacentStepWitnessTableValues_length
    (rows : List CompactFormulaTransformAdjacentStepRow) :
    (compactFormulaTransformAdjacentStepWitnessTableValues rows).length =
      rows.length * compactFormulaTransformAdjacentStepWitnessColumnCount := by
  simp [compactFormulaTransformAdjacentStepWitnessTableValues]

theorem compactFormulaTransformAdjacentStepWitnessTableValues_getI
    (rows : List CompactFormulaTransformAdjacentStepRow)
    (rowIndex column : Nat) (hrowIndex : rowIndex < rows.length)
    (hcolumn : column <
      compactFormulaTransformAdjacentStepWitnessColumnCount) :
    (compactFormulaTransformAdjacentStepWitnessTableValues rows).getI
        (rowIndex * compactFormulaTransformAdjacentStepWitnessColumnCount +
          column) =
      (compactFormulaTransformAdjacentStepRowValues
        (rows.getI rowIndex)).getI column := by
  have hflatIndex :
      rowIndex * compactFormulaTransformAdjacentStepWitnessColumnCount +
          column <
        rows.length * compactFormulaTransformAdjacentStepWitnessColumnCount := by
    rw [compactFormulaTransformAdjacentStepWitnessColumnCount] at hcolumn ⊢
    omega
  have hdivision :
      (rowIndex * compactFormulaTransformAdjacentStepWitnessColumnCount +
          column) / compactFormulaTransformAdjacentStepWitnessColumnCount =
        rowIndex := by
    rw [compactFormulaTransformAdjacentStepWitnessColumnCount] at hcolumn ⊢
    omega
  have hremainder :
      (rowIndex * compactFormulaTransformAdjacentStepWitnessColumnCount +
          column) % compactFormulaTransformAdjacentStepWitnessColumnCount =
        column := by
    rw [compactFormulaTransformAdjacentStepWitnessColumnCount] at hcolumn ⊢
    omega
  rw [List.getI_eq_getElem _ (by simpa using hflatIndex)]
  simp [compactFormulaTransformAdjacentStepWitnessTableValues,
    hdivision, hremainder]

def CompactFormulaTransformAdjacentStepRowFits
    (tableWidth : Nat) (row : CompactFormulaTransformAdjacentStepRow) : Prop :=
  ∀ column < compactFormulaTransformAdjacentStepWitnessColumnCount,
    Nat.size
      ((compactFormulaTransformAdjacentStepRowValues row).getI column) ≤
        tableWidth

def CompactFormulaTransformAdjacentStepRowsFit
    (tableWidth : Nat)
    (rows : List CompactFormulaTransformAdjacentStepRow) : Prop :=
  ∀ row ∈ rows, CompactFormulaTransformAdjacentStepRowFits tableWidth row

def compactFormulaTransformAdjacentStepDynamicWidth
    (rows : List CompactFormulaTransformAdjacentStepRow) : Nat :=
  ((rows.flatMap compactFormulaTransformAdjacentStepRowValues).map Nat.size).sum

theorem CompactFormulaTransformAdjacentStepRowFits.value_size_le
    {tableWidth : Nat} {row : CompactFormulaTransformAdjacentStepRow}
    (hfit : CompactFormulaTransformAdjacentStepRowFits tableWidth row)
    {value : Nat}
    (hvalue : value ∈ compactFormulaTransformAdjacentStepRowValues row) :
    Nat.size value ≤ tableWidth := by
  rcases List.getElem_of_mem hvalue with ⟨column, hcolumn, rfl⟩
  have hcolumn' : column <
      compactFormulaTransformAdjacentStepWitnessColumnCount := by
    simpa using hcolumn
  simpa [List.getI_eq_getElem _ hcolumn] using hfit column hcolumn'

theorem compactFormulaTransformAdjacentStepRowsFit_dynamic
    (rows : List CompactFormulaTransformAdjacentStepRow) :
    CompactFormulaTransformAdjacentStepRowsFit
      (compactFormulaTransformAdjacentStepDynamicWidth rows) rows := by
  intro row hrow column hcolumn
  have hindex : column <
      (compactFormulaTransformAdjacentStepRowValues row).length := by
    simpa using hcolumn
  let value :=
    (compactFormulaTransformAdjacentStepRowValues row).getI column
  have hvalueMem :
      value ∈
        rows.flatMap compactFormulaTransformAdjacentStepRowValues := by
    apply List.mem_flatMap.mpr
    refine ⟨row, hrow, ?_⟩
    rw [show value =
      (compactFormulaTransformAdjacentStepRowValues row).getI column by rfl,
      List.getI_eq_getElem _ hindex]
    exact List.getElem_mem hindex
  have hsizeMem :
      Nat.size value ∈
        (rows.flatMap compactFormulaTransformAdjacentStepRowValues).map
          Nat.size := by
    exact List.mem_map.mpr ⟨_, hvalueMem, rfl⟩
  simpa [compactFormulaTransformAdjacentStepDynamicWidth, value] using
    List.single_le_sum (by simp) _ hsizeMem

theorem compactFormulaTransformAdjacentStepWitnessTableValues_size_le
    {tableWidth : Nat}
    {rows : List CompactFormulaTransformAdjacentStepRow}
    (hfit : CompactFormulaTransformAdjacentStepRowsFit tableWidth rows) :
    ∀ value ∈ compactFormulaTransformAdjacentStepWitnessTableValues rows,
      Nat.size value ≤ tableWidth := by
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨flatIndex, hflatIndex, rfl⟩
  have hflatBound :
      flatIndex <
        rows.length * compactFormulaTransformAdjacentStepWitnessColumnCount :=
    List.mem_range.mp hflatIndex
  have hcolumn :
      flatIndex % compactFormulaTransformAdjacentStepWitnessColumnCount <
        compactFormulaTransformAdjacentStepWitnessColumnCount :=
    Nat.mod_lt _ (by
      simp [compactFormulaTransformAdjacentStepWitnessColumnCount])
  have hrowIndex :
      flatIndex / compactFormulaTransformAdjacentStepWitnessColumnCount <
        rows.length := by
    rw [compactFormulaTransformAdjacentStepWitnessColumnCount]
      at hflatBound ⊢
    omega
  apply hfit
    (rows.getI
      (flatIndex / compactFormulaTransformAdjacentStepWitnessColumnCount))
  · rw [List.getI_eq_getElem _ hrowIndex]
    exact List.getElem_mem hrowIndex
  · exact hcolumn

def compactFormulaTransformAdjacentStepWitnessTableCode
    (tableWidth : Nat)
    (rows : List CompactFormulaTransformAdjacentStepRow) : Nat :=
  compactFixedWidthTableCode tableWidth
    (compactFormulaTransformAdjacentStepWitnessTableValues rows)

def CompactFormulaTransformAdjacentStepWitnessTableCarriesRows
    (tableWidth table : Nat)
    (rows : List CompactFormulaTransformAdjacentStepRow) : Prop :=
  ∀ rowIndex < rows.length,
    ∀ column < compactFormulaTransformAdjacentStepWitnessColumnCount,
      CompactFixedWidthEntry table tableWidth
        (rowIndex * compactFormulaTransformAdjacentStepWitnessColumnCount +
          column)
        ((compactFormulaTransformAdjacentStepRowValues
          (rows.getI rowIndex)).getI column)

theorem compactFormulaTransformAdjacentStepWitnessTableCode_carriesRows
    {tableWidth : Nat}
    {rows : List CompactFormulaTransformAdjacentStepRow}
    (hfit : CompactFormulaTransformAdjacentStepRowsFit tableWidth rows) :
    CompactFormulaTransformAdjacentStepWitnessTableCarriesRows tableWidth
      (compactFormulaTransformAdjacentStepWitnessTableCode tableWidth rows)
        rows := by
  intro rowIndex hrowIndex column hcolumn
  have hflatIndex :
      rowIndex * compactFormulaTransformAdjacentStepWitnessColumnCount +
          column <
        (compactFormulaTransformAdjacentStepWitnessTableValues rows).length := by
    simp only [compactFormulaTransformAdjacentStepWitnessTableValues_length]
    rw [compactFormulaTransformAdjacentStepWitnessColumnCount] at hcolumn ⊢
    omega
  have hentry := compactFixedWidthTableCode_entry tableWidth
    (compactFormulaTransformAdjacentStepWitnessTableValues rows)
    (rowIndex * compactFormulaTransformAdjacentStepWitnessColumnCount +
      column)
    hflatIndex
    (compactFormulaTransformAdjacentStepWitnessTableValues_size_le hfit)
  rw [compactFormulaTransformAdjacentStepWitnessTableValues_getI
    rows rowIndex column hrowIndex hcolumn] at hentry
  exact hentry

theorem compactFormulaTransformAdjacentStepWitnessTableCode_size_le
    (tableWidth : Nat)
    (rows : List CompactFormulaTransformAdjacentStepRow) :
    Nat.size
        (compactFormulaTransformAdjacentStepWitnessTableCode tableWidth rows) ≤
      rows.length * compactFormulaTransformAdjacentStepWitnessColumnCount *
        tableWidth := by
  simpa [compactFormulaTransformAdjacentStepWitnessTableCode] using
    compactFixedWidthTableCode_size_le tableWidth
      (compactFormulaTransformAdjacentStepWitnessTableValues rows)

def compactFormulaTransformAdjacentStepFormulaEnvironmentFromColumns
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount : Nat)
    (columnValue : Nat → Nat) (coordinate : Fin 47) : Nat :=
  if hglobal : coordinate.val < 10 then
    (![tokenTable, width, tokenCount, stateBoundary, stateCount, rowIndex,
      mode, witnessStart, witnessFinish, witnessCount] : Fin 10 → Nat)
        ⟨coordinate.val, hglobal⟩
  else
    columnValue (coordinate.val - 10)

def compactFormulaTransformAdjacentStepRowFormulaEnvironment
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) : Fin 47 → Nat :=
  compactFormulaTransformAdjacentStepFormulaEnvironmentFromColumns
    tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount fun column =>
        (compactFormulaTransformAdjacentStepRowValues row).getI column

@[simp] theorem
    compactFormulaTransformAdjacentStepRowFormulaEnvironment_spec
    (tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) :
    compactFormulaTransformAdjacentStepRowDef.val.Evalb
        (compactFormulaTransformAdjacentStepRowFormulaEnvironment
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
            witnessStart witnessFinish witnessCount row) ↔
      CompactFormulaTransformAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount row := by
  have henv :
      compactFormulaTransformAdjacentStepRowFormulaEnvironment
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
            witnessStart witnessFinish witnessCount row =
        compactFormulaTransformAdjacentStepRowEnvironment
          tokenTable width tokenCount stateBoundary stateCount rowIndex mode
            witnessStart witnessFinish witnessCount row := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [henv]
  exact compactFormulaTransformAdjacentStepRowDef_spec
    tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount row

def compactFormulaTransformAdjacentStepWitnessTableColumnValue
    (tableWidth table rowIndex column : Nat) : Nat :=
  compactFixedWidthTableValue table tableWidth
    (rowIndex * compactFormulaTransformAdjacentStepWitnessColumnCount +
      column)

def compactFormulaTransformAdjacentStepWitnessTableFormulaEnvironment
    (tokenTable width tokenCount stateBoundary stateCount tableWidth table
      rowIndex mode witnessStart witnessFinish witnessCount : Nat) :
    Fin 47 → Nat :=
  compactFormulaTransformAdjacentStepFormulaEnvironmentFromColumns
    tokenTable width tokenCount stateBoundary stateCount rowIndex mode
      witnessStart witnessFinish witnessCount fun column =>
        compactFormulaTransformAdjacentStepWitnessTableColumnValue
          tableWidth table rowIndex column

def CompactFormulaTransformAdjacentStepWitnessTableGraph
    (tokenTable width tokenCount stateBoundary stateCount tableWidth table
      rowCount mode witnessStart witnessFinish witnessCount : Nat) : Prop :=
  ∀ rowIndex < rowCount,
    compactFormulaTransformAdjacentStepRowDef.val.Evalb
      (compactFormulaTransformAdjacentStepWitnessTableFormulaEnvironment
        tokenTable width tokenCount stateBoundary stateCount tableWidth table
          rowIndex mode witnessStart witnessFinish witnessCount)

def CompactFormulaTransformAdjacentStepRowsValid
    (tokenTable width tokenCount stateBoundary stateCount mode
      witnessStart witnessFinish witnessCount : Nat)
    (rows : List CompactFormulaTransformAdjacentStepRow) : Prop :=
  ∀ rowIndex < rows.length,
    CompactFormulaTransformAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex mode
        witnessStart witnessFinish witnessCount (rows.getI rowIndex)

theorem compactFormulaTransformAdjacentStepWitnessTableColumnValue_eq
    {tableWidth table : Nat}
    {rows : List CompactFormulaTransformAdjacentStepRow}
    (hrows : CompactFormulaTransformAdjacentStepWitnessTableCarriesRows
      tableWidth table rows)
    (rowIndex column : Nat) (hrowIndex : rowIndex < rows.length)
    (hcolumn : column <
      compactFormulaTransformAdjacentStepWitnessColumnCount) :
    compactFormulaTransformAdjacentStepWitnessTableColumnValue
        tableWidth table rowIndex column =
      (compactFormulaTransformAdjacentStepRowValues
        (rows.getI rowIndex)).getI column := by
  exact (CompactFixedWidthEntry.value_eq_tableValue
    (hrows rowIndex hrowIndex column hcolumn)).symm

theorem compactFormulaTransformAdjacentStepWitnessTableFormulaEnvironment_eq
    {tokenTable width tokenCount stateBoundary stateCount tableWidth table
      mode witnessStart witnessFinish witnessCount : Nat}
    {rows : List CompactFormulaTransformAdjacentStepRow}
    (hrows : CompactFormulaTransformAdjacentStepWitnessTableCarriesRows
      tableWidth table rows)
    (rowIndex : Nat) (hrowIndex : rowIndex < rows.length) :
    compactFormulaTransformAdjacentStepWitnessTableFormulaEnvironment
        tokenTable width tokenCount stateBoundary stateCount tableWidth table
          rowIndex mode witnessStart witnessFinish witnessCount =
      compactFormulaTransformAdjacentStepRowFormulaEnvironment
        tokenTable width tokenCount stateBoundary stateCount rowIndex mode
          witnessStart witnessFinish witnessCount (rows.getI rowIndex) := by
  have hcolumn (column : Nat)
      (hcolumn : column <
        compactFormulaTransformAdjacentStepWitnessColumnCount) :=
    compactFormulaTransformAdjacentStepWitnessTableColumnValue_eq
      hrows rowIndex column hrowIndex hcolumn
  funext coordinate
  by_cases hglobal : coordinate.val < 10
  · simp [compactFormulaTransformAdjacentStepWitnessTableFormulaEnvironment,
      compactFormulaTransformAdjacentStepRowFormulaEnvironment,
      compactFormulaTransformAdjacentStepFormulaEnvironmentFromColumns,
      hglobal]
  · simp only [
      compactFormulaTransformAdjacentStepWitnessTableFormulaEnvironment,
      compactFormulaTransformAdjacentStepRowFormulaEnvironment,
      compactFormulaTransformAdjacentStepFormulaEnvironmentFromColumns,
      hglobal, dite_false]
    apply hcolumn
    have hcoordinate := coordinate.isLt
    simp only [compactFormulaTransformAdjacentStepWitnessColumnCount]
    omega

theorem CompactFormulaTransformAdjacentStepWitnessTableCarriesRows.graph
    {tokenTable width tokenCount stateBoundary stateCount tableWidth table
      mode witnessStart witnessFinish witnessCount : Nat}
    {rows : List CompactFormulaTransformAdjacentStepRow}
    (hrows : CompactFormulaTransformAdjacentStepWitnessTableCarriesRows
      tableWidth table rows)
    (hvalid : CompactFormulaTransformAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary stateCount mode
        witnessStart witnessFinish witnessCount rows) :
    CompactFormulaTransformAdjacentStepWitnessTableGraph
      tokenTable width tokenCount stateBoundary stateCount tableWidth table
        rows.length mode witnessStart witnessFinish witnessCount := by
  intro rowIndex hrowIndex
  rw [compactFormulaTransformAdjacentStepWitnessTableFormulaEnvironment_eq
    hrows rowIndex hrowIndex]
  rw [compactFormulaTransformAdjacentStepRowFormulaEnvironment_spec]
  exact hvalid rowIndex hrowIndex

theorem compactFormulaTransformAdjacentStepWitnessTableCode_graph
    {tokenTable width tokenCount stateBoundary stateCount tableWidth mode
      witnessStart witnessFinish witnessCount : Nat}
    {rows : List CompactFormulaTransformAdjacentStepRow}
    (hfit : CompactFormulaTransformAdjacentStepRowsFit tableWidth rows)
    (hvalid : CompactFormulaTransformAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary stateCount mode
        witnessStart witnessFinish witnessCount rows) :
    CompactFormulaTransformAdjacentStepWitnessTableGraph
      tokenTable width tokenCount stateBoundary stateCount tableWidth
        (compactFormulaTransformAdjacentStepWitnessTableCode tableWidth rows)
        rows.length mode witnessStart witnessFinish witnessCount :=
  (compactFormulaTransformAdjacentStepWitnessTableCode_carriesRows hfit).graph
    hvalid

#print axioms compactFormulaTransformAdjacentStepWitnessTableValues_getI
#print axioms compactFormulaTransformAdjacentStepRowsFit_dynamic
#print axioms compactFormulaTransformAdjacentStepWitnessTableCode_carriesRows
#print axioms compactFormulaTransformAdjacentStepWitnessTableCode_size_le
#print axioms compactFormulaTransformAdjacentStepRowFormulaEnvironment_spec
#print axioms compactFormulaTransformAdjacentStepWitnessTableFormulaEnvironment_eq
#print axioms CompactFormulaTransformAdjacentStepWitnessTableCarriesRows.graph
#print axioms compactFormulaTransformAdjacentStepWitnessTableCode_graph

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessTable
