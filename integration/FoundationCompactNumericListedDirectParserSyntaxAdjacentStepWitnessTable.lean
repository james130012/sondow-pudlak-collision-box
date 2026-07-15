import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
import integration.FoundationCompactNumericListedDirectTokenStreamInverse

/-!
# Fixed-width witness table for adjacent syntax-parser steps

Each row stores ten current-state values, ten next-state values, and seven
syntax-step witness slots.  The six trace-wide parameters remain global, so
every row has exactly twenty-seven fixed-width columns.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula

def compactParserSyntaxAdjacentStepWitnessColumnCount : Nat := 27

def compactParserSyntaxAdjacentStepRowValues
    (row : CompactParserSyntaxAdjacentStepRow) : List Nat :=
  [row.currentCoordinates.start,
    row.currentCoordinates.finish,
    row.currentCoordinates.tokensFinish,
    row.currentCoordinates.tasksFinish,
    row.currentCoordinates.tokensBoundary,
    row.currentCoordinates.tokensCount,
    row.currentCoordinates.tasksBoundary,
    row.currentCoordinates.tasksCount,
    row.currentSize.tokensBoundarySize,
    row.currentSize.tasksBoundarySize,
    row.nextCoordinates.start,
    row.nextCoordinates.finish,
    row.nextCoordinates.tokensFinish,
    row.nextCoordinates.tasksFinish,
    row.nextCoordinates.tokensBoundary,
    row.nextCoordinates.tokensCount,
    row.nextCoordinates.tasksBoundary,
    row.nextCoordinates.tasksCount,
    row.nextSize.tokensBoundarySize,
    row.nextSize.tasksBoundarySize,
    row.stepWitness.slot0,
    row.stepWitness.slot1,
    row.stepWitness.slot2,
    row.stepWitness.slot3,
    row.stepWitness.slot4,
    row.stepWitness.slot5,
    row.stepWitness.slot6]

@[simp] theorem compactParserSyntaxAdjacentStepRowValues_length
    (row : CompactParserSyntaxAdjacentStepRow) :
    (compactParserSyntaxAdjacentStepRowValues row).length =
      compactParserSyntaxAdjacentStepWitnessColumnCount := by
  simp [compactParserSyntaxAdjacentStepRowValues,
    compactParserSyntaxAdjacentStepWitnessColumnCount]

def compactParserSyntaxAdjacentStepWitnessTableValues
    (rows : List CompactParserSyntaxAdjacentStepRow) : List Nat :=
  (List.range
      (rows.length * compactParserSyntaxAdjacentStepWitnessColumnCount)).map
    fun flatIndex =>
      (compactParserSyntaxAdjacentStepRowValues
        (rows.getI
          (flatIndex / compactParserSyntaxAdjacentStepWitnessColumnCount))).getI
        (flatIndex % compactParserSyntaxAdjacentStepWitnessColumnCount)

@[simp] theorem compactParserSyntaxAdjacentStepWitnessTableValues_length
    (rows : List CompactParserSyntaxAdjacentStepRow) :
    (compactParserSyntaxAdjacentStepWitnessTableValues rows).length =
      rows.length * compactParserSyntaxAdjacentStepWitnessColumnCount := by
  simp [compactParserSyntaxAdjacentStepWitnessTableValues]

theorem compactParserSyntaxAdjacentStepWitnessTableValues_getI
    (rows : List CompactParserSyntaxAdjacentStepRow)
    (rowIndex column : Nat) (hrowIndex : rowIndex < rows.length)
    (hcolumn : column < compactParserSyntaxAdjacentStepWitnessColumnCount) :
    (compactParserSyntaxAdjacentStepWitnessTableValues rows).getI
        (rowIndex * compactParserSyntaxAdjacentStepWitnessColumnCount + column) =
      (compactParserSyntaxAdjacentStepRowValues
        (rows.getI rowIndex)).getI column := by
  have hflatIndex :
      rowIndex * compactParserSyntaxAdjacentStepWitnessColumnCount + column <
        rows.length * compactParserSyntaxAdjacentStepWitnessColumnCount := by
    rw [compactParserSyntaxAdjacentStepWitnessColumnCount] at hcolumn ⊢
    omega
  have hdivision :
      (rowIndex * compactParserSyntaxAdjacentStepWitnessColumnCount + column) /
          compactParserSyntaxAdjacentStepWitnessColumnCount = rowIndex := by
    rw [compactParserSyntaxAdjacentStepWitnessColumnCount] at hcolumn ⊢
    omega
  have hremainder :
      (rowIndex * compactParserSyntaxAdjacentStepWitnessColumnCount + column) %
          compactParserSyntaxAdjacentStepWitnessColumnCount = column := by
    rw [compactParserSyntaxAdjacentStepWitnessColumnCount] at hcolumn ⊢
    omega
  rw [List.getI_eq_getElem _ (by simpa using hflatIndex)]
  simp [compactParserSyntaxAdjacentStepWitnessTableValues,
    hdivision, hremainder]

def CompactParserSyntaxAdjacentStepRowFits
    (tableWidth : Nat) (row : CompactParserSyntaxAdjacentStepRow) : Prop :=
  ∀ column < compactParserSyntaxAdjacentStepWitnessColumnCount,
    Nat.size ((compactParserSyntaxAdjacentStepRowValues row).getI column) ≤
      tableWidth

def CompactParserSyntaxAdjacentStepRowsFit
    (tableWidth : Nat)
    (rows : List CompactParserSyntaxAdjacentStepRow) : Prop :=
  ∀ row ∈ rows, CompactParserSyntaxAdjacentStepRowFits tableWidth row

def compactParserSyntaxAdjacentStepDynamicWidth
    (rows : List CompactParserSyntaxAdjacentStepRow) : Nat :=
  ((rows.flatMap compactParserSyntaxAdjacentStepRowValues).map Nat.size).sum

theorem CompactParserSyntaxAdjacentStepRowFits.value_size_le
    {tableWidth : Nat} {row : CompactParserSyntaxAdjacentStepRow}
    (hfit : CompactParserSyntaxAdjacentStepRowFits tableWidth row)
    {value : Nat}
    (hvalue : value ∈ compactParserSyntaxAdjacentStepRowValues row) :
    Nat.size value ≤ tableWidth := by
  rcases List.getElem_of_mem hvalue with ⟨column, hcolumn, rfl⟩
  have hcolumn' : column < compactParserSyntaxAdjacentStepWitnessColumnCount := by
    simpa using hcolumn
  simpa [List.getI_eq_getElem _ hcolumn] using hfit column hcolumn'

theorem compactParserSyntaxAdjacentStepRowsFit_dynamic
    (rows : List CompactParserSyntaxAdjacentStepRow) :
    CompactParserSyntaxAdjacentStepRowsFit
      (compactParserSyntaxAdjacentStepDynamicWidth rows) rows := by
  intro row hrow column hcolumn
  have hindex : column <
      (compactParserSyntaxAdjacentStepRowValues row).length := by
    simpa using hcolumn
  let value := (compactParserSyntaxAdjacentStepRowValues row).getI column
  have hvalueMem :
      value ∈ rows.flatMap compactParserSyntaxAdjacentStepRowValues := by
    apply List.mem_flatMap.mpr
    refine ⟨row, hrow, ?_⟩
    rw [show value =
      (compactParserSyntaxAdjacentStepRowValues row).getI column by rfl,
      List.getI_eq_getElem _ hindex]
    exact List.getElem_mem hindex
  have hsizeMem : Nat.size value ∈
      (rows.flatMap compactParserSyntaxAdjacentStepRowValues).map Nat.size := by
    exact List.mem_map.mpr ⟨_, hvalueMem, rfl⟩
  simpa [compactParserSyntaxAdjacentStepDynamicWidth, value] using
    List.single_le_sum (by simp) _ hsizeMem

theorem compactParserSyntaxAdjacentStepWitnessTableValues_size_le
    {tableWidth : Nat} {rows : List CompactParserSyntaxAdjacentStepRow}
    (hfit : CompactParserSyntaxAdjacentStepRowsFit tableWidth rows) :
    ∀ value ∈ compactParserSyntaxAdjacentStepWitnessTableValues rows,
      Nat.size value ≤ tableWidth := by
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨flatIndex, hflatIndex, rfl⟩
  have hflatBound : flatIndex <
      rows.length * compactParserSyntaxAdjacentStepWitnessColumnCount :=
    List.mem_range.mp hflatIndex
  have hcolumn : flatIndex % compactParserSyntaxAdjacentStepWitnessColumnCount <
      compactParserSyntaxAdjacentStepWitnessColumnCount :=
    Nat.mod_lt _ (by simp [compactParserSyntaxAdjacentStepWitnessColumnCount])
  have hrowIndex : flatIndex / compactParserSyntaxAdjacentStepWitnessColumnCount <
      rows.length := by
    rw [compactParserSyntaxAdjacentStepWitnessColumnCount] at hflatBound ⊢
    omega
  apply hfit
    (rows.getI (flatIndex / compactParserSyntaxAdjacentStepWitnessColumnCount))
  · rw [List.getI_eq_getElem _ hrowIndex]
    exact List.getElem_mem hrowIndex
  · exact hcolumn

def compactParserSyntaxAdjacentStepWitnessTableCode
    (tableWidth : Nat) (rows : List CompactParserSyntaxAdjacentStepRow) : Nat :=
  compactFixedWidthTableCode tableWidth
    (compactParserSyntaxAdjacentStepWitnessTableValues rows)

def CompactParserSyntaxAdjacentStepWitnessTableCarriesRows
    (tableWidth table : Nat)
    (rows : List CompactParserSyntaxAdjacentStepRow) : Prop :=
  ∀ rowIndex < rows.length,
    ∀ column < compactParserSyntaxAdjacentStepWitnessColumnCount,
      CompactFixedWidthEntry table tableWidth
        (rowIndex * compactParserSyntaxAdjacentStepWitnessColumnCount + column)
        ((compactParserSyntaxAdjacentStepRowValues
          (rows.getI rowIndex)).getI column)

theorem compactParserSyntaxAdjacentStepWitnessTableCode_carriesRows
    {tableWidth : Nat} {rows : List CompactParserSyntaxAdjacentStepRow}
    (hfit : CompactParserSyntaxAdjacentStepRowsFit tableWidth rows) :
    CompactParserSyntaxAdjacentStepWitnessTableCarriesRows tableWidth
      (compactParserSyntaxAdjacentStepWitnessTableCode tableWidth rows) rows := by
  intro rowIndex hrowIndex column hcolumn
  have hflatIndex :
      rowIndex * compactParserSyntaxAdjacentStepWitnessColumnCount + column <
        (compactParserSyntaxAdjacentStepWitnessTableValues rows).length := by
    simp only [compactParserSyntaxAdjacentStepWitnessTableValues_length]
    rw [compactParserSyntaxAdjacentStepWitnessColumnCount] at hcolumn ⊢
    omega
  have hentry := compactFixedWidthTableCode_entry tableWidth
    (compactParserSyntaxAdjacentStepWitnessTableValues rows)
    (rowIndex * compactParserSyntaxAdjacentStepWitnessColumnCount + column)
    hflatIndex
    (compactParserSyntaxAdjacentStepWitnessTableValues_size_le hfit)
  rw [compactParserSyntaxAdjacentStepWitnessTableValues_getI
    rows rowIndex column hrowIndex hcolumn] at hentry
  exact hentry

theorem compactParserSyntaxAdjacentStepWitnessTableCode_size_le
    (tableWidth : Nat) (rows : List CompactParserSyntaxAdjacentStepRow) :
    Nat.size (compactParserSyntaxAdjacentStepWitnessTableCode tableWidth rows) ≤
      rows.length * compactParserSyntaxAdjacentStepWitnessColumnCount *
        tableWidth := by
  simpa [compactParserSyntaxAdjacentStepWitnessTableCode] using
    compactFixedWidthTableCode_size_le tableWidth
      (compactParserSyntaxAdjacentStepWitnessTableValues rows)

def compactParserSyntaxAdjacentStepFormulaEnvironmentFromColumns
    (tokenTable width tokenCount stateBoundary stateCount rowIndex : Nat)
    (columnValue : Nat → Nat) (coordinate : Fin 33) : Nat :=
  if hglobal : coordinate.val < 6 then
    (![tokenTable, width, tokenCount, stateBoundary, stateCount, rowIndex] :
      Fin 6 → Nat) ⟨coordinate.val, hglobal⟩
  else columnValue (coordinate.val - 6)

def compactParserSyntaxAdjacentStepRowFormulaEnvironment
    (tokenTable width tokenCount stateBoundary stateCount rowIndex : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) : Fin 33 → Nat :=
  compactParserSyntaxAdjacentStepFormulaEnvironmentFromColumns
    tokenTable width tokenCount stateBoundary stateCount rowIndex fun column =>
      (compactParserSyntaxAdjacentStepRowValues row).getI column

@[simp] theorem compactParserSyntaxAdjacentStepRowFormulaEnvironment_spec
    (tokenTable width tokenCount stateBoundary stateCount rowIndex : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) :
    compactParserSyntaxAdjacentStepRowDef.val.Evalb
        (compactParserSyntaxAdjacentStepRowFormulaEnvironment
          tokenTable width tokenCount stateBoundary stateCount rowIndex row) ↔
      CompactParserSyntaxAdjacentStepRowGraph
        tokenTable width tokenCount stateBoundary stateCount rowIndex row := by
  have henv : compactParserSyntaxAdjacentStepRowFormulaEnvironment
          tokenTable width tokenCount stateBoundary stateCount rowIndex row =
      compactParserSyntaxAdjacentStepRowEnvironment
        tokenTable width tokenCount stateBoundary stateCount rowIndex row := by
    funext coordinate
    fin_cases coordinate <;> rfl
  rw [henv]
  exact compactParserSyntaxAdjacentStepRowDef_spec
    tokenTable width tokenCount stateBoundary stateCount rowIndex row

def compactParserSyntaxAdjacentStepWitnessTableColumnValue
    (tableWidth table rowIndex column : Nat) : Nat :=
  compactFixedWidthTableValue table tableWidth
    (rowIndex * compactParserSyntaxAdjacentStepWitnessColumnCount + column)

def compactParserSyntaxAdjacentStepWitnessTableFormulaEnvironment
    (tokenTable width tokenCount stateBoundary stateCount tableWidth table
      rowIndex : Nat) : Fin 33 → Nat :=
  compactParserSyntaxAdjacentStepFormulaEnvironmentFromColumns
    tokenTable width tokenCount stateBoundary stateCount rowIndex fun column =>
      compactParserSyntaxAdjacentStepWitnessTableColumnValue
        tableWidth table rowIndex column

def CompactParserSyntaxAdjacentStepWitnessTableGraph
    (tokenTable width tokenCount stateBoundary stateCount tableWidth table
      rowCount : Nat) : Prop :=
  ∀ rowIndex < rowCount,
    compactParserSyntaxAdjacentStepRowDef.val.Evalb
      (compactParserSyntaxAdjacentStepWitnessTableFormulaEnvironment
        tokenTable width tokenCount stateBoundary stateCount tableWidth table
          rowIndex)

def CompactParserSyntaxAdjacentStepRowsValid
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rows : List CompactParserSyntaxAdjacentStepRow) : Prop :=
  ∀ rowIndex < rows.length,
    CompactParserSyntaxAdjacentStepRowGraph
      tokenTable width tokenCount stateBoundary stateCount rowIndex
        (rows.getI rowIndex)

theorem compactParserSyntaxAdjacentStepWitnessTableColumnValue_eq
    {tableWidth table : Nat} {rows : List CompactParserSyntaxAdjacentStepRow}
    (hrows : CompactParserSyntaxAdjacentStepWitnessTableCarriesRows
      tableWidth table rows)
    (rowIndex column : Nat) (hrowIndex : rowIndex < rows.length)
    (hcolumn : column < compactParserSyntaxAdjacentStepWitnessColumnCount) :
    compactParserSyntaxAdjacentStepWitnessTableColumnValue
        tableWidth table rowIndex column =
      (compactParserSyntaxAdjacentStepRowValues
        (rows.getI rowIndex)).getI column := by
  exact (CompactFixedWidthEntry.value_eq_tableValue
    (hrows rowIndex hrowIndex column hcolumn)).symm

theorem compactParserSyntaxAdjacentStepWitnessTableFormulaEnvironment_eq
    {tokenTable width tokenCount stateBoundary stateCount tableWidth table : Nat}
    {rows : List CompactParserSyntaxAdjacentStepRow}
    (hrows : CompactParserSyntaxAdjacentStepWitnessTableCarriesRows
      tableWidth table rows)
    (rowIndex : Nat) (hrowIndex : rowIndex < rows.length) :
    compactParserSyntaxAdjacentStepWitnessTableFormulaEnvironment
        tokenTable width tokenCount stateBoundary stateCount tableWidth table
          rowIndex =
      compactParserSyntaxAdjacentStepRowFormulaEnvironment
        tokenTable width tokenCount stateBoundary stateCount rowIndex
          (rows.getI rowIndex) := by
  have hcolumn (column : Nat)
      (hcolumn : column < compactParserSyntaxAdjacentStepWitnessColumnCount) :=
    compactParserSyntaxAdjacentStepWitnessTableColumnValue_eq
      hrows rowIndex column hrowIndex hcolumn
  funext coordinate
  by_cases hglobal : coordinate.val < 6
  · simp [compactParserSyntaxAdjacentStepWitnessTableFormulaEnvironment,
      compactParserSyntaxAdjacentStepRowFormulaEnvironment,
      compactParserSyntaxAdjacentStepFormulaEnvironmentFromColumns, hglobal]
  · simp only [
      compactParserSyntaxAdjacentStepWitnessTableFormulaEnvironment,
      compactParserSyntaxAdjacentStepRowFormulaEnvironment,
      compactParserSyntaxAdjacentStepFormulaEnvironmentFromColumns,
      hglobal, dite_false]
    apply hcolumn
    have hcoordinate := coordinate.isLt
    simp only [compactParserSyntaxAdjacentStepWitnessColumnCount]
    omega

theorem CompactParserSyntaxAdjacentStepWitnessTableCarriesRows.graph
    {tokenTable width tokenCount stateBoundary stateCount tableWidth table : Nat}
    {rows : List CompactParserSyntaxAdjacentStepRow}
    (hrows : CompactParserSyntaxAdjacentStepWitnessTableCarriesRows
      tableWidth table rows)
    (hvalid : CompactParserSyntaxAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary stateCount rows) :
    CompactParserSyntaxAdjacentStepWitnessTableGraph
      tokenTable width tokenCount stateBoundary stateCount tableWidth table
        rows.length := by
  intro rowIndex hrowIndex
  rw [compactParserSyntaxAdjacentStepWitnessTableFormulaEnvironment_eq
    hrows rowIndex hrowIndex]
  rw [compactParserSyntaxAdjacentStepRowFormulaEnvironment_spec]
  exact hvalid rowIndex hrowIndex

theorem compactParserSyntaxAdjacentStepWitnessTableCode_graph
    {tokenTable width tokenCount stateBoundary stateCount tableWidth : Nat}
    {rows : List CompactParserSyntaxAdjacentStepRow}
    (hfit : CompactParserSyntaxAdjacentStepRowsFit tableWidth rows)
    (hvalid : CompactParserSyntaxAdjacentStepRowsValid
      tokenTable width tokenCount stateBoundary stateCount rows) :
    CompactParserSyntaxAdjacentStepWitnessTableGraph
      tokenTable width tokenCount stateBoundary stateCount tableWidth
        (compactParserSyntaxAdjacentStepWitnessTableCode tableWidth rows)
        rows.length :=
  (compactParserSyntaxAdjacentStepWitnessTableCode_carriesRows hfit).graph
    hvalid

#print axioms compactParserSyntaxAdjacentStepWitnessTableValues_getI
#print axioms compactParserSyntaxAdjacentStepRowsFit_dynamic
#print axioms compactParserSyntaxAdjacentStepWitnessTableCode_carriesRows
#print axioms compactParserSyntaxAdjacentStepWitnessTableCode_size_le
#print axioms compactParserSyntaxAdjacentStepRowFormulaEnvironment_spec
#print axioms compactParserSyntaxAdjacentStepWitnessTableFormulaEnvironment_eq
#print axioms CompactParserSyntaxAdjacentStepWitnessTableCarriesRows.graph
#print axioms compactParserSyntaxAdjacentStepWitnessTableCode_graph

end FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
