import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepStateFormula

/-!
# Fixed-width witness table for binary-natural stream steps

Each row stores the ten coordinates of the current state, the ten coordinates
of the next state, and the twelve branch-witness coordinates.  The three token
table parameters remain global, so one row has exactly 32 columns.  A canonical
row-major fixed-width code supports exact random access and a direct bit-size
bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTable

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectBinaryNatStreamStepRows
open FoundationCompactNumericListedDirectBinaryNatStreamStepFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStateFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStepRealization
open FoundationCompactNumericListedDirectBinaryNatStreamStepStateFormula

def compactBinaryNatStreamStepWitnessColumnCount : Nat := 32

structure CompactBinaryNatStreamStepStateRow where
  currentCoordinates : CompactBinaryNatStreamRowCoordinates
  currentSize : CompactBinaryNatStreamStateCoreSizeWitness
  nextCoordinates : CompactBinaryNatStreamRowCoordinates
  nextSize : CompactBinaryNatStreamStateCoreSizeWitness
  witness : CompactBinaryNatStreamStepWitnessCoordinates

instance : Inhabited CompactBinaryNatStreamStepStateRow where
  default :=
    { currentCoordinates :=
        { start := 0
          finish := 0
          bitsFinish := 0
          decodedFinish := 0
          bitsBoundary := 0
          bitsCount := 0
          decodedBoundary := 0
          decodedCount := 0 }
      currentSize :=
        { bitsBoundarySize := 0
          decodedBoundarySize := 0 }
      nextCoordinates :=
        { start := 0
          finish := 0
          bitsFinish := 0
          decodedFinish := 0
          bitsBoundary := 0
          bitsCount := 0
          decodedBoundary := 0
          decodedCount := 0 }
      nextSize :=
        { bitsBoundarySize := 0
          decodedBoundarySize := 0 }
      witness :=
        { branch := 0
          payload := 0
          digitCount := 0
          token := 0
          consumed := 0
          sourceOutputStart := 0
          sourceOutputBoundary := 0
          sourceOutputBoundarySize := 0
          targetOutputStart := 0
          targetOutputBoundary := 0
          targetOutputBoundarySize := 0
          outputCount := 0 } }

def compactBinaryNatStreamStepStateRowValues
    (row : CompactBinaryNatStreamStepStateRow) : List Nat :=
  [row.currentCoordinates.start,
    row.currentCoordinates.finish,
    row.currentCoordinates.bitsFinish,
    row.currentCoordinates.decodedFinish,
    row.currentCoordinates.bitsBoundary,
    row.currentCoordinates.bitsCount,
    row.currentCoordinates.decodedBoundary,
    row.currentCoordinates.decodedCount,
    row.currentSize.bitsBoundarySize,
    row.currentSize.decodedBoundarySize,
    row.nextCoordinates.start,
    row.nextCoordinates.finish,
    row.nextCoordinates.bitsFinish,
    row.nextCoordinates.decodedFinish,
    row.nextCoordinates.bitsBoundary,
    row.nextCoordinates.bitsCount,
    row.nextCoordinates.decodedBoundary,
    row.nextCoordinates.decodedCount,
    row.nextSize.bitsBoundarySize,
    row.nextSize.decodedBoundarySize,
    row.witness.branch,
    row.witness.payload,
    row.witness.digitCount,
    row.witness.token,
    row.witness.consumed,
    row.witness.sourceOutputStart,
    row.witness.sourceOutputBoundary,
    row.witness.sourceOutputBoundarySize,
    row.witness.targetOutputStart,
    row.witness.targetOutputBoundary,
    row.witness.targetOutputBoundarySize,
    row.witness.outputCount]

@[simp] theorem compactBinaryNatStreamStepStateRowValues_length
    (row : CompactBinaryNatStreamStepStateRow) :
    (compactBinaryNatStreamStepStateRowValues row).length =
      compactBinaryNatStreamStepWitnessColumnCount := by
  simp [compactBinaryNatStreamStepStateRowValues,
    compactBinaryNatStreamStepWitnessColumnCount]

def compactBinaryNatStreamStepWitnessTableValues
    (rows : List CompactBinaryNatStreamStepStateRow) : List Nat :=
  (List.range
      (rows.length * compactBinaryNatStreamStepWitnessColumnCount)).map
    fun flatIndex =>
      (compactBinaryNatStreamStepStateRowValues
        (rows.getI
          (flatIndex / compactBinaryNatStreamStepWitnessColumnCount))).getI
        (flatIndex % compactBinaryNatStreamStepWitnessColumnCount)

@[simp] theorem compactBinaryNatStreamStepWitnessTableValues_length
    (rows : List CompactBinaryNatStreamStepStateRow) :
    (compactBinaryNatStreamStepWitnessTableValues rows).length =
      rows.length * compactBinaryNatStreamStepWitnessColumnCount := by
  simp [compactBinaryNatStreamStepWitnessTableValues]

theorem compactBinaryNatStreamStepWitnessTableValues_getI
    (rows : List CompactBinaryNatStreamStepStateRow)
    (rowIndex column : Nat) (hrowIndex : rowIndex < rows.length)
    (hcolumn : column < compactBinaryNatStreamStepWitnessColumnCount) :
    (compactBinaryNatStreamStepWitnessTableValues rows).getI
        (rowIndex * compactBinaryNatStreamStepWitnessColumnCount + column) =
      (compactBinaryNatStreamStepStateRowValues
        (rows.getI rowIndex)).getI column := by
  have hflatIndex :
      rowIndex * compactBinaryNatStreamStepWitnessColumnCount + column <
        rows.length * compactBinaryNatStreamStepWitnessColumnCount := by
    rw [compactBinaryNatStreamStepWitnessColumnCount] at hcolumn ⊢
    omega
  have hdivision :
      (rowIndex * compactBinaryNatStreamStepWitnessColumnCount + column) /
          compactBinaryNatStreamStepWitnessColumnCount = rowIndex := by
    rw [compactBinaryNatStreamStepWitnessColumnCount] at hcolumn ⊢
    omega
  have hremainder :
      (rowIndex * compactBinaryNatStreamStepWitnessColumnCount + column) %
          compactBinaryNatStreamStepWitnessColumnCount = column := by
    rw [compactBinaryNatStreamStepWitnessColumnCount] at hcolumn ⊢
    omega
  rw [List.getI_eq_getElem _ (by simpa using hflatIndex)]
  simp [compactBinaryNatStreamStepWitnessTableValues,
    hdivision, hremainder]

def CompactBinaryNatStreamStepStateRowFits
    (tableWidth : Nat) (row : CompactBinaryNatStreamStepStateRow) : Prop :=
  ∀ column < compactBinaryNatStreamStepWitnessColumnCount,
    Nat.size ((compactBinaryNatStreamStepStateRowValues row).getI column) ≤
      tableWidth

def CompactBinaryNatStreamStepStateRowsFit
    (tableWidth : Nat) (rows : List CompactBinaryNatStreamStepStateRow) : Prop :=
  ∀ row ∈ rows, CompactBinaryNatStreamStepStateRowFits tableWidth row

theorem compactBinaryNatStreamStepWitnessTableValues_size_le
    {tableWidth : Nat} {rows : List CompactBinaryNatStreamStepStateRow}
    (hfit : CompactBinaryNatStreamStepStateRowsFit tableWidth rows) :
    ∀ value ∈ compactBinaryNatStreamStepWitnessTableValues rows,
      Nat.size value ≤ tableWidth := by
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨flatIndex, hflatIndex, rfl⟩
  have hflatBound :
      flatIndex < rows.length * compactBinaryNatStreamStepWitnessColumnCount :=
    List.mem_range.mp hflatIndex
  have hcolumn : flatIndex % compactBinaryNatStreamStepWitnessColumnCount <
      compactBinaryNatStreamStepWitnessColumnCount := by
    exact Nat.mod_lt _ (by
      simp [compactBinaryNatStreamStepWitnessColumnCount])
  have hrowIndex : flatIndex / compactBinaryNatStreamStepWitnessColumnCount <
      rows.length := by
    rw [compactBinaryNatStreamStepWitnessColumnCount] at hflatBound ⊢
    omega
  apply hfit (rows.getI
    (flatIndex / compactBinaryNatStreamStepWitnessColumnCount))
  · rw [List.getI_eq_getElem _ hrowIndex]
    exact List.getElem_mem hrowIndex
  · exact hcolumn

def compactBinaryNatStreamStepWitnessTableCode
    (tableWidth : Nat) (rows : List CompactBinaryNatStreamStepStateRow) : Nat :=
  compactFixedWidthTableCode tableWidth
    (compactBinaryNatStreamStepWitnessTableValues rows)

def CompactBinaryNatStreamStepWitnessTableCarriesRows
    (tableWidth table : Nat)
    (rows : List CompactBinaryNatStreamStepStateRow) : Prop :=
  ∀ rowIndex < rows.length,
    ∀ column < compactBinaryNatStreamStepWitnessColumnCount,
      CompactFixedWidthEntry table tableWidth
        (rowIndex * compactBinaryNatStreamStepWitnessColumnCount + column)
        ((compactBinaryNatStreamStepStateRowValues
          (rows.getI rowIndex)).getI column)

theorem compactBinaryNatStreamStepWitnessTableCode_carriesRows
    {tableWidth : Nat} {rows : List CompactBinaryNatStreamStepStateRow}
    (hfit : CompactBinaryNatStreamStepStateRowsFit tableWidth rows) :
    CompactBinaryNatStreamStepWitnessTableCarriesRows tableWidth
      (compactBinaryNatStreamStepWitnessTableCode tableWidth rows) rows := by
  intro rowIndex hrowIndex column hcolumn
  have hflatIndex :
      rowIndex * compactBinaryNatStreamStepWitnessColumnCount + column <
        (compactBinaryNatStreamStepWitnessTableValues rows).length := by
    simp only [compactBinaryNatStreamStepWitnessTableValues_length]
    rw [compactBinaryNatStreamStepWitnessColumnCount] at hcolumn ⊢
    omega
  have hentry := compactFixedWidthTableCode_entry tableWidth
    (compactBinaryNatStreamStepWitnessTableValues rows)
    (rowIndex * compactBinaryNatStreamStepWitnessColumnCount + column)
    hflatIndex
    (compactBinaryNatStreamStepWitnessTableValues_size_le hfit)
  rw [compactBinaryNatStreamStepWitnessTableValues_getI
    rows rowIndex column hrowIndex hcolumn] at hentry
  exact hentry

theorem compactBinaryNatStreamStepWitnessTableCode_size_le
    (tableWidth : Nat) (rows : List CompactBinaryNatStreamStepStateRow) :
    Nat.size (compactBinaryNatStreamStepWitnessTableCode tableWidth rows) ≤
      rows.length * compactBinaryNatStreamStepWitnessColumnCount *
        tableWidth := by
  simpa [compactBinaryNatStreamStepWitnessTableCode] using
    compactFixedWidthTableCode_size_le tableWidth
      (compactBinaryNatStreamStepWitnessTableValues rows)

def compactBinaryNatStreamStepFormulaEnvironmentFromColumns
    (tokenTable width tokenCount : Nat) (columnValue : Nat → Nat)
    (coordinate : Fin 35) : Nat :=
  if coordinate.val = 0 then tokenTable
  else if coordinate.val = 1 then width
  else if coordinate.val = 2 then tokenCount
  else columnValue (coordinate.val - 3)

def compactBinaryNatStreamStepStateRowFormulaEnvironment
    (tokenTable width tokenCount : Nat)
    (row : CompactBinaryNatStreamStepStateRow) : Fin 35 → Nat :=
  compactBinaryNatStreamStepFormulaEnvironmentFromColumns
    tokenTable width tokenCount fun column =>
      (compactBinaryNatStreamStepStateRowValues row).getI column

@[simp] theorem compactBinaryNatStreamStepStateRowFormulaEnvironment_spec
    (tokenTable width tokenCount : Nat)
    (row : CompactBinaryNatStreamStepStateRow) :
    compactBinaryNatStreamStepStateGraphDef.val.Evalb
        (compactBinaryNatStreamStepStateRowFormulaEnvironment
          tokenTable width tokenCount row) ↔
      CompactBinaryNatStreamStepStateGraph tokenTable width tokenCount
        row.currentCoordinates row.nextCoordinates
        row.currentSize row.nextSize row.witness := by
  have henv : compactBinaryNatStreamStepStateRowFormulaEnvironment
      tokenTable width tokenCount row =
    compactBinaryNatStreamStepStateFormulaEnvironment
    tokenTable width tokenCount
    row.currentCoordinates.start row.currentCoordinates.finish
    row.currentCoordinates.bitsFinish row.currentCoordinates.decodedFinish
    row.currentCoordinates.bitsBoundary row.currentCoordinates.bitsCount
    row.currentCoordinates.decodedBoundary row.currentCoordinates.decodedCount
    row.currentSize.bitsBoundarySize row.currentSize.decodedBoundarySize
    row.nextCoordinates.start row.nextCoordinates.finish
    row.nextCoordinates.bitsFinish row.nextCoordinates.decodedFinish
    row.nextCoordinates.bitsBoundary row.nextCoordinates.bitsCount
    row.nextCoordinates.decodedBoundary row.nextCoordinates.decodedCount
    row.nextSize.bitsBoundarySize row.nextSize.decodedBoundarySize
    row.witness.branch row.witness.payload row.witness.digitCount
    row.witness.token row.witness.consumed
    row.witness.sourceOutputStart row.witness.sourceOutputBoundary
    row.witness.sourceOutputBoundarySize
    row.witness.targetOutputStart row.witness.targetOutputBoundary
    row.witness.targetOutputBoundarySize row.witness.outputCount := by
    funext coordinate
    fin_cases coordinate <;>
      rfl
  rw [henv]
  exact compactBinaryNatStreamStepStateGraphDef_spec
    tokenTable width tokenCount
    row.currentCoordinates.start row.currentCoordinates.finish
    row.currentCoordinates.bitsFinish row.currentCoordinates.decodedFinish
    row.currentCoordinates.bitsBoundary row.currentCoordinates.bitsCount
    row.currentCoordinates.decodedBoundary row.currentCoordinates.decodedCount
    row.currentSize.bitsBoundarySize row.currentSize.decodedBoundarySize
    row.nextCoordinates.start row.nextCoordinates.finish
    row.nextCoordinates.bitsFinish row.nextCoordinates.decodedFinish
    row.nextCoordinates.bitsBoundary row.nextCoordinates.bitsCount
    row.nextCoordinates.decodedBoundary row.nextCoordinates.decodedCount
    row.nextSize.bitsBoundarySize row.nextSize.decodedBoundarySize
    row.witness.branch row.witness.payload row.witness.digitCount
    row.witness.token row.witness.consumed
    row.witness.sourceOutputStart row.witness.sourceOutputBoundary
    row.witness.sourceOutputBoundarySize
    row.witness.targetOutputStart row.witness.targetOutputBoundary
    row.witness.targetOutputBoundarySize row.witness.outputCount

def compactBinaryNatStreamStepWitnessTableColumnValue
    (tableWidth table rowIndex column : Nat) : Nat :=
  compactFixedWidthTableValue table tableWidth
    (rowIndex * compactBinaryNatStreamStepWitnessColumnCount + column)

def compactBinaryNatStreamStepWitnessTableFormulaEnvironment
    (tokenTable width tokenCount tableWidth table rowIndex : Nat) :
    Fin 35 → Nat :=
  compactBinaryNatStreamStepFormulaEnvironmentFromColumns
    tokenTable width tokenCount fun column =>
      compactBinaryNatStreamStepWitnessTableColumnValue
        tableWidth table rowIndex column

def CompactBinaryNatStreamStepWitnessTableGraph
    (tokenTable width tokenCount tableWidth table rowCount : Nat) : Prop :=
  ∀ rowIndex < rowCount,
    compactBinaryNatStreamStepStateGraphDef.val.Evalb
      (compactBinaryNatStreamStepWitnessTableFormulaEnvironment
        tokenTable width tokenCount tableWidth table rowIndex)

def CompactBinaryNatStreamStepStateRowsValid
    (tokenTable width tokenCount : Nat)
    (rows : List CompactBinaryNatStreamStepStateRow) : Prop :=
  ∀ row ∈ rows,
    CompactBinaryNatStreamStepStateGraph tokenTable width tokenCount
      row.currentCoordinates row.nextCoordinates
      row.currentSize row.nextSize row.witness

theorem compactBinaryNatStreamStepWitnessTableColumnValue_eq
    {tableWidth table : Nat}
    {rows : List CompactBinaryNatStreamStepStateRow}
    (hrows : CompactBinaryNatStreamStepWitnessTableCarriesRows
      tableWidth table rows)
    (rowIndex column : Nat) (hrowIndex : rowIndex < rows.length)
    (hcolumn : column < compactBinaryNatStreamStepWitnessColumnCount) :
    compactBinaryNatStreamStepWitnessTableColumnValue
        tableWidth table rowIndex column =
      (compactBinaryNatStreamStepStateRowValues
        (rows.getI rowIndex)).getI column := by
  exact (CompactFixedWidthEntry.value_eq_tableValue
    (hrows rowIndex hrowIndex column hcolumn)).symm

theorem compactBinaryNatStreamStepWitnessTableFormulaEnvironment_eq
    {tokenTable width tokenCount tableWidth table : Nat}
    {rows : List CompactBinaryNatStreamStepStateRow}
    (hrows : CompactBinaryNatStreamStepWitnessTableCarriesRows
      tableWidth table rows)
    (rowIndex : Nat) (hrowIndex : rowIndex < rows.length) :
    compactBinaryNatStreamStepWitnessTableFormulaEnvironment
        tokenTable width tokenCount tableWidth table rowIndex =
      compactBinaryNatStreamStepStateRowFormulaEnvironment
        tokenTable width tokenCount (rows.getI rowIndex) := by
  have hcolumn (column : Nat)
      (hcolumn : column < compactBinaryNatStreamStepWitnessColumnCount) :=
    compactBinaryNatStreamStepWitnessTableColumnValue_eq
      hrows rowIndex column hrowIndex hcolumn
  funext coordinate
  by_cases hzero : coordinate.val = 0
  · simp [compactBinaryNatStreamStepWitnessTableFormulaEnvironment,
      compactBinaryNatStreamStepStateRowFormulaEnvironment,
      compactBinaryNatStreamStepFormulaEnvironmentFromColumns, hzero]
  by_cases hone : coordinate.val = 1
  · simp [compactBinaryNatStreamStepWitnessTableFormulaEnvironment,
      compactBinaryNatStreamStepStateRowFormulaEnvironment,
      compactBinaryNatStreamStepFormulaEnvironmentFromColumns,
      hone]
  by_cases htwo : coordinate.val = 2
  · simp [compactBinaryNatStreamStepWitnessTableFormulaEnvironment,
      compactBinaryNatStreamStepStateRowFormulaEnvironment,
      compactBinaryNatStreamStepFormulaEnvironmentFromColumns,
      htwo]
  simp only [compactBinaryNatStreamStepWitnessTableFormulaEnvironment,
    compactBinaryNatStreamStepStateRowFormulaEnvironment,
    compactBinaryNatStreamStepFormulaEnvironmentFromColumns,
    hzero, hone, htwo, if_false]
  apply hcolumn
  have hcoordinate := coordinate.isLt
  simp only [compactBinaryNatStreamStepWitnessColumnCount]
  omega

theorem CompactBinaryNatStreamStepWitnessTableCarriesRows.graph
    {tokenTable width tokenCount tableWidth table : Nat}
    {rows : List CompactBinaryNatStreamStepStateRow}
    (hrows : CompactBinaryNatStreamStepWitnessTableCarriesRows
      tableWidth table rows)
    (hvalid : CompactBinaryNatStreamStepStateRowsValid
      tokenTable width tokenCount rows) :
    CompactBinaryNatStreamStepWitnessTableGraph
      tokenTable width tokenCount tableWidth table rows.length := by
  intro rowIndex hrowIndex
  rw [compactBinaryNatStreamStepWitnessTableFormulaEnvironment_eq
    hrows rowIndex hrowIndex]
  rw [compactBinaryNatStreamStepStateRowFormulaEnvironment_spec]
  apply hvalid (rows.getI rowIndex)
  rw [List.getI_eq_getElem _ hrowIndex]
  exact List.getElem_mem hrowIndex

theorem compactBinaryNatStreamStepWitnessTableCode_graph
    {tokenTable width tokenCount tableWidth : Nat}
    {rows : List CompactBinaryNatStreamStepStateRow}
    (hfit : CompactBinaryNatStreamStepStateRowsFit tableWidth rows)
    (hvalid : CompactBinaryNatStreamStepStateRowsValid
      tokenTable width tokenCount rows) :
    CompactBinaryNatStreamStepWitnessTableGraph
      tokenTable width tokenCount tableWidth
        (compactBinaryNatStreamStepWitnessTableCode tableWidth rows)
        rows.length :=
  (compactBinaryNatStreamStepWitnessTableCode_carriesRows hfit).graph hvalid

#print axioms compactBinaryNatStreamStepWitnessTableValues_getI
#print axioms compactBinaryNatStreamStepWitnessTableCode_carriesRows
#print axioms compactBinaryNatStreamStepWitnessTableCode_size_le
#print axioms compactBinaryNatStreamStepStateRowFormulaEnvironment_spec
#print axioms compactBinaryNatStreamStepWitnessTableFormulaEnvironment_eq
#print axioms CompactBinaryNatStreamStepWitnessTableCarriesRows.graph
#print axioms compactBinaryNatStreamStepWitnessTableCode_graph

end FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTable
