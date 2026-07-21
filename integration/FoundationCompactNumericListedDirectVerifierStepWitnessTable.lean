import integration.FoundationCompactNumericListedDirectVerifierStepCompleteness
import integration.FoundationCompactNumericListedDirectTokenStreamInverse

/-!
# Fixed-width witness table for complete verifier-step witnesses

Every row is the environment of one complete verifier-step witness.  The
environment contributes all 429 columns; witness formulas are supplied by
the row-validity predicate so rows remain independent of step parameters.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStepWitnessTable

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierStepFormula

def compactNumericVerifierStepWitnessColumnCount : Nat := 429

structure CompactNumericVerifierStepFormulaRow where
  environment : Fin 429 → Nat

instance : Inhabited CompactNumericVerifierStepFormulaRow where
  default := { environment := fun _ => 0 }

def CompactNumericVerifierStepFormulaRow.ofWitness
    {stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish : Nat}
    (witness : CompactNumericVerifierStepFormulaWitness
      stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish) :
    CompactNumericVerifierStepFormulaRow :=
  { environment := witness.environment }

def compactNumericVerifierStepFormulaRowValues
    (row : CompactNumericVerifierStepFormulaRow) : List Nat :=
  List.ofFn row.environment

@[simp] theorem compactNumericVerifierStepFormulaRowValues_length
    (row : CompactNumericVerifierStepFormulaRow) :
    (compactNumericVerifierStepFormulaRowValues row).length =
      compactNumericVerifierStepWitnessColumnCount := by
  change (List.ofFn row.environment).length = 429
  simp only [List.length_ofFn]

theorem compactNumericVerifierStepFormulaRowValues_getI
    (row : CompactNumericVerifierStepFormulaRow)
    (column : Nat) (hcolumn : column < compactNumericVerifierStepWitnessColumnCount) :
    (compactNumericVerifierStepFormulaRowValues row).getI column =
      row.environment ⟨column, by
        simpa [compactNumericVerifierStepWitnessColumnCount] using hcolumn⟩ := by
  have hindex : column <
      (compactNumericVerifierStepFormulaRowValues row).length := by
    rw [compactNumericVerifierStepFormulaRowValues_length]
    exact hcolumn
  rw [List.getI_eq_getElem _ hindex]
  simp only [compactNumericVerifierStepFormulaRowValues,
    List.getElem_ofFn]

def compactNumericVerifierStepWitnessTableValues
    (rows : List CompactNumericVerifierStepFormulaRow) : List Nat :=
  (List.range
      (rows.length * compactNumericVerifierStepWitnessColumnCount)).map
    fun flatIndex =>
      (compactNumericVerifierStepFormulaRowValues
        (rows.getI
          (flatIndex / compactNumericVerifierStepWitnessColumnCount))).getI
        (flatIndex % compactNumericVerifierStepWitnessColumnCount)

@[simp] theorem compactNumericVerifierStepWitnessTableValues_length
    (rows : List CompactNumericVerifierStepFormulaRow) :
    (compactNumericVerifierStepWitnessTableValues rows).length =
      rows.length * compactNumericVerifierStepWitnessColumnCount := by
  simp [compactNumericVerifierStepWitnessTableValues]

theorem compactNumericVerifierStepWitnessTableValues_getI
    (rows : List CompactNumericVerifierStepFormulaRow)
    (rowIndex column : Nat) (hrowIndex : rowIndex < rows.length)
    (hcolumn : column < compactNumericVerifierStepWitnessColumnCount) :
    (compactNumericVerifierStepWitnessTableValues rows).getI
        (rowIndex * compactNumericVerifierStepWitnessColumnCount + column) =
      (compactNumericVerifierStepFormulaRowValues
        (rows.getI rowIndex)).getI column := by
  have hflatIndex :
      rowIndex * compactNumericVerifierStepWitnessColumnCount + column <
        rows.length * compactNumericVerifierStepWitnessColumnCount := by
    rw [compactNumericVerifierStepWitnessColumnCount] at hcolumn ⊢
    omega
  have hdivision :
      (rowIndex * compactNumericVerifierStepWitnessColumnCount + column) /
          compactNumericVerifierStepWitnessColumnCount = rowIndex := by
    rw [compactNumericVerifierStepWitnessColumnCount] at hcolumn ⊢
    omega
  have hremainder :
      (rowIndex * compactNumericVerifierStepWitnessColumnCount + column) %
          compactNumericVerifierStepWitnessColumnCount = column := by
    rw [compactNumericVerifierStepWitnessColumnCount] at hcolumn ⊢
    omega
  rw [List.getI_eq_getElem _ (by simpa using hflatIndex)]
  simp [compactNumericVerifierStepWitnessTableValues,
    hdivision, hremainder]

def CompactNumericVerifierStepFormulaRowFits
    (tableWidth : Nat) (row : CompactNumericVerifierStepFormulaRow) : Prop :=
  ∀ column < compactNumericVerifierStepWitnessColumnCount,
    Nat.size ((compactNumericVerifierStepFormulaRowValues row).getI column) ≤
      tableWidth

def CompactNumericVerifierStepFormulaRowsFit
    (tableWidth : Nat) (rows : List CompactNumericVerifierStepFormulaRow) : Prop :=
  ∀ row ∈ rows, CompactNumericVerifierStepFormulaRowFits tableWidth row

theorem CompactNumericVerifierStepFormulaRowFits.value_size_le
    {tableWidth : Nat}
    {row : CompactNumericVerifierStepFormulaRow}
    (hfit : CompactNumericVerifierStepFormulaRowFits tableWidth row)
    {value : Nat}
    (hvalue : value ∈ compactNumericVerifierStepFormulaRowValues row) :
    Nat.size value ≤ tableWidth := by
  rcases List.getElem_of_mem hvalue with ⟨column, hcolumn, rfl⟩
  have hcolumn' : column < compactNumericVerifierStepWitnessColumnCount := by
    rw [compactNumericVerifierStepFormulaRowValues_length] at hcolumn
    exact hcolumn
  simpa [List.getI_eq_getElem _ hcolumn] using hfit column hcolumn'

def compactNumericVerifierStepFormulaDynamicWidth
    (rows : List CompactNumericVerifierStepFormulaRow) : Nat :=
  ((rows.flatMap compactNumericVerifierStepFormulaRowValues).map Nat.size).sum

theorem compactNumericVerifierStepFormulaRowsFit_dynamic
    (rows : List CompactNumericVerifierStepFormulaRow) :
    CompactNumericVerifierStepFormulaRowsFit
      (compactNumericVerifierStepFormulaDynamicWidth rows) rows := by
  intro row hrow column hcolumn
  have hindex : column <
      (compactNumericVerifierStepFormulaRowValues row).length := by
    rw [compactNumericVerifierStepFormulaRowValues_length]
    exact hcolumn
  let value := (compactNumericVerifierStepFormulaRowValues row).getI column
  have hvalueMem :
      value ∈ rows.flatMap compactNumericVerifierStepFormulaRowValues := by
    apply List.mem_flatMap.mpr
    refine ⟨row, hrow, ?_⟩
    rw [show value =
      (compactNumericVerifierStepFormulaRowValues row).getI column by rfl,
      List.getI_eq_getElem _ hindex]
    exact List.getElem_mem hindex
  have hsizeMem : Nat.size value ∈
      (rows.flatMap compactNumericVerifierStepFormulaRowValues).map Nat.size := by
    exact List.mem_map.mpr ⟨_, hvalueMem, rfl⟩
  simpa [compactNumericVerifierStepFormulaDynamicWidth, value] using
    List.single_le_sum (by simp) _ hsizeMem

theorem compactNumericVerifierStepWitnessTableValues_size_le
    {tableWidth : Nat}
    {rows : List CompactNumericVerifierStepFormulaRow}
    (hfit : CompactNumericVerifierStepFormulaRowsFit tableWidth rows) :
    ∀ value ∈ compactNumericVerifierStepWitnessTableValues rows,
      Nat.size value ≤ tableWidth := by
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨flatIndex, hflatIndex, rfl⟩
  have hflatBound : flatIndex <
      rows.length * compactNumericVerifierStepWitnessColumnCount :=
    List.mem_range.mp hflatIndex
  have hcolumn : flatIndex % compactNumericVerifierStepWitnessColumnCount <
      compactNumericVerifierStepWitnessColumnCount :=
    Nat.mod_lt _ (by simp [compactNumericVerifierStepWitnessColumnCount])
  have hrowIndex : flatIndex / compactNumericVerifierStepWitnessColumnCount <
      rows.length := by
    rw [compactNumericVerifierStepWitnessColumnCount] at hflatBound ⊢
    omega
  apply hfit
    (rows.getI (flatIndex / compactNumericVerifierStepWitnessColumnCount))
  · rw [List.getI_eq_getElem _ hrowIndex]
    exact List.getElem_mem hrowIndex
  · exact hcolumn

def compactNumericVerifierStepWitnessTableCode
    (tableWidth : Nat)
    (rows : List CompactNumericVerifierStepFormulaRow) : Nat :=
  compactFixedWidthTableCode tableWidth
    (compactNumericVerifierStepWitnessTableValues rows)

def CompactNumericVerifierStepWitnessTableCarriesRows
    (tableWidth table : Nat)
    (rows : List CompactNumericVerifierStepFormulaRow) : Prop :=
  ∀ rowIndex < rows.length,
    ∀ column < compactNumericVerifierStepWitnessColumnCount,
      CompactFixedWidthEntry table tableWidth
        (rowIndex * compactNumericVerifierStepWitnessColumnCount + column)
        ((compactNumericVerifierStepFormulaRowValues
          (rows.getI rowIndex)).getI column)

theorem compactNumericVerifierStepWitnessTableCode_carriesRows
    {tableWidth : Nat}
    {rows : List CompactNumericVerifierStepFormulaRow}
    (hfit : CompactNumericVerifierStepFormulaRowsFit tableWidth rows) :
    CompactNumericVerifierStepWitnessTableCarriesRows tableWidth
      (compactNumericVerifierStepWitnessTableCode tableWidth rows) rows := by
  intro rowIndex hrowIndex column hcolumn
  have hflatIndex :
      rowIndex * compactNumericVerifierStepWitnessColumnCount + column <
        (compactNumericVerifierStepWitnessTableValues rows).length := by
    simp only [compactNumericVerifierStepWitnessTableValues_length]
    rw [compactNumericVerifierStepWitnessColumnCount] at hcolumn ⊢
    omega
  have hentry := compactFixedWidthTableCode_entry tableWidth
    (compactNumericVerifierStepWitnessTableValues rows)
    (rowIndex * compactNumericVerifierStepWitnessColumnCount + column)
    hflatIndex
    (compactNumericVerifierStepWitnessTableValues_size_le hfit)
  rw [compactNumericVerifierStepWitnessTableValues_getI
    rows rowIndex column hrowIndex hcolumn] at hentry
  exact hentry

theorem compactNumericVerifierStepWitnessTableCode_size_le
    (tableWidth : Nat)
    (rows : List CompactNumericVerifierStepFormulaRow) :
    Nat.size (compactNumericVerifierStepWitnessTableCode tableWidth rows) ≤
      rows.length * compactNumericVerifierStepWitnessColumnCount * tableWidth := by
  simpa [compactNumericVerifierStepWitnessTableCode] using
    compactFixedWidthTableCode_size_le tableWidth
      (compactNumericVerifierStepWitnessTableValues rows)

def compactNumericVerifierStepWitnessTableColumnValue
    (tableWidth table rowIndex column : Nat) : Nat :=
  compactFixedWidthTableValue table tableWidth
    (rowIndex * compactNumericVerifierStepWitnessColumnCount + column)

def compactNumericVerifierStepFormulaRowEnvironment
    (row : CompactNumericVerifierStepFormulaRow) : Fin 429 → Nat :=
  row.environment

def compactNumericVerifierStepFormulaRowsValid
    (rows : List CompactNumericVerifierStepFormulaRow) : Prop :=
  ∀ row ∈ rows,
    compactNumericVerifierStepGraphDef.val.Evalb
      (compactNumericVerifierStepFormulaRowEnvironment row)

theorem compactNumericVerifierStepFormulaRow_ofWitness_formula
    {stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish : Nat}
    (witness : CompactNumericVerifierStepFormulaWitness
      stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish) :
    compactNumericVerifierStepGraphDef.val.Evalb
      (compactNumericVerifierStepFormulaRowEnvironment
        (CompactNumericVerifierStepFormulaRow.ofWitness witness)) := by
  exact witness.formula

def compactNumericVerifierStepWitnessTableFormulaEnvironment
    (tableWidth table rowIndex : Nat) : Fin 429 → Nat :=
  fun coordinate =>
    compactNumericVerifierStepWitnessTableColumnValue
      tableWidth table rowIndex coordinate.val

theorem compactNumericVerifierStepWitnessTableColumnValue_eq
    {tableWidth table : Nat}
    {rows : List CompactNumericVerifierStepFormulaRow}
    (hrows : CompactNumericVerifierStepWitnessTableCarriesRows
      tableWidth table rows)
    (rowIndex column : Nat) (hrowIndex : rowIndex < rows.length)
    (hcolumn : column < compactNumericVerifierStepWitnessColumnCount) :
    compactNumericVerifierStepWitnessTableColumnValue
        tableWidth table rowIndex column =
      (compactNumericVerifierStepFormulaRowValues
        (rows.getI rowIndex)).getI column := by
  exact (CompactFixedWidthEntry.value_eq_tableValue
    (hrows rowIndex hrowIndex column hcolumn)).symm

theorem compactNumericVerifierStepWitnessTableFormulaEnvironment_eq
    {tableWidth table : Nat}
    {rows : List CompactNumericVerifierStepFormulaRow}
    (hrows : CompactNumericVerifierStepWitnessTableCarriesRows
      tableWidth table rows)
    (rowIndex : Nat) (hrowIndex : rowIndex < rows.length) :
    compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex =
      compactNumericVerifierStepFormulaRowEnvironment
        (rows.getI rowIndex) := by
  have hcolumn (column : Nat)
      (hcolumn : column < compactNumericVerifierStepWitnessColumnCount) :=
    compactNumericVerifierStepWitnessTableColumnValue_eq
      hrows rowIndex column hrowIndex hcolumn
  funext coordinate
  change compactNumericVerifierStepWitnessTableColumnValue
      tableWidth table rowIndex coordinate.val =
    (rows.getI rowIndex).environment coordinate
  rw [hcolumn coordinate.val (by
    simpa [compactNumericVerifierStepWitnessColumnCount] using coordinate.isLt)]
  simpa using compactNumericVerifierStepFormulaRowValues_getI
    (rows.getI rowIndex) coordinate.val
    (by simpa [compactNumericVerifierStepWitnessColumnCount] using coordinate.isLt)

theorem compactNumericVerifierStepWitnessTableCarriesRows.formula
    {tableWidth table : Nat}
    {rows : List CompactNumericVerifierStepFormulaRow}
    (hrows : CompactNumericVerifierStepWitnessTableCarriesRows
      tableWidth table rows)
    (hvalid : compactNumericVerifierStepFormulaRowsValid rows)
    (rowIndex : Nat) (hrowIndex : rowIndex < rows.length) :
    compactNumericVerifierStepGraphDef.val.Evalb
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex) := by
  rw [compactNumericVerifierStepWitnessTableFormulaEnvironment_eq
    hrows rowIndex hrowIndex]
  apply hvalid (rows.getI rowIndex)
  rw [List.getI_eq_getElem _ hrowIndex]
  exact List.getElem_mem hrowIndex

theorem compactNumericVerifierStepWitnessTableCode_formula
    {tableWidth : Nat}
    {rows : List CompactNumericVerifierStepFormulaRow}
    (hfit : CompactNumericVerifierStepFormulaRowsFit tableWidth rows)
    (hvalid : compactNumericVerifierStepFormulaRowsValid rows)
    (rowIndex : Nat) (hrowIndex : rowIndex < rows.length) :
    compactNumericVerifierStepGraphDef.val.Evalb
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth (compactNumericVerifierStepWitnessTableCode tableWidth rows)
          rowIndex) := by
  exact compactNumericVerifierStepWitnessTableCarriesRows.formula
    (compactNumericVerifierStepWitnessTableCode_carriesRows hfit)
    hvalid
    rowIndex hrowIndex

theorem compactNumericVerifierStepWitnessTableCode_graph
    {tableWidth : Nat}
    {rows : List CompactNumericVerifierStepFormulaRow}
    (hfit : CompactNumericVerifierStepFormulaRowsFit tableWidth rows)
    (hvalid : compactNumericVerifierStepFormulaRowsValid rows) :
    ∀ rowIndex < rows.length,
      compactNumericVerifierStepGraphDef.val.Evalb
        (compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth (compactNumericVerifierStepWitnessTableCode tableWidth rows)
            rowIndex) := by
  intro rowIndex hrowIndex
  exact compactNumericVerifierStepWitnessTableCode_formula hfit hvalid
    rowIndex hrowIndex

#print axioms compactNumericVerifierStepFormulaRowValues_length
#print axioms compactNumericVerifierStepFormulaRowValues_getI
#print axioms compactNumericVerifierStepWitnessTableValues_getI
#print axioms compactNumericVerifierStepFormulaRowsFit_dynamic
#print axioms compactNumericVerifierStepWitnessTableCode_carriesRows
#print axioms compactNumericVerifierStepWitnessTableCode_size_le
#print axioms compactNumericVerifierStepFormulaRow_ofWitness_formula
#print axioms compactNumericVerifierStepWitnessTableFormulaEnvironment_eq
#print axioms compactNumericVerifierStepWitnessTableCarriesRows.formula
#print axioms compactNumericVerifierStepWitnessTableCode_formula
#print axioms compactNumericVerifierStepWitnessTableCode_graph

end FoundationCompactNumericListedDirectVerifierStepWitnessTable
