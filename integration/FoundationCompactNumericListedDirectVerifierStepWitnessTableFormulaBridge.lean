import integration.FoundationCompactNumericListedDirectVerifierStepWitnessTableAdjacencyFormula
import integration.FoundationCompactNumericListedDirectAtomicListRowRealization

/-!
# Semantic bridge for complete verifier-step witness tables

Fixed-width entry uniqueness identifies every boundedly quantified row value
with the corresponding decoded table column.  This prevents both the step
formula and the adjacency formula from choosing values unrelated to the
public witness table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAtomicListRowRealization
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableAdjacencyFormula

theorem compactNumericVerifierStepWitnessTableColumnValue_entry
    (tableWidth table rowIndex column : Nat) :
    CompactFixedWidthEntry table tableWidth
      (rowIndex * compactNumericVerifierStepWitnessColumnCount + column)
      (compactNumericVerifierStepWitnessTableColumnValue
        tableWidth table rowIndex column) := by
  simpa [compactNumericVerifierStepWitnessTableColumnValue] using
    compactFixedWidthTableValue_entry table tableWidth
      (rowIndex * compactNumericVerifierStepWitnessColumnCount + column)

theorem compactNumericVerifierStepWitnessTableColumnValue_le_pow
    (tableWidth table rowIndex column : Nat) :
    compactNumericVerifierStepWitnessTableColumnValue
        tableWidth table rowIndex column ≤ 2 ^ tableWidth := by
  apply Nat.le_of_lt
  apply Nat.size_le.mp
  simpa [compactNumericVerifierStepWitnessTableColumnValue] using
    compactFixedWidthTableValue_size_le table tableWidth
      (rowIndex * compactNumericVerifierStepWitnessColumnCount + column)

theorem CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue
    {tableWidth table rowIndex column value : Nat}
    (hentry : CompactFixedWidthEntry table tableWidth
      (rowIndex * compactNumericVerifierStepWitnessColumnCount + column)
      value) :
    value = compactNumericVerifierStepWitnessTableColumnValue
      tableWidth table rowIndex column := by
  simpa [compactNumericVerifierStepWitnessTableColumnValue] using
    CompactFixedWidthEntry.value_eq_tableValue hentry

theorem compactNumericVerifierStepWitnessTableBoundedRow_iff_formula
    (tableWidth table rowIndex : Nat) :
    CompactNumericVerifierStepWitnessTableBoundedRow
        tableWidth table (2 ^ tableWidth) rowIndex ↔
      compactNumericVerifierStepGraphDef.val.Evalb
        (compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table rowIndex) := by
  constructor
  · rintro ⟨environment, _hbound, hentries, hformula⟩
    have henvironment : environment =
        compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth table rowIndex := by
      funext coordinate
      exact CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue
        (hentries coordinate)
    simpa only [henvironment] using hformula
  · intro hformula
    let environment :=
      compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex
    refine ⟨environment, ?_, ?_, hformula⟩
    · intro coordinate
      exact compactNumericVerifierStepWitnessTableColumnValue_le_pow
        tableWidth table rowIndex coordinate.val
    · intro coordinate
      exact compactNumericVerifierStepWitnessTableColumnValue_entry
        tableWidth table rowIndex coordinate.val

def CompactNumericVerifierStepWitnessTableCanonicalAdjacent
    (tableWidth table rowIndex : Nat) : Prop :=
  let source := compactNumericVerifierStepWitnessTableFormulaEnvironment
    tableWidth table rowIndex
  let target := compactNumericVerifierStepWitnessTableFormulaEnvironment
    tableWidth table (rowIndex + 1)
  CompactFixedWidthCrossTableSlicesEq
    (source 0) (source 1) (source 2) (source 24) (source 25)
    (target 0) (target 1) (target 2) (target 3) (target 4)

theorem compactNumericVerifierStepWitnessTableAdjacentRow_iff_canonical
    (tableWidth table rowIndex : Nat) :
    CompactNumericVerifierStepWitnessTableAdjacentRow
        tableWidth table (2 ^ tableWidth) rowIndex ↔
      CompactNumericVerifierStepWitnessTableCanonicalAdjacent
        tableWidth table rowIndex := by
  let source := compactNumericVerifierStepWitnessTableFormulaEnvironment
    tableWidth table rowIndex
  let target := compactNumericVerifierStepWitnessTableFormulaEnvironment
    tableWidth table (rowIndex + 1)
  have hsourceEntry (column : Fin 429) :
      CompactFixedWidthEntry table tableWidth
        (rowIndex * compactNumericVerifierStepWitnessColumnCount + column.val)
        (source column) := by
    change CompactFixedWidthEntry table tableWidth
      (rowIndex * compactNumericVerifierStepWitnessColumnCount + column.val)
      (compactNumericVerifierStepWitnessTableColumnValue tableWidth table
        rowIndex column.val)
    exact compactNumericVerifierStepWitnessTableColumnValue_entry
      tableWidth table rowIndex column.val
  have htargetEntry (column : Fin 429) :
      CompactFixedWidthEntry table tableWidth
        ((rowIndex + 1) * compactNumericVerifierStepWitnessColumnCount +
          column.val)
        (target column) := by
    change CompactFixedWidthEntry table tableWidth
      ((rowIndex + 1) * compactNumericVerifierStepWitnessColumnCount +
        column.val)
      (compactNumericVerifierStepWitnessTableColumnValue tableWidth table
        (rowIndex + 1) column.val)
    exact compactNumericVerifierStepWitnessTableColumnValue_entry
      tableWidth table (rowIndex + 1) column.val
  have hsourceBound (column : Fin 429) :
      source column ≤ 2 ^ tableWidth := by
    change compactNumericVerifierStepWitnessTableColumnValue tableWidth table
      rowIndex column.val ≤ 2 ^ tableWidth
    exact compactNumericVerifierStepWitnessTableColumnValue_le_pow
      tableWidth table rowIndex column.val
  have htargetBound (column : Fin 429) :
      target column ≤ 2 ^ tableWidth := by
    change compactNumericVerifierStepWitnessTableColumnValue tableWidth table
      (rowIndex + 1) column.val ≤ 2 ^ tableWidth
    exact compactNumericVerifierStepWitnessTableColumnValue_le_pow
      tableWidth table (rowIndex + 1) column.val
  constructor
  · rintro ⟨sourceTable, _hsourceTable,
      sourceWidth, _hsourceWidth,
      sourceTokenCount, _hsourceTokenCount,
      sourceStart, _hsourceStart,
      sourceFinish, _hsourceFinish,
      targetTable, _htargetTable,
      targetWidth, _htargetWidth,
      targetTokenCount, _htargetTokenCount,
      targetStart, _htargetStart,
      targetFinish, _htargetFinish,
      h0, h1, h2, h24, h25,
      ht0, ht1, ht2, ht3, ht4, hadjacent⟩
    have hs0 := CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h0
    have hs1 := CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h1
    have hs2 := CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h2
    have hs24 := CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h24
    have hs25 := CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue h25
    have ht0' := CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue ht0
    have ht1' := CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue ht1
    have ht2' := CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue ht2
    have ht3' := CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue ht3
    have ht4' := CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue ht4
    rw [hs0, hs1, hs2, hs24, hs25,
      ht0', ht1', ht2', ht3', ht4'] at hadjacent
    simpa [CompactNumericVerifierStepWitnessTableCanonicalAdjacent,
      compactNumericVerifierStepWitnessTableFormulaEnvironment,
      source, target] using hadjacent
  · intro hadjacent
    refine ⟨source 0, hsourceBound 0,
      source 1, hsourceBound 1,
      source 2, hsourceBound 2,
      source 24, hsourceBound 24,
      source 25, hsourceBound 25,
      target 0, htargetBound 0,
      target 1, htargetBound 1,
      target 2, htargetBound 2,
      target 3, htargetBound 3,
      target 4, htargetBound 4,
      hsourceEntry 0, hsourceEntry 1, hsourceEntry 2,
      hsourceEntry 24, hsourceEntry 25,
      htargetEntry 0, htargetEntry 1, htargetEntry 2,
      htargetEntry 3, htargetEntry 4, ?_⟩
    simpa [CompactNumericVerifierStepWitnessTableCanonicalAdjacent,
      compactNumericVerifierStepWitnessTableFormulaEnvironment,
      source, target] using hadjacent

#print axioms compactNumericVerifierStepWitnessTableColumnValue_entry
#print axioms compactNumericVerifierStepWitnessTableColumnValue_le_pow
#print axioms compactNumericVerifierStepWitnessTableBoundedRow_iff_formula
#print axioms compactNumericVerifierStepWitnessTableAdjacentRow_iff_canonical

end FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge
