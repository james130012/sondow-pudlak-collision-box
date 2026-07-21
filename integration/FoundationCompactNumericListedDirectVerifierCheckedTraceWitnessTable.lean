import integration.FoundationCompactNumericListedDirectVerifierCheckedStepRows
import integration.FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge

/-!
# Complete checked trace installed in one witness table

The canonical public verifier trace supplies one independent complete-step
witness per row.  Their 429-column environments are stored in one fixed-width
table.  That table satisfies both the bounded row formula and every bounded
cross-table adjacency formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCheckedTraceWitnessTable

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierCheckedStepRows
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableAdjacencyFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge

theorem compactNumericVerifierCanonicalStepFormulaRows_getI
    (fuel rowIndex : Nat) (start : CompactNumericVerifierState)
    (hrowIndex : rowIndex < fuel) :
    (compactNumericVerifierCanonicalStepFormulaRows fuel start).getI rowIndex =
      ((compactNumericVerifierCanonicalCheckedStepRows fuel start).getI
        rowIndex).toFormulaRow := by
  have hchecked : rowIndex <
      (compactNumericVerifierCanonicalCheckedStepRows fuel start).length := by
    simpa using hrowIndex
  have hformula : rowIndex <
      (compactNumericVerifierCanonicalStepFormulaRows fuel start).length := by
    simpa using hrowIndex
  rw [List.getI_eq_getElem _ hformula, List.getI_eq_getElem _ hchecked]
  simp [compactNumericVerifierCanonicalStepFormulaRows]

theorem compactNumericVerifierCanonicalStepWitnessTable_environment_eq
    (fuel rowIndex : Nat) (start : CompactNumericVerifierState)
    (hrowIndex : rowIndex < fuel) :
    let rows := compactNumericVerifierCanonicalStepFormulaRows fuel start
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex =
      ((compactNumericVerifierCanonicalCheckedStepRows fuel start).getI
        rowIndex).environment := by
  dsimp only
  let rows := compactNumericVerifierCanonicalStepFormulaRows fuel start
  let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
  have hfit : CompactNumericVerifierStepFormulaRowsFit tableWidth rows := by
    exact compactNumericVerifierStepFormulaRowsFit_dynamic rows
  have hcarries : CompactNumericVerifierStepWitnessTableCarriesRows
      tableWidth (compactNumericVerifierStepWitnessTableCode tableWidth rows)
        rows :=
    compactNumericVerifierStepWitnessTableCode_carriesRows hfit
  have hrowIndexRows : rowIndex < rows.length := by
    simpa [rows] using hrowIndex
  rw [compactNumericVerifierStepWitnessTableFormulaEnvironment_eq
    hcarries rowIndex hrowIndexRows]
  change (rows.getI rowIndex).environment = _
  rw [show rows.getI rowIndex =
      ((compactNumericVerifierCanonicalCheckedStepRows fuel start).getI
        rowIndex).toFormulaRow by
    exact compactNumericVerifierCanonicalStepFormulaRows_getI
      fuel rowIndex start hrowIndex]
  rfl

theorem compactNumericVerifierCanonicalStepWitnessTable_boundedGraph
    (fuel : Nat) (start : CompactNumericVerifierState) :
    let rows := compactNumericVerifierCanonicalStepFormulaRows fuel start
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    CompactNumericVerifierStepWitnessTableBoundedGraph
      tableWidth table fuel (2 ^ tableWidth) := by
  dsimp only
  intro rowIndex hrowIndex
  apply
    (compactNumericVerifierStepWitnessTableBoundedRow_iff_formula
      (compactNumericVerifierStepFormulaDynamicWidth
        (compactNumericVerifierCanonicalStepFormulaRows fuel start))
      (compactNumericVerifierStepWitnessTableCode
        (compactNumericVerifierStepFormulaDynamicWidth
          (compactNumericVerifierCanonicalStepFormulaRows fuel start))
        (compactNumericVerifierCanonicalStepFormulaRows fuel start))
      rowIndex).mpr
  exact compactNumericVerifierCanonicalStepFormulaWitnessTable_graph
    fuel start rowIndex hrowIndex

theorem compactNumericVerifierCanonicalStepWitnessTable_canonicalAdjacent
    (fuel rowIndex : Nat) (start : CompactNumericVerifierState)
    (hrowIndex : rowIndex + 1 < fuel) :
    let rows := compactNumericVerifierCanonicalStepFormulaRows fuel start
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    CompactNumericVerifierStepWitnessTableCanonicalAdjacent
      tableWidth table rowIndex := by
  dsimp only
  have hadjacent := compactNumericVerifierCanonicalCheckedStepRows_adjacent
    fuel rowIndex start hrowIndex
  have hsource :=
    compactNumericVerifierCanonicalStepWitnessTable_environment_eq
      fuel rowIndex start (by omega)
  have htarget :=
    compactNumericVerifierCanonicalStepWitnessTable_environment_eq
      fuel (rowIndex + 1) start hrowIndex
  unfold CompactNumericVerifierStepWitnessTableCanonicalAdjacent
  rw [hsource, htarget]
  simpa [CompactNumericVerifierCheckedStepRowsAdjacent] using hadjacent

theorem compactNumericVerifierCanonicalStepWitnessTable_rowsAdjacent
    (fuel : Nat) (start : CompactNumericVerifierState) :
    let rows := compactNumericVerifierCanonicalStepFormulaRows fuel start
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    CompactNumericVerifierStepWitnessTableRowsAdjacent
      tableWidth table fuel (2 ^ tableWidth) := by
  dsimp only
  intro rowIndex _hrowIndex hnextRow
  apply
    (compactNumericVerifierStepWitnessTableAdjacentRow_iff_canonical
      (compactNumericVerifierStepFormulaDynamicWidth
        (compactNumericVerifierCanonicalStepFormulaRows fuel start))
      (compactNumericVerifierStepWitnessTableCode
        (compactNumericVerifierStepFormulaDynamicWidth
          (compactNumericVerifierCanonicalStepFormulaRows fuel start))
        (compactNumericVerifierCanonicalStepFormulaRows fuel start))
      rowIndex).mpr
  exact compactNumericVerifierCanonicalStepWitnessTable_canonicalAdjacent
    fuel rowIndex start hnextRow

#print axioms compactNumericVerifierCanonicalStepFormulaRows_getI
#print axioms compactNumericVerifierCanonicalStepWitnessTable_environment_eq
#print axioms compactNumericVerifierCanonicalStepWitnessTable_boundedGraph
#print axioms compactNumericVerifierCanonicalStepWitnessTable_canonicalAdjacent
#print axioms compactNumericVerifierCanonicalStepWitnessTable_rowsAdjacent

end FoundationCompactNumericListedDirectVerifierCheckedTraceWitnessTable
