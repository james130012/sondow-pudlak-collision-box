import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceRowsGlobalBound
import integration.FoundationCompactNumericListedDirectCanonicalTraceBounds
import integration.FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge

/-!
# Selecting a uniformly bounded checked row at every trace offset

The older canonical row selector chooses an arbitrary complete-step witness and
therefore does not preserve a separately proved coordinate bound.  This module
chooses from the bounded existence theorem itself and records the resulting
state equalities and coordinate bound pointwise.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierBoundedTraceSelection

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierCheckedStepRows
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableAdjacencyFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge
open FoundationCompactNumericListedDirectCanonicalTraceBounds

noncomputable def compactNumericVerifierBoundedCheckedStepRow
    (fuel : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound)
    (offset : Nat) : CompactNumericVerifierCheckedStepRow :=
  if hoffset : offset < fuel then Classical.choose (hrows offset hoffset)
  else compactNumericVerifierCanonicalCheckedStepRow
    (compactNumericVerifierStateAt start offset)

theorem compactNumericVerifierBoundedCheckedStepRow_spec
    (fuel : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound)
    (offset : Nat)
    (hoffset : offset < fuel) :
    let row := compactNumericVerifierBoundedCheckedStepRow fuel start
      coordinateBound hrows offset
    row.currentState = compactNumericVerifierStateAt start offset /\
      row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
      forall coordinate : Fin 429,
        Nat.size (row.environment coordinate) <= coordinateBound := by
  dsimp only
  rw [compactNumericVerifierBoundedCheckedStepRow, dif_pos hoffset]
  exact Classical.choose_spec (hrows offset hoffset)

noncomputable def compactNumericVerifierBoundedCheckedStepRows
    (fuel : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) :
    List CompactNumericVerifierCheckedStepRow :=
  (List.range fuel).map fun offset =>
    compactNumericVerifierBoundedCheckedStepRow fuel start coordinateBound
      hrows offset

@[simp] theorem compactNumericVerifierBoundedCheckedStepRows_length
    (fuel : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) :
    (compactNumericVerifierBoundedCheckedStepRows fuel start coordinateBound
      hrows).length = fuel := by
  simp [compactNumericVerifierBoundedCheckedStepRows]

theorem compactNumericVerifierBoundedCheckedStepRows_getI
    (fuel offset : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall index, index < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start index /\
          row.nextState =
            compactNumericVerifierStateAt start (index + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound)
    (hoffset : offset < fuel) :
    (compactNumericVerifierBoundedCheckedStepRows fuel start coordinateBound
      hrows).getI offset =
        compactNumericVerifierBoundedCheckedStepRow fuel start coordinateBound
          hrows offset := by
  have hindex : offset <
      (compactNumericVerifierBoundedCheckedStepRows fuel start coordinateBound
        hrows).length := by
    simpa using hoffset
  rw [List.getI_eq_getElem _ hindex]
  simp [compactNumericVerifierBoundedCheckedStepRows]

theorem compactNumericVerifierBoundedCheckedStepRows_spec
    (fuel offset : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall index, index < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start index /\
          row.nextState =
            compactNumericVerifierStateAt start (index + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound)
    (hoffset : offset < fuel) :
    let row := (compactNumericVerifierBoundedCheckedStepRows fuel start
      coordinateBound hrows).getI offset
    row.currentState = compactNumericVerifierStateAt start offset /\
      row.nextState = compactNumericVerifierStateAt start (offset + 1) /\
      forall coordinate : Fin 429,
        Nat.size (row.environment coordinate) <= coordinateBound := by
  dsimp only
  rw [compactNumericVerifierBoundedCheckedStepRows_getI fuel offset start
    coordinateBound hrows hoffset]
  exact compactNumericVerifierBoundedCheckedStepRow_spec fuel start
    coordinateBound hrows offset hoffset

theorem compactNumericVerifierBoundedCheckedStepRows_adjacent
    (fuel offset : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall index, index < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start index /\
          row.nextState =
            compactNumericVerifierStateAt start (index + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound)
    (hoffset : offset + 1 < fuel) :
    CompactNumericVerifierCheckedStepRowsAdjacent
      ((compactNumericVerifierBoundedCheckedStepRows fuel start
        coordinateBound hrows).getI offset)
      ((compactNumericVerifierBoundedCheckedStepRows fuel start
        coordinateBound hrows).getI (offset + 1)) := by
  apply CompactNumericVerifierCheckedStepRowsAdjacent.of_state_eq
  have hsource := compactNumericVerifierBoundedCheckedStepRows_spec
    fuel offset start coordinateBound hrows (by omega)
  have htarget := compactNumericVerifierBoundedCheckedStepRows_spec
    fuel (offset + 1) start coordinateBound hrows hoffset
  exact hsource.2.1.trans htarget.1.symm

noncomputable def compactNumericVerifierBoundedStepFormulaRows
    (fuel : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) :
    List CompactNumericVerifierStepFormulaRow :=
  (compactNumericVerifierBoundedCheckedStepRows fuel start coordinateBound
    hrows).map CompactNumericVerifierCheckedStepRow.toFormulaRow

@[simp] theorem compactNumericVerifierBoundedStepFormulaRows_length
    (fuel : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) :
    (compactNumericVerifierBoundedStepFormulaRows fuel start coordinateBound
      hrows).length = fuel := by
  simp [compactNumericVerifierBoundedStepFormulaRows]

theorem compactNumericVerifierBoundedStepFormulaRows_valid
    (fuel : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) :
    compactNumericVerifierStepFormulaRowsValid
      (compactNumericVerifierBoundedStepFormulaRows fuel start
        coordinateBound hrows) := by
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨checkedRow, _hcheckedRow, rfl⟩
  exact checkedRow.formula

theorem compactNumericVerifierBoundedStepFormulaRows_rowBitWeight_le
    (fuel : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) :
    forall row,
      row ∈ compactNumericVerifierBoundedStepFormulaRows fuel start
          coordinateBound hrows ->
        compactNumericVerifierStepFormulaRowBitWeight row <=
          compactNumericVerifierStepWitnessColumnCount * coordinateBound := by
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨checkedRow, hcheckedRow, rfl⟩
  rw [compactNumericVerifierBoundedCheckedStepRows] at hcheckedRow
  rcases List.mem_map.mp hcheckedRow with
    ⟨offset, hoffsetRange, rfl⟩
  have hoffset : offset < fuel := List.mem_range.mp hoffsetRange
  apply compactNumericVerifierStepFormulaRowBitWeight_le
  intro coordinate
  exact (compactNumericVerifierBoundedCheckedStepRow_spec fuel start
    coordinateBound hrows offset hoffset).2.2 coordinate

theorem compactNumericVerifierBoundedStepFormulaDynamicWidth_le
    (fuel : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) :
    compactNumericVerifierStepFormulaDynamicWidth
        (compactNumericVerifierBoundedStepFormulaRows fuel start
          coordinateBound hrows) <=
      fuel *
        (compactNumericVerifierStepWitnessColumnCount * coordinateBound) := by
  have hbound :=
    compactNumericVerifierStepFormulaDynamicWidth_le_of_rowBitWeight
      (compactNumericVerifierBoundedStepFormulaRows_rowBitWeight_le fuel start
        coordinateBound hrows)
  simpa only [compactNumericVerifierBoundedStepFormulaRows_length] using
    hbound

theorem compactNumericVerifierBoundedTraceCoordinates_size_le
    (fuel : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) :
    let rows := compactNumericVerifierBoundedStepFormulaRows fuel start
      coordinateBound hrows
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    tableWidth <=
        fuel *
          (compactNumericVerifierStepWitnessColumnCount * coordinateBound) /\
      Nat.size table <=
        fuel * compactNumericVerifierStepWitnessColumnCount *
          (fuel *
            (compactNumericVerifierStepWitnessColumnCount *
              coordinateBound)) /\
      Nat.size (2 ^ tableWidth) <=
        fuel *
          (compactNumericVerifierStepWitnessColumnCount * coordinateBound) +
            1 := by
  dsimp only
  let rows := compactNumericVerifierBoundedStepFormulaRows fuel start
    coordinateBound hrows
  let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
  have hwidth : tableWidth <=
      fuel *
        (compactNumericVerifierStepWitnessColumnCount * coordinateBound) := by
    simpa only [tableWidth, rows] using
      compactNumericVerifierBoundedStepFormulaDynamicWidth_le fuel start
        coordinateBound hrows
  have htable := compactNumericVerifierStepWitnessTableCode_size_le
    tableWidth rows
  have htableScale :
      rows.length * compactNumericVerifierStepWitnessColumnCount *
          tableWidth <=
        fuel * compactNumericVerifierStepWitnessColumnCount *
          (fuel *
            (compactNumericVerifierStepWitnessColumnCount *
              coordinateBound)) := by
    rw [compactNumericVerifierBoundedStepFormulaRows_length]
    exact Nat.mul_le_mul_left
      (fuel * compactNumericVerifierStepWitnessColumnCount) hwidth
  have hvalue : Nat.size (2 ^ tableWidth) <=
      fuel *
          (compactNumericVerifierStepWitnessColumnCount * coordinateBound) +
        1 := by
    rw [Nat.size_pow]
    omega
  exact ⟨hwidth, htable.trans htableScale, hvalue⟩

theorem compactNumericVerifierBoundedStepFormulaRows_getI
    (fuel rowIndex : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound)
    (hrowIndex : rowIndex < fuel) :
    (compactNumericVerifierBoundedStepFormulaRows fuel start coordinateBound
      hrows).getI rowIndex =
      ((compactNumericVerifierBoundedCheckedStepRows fuel start
        coordinateBound hrows).getI rowIndex).toFormulaRow := by
  have hchecked : rowIndex <
      (compactNumericVerifierBoundedCheckedStepRows fuel start
        coordinateBound hrows).length := by
    simpa using hrowIndex
  have hformula : rowIndex <
      (compactNumericVerifierBoundedStepFormulaRows fuel start
        coordinateBound hrows).length := by
    simpa using hrowIndex
  rw [List.getI_eq_getElem _ hformula, List.getI_eq_getElem _ hchecked]
  simp [compactNumericVerifierBoundedStepFormulaRows]

theorem compactNumericVerifierBoundedStepWitnessTable_environment_eq
    (fuel rowIndex : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound)
    (hrowIndex : rowIndex < fuel) :
    let rows := compactNumericVerifierBoundedStepFormulaRows fuel start
      coordinateBound hrows
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex =
      ((compactNumericVerifierBoundedCheckedStepRows fuel start
        coordinateBound hrows).getI rowIndex).environment := by
  dsimp only
  let rows := compactNumericVerifierBoundedStepFormulaRows fuel start
    coordinateBound hrows
  let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
  have hfit : CompactNumericVerifierStepFormulaRowsFit tableWidth rows :=
    compactNumericVerifierStepFormulaRowsFit_dynamic rows
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
      ((compactNumericVerifierBoundedCheckedStepRows fuel start
        coordinateBound hrows).getI rowIndex).toFormulaRow by
    exact compactNumericVerifierBoundedStepFormulaRows_getI fuel rowIndex
      start coordinateBound hrows hrowIndex]
  rfl

theorem compactNumericVerifierBoundedStepWitnessTable_boundedGraph
    (fuel : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) :
    let rows := compactNumericVerifierBoundedStepFormulaRows fuel start
      coordinateBound hrows
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    CompactNumericVerifierStepWitnessTableBoundedGraph
      tableWidth table fuel (2 ^ tableWidth) := by
  dsimp only
  intro rowIndex hrowIndex
  apply
    (compactNumericVerifierStepWitnessTableBoundedRow_iff_formula
      (compactNumericVerifierStepFormulaDynamicWidth
        (compactNumericVerifierBoundedStepFormulaRows fuel start
          coordinateBound hrows))
      (compactNumericVerifierStepWitnessTableCode
        (compactNumericVerifierStepFormulaDynamicWidth
          (compactNumericVerifierBoundedStepFormulaRows fuel start
            coordinateBound hrows))
        (compactNumericVerifierBoundedStepFormulaRows fuel start
          coordinateBound hrows)) rowIndex).mpr
  apply compactNumericVerifierStepWitnessTableCode_formula
    (compactNumericVerifierStepFormulaRowsFit_dynamic _)
    (compactNumericVerifierBoundedStepFormulaRows_valid fuel start
      coordinateBound hrows)
  simpa using hrowIndex

theorem compactNumericVerifierBoundedStepWitnessTable_canonicalAdjacent
    (fuel rowIndex : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound)
    (hrowIndex : rowIndex + 1 < fuel) :
    let rows := compactNumericVerifierBoundedStepFormulaRows fuel start
      coordinateBound hrows
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    CompactNumericVerifierStepWitnessTableCanonicalAdjacent
      tableWidth table rowIndex := by
  dsimp only
  have hadjacent := compactNumericVerifierBoundedCheckedStepRows_adjacent
    fuel rowIndex start coordinateBound hrows hrowIndex
  have hsource :=
    compactNumericVerifierBoundedStepWitnessTable_environment_eq fuel
      rowIndex start coordinateBound hrows (by omega)
  have htarget :=
    compactNumericVerifierBoundedStepWitnessTable_environment_eq fuel
      (rowIndex + 1) start coordinateBound hrows hrowIndex
  unfold CompactNumericVerifierStepWitnessTableCanonicalAdjacent
  rw [hsource, htarget]
  exact hadjacent

theorem compactNumericVerifierBoundedStepWitnessTable_rowsAdjacent
    (fuel : Nat)
    (start : CompactNumericVerifierState)
    (coordinateBound : Nat)
    (hrows : forall offset, offset < fuel ->
      exists row : CompactNumericVerifierCheckedStepRow,
        row.currentState = compactNumericVerifierStateAt start offset /\
          row.nextState =
            compactNumericVerifierStateAt start (offset + 1) /\
          forall coordinate : Fin 429,
            Nat.size (row.environment coordinate) <= coordinateBound) :
    let rows := compactNumericVerifierBoundedStepFormulaRows fuel start
      coordinateBound hrows
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    let table := compactNumericVerifierStepWitnessTableCode tableWidth rows
    CompactNumericVerifierStepWitnessTableRowsAdjacent
      tableWidth table fuel (2 ^ tableWidth) := by
  dsimp only
  intro rowIndex _hrowIndex hnextRow
  apply
    (compactNumericVerifierStepWitnessTableAdjacentRow_iff_canonical
      (compactNumericVerifierStepFormulaDynamicWidth
        (compactNumericVerifierBoundedStepFormulaRows fuel start
          coordinateBound hrows))
      (compactNumericVerifierStepWitnessTableCode
        (compactNumericVerifierStepFormulaDynamicWidth
          (compactNumericVerifierBoundedStepFormulaRows fuel start
            coordinateBound hrows))
        (compactNumericVerifierBoundedStepFormulaRows fuel start
          coordinateBound hrows)) rowIndex).mpr
  exact compactNumericVerifierBoundedStepWitnessTable_canonicalAdjacent
    fuel rowIndex start coordinateBound hrows hnextRow

#print axioms compactNumericVerifierBoundedCheckedStepRow_spec
#print axioms compactNumericVerifierBoundedCheckedStepRows_getI
#print axioms compactNumericVerifierBoundedCheckedStepRows_spec
#print axioms compactNumericVerifierBoundedCheckedStepRows_adjacent
#print axioms compactNumericVerifierBoundedStepFormulaRows_valid
#print axioms
  compactNumericVerifierBoundedStepFormulaRows_rowBitWeight_le
#print axioms compactNumericVerifierBoundedStepFormulaDynamicWidth_le
#print axioms compactNumericVerifierBoundedTraceCoordinates_size_le
#print axioms compactNumericVerifierBoundedStepFormulaRows_getI
#print axioms compactNumericVerifierBoundedStepWitnessTable_environment_eq
#print axioms compactNumericVerifierBoundedStepWitnessTable_boundedGraph
#print axioms
  compactNumericVerifierBoundedStepWitnessTable_canonicalAdjacent
#print axioms compactNumericVerifierBoundedStepWitnessTable_rowsAdjacent

end FoundationCompactNumericListedDirectVerifierBoundedTraceSelection
