import integration.FoundationCompactNumericListedDirectTrace
import integration.FoundationCompactNumericListedDirectVerifierCheckedStepRow

/-!
# Canonical checked rows for a complete verifier trace

The row at index `i` is a proved complete-step witness for the public state
reached after exactly `i` transitions.  Consecutive rows are joined by the
cross-table equality relation from the checked-row layer.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCheckedStepRows

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectVerifierCheckedStepRow
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTable

noncomputable def compactNumericVerifierCanonicalCheckedStepRow
    (state : CompactNumericVerifierState) :
    CompactNumericVerifierCheckedStepRow :=
  Classical.choose (exists_compactNumericVerifierCheckedStepRow state)

@[simp] theorem compactNumericVerifierCanonicalCheckedStepRow_currentState
    (state : CompactNumericVerifierState) :
    (compactNumericVerifierCanonicalCheckedStepRow state).currentState =
      state :=
  (Classical.choose_spec
    (exists_compactNumericVerifierCheckedStepRow state)).1

@[simp] theorem compactNumericVerifierCanonicalCheckedStepRow_nextState
    (state : CompactNumericVerifierState) :
    (compactNumericVerifierCanonicalCheckedStepRow state).nextState =
      compactNumericVerifierStep state :=
  (Classical.choose_spec
    (exists_compactNumericVerifierCheckedStepRow state)).2

def compactNumericVerifierCanonicalCheckedStepRows
    (fuel : Nat) (start : CompactNumericVerifierState) :
    List CompactNumericVerifierCheckedStepRow :=
  (List.range fuel).map fun stepIndex =>
    compactNumericVerifierCanonicalCheckedStepRow
      (compactNumericVerifierStateAt start stepIndex)

@[simp] theorem compactNumericVerifierCanonicalCheckedStepRows_length
    (fuel : Nat) (start : CompactNumericVerifierState) :
    (compactNumericVerifierCanonicalCheckedStepRows fuel start).length =
      fuel := by
  simp [compactNumericVerifierCanonicalCheckedStepRows]

theorem compactNumericVerifierCanonicalCheckedStepRows_getI
    (fuel stepIndex : Nat) (start : CompactNumericVerifierState)
    (hstepIndex : stepIndex < fuel) :
    (compactNumericVerifierCanonicalCheckedStepRows fuel start).getI
        stepIndex =
      compactNumericVerifierCanonicalCheckedStepRow
        (compactNumericVerifierStateAt start stepIndex) := by
  have hindex : stepIndex <
      (compactNumericVerifierCanonicalCheckedStepRows fuel start).length := by
    simpa using hstepIndex
  rw [List.getI_eq_getElem _ hindex]
  simp [compactNumericVerifierCanonicalCheckedStepRows]

theorem compactNumericVerifierCanonicalCheckedStepRows_currentState
    (fuel stepIndex : Nat) (start : CompactNumericVerifierState)
    (hstepIndex : stepIndex < fuel) :
    ((compactNumericVerifierCanonicalCheckedStepRows fuel start).getI
      stepIndex).currentState =
        compactNumericVerifierStateAt start stepIndex := by
  rw [compactNumericVerifierCanonicalCheckedStepRows_getI
    fuel stepIndex start hstepIndex]
  simp

theorem compactNumericVerifierCanonicalCheckedStepRows_nextState
    (fuel stepIndex : Nat) (start : CompactNumericVerifierState)
    (hstepIndex : stepIndex < fuel) :
    ((compactNumericVerifierCanonicalCheckedStepRows fuel start).getI
      stepIndex).nextState =
        compactNumericVerifierStateAt start (stepIndex + 1) := by
  rw [compactNumericVerifierCanonicalCheckedStepRows_getI
    fuel stepIndex start hstepIndex]
  simp [compactNumericVerifierStateAt, Function.iterate_succ_apply']

theorem compactNumericVerifierCanonicalCheckedStepRows_adjacent
    (fuel stepIndex : Nat) (start : CompactNumericVerifierState)
    (hstepIndex : stepIndex + 1 < fuel) :
    CompactNumericVerifierCheckedStepRowsAdjacent
      ((compactNumericVerifierCanonicalCheckedStepRows fuel start).getI
        stepIndex)
      ((compactNumericVerifierCanonicalCheckedStepRows fuel start).getI
        (stepIndex + 1)) := by
  apply CompactNumericVerifierCheckedStepRowsAdjacent.of_state_eq
  rw [compactNumericVerifierCanonicalCheckedStepRows_nextState
      fuel stepIndex start (by omega),
    compactNumericVerifierCanonicalCheckedStepRows_currentState
      fuel (stepIndex + 1) start hstepIndex]

def compactNumericVerifierCanonicalStepFormulaRows
    (fuel : Nat) (start : CompactNumericVerifierState) :
    List CompactNumericVerifierStepFormulaRow :=
  (compactNumericVerifierCanonicalCheckedStepRows fuel start).map
    CompactNumericVerifierCheckedStepRow.toFormulaRow

@[simp] theorem compactNumericVerifierCanonicalStepFormulaRows_length
    (fuel : Nat) (start : CompactNumericVerifierState) :
    (compactNumericVerifierCanonicalStepFormulaRows fuel start).length =
      fuel := by
  simp [compactNumericVerifierCanonicalStepFormulaRows]

theorem compactNumericVerifierCanonicalStepFormulaRows_valid
    (fuel : Nat) (start : CompactNumericVerifierState) :
    compactNumericVerifierStepFormulaRowsValid
      (compactNumericVerifierCanonicalStepFormulaRows fuel start) := by
  intro row hrow
  rcases List.mem_map.mp hrow with ⟨checkedRow, _hcheckedRow, rfl⟩
  exact checkedRow.formula

theorem compactNumericVerifierCanonicalStepFormulaRows_fit_dynamic
    (fuel : Nat) (start : CompactNumericVerifierState) :
    CompactNumericVerifierStepFormulaRowsFit
      (compactNumericVerifierStepFormulaDynamicWidth
        (compactNumericVerifierCanonicalStepFormulaRows fuel start))
      (compactNumericVerifierCanonicalStepFormulaRows fuel start) :=
  compactNumericVerifierStepFormulaRowsFit_dynamic _

theorem compactNumericVerifierCanonicalStepFormulaWitnessTable_graph
    (fuel : Nat) (start : CompactNumericVerifierState) :
    let rows := compactNumericVerifierCanonicalStepFormulaRows fuel start
    let tableWidth := compactNumericVerifierStepFormulaDynamicWidth rows
    ∀ rowIndex < fuel,
      compactNumericVerifierStepGraphDef.val.Evalb
        (compactNumericVerifierStepWitnessTableFormulaEnvironment
          tableWidth
          (compactNumericVerifierStepWitnessTableCode tableWidth rows)
          rowIndex) := by
  dsimp only
  intro rowIndex hrowIndex
  apply compactNumericVerifierStepWitnessTableCode_formula
    (compactNumericVerifierCanonicalStepFormulaRows_fit_dynamic fuel start)
    (compactNumericVerifierCanonicalStepFormulaRows_valid fuel start)
  simpa using hrowIndex

#print axioms compactNumericVerifierCanonicalCheckedStepRow_currentState
#print axioms compactNumericVerifierCanonicalCheckedStepRow_nextState
#print axioms compactNumericVerifierCanonicalCheckedStepRows_getI
#print axioms compactNumericVerifierCanonicalCheckedStepRows_adjacent
#print axioms compactNumericVerifierCanonicalStepFormulaRows_valid
#print axioms compactNumericVerifierCanonicalStepFormulaWitnessTable_graph

end FoundationCompactNumericListedDirectVerifierCheckedStepRows
