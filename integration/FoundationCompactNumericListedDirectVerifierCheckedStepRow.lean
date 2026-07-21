import integration.FoundationCompactNumericListedDirectVerifierCanonicalStepFormulaLayouts
import integration.FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity
import integration.FoundationCompactNumericListedDirectVerifierStateCrossTableEquality
import integration.FoundationCompactNumericListedDirectVerifierStepWitnessTable

/-!
# Checked rows for complete verifier steps

A checked row retains the arbitrary 429-column formula environment together
with the two verifier states decoded from its exact current and next slices.
Adjacent rows are connected arithmetically by cross-table slice equality; no
shared token table or semantic state equality is assumed.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCheckedStepRow

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectVerifierStateCrossTableEquality
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepEnvironmentSurjectivity
open FoundationCompactNumericListedDirectVerifierCanonicalStepFormulaLayouts
open FoundationCompactNumericListedDirectVerifierStepCompleteness
open FoundationCompactNumericListedDirectVerifierStepWitnessTable

structure CompactNumericVerifierCheckedStepRow where
  environment : Fin 429 -> Nat
  currentState : CompactNumericVerifierState
  nextState : CompactNumericVerifierState
  currentLayout : CompactNumericVerifierStateDirectLayout
    (environment 0) (environment 1) (environment 2)
    (environment 3) (environment 4) currentState
  nextLayout : CompactNumericVerifierStateDirectLayout
    (environment 0) (environment 1) (environment 2)
    (environment 24) (environment 25) nextState
  formula : compactNumericVerifierStepGraphDef.val.Evalb environment

noncomputable def CompactNumericVerifierStepFormulaWitness.toCheckedStepRow
    {stateTable stateWidth stateTokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    (witness : CompactNumericVerifierStepFormulaWitness
      stateTable stateWidth stateTokenCount currentStart currentFinish
      nextStart nextFinish)
    (currentState nextState : CompactNumericVerifierState)
    (hcurrent : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount currentStart currentFinish
      currentState)
    (hnext : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextFinish nextState) :
    CompactNumericVerifierCheckedStepRow :=
  { environment := witness.environment
    currentState := currentState
    nextState := nextState
    currentLayout := by
      simpa only [witness.stateTable_eq, witness.stateWidth_eq,
        witness.stateTokenCount_eq, witness.currentStart_eq,
        witness.currentFinish_eq] using hcurrent
    nextLayout := by
      simpa only [witness.stateTable_eq, witness.stateWidth_eq,
        witness.stateTokenCount_eq, witness.nextStart_eq,
        witness.nextFinish_eq] using hnext
    formula := witness.formula }

@[simp] theorem
    CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_environment
    {stateTable stateWidth stateTokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    (witness : CompactNumericVerifierStepFormulaWitness
      stateTable stateWidth stateTokenCount currentStart currentFinish
      nextStart nextFinish)
    (currentState nextState : CompactNumericVerifierState)
    (hcurrent : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount currentStart currentFinish
      currentState)
    (hnext : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextFinish nextState) :
    (CompactNumericVerifierStepFormulaWitness.toCheckedStepRow witness
      currentState nextState hcurrent hnext).environment =
      witness.environment := rfl

@[simp] theorem
    CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_currentState
    {stateTable stateWidth stateTokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    (witness : CompactNumericVerifierStepFormulaWitness
      stateTable stateWidth stateTokenCount currentStart currentFinish
      nextStart nextFinish)
    (currentState nextState : CompactNumericVerifierState)
    (hcurrent : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount currentStart currentFinish
      currentState)
    (hnext : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextFinish nextState) :
    (CompactNumericVerifierStepFormulaWitness.toCheckedStepRow witness
      currentState nextState hcurrent hnext).currentState =
      currentState := rfl

@[simp] theorem
    CompactNumericVerifierStepFormulaWitness.toCheckedStepRow_nextState
    {stateTable stateWidth stateTokenCount currentStart currentFinish
      nextStart nextFinish : Nat}
    (witness : CompactNumericVerifierStepFormulaWitness
      stateTable stateWidth stateTokenCount currentStart currentFinish
      nextStart nextFinish)
    (currentState nextState : CompactNumericVerifierState)
    (hcurrent : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount currentStart currentFinish
      currentState)
    (hnext : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextFinish nextState) :
    (CompactNumericVerifierStepFormulaWitness.toCheckedStepRow witness
      currentState nextState hcurrent hnext).nextState =
      nextState := rfl

def CompactNumericVerifierCheckedStepRow.toFormulaRow
    (row : CompactNumericVerifierCheckedStepRow) :
    CompactNumericVerifierStepFormulaRow :=
  { environment := row.environment }

@[simp] theorem CompactNumericVerifierCheckedStepRow.toFormulaRow_environment
    (row : CompactNumericVerifierCheckedStepRow) :
    row.toFormulaRow.environment = row.environment := rfl

theorem CompactNumericVerifierCheckedStepRow.exact_step
    (row : CompactNumericVerifierCheckedStepRow) :
    row.nextState = compactNumericVerifierStep row.currentState := by
  rcases compactNumericVerifierStepGraphDef_evalb_realizeExactStep
      row.environment row.formula with
    ⟨realizedCurrent, realizedNext,
      hrealizedCurrent, hrealizedNext, hrealizedStep⟩
  rcases
      FoundationCompactNumericListedDirectVerifierStateCrossTableEquality.CompactNumericVerifierStateDirectLayout.toSliceCarries
        row.currentLayout with
    ⟨hcurrentFinish, hcurrentBound, _hcurrentEntries⟩
  have hcurrentSlices : CompactFixedWidthTokenSlicesEq
      (row.environment 0) (row.environment 1) (row.environment 2)
      (row.environment 3) (row.environment 4)
      (row.environment 3) (row.environment 4) :=
    CompactFixedWidthTokenSlicesEq.refl (by omega) hcurrentBound
  have hcurrent : realizedCurrent = row.currentState :=
    CompactFixedWidthTokenSlicesEq.verifierStateValue_eq
      hcurrentSlices row.currentLayout hrealizedCurrent
  rcases
      FoundationCompactNumericListedDirectVerifierStateCrossTableEquality.CompactNumericVerifierStateDirectLayout.toSliceCarries
        row.nextLayout with
    ⟨hnextFinish, hnextBound, _hnextEntries⟩
  have hnextSlices : CompactFixedWidthTokenSlicesEq
      (row.environment 0) (row.environment 1) (row.environment 2)
      (row.environment 24) (row.environment 25)
      (row.environment 24) (row.environment 25) :=
    CompactFixedWidthTokenSlicesEq.refl (by omega) hnextBound
  have hnext : realizedNext = row.nextState :=
    CompactFixedWidthTokenSlicesEq.verifierStateValue_eq
      hnextSlices row.nextLayout hrealizedNext
  rw [← hnext, hrealizedStep, hcurrent]

theorem exists_compactNumericVerifierCheckedStepRow
    (currentState : CompactNumericVerifierState) :
    ∃ row : CompactNumericVerifierCheckedStepRow,
      row.currentState = currentState ∧
        row.nextState = compactNumericVerifierStep currentState := by
  rcases
      exists_compactNumericVerifierStepFormulaWitness_with_layouts_of_public_step
        currentState with
    ⟨backTokens, witness, hcurrentLayout, hnextLayout⟩
  let row : CompactNumericVerifierCheckedStepRow :=
    { environment := witness.environment
      currentState := currentState
      nextState := compactNumericVerifierStep currentState
      currentLayout := by
        simpa only [witness.stateTable_eq, witness.stateWidth_eq,
          witness.stateTokenCount_eq, witness.currentStart_eq,
          witness.currentFinish_eq] using hcurrentLayout
      nextLayout := by
        simpa only [witness.stateTable_eq, witness.stateWidth_eq,
          witness.stateTokenCount_eq, witness.nextStart_eq,
          witness.nextFinish_eq] using hnextLayout
      formula := witness.formula }
  exact ⟨row, rfl, rfl⟩

noncomputable instance : Inhabited CompactNumericVerifierCheckedStepRow where
  default := Classical.choose
    (exists_compactNumericVerifierCheckedStepRow default)

def CompactNumericVerifierCheckedStepRowsAdjacent
    (left right : CompactNumericVerifierCheckedStepRow) : Prop :=
  CompactFixedWidthCrossTableSlicesEq
    (left.environment 0) (left.environment 1) (left.environment 2)
    (left.environment 24) (left.environment 25)
    (right.environment 0) (right.environment 1) (right.environment 2)
    (right.environment 3) (right.environment 4)

theorem CompactNumericVerifierCheckedStepRowsAdjacent.of_state_eq
    {left right : CompactNumericVerifierCheckedStepRow}
    (hstate : left.nextState = right.currentState) :
    CompactNumericVerifierCheckedStepRowsAdjacent left right := by
  have hright : CompactNumericVerifierStateDirectLayout
      (right.environment 0) (right.environment 1) (right.environment 2)
      (right.environment 3) (right.environment 4) left.nextState := by
    simpa only [hstate] using right.currentLayout
  exact CompactFixedWidthCrossTableSlicesEq.of_verifierStateLayouts
    left.nextLayout hright

theorem CompactNumericVerifierCheckedStepRowsAdjacent.state_eq
    {left right : CompactNumericVerifierCheckedStepRow}
    (hadjacent : CompactNumericVerifierCheckedStepRowsAdjacent left right) :
    right.currentState = left.nextState := by
  exact CompactFixedWidthCrossTableSlicesEq.verifierStateValue_eq
    hadjacent left.nextLayout right.currentLayout

theorem CompactNumericVerifierCheckedStepRowsAdjacent.exact_transition
    {left right : CompactNumericVerifierCheckedStepRow}
    (hadjacent : CompactNumericVerifierCheckedStepRowsAdjacent left right) :
    right.currentState = compactNumericVerifierStep left.currentState := by
  exact hadjacent.state_eq.trans left.exact_step

#print axioms CompactNumericVerifierCheckedStepRow.exact_step
#print axioms exists_compactNumericVerifierCheckedStepRow
#print axioms CompactNumericVerifierCheckedStepRowsAdjacent.of_state_eq
#print axioms CompactNumericVerifierCheckedStepRowsAdjacent.state_eq
#print axioms CompactNumericVerifierCheckedStepRowsAdjacent.exact_transition

end FoundationCompactNumericListedDirectVerifierCheckedStepRow
