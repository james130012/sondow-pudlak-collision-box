import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessTable
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula

/-!
# Quantitative aggregation for formula-transform trace witnesses

The adjacent-step table has exactly thirty-seven fields per row and the
initial/final package has exactly thirty-one fields.  This file turns uniform
per-field bit bounds into explicit bounds for the two dynamic-width sums.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformTraceBounds

open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula

private theorem list_sum_map_le_length_mul
    {α : Type*} {values : List α} {weight : α → Nat} {bound : Nat}
    (hbound : ∀ value ∈ values, weight value ≤ bound) :
    (values.map weight).sum ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have hhead : weight head ≤ bound := hbound head (by simp)
      have htail : ∀ value ∈ tail, weight value ≤ bound := by
        intro value hvalue
        exact hbound value (by simp [hvalue])
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        weight head + (tail.map weight).sum ≤
            bound + tail.length * bound :=
          Nat.add_le_add hhead (ih htail)
        _ = (tail.length + 1) * bound := by ring

@[simp] theorem compactFormulaTransformInitialFinalWitnessValues_length
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) :
    (compactFormulaTransformInitialFinalWitnessValues witness).length = 31 := by
  simp [compactFormulaTransformInitialFinalWitnessValues]

theorem compactFormulaTransformAdjacentStepDynamicWidth_le
    {rows : List CompactFormulaTransformAdjacentStepRow} {bound : Nat}
    (hbound : ∀ row ∈ rows,
      ∀ value ∈ compactFormulaTransformAdjacentStepRowValues row,
        Nat.size value ≤ bound) :
    compactFormulaTransformAdjacentStepDynamicWidth rows ≤
      rows.length * compactFormulaTransformAdjacentStepWitnessColumnCount *
        bound := by
  induction rows with
  | nil => simp [compactFormulaTransformAdjacentStepDynamicWidth]
  | cons row tail ih =>
      have hrow :
          ((compactFormulaTransformAdjacentStepRowValues row).map Nat.size).sum ≤
            compactFormulaTransformAdjacentStepWitnessColumnCount * bound := by
        simpa only [compactFormulaTransformAdjacentStepRowValues_length] using
          (list_sum_map_le_length_mul
            (values := compactFormulaTransformAdjacentStepRowValues row)
            (weight := Nat.size) (bound := bound)
            (hbound row (by simp)))
      have htail : ∀ tailRow ∈ tail,
          ∀ value ∈ compactFormulaTransformAdjacentStepRowValues tailRow,
            Nat.size value ≤ bound := by
        intro tailRow htailRow value hvalue
        exact hbound tailRow (by simp [htailRow]) value hvalue
      simp only [compactFormulaTransformAdjacentStepDynamicWidth,
        List.flatMap_cons, List.map_append, List.sum_append, List.length_cons]
      calc
        ((compactFormulaTransformAdjacentStepRowValues row).map Nat.size).sum +
            ((tail.flatMap compactFormulaTransformAdjacentStepRowValues).map
              Nat.size).sum ≤
          compactFormulaTransformAdjacentStepWitnessColumnCount * bound +
            tail.length * compactFormulaTransformAdjacentStepWitnessColumnCount *
              bound := Nat.add_le_add hrow (ih htail)
        _ = (tail.length + 1) *
            compactFormulaTransformAdjacentStepWitnessColumnCount * bound := by
          ring

theorem compactFormulaTransformInitialFinalWitnessDynamicWidth_le
    {witness : CompactFormulaTransformInitialFinalWitnessCoordinates}
    {bound : Nat}
    (hbound : ∀ value ∈
        compactFormulaTransformInitialFinalWitnessValues witness,
      Nat.size value ≤ bound) :
    compactFormulaTransformInitialFinalWitnessDynamicWidth witness ≤
      31 * bound := by
  simpa only [compactFormulaTransformInitialFinalWitnessDynamicWidth,
    compactFormulaTransformInitialFinalWitnessValues_length] using
      (list_sum_map_le_length_mul
        (values := compactFormulaTransformInitialFinalWitnessValues witness)
        (weight := Nat.size) (bound := bound) hbound)

theorem compactFormulaTransformTableWidth_le_of_fieldSizeBounds
    {rows : List CompactFormulaTransformAdjacentStepRow}
    {endpointWitness : CompactFormulaTransformInitialFinalWitnessCoordinates}
    {tokenCount rowBound endpointBound : Nat}
    (hrows : ∀ row ∈ rows,
      ∀ value ∈ compactFormulaTransformAdjacentStepRowValues row,
        Nat.size value ≤ rowBound)
    (hendpoint : ∀ value ∈
        compactFormulaTransformInitialFinalWitnessValues endpointWitness,
      Nat.size value ≤ endpointBound) :
    compactFormulaTransformAdjacentStepDynamicWidth rows +
        (tokenCount + 1) * tokenCount +
        compactFormulaTransformInitialFinalWitnessDynamicWidth endpointWitness ≤
      rows.length * compactFormulaTransformAdjacentStepWitnessColumnCount *
          rowBound +
        (tokenCount + 1) * tokenCount + 31 * endpointBound := by
  exact Nat.add_le_add
    (Nat.add_le_add
      (compactFormulaTransformAdjacentStepDynamicWidth_le hrows)
      (Nat.le_refl ((tokenCount + 1) * tokenCount)))
    (compactFormulaTransformInitialFinalWitnessDynamicWidth_le hendpoint)

#print axioms compactFormulaTransformInitialFinalWitnessValues_length
#print axioms compactFormulaTransformAdjacentStepDynamicWidth_le
#print axioms compactFormulaTransformInitialFinalWitnessDynamicWidth_le
#print axioms compactFormulaTransformTableWidth_le_of_fieldSizeBounds

end FoundationCompactNumericListedDirectFormulaTransformTraceBounds
